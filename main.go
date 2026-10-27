
package main

import (
	"bytes"
	"context"
	"crypto/rand"
	"crypto/sha256"
	"crypto/subtle"
	"encoding/base64"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io"
	"log"
	"net"
	"net/http"
	"net/url"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"strconv"
	"strings"
	"sync"
	"syscall"
	"time"
	"unicode/utf16"

	qrcode "github.com/skip2/go-qrcode"
)

const (
	port           = 8081
	passIterations = 200000
	maxPrintBytes  = 100 << 20
	ipFailLimit    = 5
	globalFailLim  = 15
)

var (
	pinRe  = regexp.MustCompile(`^[0-9]{5}$`)
	printMu sync.Mutex
	failMu  sync.Mutex
	fails   = map[string]*failInfo{}
	cfgMu   sync.RWMutex
	cfg     config
)

type config struct {
	Enabled bool   `json:"enabled"`
	Hash    string `json:"hash,omitempty"`
	Salt    string `json:"salt,omitempty"`
}

type failInfo struct {
	count       int
	first       time.Time
	lockedUntil time.Time
}

// ---------- settings file ----------

func cfgPath() string {
	appData := os.Getenv("APPDATA")
	if appData == "" {
		home, _ := os.UserHomeDir()
		appData = filepath.Join(home, "AppData", "Roaming")
	}
	return filepath.Join(appData, "PhonePrint", "config.json")
}

func loadCfg() {
	data, err := os.ReadFile(cfgPath())
	if err == nil {
		_ = json.Unmarshal(data, &cfg)
	}
}

func saveCfg() error {
	if err := os.MkdirAll(filepath.Dir(cfgPath()), 0755); err != nil {
		return err
	}
	data, err := json.MarshalIndent(cfg, "", "  ")
	if err != nil {
		return err
	}
	return os.WriteFile(cfgPath(), data, 0600)
}

// ---------- password ----------

func hashPassword(pw string, salt []byte) string {
	h := sha256.Sum256(append(append([]byte{}, salt...), pw...))
	for i := 0; i < passIterations; i++ {
		buf := make([]byte, 0, len(h)+len(salt)+len(pw))
		buf = append(buf, h[:]...)
		buf = append(buf, salt...)
		buf = append(buf, pw...)
		h = sha256.Sum256(buf)
	}
	return hex.EncodeToString(h[:])
}

func checkPassword(pw string) bool {
	cfgMu.RLock()
	hash, saltHex := cfg.Hash, cfg.Salt
	cfgMu.RUnlock()

	if hash == "" {
		return false
	}
	salt, err := hex.DecodeString(saltHex)
	if err != nil {
		return false
	}
	return subtle.ConstantTimeCompare(
		[]byte(hashPassword(pw, salt)),
		[]byte(hash),
	) == 1
}

func printEnabled() bool {
	cfgMu.RLock()
	defer cfgMu.RUnlock()
	return cfg.Enabled && cfg.Hash != ""
}

// ---------- wrong-password lockout ----------

func isLocked(key string) bool {
	failMu.Lock()
	defer failMu.Unlock()
	fi, ok := fails[key]
	return ok && time.Now().Before(fi.lockedUntil)
}

func recordFail(key string, limit int) {
	failMu.Lock()
	defer failMu.Unlock()

	now := time.Now()
	fi := fails[key]
	if fi == nil || now.Sub(fi.first) > 10*time.Minute {
		fi = &failInfo{first: now}
		fails[key] = fi
	}

	fi.count++
	if fi.count >= limit {
		fi.lockedUntil = now.Add(5 * time.Minute)
		fi.count = 0
		fi.first = now
	}
}

func clearFail(key string) {
	failMu.Lock()
	defer failMu.Unlock()
	delete(fails, key)
}

func clientIP(r *http.Request) string {
	host, _, err := net.SplitHostPort(r.RemoteAddr)
	if err != nil {
		return r.RemoteAddr
	}
	return host
}

// ---------- network ----------

func getLANIP() string {
	ifaces, err := net.Interfaces()
	if err != nil {
		return ""
	}

	best, bestP := "", 0
	for _, ifc := range ifaces {
		if ifc.Flags&net.FlagLoopback != 0 || ifc.Flags&net.FlagUp == 0 {
			continue
		}

		addrs, err := ifc.Addrs()
		if err != nil {
			continue
		}

		for _, a := range addrs {
			ipn, ok := a.(*net.IPNet)
			if !ok {
				continue
			}
			ip4 := ipn.IP.To4()
			if ip4 == nil {
				continue
			}

			p := 0
			switch {
			case ip4[0] == 192 && ip4[1] == 168:
				p = 3
			case ip4[0] == 10:
				p = 2
			case ip4[0] == 172 && ip4[1] >= 16 && ip4[1] <= 31:
				p = 1
			}
			if p == 0 {
				continue
			}

			n := strings.ToLower(ifc.Name)
			if strings.Contains(n, "wi-fi") ||
				strings.Contains(n, "wifi") ||
				strings.Contains(n, "wlan") ||
				strings.Contains(n, "wireless") {
				p += 10
			}
			if p > bestP {
				best, bestP = ip4.String(), p
			}
		}
	}
	return best
}

func phoneURL() string {
	ip := getLANIP()
	if ip == "" {
		return ""
	}
	return fmt.Sprintf("http://%s:%d/", ip, port)
}

// ---------- Windows printers and printing ----------

func hideWindow(cmd *exec.Cmd) {
	cmd.SysProcAttr = &syscall.SysProcAttr{
		HideWindow:    true,
		CreationFlags: 0x08000000,
	}
}

func psCmd(ctx context.Context, script string, env []string) *exec.Cmd {
	u := utf16.Encode([]rune(script))
	b := make([]byte, 0, len(u)*2)
	for _, c := range u {
		b = append(b, byte(c), byte(c>>8))
	}

	cmd := exec.CommandContext(
		ctx, "powershell.exe",
		"-NoProfile", "-NonInteractive",
		"-EncodedCommand", base64.StdEncoding.EncodeToString(b),
	)
	if env != nil {
		cmd.Env = append(os.Environ(), env...)
	}
	hideWindow(cmd)
	return cmd
}

func isVirtualPrinter(name string) bool {
	n := strings.ToLower(name)
	for _, bad := range []string{"pdf", "xps", "onenote", "fax", "send to"} {
		if strings.Contains(n, bad) {
			return true
		}
	}
	return false
}

func listPrinters() ([]string, error) {
	ctx, cancel := context.WithTimeout(context.Background(), 20*time.Second)
	defer cancel()

	script := "[Console]::OutputEncoding=[System.Text.Encoding]::UTF8; " +
		"Get-Printer | Select-Object -ExpandProperty Name | ConvertTo-Json -Compress"

	out, err := psCmd(ctx, script, nil).Output()
	if err != nil {
		return nil, err
	}

	out = bytes.TrimSpace(bytes.TrimPrefix(out, []byte("\xef\xbb\xbf")))
	if len(out) == 0 {
		return []string{}, nil
	}

	var names []string
	if err := json.Unmarshal(out, &names); err != nil {
		var one string
		if err2 := json.Unmarshal(out, &one); err2 != nil {
			return nil, err
		}
		names = []string{one}
	}

	result := []string{}
	for _, n := range names {
		if n != "" && !isVirtualPrinter(n) {
			result = append(result, n)
		}
	}
	return result, nil
}

func findSumatra() string {
	var dirs []string

	if exe, err := os.Executable(); err == nil {
		dirs = append(dirs, filepath.Dir(exe))
	}
	if pf := os.Getenv("ProgramFiles"); pf != "" {
		dirs = append(dirs, filepath.Join(pf, "SumatraPDF"))
	}
	if la := os.Getenv("LOCALAPPDATA"); la != "" {
		dirs = append(dirs, filepath.Join(la, "SumatraPDF"))
	}

	for _, d := range dirs {
		matches, _ := filepath.Glob(filepath.Join(d, "SumatraPDF*.exe"))
		if len(matches) > 0 {
			return matches[0]
		}
	}
	return ""
}

const imagePrintScript = `$ErrorActionPreference = 'Stop'
Add-Type -AssemblyName System.Drawing

$global:img = [System.Drawing.Image]::FromFile($env:FB_FILE)
try {
    if ($global:img.PropertyIdList -contains 274) {
        $o = $global:img.GetPropertyItem(274).Value[0]
        if ($o -eq 3) {
            $global:img.RotateFlip([System.Drawing.RotateFlipType]::Rotate180FlipNone)
        } elseif ($o -eq 6) {
            $global:img.RotateFlip([System.Drawing.RotateFlipType]::Rotate90FlipNone)
        } elseif ($o -eq 8) {
            $global:img.RotateFlip([System.Drawing.RotateFlipType]::Rotate270FlipNone)
        }
    }

    $pd = New-Object System.Drawing.Printing.PrintDocument
    $pd.PrinterSettings.PrinterName = $env:FB_PRINTER

    if (-not $pd.PrinterSettings.IsValid) {
        throw 'Invalid printer'
    }

    $pd.PrinterSettings.Copies = [short][int]$env:FB_COPIES
    $pd.DefaultPageSettings.Color = ($env:FB_COLOR -eq 'color')
    $pd.DefaultPageSettings.Landscape = ($env:FB_ORIENTATION -eq 'landscape')

    if ($env:FB_PAPER -ne 'default') {
        $paper = $null
        foreach ($p in $pd.PrinterSettings.PaperSizes) {
            if ($p.PaperName -match ('(?i)^' + [regex]::Escape($env:FB_PAPER) + '$')) {
                $paper = $p
                break
            }
        }

        if ($null -eq $paper) {
            throw ('Paper size not supported by this printer: ' + $env:FB_PAPER)
        }
        $pd.DefaultPageSettings.PaperSize = $paper
    }

    $pd.add_PrintPage({
        param($s, $e)
        $b = $e.MarginBounds
        $r = [Math]::Min($b.Width / $global:img.Width, $b.Height / $global:img.Height)
        $w = [int]($global:img.Width * $r)
        $h = [int]($global:img.Height * $r)
        $x = $b.Left + [int](($b.Width - $w) / 2)
        $y = $b.Top + [int](($b.Height - $h) / 2)

        $e.Graphics.DrawImage($global:img, $x, $y, $w, $h)
        $e.HasMorePages = $false
    })

    $pd.Print()
} finally {
    $global:img.Dispose()
}`

func printFile(
	printer, path, kind, paper, orientation, colorMode string,
	copies int,
) error {
	ctx, cancel := context.WithTimeout(context.Background(), 120*time.Second)
	defer cancel()

	env := []string{
		"FB_FILE=" + path,
		"FB_PRINTER=" + printer,
		"FB_PAPER=" + paper,
		"FB_ORIENTATION=" + orientation,
		"FB_COLOR=" + colorMode,
		"FB_COPIES=" + strconv.Itoa(copies),
	}

	var cmd *exec.Cmd

	switch kind {
	case "image":
		cmd = psCmd(ctx, imagePrintScript, env)

	case "pdf":
		sumatra := findSumatra()
		if sumatra == "" {
			return fmt.Errorf("SumatraPDF was not found; install it to print PDFs with the selected settings")
		}

		settings := []string{}
		if paper != "default" {
			settings = append(settings, "paper="+paper)
		}
		settings = append(settings, orientation)

		if colorMode == "bw" {
			settings = append(settings, "monochrome")
		} else {
			settings = append(settings, "color")
		}
		settings = append(settings, fmt.Sprintf("%dx", copies))

		cmd = exec.CommandContext(
			ctx, sumatra,
			"-print-to", printer,
			"-print-settings", strings.Join(settings, ","),
			"-silent", path,
		)
		hideWindow(cmd)

	default:
		return fmt.Errorf("unsupported file type")
	}

	out, err := cmd.CombinedOutput()
	if err != nil {
		return fmt.Errorf("%v: %s", err, strings.TrimSpace(string(out)))
	}
	return nil
}

func sniffPrintType(h []byte) (string, string) {
	switch {
	case bytes.HasPrefix(h, []byte("%PDF")):
		return "pdf", ".pdf"
	case len(h) >= 3 && h[0] == 0xFF && h[1] == 0xD8 && h[2] == 0xFF:
		return "image", ".jpg"
	case bytes.HasPrefix(h, []byte("\x89PNG")):
		return "image", ".png"
	case bytes.HasPrefix(h, []byte("BM")):
		return "image", ".bmp"
	}
	return "", ""
}

// ---------- helpers ----------

func writeJSON(w http.ResponseWriter, status int, data interface{}) {
	w.Header().Set("Content-Type", "application/json; charset=utf-8")
	w.Header().Set("Cache-Control", "no-store")
	w.WriteHeader(status)
	_ = json.NewEncoder(w).Encode(data)
}

func openBrowser(u string) {
	cmd := exec.Command("rundll32", "url.dll,FileProtocolHandler", u)
	hideWindow(cmd)
	_ = cmd.Start()
}

func adminOnly(h http.HandlerFunc) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		ip := net.ParseIP(clientIP(r))
		if ip == nil || !ip.IsLoopback() {
			http.NotFound(w, r)
			return
		}
		if r.Host != fmt.Sprintf("localhost:%d", port) &&
			r.Host != fmt.Sprintf("127.0.0.1:%d", port) {
			http.NotFound(w, r)
			return
		}
		if r.Method == http.MethodPost {
			if o := r.Header.Get("Origin"); o != "" && o != "http://"+r.Host {
				http.Error(w, "Forbidden", http.StatusForbidden)
				return
			}
			if r.Header.Get("X-Requested-With") != "PhonePrint" {
				http.Error(w, "Forbidden", http.StatusForbidden)
				return
			}
		}
		h(w, r)
	}
}

// ---------- PC settings handlers ----------

func handleAdminPage(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "text/html; charset=utf-8")
	w.Header().Set("Cache-Control", "no-store")
	_, _ = w.Write([]byte(adminHTML))
}

func handleAdminStatus(w http.ResponseWriter, r *http.Request) {
	cfgMu.RLock()
	defer cfgMu.RUnlock()

	writeJSON(w, http.StatusOK, map[string]interface{}{
		"enabled":     cfg.Enabled,
		"hasPassword": cfg.Hash != "",
		"url":         phoneURL(),
	})
}

func handleAdminEnable(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodPost {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	var req struct {
		Enabled bool `json:"enabled"`
	}
	r.Body = http.MaxBytesReader(w, r.Body, 1024)
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		writeJSON(w, http.StatusBadRequest, map[string]string{"error": "Bad request"})
		return
	}

	cfgMu.Lock()
	defer cfgMu.Unlock()

	if req.Enabled && cfg.Hash == "" {
		writeJSON(w, http.StatusBadRequest, map[string]string{
			"error": "Set a 5-digit password first",
		})
		return
	}

	cfg.Enabled = req.Enabled
	if err := saveCfg(); err != nil {
		writeJSON(w, http.StatusInternalServerError, map[string]string{
			"error": "Could not save settings",
		})
		return
	}
	writeJSON(w, http.StatusOK, map[string]bool{"ok": true})
}

func handleAdminPassword(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodPost {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	var req struct {
		Password string `json:"password"`
	}
	r.Body = http.MaxBytesReader(w, r.Body, 1024)
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil ||
		!pinRe.MatchString(req.Password) {
		writeJSON(w, http.StatusBadRequest, map[string]string{
			"error": "Password must be exactly 5 digits",
		})
		return
	}

	salt := make([]byte, 16)
	if _, err := rand.Read(salt); err != nil {
		writeJSON(w, http.StatusInternalServerError, map[string]string{
			"error": "Could not save password",
		})
		return
	}

	cfgMu.Lock()
	defer cfgMu.Unlock()

	cfg.Salt = hex.EncodeToString(salt)
	cfg.Hash = hashPassword(req.Password, salt)
	if err := saveCfg(); err != nil {
		writeJSON(w, http.StatusInternalServerError, map[string]string{
			"error": "Could not save settings",
		})
		return
	}
	writeJSON(w, http.StatusOK, map[string]bool{"ok": true})
}

func handleAdminQR(w http.ResponseWriter, r *http.Request) {
	u := phoneURL()
	if u == "" {
		http.NotFound(w, r)
		return
	}

	png, err := qrcode.Encode(u, qrcode.Medium, 256)
	if err != nil {
		http.Error(w, "QR error", http.StatusInternalServerError)
		return
	}
	w.Header().Set("Content-Type", "image/png")
	w.Header().Set("Cache-Control", "no-store")
	_, _ = w.Write(png)
}

// ---------- phone handlers ----------

func handlePhonePage(w http.ResponseWriter, r *http.Request) {
	if r.URL.Path != "/" {
		http.NotFound(w, r)
		return
	}
	w.Header().Set("Content-Type", "text/html; charset=utf-8")
	w.Header().Set("Cache-Control", "no-store")
	_, _ = w.Write([]byte(phoneHTML))
}

func handlePhoneStatus(w http.ResponseWriter, r *http.Request) {
	writeJSON(w, http.StatusOK, map[string]bool{"enabled": printEnabled()})
}

func handlePrinters(w http.ResponseWriter, r *http.Request) {
	if !printEnabled() {
		writeJSON(w, http.StatusForbidden, map[string]string{
			"error": "Printing is turned off",
			"code":  "off",
		})
		return
	}

	printers, err := listPrinters()
	if err != nil {
		log.Printf("Failed to list printers: %v", err)
		writeJSON(w, http.StatusInternalServerError, map[string]string{
			"error": "Could not read printers",
			"code":  "failed",
		})
		return
	}
	writeJSON(w, http.StatusOK, map[string]interface{}{"printers": printers})
}

func handlePrint(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodPost {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}
	if !printEnabled() {
		writeJSON(w, http.StatusForbidden, map[string]string{
			"error": "Printing is turned off",
			"code":  "off",
		})
		return
	}

	ip := clientIP(r)
	if isLocked(ip) || isLocked("*") {
		writeJSON(w, http.StatusTooManyRequests, map[string]string{
			"error": "Too many wrong attempts",
			"code":  "locked",
		})
		return
	}

	// Check the password before reading the uploaded file.
	if !checkPassword(r.Header.Get("X-Print-Password")) {
		recordFail(ip, ipFailLimit)
		recordFail("*", globalFailLim)
		log.Printf("Wrong print password (source IP: %s)", ip)
		writeJSON(w, http.StatusUnauthorized, map[string]string{
			"error": "Wrong password",
			"code":  "password",
		})
		return
	}
	clearFail(ip)

	printer, err := url.QueryUnescape(r.Header.Get("X-Printer"))
	if err != nil {
		writeJSON(w, http.StatusBadRequest, map[string]string{
			"error": "Invalid printer name",
			"code":  "printer",
		})
		return
	}

	printers, err := listPrinters()
	if err != nil {
		log.Printf("Failed to list printers: %v", err)
		writeJSON(w, http.StatusInternalServerError, map[string]string{
			"error": "Could not read printers",
			"code":  "failed",
		})
		return
	}

	found := false
	for _, p := range printers {
		if p == printer {
			found = true
			break
		}
	}
	if !found {
		writeJSON(w, http.StatusBadRequest, map[string]string{
			"error": "Printer not available",
			"code":  "printer",
		})
		return
	}

	paper := r.Header.Get("X-Paper")
	orientation := r.Header.Get("X-Orientation")
	colorMode := r.Header.Get("X-Color-Mode")
	copiesText := r.Header.Get("X-Copies")

	switch paper {
	case "default", "A4", "A5", "Legal", "Letter":
	default:
		writeJSON(w, http.StatusBadRequest, map[string]string{
			"error": "Invalid paper size",
			"code":  "settings",
		})
		return
	}

	if orientation != "portrait" && orientation != "landscape" {
		writeJSON(w, http.StatusBadRequest, map[string]string{
			"error": "Invalid orientation",
			"code":  "settings",
		})
		return
	}

	if colorMode != "color" && colorMode != "bw" {
		writeJSON(w, http.StatusBadRequest, map[string]string{
			"error": "Invalid color mode",
			"code":  "settings",
		})
		return
	}

	copies, err := strconv.Atoi(copiesText)
	if err != nil || copies < 1 || copies > 99 {
		writeJSON(w, http.StatusBadRequest, map[string]string{
			"error": "Copies must be between 1 and 99",
			"code":  "settings",
		})
		return
	}

	r.Body = http.MaxBytesReader(w, r.Body, maxPrintBytes)
	head := make([]byte, 8)
	n, _ := io.ReadFull(r.Body, head)
	head = head[:n]

	kind, ext := sniffPrintType(head)
	if kind == "" {
		writeJSON(w, http.StatusUnsupportedMediaType, map[string]string{
			"error": "Only PDF and photos can be printed",
			"code":  "type",
		})
		return
	}

	tmp, err := os.CreateTemp("", "phoneprint-*"+ext)
	if err != nil {
		writeJSON(w, http.StatusInternalServerError, map[string]string{
			"error": "Printing failed",
			"code":  "failed",
		})
		return
	}

	tmpPath := tmp.Name()
	remove := func() { _ = os.Remove(tmpPath) }

	_, werr := tmp.Write(head)
	if werr == nil {
		_, werr = io.Copy(tmp, r.Body)
	}
	closeErr := tmp.Close()
	if werr == nil {
		werr = closeErr
	}
	if werr != nil {
		remove()
		log.Printf("Failed to receive print file: %v", werr)
		writeJSON(w, http.StatusBadRequest, map[string]string{
			"error": "Upload failed",
			"code":  "upload",
		})
		return
	}

	printMu.Lock()
	perr := printFile(
		printer, tmpPath, kind,
		paper, orientation, colorMode, copies,
	)
	printMu.Unlock()

	remove()

	if perr != nil {
		log.Printf("Print failed on %q: %v", printer, perr)
		writeJSON(w, http.StatusInternalServerError, map[string]string{
			"error": "Printing failed: " + perr.Error(),
			"code":  "failed",
		})
		return
	}

	log.Printf(
		"Printed %s on %q (paper=%s, orientation=%s, copies=%d, color=%s)",
		kind, printer, paper, orientation, copies, colorMode,
	)
	writeJSON(w, http.StatusOK, map[string]bool{"success": true})
}

// ---------- main ----------

func main() {
	loadCfg()
	adminURL := fmt.Sprintf("http://localhost:%d/admin", port)

	ln, err := net.Listen("tcp", fmt.Sprintf("0.0.0.0:%d", port))
	if err != nil {
		fmt.Printf("Port %d is already in use. Phone Print may already be running.\n", port)
		fmt.Println("Opening the settings page...")
		openBrowser(adminURL)
		time.Sleep(3 * time.Second)
		return
	}

	mux := http.NewServeMux()
	mux.HandleFunc("/", handlePhonePage)
	mux.HandleFunc("/api/status", handlePhoneStatus)
	mux.HandleFunc("/api/printers", handlePrinters)
	mux.HandleFunc("/api/print", handlePrint)
	mux.HandleFunc("/admin", adminOnly(handleAdminPage))
	mux.HandleFunc("/admin/api/status", adminOnly(handleAdminStatus))
	mux.HandleFunc("/admin/api/enable", adminOnly(handleAdminEnable))
	mux.HandleFunc("/admin/api/password", adminOnly(handleAdminPassword))
	mux.HandleFunc("/admin/qr.png", adminOnly(handleAdminQR))

	srv := &http.Server{
		Handler:           mux,
		ReadHeaderTimeout: 10 * time.Second,
		MaxHeaderBytes:    1 << 20,
	}

	fmt.Println("Phone Print is running.")
	fmt.Println("Settings page: " + adminURL)
	if u := phoneURL(); u != "" {
		fmt.Println("Phone address: " + u)
	}
	fmt.Println("Close this window to stop the program.")

	go func() {
		time.Sleep(500 * time.Millisecond)
		openBrowser(adminURL)
	}()

	log.Fatal(srv.Serve(ln))
}

// ---------- pages ----------

const adminHTML = `<!DOCTYPE html>
<html lang="en"><head><meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Phone Print - Settings</title>
<style>
*{box-sizing:border-box;margin:0;padding:0}
body{font-family:Segoe UI,Arial,sans-serif;background:#0f172a;color:#e2e8f0;padding:24px}
.c{max-width:460px;margin:0 auto}
h1{color:#38bdf8;text-align:center;margin-bottom:20px}
.card{background:#1e293b;border-radius:10px;padding:16px;margin-bottom:16px}
.card h2{font-size:1rem;margin-bottom:10px;color:#94a3b8}
.qr{text-align:center}
.qr img{background:#fff;padding:10px;border-radius:8px;width:240px;height:240px}
.url{word-break:break-all;margin-top:8px;font-size:.9rem;color:#38bdf8}
label{display:flex;align-items:center;gap:10px;font-size:1rem}
input[type=checkbox]{width:20px;height:20px}
input[type=password]{width:100%;padding:10px;border-radius:6px;border:1px solid #475569;background:#0f172a;color:#e2e8f0;font-size:1rem;margin:8px 0}
button{width:100%;padding:10px;border:none;border-radius:6px;background:#2563eb;color:#fff;font-size:1rem;cursor:pointer}
.msg{margin-top:8px;font-size:.9rem;min-height:1.2em}
.ok{color:#4ade80}.err{color:#f87171}
.small{font-size:.8rem;color:#94a3b8;margin-top:8px}
</style></head><body><div class="c">
<h1>Phone Print</h1>
<div class="card qr"><h2>Scan with your phone</h2>
<img id="qr" alt="QR code"><div class="url" id="url"></div></div>
<div class="card"><h2>Printing</h2>
<label><input type="checkbox" id="en"> Allow printing from phones</label>
<div class="small" id="pwstate"></div><div class="msg" id="msg1"></div></div>
<div class="card"><h2>Print password (5 digits)</h2>
<input type="password" id="pw" maxlength="5" inputmode="numeric" placeholder="5 digits" autocomplete="off">
<button id="save">Save password</button><div class="msg" id="msg2"></div></div>
<div class="small">Only PDF files and photos (JPG, PNG, BMP) can be printed. Close the black console window to stop Phone Print.</div>
</div>
<script>
var H={'X-Requested-With':'PhonePrint','Content-Type':'application/json'};
function $(i){return document.getElementById(i)}
function load(){
 fetch('/admin/api/status').then(function(r){return r.json()}).then(function(s){
   $('en').checked=s.enabled;
   $('pwstate').textContent=s.hasPassword?'Password is set.':'Set a password first.';
   $('url').textContent=s.url||'No Wi-Fi address found';
   if(s.url){$('qr').src='/admin/qr.png?'+Date.now();$('qr').style.display='inline-block'}
   else{$('qr').style.display='none'}
 }).catch(function(){});
}
$('en').onchange=function(){
 var want=$('en').checked;
 fetch('/admin/api/enable',{method:'POST',headers:H,body:JSON.stringify({enabled:want})})
 .then(function(r){return r.json().then(function(d){return{ok:r.ok,d:d}})})
 .then(function(x){
   if(x.ok){$('msg1').className='msg ok';$('msg1').textContent=want?'Printing is ON.':'Printing is OFF.'}
   else{$('msg1').className='msg err';$('msg1').textContent=x.d.error||'Error';load()}
 }).catch(function(){$('msg1').className='msg err';$('msg1').textContent='Network error.'});
};
$('save').onclick=function(){
 fetch('/admin/api/password',{method:'POST',headers:H,body:JSON.stringify({password:$('pw').value})})
 .then(function(r){return r.json().then(function(d){return{ok:r.ok,d:d}})})
 .then(function(x){
   if(x.ok){$('pw').value='';$('msg2').className='msg ok';$('msg2').textContent='Password saved.';load()}
   else{$('msg2').className='msg err';$('msg2').textContent=x.d.error||'Error'}
 }).catch(function(){$('msg2').className='msg err';$('msg2').textContent='Network error.'});
};
load();
</script></body></html>`

const phoneHTML = `<!DOCTYPE html>
<html lang="en"><head><meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1, maximum-scale=1">
<title>Phone Print</title>
<style>
*{box-sizing:border-box;margin:0;padding:0}
body{font-family:-apple-system,BlinkMacSystemFont,Segoe UI,Roboto,sans-serif;background:#0f172a;color:#e2e8f0;padding:20px;min-height:100vh}
.c{max-width:480px;margin:0 auto}
h1{font-size:1.5rem;text-align:center;color:#38bdf8;margin-bottom:20px}
.pick{display:block;text-align:center;background:#7c3aed;color:#fff;padding:16px;border-radius:8px;font-size:1.1rem;margin-bottom:6px}
.pick input{display:none}
.hint{color:#94a3b8;font-size:.8rem;text-align:center;margin-bottom:10px}
#fname{text-align:center;font-size:.9rem;margin-bottom:12px;word-break:break-all}
select,input[type=password],input[type=number]{width:100%;padding:12px;margin-bottom:10px;border-radius:8px;background:#1e293b;color:#e2e8f0;border:1px solid #475569;font-size:1rem}
.settings{background:#1e293b;border:1px solid #334155;border-radius:8px;padding:12px;margin:4px 0 12px}
.settings label{display:block;font-size:.9rem;color:#cbd5e1;margin:0 0 6px}
.settings select,.settings input{margin-bottom:12px}
.settings input:last-child,.settings select:last-child{margin-bottom:0}
button{display:block;width:100%;padding:14px;border:none;border-radius:8px;background:#16a34a;color:#fff;font-size:1.1rem}
button:disabled{background:#334155;color:#64748b}
#st{text-align:center;margin-top:14px;font-size:.95rem;min-height:1.3em;overflow-wrap:anywhere}
#off{text-align:center;color:#f87171;margin-top:30px}
</style></head><body><div class="c">
<h1>Phone Print</h1>
<div id="off" style="display:none">Printing is turned off on the PC.</div>
<div id="form" style="display:none">
<label class="pick">Choose file to print<input type="file" id="file" accept="application/pdf,image/jpeg,image/png,image/bmp"></label>
<div class="hint">PDF or photo (JPG, PNG, BMP), maximum 100 MB</div>
<div id="fname"></div>

<label for="sel">Printer</label>
<select id="sel"></select>

<div class="settings">
<label for="paper">Paper size</label>
<select id="paper">
<option value="default">Printer default</option>
<option value="A4">A4</option>
<option value="A5">A5</option>
<option value="Legal">Legal</option>
<option value="Letter">Letter</option>
</select>

<label for="orientation">Orientation</label>
<select id="orientation">
<option value="portrait">Portrait</option>
<option value="landscape">Landscape</option>
</select>

<label for="copies">Number of copies (1–99)</label>
<input type="number" id="copies" min="1" max="99" step="1" value="1" inputmode="numeric">

<label for="color">Color mode</label>
<select id="color">
<option value="color">Color</option>
<option value="bw">Black &amp; White</option>
</select>
</div>

<label for="pw">5-digit password</label>
<input type="password" id="pw" maxlength="5" inputmode="numeric" pattern="[0-9]*" placeholder="5-digit password" autocomplete="off">
<button id="go">Print</button>
<div id="st"></div>
</div></div>
<script>
function $(i){return document.getElementById(i)}
function say(c,t){$('st').style.color=c;$('st').textContent=t}
function getJSON(u,cb){
 var x=new XMLHttpRequest();x.open('GET',u);
 x.onload=function(){var d={};try{d=JSON.parse(x.responseText)}catch(e){}cb(x.status,d)};
 x.onerror=function(){cb(0,{})};x.send();
}
function loadPrinters(){
 getJSON('/api/printers',function(code,d){
   var keep=$('sel').value;$('sel').innerHTML='';
   if(code!==200||!d.printers||!d.printers.length){
     var o=document.createElement('option');o.value='';o.textContent='No printers found on the PC';$('sel').appendChild(o);return
   }
   d.printers.forEach(function(p){
     var o=document.createElement('option');o.value=p;o.textContent=p;
     if(p===keep)o.selected=true;
     $('sel').appendChild(o);
   });
 });
}
function refresh(){
 getJSON('/api/status',function(code,d){
   var on=(code===200&&d.enabled);
   $('off').style.display=on?'none':'block';
   if(on&&$('form').style.display==='none'){$('form').style.display='block';loadPrinters()}
   if(!on){$('form').style.display='none'}
 });
}
$('file').onchange=function(){
 $('fname').textContent=$('file').files.length?$('file').files[0].name:'';
 $('st').textContent='';loadPrinters();
};
$('go').onclick=function(){
 if(!$('file').files.length){say('#f87171','Choose a file first.');return}
 var f=$('file').files[0];
 if(f.size>100*1024*1024){say('#f87171','File is too large (max 100 MB).');return}
 if(!/^[0-9]{5}$/.test($('pw').value)){say('#f87171','Enter the 5-digit password.');return}
 if(!$('sel').value){say('#f87171','No printer selected.');return}

 var copies=Number($('copies').value);
 if(!Number.isInteger(copies)||copies<1||copies>99){
   say('#f87171','Copies must be a whole number between 1 and 99.');return
 }

 $('go').disabled=true;
 var x=new XMLHttpRequest();x.open('POST','/api/print');
 x.setRequestHeader('X-Print-Password',$('pw').value);
 x.setRequestHeader('X-Printer',encodeURIComponent($('sel').value));
 x.setRequestHeader('X-Paper',$('paper').value);
 x.setRequestHeader('X-Orientation',$('orientation').value);
 x.setRequestHeader('X-Copies',String(copies));
 x.setRequestHeader('X-Color-Mode',$('color').value);
 x.setRequestHeader('Content-Type','application/octet-stream');

 x.upload.onprogress=function(e){
   if(e.lengthComputable)say('#38bdf8','Sending... '+Math.round(e.loaded/e.total*100)+'%');
 };
 x.onload=function(){
   $('go').disabled=false;
   var d={};try{d=JSON.parse(x.responseText)}catch(e){}
   if(x.status===200){
     $('pw').value='';$('file').value='';$('fname').textContent='';
     say('#4ade80','Sent to the printer.');
   }else if(x.status===401){
     say('#f87171','Wrong password.');
   }else if(x.status===429){
     say('#f87171','Too many wrong attempts. Try again in a few minutes.');
   }else if(x.status===403){
     say('#f87171','Printing is turned off on the PC.');
   }else if(x.status===415){
     say('#f87171','Only PDF and photos (JPG, PNG, BMP) can be printed.');
   }else{
     say('#f87171',d.error||'Printing failed. Please check the printer.');
   }
 };
 x.onerror=function(){$('go').disabled=false;say('#f87171','Network error.')};
 say('#38bdf8','Sending...');
 x.send(f);
};
refresh();setInterval(refresh,10000);
</script></body></html>`
