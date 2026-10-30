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
	"image/jpeg"
	"io"
	"log"
	"math"
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

	"github.com/pdfcpu/pdfcpu/pkg/api"
	qrcode "github.com/skip2/go-qrcode"
)

const (
	port           = 8081
	passIterations = 200000
	maxPrintBytes  = 1 << 30
	ipFailLimit    = 5
	globalFailLim  = 20
	sessionIdle    = 30 * time.Minute
	maxSessions    = 100

	// "Print all together" limits
	maxStaged    = 50               // files waiting for a batch at the same time
	stageTTL     = 30 * time.Minute // uploaded batch files are deleted after this
)

var (
	pinRe   = regexp.MustCompile(`^[0-9]{4}$`)
	pagesRe = regexp.MustCompile(`^[0-9]{1,5}(-[0-9]{1,5})?(,[0-9]{1,5}(-[0-9]{1,5})?)*$`)

	printMu sync.Mutex
	failMu  sync.Mutex
	fails   = map[string]*failInfo{}
	cfgMu   sync.RWMutex
	cfg     config

	sessMu   sync.Mutex
	sessions = map[string]time.Time{}

	capsMu    sync.Mutex
	capsCache = map[string]capsEntry{}

	stageMu sync.Mutex
	staging = map[string]*staged{}
)

type config struct {
	Enabled bool   `json:"enabled"`
	Hash    string `json:"hash,omitempty"`
	Salt    string `json:"salt,omitempty"`
}

type failInfo struct {
	count      int
	first      time.Time
	strikes    int
	lastStrike time.Time
	lockedTill time.Time
}

type paperInfo struct {
	ID    string  `json:"id"`
	Label string  `json:"label"`
	W     float64 `json:"w"`
	H     float64 `json:"h"`
}

type sourceInfo struct {
	ID    string `json:"id"`
	Label string `json:"label"`
}

// the driver's own default settings (what you see in Printing Preferences)
type capsDefaults struct {
	Duplex string `json:"duplex"`
	Paper  string `json:"paper"`
	Source string `json:"source"`
}

type printerCaps struct {
	Detected  bool         `json:"detected"`
	Color     bool         `json:"color"`
	Mono      bool         `json:"mono"`
	Duplex    bool         `json:"duplex"`
	MaxCopies int          `json:"maxCopies"`
	Papers    []paperInfo  `json:"papers"`
	Sources   []sourceInfo `json:"sources"`
	Defaults  capsDefaults `json:"defaults"`
}

type capsEntry struct {
	caps printerCaps
	at   time.Time
}

type printOpts struct {
	Copies      int    `json:"copies"`
	Color       string `json:"color"`
	Paper       string `json:"paper"`
	Duplex      string `json:"duplex"`
	Orientation string `json:"orientation"`
	Scale       string `json:"scale"`
	Pages       string `json:"pages"`
	Source      string `json:"source"`
}

// a file uploaded by the phone that is waiting for "Print all together"
type staged struct {
	path    string
	kind    string
	session string
	at      time.Time
}

var paperOrder = []string{"ISOA3", "ISOA4", "ISOA5", "ISOA6", "NorthAmericaLetter", "NorthAmericaLegal", "NorthAmericaTabloid", "NorthAmericaStatement"}

var paperByEnum = map[string]paperInfo{
	"ISOA3":                 {ID: "A3", Label: "A3", W: 297, H: 420},
	"ISOA4":                 {ID: "A4", Label: "A4", W: 210, H: 297},
	"ISOA5":                 {ID: "A5", Label: "A5", W: 148, H: 210},
	"ISOA6":                 {ID: "A6", Label: "A6", W: 105, H: 148},
	"NorthAmericaLetter":    {ID: "letter", Label: "Letter", W: 215.9, H: 279.4},
	"NorthAmericaLegal":     {ID: "legal", Label: "Legal", W: 215.9, H: 355.6},
	"NorthAmericaTabloid":   {ID: "tabloid", Label: "Tabloid", W: 279.4, H: 431.8},
	"NorthAmericaStatement": {ID: "statement", Label: "Statement", W: 139.7, H: 215.9},
}

// ---------- settings file ----------

func cfgPath() string {
	appData := os.Getenv("APPDATA")
	if appData == "" {
		home, _ := os.UserHomeDir()
		appData = filepath.Join(home, "AppData", "Roaming")
	}
	// folder name kept the same so the saved PIN is not lost
	return filepath.Join(appData, "PhonePrint", "config.json")
}

func loadCfg() {
	data, err := os.ReadFile(cfgPath())
	if err == nil {
		json.Unmarshal(data, &cfg)
	}
}

// saveCfg must be called while holding cfgMu
func saveCfg() error {
	os.MkdirAll(filepath.Dir(cfgPath()), 0755)
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
	return subtle.ConstantTimeCompare([]byte(hashPassword(pw, salt)), []byte(hash)) == 1
}

func printEnabled() bool {
	cfgMu.RLock()
	defer cfgMu.RUnlock()
	return cfg.Enabled && cfg.Hash != ""
}

// ---------- sessions (after the PIN is entered) ----------

func newSession() string {
	b := make([]byte, 16)
	rand.Read(b)
	tok := hex.EncodeToString(b)
	sessMu.Lock()
	defer sessMu.Unlock()
	now := time.Now()
	for k, exp := range sessions {
		if now.After(exp) {
			delete(sessions, k)
		}
	}
	if len(sessions) >= maxSessions {
		oldest := ""
		var oldestT time.Time
		for k, exp := range sessions {
			if oldest == "" || exp.Before(oldestT) {
				oldest, oldestT = k, exp
			}
		}
		delete(sessions, oldest)
	}
	sessions[tok] = now.Add(sessionIdle)
	return tok
}

func validSession(tok string) bool {
	if len(tok) != 32 {
		return false
	}
	sessMu.Lock()
	defer sessMu.Unlock()
	exp, ok := sessions[tok]
	if !ok || time.Now().After(exp) {
		delete(sessions, tok)
		return false
	}
	sessions[tok] = time.Now().Add(sessionIdle)
	return true
}

func clearSessions() {
	sessMu.Lock()
	sessions = map[string]time.Time{}
	sessMu.Unlock()
}

// ---------- wrong-PIN lockout (gets longer with repeated failures) ----------

func isLocked(key string) bool {
	failMu.Lock()
	defer failMu.Unlock()
	fi, ok := fails[key]
	return ok && time.Now().Before(fi.lockedTill)
}

func recordFail(key string, limit int) {
	failMu.Lock()
	defer failMu.Unlock()
	now := time.Now()
	fi := fails[key]
	if fi == nil {
		fi = &failInfo{first: now}
		fails[key] = fi
	}
	if now.Sub(fi.first) > 10*time.Minute {
		fi.count = 0
		fi.first = now
	}
	if fi.strikes > 0 && now.Sub(fi.lastStrike) > time.Hour {
		fi.strikes = 0
	}
	fi.count++
	if fi.count >= limit {
		n := fi.strikes
		if n > 6 {
			n = 6
		}
		fi.lockedTill = now.Add((5 * time.Minute) << uint(n))
		fi.strikes++
		fi.lastStrike = now
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
			if strings.Contains(n, "wi-fi") || strings.Contains(n, "wifi") || strings.Contains(n, "wlan") || strings.Contains(n, "wireless") {
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

// ---------- Windows printers, features and printing ----------

func hideWindow(cmd *exec.Cmd) {
	cmd.SysProcAttr = &syscall.SysProcAttr{HideWindow: true, CreationFlags: 0x08000000}
}

func psCmd(ctx context.Context, script string, env []string) *exec.Cmd {
	u := utf16.Encode([]rune(script))
	b := make([]byte, 0, len(u)*2)
	for _, c := range u {
		b = append(b, byte(c), byte(c>>8))
	}
	cmd := exec.CommandContext(ctx, "powershell.exe", "-NoProfile", "-NonInteractive",
		"-EncodedCommand", base64.StdEncoding.EncodeToString(b))
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

func printerExists(name string) (bool, error) {
	list, err := listPrinters()
	if err != nil {
		return false, err
	}
	for _, p := range list {
		if p == name {
			return true, nil
		}
	}
	return false, nil
}

const capsScript = `$ErrorActionPreference = 'Stop'
Add-Type -AssemblyName System.Printing
$name = $env:FB_PRINTER
$q = $null
try {
  $srv = New-Object System.Printing.LocalPrintServer
  $q = $srv.GetPrintQueue($name)
} catch {
  $q = $null
}
if ($q -eq $null -and $name.StartsWith('\\')) {
  $parts = $name.TrimStart([char]92).Split([char[]]@([char]92), 2)
  $srv2 = New-Object System.Printing.PrintServer(('\\' + $parts[0]))
  $q = $srv2.GetPrintQueue($parts[1])
}
$c = $q.GetPrintCapabilities()
$o = [ordered]@{}
$o.color = [bool]($c.OutputColorCapability -contains [System.Printing.OutputColor]::Color)
$o.mono = [bool](($c.OutputColorCapability -contains [System.Printing.OutputColor]::Monochrome) -or ($c.OutputColorCapability -contains [System.Printing.OutputColor]::Grayscale))
$o.duplex = [bool](($c.DuplexingCapability -contains [System.Printing.Duplexing]::TwoSidedLongEdge) -or ($c.DuplexingCapability -contains [System.Printing.Duplexing]::TwoSidedShortEdge))
$o.maxCopies = $c.MaxCopyCount
$list = @()
foreach ($m in $c.PageMediaSizeCapability) {
  if ($m.PageMediaSizeName -ne $null) { $list += [string]$m.PageMediaSizeName }
}
$o.papers = $list
try {
  Add-Type -AssemblyName System.Drawing
  $ps = New-Object System.Drawing.Printing.PrinterSettings
  $ps.PrinterName = $name
  if ($ps.IsValid -and $ps.CanDuplex) { $o.duplex = $true }
  $fl = @()
  foreach ($s in $ps.PaperSizes) { $fl += @{ n = [string]$s.PaperName; w = [int]$s.Width; h = [int]$s.Height } }
  $o.forms = $fl
  $fs = @()
  foreach ($s in $ps.PaperSources) { $fs += @{ n = [string]$s.SourceName; k = [int]$s.RawKind } }
  $o.sources = $fs
  $dp = $ps.DefaultPageSettings
  $o.defDuplex = [string]$ps.Duplex
  $o.defW = [int]$dp.PaperSize.Width
  $o.defH = [int]$dp.PaperSize.Height
  $o.defSrc = [int]$dp.PaperSource.RawKind
} catch {}
$o | ConvertTo-Json -Compress`

func defaultCaps() printerCaps {
	return printerCaps{
		Detected: false, Color: true, Mono: true, Duplex: true, MaxCopies: 999, Sources: []sourceInfo{},
		Papers: []paperInfo{paperByEnum["ISOA4"], paperByEnum["NorthAmericaLetter"]},
	}
}

func queryCaps(printer string) printerCaps {
	ctx, cancel := context.WithTimeout(context.Background(), 25*time.Second)
	defer cancel()
	out, err := psCmd(ctx, capsScript, []string{"FB_PRINTER=" + printer}).Output()
	if err != nil {
		log.Printf("Could not read features of %q: %v", printer, err)
		return defaultCaps()
	}
	out = bytes.TrimSpace(bytes.TrimPrefix(out, []byte("\xef\xbb\xbf")))
	var raw map[string]interface{}
	if err := json.Unmarshal(out, &raw); err != nil {
		log.Printf("Could not parse features of %q: %v", printer, err)
		return defaultCaps()
	}
	c := printerCaps{Detected: true, MaxCopies: 999}
	c.Color, _ = raw["color"].(bool)
	c.Mono, _ = raw["mono"].(bool)
	c.Duplex, _ = raw["duplex"].(bool)
	if f, ok := raw["maxCopies"].(float64); ok {
		m := int(f)
		if m < 99 {
			m = 99
		}
		if m > 999 {
			m = 999
		}
		c.MaxCopies = m
	}
	have := map[string]bool{}
	switch v := raw["papers"].(type) {
	case []interface{}:
		for _, it := range v {
			if s, ok := it.(string); ok {
				have[s] = true
			}
		}
	case string:
		have[v] = true
	}
	c.Papers = []paperInfo{}
	for _, name := range paperOrder {
		if have[name] {
			c.Papers = append(c.Papers, paperByEnum[name])
		}
	}
	// every paper size known to the Windows print queue, including custom sizes
	// added in the printer driver (for example a custom A6)
	if fl, ok := raw["forms"].([]interface{}); ok {
		have2 := map[string]bool{}
		for _, p := range c.Papers {
			have2[p.ID] = true
		}
		customN := 0
		for _, it := range fl {
			m, ok := it.(map[string]interface{})
			if !ok {
				continue
			}
			name, _ := m["n"].(string)
			wf, _ := m["w"].(float64)
			hf, _ := m["h"].(float64)
			wmm, hmm := wf*0.254, hf*0.254
			if wmm < 20 || hmm < 20 {
				continue
			}
			if std, found := matchStdPaper(wmm, hmm); found {
				if !have2[std.ID] {
					c.Papers = append(c.Papers, std)
					have2[std.ID] = true
				}
				continue
			}
			if customN >= 30 || name == "" {
				continue
			}
			c.Papers = append(c.Papers, paperInfo{
				ID:    fmt.Sprintf("custom%d", customN),
				Label: fmt.Sprintf("%s (%.0fx%.0f mm)", name, wmm, hmm),
				W:     math.Round(wmm*10) / 10,
				H:     math.Round(hmm*10) / 10,
			})
			customN++
		}
	}
	// paper sources (drawers, bypass...) and the driver's current default settings
	c.Sources = []sourceInfo{}
	if fs, ok := raw["sources"].([]interface{}); ok {
		seenSrc := map[string]bool{}
		for _, it := range fs {
			m, ok := it.(map[string]interface{})
			if !ok {
				continue
			}
			name, _ := m["n"].(string)
			k, _ := m["k"].(float64)
			id := strconv.Itoa(int(k))
			if name == "" || seenSrc[id] {
				continue
			}
			seenSrc[id] = true
			c.Sources = append(c.Sources, sourceInfo{ID: id, Label: name})
		}
	}
	switch ds, _ := raw["defDuplex"].(string); ds {
	case "Vertical":
		c.Defaults.Duplex = "long"
	case "Horizontal":
		c.Defaults.Duplex = "short"
	default:
		c.Defaults.Duplex = "none"
	}
	if dw, ok := raw["defW"].(float64); ok {
		dh, _ := raw["defH"].(float64)
		wmm, hmm := dw*0.254, dh*0.254
		for _, p := range c.Papers {
			if math.Abs(wmm-p.W) < 2 && math.Abs(hmm-p.H) < 2 {
				c.Defaults.Paper = p.ID
				break
			}
		}
	}
	if dk, ok := raw["defSrc"].(float64); ok {
		id := strconv.Itoa(int(dk))
		for _, sc := range c.Sources {
			if sc.ID == id {
				c.Defaults.Source = id
			}
		}
	}
	if !c.Color && !c.Mono {
		c.Color, c.Mono = true, true
	}
	return c
}

// matchStdPaper finds the standard paper (A3, A4, Letter...) with the same size
func matchStdPaper(wmm, hmm float64) (paperInfo, bool) {
	for _, k := range paperOrder {
		p := paperByEnum[k]
		if (math.Abs(wmm-p.W) < 2 && math.Abs(hmm-p.H) < 2) || (math.Abs(wmm-p.H) < 2 && math.Abs(hmm-p.W) < 2) {
			return p, true
		}
	}
	return paperInfo{}, false
}

// sumatraPaper gives the paper name SumatraPDF understands. Custom sizes work
// only when their size equals a standard paper (for example a custom A6).
func sumatraPaper(id string, c printerCaps) (string, bool) {
	switch id {
	case "A3", "A4", "A5", "A6", "letter", "legal", "tabloid", "statement":
		return id, true
	}
	for _, p := range c.Papers {
		if p.ID == id {
			if std, ok := matchStdPaper(p.W, p.H); ok {
				return std.ID, true
			}
		}
	}
	return "", false
}

// sentSummary tells the phone exactly which settings were sent to the driver
func sentSummary(o printOpts, c printerCaps) string {
	paper := "printer default paper"
	for _, p := range c.Papers {
		if p.ID == o.Paper {
			paper = p.Label
		}
	}
	col := "color"
	if o.Color == "mono" {
		col = "black & white"
	}
	d := "one-sided"
// always send the duplex choice, so the driver default never decides
	switch o.Duplex {
	case "long":
		p = append(p, "duplexlong")
	case "short":
		p = append(p, "duplexshort")
	default:
		p = append(p, "noduplex")
	}
	src := "default tray"
	for _, sc := range c.Sources {
		if sc.ID == o.Source {
			src = sc.Label
		}
	}
	return fmt.Sprintf("%s, %s, %s, %s, copies: %d", paper, col, d, src, o.Copies)
}

func pdfPaperOK(o printOpts, c printerCaps) bool {
	if o.Paper == "" {
		return true
	}
	_, ok := sumatraPaper(o.Paper, c)
	return ok
}

func getCaps(printer string) printerCaps {
	capsMu.Lock()
	if e, ok := capsCache[printer]; ok && time.Since(e.at) < 30*time.Second {
		capsMu.Unlock()
		return e.caps
	}
	capsMu.Unlock()
	c := queryCaps(printer)
	if !c.Detected {
		c = queryCaps(printer)
	}
	if c.Detected {
		capsMu.Lock()
		capsCache[printer] = capsEntry{caps: c, at: time.Now()}
		capsMu.Unlock()
	}
	return c
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
    if ($o -eq 3) { $global:img.RotateFlip([System.Drawing.RotateFlipType]::Rotate180FlipNone) }
    elseif ($o -eq 6) { $global:img.RotateFlip([System.Drawing.RotateFlipType]::Rotate90FlipNone) }
    elseif ($o -eq 8) { $global:img.RotateFlip([System.Drawing.RotateFlipType]::Rotate270FlipNone) }
  }
  $pd = New-Object System.Drawing.Printing.PrintDocument
  $pd.PrinterSettings.PrinterName = $env:FB_PRINTER
  if (-not $pd.PrinterSettings.IsValid) { throw 'Invalid printer' }
  $pd.PrinterSettings.Copies = [int16]$env:FB_COPIES
  $pd.DefaultPageSettings.Color = ($env:FB_COLOR -eq 'color')
  if ($env:FB_PW) {
    $ww = [double]$env:FB_PW
    $hh = [double]$env:FB_PH
    foreach ($ps in $pd.PrinterSettings.PaperSizes) {
      $w = $ps.Width * 0.254
      $h = $ps.Height * 0.254
      if ([Math]::Abs($w - $ww) -lt 4 -and [Math]::Abs($h - $hh) -lt 4) {
        $pd.DefaultPageSettings.PaperSize = $ps
        break
      }
    }
  }
  if ($env:FB_DUPLEX -eq 'long') { $pd.PrinterSettings.Duplex = [System.Drawing.Printing.Duplex]::Vertical }
  elseif ($env:FB_DUPLEX -eq 'short') { $pd.PrinterSettings.Duplex = [System.Drawing.Printing.Duplex]::Horizontal }
  else { $pd.PrinterSettings.Duplex = [System.Drawing.Printing.Duplex]::Simplex }
  if ($env:FB_SRC) {
    foreach ($src in $pd.PrinterSettings.PaperSources) {
      if ([string]$src.RawKind -eq $env:FB_SRC) { $pd.DefaultPageSettings.PaperSource = $src; break }
    }
  }
  $land = $false
  if ($env:FB_ORIENT -eq 'landscape') { $land = $true }
  elseif ($env:FB_ORIENT -eq 'auto') { $land = ($global:img.Width -gt $global:img.Height) }
  $pd.DefaultPageSettings.Landscape = $land
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
} finally { $global:img.Dispose() }`

func sumatraSettings(o printOpts, c printerCaps) string {
	var p []string
	if o.Pages != "" {
		p = append(p, o.Pages)
	}
	p = append(p, strconv.Itoa(o.Copies)+"x")
	if o.Color == "mono" {
		p = append(p, "monochrome")
	} else {
		p = append(p, "color")
	}
	if o.Source != "" {
		p = append(p, "bin="+o.Source)
	}
	// always send the duplex choice, so the driver default never decides
	switch o.Duplex {
	case "long":
		p = append(p, "duplexlong")
	case "short":
		p = append(p, "duplexshort")
	default:
		p = append(p, "simplex")
	}
	switch o.Orientation {
	case "portrait":
		p = append(p, "portrait")
	case "landscape":
		p = append(p, "landscape")
	}
	if o.Scale == "noscale" {
		p = append(p, "noscale")
	} else {
		p = append(p, "fit")
	}
	return strings.Join(p, ",")
}

// queueHead finds the print queue (local or shared \\server\printer)
const queueHead = `Add-Type -AssemblyName System.Printing
$name = $env:FB_PRINTER
$q = $null
try {
  $srv = New-Object System.Printing.LocalPrintServer
  $q = $srv.GetPrintQueue($name)
} catch {
  $q = $null
}
if ($q -eq $null -and $name.StartsWith('\\')) {
  $parts = $name.TrimStart([char]92).Split([char[]]@([char]92), 2)
  $srv2 = New-Object System.Printing.PrintServer(('\\' + $parts[0]))
  $q = $srv2.GetPrintQueue($parts[1])
}
`

// applyScript writes the phone's choices into the driver's own defaults and
// reads them back to check that the driver really accepted them.
const applyScript = `$ErrorActionPreference = 'Stop'
try {
` + queueHead + `
$q.Refresh()
# back up the current driver defaults
$ms = New-Object System.IO.MemoryStream
$q.UserPrintTicket.SaveTo($ms)
[System.IO.File]::WriteAllBytes($env:FB_BACKUP, $ms.ToArray())

$t = $q.UserPrintTicket
if ($env:FB_PAPER) {
  $t.PageMediaSize = New-Object System.Printing.PageMediaSize([System.Printing.PageMediaSizeName]$env:FB_PAPER)
} elseif ($env:FB_PW) {
  $t.PageMediaSize = New-Object System.Printing.PageMediaSize(([double]$env:FB_PW * 96 / 25.4), ([double]$env:FB_PH * 96 / 25.4))
}
if ($env:FB_DUPLEX -eq 'long') { $t.Duplexing = [System.Printing.Duplexing]::TwoSidedLongEdge }
elseif ($env:FB_DUPLEX -eq 'short') { $t.Duplexing = [System.Printing.Duplexing]::TwoSidedShortEdge }
else { $t.Duplexing = [System.Printing.Duplexing]::OneSided }
if ($env:FB_COLOR -eq 'mono') { $t.OutputColor = [System.Printing.OutputColor]::Monochrome }
else { $t.OutputColor = [System.Printing.OutputColor]::Color }
$t.CopyCount = 1

try {
  $r = $q.MergeAndValidatePrintTicket($t)
  $q.UserPrintTicket = $r.ValidatedPrintTicket
  $q.Commit()
} catch {
  throw ('Windows refused to change the driver settings (try running QRPrint as Administrator): ' + $_.Exception.Message)
}

# read back and verify
$q.Refresh()
$v = $q.UserPrintTicket
$bad = @()
if ($env:FB_PAPER -or $env:FB_PW) {
  $okPaper = $false
  if ($env:FB_PAPER -and ([string]$v.PageMediaSize.PageMediaSizeName -eq $env:FB_PAPER)) { $okPaper = $true }
  if ($env:FB_PW) {
    $ew = [double]$env:FB_PW * 96 / 25.4
    $eh = [double]$env:FB_PH * 96 / 25.4
    $gw = [double]$v.PageMediaSize.Width
    $gh = [double]$v.PageMediaSize.Height
    if ((([Math]::Abs($gw - $ew) -lt 8) -and ([Math]::Abs($gh - $eh) -lt 8)) -or (([Math]::Abs($gw - $eh) -lt 8) -and ([Math]::Abs($gh - $ew) -lt 8))) { $okPaper = $true }
  }
  if (-not $okPaper) { $bad += ('paper is ' + $v.PageMediaSize.PageMediaSizeName) }
}
$wantD = 'OneSided'
if ($env:FB_DUPLEX -eq 'long') { $wantD = 'TwoSidedLongEdge' } elseif ($env:FB_DUPLEX -eq 'short') { $wantD = 'TwoSidedShortEdge' }
$gotD = [string]$v.Duplexing
if ($gotD -ne $wantD) {
  # a printer without duplex may report Unknown for one-sided: that is fine
  if (-not ($wantD -eq 'OneSided' -and $gotD -eq 'Unknown')) { $bad += ('duplex is ' + $gotD) }
}
if ($bad.Count -gt 0) { throw ('Driver did not accept: ' + ($bad -join ', ')) }
'OK'
} catch {
  [Console]::Error.WriteLine($_.Exception.Message)
  exit 1
}`

const restoreScript = `$ErrorActionPreference = 'Stop'
try {
` + queueHead + `
$bytes = [System.IO.File]::ReadAllBytes($env:FB_BACKUP)
$ms = New-Object System.IO.MemoryStream(,$bytes)
$q.UserPrintTicket = New-Object System.Printing.PrintTicket($ms)
$q.Commit()
} catch {
  [Console]::Error.WriteLine($_.Exception.Message)
  exit 1
}`

var psErrRe = regexp.MustCompile(`(?s)<S S="Error">(.*?)</S>`)

// cleanPSOutput turns PowerShell's error output into plain readable text
func cleanPSOutput(b []byte) string {
	s := string(b)
	if strings.Contains(s, "#< CLIXML") {
		var parts []string
		for _, m := range psErrRe.FindAllStringSubmatch(s, -1) {
			t := strings.ReplaceAll(m[1], "_x000D__x000A_", " ")
			t = strings.TrimSpace(t)
			if t != "" {
				parts = append(parts, t)
			}
		}
		s = strings.Join(parts, " ")
	}
	return strings.TrimSpace(s)
}

func enumForPaper(id string) string {
	for k, p := range paperByEnum {
		if p.ID == id {
			return k
		}
	}
	return ""
}

// applyDriver writes the phone's choices into the printer driver and checks them.
func applyDriver(printer string, o printOpts, c printerCaps, backup string) error {
	ctx, cancel := context.WithTimeout(context.Background(), 40*time.Second)
	defer cancel()
	env := []string{"FB_PRINTER=" + printer, "FB_BACKUP=" + backup,
		"FB_DUPLEX=" + o.Duplex, "FB_COLOR=" + o.Color}
	if o.Paper != "" {
		pw, ph := 0.0, 0.0
		for _, p := range c.Papers {
			if p.ID == o.Paper {
				pw, ph = p.W, p.H
			}
		}
		e := enumForPaper(o.Paper)
		if e != "" {
			env = append(env, "FB_PAPER="+e)
			if pw == 0 {
				pw, ph = paperByEnum[e].W, paperByEnum[e].H
			}
		}
		if pw > 0 {
			env = append(env,
				"FB_PW="+strconv.FormatFloat(pw, 'f', -1, 64),
				"FB_PH="+strconv.FormatFloat(ph, 'f', -1, 64))
		}
	}
	out, err := psCmd(ctx, applyScript, env).CombinedOutput()
	if err != nil {
		msg := cleanPSOutput(out)
		if msg == "" {
			msg = err.Error()
		}
		return fmt.Errorf("%s", msg)
	}
	return nil
}

func restoreDriver(printer, backup string) {
	ctx, cancel := context.WithTimeout(context.Background(), 40*time.Second)
	defer cancel()
	if out, err := psCmd(ctx, restoreScript, []string{"FB_PRINTER=" + printer, "FB_BACKUP=" + backup}).CombinedOutput(); err != nil {
		log.Printf("Could not restore driver settings: %v %s", err, cleanPSOutput(out))
	}
	os.Remove(backup)
}

// printFile prints everything through SumatraPDF. Photos are first turned into
// a one-page PDF, so there is one printing path. Before printing, the driver's
// own defaults are set and verified; afterwards the old defaults come back.
func printFile(printer, path, kind string, o printOpts, c printerCaps) error {
	s := findSumatra()
	if s == "" {
		return fmt.Errorf("SumatraPDF not found")
	}
	switch kind {
	case "image":
		work, err := os.MkdirTemp("", "qrprint-img-*")
		if err != nil {
			return err
		}
		defer os.RemoveAll(work)
		jpg := filepath.Join(work, "a.jpg")
		pdf := filepath.Join(work, "a.pdf")
		if err := normalizeImage(path, jpg); err != nil {
			return err
		}
		pw, ph := 210.0, 297.0
		for _, p := range c.Papers {
			if p.ID == o.Paper {
				pw, ph = p.W, p.H
			}
		}
		if err := jpegToPDF(jpg, pdf, pw, ph, o.Orientation); err != nil {
			return err
		}
		path = pdf
	case "pdf":
	default:
		return fmt.Errorf("unsupported file type")
	}

	backup := filepath.Join(os.TempDir(), "qrprint-ticket-"+strconv.FormatInt(time.Now().UnixNano(), 36)+".xml")
	if err := applyDriver(printer, o, c, backup); err != nil {
		os.Remove(backup)
		return err // nothing is printed with wrong settings
	}
	defer restoreDriver(printer, backup)

	ctx, cancel := context.WithTimeout(context.Background(), 180*time.Second)
	defer cancel()
	settings := sumatraSettings(o, c)
	log.Printf("Driver set and verified. SumatraPDF settings: %s", settings)
	cmd := exec.CommandContext(ctx, s, "-print-to", printer, "-print-settings", settings, "-silent", path)
	hideWindow(cmd)
	if out, err := cmd.CombinedOutput(); err != nil {
		return fmt.Errorf("%v: %s", err, strings.TrimSpace(string(out)))
	}
	return nil
}

// sniffPrintType decides the file type from the first bytes, not the file name
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

// normalizeOpts checks the phone's choices against what the printer supports.
// It returns an error message and code, or empty strings when everything is fine.
func normalizeOpts(o *printOpts, c printerCaps) (string, string) {
	if o.Copies < 1 {
		o.Copies = 1
	}
	if o.Copies > c.MaxCopies {
		return fmt.Sprintf("Too many copies (maximum %d)", c.MaxCopies), "copies"
	}
	if o.Color != "color" && o.Color != "mono" {
		if c.Color {
			o.Color = "color"
		} else {
			o.Color = "mono"
		}
	}
	if o.Color == "color" && !c.Color {
		o.Color = "mono"
	}
	if o.Color == "mono" && !c.Mono {
		o.Color = "color"
	}
	if o.Paper == "" && len(c.Papers) > 0 {
		o.Paper = c.Papers[0].ID
		for _, p := range c.Papers {
			if p.ID == "A4" {
				o.Paper = "A4"
			}
		}
	}
	if o.Paper != "" {
		found := false
		for _, p := range c.Papers {
			if p.ID == o.Paper {
				found = true
			}
		}
		if !found {
			return "That paper size is not available on this printer", "paper"
		}
	}
	if o.Source != "" {
		found := false
		for _, sc := range c.Sources {
			if sc.ID == o.Source {
				found = true
			}
		}
		if !found {
			if len(c.Sources) > 0 {
				return "That paper source is not available on this printer", "source"
			}
			o.Source = ""
		}
	}
	if o.Source == "" && len(c.Sources) > 0 {
		o.Source = c.Sources[0].ID
		for _, sc := range c.Sources {
			if strings.Contains(strings.ToLower(sc.Label), "auto") {
				o.Source = sc.ID
				break
			}
		}
	}
	if o.Duplex != "long" && o.Duplex != "short" {
		o.Duplex = "none"
	}
	if c.Detected && !c.Duplex {
		o.Duplex = "none"
	}
	if o.Orientation != "portrait" && o.Orientation != "landscape" {
		o.Orientation = "auto"
	}
	if o.Scale != "noscale" {
		o.Scale = "fit"
	}
	if o.Pages != "" && (len(o.Pages) > 100 || !pagesRe.MatchString(o.Pages)) {
		return "Pages format is not valid", "pages"
	}
	return "", ""
}

// ---------- helpers ----------

func writeJSON(w http.ResponseWriter, status int, data interface{}) {
	w.Header().Set("Content-Type", "application/json; charset=utf-8")
	w.Header().Set("Cache-Control", "no-store")
	w.WriteHeader(status)
	json.NewEncoder(w).Encode(data)
}

func openBrowser(u string) {
	cmd := exec.Command("rundll32", "url.dll,FileProtocolHandler", u)
	hideWindow(cmd)
	cmd.Start()
}

// adminOnly allows only the PC itself (not phones) to use the settings page
func adminOnly(h http.HandlerFunc) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		ip := net.ParseIP(clientIP(r))
		if ip == nil || !ip.IsLoopback() {
			http.NotFound(w, r)
			return
		}
		if r.Host != fmt.Sprintf("localhost:%d", port) && r.Host != fmt.Sprintf("127.0.0.1:%d", port) {
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

// phoneAuth requires printing to be on and a valid PIN session
func phoneAuth(h http.HandlerFunc) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		if !printEnabled() {
			writeJSON(w, http.StatusForbidden, map[string]string{"error": "Printing is turned off on the PC", "code": "off"})
			return
		}
		if !validSession(r.Header.Get("X-Session")) {
			writeJSON(w, http.StatusUnauthorized, map[string]string{"error": "Login required", "code": "login"})
			return
		}
		h(w, r)
	}
}

// ---------- PC settings handlers ----------

func handleAdminPage(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "text/html; charset=utf-8")
	w.Header().Set("Cache-Control", "no-store")
	w.Write([]byte(adminHTML))
}

func handleAdminStatus(w http.ResponseWriter, r *http.Request) {
	cfgMu.RLock()
	defer cfgMu.RUnlock()
	writeJSON(w, http.StatusOK, map[string]interface{}{
		"enabled":     cfg.Enabled,
		"hasPassword": cfg.Hash != "",
		"url":         phoneURL(),
		"sumatra":     findSumatra() != "",
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
		writeJSON(w, http.StatusBadRequest, map[string]string{"error": "Set a 4-digit password first"})
		return
	}
	cfg.Enabled = req.Enabled
	if err := saveCfg(); err != nil {
		writeJSON(w, http.StatusInternalServerError, map[string]string{"error": "Could not save settings"})
		return
	}
	if !req.Enabled {
		clearSessions()
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
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil || !pinRe.MatchString(req.Password) {
		writeJSON(w, http.StatusBadRequest, map[string]string{"error": "Password must be exactly 4 digits"})
		return
	}
	salt := make([]byte, 16)
	if _, err := rand.Read(salt); err != nil {
		writeJSON(w, http.StatusInternalServerError, map[string]string{"error": "Could not save password"})
		return
	}
	cfgMu.Lock()
	defer cfgMu.Unlock()
	cfg.Salt = hex.EncodeToString(salt)
	cfg.Hash = hashPassword(req.Password, salt)
	if err := saveCfg(); err != nil {
		writeJSON(w, http.StatusInternalServerError, map[string]string{"error": "Could not save settings"})
		return
	}
	clearSessions()
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
	w.Write(png)
}

// ---------- phone handlers ----------

func handlePhonePage(w http.ResponseWriter, r *http.Request) {
	if r.URL.Path != "/" {
		http.NotFound(w, r)
		return
	}
	w.Header().Set("Content-Type", "text/html; charset=utf-8")
	w.Header().Set("Cache-Control", "no-store")
	w.Write([]byte(phoneHTML))
}

func handlePhoneStatus(w http.ResponseWriter, r *http.Request) {
	writeJSON(w, http.StatusOK, map[string]bool{"enabled": printEnabled()})
}

func handleLogin(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodPost {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}
	if !printEnabled() {
		writeJSON(w, http.StatusForbidden, map[string]string{"error": "Printing is turned off on the PC", "code": "off"})
		return
	}
	ip := clientIP(r)
	if isLocked(ip) || isLocked("*") {
		writeJSON(w, http.StatusTooManyRequests, map[string]string{"error": "Too many wrong attempts", "code": "locked"})
		return
	}
	var req struct {
		Pin string `json:"pin"`
	}
	r.Body = http.MaxBytesReader(w, r.Body, 1024)
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil || !pinRe.MatchString(req.Pin) || !checkPassword(req.Pin) {
		recordFail(ip, ipFailLimit)
		recordFail("*", globalFailLim)
		log.Printf("Wrong PIN (source IP: %s)", ip)
		writeJSON(w, http.StatusUnauthorized, map[string]string{"error": "Wrong PIN", "code": "pin"})
		return
	}
	clearFail(ip)
	writeJSON(w, http.StatusOK, map[string]string{"session": newSession()})
}

func handlePing(w http.ResponseWriter, r *http.Request) {
	writeJSON(w, http.StatusOK, map[string]interface{}{"ok": true, "pdfOk": findSumatra() != ""})
}

func handlePrinters(w http.ResponseWriter, r *http.Request) {
	printers, err := listPrinters()
	if err != nil {
		log.Printf("Failed to list printers: %v", err)
		writeJSON(w, http.StatusInternalServerError, map[string]string{"error": "Could not read printers", "code": "failed"})
		return
	}
	writeJSON(w, http.StatusOK, map[string]interface{}{"printers": printers})
}

func handleCaps(w http.ResponseWriter, r *http.Request) {
	printer := r.URL.Query().Get("printer")
	ok, err := printerExists(printer)
	if err != nil {
		writeJSON(w, http.StatusInternalServerError, map[string]string{"error": "Could not read printers", "code": "failed"})
		return
	}
	if !ok {
		writeJSON(w, http.StatusBadRequest, map[string]string{"error": "Printer not available", "code": "printer"})
		return
	}
	writeJSON(w, http.StatusOK, map[string]interface{}{
		"caps":  getCaps(printer),
		"pdfOk": findSumatra() != "",
	})
}

// saveUpload reads the request body into a temp file after checking that it is
// a PDF or a photo. On failure it writes the error response and returns ok=false.
func saveUpload(w http.ResponseWriter, r *http.Request) (string, string, bool) {
	r.Body = http.MaxBytesReader(w, r.Body, maxPrintBytes)
	head := make([]byte, 8)
	n, _ := io.ReadFull(r.Body, head)
	head = head[:n]
	kind, ext := sniffPrintType(head)
	if kind == "" {
		writeJSON(w, http.StatusUnsupportedMediaType, map[string]string{"error": "Only PDF and photos can be printed", "code": "type"})
		return "", "", false
	}
	if kind == "pdf" && findSumatra() == "" {
		writeJSON(w, http.StatusBadRequest, map[string]string{"error": "PDF printing needs SumatraPDF.exe next to QRPrint.exe on the PC", "code": "nosumatra"})
		return "", "", false
	}

	tmp, err := os.CreateTemp("", "qrprint-*"+ext)
	if err != nil {
		writeJSON(w, http.StatusInternalServerError, map[string]string{"error": "Printing failed", "code": "failed"})
		return "", "", false
	}
	tmpPath := tmp.Name()

	_, werr := tmp.Write(head)
	if werr == nil {
		_, werr = io.Copy(tmp, r.Body)
	}
	tmp.Close()
	if werr != nil {
		os.Remove(tmpPath)
		log.Printf("Failed to receive print file: %v", werr)
		writeJSON(w, http.StatusBadRequest, map[string]string{"error": "Upload failed", "code": "upload"})
		return "", "", false
	}
	return tmpPath, kind, true
}

func handlePrint(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodPost {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	printer, _ := url.QueryUnescape(r.Header.Get("X-Printer"))
	optRaw, _ := url.QueryUnescape(r.Header.Get("X-Options"))

	ok, err := printerExists(printer)
	if err != nil {
		log.Printf("Failed to list printers: %v", err)
		writeJSON(w, http.StatusInternalServerError, map[string]string{"error": "Could not read printers", "code": "failed"})
		return
	}
	if !ok {
		writeJSON(w, http.StatusBadRequest, map[string]string{"error": "Printer not available", "code": "printer"})
		return
	}

	var o printOpts
	if err := json.Unmarshal([]byte(optRaw), &o); err != nil {
		writeJSON(w, http.StatusBadRequest, map[string]string{"error": "Bad print options", "code": "bad"})
		return
	}
	caps := getCaps(printer)
	if msg, code := normalizeOpts(&o, caps); msg != "" {
		writeJSON(w, http.StatusBadRequest, map[string]string{"error": msg, "code": code})
		return
	}

	tmpPath, kind, got := saveUpload(w, r)
	if !got {
		return
	}

	printMu.Lock()
	perr := printFile(printer, tmpPath, kind, o, caps)
	printMu.Unlock()
	os.Remove(tmpPath)

	if perr != nil {
		log.Printf("Print failed on %q: %v", printer, perr)
		writeJSON(w, http.StatusInternalServerError, map[string]string{"error": "Printing failed: " + perr.Error(), "code": "failed"})
		return
	}
	log.Printf("Printed a %s file on %q (%d copies)", kind, printer, o.Copies)
	writeJSON(w, http.StatusOK, map[string]interface{}{"success": true, "sent": sentSummary(o, caps)})
}

// ---------- "Print all together" ----------

// cleanStaged deletes uploaded batch files that were never printed
func cleanStaged() {
	stageMu.Lock()
	defer stageMu.Unlock()
	now := time.Now()
	for id, s := range staging {
		if now.Sub(s.at) > stageTTL {
			os.Remove(s.path)
			delete(staging, id)
		}
	}
}

// handleStage receives one file of a batch and keeps it until /api/printbatch
func handleStage(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodPost {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}
	cleanStaged()
	stageMu.Lock()
	count := len(staging)
	stageMu.Unlock()
	if count >= maxStaged {
		writeJSON(w, http.StatusTooManyRequests, map[string]string{"error": "Too many files waiting. Try again in a few minutes.", "code": "busy"})
		return
	}

	path, kind, ok := saveUpload(w, r)
	if !ok {
		return
	}
	idb := make([]byte, 16)
	if _, err := rand.Read(idb); err != nil {
		os.Remove(path)
		writeJSON(w, http.StatusInternalServerError, map[string]string{"error": "Upload failed", "code": "failed"})
		return
	}
	id := hex.EncodeToString(idb)
	stageMu.Lock()
	staging[id] = &staged{path: path, kind: kind, session: r.Header.Get("X-Session"), at: time.Now()}
	stageMu.Unlock()
	writeJSON(w, http.StatusOK, map[string]string{"id": id})
}

// normImageScript turns any photo (JPG/PNG/BMP) into an upright, white-background
// JPEG so it can be placed on a PDF page
const normImageScript = `$ErrorActionPreference = 'Stop'
Add-Type -AssemblyName System.Drawing
$img = [System.Drawing.Image]::FromFile($env:FB_FILE)
try {
  if ($img.PropertyIdList -contains 274) {
    $o = $img.GetPropertyItem(274).Value[0]
    if ($o -eq 3) { $img.RotateFlip([System.Drawing.RotateFlipType]::Rotate180FlipNone) }
    elseif ($o -eq 6) { $img.RotateFlip([System.Drawing.RotateFlipType]::Rotate90FlipNone) }
    elseif ($o -eq 8) { $img.RotateFlip([System.Drawing.RotateFlipType]::Rotate270FlipNone) }
  }
  $bmp = New-Object System.Drawing.Bitmap($img.Width, $img.Height)
  $bmp.SetResolution(96, 96)
  $g = [System.Drawing.Graphics]::FromImage($bmp)
  $g.Clear([System.Drawing.Color]::White)
  $g.DrawImage($img, 0, 0, $img.Width, $img.Height)
  $g.Dispose()
  $enc = [System.Drawing.Imaging.ImageCodecInfo]::GetImageEncoders() | Where-Object { $_.MimeType -eq 'image/jpeg' }
  $p = New-Object System.Drawing.Imaging.EncoderParameters(1)
  $p.Param[0] = New-Object System.Drawing.Imaging.EncoderParameter([System.Drawing.Imaging.Encoder]::Quality, [long]92)
  $bmp.Save($env:FB_OUT, $enc, $p)
  $bmp.Dispose()
} finally { $img.Dispose() }`

func normalizeImage(src, dst string) error {
	ctx, cancel := context.WithTimeout(context.Background(), 90*time.Second)
	defer cancel()
	out, err := psCmd(ctx, normImageScript, []string{"FB_FILE=" + src, "FB_OUT=" + dst}).CombinedOutput()
	if err != nil {
		return fmt.Errorf("%v: %s", err, strings.TrimSpace(string(out)))
	}
	return nil
}

// jpegToPDF writes a one-page PDF with the JPEG centred and fitted on the paper
func jpegToPDF(jpgPath, pdfPath string, paperWmm, paperHmm float64, orient string) error {
	data, err := os.ReadFile(jpgPath)
	if err != nil {
		return err
	}
	cfgImg, err := jpeg.DecodeConfig(bytes.NewReader(data))
	if err != nil {
		return err
	}
	iw0, ih0 := float64(cfgImg.Width), float64(cfgImg.Height)
	pw, ph := paperWmm*72/25.4, paperHmm*72/25.4
	land := orient == "landscape" || (orient == "auto" && iw0 > ih0)
	if land {
		pw, ph = ph, pw
	}
	const margin = 36.0
	scale := (pw - 2*margin) / iw0
	if s2 := (ph - 2*margin) / ih0; s2 < scale {
		scale = s2
	}
	iw, ih := iw0*scale, ih0*scale
	x, y := (pw-iw)/2, (ph-ih)/2

	var buf bytes.Buffer
	offs := make([]int, 6)
	buf.WriteString("%PDF-1.4\n")
	obj := func(n int, body string) {
		offs[n] = buf.Len()
		fmt.Fprintf(&buf, "%d 0 obj\n%s\nendobj\n", n, body)
	}
	obj(1, "<< /Type /Catalog /Pages 2 0 R >>")
	obj(2, "<< /Type /Pages /Kids [3 0 R] /Count 1 >>")
	obj(3, fmt.Sprintf("<< /Type /Page /Parent 2 0 R /MediaBox [0 0 %.2f %.2f] /Resources << /XObject << /Im0 4 0 R >> >> /Contents 5 0 R >>", pw, ph))
	offs[4] = buf.Len()
	fmt.Fprintf(&buf, "4 0 obj\n<< /Type /XObject /Subtype /Image /Width %d /Height %d /ColorSpace /DeviceRGB /BitsPerComponent 8 /Filter /DCTDecode /Length %d >>\nstream\n", cfgImg.Width, cfgImg.Height, len(data))
	buf.Write(data)
	buf.WriteString("\nendstream\nendobj\n")
	content := fmt.Sprintf("q %.2f 0 0 %.2f %.2f %.2f cm /Im0 Do Q", iw, ih, x, y)
	offs[5] = buf.Len()
	fmt.Fprintf(&buf, "5 0 obj\n<< /Length %d >>\nstream\n%s\nendstream\nendobj\n", len(content), content)
	xref := buf.Len()
	buf.WriteString("xref\n0 6\n0000000000 65535 f \n")
	for i := 1; i <= 5; i++ {
		fmt.Fprintf(&buf, "%010d 00000 n \n", offs[i])
	}
	fmt.Fprintf(&buf, "trailer\n<< /Size 6 /Root 1 0 R >>\nstartxref\n%d\n%%%%EOF\n", xref)
	return os.WriteFile(pdfPath, buf.Bytes(), 0600)
}

// handlePrintBatch joins all staged files (in the given order) into ONE PDF
// and prints it as a single job. Each photo becomes one page, each PDF keeps
// its pages, so two-sided printing continues onto the back of the page and
// "Copies" gives complete sets.
func handlePrintBatch(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodPost {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}
	var req struct {
		Printer string    `json:"printer"`
		Ids     []string  `json:"ids"`
		Opts    printOpts `json:"opts"`
	}
	r.Body = http.MaxBytesReader(w, r.Body, 1<<16)
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil || len(req.Ids) == 0 || len(req.Ids) > maxStaged {
		writeJSON(w, http.StatusBadRequest, map[string]string{"error": "Bad request", "code": "bad"})
		return
	}
	if findSumatra() == "" {
		writeJSON(w, http.StatusBadRequest, map[string]string{"error": "Print all together needs SumatraPDF.exe next to QRPrint.exe on the PC", "code": "nosumatra"})
		return
	}

	ok, err := printerExists(req.Printer)
	if err != nil {
		log.Printf("Failed to list printers: %v", err)
		writeJSON(w, http.StatusInternalServerError, map[string]string{"error": "Could not read printers", "code": "failed"})
		return
	}
	if !ok {
		writeJSON(w, http.StatusBadRequest, map[string]string{"error": "Printer not available", "code": "printer"})
		return
	}

	o := req.Opts // o.Pages (like 1-3,5) counts the pages of the joined document
	caps := getCaps(req.Printer)
	if msg, code := normalizeOpts(&o, caps); msg != "" {
		writeJSON(w, http.StatusBadRequest, map[string]string{"error": msg, "code": code})
		return
	}

	// take the staged files (only the ones uploaded by this phone session)
	session := r.Header.Get("X-Session")
	stageMu.Lock()
	items := make([]*staged, 0, len(req.Ids))
	seen := map[string]bool{}
	for _, id := range req.Ids {
		s, found := staging[id]
		if !found || s.session != session || seen[id] {
			stageMu.Unlock()
			writeJSON(w, http.StatusBadRequest, map[string]string{"error": "A file expired. Please try again.", "code": "expired"})
			return
		}
		seen[id] = true
		items = append(items, s)
	}
	for _, id := range req.Ids {
		delete(staging, id)
	}
	stageMu.Unlock()
	defer func() {
		for _, it := range items {
			os.Remove(it.path)
		}
	}()

	work, err := os.MkdirTemp("", "qrprint-batch-*")
	if err != nil {
		writeJSON(w, http.StatusInternalServerError, map[string]string{"error": "Printing failed", "code": "failed"})
		return
	}
	defer os.RemoveAll(work)

	// paper used for photo pages (A4 when the printer default is chosen)
	pwmm, phmm := 210.0, 297.0
	for _, pp := range caps.Papers {
		if pp.ID == o.Paper {
			pwmm, phmm = pp.W, pp.H
		}
	}

	parts := make([]string, 0, len(items))
	for i, it := range items {
		if it.kind == "pdf" {
			parts = append(parts, it.path)
			continue
		}
		jpg := filepath.Join(work, fmt.Sprintf("p%03d.jpg", i))
		pdf := filepath.Join(work, fmt.Sprintf("p%03d.pdf", i))
		if err := normalizeImage(it.path, jpg); err != nil {
			log.Printf("Could not prepare photo %d: %v", i+1, err)
			writeJSON(w, http.StatusInternalServerError, map[string]string{"error": fmt.Sprintf("Could not read photo %d", i+1), "code": "failed"})
			return
		}
		if err := jpegToPDF(jpg, pdf, pwmm, phmm, o.Orientation); err != nil {
			log.Printf("Could not convert photo %d: %v", i+1, err)
			writeJSON(w, http.StatusInternalServerError, map[string]string{"error": fmt.Sprintf("Could not convert photo %d", i+1), "code": "failed"})
			return
		}
		parts = append(parts, pdf)
	}

	merged := filepath.Join(work, "merged.pdf")
	if err := api.MergeCreateFile(parts, merged, false, nil); err != nil {
		log.Printf("PDF merge failed: %v", err)
		writeJSON(w, http.StatusInternalServerError, map[string]string{"error": "Could not join the files. A PDF may be damaged or password-protected.", "code": "failed"})
		return
	}

	printMu.Lock()
	perr := printFile(req.Printer, merged, "pdf", o, caps)
	printMu.Unlock()

	if perr != nil {
		log.Printf("Batch print failed on %q: %v", req.Printer, perr)
		writeJSON(w, http.StatusInternalServerError, map[string]string{"error": "Printing failed: " + perr.Error(), "code": "failed"})
		return
	}
	log.Printf("Printed one job made of %d files on %q (%d copies)", len(items), req.Printer, o.Copies)
	writeJSON(w, http.StatusOK, map[string]interface{}{"success": true, "sent": sentSummary(o, caps)})
}

// ---------- main ----------

func main() {
	loadCfg()
	adminURL := fmt.Sprintf("http://localhost:%d/admin", port)

	ln, err := net.Listen("tcp", fmt.Sprintf("0.0.0.0:%d", port))
	if err != nil {
		fmt.Printf("Port %d is already in use. QR PRINT may already be running.\n", port)
		fmt.Println("Opening the settings page...")
		openBrowser(adminURL)
		time.Sleep(3 * time.Second)
		return
	}

	mux := http.NewServeMux()
	mux.HandleFunc("/", handlePhonePage)
	mux.HandleFunc("/api/status", handlePhoneStatus)
	mux.HandleFunc("/api/login", handleLogin)
	mux.HandleFunc("/api/ping", phoneAuth(handlePing))
	mux.HandleFunc("/api/printers", phoneAuth(handlePrinters))
	mux.HandleFunc("/api/caps", phoneAuth(handleCaps))
	mux.HandleFunc("/api/print", phoneAuth(handlePrint))
	mux.HandleFunc("/api/stage", phoneAuth(handleStage))
	mux.HandleFunc("/api/printbatch", phoneAuth(handlePrintBatch))
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

	// remove batch files that were uploaded but never printed
	go func() {
		for {
			time.Sleep(5 * time.Minute)
			cleanStaged()
		}
	}()

	fmt.Println("QR PRINT is running.")
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
<title>QR PRINT - Settings</title>
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
<h1>QR PRINT</h1>
<div class="card qr"><h2>Scan with your phone</h2>
<img id="qr" alt="QR code"><div class="url" id="url"></div></div>
<div class="card"><h2>Printing</h2>
<label><input type="checkbox" id="en"> Allow printing from phones</label>
<div class="small" id="pwstate"></div><div class="msg" id="msg1"></div></div>
<div class="card"><h2>PIN (4 digits)</h2>
<input type="password" id="pw" maxlength="4" inputmode="numeric" placeholder="4 digits" autocomplete="off">
<button id="save">Save PIN</button><div class="msg" id="msg2"></div></div>
<div class="card"><h2>PDF printing</h2><div id="sum" class="small"></div></div>
<div class="small">Only PDF files and photos (JPG, PNG, BMP) can be printed. Close the black console window to stop QR PRINT.</div>
</div>
<script>
var H={'X-Requested-With':'PhonePrint','Content-Type':'application/json'};
function $(i){return document.getElementById(i)}
function load(){
  fetch('/admin/api/status').then(function(r){return r.json()}).then(function(s){
    $('en').checked=s.enabled;
    $('pwstate').textContent=s.hasPassword?'PIN is set.':'Set a PIN first.';
    $('url').textContent=s.url||'No Wi-Fi address found';
    $('sum').textContent=s.sumatra?'SumatraPDF found. PDF printing is ready.':'SumatraPDF.exe not found. Put it in the same folder as QRPrint.exe to print PDFs. Photos work without it.';
    $('sum').style.color=s.sumatra?'#4ade80':'#fbbf24';
    if(s.url){$('qr').src='/admin/qr.png?'+Date.now();$('qr').style.display='inline-block'}else{$('qr').style.display='none'}
  });
}
$('en').onchange=function(){
  var want=$('en').checked;
  fetch('/admin/api/enable',{method:'POST',headers:H,body:JSON.stringify({enabled:want})})
  .then(function(r){return r.json().then(function(d){return{ok:r.ok,d:d}})})
  .then(function(x){
    if(x.ok){$('msg1').className='msg ok';$('msg1').textContent=want?'Printing is ON.':'Printing is OFF.'}
    else{$('msg1').className='msg err';$('msg1').textContent=x.d.error||'Error';load()}
  });
};
$('save').onclick=function(){
  fetch('/admin/api/password',{method:'POST',headers:H,body:JSON.stringify({password:$('pw').value})})
  .then(function(r){return r.json().then(function(d){return{ok:r.ok,d:d}})})
  .then(function(x){
    if(x.ok){$('pw').value='';$('msg2').className='msg ok';$('msg2').textContent='PIN saved.';load()}
    else{$('msg2').className='msg err';$('msg2').textContent=x.d.error||'Error'}
  });
};
load();
</script></body></html>`

const phoneHTML = `<!DOCTYPE html>
<html lang="en"><head><meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1, maximum-scale=1">
<title>QR PRINT</title>
<style>
*{box-sizing:border-box;margin:0;padding:0}
body{font-family:-apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,sans-serif;background:#0f172a;color:#e2e8f0;min-height:100vh}
.c{max-width:520px;margin:0 auto;padding:20px}
h1{font-size:1.5rem;text-align:center;color:#38bdf8;margin-bottom:18px}
.btn{display:block;width:100%;padding:14px;border:none;border-radius:8px;background:#2563eb;color:#fff;font-size:1.05rem}
.btn.green{background:#16a34a;margin-top:6px}
.btn:disabled{background:#334155;color:#64748b}
.pick{display:block;text-align:center;background:#7c3aed;color:#fff;padding:16px;border-radius:8px;font-size:1.1rem;margin-bottom:6px}
.pick input{display:none}
.hint{color:#94a3b8;font-size:.8rem;text-align:center;margin-bottom:12px}
.row{display:flex;align-items:center;gap:8px;background:#1e293b;border-radius:8px;padding:10px 12px;margin-bottom:8px}
.nm{flex:1;min-width:0;font-size:.9rem;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.nm small{display:block;color:#94a3b8;font-size:.75rem}
.pbtn{background:#2563eb;color:#fff;border:none;border-radius:6px;padding:9px 16px;font-size:.95rem}
.xbtn{background:none;border:none;color:#64748b;font-size:1.4rem;padding:0 6px}
.xbtn.mv{font-size:1rem;padding:0 4px}
.xbtn:disabled{opacity:.25}
input.pin,select,input.txt,input.num{width:100%;padding:12px;margin-bottom:10px;border-radius:8px;background:#1e293b;color:#e2e8f0;border:1px solid #475569;font-size:1rem}
input.pin{text-align:center;letter-spacing:.6em;font-size:1.6rem}
.msg{text-align:center;margin-top:12px;font-size:.95rem;min-height:1.3em}
.err{color:#f87171}.ok{color:#4ade80}.info{color:#38bdf8}
.overlay{position:fixed;top:0;left:0;right:0;bottom:0;background:#0f172a;overflow-y:auto;-webkit-overflow-scrolling:touch}
#dlg{z-index:10}#lock{z-index:30}#off{z-index:30}
.dhead{display:flex;align-items:center;gap:10px;margin-bottom:12px}
.gbtn{background:#334155;color:#e2e8f0;border:none;border-radius:6px;padding:8px 12px;font-size:.95rem}
.gbtn:disabled{opacity:.4}
.dtitle{flex:1;min-width:0;font-size:.95rem;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.pv{background:#334155;border-radius:8px;padding:12px;max-height:46vh;overflow-y:auto;-webkit-overflow-scrolling:touch}
.pv.gray{filter:grayscale(1)}
.pvnote{color:#94a3b8;font-size:.8rem;text-align:center;margin:6px 0 14px;min-height:1.1em}
.pvmsg{color:#e2e8f0;text-align:center;font-size:.9rem;padding:20px 8px}
.lnk{display:block;text-align:center;color:#38bdf8;margin-bottom:10px}
.sheet{position:relative;width:100%;margin:0 auto;background:#fff;box-shadow:0 2px 8px rgba(0,0,0,.4)}
.sheet img{position:absolute;top:6%;left:6%;width:88%;height:88%;object-fit:contain}
canvas.pg{display:block;width:100%;height:auto;background:#fff;margin:0 auto 10px}
.brow{display:flex;align-items:center;gap:10px;background:#1e293b;border-radius:6px;padding:6px 8px;margin-bottom:6px}
.bnum{width:22px;height:22px;border-radius:11px;background:#2563eb;color:#fff;font-size:.8rem;display:flex;align-items:center;justify-content:center;flex:none}
.bth{width:44px;height:44px;object-fit:cover;border-radius:4px;background:#fff;flex:none}
.bpdf{background:#7c3aed;color:#fff;font-size:.75rem;display:flex;align-items:center;justify-content:center}
.bnm{flex:1;min-width:0;font-size:.85rem;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.bnm small{display:block;color:#94a3b8;font-size:.75rem}
.lbl{font-size:.8rem;color:#94a3b8;margin:4px 0 4px;display:flex;justify-content:space-between;align-items:center}
.mini{background:none;border:none;color:#38bdf8;font-size:.8rem}
.seg{display:flex;gap:8px;margin-bottom:10px}
.seg button,.seg div{flex:1;padding:11px;border-radius:8px;border:1px solid #475569;background:#1e293b;color:#e2e8f0;font-size:.95rem;text-align:center}
.seg button.on{background:#2563eb;border-color:#2563eb}
.cop{display:flex;gap:8px;margin-bottom:10px}
.cop button{width:52px;border:none;border-radius:8px;background:#334155;color:#fff;font-size:1.4rem}
.cop input{flex:1;text-align:center;margin-bottom:0}
</style></head><body>

<div id="main"><div class="c">
<h1>QR PRINT</h1>
<label class="pick">Choose files to print<input type="file" id="file" multiple accept="application/pdf,image/jpeg,image/png,image/bmp"></label>
<div class="hint">PDF or photos (JPG, PNG). Choose several to print them all together.</div>
<div id="files"></div>
<button id="printAll" class="btn green" type="button" style="display:none">Print all together</button>
<div id="fmsg" class="msg"></div>
</div></div>

<div id="dlg" class="overlay" style="display:none"><div class="c">
<div class="dhead"><button class="gbtn" id="dclose" type="button">&#8249; Back</button><div id="dtitle" class="dtitle"></div></div>
<div id="pv" class="pv"></div>
<div id="pvnote" class="pvnote"></div>

<div class="lbl"><span>Printer</span><button class="mini" id="refp" type="button">&#8635; Refresh</button></div>
<select id="printer"></select>

<div class="lbl"><span>Color</span></div>
<div id="colorSeg" class="seg"></div>

<div class="lbl"><span>Paper size</span></div>
<select id="paper"></select>

<div id="srcrow" style="display:none"><div class="lbl"><span>Paper source (tray)</span></div>
<select id="source"></select></div>

<div class="lbl"><span id="copLbl">Copies</span></div>
<div class="cop"><button id="cm" type="button">&#8722;</button><input id="copies" class="num" type="number" min="1" value="1" inputmode="numeric"><button id="cp" type="button">+</button></div>

<div id="duprow" style="display:none"><div class="lbl"><span>Two-sided</span></div>
<select id="duplex"><option value="none">One-sided</option><option value="long">Two-sided (long edge)</option><option value="short">Two-sided (short edge)</option></select></div>

<div class="lbl"><span>Orientation</span></div>
<select id="orient"><option value="auto">Automatic</option><option value="portrait">Portrait</option><option value="landscape">Landscape</option></select>

<div id="pdfonly" style="display:none">
<div class="lbl"><span>Scale</span></div>
<select id="scale"><option value="fit">Fit to page</option><option value="noscale">Actual size</option></select>
<div id="pagesrow">
<div class="lbl"><span>Pages</span></div>
<input id="pages" class="txt" type="text" placeholder="All pages (e.g. 1-3,5)" autocomplete="off">
</div>
</div>

<button id="doprint" class="btn green" type="button" disabled>Print</button>
<div id="dmsg" class="msg"></div>
</div></div>

<div id="lock" class="overlay" style="display:none"><div class="c">
<h1>QR PRINT</h1>
<div class="hint" style="font-size:1rem;margin-bottom:14px">Enter the 4-digit PIN</div>
<input type="password" id="pin" class="pin" maxlength="4" inputmode="numeric" pattern="[0-9]*" autocomplete="off">
<button id="unlock" class="btn" type="button">Unlock</button>
<div id="lockmsg" class="msg"></div>
</div></div>

<div id="off" class="overlay" style="display:none"><div class="c">
<h1>QR PRINT</h1>
<div class="msg err" style="font-size:1.05rem;margin-bottom:16px">Printing is turned off on the PC.</div>
<button id="retry" class="btn" type="button">Try again</button>
</div></div>

<script>
var PDFJS='https://cdnjs.cloudflare.com/ajax/libs/pdf.js/3.11.174/';
var MAXPV=20;
var S={session:'',files:[],cur:null,batch:false,bUrls:[],bCounts:[],bLbl:[],bTok:null,defApplied:false,caps:null,color:'color',pdfOk:true,pdfDoc:null,imgW:0,imgH:0,pvUrl:''};
try{S.session=sessionStorage.getItem('pp_s')||''}catch(e){}

function $(i){return document.getElementById(i)}
function el(tag,cls,txt){var e=document.createElement(tag);if(cls)e.className=cls;if(txt!==undefined)e.textContent=txt;return e}
function setMsg(id,t,cls){var e=$(id);e.textContent=t||'';e.className='msg '+(cls||'')}
function fmt(b){if(b<1024)return b+' B';if(b<1048576)return (b/1024).toFixed(1)+' KB';if(b<1073741824)return (b/1048576).toFixed(1)+' MB';return (b/1073741824).toFixed(2)+' GB'}
function kindOf(f){return (/\.pdf$/i.test(f.name)||f.type==='application/pdf')?'pdf':'image'}
function needPdf(){
  if(S.batch)return true; // joined files are printed through SumatraPDF
  return !!S.cur&&kindOf(S.cur)==='pdf';
}

function req(method,url,o,cb){
  o=o||{};
  var x=new XMLHttpRequest();
  x.open(method,url);
  if(S.session)x.setRequestHeader('X-Session',S.session);
  var h=o.headers||{};
  for(var k in h){x.setRequestHeader(k,h[k])}
  if(o.progress)x.upload.onprogress=o.progress;
  x.onload=function(){
    var d={};try{d=JSON.parse(x.responseText)}catch(e){}
    if(x.status===401&&d.code==='login'){showLock('Please enter the PIN again.')}
    if(x.status===403&&d.code==='off'){showOff()}
    cb(x.status,d);
  };
  x.onerror=function(){cb(0,{})};
  x.send(o.body===undefined?null:o.body);
}

function showLock(m){
  S.session='';try{sessionStorage.removeItem('pp_s')}catch(e){}
  $('off').style.display='none';
  $('lock').style.display='block';
  $('pin').value='';
  setMsg('lockmsg',m||'','info');
}
function showOff(){$('lock').style.display='none';$('off').style.display='block'}
function hideGates(){$('lock').style.display='none';$('off').style.display='none'}

function init(){
  req('GET','/api/status',{},function(c,d){
    if(c!==200||!d.enabled){showOff();return}
    if(!S.session){showLock('');return}
    req('GET','/api/ping',{},function(c2,d2){
      if(c2===200){S.pdfOk=!!d2.pdfOk;hideGates()}
    });
  });
}
$('retry').onclick=init;

$('unlock').onclick=function(){
  var p=$('pin').value;
  if(!/^[0-9]{4}$/.test(p)){setMsg('lockmsg','Enter the 4-digit PIN.','err');return}
  $('unlock').disabled=true;
  req('POST','/api/login',{headers:{'Content-Type':'application/json'},body:JSON.stringify({pin:p})},function(c,d){
    $('unlock').disabled=false;
    if(c===200&&d.session){
      S.session=d.session;
      try{sessionStorage.setItem('pp_s',d.session)}catch(e){}
      $('pin').value='';
      init();
    }else if(c===401){setMsg('lockmsg','Wrong PIN.','err')}
    else if(c===429){setMsg('lockmsg','Too many wrong attempts. Try again later.','err')}
    else if(c===403){}
    else{setMsg('lockmsg','Network error.','err')}
  });
};

/* ---------- file list ---------- */
$('file').onchange=function(){
  var fl=$('file').files,bad=0,i,j;
  for(i=0;i<fl.length;i++){
    var f=fl[i];
    var okType=/^(application\/pdf|image\/(jpeg|png|bmp))$/.test(f.type)||/\.(pdf|jpe?g|png|bmp)$/i.test(f.name);
    if(!okType){bad++;continue}
    var dup=false;
    for(j=0;j<S.files.length;j++){var g=S.files[j];if(g.name===f.name&&g.size===f.size&&g.lastModified===f.lastModified){dup=true}}
    if(!dup)S.files.push(f);
  }
  $('file').value='';
  setMsg('fmsg',bad?'Only PDF and photos (JPG, PNG, BMP) can be printed.':'','err');
  renderFiles();
};
function swapFiles(a,b){var t=S.files[a];S.files[a]=S.files[b];S.files[b]=t;renderFiles()}
function renderFiles(){
  var box=$('files');box.innerHTML='';
  var many=S.files.length>1;
  S.files.forEach(function(f,i){
    var row=el('div','row');
    var nm=el('div','nm',(many?(i+1)+'. ':'')+f.name);
    nm.appendChild(el('small','',fmt(f.size)));
    row.appendChild(nm);
    if(many){
      var up=el('button','xbtn mv','\u25b2');up.type='button';up.disabled=(i===0);
      up.onclick=function(){swapFiles(i,i-1)};
      var dn=el('button','xbtn mv','\u25bc');dn.type='button';dn.disabled=(i===S.files.length-1);
      dn.onclick=function(){swapFiles(i,i+1)};
      row.appendChild(up);row.appendChild(dn);
    }
    var pb=el('button','pbtn','Print');pb.type='button';
    pb.onclick=function(){openDlg(f)};
    var xb=el('button','xbtn','\u00d7');xb.type='button';
    xb.onclick=function(){S.files.splice(i,1);renderFiles()};
    row.appendChild(pb);row.appendChild(xb);
    box.appendChild(row);
  });
  var pa=$('printAll');
  pa.style.display=many?'block':'none';
  pa.textContent='Print all together ('+S.files.length+')';
}
$('printAll').onclick=function(){openBatch()};

/* ---------- print dialog ---------- */
function resetDlg(){
  S.defApplied=false;
  setMsg('dmsg','','');
  $('dlg').style.display='block';
  $('copies').value=1;
  $('doprint').disabled=true;
  $('dclose').disabled=false;
}
function openDlg(f){
  S.batch=false;S.cur=f;S.caps=null;
  clearPreview();
  $('dtitle').textContent=f.name;
  resetDlg();
  $('pdfonly').style.display=kindOf(f)==='pdf'?'block':'none';
  $('pagesrow').style.display='block';
  $('pages').value='';
  $('copLbl').textContent='Copies';
  $('doprint').textContent='Print';
  startPreview();
  loadPrinters();
}
function openBatch(){
  if(S.files.length<2)return;
  S.batch=true;S.cur=null;S.caps=null;
  clearPreview();
  $('dtitle').textContent='Print all together ('+S.files.length+' files)';
  resetDlg();
  $('pdfonly').style.display=needPdf()?'block':'none';
  $('pagesrow').style.display='block';
  $('pages').value='';
  $('copLbl').textContent='Copies (whole set)';
  $('doprint').textContent='Print all';
  renderBatchPreview();
  loadPrinters();
}
$('dclose').onclick=function(){$('dlg').style.display='none';clearPreview();S.cur=null;S.batch=false;S.bTok=null};

function loadPrinters(){
  setMsg('dmsg','Looking for printers...','info');
  $('doprint').disabled=true;
  req('GET','/api/printers',{},function(c,d){
    if(c!==200){if(c!==401&&c!==403)setMsg('dmsg','Could not read printers.','err');return}
    var sel=$('printer');
    var keep=sel.value;
    try{if(!keep)keep=localStorage.getItem('pp_printer')||''}catch(e){}
    sel.innerHTML='';
    if(!d.printers||!d.printers.length){
      var o0=el('option','','No printers found');o0.value='';sel.appendChild(o0);
      S.caps=null;setMsg('dmsg','No printers found on the PC.','err');return;
    }
    d.printers.forEach(function(p){
      var o=el('option','',p);o.value=p;if(p===keep)o.selected=true;sel.appendChild(o);
    });
    setMsg('dmsg','','');
    loadCaps();
  });
}
$('refp').onclick=loadPrinters;
$('printer').onchange=function(){S.defApplied=false;loadCaps()};

function loadCaps(){
  var name=$('printer').value;if(!name)return;
  try{localStorage.setItem('pp_printer',name)}catch(e){}
  $('doprint').disabled=true;
  setMsg('dmsg','Reading printer features...','info');
  req('GET','/api/caps?printer='+encodeURIComponent(name),{},function(c,d){
    if(c!==200||!d.caps){if(c!==401&&c!==403)setMsg('dmsg',d.error||'Could not read printer features.','err');return}
    S.caps=d.caps;S.pdfOk=!!d.pdfOk;
    buildOpts();
  });
}

function buildOpts(){
  var c=S.caps,i;
  // paper sizes
  var ps=$('paper'),prev=ps.value;ps.innerHTML='';
  c.papers.forEach(function(p){var o=el('option','',p.label);o.value=p.id;if(p.id===prev)o.selected=true;ps.appendChild(o)});
  if(!prev||!ps.querySelector('option[value="'+prev+'"]')){
    var pick=c.papers.length?c.papers[0].id:'';
    for(var pi=0;pi<c.papers.length;pi++){if(c.papers[pi].id==='A4')pick='A4'}
    ps.value=pick;
  }
  // color
  if(!((S.color==='color'&&c.color)||(S.color==='mono'&&c.mono)))S.color=c.color?'color':'mono';
  renderColor();
  // two-sided
  $('duprow').style.display=(c.detected&&!c.duplex)?'none':'block';
  if(c.detected&&!c.duplex)$('duplex').value='none';
  // paper source (tray)
  var sr=$('source'),sprev=sr.value;sr.innerHTML='';
  (c.sources||[]).forEach(function(sc){var o=el('option','',sc.label);o.value=sc.id;sr.appendChild(o)});
  var spick='';
  (c.sources||[]).forEach(function(sc){if(!spick&&/auto/i.test(sc.label))spick=sc.id});
  if(!spick&&c.sources&&c.sources.length)spick=c.sources[0].id;
  if(sprev&&sr.querySelector('option[value="'+sprev+'"]'))sr.value=sprev;else sr.value=spick;
  $('srcrow').style.display=(c.sources&&c.sources.length)?'block':'none';
  S.defApplied=true;
  // copies
  $('copies').max=c.maxCopies;
  clampCopies();
  // messages
  if(needPdf()&&!S.pdfOk){
    setMsg('dmsg','PDF printing needs SumatraPDF.exe next to QRPrint.exe on the PC.','err');
    $('doprint').disabled=true;
  }else{
    setMsg('dmsg',c.detected?'':'Could not read this printer\'s features. Showing common options.',c.detected?'':'info');
    $('doprint').disabled=false;
  }
  updatePreview();
}

function renderColor(){
  var c=S.caps,seg=$('colorSeg');seg.innerHTML='';
  if(c.color&&c.mono){
    [['color','Color'],['mono','Black & white']].forEach(function(p){
      var b=el('button',S.color===p[0]?'on':'',p[1]);b.type='button';
      b.onclick=function(){S.color=p[0];renderColor();updatePreview()};
      seg.appendChild(b);
    });
  }else{
    seg.appendChild(el('div','',c.color?'Color only':'Black & white only'));
  }
}

function clampCopies(){
  var v=parseInt($('copies').value,10);
  var max=(S.caps&&S.caps.maxCopies)||999;
  if(!v||v<1)v=1;if(v>max)v=max;
  $('copies').value=v;
}
$('cm').onclick=function(){$('copies').value=(parseInt($('copies').value,10)||1)-1;clampCopies();updatePreview()};
$('cp').onclick=function(){$('copies').value=(parseInt($('copies').value,10)||1)+1;clampCopies();updatePreview()};
$('copies').onchange=function(){clampCopies();updatePreview()};
$('paper').onchange=updatePreview;
$('orient').onchange=updatePreview;

/* ---------- preview ---------- */
function clearPreview(){
  if(S.pvUrl){URL.revokeObjectURL(S.pvUrl);S.pvUrl=''}
  for(var i=0;i<S.bUrls.length;i++){URL.revokeObjectURL(S.bUrls[i])}
  S.bUrls=[];
  $('pv').innerHTML='';$('pv').className='pv';$('pvnote').textContent='';
  S.imgW=0;S.imgH=0;S.pdfDoc=null;
}
function startPreview(){
  clearPreview();
  var f=S.cur;
  S.pvUrl=URL.createObjectURL(f);
  if(kindOf(f)==='image'){
    var im=new Image();
    im.onload=function(){if(S.cur!==f)return;S.imgW=im.naturalWidth;S.imgH=im.naturalHeight;renderImagePreview()};
    im.src=S.pvUrl;
    renderImagePreview();
  }else{
    loadPdfPreview(f);
  }
}
function renderBatchPreview(){
  var pv=$('pv');pv.innerHTML='';
  for(var k=0;k<S.bUrls.length;k++){URL.revokeObjectURL(S.bUrls[k])}
  S.bUrls=[];S.bLbl=[];S.bCounts=[];
  S.files.forEach(function(f,i){
    var row=el('div','brow');
    row.appendChild(el('div','bnum',String(i+1)));
    if(kindOf(f)==='image'){
      var im=document.createElement('img');
      var u=URL.createObjectURL(f);S.bUrls.push(u);
      im.loading='lazy';im.className='bth';im.src=u;
      row.appendChild(im);
      S.bCounts.push(1);
    }else{
      row.appendChild(el('div','bth bpdf','PDF'));
      S.bCounts.push(null);
    }
    var nm=el('div','bnm',f.name);
    var lb=el('small','','');
    nm.appendChild(lb);S.bLbl.push(lb);
    row.appendChild(nm);
    pv.appendChild(row);
  });
  updateRanges();
  // count the pages of each PDF one by one, so page numbers can be shown
  var tok={};S.bTok=tok;
  function next(i){
    if(S.bTok!==tok||i>=S.files.length)return;
    if(S.bCounts[i]!==null){next(i+1);return}
    pdfCount(S.files[i],function(n){
      if(S.bTok!==tok)return;
      S.bCounts[i]=n;updateRanges();next(i+1);
    });
  }
  next(0);
  updatePreview();
}
function updateRanges(){
  var pos=1,known=true;
  for(var i=0;i<S.files.length;i++){
    var n=S.bCounts[i],lb=S.bLbl[i];
    if(!lb)continue;
    if(known&&n!==null&&n!==undefined){
      lb.textContent=(n===1)?('page '+pos):('pages '+pos+'\u2013'+(pos+n-1));
      pos+=n;
    }else{known=false;lb.textContent=''}
  }
  S.bTotal=known?(pos-1):0;
  if(S.batch&&$('pvnote'))updatePreview();
}
function pdfCount(f,cb){
  function go(){
    var fr=new FileReader();
    fr.onload=function(){
      try{
        window.pdfjsLib.GlobalWorkerOptions.workerSrc=PDFJS+'pdf.worker.min.js';
        window.pdfjsLib.getDocument({data:new Uint8Array(fr.result)}).promise.then(function(p){
          var n=p.numPages;cb(n);
        }).catch(function(){cb(null)});
      }catch(e){cb(null)}
    };
    fr.onerror=function(){cb(null)};
    fr.readAsArrayBuffer(f);
  }
  if(window.pdfjsLib){go()}
  else{loadScript(PDFJS+'pdf.min.js',function(ok){if(ok&&window.pdfjsLib){go()}else{cb(null)}})}
}
function paperDims(){
  var id=$('paper').value;
  if(S.caps&&id){for(var i=0;i<S.caps.papers.length;i++){if(S.caps.papers[i].id===id)return S.caps.papers[i]}}
  return {w:210,h:297,label:'Default'};
}
function isLandscape(){
  var o=$('orient').value;
  if(o==='landscape')return true;
  if(o==='portrait')return false;
  return S.imgW>S.imgH;
}
function noteText(){
  var d=paperDims();
  var t=(d.label||'Default')+' \u00b7 '+(S.color==='mono'?'Black & white':'Color')+' \u00b7 \u00d7'+($('copies').value||1);
  return t;
}
function renderImagePreview(){
  if(!S.cur||kindOf(S.cur)!=='image')return;
  var pv=$('pv');pv.innerHTML='';
  var d=paperDims(),w=d.w,h=d.h;
  if(isLandscape()){var t=w;w=h;h=t}
  var sheet=el('div','sheet');
  sheet.style.maxWidth=(w>h?'380px':'270px');
  sheet.style.paddingTop=(h/w*100)+'%';
  var img=document.createElement('img');img.src=S.pvUrl;
  sheet.appendChild(img);pv.appendChild(sheet);
  $('pvnote').textContent=noteText()+' \u00b7 '+(isLandscape()?'landscape':'portrait');
}
function updatePreview(){
  $('pv').className='pv'+(S.color==='mono'?' gray':'');
  if(S.batch){
    $('pvnote').textContent=S.files.length+' files joined into one print job'+(S.bTotal?' ('+S.bTotal+' pages)':'')+' \u00b7 '+noteText();
    return;
  }
  if(!S.cur)return;
  if(kindOf(S.cur)==='image'){renderImagePreview()}
  else if(S.pdfDoc){
    var n=S.pdfDoc.numPages;
    $('pvnote').textContent=n+' page'+(n===1?'':'s')+(n>MAXPV?' (preview shows the first '+MAXPV+')':'')+' \u00b7 '+noteText();
  }
}
function loadScript(src,cb){
  var s=document.createElement('script');s.src=src;
  s.onload=function(){cb(true)};s.onerror=function(){cb(false)};
  document.head.appendChild(s);
}
function loadPdfPreview(f){
  var pv=$('pv');pv.innerHTML='';
  pv.appendChild(el('div','pvmsg','Loading preview...'));
  function fallback(){
    if(S.cur!==f)return;
    pv.innerHTML='';
    pv.appendChild(el('div','pvmsg','Preview is not available (the phone needs internet for it). You can still print.'));
    var a=el('a','lnk','Open in phone viewer');a.href=S.pvUrl;a.target='_blank';
    pv.appendChild(a);
  }
  function go(){
    var fr=new FileReader();
    fr.onload=function(){
      if(S.cur!==f)return;
      try{
        window.pdfjsLib.GlobalWorkerOptions.workerSrc=PDFJS+'pdf.worker.min.js';
        window.pdfjsLib.getDocument({data:new Uint8Array(fr.result)}).promise.then(function(pdf){
          if(S.cur!==f)return;
          S.pdfDoc=pdf;pv.innerHTML='';
          updatePreview();
          renderPage(pdf,1,Math.min(pdf.numPages,MAXPV));
        }).catch(fallback);
      }catch(e){fallback()}
    };
    fr.onerror=fallback;
    fr.readAsArrayBuffer(f);
  }
  if(window.pdfjsLib){go()}
  else{loadScript(PDFJS+'pdf.min.js',function(ok){if(ok&&window.pdfjsLib){go()}else{fallback()}})}
}
function renderPage(pdf,n,last){
  if(S.pdfDoc!==pdf||n>last)return;
  pdf.getPage(n).then(function(page){
    if(S.pdfDoc!==pdf)return;
    var pv=$('pv');
    var vp=page.getViewport({scale:1});
    var cw=Math.max(200,pv.clientWidth-24);
    var sc=(cw/vp.width)*Math.min(window.devicePixelRatio||1,2);
    var v=page.getViewport({scale:sc});
    var cv=document.createElement('canvas');
    cv.width=v.width;cv.height=v.height;cv.className='pg';
    pv.appendChild(cv);
    return page.render({canvasContext:cv.getContext('2d'),viewport:v}).promise.then(function(){renderPage(pdf,n+1,last)});
  }).catch(function(){});
}

/* ---------- print ---------- */
function printBatch(){
  var files=S.files.slice();
  if(files.length<2||!S.caps)return;
  var o={
    copies:parseInt($('copies').value,10)||1,
    color:S.color,
    paper:$('paper').value,
    duplex:$('duplex').value,
    source:$('source').value,
    orientation:$('orient').value,
    scale:$('scale').value,
    pages:$('pages').value.replace(/\s+/g,'')
  };
  if(o.copies<1)o.copies=1;
  if(o.copies>S.caps.maxCopies){setMsg('dmsg','Maximum copies: '+S.caps.maxCopies,'err');return}
  if(o.pages&&!/^[0-9]+(-[0-9]+)?(,[0-9]+(-[0-9]+)?)*$/.test(o.pages)){setMsg('dmsg','Pages: use a format like 1-3,5','err');return}
  if(o.pages&&S.bTotal){
    var nums=o.pages.match(/[0-9]+/g)||[];
    for(var q=0;q<nums.length;q++){if(parseInt(nums[q],10)>S.bTotal){setMsg('dmsg','The joined document has only '+S.bTotal+' pages.','err');return}}
  }
  var printer=$('printer').value;
  var ids=[];
  $('doprint').disabled=true;
  $('dclose').disabled=true;

  function fin(c,d,pre){
    $('doprint').disabled=false;
    $('dclose').disabled=false;
    if(c===200){setMsg('dmsg','All '+files.length+' files sent: '+(d.sent||'ok'),'ok')}
    else if(c===0){setMsg('dmsg','Network error.','err')}
    else if(c===401||c===403){setMsg('dmsg','','')}
    else{setMsg('dmsg',d.error||pre||'Printing failed.','err')}
  }
  function commit(){
    setMsg('dmsg','Joining and printing '+files.length+' files...','info');
    req('POST','/api/printbatch',{
      headers:{'Content-Type':'application/json'},
      body:JSON.stringify({printer:printer,ids:ids,opts:o})
    },function(c,d){fin(c,d,'Printing failed.')});
  }
  function stage(i){
    if(i>=files.length){commit();return}
    var f=files[i];
    var label='Uploading file '+(i+1)+' of '+files.length;
    setMsg('dmsg',label+'...','info');
    req('POST','/api/stage',{
      headers:{'Content-Type':'application/octet-stream'},
      body:f,
      progress:function(e){if(e.lengthComputable)setMsg('dmsg',label+'... '+Math.round(e.loaded/e.total*100)+'%','info')}
    },function(c,d){
      if(c===200&&d.id){ids.push(d.id);stage(i+1)}
      else{fin(c,d,'Could not upload '+f.name)}
    });
  }
  stage(0);
}

$('doprint').onclick=function(){
  if(S.batch){printBatch();return}
  var f=S.cur;
  if(!f||!S.caps)return;
  var isPdf=kindOf(f)==='pdf';
  var o={
    copies:parseInt($('copies').value,10)||1,
    color:S.color,
    paper:$('paper').value,
    duplex:$('duplex').value,
    source:$('source').value,
    orientation:$('orient').value,
    scale:$('scale').value,
    pages:isPdf?$('pages').value.replace(/\s+/g,''):''
  };
  if(o.copies<1)o.copies=1;
  if(o.copies>S.caps.maxCopies){setMsg('dmsg','Maximum copies: '+S.caps.maxCopies,'err');return}
  if(o.pages&&!/^[0-9]+(-[0-9]+)?(,[0-9]+(-[0-9]+)?)*$/.test(o.pages)){setMsg('dmsg','Pages: use a format like 1-3,5','err');return}
  $('doprint').disabled=true;
  setMsg('dmsg','Sending...','info');
  req('POST','/api/print',{
    headers:{'X-Printer':encodeURIComponent($('printer').value),'X-Options':encodeURIComponent(JSON.stringify(o)),'Content-Type':'application/octet-stream'},
    body:f,
    progress:function(e){if(e.lengthComputable)setMsg('dmsg','Sending... '+Math.round(e.loaded/e.total*100)+'%','info')}
  },function(c,d){
    $('doprint').disabled=false;
    if(c===200){setMsg('dmsg','Sent: '+(d.sent||'ok'),'ok')}
    else if(c===0){setMsg('dmsg','Network error.','err')}
    else if(c===401||c===403){setMsg('dmsg','','')}
    else{setMsg('dmsg',d.error||'Printing failed.','err')}
  });
};

init();
</script></body></html>`
