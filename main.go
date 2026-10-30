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

	"://github.com"
	qrcode "://github.com"
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
