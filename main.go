package main

import (
	"bufio"
	"bytes"
	"context"
	"crypto/aes"
	"crypto/cipher"
	cryptorand "crypto/rand"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"image"
	"image/color"
	_ "image/jpeg"
	_ "image/png"
	"io"
	mathrand "math/rand"
	"net/http"
	"net/url"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"runtime"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"syscall"
	"time"
	"unsafe"

	"gioui.org/app"
	"gioui.org/font"
	"gioui.org/font/gofont"
	"gioui.org/layout"
	"gioui.org/op"
	"gioui.org/op/clip"
	"gioui.org/op/paint"
	"gioui.org/text"
	"gioui.org/unit"
	"gioui.org/widget"
	"gioui.org/widget/material"

	"github.com/bwmarrin/discordgo"
	"github.com/corona10/goimagehash"
	"golang.org/x/exp/shiny/materialdesign/icons"
)

const (
	AppName     = "Discord Shield"
	AppVersion  = "8.0"
	ThreatDBURL = "https://raw.githubusercontent.com/roralsorom/Discord-Shield/refs/heads/main/threats.json"
	ConfigFile  = "config.json"
	ProxyFile   = "proxies.txt"
	LocalDB     = "local_threats.json"
	DiscordAPI  = "https://discord.com/api/v10"
	MsgLimit    = 100
	MaxHist     = 50000
	MaxRetry    = 8
)

// ── THEME ──

var (
	colBg      = rgb(8, 8, 12)
	colSurface = rgb(16, 16, 22)
	colCard    = rgb(22, 22, 30)
	colBorder  = rgb(35, 35, 45)
	colInput   = rgb(28, 28, 38)
	colInputBd = rgb(50, 50, 65)
	colPrimary = rgb(124, 92, 255)
	colGreen   = rgb(34, 197, 94)
	colRed     = rgb(239, 68, 68)
	colAmber   = rgb(245, 158, 11)
	colText    = rgb(245, 245, 250)
	colDim     = rgb(160, 160, 175)
	colMuted   = rgb(100, 100, 115)
	colWhite   = rgb(255, 255, 255)
	colBlack   = rgb(0, 0, 0)
	colConBg   = rgb(12, 12, 18)
	colConLine = rgb(140, 140, 160)
	colTabOff  = rgb(28, 28, 38)
)

func rgb(r, g, b uint8) color.NRGBA { return color.NRGBA{R: r, G: g, B: b, A: 255} }

var (
	cR = "\033[0m"
	cE = "\033[31m"
	cG = "\033[32m"
	cY = "\033[33m"
	cC = "\033[36m"
)

// ── ICONS ──

var (
	icoShield, icoPlay, icoStop, icoPC, icoDel *widget.Icon
	icoLock, icoEye, icoTrash, icoNet           *widget.Icon
	icoWarn, icoCheck, icoRefresh, icoBolt       *widget.Icon
	icoHash, icoTerm, icoAdd, icoDown            *widget.Icon
	icoSettings, icoFolder, icoText              *widget.Icon
)

func initIcons() {
	icoShield, _ = widget.NewIcon(icons.ActionVerifiedUser)
	icoPlay, _ = widget.NewIcon(icons.AVPlayArrow)
	icoStop, _ = widget.NewIcon(icons.AVStop)
	icoPC, _ = widget.NewIcon(icons.HardwareComputer)
	icoDel, _ = widget.NewIcon(icons.ActionDelete)
	icoLock, _ = widget.NewIcon(icons.ActionLock)
	icoEye, _ = widget.NewIcon(icons.ActionVisibility)
	icoTrash, _ = widget.NewIcon(icons.ActionDelete)
	icoNet, _ = widget.NewIcon(icons.ActionSettingsEthernet)
	icoWarn, _ = widget.NewIcon(icons.AlertWarning)
	icoCheck, _ = widget.NewIcon(icons.ActionCheckCircle)
	icoRefresh, _ = widget.NewIcon(icons.NavigationRefresh)
	icoBolt, _ = widget.NewIcon(icons.ActionFlightTakeoff)
	icoHash, _ = widget.NewIcon(icons.ImagePhotoLibrary)
	icoTerm, _ = widget.NewIcon(icons.ActionCode)
	icoAdd, _ = widget.NewIcon(icons.ContentAdd)
	icoDown, _ = widget.NewIcon(icons.FileFileDownload)
	icoSettings, _ = widget.NewIcon(icons.ActionSettings)
	icoFolder, _ = widget.NewIcon(icons.FileFolderOpen)
	icoText, _ = widget.NewIcon(icons.EditorFormatQuote)
}

// ── DATA ──

type ThreatImage struct {
	Phash         string `json:"phash"`
	HashTolerance int    `json:"hash_tolerance"`
	Note          string `json:"note,omitempty"`
}

type ThreatDB struct {
	Images       []ThreatImage `json:"images"`
	TextPatterns []string      `json:"text_patterns"`
}

type AppConfig struct {
	EncryptedToken string `json:"encrypted_token"`
	Nonce          string `json:"nonce"`
}

type DiscordMessage struct {
	ID        string `json:"id"`
	Timestamp string `json:"timestamp"`
	Author    struct {
		ID string `json:"id"`
	} `json:"author"`
	Content     string              `json:"content"`
	Attachments []DiscordAttachment `json:"attachments"`
	Mentions    []struct {
		ID string `json:"id"`
	} `json:"mentions"`
	MentionRoles    []string `json:"mention_roles"`
	MentionEveryone bool     `json:"mention_everyone"`
}

type DiscordAttachment struct {
	URL         string `json:"url"`
	ContentType string `json:"content_type"`
	Filename    string `json:"filename"`
}

type chanInfo struct {
	ID   string
	Name string
}

type msgWithCh struct {
	Msg    DiscordMessage
	ChID   string
	ChName string
}

// ── STATE ──

var (
	rawToken   string
	threatDB   ThreatDB
	remoteDB   ThreatDB
	localDB    ThreatDB
	dbMu       sync.Mutex
	textRegex  *regexp.Regexp
	proxyList  []*url.URL
	proxyMu    sync.Mutex
	proxyIdx   int

	anyAtMention = regexp.MustCompile(`@\S`)
	tokenPattern = regexp.MustCompile(`\b[A-Za-z]{6,12}\b`)

	totalCh  int32
	doneCh   int32
	nDel     int32
	nSkip    int32
	nScanned int32
	running  bool
	hasCfg   bool
	cancelFn context.CancelFunc

	mode      = "delete"
	activeTab = "main"
)

// ── WIDGETS ──

var (
	edToken        widget.Editor
	edPass         widget.Editor
	edThreads      widget.Editor
	edMaxAttach    widget.Editor
	edNewHash      widget.Editor
	edNewNote      widget.Editor
	edFolderPath   widget.Editor
	edNewPattern   widget.Editor
	ckProxy        widget.Bool
	ckHeur         widget.Bool
	ckAggr         widget.Bool
	ckAttachN      widget.Bool
	ckRandTok      widget.Bool
	ckPatternRegex widget.Bool
	btStart        widget.Clickable
	btStop         widget.Clickable
	btInstall      widget.Clickable
	btRemove       widget.Clickable
	btDelMode      widget.Clickable
	btListenMode   widget.Clickable
	btTabMain      widget.Clickable
	btTabHash      widget.Clickable
	btTabPattern   widget.Clickable
	btTabConsole   widget.Clickable
	btFetchDB      widget.Clickable
	btAddHash      widget.Clickable
	btReloadHash   widget.Clickable
	btScanFolder   widget.Clickable
	btAddPattern   widget.Clickable
	btExportDB     widget.Clickable
	wLog           widget.List
	wHashList      widget.List
	wPatternList   widget.List

	hashDelBtns    []widget.Clickable
	patternDelBtns []widget.Clickable

	folderProgress    int32
	folderTotal       int32
	folderScanning    bool
	folderScanMsg     string
	folderScanMsgMu   sync.Mutex

	logLines   []string
	logMu      sync.Mutex
	statusText string
	statusCol  color.NRGBA
	statusIco  *widget.Icon
	guiReady   bool
)

type (
	C = layout.Context
	D = layout.Dimensions
)

// ── LOG ──

func Log(msg string) {
	c := msg
	for _, x := range []string{cR, cE, cG, cY, cC} {
		c = strings.ReplaceAll(c, x, "")
	}
	e := fmt.Sprintf("[%s] %s", time.Now().Format("15:04:05"), c)
	logMu.Lock()
	logLines = append(logLines, e)
	if len(logLines) > 1000 {
		logLines = logLines[len(logLines)-1000:]
	}
	logMu.Unlock()
	fmt.Println(msg)
}

func sts(msg string, col color.NRGBA, ico *widget.Icon) {
	logMu.Lock()
	statusText = msg
	statusCol = col
	statusIco = ico
	logMu.Unlock()
}

func setFolderMsg(m string) {
	folderScanMsgMu.Lock()
	folderScanMsg = m
	folderScanMsgMu.Unlock()
}

// ── PROXY ──

func nextProxy() *url.URL {
	proxyMu.Lock()
	defer proxyMu.Unlock()
	if len(proxyList) == 0 {
		return nil
	}
	p := proxyList[proxyIdx%len(proxyList)]
	proxyIdx++
	return p
}

func newClient() *http.Client {
	p := nextProxy()
	tr := &http.Transport{DisableKeepAlives: true}
	if p != nil {
		tr.Proxy = http.ProxyURL(p)
	}
	return &http.Client{Transport: tr, Timeout: 20 * time.Second}
}

func newClientNoProxy() *http.Client {
	return &http.Client{Timeout: 20 * time.Second}
}

// ── API ──

func apiGet(client *http.Client, token, path string) ([]byte, int, error) {
	req, err := http.NewRequest("GET", DiscordAPI+path, nil)
	if err != nil {
		return nil, 0, err
	}
	req.Header.Set("Authorization", token)
	req.Header.Set("User-Agent", "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36")
	req.Header.Set("Content-Type", "application/json")
	resp, err := client.Do(req)
	if err != nil {
		return nil, 0, err
	}
	defer resp.Body.Close()
	body, err := io.ReadAll(resp.Body)
	return body, resp.StatusCode, err
}

func apiDelete(client *http.Client, token, chID, msgID string) (int, error) {
	path := fmt.Sprintf("/channels/%s/messages/%s", chID, msgID)
	req, err := http.NewRequest("DELETE", DiscordAPI+path, nil)
	if err != nil {
		return 0, err
	}
	req.Header.Set("Authorization", token)
	req.Header.Set("User-Agent", "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36")
	resp, err := client.Do(req)
	if err != nil {
		return 0, err
	}
	defer resp.Body.Close()
	io.ReadAll(resp.Body)
	return resp.StatusCode, nil
}

func apiMessages(client *http.Client, token, chID, before string) ([]DiscordMessage, int, error) {
	path := fmt.Sprintf("/channels/%s/messages?limit=%d", chID, MsgLimit)
	if before != "" {
		path += "&before=" + before
	}
	body, code, err := apiGet(client, token, path)
	if err != nil {
		return nil, code, err
	}
	if code != 200 {
		return nil, code, fmt.Errorf("HTTP %d", code)
	}
	var msgs []DiscordMessage
	err = json.Unmarshal(body, &msgs)
	return msgs, code, err
}

func apiGuilds(client *http.Client, token, before string) ([]struct {
	ID string `json:"id"`
}, int, error) {
	path := "/users/@me/guilds?limit=200"
	if before != "" {
		path += "&before=" + before
	}
	body, code, err := apiGet(client, token, path)
	if err != nil || code != 200 {
		return nil, code, err
	}
	var gs []struct {
		ID string `json:"id"`
	}
	err = json.Unmarshal(body, &gs)
	return gs, code, err
}

func apiChannels(client *http.Client, token, guildID string) ([]struct {
	ID   string `json:"id"`
	Name string `json:"name"`
	Type int    `json:"type"`
}, int, error) {
	path := fmt.Sprintf("/guilds/%s/channels", guildID)
	body, code, err := apiGet(client, token, path)
	if err != nil || code != 200 {
		return nil, code, err
	}
	var chs []struct {
		ID   string `json:"id"`
		Name string `json:"name"`
		Type int    `json:"type"`
	}
	err = json.Unmarshal(body, &chs)
	return chs, code, err
}

// ── MAIN ──

func main() {
	if len(os.Args) > 1 && os.Args[1] == "hash" {
		if len(os.Args) < 3 {
			fmt.Println("Usage: shield hash <image.png>")
			return
		}
		generateHashCLI(os.Args[2])
		return
	}

	enableANSI()
	mathrand.Seed(time.Now().UnixNano())
	initIcons()

	edPass.Mask = '*'
	edToken.SingleLine = true
	edPass.SingleLine = true
	edThreads.SingleLine = true
	edThreads.SetText("20")
	edMaxAttach.SingleLine = true
	edMaxAttach.SetText("3")
	edNewHash.SingleLine = true
	edNewNote.SingleLine = true
	edFolderPath.SingleLine = true
	edNewPattern.SingleLine = true
	ckHeur.Value = true
	ckAggr.Value = true
	ckAttachN.Value = true
	ckRandTok.Value = true
	wLog.List.Axis = layout.Vertical
	wHashList.List.Axis = layout.Vertical
	wPatternList.List.Axis = layout.Vertical

	hasCfg = cfgExists()
	if hasCfg {
		sts("Saved token found — enter password to unlock", colGreen, icoLock)
		Log(cG + "[+] config.json found. Enter password." + cR)
	} else {
		sts("Enter token + password to start", colDim, icoWarn)
	}

	loadLocalDB()

	go func() {
		w := new(app.Window)
		w.Option(app.Title(fmt.Sprintf("%s v%s", AppName, AppVersion)))
		w.Option(app.Size(unit.Dp(1050), unit.Dp(800)))
		th := material.NewTheme()
		th.Shaper = text.NewShaper(text.WithCollection(gofont.Collection()))
		th.Fg = colText
		var ops op.Ops
		frames := 0
		for {
			switch e := w.Event().(type) {
			case app.DestroyEvent:
				os.Exit(0)
			case app.FrameEvent:
				gtx := app.NewContext(&ops, e)
				frames++
				if frames > 5 {
					guiReady = true
				}
				drawUI(gtx, th)
				e.Frame(gtx.Ops)
			}
		}
	}()
	app.Main()
}

func generateHashCLI(path string) {
	f, err := os.Open(path)
	if err != nil {
		fmt.Printf("Cannot open: %v\n", err)
		return
	}
	defer f.Close()
	img, _, err := image.Decode(f)
	if err != nil {
		fmt.Printf("Cannot decode: %v\n", err)
		return
	}
	h, _ := goimagehash.PerceptionHash(img)
	fmt.Printf("\nPhash: %s\n", h.ToString())
}

// ── UI ──

func drawUI(gtx C, th *material.Theme) D {
	paint.Fill(gtx.Ops, colBg)
	return layout.UniformInset(unit.Dp(20)).Layout(gtx, func(gtx C) D {
		return layout.Flex{Axis: layout.Vertical}.Layout(gtx,
			rig(func(gtx C) D { return uiHeader(gtx, th) }),
			gap(16),
			rig(func(gtx C) D { return uiTabs(gtx, th) }),
			gap(14),
			layout.Flexed(1, func(gtx C) D {
				switch activeTab {
				case "hash":
					return uiHashTab(gtx, th)
				case "pattern":
					return uiPatternTab(gtx, th)
				case "console":
					return uiConsoleTab(gtx, th)
				default:
					return uiMainTab(gtx, th)
				}
			}),
		)
	})
}

func uiHeader(gtx C, th *material.Theme) D {
	return layout.Flex{Alignment: layout.Middle}.Layout(gtx,
		rig(func(gtx C) D {
			return roundRect(gtx, colPrimary, 10, func(gtx C) D {
				return layout.UniformInset(unit.Dp(8)).Layout(gtx, func(gtx C) D {
					return icoL(gtx, icoShield, 22, colWhite)
				})
			})
		}),
		gapW(14),
		rig(func(gtx C) D {
			return layout.Flex{Axis: layout.Vertical}.Layout(gtx,
				rig(func(gtx C) D {
					l := material.Label(th, unit.Sp(20), "Discord Shield")
					l.Color = colText
					l.Font.Weight = font.Bold
					return l.Layout(gtx)
				}),
				rig(func(gtx C) D {
					l := material.Label(th, unit.Sp(11), "Anti-hijack protection · v"+AppVersion)
					l.Color = colMuted
					return l.Layout(gtx)
				}),
			)
		}),
		layout.Flexed(1, func(gtx C) D { return D{} }),
		rig(func(gtx C) D {
			if !running {
				return pill(gtx, th, "IDLE", colMuted, colWhite)
			}
			return pill(gtx, th, "● RUNNING", colGreen, colBlack)
		}),
	)
}

func uiTabs(gtx C, th *material.Theme) D {
	if guiReady && btTabMain.Clicked(gtx) {
		activeTab = "main"
	}
	if guiReady && btTabHash.Clicked(gtx) {
		activeTab = "hash"
	}
	if guiReady && btTabPattern.Clicked(gtx) {
		activeTab = "pattern"
	}
	if guiReady && btTabConsole.Clicked(gtx) {
		activeTab = "console"
	}
	return layout.Flex{}.Layout(gtx,
		rig(func(gtx C) D { return tabBtn(gtx, th, &btTabMain, "Main", icoSettings, activeTab == "main") }),
		gapW(6),
		rig(func(gtx C) D {
			return tabBtn(gtx, th, &btTabHash, fmt.Sprintf("Hashes (%d)", len(threatDB.Images)), icoHash, activeTab == "hash")
		}),
		gapW(6),
		rig(func(gtx C) D {
			return tabBtn(gtx, th, &btTabPattern, fmt.Sprintf("Patterns (%d)", len(threatDB.TextPatterns)), icoText, activeTab == "pattern")
		}),
		gapW(6),
		rig(func(gtx C) D { return tabBtn(gtx, th, &btTabConsole, "Console", icoTerm, activeTab == "console") }),
	)
}

func uiMainTab(gtx C, th *material.Theme) D {
	return layout.Flex{Axis: layout.Vertical}.Layout(gtx,
		rig(func(gtx C) D { return uiStatus(gtx, th) }),
		gap(14),
		rig(func(gtx C) D { return uiCard(gtx, func(gtx C) D { return uiForm(gtx, th) }) }),
		gap(14),
		rig(func(gtx C) D { return uiButtons(gtx, th) }),
		gap(12),
		rig(func(gtx C) D { return uiStats(gtx, th) }),
	)
}

func uiStatus(gtx C, th *material.Theme) D {
	logMu.Lock()
	t, c, i := statusText, statusCol, statusIco
	logMu.Unlock()
	if t == "" {
		return D{}
	}
	return roundRect(gtx, c, 6, func(gtx C) D {
		return layout.UniformInset(unit.Dp(12)).Layout(gtx, func(gtx C) D {
			return layout.Flex{Alignment: layout.Middle}.Layout(gtx,
				rig(func(gtx C) D {
					if i == nil {
						return D{}
					}
					return icoL(gtx, i, 16, colBlack)
				}),
				gapW(8),
				rig(func(gtx C) D {
					l := material.Body2(th, t)
					l.Color = colBlack
					l.Font.Weight = font.Bold
					return l.Layout(gtx)
				}),
			)
		})
	})
}

func uiForm(gtx C, th *material.Theme) D {
	tl := "TOKEN"
	if hasCfg {
		tl = "TOKEN  •  blank = use saved"
	}
	return layout.Flex{Axis: layout.Vertical}.Layout(gtx,
		rig(func(gtx C) D {
			return layout.Flex{}.Layout(gtx,
				layout.Flexed(1, func(gtx C) D {
					return layout.Flex{Axis: layout.Vertical}.Layout(gtx,
						rig(func(gtx C) D { return label(gtx, th, tl) }),
						gap(6),
						rig(func(gtx C) D { return input(gtx, th, &edToken, "Paste token...") }),
					)
				}),
				gapW(14),
				layout.Flexed(1, func(gtx C) D {
					return layout.Flex{Axis: layout.Vertical}.Layout(gtx,
						rig(func(gtx C) D { return label(gtx, th, "MASTER PASSWORD") }),
						gap(6),
						rig(func(gtx C) D { return input(gtx, th, &edPass, "Password...") }),
					)
				}),
			)
		}),
		gap(18),
		rig(func(gtx C) D { return label(gtx, th, "MODE") }),
		gap(6),
		rig(func(gtx C) D {
			return layout.Flex{}.Layout(gtx,
				rig(func(gtx C) D {
					if guiReady && btDelMode.Clicked(gtx) {
						mode = "delete"
					}
					return toggleBtn(gtx, th, &btDelMode, "Delete history", icoTrash, mode == "delete")
				}),
				gapW(8),
				rig(func(gtx C) D {
					if guiReady && btListenMode.Clicked(gtx) {
						mode = "listen"
					}
					return toggleBtn(gtx, th, &btListenMode, "Listen live", icoEye, mode == "listen")
				}),
			)
		}),
		gap(18),
		rig(func(gtx C) D {
			return layout.Flex{Alignment: layout.Middle}.Layout(gtx,
				rig(func(gtx C) D {
					return layout.Flex{Axis: layout.Vertical}.Layout(gtx,
						rig(func(gtx C) D { return label(gtx, th, "THREADS") }),
						gap(6),
						rig(func(gtx C) D {
							gtx.Constraints.Max.X = gtx.Dp(unit.Dp(90))
							gtx.Constraints.Min.X = gtx.Dp(unit.Dp(90))
							return input(gtx, th, &edThreads, "20")
						}),
					)
				}),
				gapW(14),
				rig(func(gtx C) D {
					return layout.Flex{Axis: layout.Vertical}.Layout(gtx,
						rig(func(gtx C) D { return label(gtx, th, "MIN ATTACHMENTS") }),
						gap(6),
						rig(func(gtx C) D {
							gtx.Constraints.Max.X = gtx.Dp(unit.Dp(90))
							gtx.Constraints.Min.X = gtx.Dp(unit.Dp(90))
							return input(gtx, th, &edMaxAttach, "3")
						}),
					)
				}),
				gapW(20),
				layout.Flexed(1, func(gtx C) D {
					return layout.Flex{Axis: layout.Vertical}.Layout(gtx,
						rig(func(gtx C) D { return label(gtx, th, "DETECTION RULES") }),
						gap(6),
						rig(func(gtx C) D { return checkRow(gtx, th, &ckProxy, icoNet, "Use proxies.txt") }),
						gap(4),
						rig(func(gtx C) D { return checkRow(gtx, th, &ckHeur, icoBolt, "Smart: mention + image attachment") }),
						gap(4),
						rig(func(gtx C) D { return checkRow(gtx, th, &ckAggr, icoWarn, "Aggressive: any @ + image") }),
						gap(4),
						rig(func(gtx C) D { return checkRow(gtx, th, &ckAttachN, icoWarn, "Multi-attach: N+ image files") }),
						gap(4),
						rig(func(gtx C) D { return checkRow(gtx, th, &ckRandTok, icoWarn, "Random token (CpEqtkqr-style IDs)") }),
					)
				}),
			)
		}),
	)
}

func uiButtons(gtx C, th *material.Theme) D {
	if guiReady && btStart.Clicked(gtx) && !running {
		go startBot()
	}
	if guiReady && btStop.Clicked(gtx) && running {
		go stopBot()
	}
	if guiReady && btInstall.Clicked(gtx) {
		go installStartup()
	}
	if guiReady && btRemove.Clicked(gtx) {
		go uninstallStartup()
	}
	return layout.Flex{Alignment: layout.Middle}.Layout(gtx,
		layout.Flexed(1, func(gtx C) D {
			if running {
				return bigBtn(gtx, th, &btStop, "STOP", colRed, icoStop)
			}
			return bigBtn(gtx, th, &btStart, "START PROTECTION", colPrimary, icoPlay)
		}),
		gapW(10),
		rig(func(gtx C) D { return smallBtn(gtx, th, &btInstall, "Install", colGreen, icoPC) }),
		gapW(6),
		rig(func(gtx C) D { return smallBtn(gtx, th, &btRemove, "Remove", colRed, icoDel) }),
	)
}

func uiStats(gtx C, th *material.Theme) D {
	tc := atomic.LoadInt32(&totalCh)
	if !running && tc == 0 {
		return D{}
	}
	dc := atomic.LoadInt32(&doneCh)
	dm := atomic.LoadInt32(&nDel)
	sk := atomic.LoadInt32(&nSkip)
	scanned := atomic.LoadInt32(&nScanned)
	pct := 0
	if tc > 0 {
		pct = int(dc * 100 / tc)
	}
	return roundRect(gtx, colSurface, 6, func(gtx C) D {
		return layout.UniformInset(unit.Dp(12)).Layout(gtx, func(gtx C) D {
			return layout.Flex{}.Layout(gtx,
				layout.Flexed(1, func(gtx C) D { return statCell(gtx, th, "Progress", fmt.Sprintf("%d/%d (%d%%)", dc, tc, pct), colPrimary) }),
				layout.Flexed(1, func(gtx C) D { return statCell(gtx, th, "Deleted", fmt.Sprint(dm), colRed) }),
				layout.Flexed(1, func(gtx C) D { return statCell(gtx, th, "Skipped", fmt.Sprint(sk), colAmber) }),
				layout.Flexed(1, func(gtx C) D { return statCell(gtx, th, "Msgs Read", fmt.Sprint(scanned), colGreen) }),
				layout.Flexed(1, func(gtx C) D { return statCell(gtx, th, "Proxies", fmt.Sprint(len(proxyList)), colDim) }),
			)
		})
	})
}

func statCell(gtx C, th *material.Theme, lbl, val string, valCol color.NRGBA) D {
	return layout.Flex{Axis: layout.Vertical}.Layout(gtx,
		rig(func(gtx C) D {
			l := material.Label(th, unit.Sp(9), strings.ToUpper(lbl))
			l.Color = colMuted
			l.Font.Weight = font.Bold
			return l.Layout(gtx)
		}),
		rig(func(gtx C) D {
			l := material.Label(th, unit.Sp(14), val)
			l.Color = valCol
			l.Font.Weight = font.Bold
			return l.Layout(gtx)
		}),
	)
}

// ── HASH TAB ──

func uiHashTab(gtx C, th *material.Theme) D {
	if guiReady && btFetchDB.Clicked(gtx) {
		go func() {
			sts("Fetching remote threat DB...", colPrimary, icoRefresh)
			Log(cC + "[*] Fetching remote threat DB..." + cR)
			fetchRemoteDB()
			mergeDB()
			sts(fmt.Sprintf("Updated: %d total hashes", len(threatDB.Images)), colGreen, icoCheck)
			Log(fmt.Sprintf(cG+"[+] Remote DB: %d images, %d patterns"+cR,
				len(remoteDB.Images), len(remoteDB.TextPatterns)))
		}()
	}
	if guiReady && btAddHash.Clicked(gtx) {
		go addHashFromInput()
	}
	if guiReady && btReloadHash.Clicked(gtx) {
		loadLocalDB()
		mergeDB()
		Log(cG + "[+] Local DB reloaded" + cR)
	}
	if guiReady && btScanFolder.Clicked(gtx) && !folderScanning {
		go scanFolder(strings.TrimSpace(edFolderPath.Text()))
	}
	if guiReady && btExportDB.Clicked(gtx) {
		go exportLocalDB()
	}

	dbMu.Lock()
	imgs := make([]ThreatImage, len(threatDB.Images))
	copy(imgs, threatDB.Images)
	dbMu.Unlock()

	if len(hashDelBtns) < len(imgs) {
		hashDelBtns = append(hashDelBtns, make([]widget.Clickable, len(imgs)-len(hashDelBtns))...)
	}

	return layout.Flex{Axis: layout.Vertical}.Layout(gtx,
		rig(func(gtx C) D {
			return uiCard(gtx, func(gtx C) D {
				return layout.Flex{Axis: layout.Vertical}.Layout(gtx,
					// folder upload row
					rig(func(gtx C) D { return label(gtx, th, "SCAN FOLDER FOR IMAGES (generates phashes)") }),
					gap(6),
					rig(func(gtx C) D {
						return layout.Flex{Alignment: layout.Middle}.Layout(gtx,
							layout.Flexed(1, func(gtx C) D { return input(gtx, th, &edFolderPath, "C:\\path\\to\\scam\\images") }),
							gapW(8),
							rig(func(gtx C) D { return smallBtn(gtx, th, &btScanFolder, "Scan Folder", colPrimary, icoFolder) }),
						)
					}),
					rig(func(gtx C) D {
						folderScanMsgMu.Lock()
						fmsg := folderScanMsg
						folderScanMsgMu.Unlock()
						if fmsg == "" {
							return D{}
						}
						return layout.Inset{Top: unit.Dp(6)}.Layout(gtx, func(gtx C) D {
							l := material.Label(th, unit.Sp(11), fmsg)
							if folderScanning {
								l.Color = colAmber
							} else {
								l.Color = colGreen
							}
							return l.Layout(gtx)
						})
					}),
					gap(16),
					// manual add row
					rig(func(gtx C) D { return label(gtx, th, "ADD SINGLE HASH (phash)") }),
					gap(6),
					rig(func(gtx C) D {
						return layout.Flex{Alignment: layout.Middle}.Layout(gtx,
							layout.Flexed(2, func(gtx C) D { return input(gtx, th, &edNewHash, "p:xxxxxxxxxxxxxxxx") }),
							gapW(8),
							layout.Flexed(1, func(gtx C) D { return input(gtx, th, &edNewNote, "note (optional)") }),
							gapW(8),
							rig(func(gtx C) D { return smallBtn(gtx, th, &btAddHash, "Add", colGreen, icoAdd) }),
						)
					}),
					gap(12),
					// controls row
					rig(func(gtx C) D {
						return layout.Flex{Alignment: layout.Middle}.Layout(gtx,
							rig(func(gtx C) D { return smallBtn(gtx, th, &btFetchDB, "Fetch Remote", colPrimary, icoDown) }),
							gapW(6),
							rig(func(gtx C) D { return smallBtn(gtx, th, &btReloadHash, "Reload Local", colDim, icoRefresh) }),
							gapW(6),
							rig(func(gtx C) D { return smallBtn(gtx, th, &btExportDB, "Export DB", colAmber, icoDown) }),
							gapW(12),
							rig(func(gtx C) D {
								l := material.Label(th, unit.Sp(11),
									fmt.Sprintf("Remote: %d  ·  Local: %d  ·  Total: %d",
										len(remoteDB.Images), len(localDB.Images), len(threatDB.Images)))
								l.Color = colMuted
								return l.Layout(gtx)
							}),
						)
					}),
				)
			})
		}),
		gap(12),
		rig(func(gtx C) D { return label(gtx, th, fmt.Sprintf("STORED HASHES  (%d)", len(imgs))) }),
		gap(6),
		layout.Flexed(1, func(gtx C) D {
			return roundRect(gtx, colConBg, 8, func(gtx C) D {
				return layout.UniformInset(unit.Dp(8)).Layout(gtx, func(gtx C) D {
					if len(imgs) == 0 {
						l := material.Body2(th, "No hashes. Scan a folder, add manually, or fetch remote.")
						l.Color = colMuted
						return layout.Center.Layout(gtx, l.Layout)
					}
					return material.List(th, &wHashList).Layout(gtx, len(imgs), func(gtx C, i int) D {
						img := imgs[i]
						isLocal := isInLocalDB(img.Phash)

						if isLocal && i < len(hashDelBtns) && hashDelBtns[i].Clicked(gtx) {
							go removeLocalHash(img.Phash)
						}

						return layout.Inset{Top: unit.Dp(3), Bottom: unit.Dp(3)}.Layout(gtx, func(gtx C) D {
							return roundRect(gtx, colCard, 4, func(gtx C) D {
								return layout.UniformInset(unit.Dp(10)).Layout(gtx, func(gtx C) D {
									return layout.Flex{Alignment: layout.Middle}.Layout(gtx,
										rig(func(gtx C) D {
											src := "REMOTE"
											bg := colPrimary
											if isLocal {
												src = "LOCAL"
												bg = colGreen
											}
											return pill(gtx, th, src, bg, colBlack)
										}),
										gapW(10),
										layout.Flexed(1, func(gtx C) D {
											return layout.Flex{Axis: layout.Vertical}.Layout(gtx,
												rig(func(gtx C) D {
													l := material.Body2(th, img.Phash)
													l.Color = colText
													l.TextSize = unit.Sp(11)
													return l.Layout(gtx)
												}),
												rig(func(gtx C) D {
													note := img.Note
													if note == "" {
														note = "(no note)"
													}
													l := material.Body2(th, fmt.Sprintf("%s  ·  tol=%d", note, img.HashTolerance))
													l.Color = colMuted
													l.TextSize = unit.Sp(10)
													return l.Layout(gtx)
												}),
											)
										}),
										rig(func(gtx C) D {
											if !isLocal {
												return D{}
											}
											if i >= len(hashDelBtns) {
												return D{}
											}
											return smallBtn(gtx, th, &hashDelBtns[i], "Del", colRed, icoDel)
										}),
									)
								})
							})
						})
					})
				})
			})
		}),
	)
}

// ── PATTERN TAB ──

func uiPatternTab(gtx C, th *material.Theme) D {
	if guiReady && btAddPattern.Clicked(gtx) {
		go addPatternFromInput()
	}

	dbMu.Lock()
	pats := make([]string, len(threatDB.TextPatterns))
	copy(pats, threatDB.TextPatterns)
	dbMu.Unlock()

	if len(patternDelBtns) < len(pats) {
		patternDelBtns = append(patternDelBtns, make([]widget.Clickable, len(pats)-len(patternDelBtns))...)
	}

	return layout.Flex{Axis: layout.Vertical}.Layout(gtx,
		rig(func(gtx C) D {
			return uiCard(gtx, func(gtx C) D {
				return layout.Flex{Axis: layout.Vertical}.Layout(gtx,
					rig(func(gtx C) D { return label(gtx, th, "ADD TEXT PATTERN") }),
					gap(6),
					rig(func(gtx C) D {
						return layout.Flex{Alignment: layout.Middle}.Layout(gtx,
							layout.Flexed(1, func(gtx C) D {
								return input(gtx, th, &edNewPattern, "e.g. free nitro  OR  regex like: \\b[A-Z][a-z]+\\d{3}\\b")
							}),
							gapW(8),
							rig(func(gtx C) D {
								return layout.Flex{Alignment: layout.Middle}.Layout(gtx,
									rig(func(gtx C) D {
										cb := material.CheckBox(th, &ckPatternRegex, "Regex")
										cb.Color = colText
										cb.TextSize = unit.Sp(12)
										cb.IconColor = colPrimary
										return cb.Layout(gtx)
									}),
								)
							}),
							gapW(8),
							rig(func(gtx C) D { return smallBtn(gtx, th, &btAddPattern, "Add", colGreen, icoAdd) }),
						)
					}),
					gap(6),
					rig(func(gtx C) D {
						l := material.Label(th, unit.Sp(10),
							"Uncheck Regex for plain text (auto-escaped, case-insensitive). Check Regex to use raw regex like [a-z]+\\d.")
						l.Color = colMuted
						return l.Layout(gtx)
					}),
				)
			})
		}),
		gap(12),
		rig(func(gtx C) D { return label(gtx, th, fmt.Sprintf("STORED PATTERNS  (%d)", len(pats))) }),
		gap(6),
		layout.Flexed(1, func(gtx C) D {
			return roundRect(gtx, colConBg, 8, func(gtx C) D {
				return layout.UniformInset(unit.Dp(8)).Layout(gtx, func(gtx C) D {
					if len(pats) == 0 {
						l := material.Body2(th, "No patterns. Add one above or fetch remote DB.")
						l.Color = colMuted
						return layout.Center.Layout(gtx, l.Layout)
					}
					return material.List(th, &wPatternList).Layout(gtx, len(pats), func(gtx C, i int) D {
						p := pats[i]
						isLocal := isInLocalPatterns(p)

						if isLocal && i < len(patternDelBtns) && patternDelBtns[i].Clicked(gtx) {
							go removeLocalPattern(p)
						}

						return layout.Inset{Top: unit.Dp(3), Bottom: unit.Dp(3)}.Layout(gtx, func(gtx C) D {
							return roundRect(gtx, colCard, 4, func(gtx C) D {
								return layout.UniformInset(unit.Dp(10)).Layout(gtx, func(gtx C) D {
									return layout.Flex{Alignment: layout.Middle}.Layout(gtx,
										rig(func(gtx C) D {
											src := "REMOTE"
											bg := colPrimary
											if isLocal {
												src = "LOCAL"
												bg = colGreen
											}
											return pill(gtx, th, src, bg, colBlack)
										}),
										gapW(10),
										layout.Flexed(1, func(gtx C) D {
											l := material.Body2(th, p)
											l.Color = colText
											l.TextSize = unit.Sp(12)
											return l.Layout(gtx)
										}),
										rig(func(gtx C) D {
											if !isLocal {
												return D{}
											}
											if i >= len(patternDelBtns) {
												return D{}
											}
											return smallBtn(gtx, th, &patternDelBtns[i], "Del", colRed, icoDel)
										}),
									)
								})
							})
						})
					})
				})
			})
		}),
	)
}

// ── CONSOLE TAB ──

func uiConsoleTab(gtx C, th *material.Theme) D {
	return roundRect(gtx, colConBg, 8, func(gtx C) D {
		return layout.UniformInset(unit.Dp(12)).Layout(gtx, func(gtx C) D {
			logMu.Lock()
			lines := make([]string, len(logLines))
			copy(lines, logLines)
			logMu.Unlock()
			wLog.List.ScrollToEnd = true
			return material.List(th, &wLog).Layout(gtx, len(lines), func(gtx C, i int) D {
				l := material.Body2(th, lines[i])
				col := colConLine
				if strings.Contains(lines[i], "[!]") || strings.Contains(lines[i], "[!!]") {
					col = colRed
				} else if strings.Contains(lines[i], "[+]") {
					col = colGreen
				}
				l.Color = col
				l.TextSize = unit.Sp(11)
				return l.Layout(gtx)
			})
		})
	})
}

// ── UI HELPERS ──

func rig(w layout.Widget) layout.FlexChild  { return layout.Rigid(w) }
func gap(h float32) layout.FlexChild         { return layout.Rigid(layout.Spacer{Height: unit.Dp(h)}.Layout) }
func gapW(w float32) layout.FlexChild        { return layout.Rigid(layout.Spacer{Width: unit.Dp(w)}.Layout) }

func icoL(gtx C, i *widget.Icon, dp int, c color.NRGBA) D {
	if i == nil {
		return D{}
	}
	s := gtx.Dp(unit.Dp(dp))
	gtx.Constraints = layout.Exact(image.Pt(s, s))
	return i.Layout(gtx, c)
}

func label(gtx C, th *material.Theme, t string) D {
	l := material.Label(th, unit.Sp(10), t)
	l.Color = colMuted
	l.Font.Weight = font.Bold
	return l.Layout(gtx)
}

func input(gtx C, th *material.Theme, ed *widget.Editor, hint string) D {
	return borderedRect(gtx, colInput, colInputBd, 6, func(gtx C) D {
		return layout.UniformInset(unit.Dp(12)).Layout(gtx, func(gtx C) D {
			e := material.Editor(th, ed, hint)
			e.Color = colText
			e.HintColor = colMuted
			e.TextSize = unit.Sp(13)
			return e.Layout(gtx)
		})
	})
}

func uiCard(gtx C, w layout.Widget) D {
	return borderedRect(gtx, colCard, colBorder, 10, func(gtx C) D {
		return layout.UniformInset(unit.Dp(20)).Layout(gtx, w)
	})
}

func roundRect(gtx C, col color.NRGBA, rad int, w layout.Widget) D {
	return layout.Stack{}.Layout(gtx,
		layout.Expanded(func(gtx C) D {
			r := clip.RRect{Rect: image.Rectangle{Max: gtx.Constraints.Min}, NE: rad, NW: rad, SE: rad, SW: rad}
			paint.FillShape(gtx.Ops, col, r.Op(gtx.Ops))
			return D{Size: gtx.Constraints.Min}
		}),
		layout.Stacked(w),
	)
}

func borderedRect(gtx C, fill, border color.NRGBA, rad int, w layout.Widget) D {
	return layout.Stack{}.Layout(gtx,
		layout.Expanded(func(gtx C) D {
			r := clip.RRect{Rect: image.Rectangle{Max: gtx.Constraints.Min}, NE: rad, NW: rad, SE: rad, SW: rad}
			paint.FillShape(gtx.Ops, border, r.Op(gtx.Ops))
			return D{Size: gtx.Constraints.Min}
		}),
		layout.Expanded(func(gtx C) D {
			inner := image.Rectangle{Min: image.Pt(1, 1), Max: image.Pt(gtx.Constraints.Min.X-1, gtx.Constraints.Min.Y-1)}
			r := clip.RRect{Rect: inner, NE: rad, NW: rad, SE: rad, SW: rad}
			paint.FillShape(gtx.Ops, fill, r.Op(gtx.Ops))
			return D{Size: gtx.Constraints.Min}
		}),
		layout.Stacked(w),
	)
}

func bigBtn(gtx C, th *material.Theme, b *widget.Clickable, t string, col color.NRGBA, ic *widget.Icon) D {
	return material.Clickable(gtx, b, func(gtx C) D {
		return roundRect(gtx, col, 6, func(gtx C) D {
			return layout.UniformInset(unit.Dp(14)).Layout(gtx, func(gtx C) D {
				return layout.Flex{Alignment: layout.Middle, Spacing: layout.SpaceSides}.Layout(gtx,
					rig(func(gtx C) D { return icoL(gtx, ic, 18, colWhite) }),
					gapW(8),
					rig(func(gtx C) D {
						l := material.Label(th, unit.Sp(13), t)
						l.Color = colWhite
						l.Font.Weight = font.Bold
						return l.Layout(gtx)
					}),
				)
			})
		})
	})
}

func smallBtn(gtx C, th *material.Theme, b *widget.Clickable, t string, col color.NRGBA, ic *widget.Icon) D {
	return material.Clickable(gtx, b, func(gtx C) D {
		return roundRect(gtx, col, 6, func(gtx C) D {
			return layout.UniformInset(unit.Dp(10)).Layout(gtx, func(gtx C) D {
				return layout.Flex{Alignment: layout.Middle}.Layout(gtx,
					rig(func(gtx C) D { return icoL(gtx, ic, 14, colWhite) }),
					gapW(6),
					rig(func(gtx C) D {
						l := material.Label(th, unit.Sp(11), t)
						l.Color = colWhite
						l.Font.Weight = font.Bold
						return l.Layout(gtx)
					}),
				)
			})
		})
	})
}

func toggleBtn(gtx C, th *material.Theme, b *widget.Clickable, t string, ic *widget.Icon, selected bool) D {
	fill := colTabOff
	txtCol := colDim
	icoCol := colDim
	if selected {
		fill = colPrimary
		txtCol = colWhite
		icoCol = colWhite
	}
	return material.Clickable(gtx, b, func(gtx C) D {
		return roundRect(gtx, fill, 6, func(gtx C) D {
			return layout.UniformInset(unit.Dp(10)).Layout(gtx, func(gtx C) D {
				return layout.Flex{Alignment: layout.Middle}.Layout(gtx,
					rig(func(gtx C) D { return icoL(gtx, ic, 14, icoCol) }),
					gapW(6),
					rig(func(gtx C) D {
						l := material.Label(th, unit.Sp(12), t)
						l.Color = txtCol
						l.Font.Weight = font.Bold
						return l.Layout(gtx)
					}),
				)
			})
		})
	})
}

func tabBtn(gtx C, th *material.Theme, b *widget.Clickable, t string, ic *widget.Icon, selected bool) D {
	fill := colTabOff
	txtCol := colDim
	icoCol := colDim
	if selected {
		fill = colPrimary
		txtCol = colWhite
		icoCol = colWhite
	}
	return material.Clickable(gtx, b, func(gtx C) D {
		return roundRect(gtx, fill, 6, func(gtx C) D {
			return layout.Inset{Top: unit.Dp(10), Bottom: unit.Dp(10), Left: unit.Dp(16), Right: unit.Dp(16)}.Layout(gtx, func(gtx C) D {
				return layout.Flex{Alignment: layout.Middle}.Layout(gtx,
					rig(func(gtx C) D { return icoL(gtx, ic, 14, icoCol) }),
					gapW(6),
					rig(func(gtx C) D {
						l := material.Label(th, unit.Sp(12), t)
						l.Color = txtCol
						l.Font.Weight = font.Bold
						return l.Layout(gtx)
					}),
				)
			})
		})
	})
}

func checkRow(gtx C, th *material.Theme, b *widget.Bool, ic *widget.Icon, t string) D {
	return layout.Flex{Alignment: layout.Middle}.Layout(gtx,
		rig(func(gtx C) D { return icoL(gtx, ic, 14, colMuted) }),
		gapW(6),
		rig(func(gtx C) D {
			cb := material.CheckBox(th, b, t)
			cb.Color = colText
			cb.TextSize = unit.Sp(12)
			cb.IconColor = colPrimary
			return cb.Layout(gtx)
		}),
	)
}

func pill(gtx C, th *material.Theme, t string, bg, fg color.NRGBA) D {
	return roundRect(gtx, bg, 12, func(gtx C) D {
		return layout.Inset{Top: unit.Dp(4), Bottom: unit.Dp(4), Left: unit.Dp(10), Right: unit.Dp(10)}.Layout(gtx, func(gtx C) D {
			l := material.Label(th, unit.Sp(9), t)
			l.Color = fg
			l.Font.Weight = font.Bold
			return l.Layout(gtx)
		})
	})
}

// ── DB MANAGEMENT ──

func loadLocalDB() {
	data, err := os.ReadFile(LocalDB)
	if err != nil {
		localDB = ThreatDB{}
		return
	}
	dbMu.Lock()
	json.Unmarshal(data, &localDB)
	dbMu.Unlock()
	mergeDB()
}

func saveLocalDB() {
	dbMu.Lock()
	d, _ := json.MarshalIndent(localDB, "", "  ")
	dbMu.Unlock()
	os.WriteFile(LocalDB, d, 0644)
}

func mergeDB() {
	dbMu.Lock()
	threatDB.Images = append([]ThreatImage{}, remoteDB.Images...)
	threatDB.Images = append(threatDB.Images, localDB.Images...)
	threatDB.TextPatterns = append([]string{}, remoteDB.TextPatterns...)
	threatDB.TextPatterns = append(threatDB.TextPatterns, localDB.TextPatterns...)
	patterns := make([]string, len(threatDB.TextPatterns))
	copy(patterns, threatDB.TextPatterns)
	dbMu.Unlock()
	rebuildTextRegex(patterns)
}

func rebuildTextRegex(patterns []string) {
	if len(patterns) == 0 {
		textRegex = nil
		return
	}
	var validParts []string
	for _, p := range patterns {
		if p == "" {
			continue
		}
		// try compiling as-is first (assume regex)
		if _, err := regexp.Compile(p); err == nil {
			validParts = append(validParts, p)
		} else {
			// fall back to escaped literal
			validParts = append(validParts, regexp.QuoteMeta(p))
		}
	}
	if len(validParts) == 0 {
		textRegex = nil
		return
	}
	joined := "(?i)" + strings.Join(validParts, "|")
	re, err := regexp.Compile(joined)
	if err != nil {
		Log(fmt.Sprintf(cE+"[!] Combined regex failed: %v"+cR, err))
		textRegex = nil
		return
	}
	textRegex = re
}

func fetchRemoteDB() {
	r, err := http.Get(ThreatDBURL)
	if err != nil {
		Log(fmt.Sprintf(cE+"[!] Fetch failed: %v"+cR, err))
		return
	}
	defer r.Body.Close()
	if r.StatusCode != 200 {
		Log(fmt.Sprintf(cE+"[!] Fetch HTTP %d"+cR, r.StatusCode))
		return
	}
	b, _ := io.ReadAll(r.Body)
	dbMu.Lock()
	json.Unmarshal(b, &remoteDB)
	dbMu.Unlock()
}

func isInLocalDB(phash string) bool {
	dbMu.Lock()
	defer dbMu.Unlock()
	for _, i := range localDB.Images {
		if i.Phash == phash {
			return true
		}
	}
	return false
}

func isInLocalPatterns(p string) bool {
	dbMu.Lock()
	defer dbMu.Unlock()
	for _, x := range localDB.TextPatterns {
		if x == p {
			return true
		}
	}
	return false
}

func addHashFromInput() {
	h := strings.TrimSpace(edNewHash.Text())
	note := strings.TrimSpace(edNewNote.Text())
	if h == "" {
		sts("Enter a hash", colRed, icoWarn)
		return
	}
	if _, err := goimagehash.ImageHashFromString(h); err != nil {
		sts("Invalid hash format", colRed, icoWarn)
		Log(fmt.Sprintf(cE+"[!] Invalid hash: %v"+cR, err))
		return
	}
	dbMu.Lock()
	localDB.Images = append(localDB.Images, ThreatImage{Phash: h, HashTolerance: 20, Note: note})
	dbMu.Unlock()
	saveLocalDB()
	mergeDB()
	edNewHash.SetText("")
	edNewNote.SetText("")
	sts("Hash added", colGreen, icoCheck)
	Log(fmt.Sprintf(cG+"[+] Added hash: %s"+cR, h))
}

func removeLocalHash(phash string) {
	dbMu.Lock()
	var kept []ThreatImage
	for _, i := range localDB.Images {
		if i.Phash != phash {
			kept = append(kept, i)
		}
	}
	localDB.Images = kept
	dbMu.Unlock()
	saveLocalDB()
	mergeDB()
	Log(fmt.Sprintf(cG+"[+] Removed hash: %s"+cR, phash))
}

func addPatternFromInput() {
	p := strings.TrimSpace(edNewPattern.Text())
	if p == "" {
		sts("Enter a pattern", colRed, icoWarn)
		return
	}
	final := p
	if !ckPatternRegex.Value {
		// plain text: escape it
		final = regexp.QuoteMeta(p)
	} else {
		// regex: validate
		if _, err := regexp.Compile(p); err != nil {
			sts("Invalid regex", colRed, icoWarn)
			Log(fmt.Sprintf(cE+"[!] Invalid regex: %v"+cR, err))
			return
		}
	}
	// check duplicate
	dbMu.Lock()
	for _, x := range localDB.TextPatterns {
		if x == final {
			dbMu.Unlock()
			sts("Pattern already exists", colAmber, icoWarn)
			return
		}
	}
	localDB.TextPatterns = append(localDB.TextPatterns, final)
	dbMu.Unlock()
	saveLocalDB()
	mergeDB()
	edNewPattern.SetText("")
	sts("Pattern added", colGreen, icoCheck)
	Log(fmt.Sprintf(cG+"[+] Added pattern: %s"+cR, final))
}

func removeLocalPattern(p string) {
	dbMu.Lock()
	var kept []string
	for _, x := range localDB.TextPatterns {
		if x != p {
			kept = append(kept, x)
		}
	}
	localDB.TextPatterns = kept
	dbMu.Unlock()
	saveLocalDB()
	mergeDB()
	Log(fmt.Sprintf(cG+"[+] Removed pattern: %s"+cR, p))
}

func exportLocalDB() {
	dbMu.Lock()
	d, _ := json.MarshalIndent(localDB, "", "  ")
	dbMu.Unlock()
	name := fmt.Sprintf("threats_export_%s.json", time.Now().Format("20060102_150405"))
	os.WriteFile(name, d, 0644)
	sts("Exported to "+name, colGreen, icoCheck)
	Log(fmt.Sprintf(cG+"[+] Exported to %s"+cR, name))
}

// ── FOLDER SCAN ──

func scanFolder(folderPath string) {
	if folderPath == "" {
		sts("Enter a folder path", colRed, icoWarn)
		return
	}
	info, err := os.Stat(folderPath)
	if err != nil || !info.IsDir() {
		sts("Folder not found", colRed, icoWarn)
		Log(fmt.Sprintf(cE+"[!] Folder not accessible: %v"+cR, err))
		return
	}

	folderScanning = true
	atomic.StoreInt32(&folderProgress, 0)
	atomic.StoreInt32(&folderTotal, 0)
	setFolderMsg("Enumerating files...")
	Log(cC + "[*] Scanning folder: " + folderPath + cR)

	// find all image files
	var files []string
	filepath.Walk(folderPath, func(p string, i os.FileInfo, err error) error {
		if err != nil || i.IsDir() {
			return nil
		}
		lower := strings.ToLower(p)
		if strings.HasSuffix(lower, ".png") || strings.HasSuffix(lower, ".jpg") ||
			strings.HasSuffix(lower, ".jpeg") || strings.HasSuffix(lower, ".gif") ||
			strings.HasSuffix(lower, ".webp") || strings.HasSuffix(lower, ".bmp") {
			files = append(files, p)
		}
		return nil
	})

	atomic.StoreInt32(&folderTotal, int32(len(files)))
	setFolderMsg(fmt.Sprintf("Found %d images, hashing...", len(files)))
	Log(fmt.Sprintf(cG+"[+] Found %d images"+cR, len(files)))

	if len(files) == 0 {
		folderScanning = false
		setFolderMsg("No images found in folder")
		return
	}

	added := 0
	skipped := 0
	dup := 0

	for _, p := range files {
		atomic.AddInt32(&folderProgress, 1)
		prog := atomic.LoadInt32(&folderProgress)
		total := atomic.LoadInt32(&folderTotal)
		setFolderMsg(fmt.Sprintf("Hashing %d/%d — added %d, dup %d, err %d", prog, total, added, dup, skipped))

		f, err := os.Open(p)
		if err != nil {
			skipped++
			continue
		}
		img, _, err := image.Decode(f)
		f.Close()
		if err != nil {
			skipped++
			continue
		}
		h, err := goimagehash.PerceptionHash(img)
		if err != nil {
			skipped++
			continue
		}
		phash := h.ToString()

		if isInLocalDB(phash) {
			dup++
			continue
		}

		filename := filepath.Base(p)
		dbMu.Lock()
		localDB.Images = append(localDB.Images, ThreatImage{
			Phash:         phash,
			HashTolerance: 20,
			Note:          filename,
		})
		dbMu.Unlock()
		added++
	}

	saveLocalDB()
	mergeDB()

	folderScanning = false
	msg := fmt.Sprintf("Done! Added %d, %d duplicates, %d errors", added, dup, skipped)
	setFolderMsg(msg)
	sts(msg, colGreen, icoCheck)
	Log(cG + "[+] " + msg + cR)
}

// ── BOT ──

func getThreads() int {
	n, err := strconv.Atoi(strings.TrimSpace(edThreads.Text()))
	if err != nil || n < 1 {
		return 20
	}
	if n > 500 {
		return 500
	}
	return n
}

func getMinAttach() int {
	n, err := strconv.Atoi(strings.TrimSpace(edMaxAttach.Text()))
	if err != nil || n < 1 {
		return 3
	}
	return n
}

func startBot() {
	if running {
		return
	}
	tok := strings.TrimSpace(edToken.Text())
	pw := strings.TrimSpace(edPass.Text())
	useP := ckProxy.Value
	threads := getThreads()

	if tok == "" && !hasCfg {
		Log(cE + "[!] No token." + cR)
		sts("Enter a token", colRed, icoWarn)
		return
	}
	if pw == "" {
		Log(cE + "[!] Password required." + cR)
		sts("Password required", colRed, icoWarn)
		return
	}

	running = true
	atomic.StoreInt32(&totalCh, 0)
	atomic.StoreInt32(&doneCh, 0)
	atomic.StoreInt32(&nDel, 0)
	atomic.StoreInt32(&nSkip, 0)
	atomic.StoreInt32(&nScanned, 0)

	var ctx context.Context
	ctx, cancelFn = context.WithCancel(context.Background())
	sts("Initializing...", colPrimary, icoRefresh)

	go runBot(ctx, tok, pw, mode, useP, threads)
}

func stopBot() {
	if !running {
		return
	}
	Log(cY + "[*] Stopping..." + cR)
	if cancelFn != nil {
		cancelFn()
	}
	running = false
	sts("Stopped", colDim, icoStop)
}

func runBot(ctx context.Context, tok, pw, mode string, useP bool, threads int) {
	defer func() {
		if r := recover(); r != nil {
			Log(fmt.Sprintf(cE+"[!] Panic: %v"+cR, r))
			sts("Crashed", colRed, icoWarn)
		}
		running = false
	}()

	if useP {
		loadProxies()
		if len(proxyList) > 0 {
			Log(fmt.Sprintf(cG+"[+] %d proxies loaded, validating..."+cR, len(proxyList)))
			validateProxies(ctx)
			Log(fmt.Sprintf(cG+"[+] %d proxies working."+cR, len(proxyList)))
		}
	}

	sts("Scanning Discord files...", colPrimary, icoShield)
	scanInjections()

	sts("Fetching threats...", colPrimary, icoRefresh)
	fetchRemoteDB()
	loadLocalDB()
	Log(fmt.Sprintf(cG+"[+] Threats: %d images, %d patterns."+cR, len(threatDB.Images), len(threatDB.TextPatterns)))

	sts("Resolving token...", colPrimary, icoLock)
	if err := resolveToken(tok, pw); err != nil {
		Log(fmt.Sprintf(cE+"[!] %s"+cR, err))
		sts(err.Error(), colRed, icoWarn)
		return
	}

	go clipGuard(ctx)

	if mode == "delete" {
		sts("Verifying token...", colPrimary, icoLock)
		client := newClient()
		body, code, err := apiGet(client, rawToken, "/users/@me")
		if err != nil || code != 200 {
			body, code, err = apiGet(newClientNoProxy(), rawToken, "/users/@me")
			if err != nil || code != 200 {
				Log(fmt.Sprintf(cE+"[!] Token invalid (HTTP %d)"+cR, code))
				sts("Token invalid", colRed, icoWarn)
				return
			}
		}
		var me struct {
			Username string `json:"username"`
			ID       string `json:"id"`
		}
		json.Unmarshal(body, &me)
		Log(fmt.Sprintf(cG+"[+] Online: %s (%s)"+cR, me.Username, me.ID))
		sts(fmt.Sprintf("Online: %s — %d threads", me.Username, threads), colGreen, icoCheck)

		doCleanup(ctx, me.ID, threads)
		if ctx.Err() == nil {
			d := atomic.LoadInt32(&nDel)
			sts(fmt.Sprintf("Done! %d deleted", d), colGreen, icoCheck)
			Log(fmt.Sprintf(cG+"[+] Complete! %d deleted."+cR, d))
		}
	} else {
		sts("Connecting gateway...", colPrimary, icoNet)
		dg, err := discordgo.New(rawToken)
		if err != nil {
			return
		}
		dg.StateEnabled = true
		dg.LogLevel = discordgo.LogError

		ready := make(chan string, 1)
		dg.AddHandler(func(s *discordgo.Session, r *discordgo.Ready) { ready <- r.User.Username })
		dg.AddHandler(func(s *discordgo.Session, m *discordgo.MessageCreate) {
			if m.Author.ID != s.State.User.ID {
				return
			}
			reason := detectScamLive(m.Message)
			if reason != "" {
				client := newClient()
				code, _ := apiDelete(client, rawToken, m.ChannelID, m.ID)
				if code == 204 {
					atomic.AddInt32(&nDel, 1)
					Log(fmt.Sprintf(cE+"[!!] HIJACK BLOCKED: %s"+cR, reason))
					sts("HIJACK BLOCKED!", colRed, icoWarn)
				}
			}
		})

		if err := dg.Open(); err != nil {
			return
		}
		defer dg.Close()

		select {
		case name := <-ready:
			Log(fmt.Sprintf(cG+"[+] Listening: %s"+cR, name))
			sts(fmt.Sprintf("Listening: %s", name), colGreen, icoEye)
			<-ctx.Done()
		case <-ctx.Done():
		}
	}
}

func validateProxies(ctx context.Context) {
	var valid []*url.URL
	var mu sync.Mutex
	var wg sync.WaitGroup
	sem := make(chan struct{}, 50)
	for _, p := range proxyList {
		wg.Add(1)
		sem <- struct{}{}
		go func(pp *url.URL) {
			defer wg.Done()
			defer func() { <-sem }()
			if ctx.Err() != nil {
				return
			}
			tr := &http.Transport{Proxy: http.ProxyURL(pp), DisableKeepAlives: true}
			cl := &http.Client{Transport: tr, Timeout: 6 * time.Second}
			resp, err := cl.Get("https://discord.com/api/v10/gateway")
			if err == nil {
				resp.Body.Close()
				if resp.StatusCode == 200 || resp.StatusCode == 401 {
					mu.Lock()
					valid = append(valid, pp)
					mu.Unlock()
				}
			}
		}(p)
	}
	wg.Wait()
	proxyMu.Lock()
	proxyList = valid
	proxyIdx = 0
	proxyMu.Unlock()
}

func resolveToken(tok, pw string) error {
	if tok != "" {
		rawToken = tok
		enc, nonce, err := encrypt(rawToken, pw)
		if err != nil {
			return err
		}
		d, _ := json.MarshalIndent(AppConfig{EncryptedToken: enc, Nonce: nonce}, "", "  ")
		os.WriteFile(ConfigFile, d, 0644)
		Log(cG + "[+] Token saved." + cR)
		hasCfg = true
		return nil
	}
	if !cfgExists() {
		return fmt.Errorf("no token or config")
	}
	d, err := os.ReadFile(ConfigFile)
	if err != nil {
		return err
	}
	var cfg AppConfig
	if err := json.Unmarshal(d, &cfg); err != nil {
		return fmt.Errorf("corrupt config")
	}
	dec, err := decrypt(cfg.EncryptedToken, cfg.Nonce, pw)
	if err != nil {
		return fmt.Errorf("wrong password")
	}
	rawToken = dec
	Log(cG + "[+] Token decrypted." + cR)
	return nil
}

func cfgExists() bool { _, e := os.Stat(ConfigFile); return e == nil }

// ── CLEANUP ──

func doCleanup(ctx context.Context, myID string, threads int) {
	Log(cC + "[*] Fetching channel list..." + cR)
	dg, err := discordgo.New(rawToken)
	if err != nil {
		return
	}
	dg.StateEnabled = true
	dg.LogLevel = discordgo.LogError
	readyCh := make(chan struct{}, 1)
	dg.AddHandler(func(s *discordgo.Session, r *discordgo.Ready) { readyCh <- struct{}{} })
	if err := dg.Open(); err != nil {
		return
	}
	select {
	case <-readyCh:
	case <-time.After(20 * time.Second):
		dg.Close()
		return
	case <-ctx.Done():
		dg.Close()
		return
	}

	var chs []chanInfo
	dg.State.RLock()
	for _, dm := range dg.State.PrivateChannels {
		name := "Group"
		if len(dm.Recipients) > 0 {
			name = "DM:" + dm.Recipients[0].Username
		}
		chs = append(chs, chanInfo{ID: dm.ID, Name: name})
	}
	dg.State.RUnlock()
	dmCount := len(chs)
	Log(fmt.Sprintf(cG+"[+] %d DMs"+cR, dmCount))
	dg.Close()

	Log(cC + "[*] Fetching servers..." + cR)
	client := newClient()
	bid := ""
	fail := 0
	for {
		if ctx.Err() != nil {
			return
		}
		gs, code, err := apiGuilds(client, rawToken, bid)
		if err != nil || code != 200 {
			fail++
			if fail > 5 {
				break
			}
			sleepCtx(ctx, 5*time.Second)
			client = newClient()
			continue
		}
		fail = 0
		for _, g := range gs {
			gChs, gCode, _ := apiChannels(client, rawToken, g.ID)
			retries := 0
			for gCode != 200 && retries < 3 {
				sleepCtx(ctx, 2*time.Second)
				client = newClient()
				gChs, gCode, _ = apiChannels(client, rawToken, g.ID)
				retries++
			}
			for _, c := range gChs {
				if c.Type == 0 {
					chs = append(chs, chanInfo{ID: c.ID, Name: "#" + c.Name})
				}
			}
		}
		if len(gs) < 200 {
			break
		}
		bid = gs[len(gs)-1].ID
	}

	Log(fmt.Sprintf(cG+"[+] %d total channels"+cR, len(chs)))
	atomic.StoreInt32(&totalCh, int32(len(chs)))

	q := make(chan chanInfo, len(chs))
	imgQ := make(chan msgWithCh, 5000)
	var wR, wI sync.WaitGroup

	imgW := threads / 4
	if imgW < 2 {
		imgW = 2
	}
	readW := threads - imgW
	if readW < 1 {
		readW = 1
	}

	for i := 0; i < imgW; i++ {
		wI.Add(1)
		go func() {
			defer wI.Done()
			cl := newClient()
			for m := range imgQ {
				if ctx.Err() != nil {
					continue
				}
				if imgScamRaw(cl, m.Msg) {
					dc := newClient()
					tryDelete(ctx, dc, m.ChID, m.Msg.ID, fmt.Sprintf("image match [%s]", m.ChName))
				}
			}
		}()
	}

	for i := 0; i < readW; i++ {
		wR.Add(1)
		go func(wid int) {
			defer wR.Done()
			time.Sleep(time.Duration(wid*20) * time.Millisecond)
			cl := newClient()
			for ch := range q {
				if ctx.Err() != nil {
					continue
				}
				scanChRaw(ctx, cl, ch, myID, imgQ)
				pc := atomic.AddInt32(&doneCh, 1)
				tc := atomic.LoadInt32(&totalCh)
				pct := 0
				if tc > 0 {
					pct = int(pc * 100 / tc)
				}
				sts(fmt.Sprintf("Scanning %d/%d (%d%%)", pc, tc, pct), colPrimary, icoShield)
			}
		}(i)
	}

	for _, c := range chs {
		q <- c
	}
	close(q)
	wR.Wait()
	close(imgQ)
	wI.Wait()
}

func tryDelete(ctx context.Context, cl *http.Client, chID, msgID, reason string) {
	for attempt := 0; attempt < 5; attempt++ {
		if ctx.Err() != nil {
			return
		}
		code, err := apiDelete(cl, rawToken, chID, msgID)
		if code == 204 {
			atomic.AddInt32(&nDel, 1)
			Log(fmt.Sprintf(cG+"  [+] Deleted %s"+cR, reason))
			return
		}
		if code == 404 || code == 403 {
			return
		}
		if code == 429 || err != nil {
			sleepCtx(ctx, time.Duration(2+attempt*2)*time.Second)
			cl = newClient()
			continue
		}
		return
	}
}

func scanChRaw(ctx context.Context, client *http.Client, ch chanInfo, myID string, imgQ chan msgWithCh) {
	bid := ""
	n := 0
	retry := 0
	minAtt := getMinAttach()

	for {
		if ctx.Err() != nil {
			return
		}
		msgs, code, err := apiMessages(client, rawToken, ch.ID, bid)
		if code == 403 || code == 404 {
			atomic.AddInt32(&nSkip, 1)
			return
		}
		if err != nil || code == 429 || code == 0 || (code >= 500 && code < 600) ||
			(err != nil && strings.Contains(strings.ToLower(err.Error()), "invalid character")) {
			retry++
			if retry > MaxRetry {
				atomic.AddInt32(&nSkip, 1)
				return
			}
			w := time.Duration(1+retry*2) * time.Second
			if code == 429 {
				w = time.Duration(3+retry*3) * time.Second
			}
			sleepCtx(ctx, w)
			client = newClient()
			continue
		}
		if code != 200 {
			atomic.AddInt32(&nSkip, 1)
			return
		}
		retry = 0
		if len(msgs) == 0 {
			return
		}

		for _, msg := range msgs {
			bid = msg.ID
			n++
			atomic.AddInt32(&nScanned, 1)
			if n > MaxHist {
				return
			}
			if msg.Author.ID != myID {
				continue
			}

			if txtScam(msg.Content) {
				tryDelete(ctx, newClient(), ch.ID, msg.ID, fmt.Sprintf("text pattern [%s]", ch.Name))
				continue
			}

			imgAtt := countImageAttachments(msg)

			if ckRandTok.Value && imgAtt > 0 && hasRandomToken(msg.Content) {
				tryDelete(ctx, newClient(), ch.ID, msg.ID, fmt.Sprintf("random token [%s]", ch.Name))
				continue
			}

			if ckAttachN.Value && imgAtt >= minAtt {
				tryDelete(ctx, newClient(), ch.ID, msg.ID, fmt.Sprintf("%d attachments [%s]", imgAtt, ch.Name))
				continue
			}

			if ckHeur.Value && imgAtt > 0 && hasAnyMention(msg) {
				tryDelete(ctx, newClient(), ch.ID, msg.ID, fmt.Sprintf("mention+image [%s]", ch.Name))
				continue
			}

			if ckAggr.Value && imgAtt > 0 && strings.Contains(msg.Content, "@") {
				tryDelete(ctx, newClient(), ch.ID, msg.ID, fmt.Sprintf("@ + image [%s]", ch.Name))
				continue
			}

			if imgAtt > 0 {
				select {
				case imgQ <- msgWithCh{Msg: msg, ChID: ch.ID, ChName: ch.Name}:
				case <-ctx.Done():
					return
				}
			}
		}

		if len(msgs) < MsgLimit {
			return
		}
		time.Sleep(50 * time.Millisecond)
	}
}

// ── DETECTION ──

func txtScam(content string) bool {
	return textRegex != nil && content != "" && textRegex.MatchString(content)
}

func hasAnyMention(msg DiscordMessage) bool {
	if len(msg.Mentions) > 0 || len(msg.MentionRoles) > 0 || msg.MentionEveryone {
		return true
	}
	if anyAtMention.MatchString(msg.Content) {
		return true
	}
	return false
}

func isRandomToken(s string) bool {
	if len(s) < 6 || len(s) > 12 {
		return false
	}
	hasUpper := false
	hasLower := false
	for _, c := range s {
		if c >= 'A' && c <= 'Z' {
			hasUpper = true
		} else if c >= 'a' && c <= 'z' {
			hasLower = true
		} else {
			return false
		}
	}
	if !hasUpper || !hasLower {
		return false
	}
	allButFirstLower := true
	for i, c := range s {
		if i == 0 {
			continue
		}
		if c >= 'A' && c <= 'Z' {
			allButFirstLower = false
			break
		}
	}
	if allButFirstLower {
		return false
	}
	return true
}

func hasRandomToken(content string) bool {
	tokens := tokenPattern.FindAllString(content, -1)
	for _, t := range tokens {
		if isRandomToken(t) {
			return true
		}
	}
	return false
}

func countImageAttachments(msg DiscordMessage) int {
	n := 0
	for _, a := range msg.Attachments {
		if strings.HasPrefix(a.ContentType, "image/") {
			n++
			continue
		}
		lower := strings.ToLower(a.URL + " " + a.Filename)
		if strings.Contains(lower, ".png") || strings.Contains(lower, ".jpg") ||
			strings.Contains(lower, ".jpeg") || strings.Contains(lower, ".gif") ||
			strings.Contains(lower, ".webp") {
			n++
		}
	}
	return n
}

func detectScamLive(m *discordgo.Message) string {
	if txtScam(m.Content) {
		return "text pattern"
	}
	msg := DiscordMessage{Content: m.Content, MentionEveryone: m.MentionEveryone, MentionRoles: m.MentionRoles}
	for _, u := range m.Mentions {
		msg.Mentions = append(msg.Mentions, struct {
			ID string `json:"id"`
		}{ID: u.ID})
	}
	for _, a := range m.Attachments {
		msg.Attachments = append(msg.Attachments, DiscordAttachment{URL: a.URL, ContentType: a.ContentType, Filename: a.Filename})
	}
	imgAtt := countImageAttachments(msg)
	minAtt := getMinAttach()

	if ckRandTok.Value && imgAtt > 0 && hasRandomToken(m.Content) {
		return "random token + image"
	}
	if ckAttachN.Value && imgAtt >= minAtt {
		return fmt.Sprintf("%d attachments", imgAtt)
	}
	if ckHeur.Value && imgAtt > 0 && hasAnyMention(msg) {
		return "mention+image"
	}
	if ckAggr.Value && imgAtt > 0 && strings.Contains(m.Content, "@") {
		return "@ + image"
	}
	if imgAtt > 0 && imgScamRaw(newClient(), msg) {
		return "image hash"
	}
	return ""
}

func imgScamRaw(client *http.Client, msg DiscordMessage) bool {
	for _, a := range msg.Attachments {
		if countImageAttachments(DiscordMessage{Attachments: []DiscordAttachment{a}}) == 0 {
			continue
		}
		r, err := client.Get(a.URL)
		if err != nil {
			continue
		}
		if r.StatusCode != 200 {
			r.Body.Close()
			continue
		}
		d, err := io.ReadAll(r.Body)
		r.Body.Close()
		if err != nil {
			continue
		}
		img, _, err := image.Decode(bytes.NewReader(d))
		if err != nil {
			continue
		}
		h, err := goimagehash.PerceptionHash(img)
		if err != nil {
			continue
		}
		dbMu.Lock()
		images := make([]ThreatImage, len(threatDB.Images))
		copy(images, threatDB.Images)
		dbMu.Unlock()
		for _, t := range images {
			th, err := goimagehash.ImageHashFromString(t.Phash)
			if err != nil {
				continue
			}
			dist, _ := h.Distance(th)
			tol := t.HashTolerance
			if tol < 20 {
				tol = 20
			}
			if dist <= tol {
				return true
			}
		}
	}
	return false
}

// ── SECURITY ──

func scanInjections() {
	if runtime.GOOS != "windows" {
		return
	}
	local := os.Getenv("LOCALAPPDATA")
	dirs := []string{
		filepath.Join(local, "Discord"),
		filepath.Join(local, "DiscordCanary"),
		filepath.Join(local, "DiscordPTB"),
	}
	exp := `module.exports = require('./core.asar');`
	ok := true
	for _, b := range dirs {
		ms, _ := filepath.Glob(filepath.Join(b, "app-*"))
		for _, m := range ms {
			p := filepath.Join(m, "modules", "discord_desktop_core-1", "index.js")
			d, err := os.ReadFile(p)
			if err != nil {
				continue
			}
			if strings.TrimSpace(string(d)) != exp {
				ok = false
				Log(cE + "[!!] Injection: " + p + cR)
				os.WriteFile(p, []byte(exp), 0644)
				Log(cG + "[+] Cleaned." + cR)
			}
		}
	}
	if ok {
		Log(cG + "[+] Discord clean." + cR)
	}
}

func clipGuard(ctx context.Context) {
	if runtime.GOOS != "windows" {
		return
	}
	for {
		select {
		case <-ctx.Done():
			return
		case <-time.After(3 * time.Second):
		}
		o, err := exec.Command("powershell", "-NoProfile", "-Command", "Get-Clipboard").Output()
		if err != nil {
			continue
		}
		if strings.TrimSpace(string(o)) == rawToken && rawToken != "" {
			exec.Command("cmd", "/c", "echo off | clip").Run()
			Log(cE + "[SHIELD] Token wiped!" + cR)
		}
	}
}

func sleepCtx(ctx context.Context, d time.Duration) {
	select {
	case <-ctx.Done():
	case <-time.After(d):
	}
}

func deriveKey(p string) []byte { h := sha256.Sum256([]byte(p)); return h[:] }

func encrypt(tok, pw string) (string, string, error) {
	k := deriveKey(pw)
	b, _ := aes.NewCipher(k)
	g, _ := cipher.NewGCM(b)
	n := make([]byte, g.NonceSize())
	io.ReadFull(cryptorand.Reader, n)
	return hex.EncodeToString(g.Seal(nil, n, []byte(tok), nil)), hex.EncodeToString(n), nil
}

func decrypt(enc, nh, pw string) (string, error) {
	k := deriveKey(pw)
	b, _ := aes.NewCipher(k)
	g, _ := cipher.NewGCM(b)
	n, _ := hex.DecodeString(nh)
	c, _ := hex.DecodeString(enc)
	p, err := g.Open(nil, n, c, nil)
	return string(p), err
}

func loadProxies() {
	proxyList = nil
	proxyIdx = 0
	f, err := os.Open(ProxyFile)
	if err != nil {
		return
	}
	defer f.Close()
	sc := bufio.NewScanner(f)
	for sc.Scan() {
		l := strings.TrimSpace(sc.Text())
		if l == "" || strings.HasPrefix(l, "#") {
			continue
		}
		if !strings.HasPrefix(l, "http://") && !strings.HasPrefix(l, "https://") && !strings.HasPrefix(l, "socks5://") {
			l = "http://" + l
		}
		u, err := url.Parse(l)
		if err == nil {
			proxyList = append(proxyList, u)
		}
	}
}

func installStartup() {
	if runtime.GOOS != "windows" {
		return
	}
	e, _ := os.Executable()
	exec.Command("reg", "add", `HKCU\Software\Microsoft\Windows\CurrentVersion\Run`,
		"/v", "DiscordShield", "/t", "REG_SZ", "/d", e, "/f").Run()
	Log(cG + "[+] Startup installed." + cR)
	sts("Startup installed", colGreen, icoCheck)
}

func uninstallStartup() {
	if runtime.GOOS != "windows" {
		return
	}
	exec.Command("reg", "delete", `HKCU\Software\Microsoft\Windows\CurrentVersion\Run`,
		"/v", "DiscordShield", "/f").Run()
	Log(cG + "[+] Startup removed." + cR)
	sts("Startup removed", colGreen, icoCheck)
}

func enableANSI() {
	if runtime.GOOS != "windows" {
		return
	}
	k := syscall.NewLazyDLL("kernel32.dll")
	s := k.NewProc("SetConsoleMode")
	g := k.NewProc("GetConsoleMode")
	h := syscall.Handle(os.Stderr.Fd())
	var m uint32
	g.Call(uintptr(h), uintptr(unsafe.Pointer(&m)))
	s.Call(uintptr(h), uintptr(m|0x0007))
}
