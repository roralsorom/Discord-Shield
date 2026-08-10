package main

import (
    "bufio"
    "bytes"
    "context"
    "crypto/aes"
    "crypto/cipher"
    "crypto/rand"
    "crypto/sha256"
    "encoding/hex"
    "encoding/json"
    "fmt"
    "image"
    _ "image/jpeg"
    _ "image/png"
    "io"
    "log"
    "math"
    "net/http"
    "os"
    "os/exec"
    "path/filepath"
    "regexp"
    "runtime"
    "strings"
    "sync"
    "time"

    "github.com/bwmarrin/discordgo"
    "github.com/corona10/goimagehash"
    "golang.org/x/time/rate"
    "golang.org/x/term"
)

// --- CONFIGURATION ---
const (
    ThreatDBURL  = "https://raw.githubusercontent.com/yourusername/yourrepo/main/threats.json"
    MessageLimit = 100
    WorkerCount  = 5
)

type ThreatImage struct {
    Phash         string `json:"phash"`
    Size          int64  `json:"size"`
    SizeTolerance int64  `json:"size_tolerance"`
    HashTolerance int    `json:"hash_tolerance"`
}

type ThreatDB struct {
    Images       []ThreatImage `json:"images"`
    TextPatterns []string      `json:"text_patterns"`
}

type AppConfig struct {
    EncryptedToken string `json:"encrypted_token"`
    Nonce          string `json:"nonce"`
}

var limiter = rate.NewLimiter(rate.Every(time.Second/20), 1)
var rawToken string
var threatDB ThreatDB
var textRegex *regexp.Regexp

func main() {
    discordgo.Logger = func(level, caller int, format string, a ...interface{}) {}

    reader := bufio.NewReader(os.Stdin)

    // 1. Select Mode
    fmt.Println("--- Discord Hijack Guard ---")
    fmt.Print("[?] Select Mode (generate, delete, listen): ")
    mode, _ := reader.ReadString('\n')
    mode = strings.TrimSpace(strings.ToLower(mode))

    if mode == "generate" {
        fmt.Print("[?] Enter folder path containing scam images: ")
        folderPath, _ := reader.ReadString('\n')
        generateThreatJSON(strings.TrimSpace(folderPath))
        return
    }

    // 2. Security Scan & Fetch DB
    fmt.Println("[*] Running local security scan...")
    scanDiscordInjections()

    fmt.Println("[*] Fetching latest threat database from GitHub...")
    if err := fetchThreatDB(); err != nil {
        log.Fatalf("Failed to fetch threat database: %v", err)
    }
    fmt.Printf("[+] Loaded %d image hashes and %d text patterns.\n", len(threatDB.Images), len(threatDB.TextPatterns))

    if len(threatDB.TextPatterns) > 0 {
        escapedPatterns := make([]string, len(threatDB.TextPatterns))
        for i, p := range threatDB.TextPatterns {
            escapedPatterns[i] = regexp.QuoteMeta(p)
        }
        textRegex = regexp.MustCompile(strings.Join(escapedPatterns, "|"))
    }

    // 3. Token Protector
    var cfg AppConfig
    if _, err := os.Stat("config.json"); err == nil {
        fmt.Print("[?] Enter Master Password to unlock token: ")
        passwordBytes, _ := term.ReadPassword(int(os.Stdin.Fd()))
        fmt.Println()

        configData, _ := os.ReadFile("config.json")
        json.Unmarshal(configData, &cfg)

        decrypted, err := decryptToken(cfg.EncryptedToken, cfg.Nonce, string(passwordBytes))
        if err != nil {
            log.Fatalf("Failed to decrypt token. Wrong password or corrupted file.")
        }
        rawToken = decrypted
        fmt.Println("[+] Token decrypted successfully!")
    } else {
        fmt.Print("[?] Enter your Discord Token: ")
        tokenInput, _ := reader.ReadString('\n')
        rawToken = strings.TrimSpace(tokenInput)

        fmt.Print("[?] Create a Master Password to protect your token: ")
        passwordBytes, _ := term.ReadPassword(int(os.Stdin.Fd()))
        fmt.Println()

        encToken, nonce, _ := encryptToken(rawToken, string(passwordBytes))
        cfg = AppConfig{
            EncryptedToken: encToken,
            Nonce:          nonce,
        }
        configData, _ := json.MarshalIndent(cfg, "", "  ")
        os.WriteFile("config.json", configData, 0644)
        fmt.Println("[+] Token encrypted and saved to config.json!")
    }

    go clipboardProtector()

    // 4. Initialize Discord
    dg, err := discordgo.New(rawToken)
    if err != nil {
        log.Fatalf("Error creating Discord session: %v", err)
    }

    dg.UserAgent = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36"

    dg.AddHandler(func(s *discordgo.Session, r *discordgo.Ready) {
        fmt.Printf("[+] Logged in as %s (%s)\n", r.User.Username, r.User.ID)
        if mode == "delete" {
            fmt.Println("[*] Starting DELETE mode...")
            go startCleanup(s, r.User.ID)
        } else if mode == "listen" {
            fmt.Println("[*] Starting LISTEN mode... Waiting for hijackers.")
        }
    })

    if mode == "listen" {
        dg.AddHandler(func(s *discordgo.Session, m *discordgo.MessageCreate) {
            listenHandler(s, m)
        })
    }

    err = dg.Open()
    if err != nil {
        log.Fatalf("Error opening connection: %v", err)
    }
    defer dg.Close()

    select {}
}

// --- THREAT JSON GENERATOR ---
func generateThreatJSON(folderPath string) {
    files, err := os.ReadDir(folderPath)
    if err != nil {
        log.Fatalf("Failed to read folder: %v", err)
    }

    // Load existing JSON if it exists
    var db ThreatDB
    if _, err := os.Stat("threats.json"); err == nil {
        data, _ := os.ReadFile("threats.json")
        json.Unmarshal(data, &db)
        fmt.Println("[*] Found existing threats.json. Appending to it...")
    }

    existingHashes := make(map[string]bool)
    for _, img := range db.Images {
        existingHashes[img.Phash] = true
    }

    newCount := 0
    for _, file := range files {
        if file.IsDir() {
            continue
        }
        ext := strings.ToLower(filepath.Ext(file.Name()))
        if ext != ".png" && ext != ".jpg" && ext != ".jpeg" {
            continue
        }

        fullPath := filepath.Join(folderPath, file.Name())
        f, err := os.Open(fullPath)
        if err != nil {
            continue
        }

        img, _, err := image.Decode(f)
        f.Close()
        if err != nil {
            fmt.Printf("[!] Failed to decode %s: %v\n", file.Name(), err)
            continue
        }

        phash, err := goimagehash.PerceptionHash(img)
        if err != nil {
            continue
        }

        hashStr := phash.ToString()
        if existingHashes[hashStr] {
            fmt.Printf("[~] Skipping %s (Already in database)\n", file.Name())
            continue
        }

        fileInfo, _ := os.Stat(fullPath)

        threat := ThreatImage{
            Phash:         hashStr,
            Size:          fileInfo.Size(),
            SizeTolerance: 1024 * 5,
            HashTolerance: 4,
        }

        db.Images = append(db.Images, threat)
        existingHashes[hashStr] = true
        newCount++
        fmt.Printf("[+] Added %s (Hash: %s)\n", file.Name(), hashStr)
    }

    if newCount == 0 {
        fmt.Println("[*] No new images to add.")
        return
    }

    data, _ := json.MarshalIndent(db, "", "  ")
    os.WriteFile("threats.json", data, 0644)
    fmt.Printf("\n[+] Success! Added %d new images. threats.json saved.\n", newCount)
}

// --- GITHUB THREAT DB FETCHER ---
func fetchThreatDB() error {
    resp, err := http.Get(ThreatDBURL)
    if err != nil {
        return err
    }
    defer resp.Body.Close()

    if resp.StatusCode != 200 {
        return fmt.Errorf("github returned status %d", resp.StatusCode)
    }

    body, err := io.ReadAll(resp.Body)
    if err != nil {
        return err
    }

    return json.Unmarshal(body, &threatDB)
}

// --- ANTI-LOGGER & DISCORD INJECTION SCANNER ---
func scanDiscordInjections() {
    if runtime.GOOS != "windows" {
        return
    }

    localAppData := os.Getenv("LOCALAPPDATA")
    discordBase := filepath.Join(localAppData, "Discord")

    matches, _ := filepath.Glob(filepath.Join(discordBase, "app-*"))
    if len(matches) == 0 {
        return
    }

    corePath := filepath.Join(matches[0], "modules", "discord_desktop_core-1", "index.js")

    content, err := os.ReadFile(corePath)
    if err != nil {
        return
    }

    cleanContent := `module.exports = require('./core.asar');`

    if strings.TrimSpace(string(content)) != cleanContent {
        fmt.Println("\n[🚨 CRITICAL ALERT] Malicious code injection detected in Discord files!")
        fmt.Println("[*] File:", corePath)
        fmt.Println("[*] Automatically cleaning malicious script and restoring clean Discord core...")

        err := os.WriteFile(corePath, []byte(cleanContent), 0644)
        if err == nil {
            fmt.Println("[+] Successfully removed token grabber injection! Please restart Discord.")
        } else {
            fmt.Println("[!] Failed to clean file automatically. Please reinstall Discord immediately.")
        }
    }
}

func deriveKey(password string) []byte {
    hash := sha256.Sum256([]byte(password))
    return hash[:]
}

func encryptToken(token, password string) (string, string, error) {
    key := deriveKey(password)
    block, err := aes.NewCipher(key)
    if err != nil {
        return "", "", err
    }
    aesgcm, err := cipher.NewGCM(block)
    if err != nil {
        return "", "", err
    }
    nonce := make([]byte, aesgcm.NonceSize())
    if _, err := io.ReadFull(rand.Reader, nonce); err != nil {
        return "", "", err
    }
    encrypted := aesgcm.Seal(nil, nonce, []byte(token), nil)
    return hex.EncodeToString(encrypted), hex.EncodeToString(nonce), nil
}

func decryptToken(encToken, nonceHex, password string) (string, error) {
    key := deriveKey(password)
    block, err := aes.NewCipher(key)
    if err != nil {
        return "", err
    }
    aesgcm, err := cipher.NewGCM(block)
    if err != nil {
        return "", err
    }
    nonce, _ := hex.DecodeString(nonceHex)
    encrypted, _ := hex.DecodeString(encToken)
    decrypted, err := aesgcm.Open(nil, nonce, encrypted, nil)
    if err != nil {
        return "", err
    }
    return string(decrypted), nil
}

func clipboardProtector() {
    for {
        time.Sleep(2 * time.Second)
        out, err := exec.Command("powershell", "Get-Clipboard").Output()
        if err == nil {
            clipContent := strings.TrimSpace(string(out))
            if clipContent == rawToken && rawToken != "" {
                exec.Command("cmd", "/c", "echo off | clip").Run()
                fmt.Println("\n[🛡️] ANTI-LOGGER: Detected token in clipboard! Wiped it clean.")
            }
        }
    }
}

// --- MESSAGE MATCHING LOGIC ---
func isScamMessage(msg *discordgo.Message) bool {
    if textRegex != nil && msg.Content != "" {
        if textRegex.MatchString(msg.Content) {
            return true
        }
    }

    if len(msg.Attachments) > 0 {
        for _, att := range msg.Attachments {
            for _, threat := range threatDB.Images {
                if math.Abs(float64(att.Size)-float64(threat.Size)) > float64(threat.SizeTolerance) {
                    continue
                }

                resp, err := http.Get(att.URL)
                if err != nil || resp.StatusCode != 200 {
                    continue
                }

                imgData, err := io.ReadAll(resp.Body)
                resp.Body.Close()
                if err != nil {
                    continue
                }

                img, _, err := image.Decode(bytes.NewReader(imgData))
                if err != nil {
                    continue
                }

                msgHash, err := goimagehash.PerceptionHash(img)
                if err != nil {
                    continue
                }

                targetHash, err := goimagehash.ImageHashFromString(threat.Phash)
                if err != nil {
                    continue
                }

                distance, _ := msgHash.Distance(targetHash)
                if distance <= threat.HashTolerance {
                    return true
                }
            }
        }
    }

    return false
}

// --- LISTEN MODE ---
func listenHandler(s *discordgo.Session, m *discordgo.MessageCreate) {
    if m.Author.ID != s.State.User.ID {
        return
    }

    if isScamMessage(m.Message) {
        limiter.Wait(context.Background())
        s.ChannelMessageDelete(m.ChannelID, m.ID)
        fmt.Printf("\n[🚨] HIJACK DETECTED! Deleted malicious payload sent by hijacker.\n")

        alertMsg, _ := s.ChannelMessageSend(m.ChannelID, "🚨 HIJACK DETECTED: We have been compromised! Deleting malicious payload. 🚨")
        time.Sleep(5 * time.Second)
        s.ChannelMessageDelete(m.ChannelID, alertMsg.ID)
    }
}

// --- DELETE MODE ---
func startCleanup(s *discordgo.Session, myUserID string) {
    var channels []*discordgo.Channel

    body, err := s.Request("GET", "/users/@me/channels", "")
    if err == nil {
        var dms []*discordgo.Channel
        if json.Unmarshal(body, &dms) == nil {
            channels = append(channels, dms...)
        }
    }

    guilds, err := s.UserGuilds(100, "", "", false)
    if err == nil {
        for _, g := range guilds {
            guildChannels, err := s.GuildChannels(g.ID)
            if err != nil {
                continue
            }
            for _, c := range guildChannels {
                if c.Type == discordgo.ChannelTypeGuildText {
                    channels = append(channels, c)
                }
            }
        }
    }

    fmt.Printf("[*] Found %d total channels to process...\n", len(channels))

    ch := make(chan *discordgo.Channel, len(channels))
    var wg sync.WaitGroup

    for i := 0; i < WorkerCount; i++ {
        wg.Add(1)
        go worker(s, ch, &wg, myUserID)
    }

    for _, c := range channels {
        ch <- c
    }
    close(ch)

    wg.Wait()
    fmt.Println("\n[+] Cleanup process finished! You can close the program.")
}

func worker(s *discordgo.Session, ch <-chan *discordgo.Channel, wg *sync.WaitGroup, myUserID string) {
    defer wg.Done()
    for channel := range ch {
        processChannel(s, channel, myUserID)
    }
}

func processChannel(s *discordgo.Session, c *discordgo.Channel, myUserID string) {
    channelName := c.Name
    if c.Name == "" && len(c.Recipients) > 0 {
        channelName = "DM with " + c.Recipients[0].Username
    } else if c.Name == "" {
        channelName = "Group DM"
    } else {
        channelName = "#" + c.Name
    }

    beforeID := ""
    for {
        limiter.Wait(context.Background())

        msgs, err := s.ChannelMessages(c.ID, MessageLimit, beforeID, "", "")
        if err != nil {
            if strings.Contains(err.Error(), "1015") {
                fmt.Printf("  [!] Cloudflare ban hit. Pausing for 60 seconds...\n")
                time.Sleep(60 * time.Second)
                continue
            }
            return
        }
        if len(msgs) == 0 {
            return
        }

        for _, msg := range msgs {
            beforeID = msg.ID
            if msg.Author.ID != myUserID {
                continue
            }

            if isScamMessage(msg) {
                limiter.Wait(context.Background())
                s.ChannelMessageDelete(c.ID, msg.ID)
                fmt.Printf("  [+] Deleted scam message in %s\n", channelName)
            }
        }

        if len(msgs) < MessageLimit {
            break
        }
    }
}