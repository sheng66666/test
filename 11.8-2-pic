import customtkinter as ctk
import threading
import json
import time
import os
import sys
import ctypes
import hashlib
import io
import pyautogui
import cv2
import numpy as np
from PIL import ImageGrab, ImageDraw
from pywinauto import Application
import pygame
import win32gui
from difflib import SequenceMatcher
from datetime import datetime, timedelta
import tkinter as tk
from tkinter import filedialog
import pygetwindow as gw
import win32con
import uuid
import traceback
import functools
from collections import deque

# ===== 簡化配色方案 =====
COLORS = {
    'success': '#28a745',
    'danger': '#dc3545',
    'warning': '#ffc107',
    'info': '#6c757d',
    'primary': '#007bff',
    'card_bg': '#2D2D30',
    'dark_bg': '#1A1A1A',
    'border': '#B8860B',
    'text_primary': '#F7FAFC',
    'text_secondary': '#A0AEC0',
    'primary_hover': '#0056b3',
    'success_hover': '#1e7e34',
    'danger_hover': '#bd2130',
    'info_hover': '#495057',
    'warning_hover': '#d39e00',
    'accent': '#DAA520',
    'accent_hover': '#B8860B',
    'secondary': '#4A5568',
    'secondary_hover': '#2D3748'
}

# ===== 常數設定 =====
BTN_WIDTH = 260
BTN_HEIGHT = 30
BTN_CORNER_RADIUS = 15
FONT_FAMILY = "新細明體"

pygame.mixer.init()

def cv_imread(file_path, flags=cv2.IMREAD_COLOR):
    """支援中文路徑的圖片讀取"""
    return cv2.imdecode(np.fromfile(file_path, dtype=np.uint8), flags)

def resource_path(relative_path):
    if hasattr(sys, "_MEIPASS"):
        return os.path.join(sys._MEIPASS, relative_path)
    return os.path.join(os.path.abspath("."), relative_path)

try:
    sound_path = resource_path("event_sound.wav")
    if not os.path.exists(sound_path):
        print(f"音效檔不存在：{sound_path}")
    event_sound = pygame.mixer.Sound(sound_path)
except Exception as e:
    print(f"載入音效失敗：{e}")
    event_sound = None

# ===== 全域變數 =====
event_templates = {}

#  1.定義遊戲路徑預設值
DEFAULT_GAME_EXE_PATH = r"C:\Users\jinyong\Downloads\JYOnline_TW\maina\loginp.exe"
DEFAULT_GAME_EXE_PARAMS = "123"

# 2. 設定檔路徑
BASE_DIR = os.path.dirname(sys.executable) if getattr(sys, 'frozen', False) else os.path.dirname(__file__)
SETTINGS_FILE = os.path.join(BASE_DIR, "game_settings.json")



ACCOUNTS_CONFIG = os.path.join(BASE_DIR, "accounts.json")
LOGIN_WINDOW_TITLE_REGEX = "JYOnline"
SERVER_CONFIRM_COORDS = (322, 548)
BASE_WIN_WIDTH = 800
BASE_WIN_HEIGHT = 600
BASE_SCAN_REGION = (328, 110, 282, 24)
CHAT_BAR_TEMPLATE = "chat_bar.png"
BASE_CHAT_BAR_REGION = (263, 577, 285, 19)
DEFAULT_GAME_X = 4
DEFAULT_GAME_Y = 23
DEFAULT_GAME_W = 800
DEFAULT_GAME_H = 600

# 應用狀態變數
stop_auto_scroll_login_log = False
stop_auto_scroll_scan_log = False
login_stopped = False
recognize_announcement = True
scan_running = False
rotation_running = False
restart_enabled = False
schedule_enabled = True

# 計時與間隔設定
rotation_interval = 15
restart_minutes = 20
login_delay_seconds = 5

# 執行狀態與計數器
rotation_thread_id = None
rotation_thread = None
last_scan_image_hash = None
rotation_countdown = 0
restart_countdown = restart_minutes * 60

# 集合與列表
accounts = []
vars_checkbox = []
windows_handles = []

# 事件與鎖
rotation_paused = threading.Event()
rotation_paused.set()
event_processing = threading.Event()
event_processing.clear()
rotation_countdown_lock = threading.Lock()
restart_countdown_lock = threading.Lock()
restart_thread_stop_event = threading.Event()
login_lock = threading.Lock()

# 座標與事件對應
option_coordinates = {
    1: (420, 307),
    2: (420, 325),
    3: (420, 344),
    4: (420, 362),
}

event_dialogs = {
    "走路突然踢到一個空酒瓶": ("獨孤九劍奧義", 1),
    "有人騎著一匹雪白的駿馬跑過": ("真．辟邪劍法", 1),
    "蘆葦叢中有一根蘆葦怎麼看就是不對勁": ("西毒杖法", 1),
    "有位大鬍子的路人以不友善的眼神瞟你": ("野球拳", 3),
    "路邊有個怪異小土堆": ("六脈神劍", 3),
    "有影子掠過": ("金剛伏魔鞭法", 1),
    "水邊有個大木箱浮浮沉沉": ("黯然銷魂掌", 1),
    "遠方的石頭上有個閃閃發亮的東西": ("金蛇劍法", 1),
    "似乎有東西淩空朝你射來": ("降龍十八掌", 3),
    "路旁有根破損的鐵杖": ("打狗棒法", 4),
    "有只被泥沙覆蓋的破鞋": ("胡家刀法", 1),
}

schedule_times = {
    "0": {"enabled": True, "time": "10:15"},
    "1": {"enabled": True, "time": "10:15"},
    "2": {"enabled": True, "time": "10:15"},
    "3": {"enabled": True, "time": "10:15"},
    "4": {"enabled": True, "time": "10:15"},
    "5": {"enabled": True, "time": "08:15"},
    "6": {"enabled": True, "time": "08:15"},
}

# ===== 工具函式 =====

# 3. 定義遊戲路徑設定檔的讀寫函式
def load_game_settings():
    if os.path.exists(SETTINGS_FILE):
        try:
            with open(SETTINGS_FILE, "r", encoding="utf-8") as f:
                return json.load(f)
        except Exception:
            pass
    return {
        "game_exe_path": DEFAULT_GAME_EXE_PATH,
        "game_exe_params": DEFAULT_GAME_EXE_PARAMS
    }

def save_game_settings_to_file(path, params):
    with open(SETTINGS_FILE, "w", encoding="utf-8") as f:
        json.dump({"game_exe_path": path, "game_exe_params": params}, f, ensure_ascii=False, indent=2)

# 4. 這時候才可以呼叫 load_game_settings
game_settings = load_game_settings()
GAME_EXE_PATH = game_settings["game_exe_path"]
GAME_EXE_PARAMS = game_settings["game_exe_params"]

def get_game_client_area_rect():
    """回傳遊戲客戶端區域座標"""
    windows = gw.getWindowsWithTitle(LOGIN_WINDOW_TITLE_REGEX)
    if not windows:
        return (DEFAULT_GAME_X, DEFAULT_GAME_Y, DEFAULT_GAME_W, DEFAULT_GAME_H)
    win = windows[0]
    hwnd = win._hWnd
    left, top, right, bottom = win32gui.GetClientRect(hwnd)
    client_x, client_y = win32gui.ClientToScreen(hwnd, (left, top))
    client_x2, client_y2 = win32gui.ClientToScreen(hwnd, (right, bottom))
    client_w = client_x2 - client_x
    client_h = client_y2 - client_y
    return (client_x, client_y, client_w, client_h)

def get_dynamic_chat_bar_region():
    client_rect = get_game_client_area_rect()
    if not client_rect:
        return BASE_CHAT_BAR_REGION
    client_x, client_y, client_w, client_h = client_rect
    rel_x, rel_y, rel_w, rel_h = BASE_CHAT_BAR_REGION
    scale_x = client_w / BASE_WIN_WIDTH
    scale_y = client_h / BASE_WIN_HEIGHT
    abs_x = int(client_x + rel_x * scale_x)
    abs_y = int(client_y + rel_y * scale_y)
    abs_w = int(rel_w * scale_x)
    abs_h = int(rel_h * scale_y)
    return (abs_x, abs_y, abs_w, abs_h)

def get_dynamic_scan_region():
    client_rect = get_game_client_area_rect()
    if not client_rect:
        return BASE_SCAN_REGION
    client_x, client_y, client_w, client_h = client_rect
    rel_x, rel_y, rel_w, rel_h = BASE_SCAN_REGION
    scale_x = client_w / BASE_WIN_WIDTH
    scale_y = client_h / BASE_WIN_HEIGHT
    abs_x = int(client_x + rel_x * scale_x)
    abs_y = int(client_y + rel_y * scale_y)
    abs_w = int(rel_w * scale_x)
    abs_h = int(rel_h * scale_y)
    return (abs_x, abs_y, abs_w, abs_h)

def get_dynamic_coordinate(rel_x, rel_y):
    client_rect = get_game_client_area_rect()
    if not client_rect:
        return rel_x, rel_y
    client_x, client_y, client_w, client_h = client_rect
    scale_x = client_w / BASE_WIN_WIDTH
    scale_y = client_h / BASE_WIN_HEIGHT
    abs_x = int(client_x + rel_x * scale_x)
    abs_y = int(client_y + rel_y * scale_y)
    return abs_x, abs_y

def bring_foreground(hwnd):
    SW_SHOW = 5
    ctypes.windll.user32.ShowWindow(hwnd, SW_SHOW)
    ctypes.windll.user32.SetForegroundWindow(hwnd)

def key_press(vk_code):
    KEYEVENTF_KEYUP = 0x0002
    ctypes.windll.user32.keybd_event(vk_code, 0, 0, 0)
    ctypes.windll.user32.keybd_event(vk_code, 0, KEYEVENTF_KEYUP, 0)
# ===== 圖片快取與掃描功能 =====
import functools
from collections import deque

class ImageCache:
    """圖片處理快取管理器"""
    def __init__(self, max_size=10):
        self.cache = {}
        self.max_size = max_size
        self.access_order = deque()
    
    def get_image_hash(self, region):
        """快取式圖片雜湊計算"""
        region_key = tuple(region)
        current_time = time.time()
        
        # 檢查快取是否存在且未過期（2秒內）
        if region_key in self.cache:
            cached_hash, timestamp = self.cache[region_key]
            if current_time - timestamp < 2.0:
                return cached_hash
        
        # 重新計算雜湊
        try:
            x, y, w, h = region
            img = ImageGrab.grab(bbox=(x, y, x + w, y + h))
            buf = io.BytesIO()
            img.save(buf, format="PNG")
            img_bytes = buf.getvalue()
            img_hash = hashlib.md5(img_bytes).hexdigest()
            
            # 更新快取
            self.cache[region_key] = (img_hash, current_time)
            self.access_order.append(region_key)
            
            # 限制快取大小
            if len(self.cache) > self.max_size:
                oldest = self.access_order.popleft()
                self.cache.pop(oldest, None)
            
            return img_hash
            
        except Exception:
            return None

# 建立圖片快取管理器
image_cache = ImageCache()

@functools.lru_cache(maxsize=16)
def cached_get_dynamic_scan_region():
    """快取掃描區域座標"""
    return get_dynamic_scan_region()

def load_event_templates():
    global event_templates
    event_templates.clear()
    for dlg in event_dialogs:
        tpl_path = resource_path(os.path.join("event_templates", f"{dlg}.png"))
        if os.path.exists(tpl_path):
            template = cv_imread(tpl_path, cv2.IMREAD_GRAYSCALE)
            if template is not None:
                event_templates[dlg] = template

def match_event_template(img, threshold=0.8):
    """模板比對功能"""
    img_gray = cv2.cvtColor(np.array(img), cv2.COLOR_RGB2GRAY)
    for dlg, template in event_templates.items():
        if template.shape[0] > img_gray.shape[0] or template.shape[1] > img_gray.shape[1]:
            continue
        res = cv2.matchTemplate(img_gray, template, cv2.TM_CCOEFF_NORMED)
        _, max_val, _, _ = cv2.minMaxLoc(res)
        if max_val >= threshold:
            return dlg, max_val
    return None, None

def is_chat_bar_visible(threshold=0.8):
    tpl = resource_path(CHAT_BAR_TEMPLATE)
    if not os.path.exists(tpl):
        write_login_log(f"❌ {CHAT_BAR_TEMPLATE} 不存在，跳過驗證")
        return False
    template = cv_imread(tpl, cv2.IMREAD_GRAYSCALE)
    if template is None:
        write_login_log(f"❌ 模板圖片 {tpl} 讀取失敗")
        return False
    x, y, w, h = get_dynamic_chat_bar_region()
    img = pyautogui.screenshot(region=(x, y, w, h))
    gray = cv2.cvtColor(np.array(img), cv2.COLOR_RGB2GRAY)
    res = cv2.matchTemplate(gray, template, cv2.TM_CCOEFF_NORMED)
    _, max_val, _, _ = cv2.minMaxLoc(res)
    write_login_log(f"聊天欄相似度: {max_val:.2f}")
    return max_val >= threshold

def detect_announcement():
    if not recognize_announcement:
        return False
    tpl = resource_path("close.png")
    if not os.path.exists(tpl):
        write_login_log("close.png 不存在，跳過公告偵測")
        return False
    template = cv_imread(tpl, cv2.IMREAD_GRAYSCALE)
    if template is None:
        write_login_log(f"❌ 模板圖片 {tpl} 讀取失敗")
        return False
    screenshot = pyautogui.screenshot()
    gray = cv2.cvtColor(np.array(screenshot), cv2.COLOR_BGR2GRAY)
    res = cv2.matchTemplate(gray, template, cv2.TM_CCOEFF_NORMED)
    _, max_val, _, _ = cv2.minMaxLoc(res)
    write_login_log(f"公告相似度: {max_val:.2f}")
    return max_val >= 0.8

def close_announcement():
    x_rel, y_rel, w, h = 656, 50, 39, 28
    cx, cy = get_dynamic_coordinate(x_rel + w // 2, y_rel + h // 2)
    time.sleep(0.5)
    pyautogui.moveTo(cx, cy, duration=0.1)
    pyautogui.click()
    dbg = ImageGrab.grab()
    draw = ImageDraw.Draw(dbg)
    r = 10
    draw.ellipse((cx - r, cy - r, cx + r, cy + r), outline="red", width=3)
    os.makedirs("screenshots", exist_ok=True)
    fn = f"screenshots/debug_close_{time.strftime('%H%M%S')}.png"
    dbg.save(fn)
    write_login_log(f"已關閉公告，點擊座標：({cx},{cy})，檔案：{fn}")

def login_account_and_get_hwnd(account):
    cmd = f'"{GAME_EXE_PATH}" {GAME_EXE_PARAMS}'
    appwin = Application(backend="win32").start(cmd)
    win = appwin.window(title_re=LOGIN_WINDOW_TITLE_REGEX)
    win.wait("visible", timeout=10)
    bring_foreground(win.handle)
    win.set_focus()
    time.sleep(0.1)
    key_press(0x11)
    time.sleep(0.1)
    rect = win.rectangle()
    screen_x = rect.left + SERVER_CONFIRM_COORDS[0]
    screen_y = rect.top + SERVER_CONFIRM_COORDS[1]
    ctypes.windll.user32.SetCursorPos(screen_x, screen_y)
    time.sleep(0.1)
    ctypes.windll.user32.mouse_event(0x0002, 0, 0, 0, 0)
    ctypes.windll.user32.mouse_event(0x0004, 0, 0, 0, 0)
    time.sleep(0.1)
    key_press(0x0D)
    time.sleep(0.1)
    bring_foreground(win.handle)
    win.set_focus()
    time.sleep(0.1)
    win.type_keys(account["username"], with_spaces=True, pause=0.01)
    time.sleep(0.1)
    key_press(0x09)
    time.sleep(0.1)
    win.type_keys(account["password"], with_spaces=True, pause=0.01)
    time.sleep(0.1)
    key_press(0x0D)
    write_login_log(f"{account['username']} 登入中")
    return win.handle

def is_window_valid(hwnd):
    try:
        return win32gui.IsWindow(hwnd) and win32gui.IsWindowVisible(hwnd)
    except Exception:
        return False

def clean_invalid_handles():
    global windows_handles
    windows_handles = [hwnd for hwnd in windows_handles if is_window_valid(hwnd)]

def close_window(hwnd):
    try:
        win32gui.PostMessage(hwnd, 0x0010, 0, 0)
        write_login_log(f"已關閉視窗 hwnd={hwnd}")
    except Exception as e:
        write_login_log(f"關閉視窗失敗 hwnd={hwnd}: {e}")

def write_login_log(message):
    """優化後的登入日誌寫入"""
    try:
        app.login_log_textbox.configure(state="normal")
        app.login_log_textbox.insert("end", message + "\n")
        
        # 限制日誌行數為100行
        lines_count = int(app.login_log_textbox.index('end-1c').split('.')[0])
        if lines_count > 100:
            delete_lines = lines_count - 100
            app.login_log_textbox.delete("1.0", f"{delete_lines + 1}.0")
        
        app.login_log_textbox.configure(state="disabled")
        if not stop_auto_scroll_login_log:
            app.login_log_textbox.see("end")
    except Exception:
        pass

def write_scan_log(message):
    """優化後的掃描日誌寫入"""
    try:
        app.scan_log_textbox.configure(state="normal")
        app.scan_log_textbox.insert("end", message + "\n")
        
        # 限制日誌行數為100行
        lines_count = int(app.scan_log_textbox.index('end-1c').split('.')[0])
        if lines_count > 100:
            delete_lines = lines_count - 100
            app.scan_log_textbox.delete("1.0", f"{delete_lines + 1}.0")
        
        app.scan_log_textbox.configure(state="disabled")
        if not stop_auto_scroll_scan_log:
            app.scan_log_textbox.see("end")
    except Exception:
        pass

def scan_loop():
    """優化後的掃描循環"""
    global scan_running, last_scan_image_hash
    write_scan_log("開始掛機掃描")
    
    consecutive_no_change = 0
    adaptive_delay = 1.0  # 自適應延遲
    
    while scan_running:
        # 使用快取的掃描區域
        region = cached_get_dynamic_scan_region()
        
        # 使用快取的圖片雜湊
        img_hash = image_cache.get_image_hash(region)
        if img_hash is None:
            time.sleep(adaptive_delay)
            continue
        
        # 檢查圖片是否有變化
        if img_hash == last_scan_image_hash:
            consecutive_no_change += 1
            # 自適應延遲：連續無變化時增加延遲
            if consecutive_no_change > 5:
                adaptive_delay = min(3.0, adaptive_delay * 1.2)
            time.sleep(adaptive_delay)
            continue
        else:
            consecutive_no_change = 0
            adaptive_delay = 1.0  # 重置延遲
            last_scan_image_hash = img_hash

        # 重新截圖進行模板比對
        try:
            x, y, w, h = region
            img = ImageGrab.grab(bbox=(x, y, x + w, y + h))
        except Exception as e:
            write_scan_log(f"截圖異常: {e}")
            time.sleep(adaptive_delay)
            continue

        # 事件模板比對
        try:
            dlg, score = match_event_template(img, threshold=0.8)
        except Exception as e:
            write_scan_log(f"模板比對發生錯誤: {e}")
            time.sleep(adaptive_delay)
            continue

        if dlg:
            write_scan_log(f"模板比對事件：{dlg} 相似度={score:.2f}")
            evt, opt = event_dialogs[dlg]
            cx_rel, cy_rel = option_coordinates[opt]
            try:
                cx, cy = get_dynamic_coordinate(cx_rel, cy_rel)
            except Exception as e:
                write_scan_log(f"計算動態座標失敗: {e}")
                continue
            if event_sound:
                try:
                    event_sound.play()
                except Exception as e:
                    write_scan_log(f"播放音效失敗: {e}")
            try:
                handle_event_trigger(evt, opt, cx, cy)
            except Exception as e:
                write_scan_log(f"處理事件觸發失敗: {e}")
        else:
            write_scan_log("無事件符合")
        
        time.sleep(adaptive_delay)
    
    write_scan_log("掃描已停止")

def screenshot_with_circle(cx, cy, radius=16, color='#FFD600', width=3):
    img = ImageGrab.grab()
    draw = ImageDraw.Draw(img)
    draw.ellipse((cx - radius, cy - radius, cx + radius, cy + radius), outline=color, width=width)
    return img

def handle_event_trigger(evt, opt, cx, cy):
    event_processing.set()
    try:
        timestamp = time.strftime('%Y%m%d_%H%M%S')
        os.makedirs('screenshots', exist_ok=True)
        fn1 = f"screenshots/{evt}_{timestamp}.png"
        img1 = ImageGrab.grab()
        img1.save(fn1)
        write_scan_log(f"已截圖(事件前): {fn1}")
        pyautogui.moveTo(cx, cy, duration=1.2)
        fn2 = f"screenshots/{evt}_{timestamp}_選項{opt}.png"
        img2 = ImageGrab.grab()
        img2.save(fn2)
        write_scan_log(f"已截圖(滑鼠移動後): {fn2}")
        total_effect_time = 3.0
        click_time = 1.5
        radius = 16
        color = '#FFD600'
        width = 3
        start_time = time.time()
        has_clicked = False
        while True:
            elapsed = time.time() - start_time
            if not has_clicked and elapsed >= click_time:
                fn3 = f"screenshots/{evt}_{timestamp}_點擊完成.png"
                img3 = screenshot_with_circle(cx, cy, radius, color, width)
                img3.save(fn3)
                write_scan_log(f"已截圖(點擊完成): {fn3}")
                pyautogui.moveTo(cx, cy, duration=0.1)
                for _ in range(5):
                    pyautogui.click()
                    time.sleep(0.05)
                has_clicked = True
            if elapsed >= total_effect_time:
                break
            time.sleep(0.05)
    finally:
        time.sleep(1.5)
        event_processing.clear()
# ===== 登入與視窗管理功能 =====
def login_all_accounts():
    if login_lock.locked():
        write_login_log("登入流程已在執行中，請勿重複啟動")
        return
    clean_invalid_handles()
    rotation_paused.clear()

    with login_lock:
        global windows_handles, login_stopped, restart_countdown
        login_stopped = False
        selected_accounts = [accounts[i] for i in range(len(accounts)) if i < len(vars_checkbox) and vars_checkbox[i].get()]
        
        for account in selected_accounts:
            retry = 0
            success = False
            hwnd = None
            while retry < 5 and not success and not login_stopped:
                try:
                    if hwnd:
                        close_window(hwnd)
                    hwnd = login_account_and_get_hwnd(account)
                    
                    for _ in range(login_delay_seconds):
                        if login_stopped:
                            break
                        time.sleep(1)
                    if login_stopped:
                        break
                        
                    if is_chat_bar_visible():
                        write_login_log(f"{account['username']} 登入成功")
                        if recognize_announcement and detect_announcement():
                            write_login_log("偵測到公告，準備關閉")
                            close_announcement()
                        else:
                            write_login_log("無公告，不需關閉")
                        if hwnd not in windows_handles:
                            windows_handles.append(hwnd)
                        success = True
                    else:
                        write_login_log(f"{account['username']} 登入失敗，重試第{retry + 1}次")
                        close_window(hwnd)
                        retry += 1
                        for _ in range(1):
                            if login_stopped:
                                break
                            time.sleep(1)
                except Exception as e:
                    write_login_log(f"{account['username']} 登入異常: {e}")
                    if hwnd:
                        close_window(hwnd)
                    retry += 1
                    for _ in range(1):
                        if login_stopped:
                            break
                        time.sleep(1)
            if login_stopped:
                write_login_log("已停止自動登入流程")
                break

    if windows_handles and not login_stopped:
        start_window_rotation(windows_handles)
        write_login_log("所有帳號登入流程結束，開始輪流前移視窗！")
    
    with restart_countdown_lock:
        restart_countdown = restart_minutes * 60
    rotation_paused.set()

# ===== 掃描紅框顯示 =====
scan_box_window = None
scan_box_canvas = None
scan_box_running = False
stop_event = threading.Event()

def start_show_scan_region_box():
    global scan_box_running, stop_event, scan_box_window, scan_box_canvas
    if scan_box_running:
        return
    scan_box_running = True
    stop_event.clear()
    
    def loop():
        global scan_box_window, scan_box_canvas, scan_box_running
        last_region = None
        while not stop_event.is_set():
            region = get_dynamic_scan_region()
            if region != last_region:
                x, y, w, h = region
                if scan_box_window is None or not scan_box_window.winfo_exists():
                    scan_box_window = ctk.CTkToplevel(app)
                    scan_box_window.overrideredirect(True)
                    scan_box_window.attributes("-topmost", True)
                    scan_box_window.attributes("-alpha", 1.0)
                    scan_box_window.attributes("-transparentcolor", "white")
                    scan_box_window.geometry(f"{w}x{h}+{x}+{y}")
                    scan_box_canvas = ctk.CTkCanvas(scan_box_window, width=w, height=h, bg='white', highlightthickness=0)
                    scan_box_canvas.pack(fill="both", expand=True)
                else:
                    scan_box_window.geometry(f"{w}x{h}+{x}+{y}")
                    scan_box_canvas.config(width=w, height=h)
                scan_box_canvas.delete("all")
                scan_box_canvas.create_rectangle(2, 2, w-2, h-2, outline="red", width=3)
                last_region = region
            if scan_box_window and scan_box_window.winfo_exists():
                scan_box_window.update()
            time.sleep(0.2)
        if scan_box_window is not None and scan_box_window.winfo_exists():
            scan_box_window.destroy()
            scan_box_window = None
            scan_box_canvas = None
        scan_box_running = False
    
    threading.Thread(target=loop, daemon=True).start()

def stop_show_scan_region_box():
    global scan_box_running, stop_event
    stop_event.set()

# ===== 輪巡功能 =====
def start_window_rotation(windows):
    global rotation_running, rotation_thread_id, rotation_thread, windows_handles
    stop_window_rotation()
    this_id = uuid.uuid4()
    rotation_thread_id = this_id

    def rotation_task():
        global rotation_running, rotation_countdown, windows_handles, rotation_thread_id
        idx = 0
        rotation_running = True
        with rotation_countdown_lock:
            rotation_countdown = rotation_interval

        while rotation_running and windows_handles and rotation_thread_id == this_id:
            clean_invalid_handles()
            if not windows_handles:
                break
            if idx >= len(windows_handles):
                idx = 0
            hwnd = windows_handles[idx]

            if event_processing.is_set():
                time.sleep(0.1)
                if not rotation_running or rotation_thread_id != this_id:
                    break
                continue

            rotation_paused.wait()
            if not rotation_running or rotation_thread_id != this_id:
                break

            try:
                bring_foreground(hwnd)
                write_scan_log(f"切換到第{idx + 1}個帳號視窗")
            except Exception as e:
                write_scan_log(f"輪換視窗失敗: {e}")

            idx = (idx + 1) % len(windows_handles)

            with rotation_countdown_lock:
                rotation_countdown = rotation_interval

            while True:
                with rotation_countdown_lock:
                    if (rotation_countdown <= 0 or
                        not rotation_running or
                        event_processing.is_set() or
                        rotation_thread_id != this_id):
                        break
                    current_rotation = rotation_countdown

                try:
                    app.after(0, app.set_rotation_timer_label, current_rotation)
                except Exception:
                    pass

                for _ in range(10):
                    if not rotation_running or rotation_thread_id != this_id:
                        break
                    time.sleep(0.1)
                with rotation_countdown_lock:
                    rotation_countdown -= 1

        try:
            app.after(0, app.set_rotation_timer_label, 0)
        except Exception:
            pass

    t = threading.Thread(target=rotation_task, daemon=True)
    rotation_thread = t
    t.start()

def stop_window_rotation():
    global rotation_running
    rotation_running = False
    rotation_paused.set()

# ===== 計時器線程 =====
def restart_timer_thread():
    global restart_minutes, restart_countdown, restart_enabled
    while not restart_thread_stop_event.is_set():
        time.sleep(1)
        with restart_countdown_lock:
            if not restart_enabled or not windows_handles:
                restart_countdown = restart_minutes * 60
                current_count = restart_countdown
            else:
                if restart_countdown <= 0:
                    write_login_log(f"自動重啟：{restart_minutes}分鐘到，關閉遊戲並重新登入")
                    current_handles = windows_handles.copy()
                    for hwnd in current_handles:
                        close_window(hwnd)
                    time.sleep(5)
                    if not login_lock.locked():
                        threading.Thread(target=login_all_accounts, daemon=True).start()
                    restart_countdown = restart_minutes * 60
                    current_count = restart_countdown
                else:
                    restart_countdown -= 1
                    current_count = restart_countdown
        try:
            app.after(0, app.set_restart_timer_label, current_count)
        except Exception:
            pass

def schedule_timer_thread():
    while True:
        time.sleep(1)
        min_delta = None
        now = datetime.now()
        if schedule_enabled and windows_handles:
            for idx in range(7):
                conf = schedule_times[str(idx)]
                if not conf["enabled"]:
                    continue
                tstr = conf["time"]
                if not tstr:
                    continue
                try:
                    hh, mm = [int(x) for x in tstr.split(":")]
                    target = now.replace(hour=hh, minute=mm, second=0, microsecond=0)
                    dow = now.weekday()
                    day_gap = (idx - dow) % 7
                    if day_gap == 0 and now >= target:
                        target += timedelta(days=7)
                    else:
                        target += timedelta(days=day_gap)
                    delta = (target - now).total_seconds()
                    if (min_delta is None or delta < min_delta) and delta > 0:
                        min_delta = delta
                except:
                    continue
            if min_delta is not None:
                current_delta = int(min_delta)
                try:
                    app.after(0, app.set_schedule_timer_label, current_delta)
                except:
                    pass
                if current_delta <= 0:
                    write_login_log(f"排程時間到，關閉遊戲並重新登入")
                    for hwnd in windows_handles:
                        close_window(hwnd)
                    time.sleep(5)
                    login_all_accounts()
                    time.sleep(60)
            else:
                try:
                    app.after(0, app.set_schedule_timer_label, 0)
                except:
                    pass
        else:
            try:
                app.after(0, app.set_schedule_timer_label, 0)
            except:
                pass

# ===== 格式化倒數時間 =====
def format_countdown(seconds):
    seconds = int(max(seconds, 0))
    days = seconds // 86400
    hours = (seconds % 86400) // 3600
    minutes = (seconds % 3600) // 60
    sec = seconds % 60
    return f"{days}天{hours:02d}:{minutes:02d}:{sec:02d}"

# ===== 帳號資料儲存/載入 =====
def save_accounts(filepath=ACCOUNTS_CONFIG):
    for idx, acc in enumerate(accounts):
        if idx < len(vars_checkbox):
            acc["enabled"] = vars_checkbox[idx].get()
    try:
        with open(filepath, "w", encoding="utf-8") as f:
            json.dump(accounts, f, ensure_ascii=False, indent=2)
        write_login_log(f"帳號已儲存")
    except Exception as e:
        write_login_log(f"儲存帳號失敗: {e}")

def load_accounts(filepath=ACCOUNTS_CONFIG):
    global accounts
    if os.path.exists(filepath):
        try:
            with open(filepath, "r", encoding="utf-8") as f:
                accounts[:] = json.load(f)
        except Exception as e:
            accounts[:] = []
            write_login_log(f"載入帳號失敗: {e}")
    else:
        accounts[:] = []
    if hasattr(app, "refresh_account_list"):
        app.refresh_account_list()
# ===== 主程式 GUI 類別 =====
class AccountManagerApp(ctk.CTk):
    def __init__(self):
        super().__init__()
        self.title("金庸自動掛機助手")
        self.geometry("720x800")
        self.minsize(720, 800)
        self.resizable(False, False)
        self.protocol("WM_DELETE_WINDOW", self.on_close)
        
        # 設定字體
        self.default_font = ctk.CTkFont(family="新細明體", size=12)
        self.bold_font = ctk.CTkFont(family="新細明體", size=12, weight="bold")
        self.title_font = ctk.CTkFont(family="新細明體", size=14, weight="bold")
        self.time_font = ctk.CTkFont(family="新細明體", size=16, weight="bold")
        
        # 主視窗分上下兩大區塊 - 固定左側，右側對齊監控
        self.grid_columnconfigure(0, weight=0, minsize=350)  # 左側固定寬度，確保不被壓縮
        self.grid_columnconfigure(1, weight=1, minsize=350)  # 右側自適應，與右下監控對齊
        self.grid_rowconfigure(0, weight=3, minsize=400)
        self.grid_rowconfigure(1, weight=2, minsize=250)

        # 左側帳號管理區塊
        self.left_frame = ctk.CTkFrame(self, fg_color="transparent")
        self.left_frame.grid(row=0, column=0, sticky="nsew", padx=(10, 2), pady=10)
        self.left_frame.grid_columnconfigure(0, weight=1)
        self.left_frame.grid_rowconfigure(0, weight=0, minsize=100)  # 輸入區域最小高度
        self.left_frame.grid_rowconfigure(1, weight=1, minsize=250)  # 帳號清單最小高度 (稍微減少)
        self.left_frame.grid_rowconfigure(2, weight=0, minsize=40)   # 時間標籤區域

        # 帳號輸入區塊
        self.input_frame = ctk.CTkFrame(self.left_frame, corner_radius=15, 
                                       fg_color=COLORS['card_bg'], border_width=1, border_color=COLORS['border'])
        self.input_frame.grid(row=0, column=0, sticky="ew", pady=(0, 8))
        self.input_frame.grid_columnconfigure((0, 1, 2), weight=1)
        
        # 帳號管理標題
        ctk.CTkLabel(self.input_frame, text="帳號管理", 
                    font=self.title_font, text_color=COLORS['primary']).grid(
            row=0, column=0, columnspan=3, padx=8, pady=(8, 4), sticky="w")
        
        self.account_entry = ctk.CTkEntry(self.input_frame, placeholder_text="帳號", 
                                         width=100, corner_radius=15, font=self.default_font)
        self.account_entry.grid(row=1, column=0, padx=6, pady=8, sticky="ew")
        
        self.password_entry = ctk.CTkEntry(self.input_frame, placeholder_text="密碼", 
                                          width=100, corner_radius=15, show="*", font=self.default_font)
        self.password_entry.grid(row=1, column=1, padx=6, pady=8, sticky="ew")
        
        self.add_btn = ctk.CTkButton(self.input_frame, text="新增", width=60, corner_radius=15, 
                                    command=self.add_account, fg_color=COLORS['success'], 
                                    hover_color=COLORS['success'], font=self.default_font)
        self.add_btn.grid(row=1, column=2, padx=6, pady=8, sticky="ew")

        # Tab切換與Enter/空白鍵綁定 - 簡化版
        self.account_entry.bind("<Tab>", lambda e: self.password_entry.focus())
        self.account_entry.bind("<Return>", lambda e: self.password_entry.focus())
        self.password_entry.bind("<Tab>", lambda e: self.add_btn.focus())
        self.password_entry.bind("<Return>", lambda e: self.add_account())
        self.add_btn.bind("<Return>", lambda e: self.add_account())
        self.add_btn.bind("<space>", lambda e: self.add_account())

        # 帳號清單 - 修正布局，讓帳號從上方開始顯示
        self.account_list_frame = ctk.CTkScrollableFrame(self.left_frame, height=300, 
                                                        fg_color=COLORS['dark_bg'])
        self.account_list_frame.grid(row=1, column=0, sticky="new", padx=0, pady=0)
        # 目前時間顯示 - 放在左側帳號區塊下方
        self.current_time_label = ctk.CTkLabel(self.left_frame, text="目前時間：", 
                                              font=self.time_font, text_color=COLORS['primary'])
        self.current_time_label.grid(row=2, column=0, sticky="ew", padx=8, pady=(8, 0))
        self.update_current_time()
        
        
        
                # 右側功能控制區塊 - 可滾動
        self.right_frame = ctk.CTkScrollableFrame(
            self, 
            fg_color="transparent", 
            height=400,
            scrollbar_fg_color=COLORS['card_bg'],        # 使用卡片背景色
            scrollbar_button_color=COLORS['card_bg']      # 使用卡片背景色
        )
        self.right_frame.grid(row=0, column=1, sticky="nsew", padx=(3, 10), pady=10)
        self.right_frame.grid_columnconfigure(0, weight=1)
        
        # 將滾動條設為極小寬度
        try:
            self.right_frame._scrollbar.configure(width=3)  # 極小寬度
        except:
            pass


        
        # 主要操作容器
        self.main_control_container = ctk.CTkFrame(self.right_frame, corner_radius=15, 
                                                  fg_color=COLORS['card_bg'], border_width=1, border_color=COLORS['border'])
        self.main_control_container.grid(row=0, column=0, sticky="ew", pady=(0, 8))
        self.main_control_container.grid_columnconfigure(0, weight=1)
        
        ctk.CTkLabel(self.main_control_container, text="主要操作", 
                    font=self.title_font, text_color=COLORS['primary']).grid(
            row=0, column=0, padx=10, pady=(8, 4), sticky="w")
        
        self.auto_login_button = ctk.CTkButton(self.main_control_container, text="開始自動登入",
                                              width=260, height=30, corner_radius=15,
                                              command=self.start_auto_login, fg_color=COLORS['success'], 
                                              hover_color=COLORS['success'], font=self.default_font)
        self.auto_login_button.grid(row=1, column=0, padx=10, pady=5, sticky="ew")
        
        self.stop_login_button = ctk.CTkButton(self.main_control_container, text="停止自動登入",
                                              width=260, height=30, corner_radius=15,
                                              command=self.stop_auto_login, fg_color=COLORS['danger'], 
                                              hover_color=COLORS['danger'], font=self.default_font)
        self.stop_login_button.grid(row=2, column=0, padx=10, pady=5, sticky="ew")
        
        self.start_scan_button = ctk.CTkButton(self.main_control_container, text="開始掃描",
                                              width=260, height=30, corner_radius=15,
                                              command=self.start_scan, text_color="#333", fg_color=COLORS['warning'], 
                                              hover_color=COLORS['warning'], font=self.default_font)
        self.start_scan_button.grid(row=3, column=0, padx=10, pady=5, sticky="ew")
        
        self.stop_scan_button = ctk.CTkButton(self.main_control_container, text="停止掃描",
                                             width=260, height=30, corner_radius=15,
                                             command=self.stop_scan, fg_color=COLORS['info'], 
                                             hover_color=COLORS['info'], font=self.default_font)
        self.stop_scan_button.grid(row=4, column=0, padx=10, pady=5, sticky="ew")

        # 登入延遲設定
        delay_frame = ctk.CTkFrame(self.main_control_container, fg_color="transparent")
        delay_frame.grid(row=5, column=0, sticky="w", padx=10, pady=(5, 10))
        ctk.CTkLabel(delay_frame, text="登入延遲:", font=self.default_font).pack(side="left")
        self.auto_login_delay_entry = ctk.CTkEntry(delay_frame, width=60, placeholder_text="延遲(秒)", 
                                                  font=self.default_font)
        self.auto_login_delay_entry.pack(side="left", padx=(5, 0))
        self.auto_login_delay_entry.insert(0, str(login_delay_seconds))
        self.auto_login_delay_entry.bind("<KeyRelease>", self.on_login_delay_change)

        # 功能設定容器
        self.function_container = ctk.CTkFrame(self.right_frame, corner_radius=15, 
                                              fg_color=COLORS['card_bg'], border_width=1, border_color=COLORS['border'])
        self.function_container.grid(row=1, column=0, sticky="ew", pady=(0, 8))
        self.function_container.grid_columnconfigure((0, 1), weight=1)
        
        ctk.CTkLabel(self.function_container, text="功能設定", 
                    font=self.title_font, text_color=COLORS['primary']).grid(
            row=0, column=0, columnspan=2, padx=10, pady=(8, 4), sticky="w")
        
        # 遊戲路徑設定
        path_frame = ctk.CTkFrame(self.function_container, fg_color="transparent")
        path_frame.grid(row=1, column=0, columnspan=2, sticky="ew", padx=10, pady=5)
        path_frame.grid_columnconfigure(1, weight=1)
        
        ctk.CTkButton(path_frame, text="遊戲路徑", width=80, height=28,
                      command=self.browse_game_path, corner_radius=14,
                      fg_color=COLORS['warning'], hover_color=COLORS['warning_hover'],
                      font=self.default_font, text_color="#333").grid(row=0, column=0, padx=(0, 8))
        
        self.game_params_entry = ctk.CTkEntry(path_frame, width=60, height=28, placeholder_text="遊戲參數",
                                      font=self.default_font, corner_radius=14)
        self.game_params_entry.grid(row=0, column=1, sticky="w")  # 改為 sticky="w"，不自動擴展
        self.game_params_entry.insert(0, GAME_EXE_PARAMS)
        self.game_params_entry.bind("<FocusOut>", self.save_game_settings)
        self.game_params_entry.bind("<KeyRelease>", self.save_game_settings)
        
        self.announce_var = ctk.BooleanVar(value=recognize_announcement)
        self.announce_checkbox = ctk.CTkCheckBox(self.function_container, text="辨識公告",
                                                variable=self.announce_var, command=self.toggle_announce, 
                                                font=self.default_font)
        self.announce_checkbox.grid(row=2, column=0, padx=10, pady=2, sticky="w")
        
        self.show_scan_box_var = ctk.BooleanVar(value=False)
        self.show_scan_box_checkbox = ctk.CTkCheckBox(self.function_container, text="顯示掃描區",
                                                     variable=self.show_scan_box_var, 
                                                     command=self.on_toggle_show_scan_box, font=self.default_font)
        self.show_scan_box_checkbox.grid(row=2, column=1, padx=10, pady=2, sticky="w")
        
        self.rotation_var = ctk.BooleanVar(value=True)
        self.rotation_checkbox = ctk.CTkCheckBox(self.function_container, text="啟用輪巡",
                                                variable=self.rotation_var, command=self.toggle_rotation, 
                                                font=self.default_font)
        self.rotation_checkbox.grid(row=3, column=0, padx=10, pady=2, sticky="w")
        
        # 輪巡間隔
        rotation_frame = ctk.CTkFrame(self.function_container, fg_color="transparent")
        rotation_frame.grid(row=4, column=0, sticky="w", padx=10, pady=2)
        ctk.CTkLabel(rotation_frame, text="輪巡間隔:", font=self.default_font).pack(side="left")
        self.entry_rotation_interval = ctk.CTkEntry(rotation_frame, placeholder_text="間隔(秒)", 
                                                   width=60, font=self.default_font)
        self.entry_rotation_interval.pack(side="left", padx=(5, 0))
        self.entry_rotation_interval.insert(0, str(rotation_interval))
        self.entry_rotation_interval.bind("<FocusOut>", self.on_rotation_interval_change)
        self.entry_rotation_interval.bind("<Return>", self.on_rotation_interval_change)
        
        self.rotation_timer_label = ctk.CTkLabel(self.function_container, text="輪巡倒數：0秒", 
                                                font=self.default_font)
        self.rotation_timer_label.grid(row=3, column=1, padx=10, pady=2, sticky="w")
        
        # 自動重開設定
        self.var_restart_enabled = ctk.BooleanVar(value=False)
        self.chk_restart = ctk.CTkCheckBox(self.function_container, text="啟用自動重開",
                                          variable=self.var_restart_enabled, 
                                          command=self.on_restart_enabled_toggle, font=self.default_font)
        self.chk_restart.grid(row=5, column=0, padx=10, pady=2, sticky="w")
        
        restart_frame = ctk.CTkFrame(self.function_container, fg_color="transparent")
        restart_frame.grid(row=6, column=0, sticky="w", padx=10, pady=(2, 10))
        ctk.CTkLabel(restart_frame, text="重開間隔:", font=self.default_font).pack(side="left")
        self.entry_restart_minutes = ctk.CTkEntry(restart_frame, placeholder_text="間隔(分)", 
                                                 width=60, font=self.default_font)
        self.entry_restart_minutes.pack(side="left", padx=(5, 0))
        self.entry_restart_minutes.insert(0, str(restart_minutes))
        self.entry_restart_minutes.bind("<FocusOut>", self.on_restart_minutes_change)
        self.entry_restart_minutes.bind("<Return>", self.on_restart_minutes_change)
        
        self.restart_timer_label = ctk.CTkLabel(self.function_container, text="自動重開倒數：00天00:00:00", 
                                               font=self.default_font)
        self.restart_timer_label.grid(row=5, column=1, padx=10, pady=2, sticky="w")

        # 排程設定容器
        self.schedule_container = ctk.CTkFrame(self.right_frame, corner_radius=15, 
                                              fg_color=COLORS['card_bg'], border_width=1, border_color=COLORS['border'])
        self.schedule_container.grid(row=2, column=0, sticky="ew", pady=(0, 8))
        self.schedule_container.grid_columnconfigure((0, 1, 2, 3), weight=1)
        
        self.schedule_enabled_var = ctk.BooleanVar(value=schedule_enabled)
        self.schedule_checkbox = ctk.CTkCheckBox(self.schedule_container, text="啟用重啟排程", 
                                                variable=self.schedule_enabled_var,
                                                command=self.toggle_schedule, font=self.title_font,
                                                text_color=COLORS['primary'])
        self.schedule_checkbox.grid(row=0, column=0, columnspan=2, padx=10, pady=(8, 4), sticky="w")
        
        self.schedule_timer_label = ctk.CTkLabel(self.schedule_container, text="排程倒數：00天00:00:00",
                                                font=self.default_font)
        self.schedule_timer_label.grid(row=0, column=2, columnspan=2, padx=10, pady=(8, 4), sticky="w")

        days = ["週一", "週二", "週三", "週四", "週五", "週六", "週日"]
        self.schedule_days = []

        # 週一到週四
        for row, i in enumerate(range(4)):
                row_frame = ctk.CTkFrame(self.schedule_container, fg_color="transparent")
                row_frame.grid(row=row+1, column=0, sticky="w", padx=10, pady=1)
                var = ctk.BooleanVar(value=schedule_times[str(i)]["enabled"])
                cb = ctk.CTkCheckBox(row_frame, text="", variable=var, command=self.save_schedule, width=18)
                cb.pack(side="left", padx=0)
                label = ctk.CTkLabel(row_frame, text=days[i], anchor="w", font=self.default_font)
                label.pack(side="left", padx=(4, 6))
                entry = ctk.CTkEntry(row_frame, width=54, font=self.default_font)
                entry.pack(side="left", padx=(6, 2))
                def on_time_entry_keyrelease(event, ent=entry):
                        val = ent.get()
                        if len(val) == 2 and ':' not in val:
                                ent.insert(2, ':')
                entry.bind("<KeyRelease>", on_time_entry_keyrelease)
                entry.insert(0, schedule_times[str(i)]["time"])
                entry.bind("<FocusOut>", lambda e: self.save_schedule())
                entry.bind("<Return>", lambda e: self.save_schedule())
                self.schedule_days.append({"var": var, "entry": entry})

        # 週五到週日
        for row, i in enumerate(range(4, 7)):
                row_frame = ctk.CTkFrame(self.schedule_container, fg_color="transparent")
                row_frame.grid(row=row+1, column=2, sticky="w", padx=10, pady=1)
                var = ctk.BooleanVar(value=schedule_times[str(i)]["enabled"])
                cb = ctk.CTkCheckBox(row_frame, text="", variable=var, command=self.save_schedule, width=18)
                cb.pack(side="left", padx=0)
                label = ctk.CTkLabel(row_frame, text=days[i], anchor="w", font=self.default_font)
                label.pack(side="left", padx=(4, 6))
                entry = ctk.CTkEntry(row_frame, width=54, font=self.default_font)
                entry.pack(side="left", padx=(6, 2))
                def on_time_entry_keyrelease(event, ent=entry):
                        val = ent.get()
                        if len(val) == 2 and ':' not in val:
                                ent.insert(2, ':')
                entry.bind("<KeyRelease>", on_time_entry_keyrelease)
                entry.insert(0, schedule_times[str(i)]["time"])
                entry.bind("<FocusOut>", lambda e: self.save_schedule())
                entry.bind("<Return>", lambda e: self.save_schedule())
                self.schedule_days.append({"var": var, "entry": entry})

        
        # 下方日誌區域 - 分兩欄對齊上方
        self.log_container = ctk.CTkFrame(self, fg_color="transparent")
        self.log_container.grid(row=1, column=0, columnspan=2, sticky="nsew", padx=10, pady=(0, 10))
        self.log_container.grid_columnconfigure(0, weight=0, minsize=350)  # 左側固定寬度對齊帳號區
        self.log_container.grid_columnconfigure(1, weight=1, minsize=350)   # 右側自適應對齊操作區
        self.log_container.grid_rowconfigure(0, weight=1)

        # 左側：掃描監控日誌
        self.scan_log_card = ctk.CTkFrame(self.log_container, corner_radius=15, 
                                         fg_color=COLORS['card_bg'], border_width=1, border_color=COLORS['border'])
        self.scan_log_card.grid(row=0, column=0, sticky="nsew", padx=(0, 2))  # 減少右側間距
        self.scan_log_card.grid_rowconfigure(1, weight=1)
        self.scan_log_card.grid_columnconfigure(0, weight=1)
        
        # 掃描日誌標題
        scan_header = ctk.CTkFrame(self.scan_log_card, fg_color="transparent")
        scan_header.grid(row=0, column=0, sticky="ew", padx=10, pady=(10, 5))
        scan_header.grid_columnconfigure(0, weight=1)
        
        ctk.CTkLabel(scan_header, text="掃描監控日誌", 
                    font=self.title_font, text_color=COLORS['primary']).pack(side="left")
        
        ctk.CTkLabel(scan_header, text="停止滾動", font=self.default_font).pack(side="right", padx=(0, 5))
        self.stop_scroll_scan_var = ctk.BooleanVar(value=False)
        ctk.CTkCheckBox(scan_header, text="", variable=self.stop_scroll_scan_var, 
                       command=self.on_toggle_stop_scroll_scan, width=18).pack(side="right")
        
        self.scan_log_textbox = ctk.CTkTextbox(self.scan_log_card, corner_radius=10, 
                                              border_width=2, border_color=COLORS['border'], 
                                              font=self.default_font)
        self.scan_log_textbox.grid(row=1, column=0, sticky="nsew", padx=10, pady=(0, 10))

        # 右側：登入監控日誌
        self.login_log_card = ctk.CTkFrame(self.log_container, corner_radius=15, 
                                          fg_color=COLORS['card_bg'], border_width=1, border_color=COLORS['border'])
        self.login_log_card.grid(row=0, column=1, sticky="nsew", padx=(3, 0))  # 保持原配置
        self.login_log_card.grid_rowconfigure(1, weight=1)
        self.login_log_card.grid_columnconfigure(0, weight=1)
        
        # 登入日誌標題
        login_header = ctk.CTkFrame(self.login_log_card, fg_color="transparent")
        login_header.grid(row=0, column=0, sticky="ew", padx=10, pady=(10, 5))
        login_header.grid_columnconfigure(0, weight=1)
        
        ctk.CTkLabel(login_header, text="登入監控日誌", 
                    font=self.title_font, text_color=COLORS['primary']).pack(side="left")
        
        ctk.CTkLabel(login_header, text="停止滾動", font=self.default_font).pack(side="right", padx=(0, 5))
        self.stop_scroll_login_var = ctk.BooleanVar(value=False)
        ctk.CTkCheckBox(login_header, text="", variable=self.stop_scroll_login_var, 
                       command=self.on_toggle_stop_scroll_login, width=18).pack(side="right")
        
        self.login_log_textbox = ctk.CTkTextbox(self.login_log_card, corner_radius=10, 
                                               border_width=2, border_color=COLORS['border'], 
                                               font=self.default_font)
        self.login_log_textbox.grid(row=1, column=0, sticky="nsew", padx=10, pady=(0, 10))

        # 初始化
        self.refresh_account_list()
    # ===== 帳號管理方法 =====
    def add_account(self):
        """新增帳號"""
        user = self.account_entry.get().strip()
        pwd = self.password_entry.get().strip()
        if not user or not pwd:
            write_login_log("❗ 帳號與密碼不可為空")
            if not user:
                self.account_entry.focus_set()
            else:
                self.password_entry.focus_set()
            return
        accounts.append({"username": user, "password": pwd, "enabled": True})
        self.account_entry.delete(0, "end")
        self.password_entry.delete(0, "end")
        save_accounts()
        self.refresh_account_list()
        write_login_log(f"✅ 新增帳號：{user}")
        self.account_entry.focus_set()

    def refresh_account_list(self):
        """刷新帳號清單"""
        for w in self.account_list_frame.winfo_children():
            w.destroy()
        vars_checkbox.clear()
        self.account_list_frame.grid_columnconfigure(0, weight=1)

        def move_account_up(idx):
            if idx > 0:
                accounts[idx - 1], accounts[idx] = accounts[idx], accounts[idx - 1]
                save_accounts()
                self.refresh_account_list()
                write_login_log(f"📈 帳號上移")

        def move_account_down(idx):
            if idx < len(accounts) - 1:
                accounts[idx + 1], accounts[idx] = accounts[idx], accounts[idx + 1]
                save_accounts()
                self.refresh_account_list()
                write_login_log(f"📉 帳號下移")

        for idx, acc in enumerate(accounts):
            row_frame = ctk.CTkFrame(
                self.account_list_frame,
                corner_radius=12,
                fg_color=COLORS['card_bg'],
                border_width=1,
                border_color=COLORS['border']
            )
            row_frame.grid(row=idx, column=0, sticky="ew", padx=6, pady=3)
            row_frame.grid_columnconfigure(0, weight=0)
            row_frame.grid_columnconfigure(1, weight=1)
            row_frame.grid_columnconfigure(2, weight=0)

            # 勾選框與帳號名稱
            var = ctk.BooleanVar(value=acc.get("enabled", False))
            cb = ctk.CTkCheckBox(
                row_frame,
                text=acc.get("username", ""),
                variable=var,
                width=20,
                font=self.default_font,
                fg_color=COLORS['success'],
                border_color=COLORS['success']
            )
            cb.grid(row=0, column=0, padx=(8, 6), pady=6, sticky="w")
            vars_checkbox.append(var)

            # 密碼顯示
            pwd_display = "*" * len(acc.get("password", ""))
            pwd_label = ctk.CTkLabel(row_frame, text=pwd_display, anchor="w", 
                                     font=self.default_font)
            pwd_label.grid(row=0, column=1, sticky="ew", padx=(6, 6), pady=6)

            # 操作按鈕區
            btn_frame = ctk.CTkFrame(row_frame, fg_color="transparent")
            btn_frame.grid(row=0, column=2, sticky="e", padx=(6, 8), pady=4)

            # 刪除按鈕
            del_btn = ctk.CTkButton(
                btn_frame, text="刪", width=28, height=24,
                fg_color=COLORS['danger'],
                command=lambda i=idx: self.delete_account(i),
                corner_radius=12, font=self.default_font
            )
            del_btn.pack(side="right", padx=(2, 0))

            # 上移按鈕
            up_btn = ctk.CTkButton(
                btn_frame, text="↑", width=28, height=24,
                command=lambda i=idx: move_account_up(i), corner_radius=12,
                font=self.default_font, 
                fg_color=COLORS['primary']
            )
            up_btn.pack(side="right", padx=1)

            # 下移按鈕
            down_btn = ctk.CTkButton(
                btn_frame, text="↓", width=28, height=24,
                command=lambda i=idx: move_account_down(i), corner_radius=12,
                font=self.default_font, 
                fg_color=COLORS['primary']
            )
            down_btn.pack(side="right", padx=1)

    def delete_account(self, idx):
        """刪除帳號"""
        if 0 <= idx < len(accounts):
            username = accounts[idx].get("username", "未知")
            del accounts[idx]
            save_accounts()
            self.refresh_account_list()
            write_login_log(f"✕ 已刪除帳號：{username}")

    # ===== 功能控制方法 =====
    def start_auto_login(self):
        """開始自動登入"""
        threading.Thread(target=login_all_accounts, daemon=True).start()

    def stop_auto_login(self):
        """停止自動登入"""
        global login_stopped
        login_stopped = True
        write_login_log("■ 停止自動登入")

    def start_scan(self):
        """開始掃描"""
        global scan_running
        if scan_running:
            write_scan_log("掃描已在執行中")
            return
        scan_running = True
        threading.Thread(target=scan_loop, daemon=True).start()
        write_scan_log("開始掃描")

    def stop_scan(self):
        """停止掃描"""
        global scan_running
        if not scan_running:
            write_scan_log("掃描尚未啟動")
            return
        scan_running = False
        write_scan_log("停止掃描")

    # ===== 遊戲設定方法 =====
    def browse_game_path(self):
        """瀏覽遊戲路徑"""
        from tkinter import filedialog
        file_path = filedialog.askopenfilename(
            title="選擇遊戲執行檔",
            filetypes=[("執行檔", "*.exe"), ("所有檔案", "*.*")]
        )
        if file_path:
            global GAME_EXE_PATH
            GAME_EXE_PATH = file_path
            save_game_settings_to_file(GAME_EXE_PATH, self.game_params_entry.get())
            write_login_log(f"✅ 遊戲路徑已設定：{file_path}")

    def save_game_settings(self, event=None):
        """儲存遊戲設定"""
        global GAME_EXE_PARAMS
        GAME_EXE_PARAMS = self.game_params_entry.get()
        save_game_settings_to_file(GAME_EXE_PATH, GAME_EXE_PARAMS)
        write_login_log(f"✅ 遊戲參數已儲存：{GAME_EXE_PARAMS}")

    # ===== 功能設定方法 =====
    def toggle_announce(self):
        """切換公告判斷"""
        global recognize_announcement
        recognize_announcement = self.announce_var.get()
        status = "啟用" if recognize_announcement else "停用"
        write_login_log(f"公告判斷已{status}")

    def on_toggle_show_scan_box(self):
        """切換掃描區顯示"""
        if self.show_scan_box_var.get():
            start_show_scan_region_box()
            write_scan_log("掃描區顯示已啟用")
        else:
            stop_show_scan_region_box()
            write_scan_log("掃描區顯示已停用")

    def toggle_rotation(self):
        """切換輪巡功能"""
        global rotation_countdown, rotation_running
        if self.rotation_var.get():
            write_login_log("輪巡啟用")
            rotation_paused.set()
            if not rotation_running and windows_handles:
                start_window_rotation(windows_handles)
            with rotation_countdown_lock:
                rotation_countdown = rotation_interval
        else:
            write_login_log("輪巡停用")
            rotation_paused.clear()
            stop_window_rotation()
            with rotation_countdown_lock:
                rotation_countdown = 0
            self.set_rotation_timer_label(0)

    def toggle_schedule(self):
        """切換排程功能"""
        global schedule_enabled
        schedule_enabled = self.schedule_enabled_var.get()
        status = "啟用" if schedule_enabled else "停用"
        write_login_log(f"重啟排程已{status}")

    def save_schedule(self):
        """儲存排程設定"""
        global schedule_times
        for i, day_setting in enumerate(self.schedule_days):
            schedule_times[str(i)] = {
                "enabled": day_setting["var"].get(),
                "time": day_setting["entry"].get()
            }
        write_login_log("排程設定已儲存")

    def on_rotation_interval_change(self, event=None):
        """輪巡間隔變更"""
        global rotation_interval, rotation_countdown
        try:
            val = int(self.entry_rotation_interval.get())
            if val < 1:
                val = 1
        except:
            val = rotation_interval
        rotation_interval = val
        self.entry_rotation_interval.delete(0, ctk.END)
        self.entry_rotation_interval.insert(0, str(val))
        write_scan_log(f"輪巡間隔已設為 {rotation_interval} 秒")

    def on_login_delay_change(self, event=None):
        """登入延遲變更"""
        global login_delay_seconds
        try:
            val = int(self.auto_login_delay_entry.get())
            if val < 0:
                val = 0
        except:
            val = login_delay_seconds
        login_delay_seconds = val

    def on_restart_enabled_toggle(self):
        """自動重開啟用切換"""
        global restart_countdown, restart_minutes, restart_enabled
        restart_enabled = self.var_restart_enabled.get()
        if not restart_enabled:
            with restart_countdown_lock:
                restart_countdown = 0
            self.set_restart_timer_label(0)
            write_login_log("自動重開已停用")
        else:
            try:
                val = int(self.entry_restart_minutes.get())
                if val > 0:
                    with restart_countdown_lock:
                        restart_minutes = val
                        restart_countdown = restart_minutes * 60
                    write_login_log(f"自動重開已啟用，間隔 {restart_minutes} 分鐘")
            except:
                pass

    def on_restart_minutes_change(self, event=None):
        """重開間隔變更"""
        global restart_minutes
        try:
            val = int(self.entry_restart_minutes.get())
            if val <= 0:
                val = 20
            restart_minutes = val
        except:
            pass

    # ===== 日誌控制方法 =====
    def on_toggle_stop_scroll_scan(self):
        """切換掃描日誌自動滾動"""
        global stop_auto_scroll_scan_log
        stop_auto_scroll_scan_log = self.stop_scroll_scan_var.get()

    def on_toggle_stop_scroll_login(self):
        """切換登入日誌自動滾動"""
        global stop_auto_scroll_login_log
        stop_auto_scroll_login_log = self.stop_scroll_login_var.get()

    # ===== 計時器標籤更新方法 =====
    def set_restart_timer_label(self, seconds):
        """設定重啟計時器標籤"""
        text = format_countdown(seconds)
        self.restart_timer_label.configure(text=f"自動重開倒數：{text}")

    def set_rotation_timer_label(self, seconds):
        """設定輪巡計時器標籤"""
        self.rotation_timer_label.configure(text=f"輪巡倒數：{seconds}秒")

    def set_schedule_timer_label(self, seconds):
        """設定排程計時器標籤"""
        text = format_countdown(seconds)
        self.schedule_timer_label.configure(text=f"排程倒數：{text}")

    def update_current_time(self):
        """更新目前時間顯示"""
        now = datetime.now()
        weekday_map = ["週一", "週二", "週三", "週四", "週五", "週六", "週日"]
        week_str = weekday_map[now.weekday()]
        time_str = now.strftime("%Y/%m/%d %H:%M:%S")
        self.current_time_label.configure(text=f"目前時間：{time_str} {week_str}")
        self.after(1000, self.update_current_time)

    def on_close(self):
        """關閉應用程式"""
        global scan_running, rotation_running, login_stopped
        login_stopped = True
        scan_running = False
        rotation_running = False
        restart_thread_stop_event.set()
        self.destroy()

# ===== 格式化倒數時間 =====
def format_countdown(seconds):
    """格式化倒數時間顯示"""
    seconds = int(max(seconds, 0))
    days = seconds // 86400
    hours = (seconds % 86400) // 3600
    minutes = (seconds % 3600) // 60
    sec = seconds % 60
    return f"{days}天{hours:02d}:{minutes:02d}:{sec:02d}"

# ===== 帳號資料儲存/載入 =====
def save_accounts(filepath=ACCOUNTS_CONFIG):
    """儲存帳號資料"""
    for idx, acc in enumerate(accounts):
        if idx < len(vars_checkbox):
            acc["enabled"] = vars_checkbox[idx].get()
    try:
        with open(filepath, "w", encoding="utf-8") as f:
            json.dump(accounts, f, ensure_ascii=False, indent=2)
        write_login_log(f"帳號已儲存")
    except Exception as e:
        write_login_log(f"儲存帳號失敗: {e}")

def load_accounts(filepath=ACCOUNTS_CONFIG):
    """載入帳號資料"""
    global accounts
    if os.path.exists(filepath):
        try:
            with open(filepath, "r", encoding="utf-8") as f:
                accounts[:] = json.load(f)
        except Exception as e:
            accounts[:] = []
            write_login_log(f"載入帳號失敗: {e}")
    else:
        accounts[:] = []
    
    if hasattr(app, "refresh_account_list"):
        app.refresh_account_list()

# ===== 主程式入口 =====
if __name__ == "__main__":
    # 設定外觀
    ctk.set_appearance_mode("dark")
    ctk.set_default_color_theme("dark-blue")
    
    # 建立應用程式
    app = AccountManagerApp()
    
    # 載入資料
    load_accounts()
    load_event_templates()
    
    # 啟動計時器線程
    threading.Thread(target=restart_timer_thread, daemon=True).start()
    threading.Thread(target=schedule_timer_thread, daemon=True).start()
    
    # 啟動主程式
    write_login_log("金庸自動掛機助手已啟動")
    app.mainloop()
