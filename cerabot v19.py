from typing import Any, Dict, List, Optional, Tuple, Set, Union, Protocol
from dataclasses import dataclass, field
import pydirectinput
import time
import pymem
import threading
import frida
import pyautogui
import bresenham
import json
import tkinter as tk
from ttkthemes import ThemedTk
from pynput import keyboard
from tkinter import ttk
from pathlib import Path
import os, sys
from collections import deque
import re
import copy
import shutil
import ctypes
from ctypes import wintypes
from tkinter import messagebox, simpledialog
try:
    import win32gui
    import win32con
    import win32process
except Exception:
    win32gui = None
    win32con = None
    win32process = None

def _app_base_dir() -> Path:
    """Return the writable base folder for config/data files."""
    if getattr(sys, "frozen", False):
        return Path(sys.executable).resolve().parent
    return Path(__file__).resolve().parent

def _resource_base_dir() -> Path:
    """Return the bundled resource folder (PyInstaller temp dir when onefile)."""
    if getattr(sys, "frozen", False):
        meipass = getattr(sys, "_MEIPASS", None)
        if meipass:
            return Path(str(meipass)).resolve()
    return _app_base_dir()

def _copy_missing_files(src_dir: Path, dst_dir: Path):
    """Copy bundled defaults into writable runtime dirs without overwriting user files."""
    try:
        if not src_dir.is_dir():
            return
    except Exception:
        return

    try:
        if src_dir.resolve() == dst_dir.resolve():
            return
    except Exception:
        pass

    for src_file in src_dir.rglob("*"):
        try:
            if not src_file.is_file():
                continue
            rel = src_file.relative_to(src_dir)
            dst_file = dst_dir / rel
            if dst_file.exists():
                continue
            dst_file.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(src_file, dst_file)
        except Exception:
            pass

def _seed_runtime_data_dirs(app_base_dir: Path, resource_base_dir: Path, config_dir: Path, walkable_maps_dir: Path):
    """
    For frozen builds, pre-populate writable runtime folders from bundled assets.
    Keeps user-edited files persistent beside the EXE.
    """
    if not getattr(sys, "frozen", False):
        return

    try:
        config_dir.mkdir(parents=True, exist_ok=True)
    except Exception:
        pass
    try:
        walkable_maps_dir.mkdir(parents=True, exist_ok=True)
    except Exception:
        pass

    for cfg_name in ("config", "Config"):
        _copy_missing_files(resource_base_dir / cfg_name, config_dir)
    _copy_missing_files(resource_base_dir / "walkable_maps", walkable_maps_dir)
BOT_GUI = None  # Global reference to the GUI instance
pydirectinput.FAILSAFE = False  # Disable fail-safe to allow corner screen interactions
pyautogui.PAUSE = 0

NPC_AOB    = "66 89 90 A0 00 00 00"
npcAddress = None
WALK_AOB = "BA 02 00 00 00 89 41 08 8D 85 F4 FD FF FF"
walkAddress = None
DIRECTIONAL_AOB = "88 53 56 8B 0D ?? ?? ?? ?? 8B 01 8B 90 ?? ?? 00 00"
directionalAddress = None
SPEECH_AOB = "89 8B 8C 02 00 00"  # mov [ebx+28C], ecx
NPC_NAME_OFFSET = 0x20
TEXT_OFFSET = 0x24

EXP_AOB = "8B 55 0C 33 F6 89 53 28 81 FE ?? ?? 00 00"
HP_AOB = "89 B4 8B F0 01 00 00"
MANA_AOB = "89 B4 8B 88 03 00 00"
OTHER_PLAYERS_AOB = "66 89 91 50 01 00 00"
MAP_ID_AOB = "89 4B 14 8B 85 1C FF FF FF 89 43 1C"

NPC_ADD1_AOB = "66 01 81 A0 00 00 00"
NPC_ADD2_AOB = "66 01 82 A2 00 00 00"

NPC_VAR_OFFSET = 0xA0

SPAWN_UID_OFFSET = 0xA0
MOB_ID_OFFSET = 0x98     # we read short at address_x - 0x98
MOB_ID_FILTERS = {285, 302, 188, 422, 538, 286, 292, 672, 301, 543, 325, 321, 
                  319, 305, 502, 511, 512, 513, 514, 754, 413, 15, 324, 412, 84, 
                  421, 422, 417}

LAST_MOVED_TIMER_SECONDS = 35     # how long before unmoved NPC is stale
FLANK_RANGE = 1
INVALID_COORD_LIMIT = 100    # max valid X/Y (anything higher is junk)
RANGE_MODE = {}
AVOID_OTHER_PLAYERS = False
map_data_lock = threading.Lock()
current_path_tiles: List[Tuple[int, int]] = []
path_fade_timestamp: Optional[float] = None
RECENT_REMOVALS: Dict[str, Tuple[str, float]] = {}
player_base = None
_FRIDA_HOOKS_LOCK = threading.Lock()
_FRIDA_HOOKS: List[Tuple[str, Any, Any]] = []
_RUNTIME_STATE_LOCK = threading.RLock()

recent_speech_log = deque(maxlen=120)
npc_last_speech = {}             # addr_hex -> {"text": str, "ts": float}
speech_quarantine_until = 0.0
speech_quarantine_reason = ""
speech_quarantine_source = ""
TRIGGERS = [
    r'\bmax\b',
    r'\bnecklace\b',
    r'\bdecoy\b',
    r'\bdcoy\b',
    r'\bplease stop\b',
    r'\b5\b',
]  # optional regex triggers
SPEECH_QUARANTINE_SEC = 120.0
other_players = {}  # Dict to store found player X addresses (used by get_nearby_players)
other_players_lock = threading.Lock()

TARGET_PID = None  # Selected Endless.exe PID when multiple clients are open

x_address = None
y_address = None
directional_address = None
mapIdAddress = None
current_target_npc = None
pm = None  # Global pymem instance
stat_base = None  
CLICKING_ENABLED = True
resurrect_points = []
player_click_point = None  # Click point for self-buff (player character position)
movement_allowed = threading.Event()
movement_allowed.set()
clicks_in_progress = threading.Event()
WANDER_TIMEOUT_S = 15.0  # max time to wander with no targets before re-running Home
game_win = None
STOP_HOME_IF_TARGET = True
IGNORE_PROTECTION = False          # False = protection ON, True = ignore (boss mode)
POST_PROTECT_GRACE_S = 2.0       # tiny debounce after protection ends
NEARBY_THREAT_RADIUS = 1         # radius for threat detection
DARK_MODE = True                   # Forced dark mode

HOME_POS = (3, 12)     # <<< SET THIS to your desired (X, Y) "home" tile
RUN_HOME_AFTER_KILL = True
HOME_NEAR_THRESH = 1       # distance in tiles considered "arrived
HOME_TRAVEL_TIMEOUT = 0.0  # <= 0 disables home-navigation timeout
HP_HOME_ENABLED   = False   # master toggle for HP-based home logic
HP_HOME_ACTIVE    = False
HP_HOME_LOW_PCT   = 30.0    # go home if HP <= this %
HP_HOME_HIGH_PCT  = 60.0    # stand up again when HP >= this %
AUTO_LOAD_MAP_BY_ID = False
START_MAP_ID: Optional[int] = None
_wander_damage_abort = False
HP_HOME_ABORT_LOCK = False
HP_HOME_LAST_ABORT = 0.0
home_routine_running = threading.Event()
WALKABLE_ARG = sys.argv[1] if len(sys.argv) > 1 else None
_WALKABLE_CACHE_LOCK = threading.Lock()
_WALKABLE_CACHE_TILES: Optional[Set[Tuple[int, int]]] = None
_WALKABLE_CACHE_PATH: Optional[Path] = None
_WALKABLE_CACHE_MTIME: Optional[float] = None
IMMUNITY_SEC = 0.0  # first N seconds to ignore death detection for a fresh target
_target_immunity_until = {}  # addr_hex -> monotonic deadline
BOSS_AGGRO_TOGGLE = True  # <<< Toggle for boss aggro detection during sitting
SIT_TIMER_SECONDS = 70   # <<< Configurable sit timer in seconds
APP_BASE_DIR = _app_base_dir()
RESOURCE_BASE_DIR = _resource_base_dir()
WALKABLE_MAPS_DIR = APP_BASE_DIR / "walkable_maps"
CONFIG_DIR = APP_BASE_DIR / "config"
DEFAULT_CONFIG_FILE_NAME = "cerabot_config.json"
LEGACY_CONFIG_FILE_NAME = "cerafrog_config.json"
CONFIG_FILE = str((CONFIG_DIR / DEFAULT_CONFIG_FILE_NAME).resolve())  # Active config file path
_seed_runtime_data_dirs(APP_BASE_DIR, RESOURCE_BASE_DIR, CONFIG_DIR, WALKABLE_MAPS_DIR)
KILL_QUARANTINE_SEC = 1.0        # keep a killed NPC muted for ~8s (prevents re-targeting during home routine)
RECENTLY_KILLED: Dict[str, float] = {}  # addr_hex -> time.monotonic()
_last_kill_ts: Dict[str, float] = {}
_kill_lock = threading.Lock()
KILL_DEBOUNCE_SEC = 0.25
DIRECTIONAL_LOOT = True          # pick 1 of 4, based on facing
LOOT_HOLD_SECONDS = 3.0       # how long to keep clicking one spot
FAST_CLICK = False
FAST_CLICK_BURST_COUNT = 3
FAST_CLICK_GAP_S = 0.12 
ATTACK_RECENCY_S = 0.3
last_attack_time = 0.0
last_attack_addr = None
ATTACK_ACTIVE = False
vanish_timer: Dict[str, float] = {}
get_player_coords = None
_HP_FRIDA_SESSION = None
_HP_FRIDA_SCRIPT  = None  # Keep Python-side reference so hook script is not GC'd.
_MANA_FRIDA_SESSION = None
_MANA_FRIDA_SCRIPT  = None  # Keep Python-side reference so hook script is not GC'd.
_MAP_ID_FRIDA_SESSION = None
_MAP_ID_FRIDA_SCRIPT = None
NO_CLICK_UNTIL = 0.0
CLICK_BUFFS_ENABLED    = False       # GUI toggle
CLICK_BUFF_INTERVAL_S  = 20.0        # seconds between F6 self-buff clicks
F5_TAP_COUNT = 24
HOME_AFTER_KILLS_N = 1
KILLS_SINCE_HOME = 0

HP_BUFFS_ENABLED        = False
HP_BUFF_THRESHOLD_PCT   = 40.0   # start healing
HP_BUFF_TARGET_PCT      = 60.0   # stop healing ONLY after this
HP_BUFF_COOLDOWN_S      = 1.0    # potion cooldown

UI_UPDATE_INTERVAL_MS = 50
UI_RUNTIME_REFRESH_S = 0.10
UI_MAP_REFRESH_S = 0.10
UI_OTHER_PLAYERS_REFRESH_S = 0.20
UI_STATS_REFRESH_S = 0.50
UI_CHAT_REFRESH_S = 0.20

_WARN_THROTTLE: Dict[str, float] = {}
LOG_VERBOSITY = int(os.environ.get("CERABOT_LOG_VERBOSITY", "1"))  # 0=warn/error, 1=info, 2=debug
_RAW_PRINT = print

_MAP_ID_LOCK = threading.Lock()
CURRENT_MAP_ID: Optional[int] = None
LAST_MAP_ID_TS: float = 0.0

_WALKABLE_SOURCE_LOCK = threading.Lock()
WALKABLE_SOURCE_MODE = "file"  # "file" or "default_grid"
WALKABLE_SOURCE_MESSAGE = ""
WALKABLE_SOURCE_PATH: Optional[str] = None
_INITIAL_CONFIG_STATE: Optional["ConfigState"] = None

DIR_TO_SLOT = {
    0: 2,  # 0 = Down  -> points[2]
    1: 3,  # 1 = Left  -> points[3]
    2: 0,  # 2 = Up    -> points[0]
    3: 1,  # 3 = Right -> points[1]
}

bot_running = False  # set true only when Start is pressed

HOTKEY_BINDINGS = {
    "mine": "f1",        # Tool hotkey for mining
    "chop": "f2",        # Tool hotkey for chopping
    "hp_buff": "f3",     # HP-based buff / potion hotkey
    "buff": "f5",        # Buff hotkey
    "buff_self": "f6",   # Self-buff hotkey
    "sit_cancel": "f7",  # Sit animation cancel
    "weapon": "f8",      # Combat weapon switch
    "stand": "f11",      # Stand up from sit
}

@dataclass
class ConfigState:
    boss_aggro_toggle: bool = True
    sit_timer_seconds: int = 70
    last_moved_timer_seconds: int = 35
    mob_id_filters: Set[int] = field(default_factory=set)
    home_pos: Tuple[int, int] = (3, 12)
    flank_range: int = 1
    run_home_after_kill: bool = True
    clicking_enabled: bool = True
    fast_click: bool = False
    fast_click_burst_count: int = 3
    fast_click_gap_s: float = 0.12
    click_buffs_enabled: bool = False
    click_buff_interval_s: float = 20.0
    hp_buffs_enabled: bool = False
    hp_buff_threshold_pct: float = 40.0
    ignore_protection: bool = False
    f5_tap_count: int = 24
    wander_timeout_s: float = 15.0
    home_after_kills_n: int = 1
    avoid_other_players: bool = False
    hp_home_enabled: bool = False
    hp_home_low_pct: float = 30.0
    hp_home_high_pct: float = 60.0
    hp_buff_target_pct: float = 60.0
    hp_buff_cooldown_s: float = 1.0
    auto_load_map_by_id: bool = False
    start_map_id: Optional[int] = None
    resurrect_points: List[Tuple[int, int]] = field(default_factory=list)
    player_click_point: Optional[Tuple[int, int]] = None
    dark_mode: bool = True
    hotkey_bindings: Dict[str, str] = field(default_factory=dict)

@dataclass
class RuntimeState:
    bot_running: bool = False
    attack_active: bool = False
    last_attack_time: float = 0.0
    last_attack_addr: Optional[str] = None
    no_click_until: float = 0.0
    target_pid: Optional[int] = None

CONFIG_STATE = ConfigState()
RUNTIME_STATE = RuntimeState()

def _coerce_int_set(values: Any, fallback: Optional[Set[int]] = None) -> Set[int]:
    out: Set[int] = set()
    src = values if values is not None else (fallback or set())
    for v in src:
        try:
            out.add(int(v))
        except Exception:
            pass
    return out

def _refresh_config_state_from_globals():
    CONFIG_STATE.boss_aggro_toggle = bool(BOSS_AGGRO_TOGGLE)
    CONFIG_STATE.sit_timer_seconds = int(SIT_TIMER_SECONDS)
    CONFIG_STATE.last_moved_timer_seconds = int(LAST_MOVED_TIMER_SECONDS)
    CONFIG_STATE.mob_id_filters = _coerce_int_set(MOB_ID_FILTERS)
    CONFIG_STATE.home_pos = tuple(HOME_POS) if isinstance(HOME_POS, (list, tuple)) and len(HOME_POS) == 2 else (3, 12)
    CONFIG_STATE.flank_range = int(FLANK_RANGE)
    CONFIG_STATE.run_home_after_kill = bool(RUN_HOME_AFTER_KILL)
    CONFIG_STATE.clicking_enabled = bool(CLICKING_ENABLED)
    CONFIG_STATE.fast_click = bool(FAST_CLICK)
    CONFIG_STATE.fast_click_burst_count = int(FAST_CLICK_BURST_COUNT)
    CONFIG_STATE.fast_click_gap_s = float(FAST_CLICK_GAP_S)
    CONFIG_STATE.click_buffs_enabled = bool(CLICK_BUFFS_ENABLED)
    CONFIG_STATE.click_buff_interval_s = float(CLICK_BUFF_INTERVAL_S)
    CONFIG_STATE.hp_buffs_enabled = bool(HP_BUFFS_ENABLED)
    CONFIG_STATE.hp_buff_threshold_pct = float(HP_BUFF_THRESHOLD_PCT)
    CONFIG_STATE.ignore_protection = bool(IGNORE_PROTECTION)
    CONFIG_STATE.f5_tap_count = int(F5_TAP_COUNT)
    CONFIG_STATE.wander_timeout_s = float(WANDER_TIMEOUT_S)
    CONFIG_STATE.home_after_kills_n = int(HOME_AFTER_KILLS_N)
    CONFIG_STATE.avoid_other_players = bool(AVOID_OTHER_PLAYERS)
    CONFIG_STATE.hp_home_enabled = bool(HP_HOME_ENABLED)
    CONFIG_STATE.hp_home_low_pct = float(HP_HOME_LOW_PCT)
    CONFIG_STATE.hp_home_high_pct = float(HP_HOME_HIGH_PCT)
    CONFIG_STATE.hp_buff_target_pct = float(HP_BUFF_TARGET_PCT)
    CONFIG_STATE.hp_buff_cooldown_s = float(HP_BUFF_COOLDOWN_S)
    CONFIG_STATE.auto_load_map_by_id = bool(AUTO_LOAD_MAP_BY_ID)
    CONFIG_STATE.start_map_id = int(START_MAP_ID) if START_MAP_ID is not None else None
    CONFIG_STATE.resurrect_points = [tuple(p) for p in resurrect_points if isinstance(p, (list, tuple)) and len(p) == 2]
    CONFIG_STATE.player_click_point = tuple(player_click_point) if isinstance(player_click_point, (list, tuple)) and len(player_click_point) == 2 else None
    CONFIG_STATE.dark_mode = bool(DARK_MODE)
    CONFIG_STATE.hotkey_bindings = HOTKEY_BINDINGS.copy()

def _apply_config_state_to_globals():
    global BOSS_AGGRO_TOGGLE, SIT_TIMER_SECONDS, LAST_MOVED_TIMER_SECONDS, MOB_ID_FILTERS, HOME_POS
    global FLANK_RANGE, RUN_HOME_AFTER_KILL, CLICKING_ENABLED, FAST_CLICK, FAST_CLICK_BURST_COUNT
    global FAST_CLICK_GAP_S, IGNORE_PROTECTION, HOME_AFTER_KILLS_N, F5_TAP_COUNT, WANDER_TIMEOUT_S
    global HP_HOME_ENABLED, HP_HOME_LOW_PCT, HP_HOME_HIGH_PCT, AVOID_OTHER_PLAYERS
    global CLICK_BUFFS_ENABLED, CLICK_BUFF_INTERVAL_S, HP_BUFFS_ENABLED, HP_BUFF_THRESHOLD_PCT
    global HP_BUFF_TARGET_PCT, HP_BUFF_COOLDOWN_S, AUTO_LOAD_MAP_BY_ID, START_MAP_ID, player_click_point, DARK_MODE

    BOSS_AGGRO_TOGGLE = bool(CONFIG_STATE.boss_aggro_toggle)
    SIT_TIMER_SECONDS = int(CONFIG_STATE.sit_timer_seconds)
    LAST_MOVED_TIMER_SECONDS = int(CONFIG_STATE.last_moved_timer_seconds)
    MOB_ID_FILTERS = _coerce_int_set(CONFIG_STATE.mob_id_filters, fallback=MOB_ID_FILTERS)
    HOME_POS = tuple(CONFIG_STATE.home_pos) if isinstance(CONFIG_STATE.home_pos, (list, tuple)) and len(CONFIG_STATE.home_pos) == 2 else HOME_POS
    FLANK_RANGE = int(CONFIG_STATE.flank_range)
    RUN_HOME_AFTER_KILL = bool(CONFIG_STATE.run_home_after_kill)
    CLICKING_ENABLED = bool(CONFIG_STATE.clicking_enabled)
    FAST_CLICK = bool(CONFIG_STATE.fast_click)
    FAST_CLICK_BURST_COUNT = int(CONFIG_STATE.fast_click_burst_count)
    FAST_CLICK_GAP_S = float(CONFIG_STATE.fast_click_gap_s)
    CLICK_BUFFS_ENABLED = bool(CONFIG_STATE.click_buffs_enabled)
    CLICK_BUFF_INTERVAL_S = float(CONFIG_STATE.click_buff_interval_s)
    HP_BUFFS_ENABLED = bool(CONFIG_STATE.hp_buffs_enabled)
    HP_BUFF_THRESHOLD_PCT = float(CONFIG_STATE.hp_buff_threshold_pct)
    IGNORE_PROTECTION = bool(CONFIG_STATE.ignore_protection)
    F5_TAP_COUNT = int(CONFIG_STATE.f5_tap_count)
    WANDER_TIMEOUT_S = float(CONFIG_STATE.wander_timeout_s)
    HOME_AFTER_KILLS_N = max(1, int(CONFIG_STATE.home_after_kills_n))
    AVOID_OTHER_PLAYERS = bool(CONFIG_STATE.avoid_other_players)
    HP_HOME_ENABLED = bool(CONFIG_STATE.hp_home_enabled)
    HP_HOME_LOW_PCT = float(CONFIG_STATE.hp_home_low_pct)
    HP_HOME_HIGH_PCT = float(CONFIG_STATE.hp_home_high_pct)
    HP_BUFF_TARGET_PCT = float(CONFIG_STATE.hp_buff_target_pct)
    HP_BUFF_COOLDOWN_S = float(CONFIG_STATE.hp_buff_cooldown_s)
    AUTO_LOAD_MAP_BY_ID = bool(CONFIG_STATE.auto_load_map_by_id)
    START_MAP_ID = int(CONFIG_STATE.start_map_id) if CONFIG_STATE.start_map_id is not None else None
    resurrect_points[:] = [tuple(p) for p in CONFIG_STATE.resurrect_points if isinstance(p, (list, tuple)) and len(p) == 2]
    player_click_point = tuple(CONFIG_STATE.player_click_point) if isinstance(CONFIG_STATE.player_click_point, (list, tuple)) and len(CONFIG_STATE.player_click_point) == 2 else None
    DARK_MODE = bool(CONFIG_STATE.dark_mode)
    HOTKEY_BINDINGS.clear()
    HOTKEY_BINDINGS.update(CONFIG_STATE.hotkey_bindings)

def _refresh_runtime_state_from_globals():
    with _RUNTIME_STATE_LOCK:
        RUNTIME_STATE.bot_running = bool(bot_running)
        RUNTIME_STATE.attack_active = bool(ATTACK_ACTIVE)
        RUNTIME_STATE.last_attack_time = float(last_attack_time)
        RUNTIME_STATE.last_attack_addr = last_attack_addr
        RUNTIME_STATE.no_click_until = float(NO_CLICK_UNTIL)
        RUNTIME_STATE.target_pid = int(TARGET_PID) if TARGET_PID is not None else None

def _apply_runtime_state_to_globals():
    global bot_running, ATTACK_ACTIVE, last_attack_time, last_attack_addr, NO_CLICK_UNTIL, TARGET_PID
    with _RUNTIME_STATE_LOCK:
        bot_running = bool(RUNTIME_STATE.bot_running)
        ATTACK_ACTIVE = bool(RUNTIME_STATE.attack_active)
        last_attack_time = float(RUNTIME_STATE.last_attack_time)
        last_attack_addr = RUNTIME_STATE.last_attack_addr
        NO_CLICK_UNTIL = float(RUNTIME_STATE.no_click_until)
        TARGET_PID = int(RUNTIME_STATE.target_pid) if RUNTIME_STATE.target_pid is not None else None

def _set_bot_running(active: bool):
    with _RUNTIME_STATE_LOCK:
        RUNTIME_STATE.bot_running = bool(active)
        _apply_runtime_state_to_globals()

def _as_home_pos(value: Any) -> Tuple[int, int]:
    if isinstance(value, (list, tuple)) and len(value) == 2:
        return (int(value[0]), int(value[1]))
    return CONFIG_STATE.home_pos

def _as_optional_int(value: Any) -> Optional[int]:
    if value is None:
        return None
    if isinstance(value, str) and not value.strip():
        return None
    try:
        return int(value)
    except Exception:
        return None

CFG_BOSS_AGGRO_TOGGLE = "BOSS_AGGRO_TOGGLE"
CFG_SIT_TIMER_SECONDS = "SIT_TIMER_SECONDS"
CFG_LAST_MOVED_TIMER_SECONDS = "LAST_MOVED_TIMER_SECONDS"
CFG_HOME_POS = "HOME_POS"
CFG_FLANK_RANGE = "FLANK_RANGE"
CFG_RUN_HOME_AFTER_KILL = "RUN_HOME_AFTER_KILL"
CFG_CLICKING_ENABLED = "CLICKING_ENABLED"
CFG_FAST_CLICK = "FAST_CLICK"
CFG_FAST_CLICK_BURST_COUNT = "FAST_CLICK_BURST_COUNT"
CFG_FAST_CLICK_GAP_S = "FAST_CLICK_GAP_S"
CFG_CLICK_BUFFS_ENABLED = "CLICK_BUFFS_ENABLED"
CFG_HP_BUFFS_ENABLED = "HP_BUFFS_ENABLED"
CFG_HP_BUFF_THRESHOLD_PCT = "HP_BUFF_THRESHOLD_PCT"
CFG_IGNORE_PROTECTION = "IGNORE_PROTECTION"
CFG_F5_TAP_COUNT = "F5_TAP_COUNT"
CFG_WANDER_TIMEOUT_S = "WANDER_TIMEOUT_S"
CFG_HOME_AFTER_KILLS_N = "HOME_AFTER_KILLS_N"
CFG_AVOID_OTHER_PLAYERS = "AVOID_OTHER_PLAYERS"
CFG_HP_HOME_ENABLED = "HP_HOME_ENABLED"
CFG_HP_HOME_LOW_PCT = "HP_HOME_LOW_PCT"
CFG_HP_HOME_HIGH_PCT = "HP_HOME_HIGH_PCT"
CFG_HP_BUFF_TARGET_PCT = "HP_BUFF_TARGET_PCT"
CFG_CLICK_BUFF_INTERVAL_S = "CLICK_BUFF_INTERVAL_S"
CFG_AUTO_LOAD_MAP_BY_ID = "AUTO_LOAD_MAP_BY_ID"
CFG_START_MAP_ID = "START_MAP_ID"

_CONFIG_FIELD_BINDINGS: Dict[str, Tuple[str, Any]] = {
    CFG_BOSS_AGGRO_TOGGLE: ("boss_aggro_toggle", bool),
    CFG_SIT_TIMER_SECONDS: ("sit_timer_seconds", int),
    CFG_LAST_MOVED_TIMER_SECONDS: ("last_moved_timer_seconds", int),
    CFG_HOME_POS: ("home_pos", _as_home_pos),
    CFG_FLANK_RANGE: ("flank_range", int),
    CFG_RUN_HOME_AFTER_KILL: ("run_home_after_kill", bool),
    CFG_CLICKING_ENABLED: ("clicking_enabled", bool),
    CFG_FAST_CLICK: ("fast_click", bool),
    CFG_FAST_CLICK_BURST_COUNT: ("fast_click_burst_count", int),
    CFG_FAST_CLICK_GAP_S: ("fast_click_gap_s", float),
    CFG_CLICK_BUFFS_ENABLED: ("click_buffs_enabled", bool),
    CFG_HP_BUFFS_ENABLED: ("hp_buffs_enabled", bool),
    CFG_HP_BUFF_THRESHOLD_PCT: ("hp_buff_threshold_pct", float),
    CFG_IGNORE_PROTECTION: ("ignore_protection", bool),
    CFG_F5_TAP_COUNT: ("f5_tap_count", int),
    CFG_WANDER_TIMEOUT_S: ("wander_timeout_s", float),
    CFG_HOME_AFTER_KILLS_N: ("home_after_kills_n", int),
    CFG_AVOID_OTHER_PLAYERS: ("avoid_other_players", bool),
    CFG_HP_HOME_ENABLED: ("hp_home_enabled", bool),
    CFG_HP_HOME_LOW_PCT: ("hp_home_low_pct", float),
    CFG_HP_HOME_HIGH_PCT: ("hp_home_high_pct", float),
    CFG_HP_BUFF_TARGET_PCT: ("hp_buff_target_pct", float),
    CFG_CLICK_BUFF_INTERVAL_S: ("click_buff_interval_s", float),
    CFG_AUTO_LOAD_MAP_BY_ID: ("auto_load_map_by_id", bool),
    CFG_START_MAP_ID: ("start_map_id", _as_optional_int),
}

def _set_config_value(global_name: str, value: Any):
    _refresh_config_state_from_globals()
    binding = _CONFIG_FIELD_BINDINGS.get(global_name)
    if not binding:
        raise KeyError(f"Unsupported config setting: {global_name}")
    field_name, caster = binding
    setattr(CONFIG_STATE, field_name, caster(value))
    _apply_config_state_to_globals()

def _read_setting(global_name: str, default: Any = None):
    _refresh_config_state_from_globals()
    binding = _CONFIG_FIELD_BINDINGS.get(global_name)
    if not binding:
        return default
    field_name, _ = binding
    return getattr(CONFIG_STATE, field_name, default)

def _config_sort_key(path: Path):
    name = str(path.name or "").strip().lower()
    starts_num = bool(name) and name[0].isdigit()
    return (starts_num, name)

def _config_dir_path() -> Path:
    path = CONFIG_DIR.resolve()
    path.mkdir(parents=True, exist_ok=True)
    return path

def _normalize_config_name(name: str) -> str:
    raw = str(name or "").strip()
    if not raw:
        return DEFAULT_CONFIG_FILE_NAME
    if not raw.lower().endswith(".json"):
        raw = f"{raw}.json"
    return raw

def _set_active_config_file(path: Optional[Union[str, Path]] = None) -> Path:
    global CONFIG_FILE
    cfg_dir = _config_dir_path()

    if path is None:
        candidate = Path(CONFIG_FILE)
        if not candidate.is_absolute():
            candidate = (cfg_dir / candidate)
    else:
        raw = Path(os.path.expandvars(os.path.expanduser(str(path))))
        candidate = raw if raw.is_absolute() else (cfg_dir / raw)

    candidate = candidate.resolve()
    if candidate.suffix.lower() != ".json":
        candidate = candidate.with_suffix(".json")

    # Never persist under legacy filename; normalize to current default name.
    if candidate.name.lower() == LEGACY_CONFIG_FILE_NAME.lower():
        candidate = candidate.with_name(DEFAULT_CONFIG_FILE_NAME)

    if candidate.parent.resolve() != cfg_dir:
        candidate = (cfg_dir / candidate.name).resolve()

    candidate.parent.mkdir(parents=True, exist_ok=True)
    CONFIG_FILE = str(candidate)
    return candidate

def _get_active_config_file() -> Path:
    return _set_active_config_file(None)

def _list_config_files() -> List[Path]:
    cfg_dir = _config_dir_path()
    files = sorted([p for p in cfg_dir.glob("*.json") if p.is_file()], key=_config_sort_key)
    active = _get_active_config_file()
    if active.is_file():
        try:
            if all(p.resolve() != active.resolve() for p in files):
                files.append(active)
        except Exception:
            files.append(active)
    return sorted(files, key=_config_sort_key)

def _apply_config_state_snapshot(snapshot: "ConfigState"):
    for field_name, value in vars(snapshot).items():
        setattr(CONFIG_STATE, field_name, copy.deepcopy(value))
    _apply_config_state_to_globals()

def _config_payload_from_state(state: "ConfigState") -> Dict[str, Any]:
    return {
        "BOSS_AGGRO_TOGGLE": bool(state.boss_aggro_toggle),
        "SIT_TIMER_SECONDS": int(state.sit_timer_seconds),
        "LAST_MOVED_TIMER_SECONDS": int(state.last_moved_timer_seconds),
        "MOB_ID_FILTERS": sorted(_coerce_int_set(state.mob_id_filters)),
        "HOME_POS": list(state.home_pos),
        "FLANK_RANGE": int(state.flank_range),
        "RUN_HOME_AFTER_KILL": bool(state.run_home_after_kill),
        "CLICKING_ENABLED": bool(state.clicking_enabled),
        "FAST_CLICK": bool(state.fast_click),
        "FAST_CLICK_BURST_COUNT": int(state.fast_click_burst_count),
        "FAST_CLICK_GAP_S": float(state.fast_click_gap_s),
        "CLICK_BUFFS_ENABLED": bool(state.click_buffs_enabled),
        "CLICK_BUFF_INTERVAL_S": float(state.click_buff_interval_s),
        "HP_BUFFS_ENABLED": bool(state.hp_buffs_enabled),
        "HP_BUFF_THRESHOLD_PCT": float(state.hp_buff_threshold_pct),
        "IGNORE_PROTECTION": bool(state.ignore_protection),
        "F5_TAP_COUNT": int(state.f5_tap_count),
        "WANDER_TIMEOUT_S": float(state.wander_timeout_s),
        "HOME_AFTER_KILLS_N": int(state.home_after_kills_n),
        "AVOID_OTHER_PLAYERS": bool(state.avoid_other_players),
        "HP_HOME_ENABLED": bool(state.hp_home_enabled),
        "HP_HOME_LOW_PCT": float(state.hp_home_low_pct),
        "HP_HOME_HIGH_PCT": float(state.hp_home_high_pct),
        "HP_BUFF_TARGET_PCT": float(state.hp_buff_target_pct),
        "HP_BUFF_COOLDOWN_S": float(state.hp_buff_cooldown_s),
        "AUTO_LOAD_MAP_BY_ID": bool(state.auto_load_map_by_id),
        "START_MAP_ID": state.start_map_id,
        "RESURRECT_POINTS": [list(p) for p in state.resurrect_points],
        "PLAYER_CLICK_POINT": list(state.player_click_point) if state.player_click_point else None,
        "DARK_MODE": bool(state.dark_mode),
        "HOTKEY_BINDINGS": dict(state.hotkey_bindings or {}),
    }

def _sync_config_state():
    _refresh_config_state_from_globals()

def _set_target_pid(pid: Optional[int]):
    with _RUNTIME_STATE_LOCK:
        RUNTIME_STATE.target_pid = int(pid) if pid is not None else None
        _apply_runtime_state_to_globals()

def _set_attack_state(active: bool, target_addr: Optional[str] = None, attack_time: Optional[float] = None):
    with _RUNTIME_STATE_LOCK:
        RUNTIME_STATE.attack_active = bool(active)
        if active:
            ts = time.time() if attack_time is None else float(attack_time)
            RUNTIME_STATE.last_attack_time = ts
            if target_addr is not None:
                RUNTIME_STATE.last_attack_addr = target_addr
        _apply_runtime_state_to_globals()

def _extend_no_click(seconds: float):
    with _RUNTIME_STATE_LOCK:
        deadline = time.monotonic() + float(seconds)
        if deadline > RUNTIME_STATE.no_click_until:
            RUNTIME_STATE.no_click_until = deadline
            _apply_runtime_state_to_globals()

def _warn_throttled(key: str, message: str, interval_s: float = 5.0):
    """Best-effort warning logger with per-key rate limiting."""
    now = time.monotonic()
    last = _WARN_THROTTLE.get(key, 0.0)
    if (now - last) >= float(interval_s):
        _WARN_THROTTLE[key] = now
        _log_warn(message)

def _log_debug(*args, **kwargs):
    if LOG_VERBOSITY >= 2:
        _RAW_PRINT(*args, **kwargs)

def _log_info(*args, **kwargs):
    if LOG_VERBOSITY >= 1:
        _RAW_PRINT(*args, **kwargs)

def _log_warn(*args, **kwargs):
    _RAW_PRINT(*args, **kwargs)

def _log_error(*args, **kwargs):
    _RAW_PRINT(*args, **kwargs)

VK_MAPPING: Dict[str, int] = {
    "left": 0x25, "up": 0x26, "right": 0x27, "down": 0x28,
    "enter": 0x0D, "esc": 0x1B, "space": 0x20, "ctrl": 0x11, "alt": 0x12, "shift": 0x10,
    "f1": 0x70, "f2": 0x71, "f3": 0x72, "f4": 0x73, "f5": 0x74, "f6": 0x75,
    "f7": 0x76, "f8": 0x77, "f9": 0x78, "f10": 0x79, "f11": 0x7A, "f12": 0x7B,
    "0": 0x30, "1": 0x31, "2": 0x32, "3": 0x33, "4": 0x34,
    "5": 0x35, "6": 0x36, "7": 0x37, "8": 0x38, "9": 0x39,
    "a": 0x41, "b": 0x42, "c": 0x43, "d": 0x44, "e": 0x45, "f": 0x46, "g": 0x47,
    "h": 0x48, "i": 0x49, "j": 0x4A, "k": 0x4B, "l": 0x4C, "m": 0x4D, "n": 0x4E,
    "o": 0x4F, "p": 0x50, "q": 0x51, "r": 0x52, "s": 0x53, "t": 0x54, "u": 0x55,
    "v": 0x56, "w": 0x57, "x": 0x58, "y": 0x59, "z": 0x5A,
}

_BG_INPUT_LOCK = threading.RLock()
_BG_INPUT = None
_BG_PATCHED = False
_BG_ORIG_FUNCS: Dict[str, Any] = {}
_EO_HWND_CACHE = 0

class _EmbeddedFridaInput:
    """18.6-style background input transport using input_spoofer.js."""
    def __init__(self):
        self.session = None
        self.script = None
        self.hwnd = 0
        self.attached = False
        # Match 18.6 default pacing to prevent overdriving turn/ctrl transitions.
        self.PAUSE = 0.1
        self._post_lock = threading.Lock()
        self._hb_stop = threading.Event()
        self._hb_thread = None

    def _script_path(self) -> Optional[Path]:
        base = _app_base_dir()
        resource_base = _resource_base_dir()
        candidates = [
            base / "input_spoofer.js",
            resource_base / "input_spoofer.js",
            Path.cwd() / "input_spoofer.js",
            base / "bot-v18.6-eco" / "input_spoofer.js",
            resource_base / "bot-v18.6-eco" / "input_spoofer.js",
            Path.cwd() / "bot-v18.6-eco" / "input_spoofer.js",
        ]
        for p in candidates:
            try:
                if p.is_file():
                    return p
            except Exception:
                pass
        return None

    def _find_hwnd_by_pid(self, pid: int) -> int:
        if not (win32gui and win32process):
            return 0
        found: List[int] = []
        def _enum(hwnd, _):
            try:
                if not win32gui.IsWindowVisible(hwnd):
                    return True
                _, p = win32process.GetWindowThreadProcessId(hwnd)
                if int(p) == int(pid):
                    found.append(int(hwnd))
            except Exception:
                pass
            return True
        try:
            win32gui.EnumWindows(_enum, None)
        except Exception:
            return 0
        return int(found[0]) if found else 0

    def _screen_to_client(self, x: int, y: int) -> Tuple[int, int]:
        if not (self.hwnd and win32gui):
            return int(x), int(y)
        try:
            cx, cy = win32gui.ScreenToClient(int(self.hwnd), (int(x), int(y)))
            return int(cx), int(cy)
        except Exception:
            return int(x), int(y)

    def _on_message(self, message, _data):
        mtype = message.get("type")
        if mtype == "error":
            _log_warn(f"[INPUT] Frida script error: {message.get('description') or message.get('stack')}")
            return
        if mtype != "send":
            return
        payload = message.get("payload")
        if isinstance(payload, dict):
            msg = str(payload.get("message", ""))
            if "Found Game HWND" in msg:
                m = re.search(r"(0x[0-9A-Fa-f]+|\d+)\s*$", msg)
                if m:
                    try:
                        self.hwnd = int(m.group(1), 0)
                    except Exception:
                        pass

    def _post(self, payload: Dict[str, Any]) -> bool:
        if not self.attached or self.script is None:
            return False
        try:
            with self._post_lock:
                self.script.post(payload)
            return True
        except Exception:
            return False

    def _heartbeat_loop(self):
        while self.attached and not self._hb_stop.is_set():
            try:
                self._post({"cmd": "heartbeat"})
            except Exception:
                pass
            self._hb_stop.wait(1.0)

    def connect(self, pid: int) -> bool:
        try:
            script_path = self._script_path()
            if script_path is None:
                _log_warn("[INPUT] input_spoofer.js not found; background input disabled.")
                return False
            source = script_path.read_text(encoding="utf-8", errors="ignore")
            self.session = frida.attach(int(pid))
            self.script = self.session.create_script(source)
            self.script.on("message", self._on_message)
            self.script.load()
            self.attached = True
            self.hwnd = self._find_hwnd_by_pid(int(pid))
            if self.hwnd:
                self._post({"cmd": "set_hwnd", "hwnd": hex(int(self.hwnd))})
            self._post({"cmd": "force_focus"})
            self._post({"cmd": "set_sleep_cap", "val": 10})
            self._hb_stop.clear()
            self._hb_thread = threading.Thread(target=self._heartbeat_loop, daemon=True)
            self._hb_thread.start()
            return True
        except Exception as e:
            self.attached = False
            _log_warn(f"[INPUT] Background attach failed: {e}")
            return False

    def set_sleep_cap(self, ms):
        if self.attached:
            self._post({"cmd": "set_sleep_cap", "val": int(ms)})

    def _vk(self, key) -> int:
        if isinstance(key, int):
            return int(key)
        return int(VK_MAPPING.get(str(key).lower(), 0))

    def _maybe_pause(self):
        if self.PAUSE and self.PAUSE > 0:
            time.sleep(float(self.PAUSE))

    def keyDown(self, key, *_, **__):
        vk = self._vk(key)
        if vk:
            self._post({"cmd": "key_event", "vk": vk, "down": True})
        self._maybe_pause()

    def keyUp(self, key, *_, **__):
        vk = self._vk(key)
        if vk:
            self._post({"cmd": "key_event", "vk": vk, "down": False})
        self._maybe_pause()

    def press(self, key, presses=1, interval=0.0, *_, **__):
        vk = self._vk(key)
        if not vk:
            return
        n = max(1, int(presses))
        inter = max(0.0, float(interval))
        self._post({"cmd": "press_key", "vk": vk, "count": n, "interval": int(inter * 1000.0)})
        time.sleep((n * 0.05) + (n * inter))

    def click(self, x=None, y=None, clicks=1, interval=0.0, button="left", *_, **__):
        if x is None or y is None:
            return
        cx, cy = self._screen_to_client(int(x), int(y))
        n = max(1, int(clicks))
        inter = max(0.0, float(interval))
        self._post({"cmd": "click_mouse", "x": cx, "y": cy, "button": str(button), "count": n})
        time.sleep((n * 0.05) + (n * 0.05) + (n * inter))

    def click_client(self, x=None, y=None, clicks=1, interval=0.0, button="left"):
        """Click using client-relative coordinates directly (no coordinate conversion)."""
        if x is None or y is None:
            return
        n = max(1, int(clicks))
        inter = max(0.0, float(interval))
        self._post({"cmd": "click_mouse", "x": int(x), "y": int(y), "button": str(button), "count": n})
        time.sleep((n * 0.05) + (n * 0.05) + (n * inter))

    def moveTo(self, x, y, duration=0, *_, **__):
        if win32con is None:
            return
        cx, cy = self._screen_to_client(int(x), int(y))
        self._post({"cmd": "mouse_event", "msg": int(win32con.WM_MOUSEMOVE), "x": cx, "y": cy})
        self._maybe_pause()

    def mouseDown(self, x=None, y=None, button="left", *_, **__):
        if win32con is None or x is None or y is None:
            return
        cx, cy = self._screen_to_client(int(x), int(y))
        msg = int(win32con.WM_LBUTTONDOWN if str(button).lower() == "left" else win32con.WM_RBUTTONDOWN)
        self._post({"cmd": "mouse_event", "msg": msg, "x": cx, "y": cy})
        self._maybe_pause()

    def mouseUp(self, x=None, y=None, button="left", *_, **__):
        if win32con is None or x is None or y is None:
            return
        cx, cy = self._screen_to_client(int(x), int(y))
        msg = int(win32con.WM_LBUTTONUP if str(button).lower() == "left" else win32con.WM_RBUTTONUP)
        self._post({"cmd": "mouse_event", "msg": msg, "x": cx, "y": cy})
        self._maybe_pause()

    def cleanup(self):
        if not self.attached:
            return
        try:
            self._hb_stop.set()
            self._post({"cmd": "cleanup"})
            time.sleep(0.20)
        except Exception:
            pass
        try:
            if self.session is not None:
                self.session.detach()
        except Exception:
            pass
        self.attached = False
        self.script = None
        self.session = None
        self.hwnd = 0

def _install_background_input_hooks(backend: _EmbeddedFridaInput):
    global _BG_PATCHED
    if _BG_PATCHED:
        return
    _BG_ORIG_FUNCS["pydirectinput.keyDown"] = getattr(pydirectinput, "keyDown", None)
    _BG_ORIG_FUNCS["pydirectinput.keyUp"] = getattr(pydirectinput, "keyUp", None)
    _BG_ORIG_FUNCS["pydirectinput.press"] = getattr(pydirectinput, "press", None)
    _BG_ORIG_FUNCS["pydirectinput.click"] = getattr(pydirectinput, "click", None)
    _BG_ORIG_FUNCS["pydirectinput.moveTo"] = getattr(pydirectinput, "moveTo", None)
    _BG_ORIG_FUNCS["pydirectinput.mouseDown"] = getattr(pydirectinput, "mouseDown", None)
    _BG_ORIG_FUNCS["pydirectinput.mouseUp"] = getattr(pydirectinput, "mouseUp", None)
    _BG_ORIG_FUNCS["pyautogui.click"] = getattr(pyautogui, "click", None)
    _BG_ORIG_FUNCS["pyautogui.moveTo"] = getattr(pyautogui, "moveTo", None)
    _BG_ORIG_FUNCS["pyautogui.keyDown"] = getattr(pyautogui, "keyDown", None)
    _BG_ORIG_FUNCS["pyautogui.keyUp"] = getattr(pyautogui, "keyUp", None)
    _BG_ORIG_FUNCS["pyautogui.press"] = getattr(pyautogui, "press", None)
    _BG_ORIG_FUNCS["pyautogui.mouseDown"] = getattr(pyautogui, "mouseDown", None)
    _BG_ORIG_FUNCS["pyautogui.mouseUp"] = getattr(pyautogui, "mouseUp", None)

    pydirectinput.keyDown = backend.keyDown
    pydirectinput.keyUp = backend.keyUp
    pydirectinput.press = backend.press
    pydirectinput.click = backend.click
    pydirectinput.moveTo = backend.moveTo
    pydirectinput.mouseDown = backend.mouseDown
    pydirectinput.mouseUp = backend.mouseUp
    pyautogui.click = backend.click
    pyautogui.moveTo = backend.moveTo
    pyautogui.keyDown = backend.keyDown
    pyautogui.keyUp = backend.keyUp
    pyautogui.press = backend.press
    pyautogui.mouseDown = backend.mouseDown
    pyautogui.mouseUp = backend.mouseUp
    _BG_PATCHED = True

def _restore_background_input_hooks():
    global _BG_PATCHED
    if not _BG_PATCHED:
        return
    for name, fn in _BG_ORIG_FUNCS.items():
        if fn is None:
            continue
        obj_name, attr = name.split(".", 1)
        obj = pydirectinput if obj_name == "pydirectinput" else pyautogui
        try:
            setattr(obj, attr, fn)
        except Exception:
            pass
    _BG_PATCHED = False

def initialize_background_input(pid: Optional[int] = None) -> bool:
    global _BG_INPUT
    if pid is None:
        pid = TARGET_PID
    if not pid:
        _log_warn("[INPUT] TARGET_PID not set. Background input disabled.")
        return False
    with _BG_INPUT_LOCK:
        if _BG_INPUT is not None and _BG_INPUT.attached:
            return True
        backend = _EmbeddedFridaInput()
        if not backend.connect(int(pid)):
            _BG_INPUT = None
            return False
        _BG_INPUT = backend
        _install_background_input_hooks(backend)
    _log_info("[INPUT] Using embedded v18.6 spoofer backend (monofile mode).")
    _log_info(f"[INPUT] Background input enabled for PID {int(pid)}")
    return True

def shutdown_background_input():
    global _BG_INPUT
    with _BG_INPUT_LOCK:
        backend = _BG_INPUT
        _BG_INPUT = None
    try:
        if backend is not None:
            backend.cleanup()
    finally:
        _restore_background_input_hooks()

def _background_input_ready() -> bool:
    with _BG_INPUT_LOCK:
        return bool(_BG_PATCHED and _BG_INPUT is not None and getattr(_BG_INPUT, "attached", False))

def _require_background_input(action: str) -> bool:
    if _background_input_ready():
        return True
    _warn_throttled(
        f"input:bg_missing:{action}",
        f"[INPUT] Dropped {action}; background backend not ready.",
        interval_s=1.5,
    )
    return False

_refresh_config_state_from_globals()
_refresh_runtime_state_from_globals()
_INITIAL_CONFIG_STATE = copy.deepcopy(CONFIG_STATE)

STAT_OFFSETS = {
        'exp':      0x000,   # at exp_base itself
        'weight':  -0x008,   # 0x0293F404
        'level':    0x008,   # 0x0293F414
        'tnl':      0x010,   # 0x0293F41C
        'eon':      0x034,   # 0x0293F440
        'vit':      0x188,   # 0x0293F594
        'dex':      0x184,   # 0x0293F590
        'acc':      0x180,   # 0x0293F58C
        'def':      0x17C,   # 0x0293F588
        'pwr':      0x178,   # 0x0293F584
        'crit':     0x174,   # 0x0293F580
        'armor':    0x170,   # 0x0293F57C
        'eva':      0x16C,   # 0x0293F578
        'hit_rate': 0x168,   # 0x0293F574
        'max_dmg':  0x164,   # 0x0293F570
        'min_dmg':  0x160,   # 0x0293F56C
        'aura':     0x18C,   # 0x0293F598
        'max_hp':   0x358,   # 0x0293F764
        'max_mana': 0x4F0,   # 0x0293F8FC
    }

def save_settings(config_path: Optional[Union[str, Path]] = None):
    """Save current settings to the active config file (or provided config file)."""
    try:
        target = _set_active_config_file(config_path)
        _refresh_config_state_from_globals()
        payload = _config_payload_from_state(CONFIG_STATE)
        with target.open("w", encoding="utf-8") as f:
            json.dump(payload, f, indent=2)
        _log_info(f"[CONFIG] Settings saved to {target}")
    except Exception as e:
        _log_warn(f"[CONFIG] Failed to save settings: {e}")

def load_settings(config_path: Optional[Union[str, Path]] = None):
    try:
        target = _set_active_config_file(config_path)
        if target.is_file():
            with target.open("r", encoding="utf-8") as f:
                config = json.load(f)

            CONFIG_STATE.boss_aggro_toggle = bool(config.get("BOSS_AGGRO_TOGGLE", CONFIG_STATE.boss_aggro_toggle))
            CONFIG_STATE.sit_timer_seconds = int(config.get("SIT_TIMER_SECONDS", CONFIG_STATE.sit_timer_seconds))
            CONFIG_STATE.last_moved_timer_seconds = int(config.get("LAST_MOVED_TIMER_SECONDS", CONFIG_STATE.last_moved_timer_seconds))
            CONFIG_STATE.mob_id_filters = _coerce_int_set(config.get("MOB_ID_FILTERS"), fallback=CONFIG_STATE.mob_id_filters)
            CONFIG_STATE.home_pos = tuple(config.get("HOME_POS", list(CONFIG_STATE.home_pos)))
            CONFIG_STATE.flank_range = int(config.get("FLANK_RANGE", CONFIG_STATE.flank_range))
            CONFIG_STATE.run_home_after_kill = bool(config.get("RUN_HOME_AFTER_KILL", CONFIG_STATE.run_home_after_kill))
            CONFIG_STATE.clicking_enabled = bool(config.get("CLICKING_ENABLED", CONFIG_STATE.clicking_enabled))
            CONFIG_STATE.fast_click = bool(config.get("FAST_CLICK", CONFIG_STATE.fast_click))
            CONFIG_STATE.fast_click_burst_count = int(config.get("FAST_CLICK_BURST_COUNT", CONFIG_STATE.fast_click_burst_count))
            CONFIG_STATE.fast_click_gap_s = float(config.get("FAST_CLICK_GAP_S", CONFIG_STATE.fast_click_gap_s))
            CONFIG_STATE.f5_tap_count = int(config.get("F5_TAP_COUNT", CONFIG_STATE.f5_tap_count))
            CONFIG_STATE.wander_timeout_s = float(config.get("WANDER_TIMEOUT_S", CONFIG_STATE.wander_timeout_s))
            CONFIG_STATE.home_after_kills_n = max(1, int(config.get("HOME_AFTER_KILLS_N", CONFIG_STATE.home_after_kills_n)))
            CONFIG_STATE.avoid_other_players = bool(config.get("AVOID_OTHER_PLAYERS", CONFIG_STATE.avoid_other_players))
            CONFIG_STATE.hp_home_enabled = bool(config.get("HP_HOME_ENABLED", CONFIG_STATE.hp_home_enabled))
            CONFIG_STATE.hp_home_low_pct = float(config.get("HP_HOME_LOW_PCT", CONFIG_STATE.hp_home_low_pct))
            CONFIG_STATE.hp_home_high_pct = float(config.get("HP_HOME_HIGH_PCT", CONFIG_STATE.hp_home_high_pct))
            CONFIG_STATE.ignore_protection = bool(config.get("IGNORE_PROTECTION", CONFIG_STATE.ignore_protection))
            CONFIG_STATE.click_buffs_enabled = bool(config.get("CLICK_BUFFS_ENABLED", CONFIG_STATE.click_buffs_enabled))
            CONFIG_STATE.click_buff_interval_s = float(config.get("CLICK_BUFF_INTERVAL_S", CONFIG_STATE.click_buff_interval_s))
            CONFIG_STATE.hp_buffs_enabled = bool(config.get("HP_BUFFS_ENABLED", CONFIG_STATE.hp_buffs_enabled))
            CONFIG_STATE.hp_buff_threshold_pct = float(config.get("HP_BUFF_THRESHOLD_PCT", CONFIG_STATE.hp_buff_threshold_pct))
            CONFIG_STATE.hp_buff_target_pct = float(config.get("HP_BUFF_TARGET_PCT", CONFIG_STATE.hp_buff_target_pct))
            CONFIG_STATE.hp_buff_cooldown_s = float(config.get("HP_BUFF_COOLDOWN_S", CONFIG_STATE.hp_buff_cooldown_s))
            CONFIG_STATE.auto_load_map_by_id = bool(config.get("AUTO_LOAD_MAP_BY_ID", CONFIG_STATE.auto_load_map_by_id))
            CONFIG_STATE.start_map_id = _as_optional_int(config.get("START_MAP_ID", CONFIG_STATE.start_map_id))

            saved_points = config.get("RESURRECT_POINTS", [])
            if isinstance(saved_points, list):
                CONFIG_STATE.resurrect_points = [tuple(p) for p in saved_points if isinstance(p, (list, tuple)) and len(p) == 2]

            saved_player_point = config.get("PLAYER_CLICK_POINT")
            CONFIG_STATE.player_click_point = tuple(saved_player_point) if isinstance(saved_player_point, (list, tuple)) and len(saved_player_point) == 2 else None
            legacy_mode = str(config.get("CLICK_POINTS_MODE", "client")).lower()
            if legacy_mode != "client":
                CONFIG_STATE.resurrect_points = []
                CONFIG_STATE.player_click_point = None
                _log_warn("[CONFIG] Legacy click-point mode detected and cleared. Re-record click points (client mode).")
            CONFIG_STATE.dark_mode = True

            loaded_hotkeys = config.get("HOTKEY_BINDINGS", {})
            if isinstance(loaded_hotkeys, dict):
                merged_hotkeys = HOTKEY_BINDINGS.copy()
                merged_hotkeys.update({str(k): str(v) for k, v in loaded_hotkeys.items()})
                CONFIG_STATE.hotkey_bindings = merged_hotkeys
            else:
                CONFIG_STATE.hotkey_bindings = HOTKEY_BINDINGS.copy()

            _apply_config_state_to_globals()
            _log_info(f"[CONFIG] Settings loaded from {target}")
        else:
            if _INITIAL_CONFIG_STATE is not None:
                _apply_config_state_snapshot(_INITIAL_CONFIG_STATE)
            else:
                _refresh_config_state_from_globals()
            save_settings(str(target))
            _log_info(f"[CONFIG] No config file found at {target}; created default config")
    except Exception as e:
        _log_warn(f"[CONFIG] Failed to load settings: {e}")

def _get_foreground_pid():
    """Return PID of the currently focused (foreground) window."""
    user32 = ctypes.windll.user32
    hwnd = user32.GetForegroundWindow()
    if not hwnd:
        return None
    pid = wintypes.DWORD()
    user32.GetWindowThreadProcessId(hwnd, ctypes.byref(pid))
    return int(pid.value) if pid.value else None

def _hwnd_pid(hwnd: int) -> int:
    try:
        user32 = ctypes.windll.user32
        pid = wintypes.DWORD()
        user32.GetWindowThreadProcessId(int(hwnd), ctypes.byref(pid))
        return int(pid.value or 0)
    except Exception:
        return 0

def _is_hwnd_alive(hwnd: int) -> bool:
    try:
        return bool(int(ctypes.windll.user32.IsWindow(int(hwnd))))
    except Exception:
        return False

def _is_hwnd_for_target(hwnd: int) -> bool:
    if not hwnd:
        return False
    if not _is_hwnd_alive(int(hwnd)):
        return False
    if TARGET_PID:
        return _hwnd_pid(int(hwnd)) == int(TARGET_PID)
    return True

def _window_from_point(x: int, y: int) -> int:
    try:
        user32 = ctypes.windll.user32
        pt = wintypes.POINT(int(x), int(y))
        hwnd = int(user32.WindowFromPoint(pt) or 0)
        if not hwnd:
            return 0
        try:
            GA_ROOT = 2
            root = int(user32.GetAncestor(int(hwnd), GA_ROOT) or 0)
            if root:
                hwnd = root
        except Exception:
            pass
        return hwnd
    except Exception:
        return 0

def _enum_hwnds_for_pid(target_pid: int) -> List[int]:
    out: List[int] = []
    try:
        user32 = ctypes.windll.user32
        EnumProc = ctypes.WINFUNCTYPE(ctypes.c_bool, wintypes.HWND, wintypes.LPARAM)
        pid_dw = wintypes.DWORD()

        def _cb(hwnd, _lparam):
            try:
                user32.GetWindowThreadProcessId(hwnd, ctypes.byref(pid_dw))
                if int(pid_dw.value or 0) == int(target_pid):
                    out.append(int(hwnd))
            except Exception:
                pass
            return True

        user32.EnumWindows(EnumProc(_cb), 0)
    except Exception:
        pass
    return out

def _score_hwnd(hwnd: int) -> Tuple[int, int]:
    """Return (score, area) for selecting best top-level candidate."""
    score = 0
    area = 0
    try:
        user32 = ctypes.windll.user32
        try:
            if int(user32.IsWindowVisible(int(hwnd))):
                score += 2
        except Exception:
            pass
        try:
            GW_OWNER = 4
            owner = int(user32.GetWindow(int(hwnd), GW_OWNER) or 0)
            if owner:
                score -= 3
        except Exception:
            pass
        try:
            rect = wintypes.RECT()
            if int(user32.GetWindowRect(int(hwnd), ctypes.byref(rect))):
                w = max(0, int(rect.right) - int(rect.left))
                h = max(0, int(rect.bottom) - int(rect.top))
                area = w * h
                if area > 0:
                    score += 2
        except Exception:
            pass
    except Exception:
        pass
    return score, area

def _get_target_hwnd() -> int:
    """Best-effort Endless window handle for coordinate conversion."""
    global _EO_HWND_CACHE

    if _is_hwnd_for_target(_EO_HWND_CACHE):
        return int(_EO_HWND_CACHE)

    try:
        with _BG_INPUT_LOCK:
            if _BG_INPUT is not None and getattr(_BG_INPUT, "attached", False):
                hwnd = int(getattr(_BG_INPUT, "hwnd", 0) or 0)
                if _is_hwnd_for_target(hwnd):
                    _EO_HWND_CACHE = int(hwnd)
                    return hwnd
    except Exception:
        pass

    # PID-based enumeration (ctypes, no pywin32 dependency).
    try:
        if TARGET_PID:
            candidates = _enum_hwnds_for_pid(int(TARGET_PID))
            if candidates:
                ranked = sorted(candidates, key=lambda h: _score_hwnd(h), reverse=True)
                if ranked:
                    _EO_HWND_CACHE = int(ranked[0])
                    return int(ranked[0])
    except Exception:
        pass

    # Foreground fallback if it belongs to selected target PID.
    try:
        user32 = ctypes.windll.user32
        fg = int(user32.GetForegroundWindow() or 0)
        if fg and TARGET_PID and _hwnd_pid(fg) == int(TARGET_PID):
            _EO_HWND_CACHE = int(fg)
            return fg
    except Exception:
        pass

    # Last fallback: pyautogui/pygetwindow handle lookup by title.
    try:
        wins = pyautogui.getWindowsWithTitle("Endless")
        for w in wins:
            for attr in ("_hWnd", "hWnd", "_hwnd", "hwnd"):
                hwnd = getattr(w, attr, None)
                if _is_hwnd_for_target(int(hwnd or 0)):
                    _EO_HWND_CACHE = int(hwnd)
                    return int(hwnd)
    except Exception:
        pass

    return 0

def _screen_to_client_xy(x: int, y: int, hwnd: Optional[int] = None) -> Optional[Tuple[int, int]]:
    if not hwnd:
        hwnd = _get_target_hwnd()
    if not hwnd:
        return None
    try:
        user32 = ctypes.windll.user32
        pt = wintypes.POINT(int(x), int(y))
        ok = int(user32.ScreenToClient(int(hwnd), ctypes.byref(pt)))
        if not ok:
            return None
        return int(pt.x), int(pt.y)
    except Exception:
        return None

def _client_to_screen_xy(x: int, y: int, hwnd: Optional[int] = None) -> Optional[Tuple[int, int]]:
    if not hwnd:
        hwnd = _get_target_hwnd()
    if not hwnd:
        return None
    try:
        user32 = ctypes.windll.user32
        pt = wintypes.POINT(int(x), int(y))
        ok = int(user32.ClientToScreen(int(hwnd), ctypes.byref(pt)))
        if not ok:
            return None
        return int(pt.x), int(pt.y)
    except Exception:
        return None

def _resolve_click_xy(point: Any) -> Optional[Tuple[int, int]]:
    """Resolve client-relative click point to screen coords for backend click dispatch."""
    global _EO_HWND_CACHE
    if not (isinstance(point, (tuple, list)) and len(point) == 2):
        return None
    try:
        x, y = int(point[0]), int(point[1])
    except Exception:
        return None

    # Try cached/attached/discovered hwnd candidates until one converts successfully.
    tried: Set[int] = set()
    candidates: List[int] = []

    if _is_hwnd_for_target(_EO_HWND_CACHE):
        candidates.append(int(_EO_HWND_CACHE))

    try:
        with _BG_INPUT_LOCK:
            if _BG_INPUT is not None and getattr(_BG_INPUT, "attached", False):
                bh = int(getattr(_BG_INPUT, "hwnd", 0) or 0)
                if _is_hwnd_for_target(bh):
                    candidates.append(bh)
    except Exception:
        pass

    dh = _get_target_hwnd()
    if _is_hwnd_for_target(dh):
        candidates.append(int(dh))

    if TARGET_PID:
        try:
            candidates.extend([int(h) for h in _enum_hwnds_for_pid(int(TARGET_PID)) if _is_hwnd_for_target(int(h))])
        except Exception:
            pass

    for hwnd in candidates:
        if hwnd in tried:
            continue
        tried.add(hwnd)
        xy = _client_to_screen_xy(x, y, hwnd=hwnd)
        if xy is not None:
            _EO_HWND_CACHE = int(hwnd)
            return xy

    _warn_throttled("click:resolve:no_hwnd", "[CLICK] Cannot resolve client click point; EO window handle unavailable.", interval_s=2.0)
    return None

def _resolve_client_point(point: Any) -> Optional[Tuple[int, int]]:
    """Validate and normalize stored client-relative click point."""
    if not (isinstance(point, (tuple, list)) and len(point) == 2):
        return None
    try:
        return int(point[0]), int(point[1])
    except Exception:
        return None

def _enumerate_endless_processes():
    """Return list of dicts: [{'pid': int, 'name': str}, ...] for Endless.exe."""
    try:
        dev = frida.get_local_device()
        procs = dev.enumerate_processes()
        matches = [p for p in procs if (p.name or "").lower() == "endless.exe"]
        return [{"pid": int(p.pid), "name": p.name} for p in matches]
    except Exception as e:
        _log_warn(f"[BOOT] Could not enumerate processes via Frida: {e}")
        return []

def _wait_for_foreground_endless_pid(pids: Set[int], timeout_s: float = 15.0, poll_s: float = 0.05):
    """Wait until the foreground window belongs to one of `pids`."""
    start = time.time()
    last = None
    while (time.time() - start) < timeout_s:
        pid = _get_foreground_pid()
        if pid != last:
            last = pid
        if pid in pids:
            return pid
        time.sleep(poll_s)
    return None

def _wait_for_global_hotkey_pynput(hotkey=keyboard.Key.f12, timeout_s=15.0) -> bool:
    """
    Wait for a global hotkey (default F12) using pynput.
    Returns True if pressed before timeout, else False.
    """
    ev = threading.Event()

    def on_press(key):
        try:
            if key == hotkey:
                ev.set()
                return False  # stop listener
        except Exception:
            pass

    listener = keyboard.Listener(on_press=on_press)
    listener.start()
    try:
        ev.wait(timeout_s)
        return ev.is_set()
    finally:
        try:
            listener.stop()
        except Exception:
            pass

def select_target_pid_preboot():
    """
    If more than one Endless.exe is running:
      - Ask user to click the desired Endless window
      - Press F12 to capture that window PID (avoids messagebox stealing focus)
    Sets runtime TARGET_PID.
    """
    matches = _enumerate_endless_processes()
    if len(matches) == 0:
        raise RuntimeError("No Endless.exe process found.")
    if len(matches) == 1:
        _set_target_pid(matches[0]["pid"])
        _log_info(f"[BOOT] Single Endless.exe detected. TARGET_PID={TARGET_PID}")
        return

    pids = {m["pid"] for m in matches}
    _log_info(f"[BOOT] Multiple Endless.exe detected: {sorted(pids)}")

    temp_root = None
    try:
        temp_root = tk.Tk()
        temp_root.withdraw()
    except Exception:
        temp_root = None

    selected = None

    for attempt in range(3):
        messagebox.showinfo(
            "Select Endless Client",
            "Multiple Endless Online clients detected.\n\n"
            "After closing this box:\n"
            "1) Click the Endless window you want to attach to (bring it to front)\n"
            "2) (Optional) Press F12\n\n"
            f"Detected Endless PIDs: {sorted(pids)}\n"
            f"(Attempt {attempt+1}/3)"
        )

        focused = _wait_for_foreground_endless_pid(pids, timeout_s=8.0)
        if focused:
            selected = focused
            break

        pressed = _wait_for_global_hotkey_pynput(keyboard.Key.f12, timeout_s=15.0)
        if not pressed:
            _log_warn(f"[BOOT] Timed out waiting for F12 (attempt {attempt+1}/3)")
            continue

        pid = _get_foreground_pid()
        if pid in pids:
            selected = pid
            break

        _log_info(f"[BOOT] Foreground PID {pid} is not one of Endless PIDs {sorted(pids)} (attempt {attempt+1}/3)")
    if selected is None:
        pid_str = simpledialog.askstring(
            "Select Endless PID",
            "Click selection failed.\n\nEnter the PID to attach to:\n"
            f"Detected Endless PIDs: {sorted(pids)}"
        )
        try:
            pid_val = int(pid_str) if pid_str else None
        except ValueError:
            pid_val = None

        if pid_val in pids:
            selected = pid_val

    if temp_root is not None:
        try:
            temp_root.destroy()
        except Exception:
            pass

    if selected is None:
        raise RuntimeError(f"Could not select a valid Endless.exe PID. Detected: {sorted(pids)}")

    _set_target_pid(selected)
    _log_info(f"[BOOT] Selected TARGET_PID={TARGET_PID}")

def frida_attach_target():
    """Attach Frida to selected PID if set, else fallback to process name."""
    if TARGET_PID:
        return frida.attach(int(TARGET_PID))
    return frida.attach("Endless.exe")

def _load_frida_script(session, script_code: str, on_message_cb, *, label: str, keepalive: bool = True):
    """Create, bind, and load a Frida script with optional keepalive tracking."""
    script = session.create_script(script_code)
    script.on("message", on_message_cb)
    script.load()
    if keepalive:
        with _FRIDA_HOOKS_LOCK:
            _FRIDA_HOOKS.append((label, session, script))
    return script

def _detach_tracked_frida_hooks():
    """Detach all tracked long-lived Frida sessions once."""
    with _FRIDA_HOOKS_LOCK:
        hooks = list(_FRIDA_HOOKS)
        _FRIDA_HOOKS.clear()

    detached = set()
    for label, session, _script in reversed(hooks):
        sid = id(session)
        if sid in detached:
            continue
        try:
            session.detach()
            _log_info(f"[FRIDA] Detached session: {label}")
        except Exception as e:
            _log_warn(f"[FRIDA] Detach failed ({label}): {e}")
        detached.add(sid)

STEP_TIMEOUT_S = 0.30   # Time per tile movement (increased to account for coordinate update lag)
STEP_POLL_S    = 0.010  # Poll faster for quicker detection (10ms, 100 Hz)

class Target(Protocol):
    def get_xy(self) -> Optional[Optional[Tuple[int, int]]]: ...
    def is_valid(self) -> bool: ...
    def on_arrival(self) -> bool: ...

def _live_xy() -> Optional[Optional[Tuple[int, int]]]:
    x, y = _get_xy_safe()
    if x is None or y is None: return None
    return (int(x), int(y))

def _path_or_none(start: Optional[Tuple[int, int]], goal: Optional[Tuple[int, int]], walkable: set):
    path = astar_pathfinding(start, goal, walkable)
    if not path or len(path) < 2: return None
    return path

def _direction_key(from_xy: Tuple[int, int], to_xy: Tuple[int, int]) -> Optional[str]:
    """Map a single-tile cardinal step to the game movement key."""
    dx = int(to_xy[0]) - int(from_xy[0])
    dy = int(to_xy[1]) - int(from_xy[1])
    if dx == 1 and dy == 0:
        return "right"
    if dx == -1 and dy == 0:
        return "left"
    if dx == 0 and dy == 1:
        return "down"
    if dx == 0 and dy == -1:
        return "up"
    return None

def _desired_facing(ply_x: int, ply_y: int, tgt_x: int, tgt_y: int) -> Optional[int]:
    """Return desired facing index (0=down,1=left,2=up,3=right) toward target tile."""
    if tgt_x > ply_x:
        return 3
    if tgt_x < ply_x:
        return 1
    if tgt_y > ply_y:
        return 0
    if tgt_y < ply_y:
        return 2
    return None

def _other_player_tiles_near(px: int, py: int, radius: int = 9) -> Set[Tuple[int, int]]:
    """Collect other-player tiles near a point using Frida-tracked snapshot data."""
    tiles: Set[Tuple[int, int]] = set()
    try:
        nearby_players = get_nearby_players(px, py, radius=radius)
    except Exception:
        return tiles

    for meta in nearby_players:
        ox = meta.get("X")
        oy = meta.get("Y")
        if ox is None or oy is None or _coords_oob(ox, oy):
            continue
        tiles.add((int(ox), int(oy)))
    return tiles

def _shortest_path_to_any(
    start: Tuple[int, int],
    candidates: List[Tuple[int, int]],
    walkable_tiles: Set[Tuple[int, int]],
) -> Optional[Tuple[List[Tuple[int, int]], Tuple[int, int]]]:
    """
    Return the shortest valid A* path from start to one of candidates.
    Output shape: (path, target_tile)
    """
    best: Optional[Tuple[List[Tuple[int, int]], Tuple[int, int]]] = None
    for tgt in candidates:
        path = astar_pathfinding(start, tgt, walkable_tiles)
        if not path:
            continue
        if best is None or len(path) < len(best[0]):
            best = (path, tgt)
    return best

def go_to_target(
    target: Target,
    *,
    near_thresh: float = 0.6,
    timeout_s: float = 20.0,
    tag: str = "NAV",
    excluded_tiles: set = None,
    exact_goal: bool = False,
    ignore_player_blockers: bool = False,
    push_through_blockers: bool = False,
) -> bool:
    """Universal live-XY navigator shared by home/combat movement targets."""
    import time
    base_walkable = get_walkable_tiles_cached()
    no_timeout = (timeout_s is None) or (float(timeout_s) <= 0.0)
    timeout_value = 0.0 if no_timeout else float(timeout_s)
    quiet_nav = str(tag).upper() == "HOME"

    def _nav_log(msg: str):
        if not quiet_nav:
            _log_debug(msg)

    if excluded_tiles:
        base_walkable -= set(excluded_tiles)

    _nav_log(
        f"[NAV] go_to_target timeout_s={'OFF' if no_timeout else timeout_value} (near_thresh={near_thresh}, tag={tag}, "
        f"excluded={len(excluded_tiles) if excluded_tiles else 0}, exact_goal={exact_goal}, "
        f"ignore_player_blockers={ignore_player_blockers}, push_through={push_through_blockers})"
    )

    cur = _live_xy()
    if cur is None:
        _nav_log(f"[{tag}] invalid start XY {cur}; abort")
        return False
    if cur not in base_walkable:
        if push_through_blockers:
            base_walkable.add(cur)
        else:
            _nav_log(f"[{tag}] invalid start XY {cur}; abort")
            return False

    goal = target.get_xy()
    if goal is None:
        _nav_log(f"[{tag}] target has no position")
        return False
    if goal not in base_walkable:
        if push_through_blockers:
            base_walkable.add(goal)
        else:
            _nav_log(f"[{tag}] goal {goal} not walkable")
            return False

    def _arrived(xy: Optional[Tuple[int, int]], dest: Tuple[int, int]) -> bool:
        if xy is None:
            return False
        if exact_goal:
            return int(xy[0]) == int(dest[0]) and int(xy[1]) == int(dest[1])
        return _distance_tiles(xy, dest) <= near_thresh

    if _arrived(cur, goal):
        return bool(target.on_arrival())

    t0 = time.time()
    blocked_tile_failures: Dict[Tuple[int, int], int] = {}
    BLOCKED_TILE_THRESHOLD = 3

    while True:
        if (not no_timeout) and ((time.time() - t0) >= timeout_value):
            break
        if not target.is_valid():
            _nav_log(f"[{tag}] target invalid/despawned")
            return False

        g = target.get_xy()
        if g is None:
            _nav_log(f"[{tag}] target lost")
            return False
        goal = g

        if (not ignore_player_blockers) and goal in _other_player_tiles_near(goal[0], goal[1], radius=1):
            _nav_log(f"[{tag}] goal tile {goal} now occupied by player; aborting to try alternate stand")
            return False

        cur = _live_xy()
        if _arrived(cur, goal):
            if target.on_arrival():
                return True

        if cur is not None and cur not in base_walkable:
            _nav_log(f"[{tag}] player at {cur} is on unwalkable tile; trying to recover to nearby walkable tile...")
            neighbors = [(cur[0], cur[1]-1), (cur[0]+1, cur[1]), (cur[0], cur[1]+1), (cur[0]-1, cur[1])]
            for neighbor in neighbors:
                if neighbor in base_walkable:
                    _nav_log(f"[{tag}] recovering to walkable neighbor {neighbor}")
                    key = _direction_key(cur, neighbor)
                    if not key:
                        continue
                    hold_key(key)
                    recovery_deadline = time.monotonic() + 1.0
                    recovered = False
                    try:
                        while time.monotonic() < recovery_deadline:
                            xy = _live_xy()
                            if xy and xy != cur and xy in base_walkable:
                                cur = xy
                                recovered = True
                                _nav_log(f"[{tag}] recovered to {cur}")
                                break
                            time.sleep(STEP_POLL_S)
                    finally:
                        release_key(key)

                    if recovered:
                        break

        if cur is None:
            continue

        allowed_walkable = base_walkable.copy()
        if cur not in allowed_walkable:
            allowed_walkable.add(cur)

        if not ignore_player_blockers:
            for tile in _other_player_tiles_near(cur[0], cur[1], radius=9):
                allowed_walkable.discard(tile)

        for tile, fail_count in list(blocked_tile_failures.items()):
            if fail_count >= BLOCKED_TILE_THRESHOLD:
                allowed_walkable.discard(tile)

        path = _path_or_none(cur, goal, allowed_walkable)
        if path is None:
            if push_through_blockers:
                dx = int(goal[0]) - int(cur[0])
                dy = int(goal[1]) - int(cur[1])
                if dx == 0 and dy == 0:
                    if target.on_arrival():
                        return True
                    return False

                if abs(dx) >= abs(dy):
                    nxt = (cur[0] + (1 if dx > 0 else -1 if dx < 0 else 0), cur[1])
                    if dx == 0:
                        nxt = (cur[0], cur[1] + (1 if dy > 0 else -1))
                else:
                    nxt = (cur[0], cur[1] + (1 if dy > 0 else -1 if dy < 0 else 0))
                    if dy == 0:
                        nxt = (cur[0] + (1 if dx > 0 else -1), cur[1])

                key = _direction_key(cur, nxt)
                if key:
                    hold_key(key)
                    push_deadline = time.monotonic() + STEP_TIMEOUT_S + 0.90
                    try:
                        while time.monotonic() < push_deadline:
                            xy = _live_xy()
                            if _arrived(xy, goal):
                                release_key(key)
                                return bool(target.on_arrival())
                            if xy and xy != cur:
                                cur = xy
                                break
                            time.sleep(STEP_POLL_S)
                    finally:
                        try:
                            release_key(key)
                        except Exception:
                            pass
                time.sleep(0.01)
                continue

            _nav_log(f"[{tag}] no path {cur}->{goal}")
            return False

        if not ignore_player_blockers:
            blocked_path_tiles = list(set(path[1:]).intersection(_other_player_tiles_near(cur[0], cur[1], radius=9)))
            if blocked_path_tiles:
                _nav_log(f"[{tag}] path blocked by players at {blocked_path_tiles}; rerouting...")
                time.sleep(0.01)
                continue

        try:
            global current_path_tiles, path_fade_timestamp
            current_path_tiles = path[1:]
            path_fade_timestamp = None  # Reset - path is now actively being traversed, not yet at destination
        except Exception:
            pass

        progressed = False
        i = 1
        while i < len(path):
            nxt = path[i]
            if nxt not in allowed_walkable:
                _nav_log(f"[{tag}] path step {nxt} not walkable")
                break

            key = _direction_key(cur, nxt)
            if not key:
                break

            hold_key(key)
            deadline = time.monotonic() + STEP_TIMEOUT_S + 0.20
            reached_next = False
            xy = cur
            try:
                while time.monotonic() < deadline:
                    xy = _live_xy()
                    if xy and xy == nxt:
                        cur = xy
                        reached_next = True
                        break
                    elif xy and xy != cur:
                        cur = xy

                    if xy and _distance_tiles(xy, nxt) <= 0.5:
                        cur = xy
                        reached_next = True
                        break

                    if _arrived(cur, goal):
                        break

                    time.sleep(STEP_POLL_S)
            finally:
                release_key(key)

            if reached_next:
                progressed = True
                blocked_tile_failures.pop(nxt, None)
                i += 1
                if _arrived(cur, goal):
                    if target.on_arrival():
                        return True
                    else:
                        return False
                continue

            if push_through_blockers:
                hold_key(key)
                push_deadline = time.monotonic() + STEP_TIMEOUT_S + 0.90
                moved_during_push = False
                try:
                    while time.monotonic() < push_deadline:
                        xy = _live_xy()
                        if _arrived(xy, goal):
                            release_key(key)
                            return bool(target.on_arrival())
                        if xy and xy != cur:
                            cur = xy
                            moved_during_push = True
                            break
                        time.sleep(STEP_POLL_S)
                finally:
                    try:
                        release_key(key)
                    except Exception:
                        pass

                if moved_during_push:
                    progressed = True
                    break

            blocked_tile_failures[nxt] = blocked_tile_failures.get(nxt, 0) + 1

            if cur not in base_walkable:
                _nav_log(f"[{tag}] player drifted to unwalkable tile {cur}; breaking for recovery in outer loop")
                progressed = False
                break

            _nav_log(f"[{tag}] player drifted to {cur} (not on planned path); rerouting...")
            progressed = False
            break

        if not progressed:
            cur = _live_xy()
            if _arrived(cur, goal):
                if target.on_arrival():
                    return True
                else:
                    return False
            time.sleep(0.01)

    _nav_log(f"[{tag}] timeout navigating to {goal}")
    return False

def start_bot():
    """Start all bot threads"""
    _set_bot_running(True)
    _log_info("[BOT] Time to Kill Shit!")
    
def stop_bot(detach_hooks: bool = False):
    """Stop bot runtime. Optionally detach tracked Frida hooks."""
    _set_bot_running(False)
    _set_attack_state(False)
    try:
        release_key('ctrl')
    except Exception:
        pass
    _log_info("[BOT] STOP Damnit!")
    if detach_hooks:
        _detach_tracked_frida_hooks()

def record_direction_points():
    """
    Prompts user to click 5 times in this exact order:
      1) UP
      2) RIGHT
      3) DOWN
      4) LEFT
      5) PLAYER (your own character)

    Stores (strict client-relative/session-bound):
      - First 4 into global `resurrect_points` as [Up, Right, Down, Left]
      - 5th into global `player_click_point`
      - Requires a valid Endless window handle.
    """
    global resurrect_points, player_click_point

    hwnd = _get_target_hwnd()

    resurrect_points.clear()
    player_click_point = None

    prompts = ["UP", "RIGHT", "DOWN", "LEFT", "PLAYER"]
    _log_info("[SETUP] Click the following in your game window when prompted.")
    from pynput import mouse

    captured = []
    bound_hwnd = int(hwnd or 0)
    if bound_hwnd:
        _log_info(f"[SETUP] Using EO handle 0x{bound_hwnd:X} for client conversion.")
    else:
        _log_warn("[SETUP] EO handle not pre-resolved; first valid click in EO window will bind it.")
    _log_info("[SETUP] Click point mode: CLIENT (session-bound)")

    def capture_one(label):
        nonlocal bound_hwnd
        _log_info(f"   -> Click the {label} spot now...")
        def on_click(x, y, button, pressed):
            nonlocal bound_hwnd
            if pressed:
                sx, sy = int(x), int(y)
                if not bound_hwnd:
                    candidate = _window_from_point(sx, sy)
                    if candidate and TARGET_PID and _hwnd_pid(candidate) != int(TARGET_PID):
                        _log_warn(f"     {label} click ignored (not EO target PID).")
                        return
                    if candidate:
                        bound_hwnd = int(candidate)
                        _log_info(f"[SETUP] Bound EO handle from click: 0x{bound_hwnd:X}")
                cxy = _screen_to_client_xy(sx, sy, hwnd=bound_hwnd if bound_hwnd else None)
                if cxy is None:
                    _log_warn(f"     {label} skipped (could not convert screen to client). Click inside EO window.")
                    return
                cx, cy = cxy
                captured.append((cx, cy))
                _log_info(f"     {label} recorded client=({cx}, {cy})")
                return False
        with mouse.Listener(on_click=on_click) as listener:
            listener.join()

    for lab in prompts:
        capture_one(lab)

    if len(captured) >= 4:
        resurrect_points[:] = captured[:4]  # [Up, Right, Down, Left]
        _log_info("[SETUP] Loot click points set (Up,Right,Down,Left):", resurrect_points)
    else:
        _log_info("[SETUP] Not enough points recorded for loot (need 4).")

    if len(captured) >= 5:
        player_click_point = captured[4]
        _log_info(f"[SETUP] Player click point set at {player_click_point}")
    else:
        _log_info("[SETUP] No player point recorded.")
    
    try:
        save_settings()
    except Exception:
        pass

def _all_stop():
    """Release any keys that could cause movement/attacking."""
    for k in ('ctrl', 'up', 'down', 'left', 'right'):
        try:
            release_key(k)
        except Exception:
            pass
    time.sleep(0.08)

def _pause_movement(settle_delay: float = 0.01, tag: str = "ACTION"):
    """Fully pause movement & attacks during pickups/home routine."""
    try:
        movement_allowed.clear()  # gate combat_thread BEFORE we click
    except Exception:
        pass
    _all_stop()
    time.sleep(settle_delay)  # minimal settle time since loot is now async

def _resume_movement():
    """Allow combat thread to continue (after clicks/routines)."""
    _all_stop()                   # belt-and-suspenders
    try:
        movement_allowed.set()
    except Exception:
        pass

def block_clicks_for(seconds: float):
    _extend_no_click(seconds)
    
def _has_nearby_target(radius: int = NEARBY_THREAT_RADIUS) -> bool:
    """True if any valid target NPC is within `radius` tiles of the player.

    Used by HOME / HP-HOME safety logic so we only abort when a mob is actually
    close enough to be a real threat ("beside" the player), not just anywhere
    on the map.
    """
    try:
        if not STOP_HOME_IF_TARGET:
            return False
        _, snapshot = _get_map_snapshot()
        if not snapshot:
            return False

        px, py = _live_xy() or (None, None)
        if px is None or py is None:
            return False

        now = time.monotonic()
        for item in snapshot:
            if item.get("type") != "npc":
                continue
            uid = item.get("unique_id")
            if uid not in MOB_ID_FILTERS:
                continue
            addr_hex = item.get("address_x")
            if addr_hex and (now - RECENTLY_KILLED.get(addr_hex, 0.0)) < KILL_QUARANTINE_SEC:
                continue
            
            ox = item.get("X")
            oy = item.get("Y")
            if ox is None or oy is None:
                continue
            
            if max(abs(ox - px), abs(oy - py)) <= radius:
                return True
        
        return False
    except Exception as e:
        _warn_throttled("nearby_target:error", f"[THREAT] nearby target scan error: {e}", interval_s=3.0)
        return False

def is_attacking() -> bool:
    return bool(RUNTIME_STATE.attack_active)

def recently_attacking(addr: Optional[str], window: float = ATTACK_RECENCY_S) -> bool:
    return (addr is not None
            and addr == RUNTIME_STATE.last_attack_addr
            and (time.time() - RUNTIME_STATE.last_attack_time) < window)

def read_stat(name):
    """
    Reads a single stat using STAT_OFFSETS and the global stat_base.
    Special handling for current_hp/current_mana which come from Frida hooks.
    """
    global stat_base, CURRENT_HP, CURRENT_MANA
    if stat_base is None and name not in ('current_hp', 'current_mana'):
        return None
    
    if name == 'current_hp':
        try:
            return CURRENT_HP  # Atomic read, no lock needed
        except Exception:
            return None
    
    if name == 'current_mana':
        try:
            return CURRENT_MANA  # Atomic read, no lock needed
        except Exception:
            return None
    
    addr = stat_base + STAT_OFFSETS[name]
    try:
        return pm.read_int(addr)
    except Exception:
        return None

def read_all_stats():
    """
    Reads all stats into a dictionary.
    """
    stats = {}
    for k in STAT_OFFSETS:
        stats[k] = read_stat(k)
    stats['current_hp'] = read_current_hp()
    stats['current_mana'] = read_current_mana()
    return stats

def _normalize_direction(raw_dir: Any) -> int:
    """Normalize client-facing byte to 0..3 (Down, Left, Up, Right)."""
    try:
        return int(raw_dir) & 0x03
    except Exception:
        return 0

def _read_facing_live() -> Optional[int]:
    """Return current facing 0..3 from directional_address, or None if unavailable."""
    try:
        if directional_address and pm:
            return _normalize_direction(pm.read_uchar(directional_address))
    except Exception:
        pass
    return None

def tap_key(key_name: str, times: int = 1, gap: float = 0.08):
    """Best-effort key tap that works with your existing press/release or keyboard lib."""
    import time
    for _ in range(times):
        try:
            press_key(key_name, presses=1, delay=0.0)
        except Exception as e:
            _warn_throttled(f"tap_key:{key_name}", f"[WARN] tap_key({key_name}) failed: {e}", interval_s=2.0)
        time.sleep(gap)

def tap_key_async(key_name: str, times: int = 1, gap: float = 0.08):
    """Non-blocking key tap - executes in background thread without delay."""
    def _async_tap():
        try:
            tap_key(key_name, times=times, gap=gap)
        except Exception as e:
            _warn_throttled(f"tap_key_async:{key_name}", f"[WARN] Async tap_key({key_name}) failed: {e}", interval_s=2.0)
    
    thread = threading.Thread(target=_async_tap, daemon=True)
    thread.start()

def _do_loot_async(game_win, pts, facing, burst=None, gap=None, hold_seconds=None, tag="KILL"):
    """Execute loot clicking asynchronously without blocking combat."""
    def _async_loot():
        try:
            if burst is not None and gap is not None:
                _do_fast_click_burst(game_win, pts, facing, burst, gap, tag=tag)
            elif hold_seconds is not None:
                _do_directional_loot(game_win, pts, facing, hold_seconds=hold_seconds, tag=tag)
            else:
                _do_clicks(game_win, pts, tag=tag)
        except Exception as e:
            _warn_throttled("loot_async:fail", f"[WARN] Async loot failed: {e}", interval_s=2.0)
    
    thread = threading.Thread(target=_async_loot, daemon=True)
    thread.start()

def _get_xy_safe():
    """Try to read player coords if your script exposes it; otherwise return (None, None)."""
    fn = get_player_coords
    if callable(fn):
        try:
            return fn(pm)
        except Exception:
            pass
    try:
        return (pm.read_short(x_address), pm.read_short(y_address))
    except Exception:
        return (None, None)

def _distance_tiles(a, b):
    if a[0] is None or b[0] is None:
        return None
    dx = a[0] - b[0]
    dy = a[1] - b[1]
    return (dx*dx + dy*dy) ** 0.5

def _nearby_threat_safe() -> bool:
    """Best-effort nearby-threat check that never raises."""
    try:
        return bool(_has_nearby_target())
    except Exception:
        return False

def _start_home_routine_if_idle(*, delay_s: float = 0.0) -> bool:
    """
    Start home routine once if not already running.
    Returns True when a new thread was started.
    """
    if home_routine_running.is_set():
        return False
    threading.Thread(target=_home_routine, daemon=True).start()
    if delay_s > 0:
        time.sleep(delay_s)
    return True

def _go_to_home_blocking():
    """Walk to HOME_POS using the live navigator; abort early if targets appear
    (unless we're in strict HP-home mode)."""
    global HP_HOME_ABORT_LOCK
    if not isinstance(HOME_POS, tuple) or len(HOME_POS) != 2:
        return "SKIP"

    hp_home = bool(HP_HOME_ACTIVE)

    if (not hp_home) and _nearby_threat_safe():
        return "ABORT"

    hx, hy = int(HOME_POS[0]), int(HOME_POS[1])

    class _HomeTarget:
        def get_xy(self):
            return (hx, hy)
        def is_valid(self):
            return True
        def on_arrival(self):
            return True

    try:
        arrived = go_to_target(
            _HomeTarget(),
            tag="HOME",
            near_thresh=0.0,
            exact_goal=True,
            ignore_player_blockers=True,
            push_through_blockers=True,
            timeout_s=HOME_TRAVEL_TIMEOUT,
        )
    except Exception as e:
        return "TIMEOUT"

    if arrived:
        _log_info(f"[HOME] Arrived home: {HOME_POS}")
        return "ARRIVED"

    if not hp_home and _nearby_threat_safe():
        HP_HOME_ABORT_LOCK = True
        return "ABORT"

    return "TIMEOUT"

def _home_routine():
    global HP_HOME_ACTIVE, KILLS_SINCE_HOME, HP_HOME_ABORT_LOCK, HP_HOME_LAST_ABORT
    if home_routine_running.is_set():
        return
    home_routine_running.set()
    _log_info("[HOME] Home run started.")

    hp_home_strict  = bool(HP_HOME_ACTIVE)
    hp_home_feature = bool(HP_HOME_ENABLED)

    def _should_abort_for_nearby() -> bool:
        return (not hp_home_strict) and _nearby_threat_safe()

    def _hp_safety_check(last_hp):
        try:
            cur_hp = read_current_hp()
        except Exception:
            cur_hp = None

        if cur_hp is None:
            return last_hp, False

        target_near = _nearby_threat_safe()

        if last_hp is not None and cur_hp < last_hp and target_near:
            try:
                tap_key_async('f8', times=1) 
                tap_key('f11', times=1)   # stand up if we were sitting
            except Exception:
                pass

            try:
                import time
                HP_HOME_LAST_ABORT = time.time()
            except Exception:
                pass

            return cur_hp, True
        
        return cur_hp, False
    
    def _wait_for_clicks(label: str, timeout_s: float = 6.0):
        try:
            start = time.time()
            while clicks_in_progress.is_set():
                if timeout_s and (time.time() - start) > timeout_s:
                    break
                time.sleep(0.01)
        except NameError:
            pass

    def _finish():
        global HP_HOME_ACTIVE
        try:
            _resume_movement()
        except Exception:
            pass
        try:
            HP_HOME_ACTIVE = False
        except Exception:
            pass
        home_routine_running.clear()

    try:
        _wait_for_clicks("pre-travel")
        try:
            _pause_movement(tag="HOME")
        except Exception:
            pass
        try:
            release_key('ctrl')
        except Exception:
            pass

        if _should_abort_for_nearby():
            return

        travel_status = None
        try:
            travel_status = _go_to_home_blocking()
        except Exception as e:
            travel_status = "TIMEOUT"

        if travel_status in ("ABORT",) and not hp_home_strict:
            return
        if travel_status in ("SKIP", "TIMEOUT"):
            if _should_abort_for_nearby():
                return

        _wait_for_clicks("pre-buff")

        if _should_abort_for_nearby():
            HP_HOME_ABORT_LOCK = True
            return

        try:
            _pause_movement(tag="HOME")          # movement_allowed.clear + _all_stop + tiny sleep
        except Exception:
            for k in ('up', 'down', 'left', 'right'):
                try:
                    release_key(k)
                except Exception:
                    pass
            time.sleep(0.1)

        try:
            tap_key_async('f7', times=1)  # async - don't block
            tap_key('f11', times=1)  # proceed immediately
            block_clicks_for(3.0)
        except Exception as e:
            pass

        f5_total = int(F5_TAP_COUNT)
        f5_gap = 0.08
        for i in range(f5_total):
            if _nearby_threat_safe():
                try:
                    tap_key_async('f8', times=1, gap=0.05)  # async - don't block
                    tap_key('f11', times=1, gap=0.05)  # stand up if sitting
                except Exception:
                    pass
                return  # leave _home_routine(); finally block will clean up

            try:
                tap_key('f5', times=1, gap=f5_gap)
            except Exception:
                pass

        if not hp_home_strict:
            try:
                sit_secs = int(SIT_TIMER_SECONDS)
            except NameError:
                sit_secs = 10

            _log_info(f"[HOME] Waiting up to {sit_secs}s (interruptible).")

            try:
                if BOSS_AGGRO_TOGGLE:
                    for i in range(sit_secs):
                        if _nearby_threat_safe():
                            HP_HOME_ABORT_LOCK = True
                            tap_key('f11', times=1)
                            return

                        time.sleep(1)
            except NameError:
                pass

        else:
            pass

        try:
            if hp_home_feature and hp_home_strict:
                max_hp = read_stat('max_hp')
                if max_hp and max_hp > 0:
                    high_thresh = float(HP_HOME_HIGH_PCT)

                    last_hp = read_current_hp()

                    while True:
                        try:
                            last_hp, abort = _hp_safety_check(last_hp)
                        except Exception as e:
                            break

                        if abort:
                            return

                        cur_hp = last_hp
                        if cur_hp is None:
                            break

                        hp_pct = (cur_hp / max_hp) * 100.0
                        if hp_pct >= high_thresh:
                            break

                        time.sleep(0.5)
        except Exception as e:
            pass

        try:
            tap_key('f11', times=1, gap=0.05)
        except Exception:
            pass
        
        try:
            KILLS_SINCE_HOME = 0
        except Exception:
            pass

    finally:
        _finish()

def _in_immunity(addr_hex: str) -> bool:
    """True if addr_hex is inside the 'first N seconds after attach' window."""
    try:
        import time as _t
        if not addr_hex:
            return False
        deadline = _target_immunity_until.get(addr_hex, 0.0)
        return _t.monotonic() < deadline
    except Exception:
        return False

def _fire_kill_once(addr_hex: str, reason: str) -> bool:
    """
    Run kill actions only if addr_hex == current_target_npc, and at most once per debounce/quarantine window.
    """
    import time
    global current_target_npc

    if not addr_hex or addr_hex != current_target_npc:
        return False

    try:
        if home_routine_running.is_set() or clicks_in_progress.is_set():
            return False
    except Exception:
        pass

    now = time.monotonic()

    last_k = RECENTLY_KILLED.get(addr_hex, 0.0)
    if (now - last_k) < KILL_QUARANTINE_SEC:
        return False

    prev = _last_kill_ts.get(addr_hex, 0.0)
    if (now - prev) < KILL_DEBOUNCE_SEC:
        return False

    with _kill_lock:
        prev = _last_kill_ts.get(addr_hex, 0.0)
        if (now - prev) < KILL_DEBOUNCE_SEC:
            return False

        _last_kill_ts[addr_hex] = now
        RECENTLY_KILLED[addr_hex] = now

        _on_kill(addr_hex, reason=reason)
        return True

def on_message_exp(message, data):
    global stat_base
    if message['type'] == 'send':
        payload = message['payload']
        base_str = payload.get('exp_address')
        if base_str:
            try:
                stat_base = int(base_str, 16)
                start_weight_lock()
                if current_target_npc:
                    _fire_kill_once(current_target_npc, reason="EXP-HOOK")
                    
            except Exception as e:
                _log_warn(f"[frida] Failed to parse stat base: {e}")

def _on_message_scalar(message, payload_key: str, err_tag: str) -> Optional[int]:
    """Shared Frida callback helper for scalar payload updates like HP/MANA."""
    if message['type'] == 'send':
        payload = message.get('payload', {})
        if payload_key in payload:
            try:
                return int(payload[payload_key])
            except Exception:
                return None
    elif message['type'] == 'error':
        _log_info(f"[frida][{err_tag}] {message.get('stack')}")
    return None

def on_message_hp(message, data):
    """Handle HP updates from Frida hook."""
    global CURRENT_HP
    value = _on_message_scalar(message, payload_key='hp', err_tag='hp')
    if value is not None:
        CURRENT_HP = value

def on_message_mana(message, data):
    """Handle mana updates from Frida hook."""
    global CURRENT_MANA
    value = _on_message_scalar(message, payload_key='mana', err_tag='mana')
    if value is not None:
        CURRENT_MANA = value

def _on_kill(addr_hex: str, reason: str):
    global current_target_npc, KILLS_SINCE_HOME, vanish_timer  # must be declared at the very top

    def _ts():
        import time
        return time.strftime("%H:%M:%S")

    _log_info(f"[KILLS][{_ts()}] KILLED: {addr_hex if addr_hex else '0x0'} | {reason}")

    try:
        import time as _t
        if addr_hex:
            RECENTLY_KILLED[addr_hex] = _t.monotonic()
    except Exception:
        pass

    try:
        clicking_disabled = not CLICKING_ENABLED
        run_home = bool(RUN_HOME_AFTER_KILL)
        fast_click_enabled = bool(FAST_CLICK)
    except Exception:
        clicking_disabled, run_home, fast_click_enabled = False, False, False

    if clicking_disabled and (not fast_click_enabled) and (not run_home):
        try:
            try:
                release_key('ctrl')
            except Exception:
                pass

            if manager and addr_hex:
                manager.remove_address(addr_hex)
        except Exception:
            pass

        try:
            if addr_hex:
                vanish_timer.pop(addr_hex, None)
            current_target_npc = None
        except Exception:
            pass

        _log_info(f"[KILL] Training Mode - home disabled, immediate resume (addr={addr_hex})")
        return

    try:
        _pause_movement(settle_delay=0.01, tag="KILL")  # minimal pause since loot is async
    except Exception:
        pass
    try:
        release_key('ctrl')
    except Exception:
        pass

    game_win = None

    facing = 0
    try:
        facing = int(player_data_manager.get_data().get("direction", 0))
    except Exception:
        pass

    pts = list(resurrect_points)

    try:
        if FAST_CLICK and (not CLICKING_ENABLED):
            _do_loot_async(
                game_win, 
                pts, 
                facing, 
                burst=int(FAST_CLICK_BURST_COUNT),
                gap=float(FAST_CLICK_GAP_S),
                tag="KILL"
            )
        elif DIRECTIONAL_LOOT:
            _do_loot_async(game_win, pts, facing, hold_seconds=LOOT_HOLD_SECONDS, tag="KILL")
        else:
            _do_loot_async(game_win, pts, facing, tag="KILL")
    except Exception:
        pass

    try:
        run_home_toggle = bool(RUN_HOME_AFTER_KILL)

        KILLS_SINCE_HOME = int(KILLS_SINCE_HOME) + 1

        should_home_now = (
            run_home_toggle
            and int(KILLS_SINCE_HOME) >= int(HOME_AFTER_KILLS_N)
        )

        if should_home_now:
            _log_info(f"[KILLS] Threshold reached: {KILLS_SINCE_HOME} / {HOME_AFTER_KILLS_N} -> going Home")
            _start_home_routine_if_idle()
        else:
            _resume_movement()
    except Exception:
        pass

    try:
        if manager and addr_hex:
            manager.remove_address(addr_hex)
    except Exception:
        pass

    try:
        if addr_hex:
            vanish_timer.pop(addr_hex, None)
        current_target_npc = None
    except Exception:
        pass

def _face_in_game_best_effort(facing: int):
    """Turn without stepping: only micro-tap if facing differs."""
    try:
        want = int(facing) % 4

        cur = _read_facing_live()
        if cur is not None and (cur % 4) == want:
            return

        dir_key = {0:'down', 1:'left', 2:'up', 3:'right'}[want]

        for k in ('up','down','left','right'):
            try:
                release_key(k)
            except Exception:
                pass

        hold_key(dir_key)
        time.sleep(0.003)
        release_key(dir_key)
    except Exception:
        pass
def _resolve_walkable_path(preferred: Optional[str]) -> Optional[Path]:
    """
    Resolve walkable JSON from the bot's own directory.
    Relative paths are interpreted relative to APP_BASE_DIR.
    """
    candidates: List[Path] = []
    app_dir = APP_BASE_DIR.resolve()

    def expand(p: Union[str, Path]) -> Path:
        raw = Path(os.path.expandvars(os.path.expanduser(str(p))))
        if raw.is_absolute():
            return raw.resolve()
        return (app_dir / raw).resolve()

    def in_app_dir(p: Path) -> bool:
        try:
            resolved = p.resolve()
            return resolved == app_dir or (app_dir in resolved.parents)
        except Exception:
            return False

    if preferred:
        p = expand(preferred)
        candidate = (p / "walkable.json") if p.is_dir() else p
        if in_app_dir(candidate):
            candidates.append(candidate)

    env = os.getenv("WALKABLE_JSON")
    if env:
        q = expand(env)
        candidate = q if not q.is_dir() else q / "walkable.json"
        if in_app_dir(candidate):
            candidates.append(candidate)

    candidates.append(app_dir / "walkable.json")
    candidates.append(app_dir / "walkable.json.json")
    candidates.append(app_dir / "walkable")

    for c in candidates:
        try:
            if c.is_file():
                return c
        except Exception:
            pass

    return None

def initialize_pymem():
    global pm
    if pm is not None:
        return

    pid = TARGET_PID
    if pid:
        try:
            pm = pymem.Pymem(process_id=int(pid))
        except TypeError:
            pm = pymem.Pymem(int(pid))
        _log_info(f"[BOOT] Pymem attached to PID {pid}")
    else:
        pm = pymem.Pymem("Endless.exe")
        _log_info("[BOOT] Pymem attached by name Endless.exe")

def resolve_all_aobs(timeout=5.0):
    """
    Universal Frida-based AOB resolver.
    Resolves WALK, NPC, SPEECH, DIRECTIONAL, EXP, HP, MANA, OTHER_PLAYERS, MAP_ID.
    Stores all as integer RVA offsets.
    """

    import frida, time

    global walkAddress, npcAddress, speechAddress
    global directionalAddress, expAddress, hpAddress, manaAddress
    global otherPlayersAddress, mapIdAddress

    walkAddress = None
    npcAddress = None
    speechAddress = None
    directionalAddress = None
    expAddress = None
    hpAddress = None
    manaAddress = None
    otherPlayersAddress = None
    mapIdAddress = None

    session = frida_attach_target()

    FRIDA_JS = f"""
    'use strict';

    const moduleName = "Endless.exe";
    const module = Process.getModuleByName(moduleName);
    const base = module.base;
    const size = module.size;

    function scan(pattern, firstOnly) {{
        return new Promise(resolve => {{
            let found = null;
            Memory.scan(base, size, pattern, {{
                onMatch(address) {{
                    if (firstOnly) {{
                        // Keep the lowest address match (stable "first in module" semantics).
                        if (found === null || address.compare(found) < 0) {{
                            found = address;
                        }}
                    }} else {{
                        // keep legacy behavior (last match) for non-speech hooks
                        found = address;
                    }}
                }},
                onComplete() {{
                    resolve(found);
                }}
            }});
        }});
    }}

    async function main() {{
        const walkHit         = await scan("{WALK_AOB}", false);
        const npcHit          = await scan("{NPC_AOB}", false);
        const speechHit       = await scan("{SPEECH_AOB}", true);
        const directionalHit  = await scan("{DIRECTIONAL_AOB}", false);
        const expHit          = await scan("{EXP_AOB}", false);
        const hpHit           = await scan("{HP_AOB}", false);
        const manaHit         = await scan("{MANA_AOB}", false);
        const otherPlayersHit = await scan("{OTHER_PLAYERS_AOB}", false);
        const mapIdHit        = await scan("{MAP_ID_AOB}", true);

        send({{
            type: "aob_results",
            base: base.toString(),
            walk: walkHit ? walkHit.toString() : null,
            npc: npcHit ? npcHit.toString() : null,
            speech: speechHit ? speechHit.toString() : null,
            directional: directionalHit ? directionalHit.toString() : null,
            exp: expHit ? expHit.toString() : null,
            hp: hpHit ? hpHit.toString() : null,
            mana: manaHit ? manaHit.toString() : null,
            other_players: otherPlayersHit ? otherPlayersHit.toString() : null,
            map_id: mapIdHit ? mapIdHit.toString() : null
        }});
    }}

    main();
    """

    resolved = {"done": False}

    def on_aob_message(message, data):
        global walkAddress, npcAddress, speechAddress
        global directionalAddress, expAddress, hpAddress, manaAddress
        global otherPlayersAddress, mapIdAddress

        if message["type"] != "send":
            return

        payload = message["payload"]
        if payload.get("type") != "aob_results":
            return

        base = int(payload["base"], 16)

        if payload["walk"]:
            walkAddress = (int(payload["walk"], 16) + 5) - base

        if payload["npc"]:
            npcAddress = int(payload["npc"], 16) - base

        if payload["speech"]:
            speechAddress = int(payload["speech"], 16) - base

        if payload["directional"]:
            directionalAddress = int(payload["directional"], 16) - base

        if payload["exp"]:
            expAddress = (int(payload["exp"], 16) + 5) - base

        if payload["hp"]:
            hpAddress = int(payload["hp"], 16) - base

        if payload.get("mana"):
            manaAddress = int(payload["mana"], 16) - base

        if payload["other_players"]:
            otherPlayersAddress = int(payload["other_players"], 16) - base
        if payload.get("map_id"):
            mapIdAddress = int(payload["map_id"], 16) - base

        resolved["done"] = True

    _load_frida_script(session, FRIDA_JS, on_aob_message, label="aob-resolver", keepalive=False)

    start = time.time()
    while not resolved["done"]:
        if time.time() - start > timeout:
            break
        time.sleep(0.05)

    session.detach()

    addresses = (
        walkAddress,
        npcAddress,
        speechAddress,
        directionalAddress,
        expAddress,
        hpAddress,
        otherPlayersAddress
    )

    if any(addr is None for addr in addresses):
        _log_warn("[AOB ERROR] Resolution failed.")
        return False

    _log_info("[AOB] WALK          ->", hex(walkAddress))
    _log_info("[AOB] NPC           ->", hex(npcAddress))
    _log_info("[AOB] SPEECH        ->", hex(speechAddress))
    _log_info("[AOB] DIRECTIONAL   ->", hex(directionalAddress))
    _log_info("[AOB] EXP           ->", hex(expAddress))
    _log_info("[AOB] HP            ->", hex(hpAddress))
    _log_info("[AOB] MANA          ->", (hex(manaAddress) if isinstance(manaAddress, int) else "N/A"))
    _log_info("[AOB] OTHER_PLAYERS ->", hex(otherPlayersAddress))
    if isinstance(mapIdAddress, int):
        _log_info("[AOB] MAP_ID        ->", hex(mapIdAddress))
    else:
        _log_warn("[AOB] MAP_ID signature not found; auto map-id loading unavailable.")

    return True

def press_key(key, presses=1, delay=0.1, interval=0.0):
    if not _require_background_input(f"press:{key}"):
        return False
    try:
        pydirectinput.press(key, presses=max(1, int(presses)), interval=max(0.0, float(interval)))
    except Exception as e:
        _warn_throttled("input:press_fail", f"[INPUT] press failed ({key}): {e}", interval_s=1.5)
        return False
    if delay > 0:
        time.sleep(delay)
    return True

def hold_key(key):
    if not _require_background_input(f"hold:{key}"):
        return False
    try:
        pydirectinput.keyDown(key)
        return True
    except Exception as e:
        _warn_throttled("input:hold_fail", f"[INPUT] hold failed ({key}): {e}", interval_s=1.5)
        return False

def release_key(key):
    if not _require_background_input(f"release:{key}"):
        return False
    try:
        pydirectinput.keyUp(key)
        return True
    except Exception as e:
        _warn_throttled("input:release_fail", f"[INPUT] release failed ({key}): {e}", interval_s=1.5)
        return False

def click_point(x, y, *, clicks=1, interval=0.0, button="left", delay=0.0):
    if not _require_background_input("click"):
        return False
    try:
        pydirectinput.click(
            x=int(x),
            y=int(y),
            clicks=max(1, int(clicks)),
            interval=max(0.0, float(interval)),
            button=str(button),
        )
    except TypeError:
        try:
            pydirectinput.click(x=int(x), y=int(y))
        except Exception as e:
            _warn_throttled("input:click_fail", f"[INPUT] click failed ({x},{y}): {e}", interval_s=1.5)
            return False
    except Exception as e:
        _warn_throttled("input:click_fail", f"[INPUT] click failed ({x},{y}): {e}", interval_s=1.5)
        return False
    if delay > 0:
        time.sleep(delay)
    return True

def click_client_point(x, y, *, clicks=1, interval=0.0, button="left", delay=0.0):
    """Background click using client-relative coordinates."""
    if not _require_background_input("click_client"):
        return False
    try:
        with _BG_INPUT_LOCK:
            backend = _BG_INPUT
        if backend is None or not getattr(backend, "attached", False):
            _warn_throttled("input:click_client_missing", "[INPUT] click_client backend missing.", interval_s=1.5)
            return False
        if hasattr(backend, "click_client"):
            backend.click_client(
                x=int(x),
                y=int(y),
                clicks=max(1, int(clicks)),
                interval=max(0.0, float(interval)),
                button=str(button),
            )
        else:
            # Safety fallback for older backend shape.
            xy = _client_to_screen_xy(int(x), int(y))
            if not xy:
                _warn_throttled("input:click_client_no_hwnd", "[INPUT] click_client fallback failed (no hwnd).", interval_s=1.5)
                return False
            sx, sy = xy
            return click_point(sx, sy, clicks=clicks, interval=interval, button=button, delay=delay)
    except Exception as e:
        _warn_throttled("input:click_client_fail", f"[INPUT] click_client failed ({x},{y}): {e}", interval_s=1.5)
        return False
    if delay > 0:
        time.sleep(delay)
    return True

def on_message_xy(message, data):
    global x_address, y_address, player_base

    if message["type"] != "send":
        return

    payload = message["payload"]
    if payload.get("type") != "xy_found":
        return

    if player_base is not None:
        return

    x_address = int(payload["x"], 16)
    y_address = int(payload["y"], 16)

    player_base = x_address - 0x08

    _log_info(f"[XY LOCKED] Base: {hex(player_base)} | X: {hex(x_address)} | Y: {hex(y_address)}")

def start_frida_exp():
    global expAddress

    if not isinstance(expAddress, int):
        _log_warn("[EXP] Invalid RVA type:", type(expAddress))
        return

    session = frida_attach_target()

    _log_info("[EXP] Hook installed")

    script_code = f"""
    var mod = Process.getModuleByName("Endless.exe");
    var base = mod.base;

    var target = base.add(ptr("{hex(expAddress)}"));

    Interceptor.attach(target, {{
        onEnter: function(args) {{
            var ebx = this.context.ebx || this.context.rbx;
            var edx = this.context.edx || this.context.rdx;

            if (!ebx) return;

            var expAddr = ebx.add(0x28);
            var newExp = edx.toInt32();

            send({{
                exp_address: expAddr.toString(),
                exp_value: newExp
            }});
        }}
    }});
    """

    _load_frida_script(session, script_code, on_message_exp, label="exp-hook")

def _start_frida_scalar_hook(
    *,
    rva: Any,
    tag: str,
    payload_key: str,
    on_message_cb,
    label: str,
    none_message: Optional[str] = None,
):
    """Install a scalar Frida hook (HP/MANA-like) and return (session, script)."""
    if rva is None and none_message:
        _log_info(none_message)
        return None, None
    if not isinstance(rva, int):
        _log_warn(f"[{tag}] Invalid RVA type:", type(rva))
        return None, None

    session = frida_attach_target()
    script_code = f"""
    var mod = Process.getModuleByName("Endless.exe");
    var base = mod.base;
    var target = base.add(ptr("{hex(rva)}"));

    Interceptor.attach(target, {{
        onEnter: function(args) {{
            var esi = this.context.esi || this.context.rsi;
            if (!esi) return;

            send({{
                {payload_key}: esi.toInt32()
            }});
        }}
    }});
    """
    script = _load_frida_script(session, script_code, on_message_cb, label=label)
    _log_info(f"[{tag}] Hook installed")
    return session, script

def start_frida_current_hp():
    global hpAddress, _HP_FRIDA_SESSION, _HP_FRIDA_SCRIPT
    _HP_FRIDA_SESSION, _HP_FRIDA_SCRIPT = _start_frida_scalar_hook(
        rva=hpAddress,
        tag="HP",
        payload_key="hp",
        on_message_cb=on_message_hp,
        label="hp-hook",
    )

def start_frida_current_mana():
    global manaAddress, _MANA_FRIDA_SESSION, _MANA_FRIDA_SCRIPT
    _MANA_FRIDA_SESSION, _MANA_FRIDA_SCRIPT = _start_frida_scalar_hook(
        rva=manaAddress,
        tag="MANA",
        payload_key="mana",
        on_message_cb=on_message_mana,
        label="mana-hook",
        none_message="[MANA] No resolved RVA; hook skipped.",
    )

def on_message_directional(message, data):
    global directional_address
    if message.get('type') == 'send':
        payload = message.get('payload', {})
        addr_hex = payload.get('directional_address')
        if not addr_hex:
            return
        try:
            directional_address = int(addr_hex, 16)
        except Exception:
            return
        _log_info(f"[FRIDA] directional_address={hex(directional_address)}")
        sys.stdout.flush()
    elif message.get('type') == 'error':
        _log_warn(f"[FRIDA][directional] Error: {message.get('stack')}")
        sys.stdout.flush()

def start_frida_session_directional(target_rva):
    if target_rva is None:
        _log_warn("[DIRECTIONAL] No resolved RVA. Aborting hook.")
        return

    if not isinstance(target_rva, int):
        _log_warn("[DIRECTIONAL] Invalid RVA type:", type(target_rva))
        return

    session = frida_attach_target()

    _log_info("Directional Started - Waiting for mov [ebx+56],dl to execute")

    script_code = f"""
    var mod = Process.getModuleByName("Endless.exe");
    var base = mod.base;

    var target = base.add(ptr({target_rva}));

    Interceptor.attach(target, {{
        onEnter: function(args) {{
            var ebx = this.context.ebx || this.context.rbx;
            if (!ebx) return;

            var characterDirectionAddress = ebx.add(0x56);
            var characterDirection = characterDirectionAddress.readU8();

            send({{
                directional_address: characterDirectionAddress.toString(),
                character_direction: characterDirection
            }});
        }}
    }});
    """

    got_directional_ptr = threading.Event()

    def _on_bootstrap_message(message, data):
        on_message_directional(message, data)
        mtype = message.get("type")
        if mtype == "send":
            payload = message.get("payload", {})
            if payload.get("directional_address"):
                got_directional_ptr.set()
        elif mtype == "error":
            got_directional_ptr.set()

    try:
        _load_frida_script(session, script_code, _on_bootstrap_message, label="directional-bootstrap", keepalive=False)
        if not got_directional_ptr.wait(timeout=15.0):
            _log_warn("[DIRECTIONAL] Timed out waiting for directional pointer.")
    finally:
        def _safe_detach():
            try:
                session.detach()
            except Exception:
                pass
        threading.Thread(target=_safe_detach, daemon=True).start()

    _log_info("Directional Session Completed.")

def on_message_map_id(message, data):
    if message.get("type") != "send":
        return
    payload = message.get("payload") or {}
    raw = payload.get("map_id")
    if raw is None:
        return
    try:
        map_id = int(raw)
    except Exception:
        return
    if map_id <= 0:
        return

    prev = _get_current_map_id()
    if prev != map_id:
        _set_current_map_id(map_id)
        _log_info(f"[MAP_ID] current map -> {map_id}")

def start_frida_map_id():
    global mapIdAddress, _MAP_ID_FRIDA_SESSION, _MAP_ID_FRIDA_SCRIPT
    if not isinstance(mapIdAddress, int):
        _log_warn("[MAP_ID] Invalid or missing RVA; hook skipped.")
        return

    session = frida_attach_target()
    script_code = f"""
    var mod = Process.getModuleByName("Endless.exe");
    var base = mod.base;
    var target = base.add(ptr("{hex(mapIdAddress)}"));
    var lastMapId = -1;

    Interceptor.attach(target, {{
        onEnter: function(args) {{
            var ecx = this.context.ecx || this.context.rcx;
            if (!ecx) return;
            var mapId = ecx.toInt32();
            if (mapId <= 0 || mapId === lastMapId) return;
            lastMapId = mapId;
            send({{
                map_id: mapId
            }});
        }}
    }});
    """
    _MAP_ID_FRIDA_SESSION = session
    _MAP_ID_FRIDA_SCRIPT = _load_frida_script(session, script_code, on_message_map_id, label="map-id-hook")
    _log_info("[MAP_ID] Hook installed.")

def patch_adds_with_nops():
    """
    Resolve the two npcFinalize add instructions via AOB
    and NOP them safely using Frida.
    """

    session = frida_attach_target()

    js = f"""
    'use strict';

    const module = Process.getModuleByName("Endless.exe");
    const base = module.base;
    const size = module.size;

    const patterns = [
        "{NPC_ADD1_AOB}",
        "{NPC_ADD2_AOB}"
    ];

    function scanAndPatch(pattern) {{
        Memory.scan(base, size, pattern, {{
            onMatch(address) {{
                // Make 7 bytes writable
                Memory.protect(address, 7, 'rwx');

                for (let i = 0; i < 7; i++) {{
                    Memory.writeU8(address.add(i), 0x90);
                }}

                Memory.protect(address, 7, 'r-x');

                send({{
                    type: "patched",
                    addr: address.toString()
                }});
            }},
            onComplete() {{}}
        }});
    }}

    for (let p of patterns) {{
        scanAndPatch(p);
    }}
    """

    def on_patch_message(message, data):
        if message["type"] == "send":
            payload = message["payload"]
            if payload.get("type") == "patched":
                _log_info(f"[AOB] Patched @ {payload['addr']}")

    _load_frida_script(session, js, on_patch_message, label="npc-nop-patch", keepalive=False)

    time.sleep(1.0)
    session.detach()

def start_frida_speech_monitor():
    """
    Frida-based speech monitor.
    Uses resolved global speechAddress.
    No kernel32 scanning.
    """

    import frida, time, re

    global speechAddress, current_target_npc

    if not speechAddress:
        _log_warn("[SPEECH] No resolved speechAddress.")
        return

    hook_rva = int(speechAddress)

    FRIDA_JS = f"""
    'use strict';

    const mod = Process.getModuleByName("Endless.exe");
    const base = mod.base;
    const size = mod.size;
    const rva = ptr("{hex(hook_rva)}");
    // speechAddress is stored as RVA in Python; resolve to absolute VA here.
    const HOOK = base.add(rva);
    if (HOOK.compare(base) < 0 || HOOK.compare(base.add(size)) >= 0) {{
        throw new Error("Speech HOOK out of module range: " + HOOK);
    }}
    const NPC_OFF = {NPC_NAME_OFFSET};
    const TXT_OFF = {TEXT_OFFSET};

    function notNull(p) {{
        return p && !p.isNull();
    }}

    function safePtr(a) {{
        try {{ return Memory.readPointer(a); }}
        catch (_) {{ return NULL; }}
    }}

    function readUtf8Safe(p) {{
        if (!notNull(p)) return "";
        try {{
            let s = Memory.readUtf8String(p);
            if (!s) return "";
            s = s.replace(/[\\x00-\\x1F]/g, "");
            return s.trim();
        }} catch (_) {{
            return "";
        }}
    }}

    function readLines(arrBase) {{
        const lines = [];
        const psz = Process.pointerSize;
        let nullStreak = 0;

        for (let i = 0; i < 16; i++) {{
            let tp;
            try {{
                tp = Memory.readPointer(arrBase.add(i * psz));
            }} catch (_) {{
                break;
            }}

            if (!notNull(tp)) {{
                nullStreak++;
                if (nullStreak >= 3) break;
                continue;
            }}

            nullStreak = 0;

            let s = readUtf8Safe(tp);

            if (!s) {{
                const q = safePtr(tp);
                if (notNull(q))
                    s = readUtf8Safe(q);
            }}

            if (s && s.length > 2 && !/^\\W+$/.test(s))
                lines.push(s);
        }}

        return lines.length ? lines.join("\\n") : null;
    }}

    Interceptor.attach(HOOK, {{
        onEnter() {{

            const ecxReg = this.context.ecx || this.context.rcx;
            if (!ecxReg) return;
            const ecx = ptr(ecxReg);
            if (ecx.isNull()) return;
            const ebxReg = this.context.ebx || this.context.rbx;
            if (!ebxReg) return;
            const npcBase = ptr(ebxReg);

            const npcPtr = safePtr(ecx.add(NPC_OFF));
            const npc = readUtf8Safe(npcPtr);

            const inlineBase = ecx.add(TXT_OFF);

            let dialog = readLines(inlineBase);

            if (!dialog) {{
                const arrPtr = safePtr(inlineBase);
                if (notNull(arrPtr))
                    dialog = readLines(arrPtr);
            }}

            if (!dialog) return;

            send({{
                type: "speech",
                npc: npc,
                text: dialog,
                npc_base: npcBase.toString(),
                x_addr: npcBase.add({NPC_VAR_OFFSET}).toString(),
                speech_addr: npcBase.add(0x28C).toString()
            }});
        }}
    }});

    send({{ type: "ready" }});
    """

    class _Deduper:
        def __init__(self, window_s=4.0):
            self.window = window_s
            self.seen = {}

        def accept(self, text, source=None):
            now = time.time()
            key = f"{str(source or '')}|{text}"
            last = self.seen.get(key)
            if last and (now - last) < self.window:
                return False
            self.seen[key] = now
            for k in list(self.seen):
                if now - self.seen[k] > self.window:
                    self.seen.pop(k, None)
            return True

    deduper = _Deduper()

    def _on_message(message, data):
        mtype = message.get("type")
        if mtype == "error":
            _log_info(f"[SPEECH][frida] {message.get('stack')}")
            return
        if mtype != "send":
            return

        payload = message.get("payload", {})

        payload_type = payload.get("type")
        payload_type_norm = str(payload_type).strip().lower() if payload_type is not None else None
        if payload_type_norm not in (None, "speech", "chat", "dialog"):
            return

        npc = (payload.get("npc") or payload.get("name") or "").strip()
        text = (payload.get("text") or payload.get("dialog") or payload.get("msg") or "").strip()
        x_addr_raw = payload.get("x_addr")
        speech_addr_raw = payload.get("speech_addr")

        dedupe_source = x_addr_raw or npc or ""
        if not text or not deduper.accept(text, source=dedupe_source):
            return

        ts = time.time()

        try:
            npc_key = None
            if x_addr_raw:
                try:
                    npc_key = hex(int(str(x_addr_raw), 16)).upper()
                except Exception:
                    npc_key = str(x_addr_raw).upper()
            elif speech_addr_raw:
                try:
                    npc_key = hex(int(str(speech_addr_raw), 16) - 0x1EC).upper()
                except Exception:
                    npc_key = None

            if npc and npc_key:
                source_label = f"{npc} [{npc_key}]"
            elif npc:
                source_label = npc
            elif npc_key:
                source_label = f"[{npc_key}]"
            else:
                source_label = "??"

            source_key = npc_key or npc or source_label
            recent_speech_log.append((ts, source_label, text))
            npc_last_speech[source_key] = {
                "text": text,
                "ts": ts,
                "npc": npc or None,
                "source_label": source_label,
            }

            if npc_key:
                try:
                    with manager._lock:
                        st = manager.addresses.get(npc_key)
                        if st is not None:
                            st["last_speech"] = text
                            st["last_speech_ts"] = ts
                            if npc:
                                st["name"] = npc
                except Exception:
                    pass
        except Exception:
            pass

        matched_trigger = next((pat for pat in TRIGGERS if re.search(pat, text, flags=re.IGNORECASE)), None)
        if matched_trigger:
            global speech_quarantine_until, speech_quarantine_reason, speech_quarantine_source, current_target_npc
            now_q = time.time()
            quarantine_s = float(SPEECH_QUARANTINE_SEC)
            source_disp = source_label if 'source_label' in locals() else (npc or "??")

            speech_quarantine_reason = text
            speech_quarantine_source = source_disp

            if now_q >= speech_quarantine_until:
                speech_quarantine_until = now_q + quarantine_s
                try:
                    release_key('ctrl')
                except Exception:
                    pass
                current_target_npc = None

    session = frida_attach_target()
    _load_frida_script(session, FRIDA_JS, _on_message, label="speech-monitor")

    try:
        while True:
            time.sleep(1.0)
    except Exception:
        pass

OTHER_PLAYER_X_OFFSET = 0x150
OTHER_PLAYER_Y_OFFSET = 0x152
FACING_OFFSET = 0x15C
LEVEL_OFFSET = 0x68
NAME_PTR_OFFSET = 0x1C

other_player_addresses = {}     # All discovered X addresses
self_player_address = None      # Identified self structure
self_player_name = None         # Stable self identity key across shifting addresses
self_player_last_seen_ts = 0.0  # Last tick we confirmed current self address
position_match_count = {}       # Track match frequency for self detection

def _player_name_key(name: Any) -> str:
    """Normalize player name for stable comparisons."""
    if not name:
        return ""
    return re.sub(r"\s+", " ", str(name)).strip().casefold()

def _read_other_player_meta(addr_hex: str) -> Dict[str, Any]:
    """Best-effort read of other-player metadata from struct base."""
    out: Dict[str, Any] = {}
    try:
        if pm is None:
            return out

        ax = int(addr_hex, 16)
        base_addr = ax - OTHER_PLAYER_X_OFFSET
        if base_addr <= 0x10000:
            return out

        try:
            facing = int(pm.read_uchar(base_addr + FACING_OFFSET))
            if 0 <= facing <= 7:
                out["facing"] = facing
        except Exception:
            pass

        try:
            level = int(pm.read_short(base_addr + LEVEL_OFFSET))
            if 0 <= level <= 999:
                out["level"] = level
        except Exception:
            pass

        try:
            name_ptr = int(pm.read_int(base_addr + NAME_PTR_OFFSET))
            if name_ptr > 0x10000:
                raw = pm.read_bytes(name_ptr, 32)
                name = raw.split(b"\x00", 1)[0].decode("utf-8", errors="ignore").strip()
                name = re.sub(r"[\x00-\x1F]+", "", name)
                if name:
                    out["name"] = name
        except Exception:
            pass

    except Exception:
        pass

    return out

def _add_other_player_address(addr_hex):
    """Store a found player X address"""

    if addr_hex not in other_player_addresses:
        other_player_addresses[addr_hex] = True
        position_match_count[addr_hex] = 0

    addr_int = int(addr_hex, 16)
    y_hex = hex(addr_int + 2).upper()

    with other_players_lock:
        if addr_hex not in other_players:
            meta = _read_other_player_meta(addr_hex)
            other_players[addr_hex] = {
                "paired_address": y_hex,
                "last_x": None,
                "last_y": None,
                "last_seen": time.time(),
                "name": meta.get("name"),
                "level": meta.get("level"),
                "facing": meta.get("facing"),
                "meta_refresh_due": 0.0,
            }

def on_message_other_players(message, data):
    """Callback for other-player hook messages"""

    if message['type'] != 'send':
        return

    payload = message.get('payload', {})
    addr_hex = payload.get('address')

    if not addr_hex:
        return

    addr_hex = addr_hex.upper()
    _add_other_player_address(addr_hex)

def start_frida_other_players():
    """
    Hooks:
        mov [ecx+150], dx

    Uses AOB-resolved RVA (otherPlayersAddress).
    Tracks ALL players including self.
    """

    global otherPlayersAddress

    if not isinstance(otherPlayersAddress, int):
        _log_warn("[OTHER_PLAYERS] Invalid RVA type:", type(otherPlayersAddress))
        return

    try:
        session = frida_attach_target()

        script_code = f"""
        var mod = Process.getModuleByName("Endless.exe");
        var base = mod.base;

        var target = base.add(ptr("{hex(otherPlayersAddress)}"));
        var seen = Object.create(null);

        function isReadable(addr) {{
            try {{
                var range = Process.findRangeByAddress(addr);
                return !!range && range.protection.indexOf('r') !== -1;
            }} catch (_) {{
                return false;
            }}
        }}

        Interceptor.attach(target, {{
            onEnter: function () {{
                try {{
                    // Hook target is: mov [ecx+150], dx
                    // Capture X-coordinate address as (ecx + 0x150).
                    var ecx = this.context.ecx || this.context.rcx;
                    if (!ecx) return;

                    var xAddr = ptr(ecx).add({OTHER_PLAYER_X_OFFSET});
                    if (xAddr.compare(ptr("0x10000")) < 0) return;
                    if (!isReadable(xAddr)) return;

                    var addrHex = xAddr.toString().toUpperCase();
                    if (seen[addrHex]) return;
                    seen[addrHex] = 1;

                    send({{ address: addrHex }});
                }} catch (_) {{
                    // swallow errors in hot hook to avoid destabilizing target
                }}
            }}
        }});
        """

        _load_frida_script(session, script_code, on_message_other_players, label="other-players")

    except Exception as e:
        _log_warn(f"[frida][other_players] Failed to start: {e}")
CURRENT_HP = None  # Updated by Frida hook
CURRENT_MANA = None  # Updated by Frida hook

def read_current_hp():
    """Return current HP from Frida hook."""
    global CURRENT_HP
    return CURRENT_HP

def read_current_mana():
    """Return current mana from Frida hook."""
    global CURRENT_MANA
    return CURRENT_MANA

class PlayerDataManager:
    def __init__(self):
        self._lock = threading.Lock()
        self.data = {
            "x": 0,
            "y": 0,
            "direction": 0
        }

    def update(self, x, y, direction):
        with self._lock:
            self.data["x"] = x
            self.data["y"] = y
            self.data["direction"] = direction

    def get_data(self):
        with self._lock:
            return dict(self.data)

def force_weight_zero():
    global stat_base, pm
    try:
        if not stat_base:
            return False

        weight_addr = stat_base + STAT_OFFSETS['weight']
        pm.write_int(weight_addr, 0)
        return True
    except Exception:
        return False

_weight_lock_running = False

def _weight_lock_loop():
    global _weight_lock_running
    while _weight_lock_running:
        if bot_running and stat_base:
            force_weight_zero()
            time.sleep(0.02)  # 50 times per second while actively running
        else:
            time.sleep(0.20)  # idle when bot is stopped/not initialized

def start_weight_lock():
    global _weight_lock_running
    if _weight_lock_running:
        return
    _weight_lock_running = True
    threading.Thread(target=_weight_lock_loop, daemon=True).start()
    _log_info("[WEIGHT] Dynamic weight lock active.")

class AddressManager:
    def __init__(self):
        self.addresses = {}
        self._protection_default = 3  # seconds
        self.ignore_protection = False
        self._lock = threading.Lock()
        self._removal_history = []
        self._history_max = 50

    def add_address(self, address):
        address1 = int(address, 16)
        address2 = address1 + 2
        address1_hex = hex(address1).upper()
        address2_hex = hex(address2).upper()
        with self._lock:
            if address1_hex not in self.addresses:
                self.addresses[address1_hex] = {
                    "paired_address": address2_hex,
                    "last_x": None,
                    "last_y": None,
                    "last_moved": time.time(),
                    "is_dead_counter": 0,
                    "last_is_dead_value": None,
                    "first_seen_ts": time.time(),
                    "oob_strikes": 0,
                    "last_good_xy": None,
                    "last_unique_id": None,
                    "got_hit": None,
                    "protected_until": None,
                    "protected_cleared_at": None,
                }
                return True
            return False

    def set_ignore_protection(self, flag: bool):
        self.ignore_protection = bool(flag)

    def is_protected(self, addr_hex: str) -> bool:
        if IGNORE_PROTECTION:
            return False
        if self.ignore_protection:
            return False
        with self._lock:
            st = self.addresses.get(addr_hex)
        if not st:
            return False
        now = time.time()
        pu = st.get("protected_until")
        if pu and now < pu:
            return True
        with self._lock:
            if pu and now >= pu:
                st["protected_until"] = None
                st["protected_cleared_at"] = now
            pc = st.get("protected_cleared_at")
        if pc and (now - pc) < POST_PROTECT_GRACE_S:
            return True
        return False

    def mark_protected(self, addr_hex: str, seconds: Optional[int] = None, reason: str = "got_hit", meta: Optional[Dict[str, Any]] = None):

        secs = seconds if seconds is not None else self._protection_default
        with self._lock:
            st = self.addresses.get(addr_hex)
            if not st:
                return False
            st["protected_until"] = time.time() + max(1, secs)
            st["protected_cleared_at"] = None
            self._log_removal(addr_hex, f"protected:{reason}", meta or {}, dict(st))
            return True

    def protection_seconds_left(self, addr_hex: str) -> int:
        with self._lock:
            st = self.addresses.get(addr_hex)
        if not st or not st.get("protected_until"):
            return 0
        return max(0, int(st["protected_until"] - time.time()))

    def remove_address(self, address, reason: str = "unspecified", meta: Optional[Dict[str, Any]] = None):

        address1 = int(address, 16)
        address1_hex = hex(address1).upper()
        with self._lock:
            if address1_hex in self.addresses:
                last_state = dict(self.addresses[address1_hex])
                del self.addresses[address1_hex]
                self._log_removal(address1_hex, reason, meta or {}, last_state)
                return True
            return False

    def list_addresses(self):
        with self._lock:
            return [{"X": x, "Y": data["paired_address"]} for x, data in self.addresses.items()]

    def _log_removal(self, addr_hex: str, reason: str, meta: Optional[Dict[str, Any]] = None, last_state: Optional[Dict[str, Any]] = None):

        entry = {
            "ts": time.time(),
            "address": addr_hex,
            "reason": reason,
            "meta": meta or {},
            "last_state": last_state or {},
        }
        self._removal_history.append(entry)
        if len(self._removal_history) > self._history_max:
            self._removal_history = self._removal_history[-self._history_max:]

    def get_removal_history(self):
        with self._lock:
            return list(self._removal_history)
class MapDataIndexer:
    """Maintains indexed view of map_data for O(1) lookups instead of O(n) linear searches."""
    def __init__(self):
        self.all_data = []
        self._player = None
        self._npcs = []
        self._other_players = []
        self._npc_by_addr = {}
    
    def update(self, items):
        """Rebuild indices from new data. Call whenever map_data changes."""
        self.all_data = items
        self._player = None
        self._npcs = []
        self._other_players = []
        self._npc_by_addr = {}
        
        for item in items:
            item_type = item.get('type')
            if item_type == 'player':
                self._player = item
            elif item_type == 'other_player':
                self._other_players.append(item)
            elif item_type == 'npc':
                addr = item.get('address_x')
                if addr:
                    self._npc_by_addr[addr] = item
                self._npcs.append(item)
    
    def get_player(self):
        """Get player data in O(1)."""
        return self._player
    
    def get_npcs(self):
        """Get all NPCs in O(1)."""
        return self._npcs

    def get_other_players(self):
        """Get all other players in O(1)."""
        return self._other_players
    
    def get_npc_by_addr(self, addr):
        """Get NPC by address in O(1)."""
        return self._npc_by_addr.get(addr)

def _get_map_version() -> int:
    with map_data_lock:
        return int(MAP_DATA_VERSION)

def _get_map_snapshot() -> Tuple[int, List[Dict[str, Any]]]:
    with map_data_lock:
        return int(MAP_DATA_VERSION), list(map_data)

def _get_map_snapshot_if_changed(last_version: int) -> Tuple[int, Optional[List[Dict[str, Any]]]]:
    with map_data_lock:
        current = int(MAP_DATA_VERSION)
        if int(last_version) == current:
            return current, None
        return current, list(map_data)

def _publish_map_frame(frame: List[Dict[str, Any]]) -> bool:
    global MAP_DATA_VERSION
    with map_data_lock:
        if map_data != frame:
            map_data[:] = frame
            MAP_DATA_VERSION += 1
            return True
        return False

def _get_other_players_snapshot() -> List[Tuple[str, Dict[str, Any]]]:
    with other_players_lock:
        return [(addr, dict(meta)) for addr, meta in other_players.items()]

def _get_other_player_meta(addr_hex: str) -> Dict[str, Any]:
    key = (addr_hex or "").upper()
    with other_players_lock:
        return dict(other_players.get(key, {}))

def _update_other_player_meta(addr_hex: str, updates: Dict[str, Any]) -> bool:
    key = (addr_hex or "").upper()
    if not updates:
        return False
    with other_players_lock:
        st = other_players.get(key)
        if st is None:
            return False
        st.update(updates)
        return True

def _pop_other_player(addr_hex: str):
    key = (addr_hex or "").upper()
    with other_players_lock:
        other_players.pop(key, None)

def _get_runtime_flags() -> Dict[str, Any]:
    with _RUNTIME_STATE_LOCK:
        return {
            "bot_running": bool(bot_running),
            "attack_active": bool(ATTACK_ACTIVE),
            "no_click_until": float(NO_CLICK_UNTIL),
            "target_pid": int(TARGET_PID) if TARGET_PID is not None else None,
            "movement_allowed": bool(movement_allowed.is_set()),
            "clicks_in_progress": bool(clicks_in_progress.is_set()),
            "home_running": bool(home_routine_running.is_set()),
        }

def _set_current_map_id(value: Optional[int]) -> Optional[int]:
    global CURRENT_MAP_ID, LAST_MAP_ID_TS
    out: Optional[int] = None
    try:
        if value is not None:
            out = int(value)
    except Exception:
        out = None
    with _MAP_ID_LOCK:
        CURRENT_MAP_ID = out
        LAST_MAP_ID_TS = time.time()
    return out

def _get_current_map_id() -> Optional[int]:
    with _MAP_ID_LOCK:
        return CURRENT_MAP_ID

def _set_walkable_source_state(mode: str, *, message: str = "", path: Optional[Union[str, Path]] = None):
    global WALKABLE_SOURCE_MODE, WALKABLE_SOURCE_MESSAGE, WALKABLE_SOURCE_PATH
    resolved_path: Optional[str] = None
    if path is not None:
        try:
            resolved_path = str(Path(path).resolve())
        except Exception:
            resolved_path = str(path)
    with _WALKABLE_SOURCE_LOCK:
        WALKABLE_SOURCE_MODE = str(mode)
        WALKABLE_SOURCE_MESSAGE = str(message or "")
        WALKABLE_SOURCE_PATH = resolved_path

def _get_walkable_source_state() -> Tuple[str, str, Optional[str]]:
    with _WALKABLE_SOURCE_LOCK:
        return (
            str(WALKABLE_SOURCE_MODE),
            str(WALKABLE_SOURCE_MESSAGE or ""),
            WALKABLE_SOURCE_PATH,
        )

manager = AddressManager()
player_data_manager = PlayerDataManager()
map_data = []
MAP_DATA_VERSION = 0
MAP_INFO_ENTITIES = [] # Decoded entities from 0x2B packets
map_data_indexer = MapDataIndexer()  # Indexed view for fast lookups

class ScrollableFrame(ttk.Frame):

    """A vertical scrollable frame for stacking sections in a single column."""
    def __init__(self, parent, **kwargs):
        super().__init__(parent, **kwargs)
        self.canvas = tk.Canvas(self, borderwidth=0, highlightthickness=0)
        self.vbar = ttk.Scrollbar(self, orient="vertical", command=self.canvas.yview)
        self.interior = ttk.Frame(self.canvas)

        self.canvas.configure(yscrollcommand=self.vbar.set)

        self._win_id = self.canvas.create_window((0, 0), window=self.interior, anchor="nw")

        self.canvas.grid(row=0, column=0, sticky="nsew")
        self.vbar.grid(row=0, column=1, sticky="ns")

        self.rowconfigure(0, weight=1)
        self.columnconfigure(0, weight=1)

        def _on_interior_configure(event):
            self.canvas.configure(scrollregion=self.canvas.bbox("all"))
            self.canvas.itemconfigure(self._win_id, width=self.canvas.winfo_width())
        self.interior.bind("<Configure>", _on_interior_configure)

        def _on_canvas_configure(event):
            self.canvas.itemconfigure(self._win_id, width=event.width)
        self.canvas.bind("<Configure>", _on_canvas_configure)

        self.canvas.bind("<Enter>", self._bind_wheel)
        self.canvas.bind("<Leave>", self._unbind_wheel)

    def _bind_wheel(self, _):
        self.canvas.bind_all("<MouseWheel>", self._on_mousewheel)
        self.canvas.bind_all("<Button-4>", self._on_mousewheel_linux)
        self.canvas.bind_all("<Button-5>", self._on_mousewheel_linux)

    def _unbind_wheel(self, _):
        self.canvas.unbind_all("<MouseWheel>")
        self.canvas.unbind_all("<Button-4>")
        self.canvas.unbind_all("<Button-5>")

    def _on_mousewheel(self, event):
        self.canvas.yview_scroll(-1 * (event.delta // 120 if event.delta else 1), "units")

    def _on_mousewheel_linux(self, event):
        self.canvas.yview_scroll(-1 if event.num == 4 else 1, "units")

class PlayerDataPopup:
    """
    Large single-file GUI controller.

    Section map:
    1) Lifecycle / window state
    2) Window placement + persistence helpers
    3) UI construction + hotkey tab
    4) Config mutation helpers + setting handlers
    5) Styling + refresh/render helpers
    6) Map interaction helpers
    7) Runtime bot action handlers
    """
    def __init__(self, player_data_manager):
        self.player_data_manager = player_data_manager
        self.root = ThemedTk(theme="black")
        self.root.title("Bot Control Panel")
        
        self.root.configure(bg='#1a1f2e')
        self.root.option_add('*Background', '#1a1f2e')
        
        self.ignore_prot_var = tk.BooleanVar(value=IGNORE_PROTECTION)

        self._map_tile_w = 64
        self._map_grid_radius = 8
        if AUTO_LOAD_MAP_BY_ID:
            self._walkable_path = _resolve_walkable_path(WALKABLE_ARG)
            if self._walkable_path is None:
                self._walkable_path = APP_BASE_DIR / "walkable.json"
        else:
            self._walkable_path = (APP_BASE_DIR / "walkable.json").resolve()
        self._walkable_coords_cache = load_walkable_tiles(str(self._walkable_path))
        self._walkable_map_paths: Dict[str, Path] = {}
        self._walkable_map_syncing = False
        self._walkable_recording = False
        self._walkable_record_tiles: Set[Tuple[int, int]] = set()
        self._walkable_record_lock = threading.Lock()
        self._walkable_record_started_at: Optional[float] = None
        self._walkable_record_last_elapsed_s = 0
        self._walkable_record_last_tile: Optional[Tuple[int, int]] = None
        self._config_paths: Dict[str, Path] = {}
        self._config_syncing = False
        self._last_seen_map_id: Optional[int] = None
        self._last_auto_loaded_map_id: Optional[int] = None
        self._walkable_default_warning_text = (
            "WARNING: using default grid. Please enable auto load or select JSON from Walkable Maps tab."
        )
        self._hovered_tile = None
        self._dragging = False
        self._drag_mode = None
        self._dragged_tiles = set()
        self._drag_start_tile = None
        self._last_drag_tile = None
        self._last_map_draw = 0.0
        self._last_runtime_update = 0.0
        self._last_stats_update = 0.0
        self._last_other_players_update = 0.0
        self._last_chat_update = 0.0
        self._last_chat_snapshot = []
        self._last_map_signature = None
        self._last_map_mouse_ts = 0.0
        self._map_mouse_interval_s = 1.0 / 60.0
        self._session_exp_active = False
        self._session_exp_started_at = None
        self._session_exp_total = 0
        self._session_exp_last_value = None
        self._stop_in_progress = False
        self._close_in_progress = False
        self._ui_running = True
        self._ui_cache = {}

        self.root.geometry("1120x720")   # initial size (taller? bump second number)
        self.root.minsize(980, 620)      # keeps panes from collapsing
        self.root.resizable(True, True)

        self.labels = {}
        self.stats_labels = {}

        self.boss_aggro_var = tk.BooleanVar(value=BOSS_AGGRO_TOGGLE)
        self.avoid_players_var = tk.BooleanVar(value=AVOID_OTHER_PLAYERS)
        self.hp_home_toggle_var = tk.BooleanVar(value=HP_HOME_ENABLED)

        if START_MAP_ID is not None:
            try:
                _set_current_map_id(int(START_MAP_ID))
            except Exception:
                pass

        self.create_widgets()
        self.create_styles()  
        self.update_ui()
        self._refresh_protection_status()
        self._place_left_center()
        self.root.after_idle(self._place_left_center)

        self.root.bind("<F12>", self._bring_to_front)
        self.root.after(0, self._ensure_visible)
        self.root.after(50, self._bring_to_front)

        self.root.protocol("WM_DELETE_WINDOW", self.on_closing)

        global BOT_GUI
        BOT_GUI = self

    def _save_walkable_tiles(self):
        """Persist current walkable cache to the currently loaded walkable JSON."""
        try:
            path = self._walkable_path
            path.parent.mkdir(parents=True, exist_ok=True)
            payload = {
                "safe_tiles": [
                    {"X": int(x), "Y": int(y)}
                    for (x, y) in sorted(self._walkable_coords_cache, key=lambda t: (t[0], t[1]))
                ]
            }
            with path.open("w", encoding="utf-8") as f:
                json.dump(payload, f, indent=2)
            _invalidate_walkable_cache()
            _set_walkable_source_state("file", path=path)
        except Exception as e:
            _log_warn(f"[WALKABLE] Failed to save {self._walkable_path}: {e}")

    def _load_walkable_tiles_strict(self, path: Path) -> Set[Tuple[int, int]]:
        """Strict loader for GUI-selected walkable files."""
        with path.open("r", encoding="utf-8") as f:
            data = json.load(f)
        return self._extract_walkable_tiles_payload(data)

    def _extract_walkable_tiles_payload(self, data: Any) -> Set[Tuple[int, int]]:
        if not isinstance(data, dict):
            raise ValueError("JSON root must be an object.")

        def normalize(raw_tiles: Any) -> Set[Tuple[int, int]]:
            out: Set[Tuple[int, int]] = set()
            if not isinstance(raw_tiles, list):
                return out
            for tile in raw_tiles:
                try:
                    if isinstance(tile, dict):
                        xv = tile.get("X", tile.get("x"))
                        yv = tile.get("Y", tile.get("y"))
                        if xv is None or yv is None:
                            continue
                        out.add((int(xv), int(yv)))
                    elif isinstance(tile, (list, tuple)) and len(tile) >= 2:
                        out.add((int(tile[0]), int(tile[1])))
                except Exception:
                    continue
            return out

        for key in ("safe_tiles", "walkable_tiles", "tiles"):
            if key in data:
                raw = data.get(key)
                if not isinstance(raw, list):
                    raise ValueError(f"'{key}' must be a list.")
                return normalize(raw)

        raise ValueError("Missing walkable tile list (expected safe_tiles/walkable_tiles/tiles).")

    def _is_walkable_json_file(self, path: Path) -> bool:
        try:
            with path.open("r", encoding="utf-8") as f:
                data = json.load(f)
            self._extract_walkable_tiles_payload(data)
            return True
        except Exception:
            return False

    def _extract_map_id_from_filename(self, path: Path) -> Optional[int]:
        stem = str(path.stem or "").strip()
        if not stem:
            return None
        m = re.match(r"^\s*(\d+)", stem)
        if m:
            try:
                return int(m.group(1))
            except Exception:
                return None
        m = re.search(r"(\d+)", stem)
        if m:
            try:
                return int(m.group(1))
            except Exception:
                return None
        return None

    def _find_walkable_map_by_map_id(self, map_id: int) -> Optional[Path]:
        try:
            target = int(map_id)
        except Exception:
            return None
        if target <= 0:
            return None

        maps_dir = WALKABLE_MAPS_DIR
        if not maps_dir.is_dir():
            return None

        candidates = sorted([p for p in maps_dir.glob("*.json") if p.is_file()], key=lambda p: p.name.lower())
        exact_prefix: List[Path] = []
        fuzzy_match: List[Path] = []

        id_txt = str(target)
        for p in candidates:
            stem = p.stem
            if re.match(rf"^\s*{re.escape(id_txt)}(\D|$)", stem):
                exact_prefix.append(p)
                continue
            parsed = self._extract_map_id_from_filename(p)
            if parsed == target:
                fuzzy_match.append(p)

        if exact_prefix:
            for p in exact_prefix:
                if self._is_walkable_json_file(p):
                    return p
            return exact_prefix[0]
        if fuzzy_match:
            for p in fuzzy_match:
                if self._is_walkable_json_file(p):
                    return p
            return fuzzy_match[0]
        return None

    def _list_walkable_json_files(self) -> List[Path]:
        out: List[Path] = []
        seen: Set[str] = set()

        def _walkable_name_sort_key(p: Path):
            name = str(p.name or "").strip().lower()
            starts_num = bool(name) and name[0].isdigit()
            if not starts_num:
                return (0, name)
            m = re.match(r"^\s*(\d+)", name)
            if m:
                return (1, int(m.group(1)), name)
            return (1, 10**12, name)

        def _append_if_new(p: Path):
            try:
                key = str(p.resolve()).lower()
            except Exception:
                key = str(p).lower()
            if key in seen:
                return
            seen.add(key)
            out.append(p)

        maps_dir = WALKABLE_MAPS_DIR
        if maps_dir.is_dir():
            for p in sorted([p for p in maps_dir.glob("*.json") if p.is_file()], key=_walkable_name_sort_key):
                if self._is_walkable_json_file(p):
                    _append_if_new(p)

        fallback = (APP_BASE_DIR / "walkable.json")
        if fallback.is_file():
            _append_if_new(fallback)

        if self._walkable_path and self._walkable_path.is_file():
            _append_if_new(self._walkable_path)

        return sorted(out, key=_walkable_name_sort_key)

    def _refresh_walkable_map_choices(self):
        if not hasattr(self, "walkable_map_combo"):
            return

        paths = self._list_walkable_json_files()
        label_to_path: Dict[str, Path] = {}
        labels: List[str] = []
        for p in paths:
            label = p.name
            if label in label_to_path:
                label = str(p)
            labels.append(label)
            label_to_path[label] = p
        self._walkable_map_paths = label_to_path
        self.walkable_map_combo["values"] = labels

        active_label = ""
        try:
            current = self._walkable_path.resolve()
            for lbl, path in label_to_path.items():
                if path.resolve() == current:
                    active_label = lbl
                    break
        except Exception:
            pass
        if not active_label and labels:
            active_label = labels[0]

        self._walkable_map_syncing = True
        try:
            self.walkable_map_var.set(active_label)
        finally:
            self._walkable_map_syncing = False

        if active_label and active_label in label_to_path:
            active_name = label_to_path[active_label].name
            self.walkable_active_label.config(text=f"Active: {active_name}", foreground="green")
        else:
            self.walkable_active_label.config(text="Active: (none)", foreground="red")

    def _apply_walkable_map_path(self, path: Path, *, show_errors: bool = True) -> bool:
        try:
            resolved = path.resolve()
            tiles = self._load_walkable_tiles_strict(resolved)
        except Exception as e:
            if show_errors:
                messagebox.showerror(
                    "Invalid Walkable Map",
                    f"Could not load '{path.name}' as a walkable map.\n\n{e}",
                )
            _log_warn(f"[WALKABLE] Failed to load '{path}': {e}")
            return False

        global WALKABLE_ARG
        self._walkable_path = resolved
        self._walkable_coords_cache = set(tiles)
        WALKABLE_ARG = str(resolved)
        os.environ["WALKABLE_JSON"] = str(resolved)
        _invalidate_walkable_cache()
        _set_walkable_source_state("file", path=resolved)
        self._last_map_signature = None

        if hasattr(self, "walkable_active_label"):
            self.walkable_active_label.config(text=f"Active: {resolved.name}", foreground="green")
        if hasattr(self, "walkable_map_var"):
            for lbl, p in self._walkable_map_paths.items():
                try:
                    if p.resolve() == resolved:
                        self._walkable_map_syncing = True
                        try:
                            self.walkable_map_var.set(lbl)
                        finally:
                            self._walkable_map_syncing = False
                        break
                except Exception:
                    continue
        try:
            self.draw_map()
        except Exception:
            pass
        self._refresh_walkable_warning_label()
        _log_info(f"[WALKABLE] Active map set to '{resolved.name}'")
        return True

    def _on_walkable_map_selected(self, _event=None):
        if self._walkable_map_syncing:
            return
        if self._walkable_recording:
            messagebox.showinfo("Recording Active", "Stop recording before switching maps.")
            self._refresh_walkable_map_choices()
            return
        selected = self.walkable_map_var.get().strip()
        target = self._walkable_map_paths.get(selected)
        if not target:
            return
        if not self._apply_walkable_map_path(target):
            self._refresh_walkable_map_choices()

    def _load_default_walkable_grid(self):
        fallback = (APP_BASE_DIR / "walkable.json").resolve()
        global WALKABLE_ARG
        self._walkable_path = fallback
        WALKABLE_ARG = str(fallback)
        os.environ["WALKABLE_JSON"] = str(fallback)
        self._walkable_coords_cache = load_walkable_tiles(str(fallback))
        _invalidate_walkable_cache()
        self._last_map_signature = None
        try:
            self.draw_map()
        except Exception:
            pass
        self._refresh_walkable_warning_label()

    def _apply_manual_walkable_fallback_mode(self):
        """When auto map-id loading is disabled, use walkable.json beside bot or default grid."""
        fallback = (APP_BASE_DIR / "walkable.json").resolve()
        if fallback.is_file():
            self._apply_walkable_map_path(fallback, show_errors=False)
        else:
            self._load_default_walkable_grid()

    def _attempt_auto_map_load(
        self,
        map_id: Optional[int],
        *,
        force: bool = False,
        ignore_toggle: bool = False,
    ):
        if self._walkable_recording:
            return
        if (not ignore_toggle) and (not AUTO_LOAD_MAP_BY_ID):
            return
        if map_id is None:
            return
        try:
            map_id_int = int(map_id)
        except Exception:
            return
        if map_id_int <= 0:
            return
        if (not force) and self._last_auto_loaded_map_id == map_id_int:
            return

        target = self._find_walkable_map_by_map_id(map_id_int)
        if target is not None:
            if self._apply_walkable_map_path(target, show_errors=False):
                self._last_auto_loaded_map_id = map_id_int
                _log_info(f"[WALKABLE] Auto-loaded map {target.name} for map ID {map_id_int}")
                return
            _log_warn(f"[WALKABLE] Map-id candidate '{target.name}' is not a valid walkable map; falling back.")

        fallback = (APP_BASE_DIR / "walkable.json").resolve()
        if fallback.is_file():
            if self._apply_walkable_map_path(fallback, show_errors=False):
                self._last_auto_loaded_map_id = map_id_int
                _log_warn(f"[WALKABLE] No map-id JSON for {map_id_int}; using walkable.json")
                return

        self._load_default_walkable_grid()
        self._last_auto_loaded_map_id = map_id_int
        _set_walkable_source_state("default_grid", message=self._walkable_default_warning_text, path=fallback)
        _log_warn(f"[WALKABLE] No map-id JSON for {map_id_int} and no walkable.json; using default grid.")

    def _refresh_map_id_ui_and_autoload(self):
        map_id = _get_current_map_id()
        if map_id != self._last_seen_map_id:
            self._last_seen_map_id = map_id
            if hasattr(self, "map_id_value_label"):
                text = str(map_id) if map_id is not None else "?"
                color = "white" if map_id is not None else "#ffcc66"
                self.map_id_value_label.config(text=text, foreground=color)

        if AUTO_LOAD_MAP_BY_ID and map_id is not None:
            self._attempt_auto_map_load(map_id, force=False)

    def _refresh_walkable_warning_label(self):
        if not hasattr(self, "walkable_warning_label"):
            return
        mode, message, _ = _get_walkable_source_state()
        if mode == "default_grid":
            text = message or self._walkable_default_warning_text
            self._set_label_cached("walkable:warn", self.walkable_warning_label, text, "#ffb347")
        else:
            self._set_label_cached("walkable:warn", self.walkable_warning_label, "", "#ffb347")

    def on_auto_map_id_toggle(self):
        enabled = bool(self.auto_mapid_var.get())
        _set_config_value(CFG_AUTO_LOAD_MAP_BY_ID, enabled)
        self._last_auto_loaded_map_id = None
        if enabled:
            self._attempt_auto_map_load(_get_current_map_id(), force=True)
            _log_info("[GUI] Auto-load by Map ID ENABLED")
        else:
            self._apply_manual_walkable_fallback_mode()
            _log_info("[GUI] Auto-load by Map ID DISABLED")
        self._refresh_walkable_warning_label()
        save_settings()

    def on_auto_load_current_map_id(self):
        map_id = _get_current_map_id()
        if map_id is None:
            messagebox.showwarning("Map ID Missing", "Map ID is not available yet.")
            return
        self._attempt_auto_map_load(map_id, force=True)

    def on_manual_load_map_id(self, event=None):
        raw = ""
        try:
            raw = self.manual_map_id_var.get().strip()
        except Exception:
            raw = ""
        if not raw:
            messagebox.showwarning("Map ID Required", "Enter a map ID number first.")
            return
        try:
            map_id = int(raw)
        except Exception:
            messagebox.showwarning("Invalid Map ID", "Map ID must be an integer.")
            return
        if map_id <= 0:
            messagebox.showwarning("Invalid Map ID", "Map ID must be > 0.")
            return
        _set_current_map_id(map_id)
        _set_config_value(CFG_START_MAP_ID, map_id)
        save_settings()
        self._attempt_auto_map_load(map_id, force=True, ignore_toggle=True)

    def _walkable_record_loop(self):
        while self._walkable_recording and self._ui_running:
            x, y = _get_xy_safe()
            if isinstance(x, int) and isinstance(y, int):
                if 0 < x <= INVALID_COORD_LIMIT and 0 < y <= INVALID_COORD_LIMIT:
                    added = False
                    count = 0
                    with self._walkable_record_lock:
                        tile = (int(x), int(y))
                        before = len(self._walkable_record_tiles)
                        self._walkable_record_tiles.add(tile)
                        count = len(self._walkable_record_tiles)
                        added = (count != before)
                        if added:
                            self._walkable_record_last_tile = tile
                    if added:
                        self._run_on_ui_thread(
                            lambda tx=int(x), ty=int(y), cnt=count: self._on_walkable_tile_captured(tx, ty, cnt)
                        )
            time.sleep(0.20)

    def _on_walkable_record_start(self):
        if self._walkable_recording:
            return

        if bot_running:
            self.on_stop_bot()

        x, y = _get_xy_safe()
        if x is None or y is None:
            messagebox.showwarning(
                "Recorder Unavailable",
                "Player coordinates are not ready yet.\nWait for startup hooks, then try again.",
            )
            return

        with self._walkable_record_lock:
            first_tile = (int(x), int(y))
            self._walkable_record_tiles = {first_tile}
            self._walkable_record_last_tile = first_tile
        self._walkable_record_started_at = time.time()
        self._walkable_record_last_elapsed_s = 0
        self._walkable_recording = True

        self.walkable_record_start_btn.config(state=tk.DISABLED)
        self.walkable_record_stop_btn.config(state=tk.NORMAL)
        self.walkable_map_combo.config(state="disabled")
        self.walkable_refresh_btn.config(state=tk.DISABLED)
        self.walkable_record_status_label.config(
            text=f"Recording safe tiles... Unique: 1 | Last: ({int(x)}, {int(y)})",
            foreground="green",
        )
        self._refresh_walkable_record_status()
        _log_info("[WALKABLE] Recording started from GUI.")
        threading.Thread(target=self._walkable_record_loop, daemon=True).start()

    def _on_walkable_tile_captured(self, x: int, y: int, count: int):
        if not self._walkable_recording:
            return
        self.walkable_record_status_label.config(
            text=f"Recording safe tiles... Unique: {count} | Last: ({x}, {y})",
            foreground="green",
        )
        self._refresh_walkable_record_status()

    def _unique_walkable_save_path(self, path: Path) -> Path:
        if not path.exists():
            return path
        stem, suffix = path.stem, path.suffix or ".json"
        i = 1
        while True:
            candidate = path.with_name(f"{stem} ({i}){suffix}")
            if not candidate.exists():
                return candidate
            i += 1

    def _on_walkable_record_stop(self):
        if not self._walkable_recording:
            return

        self._walkable_recording = False
        if self._walkable_record_started_at is not None:
            self._walkable_record_last_elapsed_s = max(
                0, int(time.time() - self._walkable_record_started_at)
            )

        self.walkable_record_start_btn.config(state=tk.NORMAL)
        self.walkable_record_stop_btn.config(state=tk.DISABLED)
        self.walkable_map_combo.config(state="readonly")
        self.walkable_refresh_btn.config(state=tk.NORMAL)

        with self._walkable_record_lock:
            tiles = sorted(self._walkable_record_tiles, key=lambda t: (t[0], t[1]))
        if not tiles:
            self.walkable_record_status_label.config(
                text="Recording stopped with 0 tiles; nothing saved.",
                foreground="orange",
            )
            _log_warn("[WALKABLE] Recording stopped with no tiles.")
            return

        default_name = f"walkable-{time.strftime('%Y%m%d-%H%M%S')}"
        entered = simpledialog.askstring(
            "Save Walkable Map",
            "Save map as (name only, .json optional):",
            initialvalue=default_name,
            parent=self.root,
        )
        if entered is None:
            self.walkable_record_status_label.config(
                text="Recording stopped. Save canceled.",
                foreground="orange",
            )
            _log_info("[WALKABLE] Recording save canceled by user.")
            return

        map_name = entered.strip() or default_name
        if not map_name.lower().endswith(".json"):
            map_name = f"{map_name}.json"
        target_dir = APP_BASE_DIR if map_name.lower() == "walkable.json" else WALKABLE_MAPS_DIR
        target_dir.mkdir(parents=True, exist_ok=True)
        save_path = (target_dir / map_name).resolve()
        if save_path.exists():
            overwrite = messagebox.askyesno(
                "Overwrite Map?",
                f"'{save_path.name}' already exists.\nOverwrite it?",
                parent=self.root,
            )
            if not overwrite:
                save_path = self._unique_walkable_save_path(save_path)

        payload = {
            "safe_tiles": [
                {"X": int(xv), "Y": int(yv)}
                for (xv, yv) in tiles
            ]
        }
        try:
            with save_path.open("w", encoding="utf-8") as f:
                json.dump(payload, f, indent=2)
        except Exception as e:
            messagebox.showerror("Save Failed", f"Could not save map:\n{e}")
            self.walkable_record_status_label.config(text="Save failed.", foreground="red")
            _log_warn(f"[WALKABLE] Save failed for '{save_path}': {e}")
            return

        self.walkable_record_status_label.config(
            text=f"Saved {len(tiles)} unique tiles to {save_path.name}",
            foreground="green",
        )
        _log_info(f"[WALKABLE] Saved {len(tiles)} unique tiles to '{save_path}'")

        self._refresh_walkable_map_choices()
        self._apply_walkable_map_path(save_path, show_errors=False)

    def _refresh_walkable_record_status(self, now_ts: Optional[float] = None):
        if not hasattr(self, "walkable_record_counter_label"):
            return
        with self._walkable_record_lock:
            tile_count = len(self._walkable_record_tiles)

        if self._walkable_recording and self._walkable_record_started_at is not None:
            now_val = now_ts if now_ts is not None else time.time()
            elapsed = max(0, int(now_val - self._walkable_record_started_at))
            self._walkable_record_last_elapsed_s = elapsed
        else:
            elapsed = int(self._walkable_record_last_elapsed_s)

        mm, ss = divmod(elapsed, 60)
        self._set_label_cached(
            "walkable:record_counter",
            self.walkable_record_counter_label,
            f"Recorded unique tiles: {tile_count}    Elapsed: {mm:02d}:{ss:02d}",
        )

    def _create_walkable_maps_tab(self, parent):
        parent.columnconfigure(0, weight=1)

        ttk.Label(
            parent,
            text="Walkable Maps",
            font=("Arial", 11, "bold"),
        ).grid(row=0, column=0, sticky="w", padx=10, pady=(10, 4))
        ttk.Label(
            parent,
            text="Select maps from walkable_maps/ or record a new map from the GUI.",
            foreground="gray",
        ).grid(row=1, column=0, sticky="w", padx=10, pady=(0, 10))

        picker = ttk.Frame(parent)
        picker.grid(row=2, column=0, sticky="ew", padx=10, pady=(0, 8))
        picker.columnconfigure(0, weight=1)

        self.walkable_map_var = tk.StringVar(value="")
        self.walkable_map_combo = ttk.Combobox(
            picker,
            textvariable=self.walkable_map_var,
            state="readonly",
        )
        self.walkable_map_combo.grid(row=0, column=0, sticky="ew")
        self.walkable_map_combo.bind("<<ComboboxSelected>>", self._on_walkable_map_selected)

        self.walkable_refresh_btn = ttk.Button(
            picker,
            text="Refresh",
            command=self._refresh_walkable_map_choices,
        )
        self.walkable_refresh_btn.grid(row=0, column=1, sticky="e", padx=(8, 0))

        self.walkable_active_label = ttk.Label(
            parent,
            text=f"Active: {self._walkable_path.name}",
            foreground="green",
        )
        self.walkable_active_label.grid(row=3, column=0, sticky="w", padx=10, pady=(0, 10))

        recorder = ttk.LabelFrame(parent, text="Map Recorder", padding=10)
        recorder.grid(row=4, column=0, sticky="ew", padx=10, pady=(0, 10))
        recorder.columnconfigure(0, weight=1)

        btn_row = ttk.Frame(recorder)
        btn_row.grid(row=0, column=0, sticky="w")
        self.walkable_record_start_btn = ttk.Button(
            btn_row,
            text="Record New Map",
            command=self._on_walkable_record_start,
        )
        self.walkable_record_start_btn.grid(row=0, column=0, padx=(0, 8))
        self.walkable_record_stop_btn = ttk.Button(
            btn_row,
            text="Stop & Save",
            command=self._on_walkable_record_stop,
            state=tk.DISABLED,
        )
        self.walkable_record_stop_btn.grid(row=0, column=1)

        self.walkable_record_status_label = ttk.Label(
            recorder,
            text="Idle. Press Record New Map to start.",
            foreground="blue",
        )
        self.walkable_record_status_label.grid(row=1, column=0, sticky="w", pady=(8, 2))

        self.walkable_record_counter_label = ttk.Label(
            recorder,
            text="Recorded unique tiles: 0    Elapsed: 00:00",
        )
        self.walkable_record_counter_label.grid(row=2, column=0, sticky="w")

        ttk.Label(
            recorder,
            text="Starting recording will stop the bot, then capture your walked safe tiles.",
            foreground="gray",
        ).grid(row=3, column=0, sticky="w", pady=(8, 0))

        self._refresh_walkable_map_choices()
        self._refresh_walkable_record_status()

    def _refresh_config_file_choices(self):
        if not hasattr(self, "config_file_combo"):
            return

        files = _list_config_files()
        label_to_path: Dict[str, Path] = {}
        labels: List[str] = []
        for p in files:
            label = p.name
            if label in label_to_path:
                label = str(p)
            labels.append(label)
            label_to_path[label] = p
        self._config_paths = label_to_path
        self.config_file_combo["values"] = labels

        active = _get_active_config_file()
        active_label = ""
        for lbl, p in label_to_path.items():
            try:
                if p.resolve() == active.resolve():
                    active_label = lbl
                    break
            except Exception:
                continue

        if not active_label and labels:
            active_label = labels[0]

        self._config_syncing = True
        try:
            self.config_file_var.set(active_label)
        finally:
            self._config_syncing = False

        if active_label and active_label in label_to_path:
            self.config_active_label.config(text=f"Active: {label_to_path[active_label].name}", foreground="green")
        else:
            self.config_active_label.config(text="Active: (none)", foreground="red")

    def _apply_config_file_path(self, path: Path) -> bool:
        try:
            resolved = path.resolve()
            load_settings(str(resolved))
        except Exception as e:
            messagebox.showerror("Config Load Failed", f"Could not load config:\n{e}")
            _log_warn(f"[CONFIG] Failed to load config '{path}': {e}")
            return False

        self._config_syncing = True
        try:
            self.config_file_var.set(resolved.name)
        finally:
            self._config_syncing = False
        self.config_active_label.config(text=f"Active: {resolved.name}", foreground="green")

        if hasattr(self, "manual_map_id_var"):
            self._set_var_cached(
                "var:manual_map_id",
                self.manual_map_id_var,
                (str(START_MAP_ID) if START_MAP_ID is not None else ""),
            )
        self._last_auto_loaded_map_id = None
        self._last_map_signature = None
        self._refresh_walkable_map_choices()
        self._refresh_walkable_warning_label()
        _log_info(f"[CONFIG] Active config switched to {resolved}")
        return True

    def _on_config_file_selected(self, _event=None):
        if self._config_syncing:
            return
        selected = self.config_file_var.get().strip()
        target = self._config_paths.get(selected)
        if not target:
            return
        if not self._apply_config_file_path(target):
            self._refresh_config_file_choices()

    def _next_unique_config_path(self, filename: str) -> Path:
        cfg_dir = _config_dir_path()
        name = _normalize_config_name(filename)
        candidate = (cfg_dir / name).resolve()
        if not candidate.exists():
            return candidate
        stem = candidate.stem
        suffix = candidate.suffix or ".json"
        i = 1
        while True:
            attempt = (cfg_dir / f"{stem} ({i}){suffix}").resolve()
            if not attempt.exists():
                return attempt
            i += 1

    def _create_new_config_file(self):
        suggested = f"config-{time.strftime('%Y%m%d-%H%M%S')}"
        entered = simpledialog.askstring(
            "New Config",
            "Name for new config file (.json optional):",
            initialvalue=suggested,
            parent=self.root,
        )
        if entered is None:
            return

        filename = _normalize_config_name(entered)
        cfg_dir = _config_dir_path()
        path = (cfg_dir / filename).resolve()
        if path.exists():
            overwrite = messagebox.askyesno(
                "Overwrite Config?",
                f"'{path.name}' already exists.\nOverwrite it?",
                parent=self.root,
            )
            if not overwrite:
                path = self._next_unique_config_path(filename)

        base_state = copy.deepcopy(_INITIAL_CONFIG_STATE) if _INITIAL_CONFIG_STATE is not None else ConfigState()
        payload = _config_payload_from_state(base_state)
        try:
            with path.open("w", encoding="utf-8") as f:
                json.dump(payload, f, indent=2)
        except Exception as e:
            messagebox.showerror("Create Config Failed", f"Could not create config file:\n{e}")
            _log_warn(f"[CONFIG] Failed to create config '{path}': {e}")
            return

        self._refresh_config_file_choices()
        self._apply_config_file_path(path)

    def _create_config_tab(self, parent):
        parent.columnconfigure(0, weight=1)

        ttk.Label(
            parent,
            text="Config Files",
            font=("Arial", 11, "bold"),
        ).grid(row=0, column=0, sticky="w", padx=10, pady=(10, 4))
        ttk.Label(
            parent,
            text="Choose a config to auto-load for this session, or create a clean default config.",
            foreground="gray",
        ).grid(row=1, column=0, sticky="w", padx=10, pady=(0, 10))

        picker = ttk.Frame(parent)
        picker.grid(row=2, column=0, sticky="ew", padx=10, pady=(0, 8))
        picker.columnconfigure(0, weight=1)

        self.config_file_var = tk.StringVar(value="")
        self.config_file_combo = ttk.Combobox(
            picker,
            textvariable=self.config_file_var,
            state="readonly",
        )
        self.config_file_combo.grid(row=0, column=0, sticky="ew")
        self.config_file_combo.bind("<<ComboboxSelected>>", self._on_config_file_selected)

        self.config_refresh_btn = ttk.Button(
            picker,
            text="Refresh",
            command=self._refresh_config_file_choices,
        )
        self.config_refresh_btn.grid(row=0, column=1, sticky="e", padx=(8, 0))

        self.config_new_btn = ttk.Button(
            parent,
            text="Create New Config",
            command=self._create_new_config_file,
        )
        self.config_new_btn.grid(row=3, column=0, sticky="w", padx=10, pady=(0, 8))

        self.config_active_label = ttk.Label(parent, text="Active: (none)", foreground="red")
        self.config_active_label.grid(row=4, column=0, sticky="w", padx=10, pady=(0, 8))

        self._refresh_config_file_choices()

    def _bring_to_front(self, *_):
        try:
            self.root.deiconify()
        except Exception:
            pass
        self.root.lift()
        self.root.focus_force()
        self.root.attributes("-topmost", True)
        self.root.after(400, lambda: self.root.attributes("-topmost", False))

    def _ensure_visible(self):
        """If window is off-screen (OS restored weird coords), re-center it."""
        sw = self.root.winfo_screenwidth()
        sh = self.root.winfo_screenheight()
        try:
            g = self.root.geometry()  # "WxH+X+Y"
            size, _, _ = g.partition('+')
            w, _, h = size.partition('x')
            w, h = int(w), int(h)
            parts = g.split('+')
            x = int(parts[1]) if len(parts) > 1 else 100
            y = int(parts[2]) if len(parts) > 2 else 100
        except Exception:
            w, h, x, y = 1120, 720, 100, 100
        off = (x > sw - 40) or (y > sh - 40) or (x + w < 40) or (y + h < 40)
        if off:
            nx = max(0, (sw - w) // 2)
            ny = max(0, (sh - h) // 2)
            self.root.geometry(f"{w}x{h}+{nx}+{ny}")

    def _place_left_center(self):
        """Force the window near the left edge, vertically centered."""
        self.root.update_idletasks()

        w = max(self.root.winfo_width(),  1120)
        h = max(self.root.winfo_height(),  720)

        sw = self.root.winfo_screenwidth()
        sh = self.root.winfo_screenheight()

        x = max(0, int(sw * 0.05))
        y = max(0, (sh - h) // 2)

        self.root.geometry(f"{w}x{h}+{x}+{y}")

    def create_widgets(self):
        self.root.geometry("1080x700")   # normal window
        self.root.minsize(920, 600)
        self.root.rowconfigure(0, weight=1)
        self.root.columnconfigure(0, weight=1)

        PADX, PADY = (8, 8), (6, 6)

        paned = ttk.PanedWindow(self.root, orient="horizontal")
        paned.grid(row=0, column=0, sticky="nsew")

        left_container = ttk.Frame(paned)
        paned.add(left_container, weight=3)
        left_container.rowconfigure(0, weight=1)
        left_container.columnconfigure(0, weight=1)

        left = ScrollableFrame(left_container)
        left.grid(row=0, column=0, sticky="nsew")

        def add_section(title):
            """Create a styled section with consistent padding and professional appearance"""
            outer = ttk.Frame(left.interior, style='TFrame')
            outer.grid(sticky="ew", padx=PADX, pady=PADY)
            outer.columnconfigure(0, weight=1)
            outer.rowconfigure(0, weight=1)
            
            inner = ttk.LabelFrame(outer, text=title, padding=10)
            inner.grid(row=0, column=0, sticky="nsew", padx=0, pady=0)
            inner.columnconfigure(0, weight=1)
            
            return inner

        self.notebook = ttk.Notebook(paned)
        paned.add(self.notebook, weight=2)
        
        right_scroll = ScrollableFrame(self.notebook)
        self.notebook.add(right_scroll, text="Dashboard")
        right = right_scroll.interior
        right.rowconfigure(0, weight=0)  # map
        right.rowconfigure(1, weight=0)  # info
        right.rowconfigure(2, weight=1)  # chat grows
        right.columnconfigure(0, weight=1)
        
        right.grid_rowconfigure(2, minsize=190)

        hotkeys_scroll = ScrollableFrame(self.notebook)
        self.notebook.add(hotkeys_scroll, text="Hotkeys")
        hotkeys_frame = hotkeys_scroll.interior
        hotkeys_frame.columnconfigure(0, weight=1)
        self._create_hotkeys_tab(hotkeys_frame)

        walkable_maps_scroll = ScrollableFrame(self.notebook)
        self.notebook.add(walkable_maps_scroll, text="Walkable Maps")
        walkable_maps_frame = walkable_maps_scroll.interior
        walkable_maps_frame.columnconfigure(0, weight=1)
        self._create_walkable_maps_tab(walkable_maps_frame)

        config_scroll = ScrollableFrame(self.notebook)
        self.notebook.add(config_scroll, text="Config")
        config_frame = config_scroll.interior
        config_frame.columnconfigure(0, weight=1)
        self._create_config_tab(config_frame)

        try:
            paned.paneconfigure(left_container, minsize=320)
            paned.paneconfigure(right_scroll,   minsize=480)   # <- point at the actual pane
            self.root.after_idle(lambda: (paned.update_idletasks(), paned.sashpos(0, 500)))
        except Exception:
            pass
        bot = add_section("Bot Control")
        self.start_bot_button = ttk.Button(bot, text="Start", command=self.on_start_bot, style="success.TButton")
        self.start_bot_button.grid(row=0, column=0, sticky="w", padx=(0,6))
        self.stop_bot_button  = ttk.Button(bot, text="Stop",  command=self.on_stop_bot,  style="danger.TButton", state=tk.DISABLED)
        self.stop_bot_button.grid(row=0, column=1, sticky="w")
        self.bot_status_label = ttk.Label(bot, text="Status: STOPPED", foreground="red")
        self.bot_status_label.grid(row=1, column=0, columnspan=2, sticky="w", pady=(5,0))
        
        sit = add_section("Sit Timer Configuration")
        ttk.Label(sit, text="Sit (seconds):").grid(row=0, column=0, sticky="w")
        self.sit_timer_var = tk.StringVar(value=str(SIT_TIMER_SECONDS))
        e = ttk.Entry(sit, textvariable=self.sit_timer_var, width=8)
        e.grid(row=0, column=1, sticky="w", padx=(8,0))
        e.bind("<FocusOut>", self.on_sit_timer_change)
        e.bind("<Return>",   self.on_sit_timer_change)
        self.sit_timer_status = ttk.Label(sit, text=f"Current: {SIT_TIMER_SECONDS}s", foreground="red")
        self.sit_timer_status.grid(row=1, column=0, columnspan=2, sticky="w", pady=(5,0))

        stale = add_section("Stale NPC")
        ttk.Label(stale, text="NPC cleanup timer (seconds):").grid(row=0, column=0, sticky="w")
        self.last_moved_timer_var = tk.StringVar(value=str(LAST_MOVED_TIMER_SECONDS))
        e2 = ttk.Entry(stale, textvariable=self.last_moved_timer_var, width=8)
        e2.grid(row=0, column=1, sticky="w", padx=(8,0))
        e2.bind("<FocusOut>", self.on_last_moved_timer_change)
        e2.bind("<Return>",   self.on_last_moved_timer_change)
        self.last_moved_timer_status = ttk.Label(stale, text=f"Current: {LAST_MOVED_TIMER_SECONDS}s", foreground="red")
        self.last_moved_timer_status.grid(row=1, column=0, columnspan=2, sticky="w", pady=(5,0))

        range_f = add_section("Range")
        ttk.Label(range_f, text="Tiles (1-5):").grid(row=0, column=0, sticky="w")
        self.flank_range_var = tk.StringVar(value=str(FLANK_RANGE))
        flank_entry = ttk.Entry(range_f, textvariable=self.flank_range_var, width=6)
        flank_entry.grid(row=0, column=1, sticky="w", padx=(10,0))
        flank_entry.bind("<FocusOut>", self.on_flank_range_change)
        flank_entry.bind("<Return>",   self.on_flank_range_change)
        self.flank_range_status = ttk.Label(range_f, text=f"Current: {FLANK_RANGE}", foreground="red")
        self.flank_range_status.grid(row=1, column=0, columnspan=2, sticky="w", pady=(5,0))

        players_live = add_section("Other Players (Live)")
        self.other_players_summary = ttk.Label(players_live, text="Active: 0", foreground="red")
        self.other_players_summary.grid(row=0, column=0, sticky="w", pady=(0,4))

        players_live_wrap = ttk.Frame(players_live)
        players_live_wrap.grid(row=1, column=0, sticky="nsew")
        players_live_wrap.columnconfigure(0, weight=1)
        players_live_wrap.rowconfigure(0, weight=1)

        self.other_players_tree = ttk.Treeview(
            players_live_wrap,
            columns=("name", "level", "facing", "x", "y"),
            show="headings",
            height=6,
        )
        self.other_players_tree.heading("name", text="Name")
        self.other_players_tree.heading("level", text="Lvl")
        self.other_players_tree.heading("facing", text="Face")
        self.other_players_tree.heading("x", text="X")
        self.other_players_tree.heading("y", text="Y")
        self.other_players_tree.column("name", width=130, anchor="w")
        self.other_players_tree.column("level", width=45, anchor="center")
        self.other_players_tree.column("facing", width=45, anchor="center")
        self.other_players_tree.column("x", width=45, anchor="center")
        self.other_players_tree.column("y", width=45, anchor="center")
        self.other_players_tree.grid(row=0, column=0, sticky="nsew")

        players_live_sb = ttk.Scrollbar(players_live_wrap, orient="vertical", command=self.other_players_tree.yview)
        players_live_sb.grid(row=0, column=1, sticky="ns")
        self.other_players_tree.configure(yscrollcommand=players_live_sb.set)
        self._other_player_row_ids = {}

        player_avoid = add_section("Player Avoidance")
        self.avoid_players_var = tk.BooleanVar(value=AVOID_OTHER_PLAYERS)
        ttk.Checkbutton(
            player_avoid,
            text="Avoid other players (stay 1 tile away)",
            variable=self.avoid_players_var,
            command=self.on_avoid_players_toggle
        ).grid(row=0, column=0, sticky="w")

        self.protection_status = ttk.Label(player_avoid, text="Protection: ENABLED", foreground="green")
        self.protection_status.grid(row=1, column=0, sticky="w", pady=(6,2))

        ttk.Checkbutton(
            player_avoid,
            text="Disable protected NPCs (boss mode)",
            variable=self.ignore_prot_var,
            command=self.on_protection_toggle
        ).grid(row=2, column=0, sticky="w")

        npc = add_section("NPC Target Management")
        ttk.Label(npc, text="Add NPC ID:").grid(row=0, column=0, sticky="w")
        self.add_npc_var = tk.StringVar()
        add_npc_entry = ttk.Entry(npc, textvariable=self.add_npc_var, width=8)
        add_npc_entry.grid(row=0, column=1, sticky="w", padx=(5,0))
        add_npc_entry.bind("<Return>", self.add_npc_target)
        ttk.Button(npc, text="Add", command=self.add_npc_target).grid(row=0, column=2, sticky="w", padx=(5,0))

        ttk.Label(npc, text="Remove NPC ID:").grid(row=1, column=0, sticky="w", pady=(5,0))
        self.remove_npc_var = tk.StringVar()
        remove_npc_entry = ttk.Entry(npc, textvariable=self.remove_npc_var, width=8)
        remove_npc_entry.grid(row=1, column=1, sticky="w", padx=(5,0), pady=(5,0))
        remove_npc_entry.bind("<Return>", self.remove_npc_target)
        ttk.Button(npc, text="Remove", command=self.remove_npc_target).grid(row=1, column=2, sticky="w", padx=(5,0), pady=(5,0))

        ttk.Label(npc, text="Current targets:").grid(row=2, column=0, sticky="w", pady=(6,0))
        self.targets_display = ttk.Label(npc, text="", foreground="green")
        self.targets_display.grid(row=2, column=1, columnspan=2, sticky="w", pady=(6,0))

        home_toggle = add_section("Home Routine (Run After Kill)")
        self.home_toggle_var = tk.BooleanVar(value=RUN_HOME_AFTER_KILL)
        ttk.Checkbutton(home_toggle, text="Enable (Bossing)",
                        variable=self.home_toggle_var, command=self.on_home_toggle).grid(row=0, column=0, sticky="w")

        ttk.Label(home_toggle, text="Enable early stand-up when NPCs detected:").grid(row=1, column=0, sticky="w", pady=(6,0))
        ttk.Checkbutton(home_toggle, text="Enable",
                        variable=self.boss_aggro_var,
                        command=self.on_boss_aggro_toggle).grid(row=1, column=1, sticky="w", padx=(10,0), pady=(6,0))
        self.boss_aggro_status = ttk.Label(
            home_toggle,
            text=("Status: ENABLED" if self.boss_aggro_var.get() else "Status: DISABLED"),
            foreground=("green" if self.boss_aggro_var.get() else "red")
        )
        self.boss_aggro_status.grid(row=2, column=0, columnspan=2, sticky="w", pady=(5,0))

        ttk.Label(home_toggle, text="F5 taps after F11:").grid(row=3, column=0, sticky="w", pady=(6,0))
        self.f5_taps_var = tk.StringVar(value=str(F5_TAP_COUNT))
        f5_entry = ttk.Entry(home_toggle, textvariable=self.f5_taps_var, width=8)
        f5_entry.grid(row=3, column=1, sticky="w", padx=(10,0))
        f5_entry.bind("<FocusOut>", self.on_f5_taps_change)
        f5_entry.bind("<Return>",   self.on_f5_taps_change)
        self.f5_taps_status = ttk.Label(home_toggle, text=f"Current: {F5_TAP_COUNT}", foreground="red")
        self.f5_taps_status.grid(row=4, column=0, columnspan=2, sticky="w", pady=(3,0))

        ttk.Label(home_toggle, text="Wander timeout (s) before going Home:").grid(row=5, column=0, sticky="w", pady=(6,0))
        self.wander_timeout_var = tk.StringVar(value=str(WANDER_TIMEOUT_S))
        wander_entry = ttk.Entry(home_toggle, textvariable=self.wander_timeout_var, width=8)
        wander_entry.grid(row=5, column=1, sticky="w", padx=(10,0))
        wander_entry.bind("<FocusOut>", self.on_wander_timeout_change)
        wander_entry.bind("<Return>",   self.on_wander_timeout_change)
        self.wander_timeout_status = ttk.Label(home_toggle, text=f"Current: {WANDER_TIMEOUT_S}s", foreground="red")
        self.wander_timeout_status.grid(row=6, column=0, columnspan=2, sticky="w", pady=(3,0))

        ttk.Label(home_toggle, text="Go Home after N kills:").grid(row=7, column=0, sticky="w", pady=(6,0))
        self.kills_per_home_var = tk.StringVar(value=str(HOME_AFTER_KILLS_N))
        kills_entry = ttk.Entry(home_toggle, textvariable=self.kills_per_home_var, width=8)
        kills_entry.grid(row=7, column=1, sticky="w", padx=(10,0))
        kills_entry.bind("<FocusOut>", self.on_kills_per_home_change)
        kills_entry.bind("<Return>",   self.on_kills_per_home_change)
        self.kills_per_home_status = ttk.Label(home_toggle, text=f"Current: {HOME_AFTER_KILLS_N}", foreground="red")
        self.kills_per_home_status.grid(row=8, column=0, columnspan=2, sticky="w", pady=(3,0))

        ttk.Label(home_toggle, text="HP emergency home:").grid(row=9, column=0, sticky="w", pady=(8,0))

        self.hp_home_toggle_var = tk.BooleanVar(value=HP_HOME_ENABLED)
        ttk.Checkbutton(
            home_toggle,
            text="Use HP to trigger Home",
            variable=self.hp_home_toggle_var,
            command=self.on_hp_home_toggle
        ).grid(row=9, column=1, sticky="w", padx=(10,0), pady=(8,0))

        ttk.Label(home_toggle, text="Go Home below HP (%):").grid(row=10, column=0, sticky="w", pady=(4,0))
        self.hp_home_low_var = tk.StringVar(value=str(int(HP_HOME_LOW_PCT)))
        low_entry = ttk.Entry(home_toggle, textvariable=self.hp_home_low_var, width=8)
        low_entry.grid(row=10, column=1, sticky="w", padx=(10,0))
        low_entry.bind("<FocusOut>", self.on_hp_home_thresholds_change)
        low_entry.bind("<Return>",   self.on_hp_home_thresholds_change)

        ttk.Label(home_toggle, text="Stand up above HP (%):").grid(row=11, column=0, sticky="w", pady=(4,0))
        self.hp_home_high_var = tk.StringVar(value=str(int(HP_HOME_HIGH_PCT)))
        high_entry = ttk.Entry(home_toggle, textvariable=self.hp_home_high_var, width=8)
        high_entry.grid(row=11, column=1, sticky="w", padx=(10,0))
        high_entry.bind("<FocusOut>", self.on_hp_home_thresholds_change)
        high_entry.bind("<Return>",   self.on_hp_home_thresholds_change)

        self.hp_home_status = ttk.Label(
            home_toggle,
            text=f"Trigger < {int(HP_HOME_LOW_PCT)}%, stand at >= {int(HP_HOME_HIGH_PCT)}%",
            foreground="red"
        )
        self.hp_home_status.grid(row=12, column=0, columnspan=2, sticky="w", pady=(3,0))

        ttk.Label(home_toggle, text="Home coordinates:").grid(row=13, column=0, sticky="w", pady=(8,0))
        coords_row = ttk.Frame(home_toggle)
        coords_row.grid(row=14, column=0, columnspan=2, sticky="w", pady=(2,0))
        ttk.Label(coords_row, text="X:").grid(row=0, column=0, sticky="w")
        self.home_x_var = tk.StringVar(value=str(HOME_POS[0]))
        ttk.Entry(coords_row, textvariable=self.home_x_var, width=6).grid(row=0, column=1, sticky="w", padx=(5,0))
        ttk.Label(coords_row, text="Y:").grid(row=0, column=2, sticky="w", padx=(10,0))
        self.home_y_var = tk.StringVar(value=str(HOME_POS[1]))
        ttk.Entry(coords_row, textvariable=self.home_y_var, width=6).grid(row=0, column=3, sticky="w", padx=(5,0))
        ttk.Button(coords_row, text="Apply",            command=self.on_home_change).grid(row=0, column=4, sticky="w", padx=(10,0))
        ttk.Button(coords_row, text="Set from current", command=self.set_home_from_current).grid(row=0, column=5, sticky="w", padx=(5,0))
        self.home_status = ttk.Label(home_toggle, text=f"Current: ({HOME_POS[0]}, {HOME_POS[1]})", foreground="red")
        self.home_status.grid(row=15, column=0, columnspan=2, sticky="w", pady=(5,0))

        click = add_section("Corpse/Loot Clicking")
        self.click_toggle_var = tk.BooleanVar(value=CLICKING_ENABLED)
        ttk.Checkbutton(click, text="Enable clicking after kills",
                        variable=self.click_toggle_var, command=self.on_click_toggle).grid(row=0, column=0, sticky="w")

        self.fast_click_var = tk.BooleanVar(value=FAST_CLICK)
        ttk.Checkbutton(click, text="Fast click burst",
                        variable=self.fast_click_var, command=self.on_fast_click_toggle).grid(row=1, column=0, sticky="w", pady=(4,0))

        params = ttk.Frame(click)
        params.grid(row=2, column=0, sticky="w", pady=(2,0))
        ttk.Label(params, text="Burst:").grid(row=0, column=0, sticky="w")

        self.fast_click_burst_var = tk.StringVar(value=str(FAST_CLICK_BURST_COUNT))
        self.fast_click_burst_entry = ttk.Entry(params, textvariable=self.fast_click_burst_var, width=5)
        self.fast_click_burst_entry.grid(row=0, column=1, sticky="w", padx=(4,12))
        self.fast_click_burst_entry.bind("<FocusOut>", self.on_fast_click_params_change)
        self.fast_click_burst_entry.bind("<Return>",   self.on_fast_click_params_change)

        ttk.Label(params, text="Gap (s):").grid(row=0, column=2, sticky="w")
        self.fast_click_gap_var = tk.StringVar(value=str(FAST_CLICK_GAP_S))
        self.fast_click_gap_entry = ttk.Entry(params, textvariable=self.fast_click_gap_var, width=6)
        self.fast_click_gap_entry.grid(row=0, column=3, sticky="w", padx=(4,0))
        self.fast_click_gap_entry.bind("<FocusOut>", self.on_fast_click_params_change)
        self.fast_click_gap_entry.bind("<Return>",   self.on_fast_click_params_change)
        
        self.buff_click_var = tk.BooleanVar(value=CLICK_BUFFS_ENABLED)
        timed_key = HOTKEY_BINDINGS.get("buff_self", "f6").upper()
        ttk.Checkbutton(
            click,
            text=f"Enable timed self-buff ({timed_key})",
            variable=self.buff_click_var,
            command=self.on_buff_click_toggle
        ).grid(row=3, column=0, sticky="w", pady=(4, 0))

        buff_params = ttk.Frame(click)
        buff_params.grid(row=4, column=0, sticky="w", pady=(2, 0))

        ttk.Label(buff_params, text="Buff every (s):").grid(row=0, column=0, sticky="w")

        self.buff_interval_var = tk.StringVar(value=str(CLICK_BUFF_INTERVAL_S))
        buff_interval_entry = ttk.Entry(buff_params, textvariable=self.buff_interval_var, width=6)
        buff_interval_entry.grid(row=0, column=1, sticky="w", padx=(4, 0))

        buff_interval_entry.bind("<FocusOut>", self.on_buff_interval_change)
        buff_interval_entry.bind("<Return>",   self.on_buff_interval_change)

        self.hp_buff_var = tk.BooleanVar(value=HP_BUFFS_ENABLED)
        hp_key = HOTKEY_BINDINGS.get("hp_buff", "f3").upper()
        ttk.Checkbutton(
            click,
            text=f"Enable HP buff/potion ({hp_key})",
            variable=self.hp_buff_var,
            command=self.on_hp_buff_toggle
        ).grid(row=5, column=0, sticky="w", pady=(4, 0))

        hp_params = ttk.Frame(click)
        hp_params.grid(row=6, column=0, sticky="w", pady=(2, 0))

        ttk.Label(hp_params, text="Trigger if HP <= (%):").grid(row=0, column=0, sticky="w")
        self.hp_buff_threshold_var = tk.StringVar(value=str(HP_BUFF_THRESHOLD_PCT))
        hp_thresh_entry = ttk.Entry(hp_params, textvariable=self.hp_buff_threshold_var, width=6)
        hp_thresh_entry.grid(row=0, column=1, sticky="w", padx=(4, 0))
        hp_thresh_entry.bind("<FocusOut>", self.on_hp_buff_threshold_change)
        hp_thresh_entry.bind("<Return>",   self.on_hp_buff_threshold_change)

        ttk.Label(hp_params, text="Heal to >= (%):").grid(row=0, column=2, sticky="w", padx=(12, 0))
        self.hp_buff_target_var = tk.StringVar(value=str(HP_BUFF_TARGET_PCT))
        hp_target_entry = ttk.Entry(hp_params, textvariable=self.hp_buff_target_var, width=6)
        hp_target_entry.grid(row=0, column=3, sticky="w", padx=(4, 0))
        hp_target_entry.bind("<FocusOut>", self.on_hp_buff_target_change)
        hp_target_entry.bind("<Return>",   self.on_hp_buff_target_change)

        self.rerecord_points_button = ttk.Button(click, text="Record Click Points", command=self.on_rerecord_click_points, style="TButton")
        self.rerecord_points_button.grid(row=7, column=0, sticky="w", pady=(4, 0))
        map_frame = ttk.LabelFrame(right, text="Map View", padding=6)
        map_frame.grid(row=0, column=0, sticky="nsew", padx=PADX, pady=PADY)
        map_frame.columnconfigure(0, weight=1)
        map_frame.rowconfigure(0, weight=1)
        self.canvas = tk.Canvas(map_frame, width=440, height=320, bg="#0f132a", highlightthickness=0)
        self.canvas.grid(row=0, column=0, sticky="nsew")
        self.canvas.bind('<Motion>', self._on_map_mouse_move)
        self.canvas.bind('<Leave>', self._on_map_mouse_leave)
        self.canvas.bind('<ButtonPress-1>', self._on_map_mouse_drag_start)
        self.canvas.bind('<B1-Motion>', self._on_map_mouse_drag_motion)
        self.canvas.bind('<ButtonRelease-1>', self._on_map_mouse_drag_end)

        map_info_frame = tk.Frame(map_frame, bg="#2d3442", relief='flat', bd=0)
        map_info_frame.grid(row=1, column=0, sticky="ew", padx=1, pady=1)
        map_info_frame.columnconfigure(0, weight=1)  # Left side expands
        
        counts_frame = tk.Frame(map_info_frame, bg="#2d3442")
        counts_frame.grid(row=0, column=0, sticky="w", padx=0, pady=0)
        
        tk.Label(counts_frame, text="Players: ", foreground="#ff6b6b", font=("Arial", 8), bg="#2d3442").pack(side=tk.LEFT)
        self.player_count_label = tk.Label(counts_frame, text="0", foreground="white", font=("Arial", 8, "bold"), bg="#2d3442")
        self.player_count_label.pack(side=tk.LEFT, padx=(0, 8))
        
        tk.Label(counts_frame, text="NPCs: ", foreground="#fff9c4", font=("Arial", 8), bg="#2d3442").pack(side=tk.LEFT)
        self.npc_count_label = tk.Label(counts_frame, text="0", foreground="white", font=("Arial", 8, "bold"), bg="#2d3442")
        self.npc_count_label.pack(side=tk.LEFT, padx=(0, 8))
        self.walkable_warning_label = tk.Label(
            counts_frame,
            text="",
            foreground="#ffb347",
            font=("Arial", 8, "bold"),
            bg="#2d3442",
        )
        self.walkable_warning_label.pack(side=tk.LEFT, padx=(2, 0))

        self.show_coords_var = tk.BooleanVar(value=True)
        coords_label = tk.Label(map_info_frame, text="Show Coords", font=("Arial", 8), bg="#2d3442", fg="#e8eef7")
        coords_label.grid(row=0, column=1, sticky="e", padx=0, pady=0)
        coords_toggle = ttk.Checkbutton(map_info_frame, variable=self.show_coords_var, command=self.draw_map)
        coords_toggle.grid(row=0, column=2, sticky="e", padx=0, pady=0)

        self.auto_mapid_var = tk.BooleanVar(value=AUTO_LOAD_MAP_BY_ID)
        self.auto_mapid_toggle = ttk.Checkbutton(
            map_info_frame,
            text="Auto MapID",
            variable=self.auto_mapid_var,
            command=self.on_auto_map_id_toggle,
        )
        self.auto_mapid_toggle.grid(row=0, column=3, sticky="e", padx=(8, 0), pady=0)

        mapid_lbl = tk.Label(map_info_frame, text="MapID:", font=("Arial", 8), bg="#2d3442", fg="#e8eef7")
        mapid_lbl.grid(row=0, column=4, sticky="e", padx=(8, 0), pady=0)
        self.map_id_value_label = tk.Label(map_info_frame, text="?", foreground="#ffcc66", font=("Arial", 8, "bold"), bg="#2d3442")
        self.map_id_value_label.grid(row=0, column=5, sticky="e", padx=(2, 0), pady=0)

        manual_mapid_lbl = tk.Label(map_info_frame, text="Set:", font=("Arial", 8), bg="#2d3442", fg="#e8eef7")
        manual_mapid_lbl.grid(row=0, column=6, sticky="e", padx=(8, 0), pady=0)
        self.manual_map_id_var = tk.StringVar(value=(str(START_MAP_ID) if START_MAP_ID is not None else ""))
        self.manual_map_id_entry = ttk.Entry(map_info_frame, textvariable=self.manual_map_id_var, width=7)
        self.manual_map_id_entry.grid(row=0, column=7, sticky="e", padx=(4, 0), pady=0)
        self.manual_map_id_entry.bind("<Return>", self.on_manual_load_map_id)

        info_row = ttk.Frame(right)
        info_row.grid(row=1, column=0, sticky="nsew", padx=PADX, pady=PADY)
        info_row.columnconfigure(0, weight=0)
        info_row.columnconfigure(1, weight=1)

        player_frame = ttk.LabelFrame(info_row, text="Player Data", padding=6)
        player_frame.grid(row=0, column=0, sticky="nw", padx=(0, 12))
        for i, text in enumerate(["X", "Y", "Direction"]):
            ttk.Label(player_frame, text=f"{text}:").grid(row=i, column=0, sticky="w")
            v = ttk.Label(player_frame, text="0")
            v.grid(row=i, column=1, sticky="e", padx=(8,0))
            self.labels[text] = v

        ttk.Label(player_frame, text="HP:").grid(row=3, column=0, sticky="w", pady=(8, 2))
        hp_lbl = ttk.Label(player_frame, text="")
        hp_lbl.grid(row=3, column=1, sticky="e", padx=(8,0), pady=(8, 2))
        self.hp_mp_label = hp_lbl
        
        ttk.Label(player_frame, text="MP:").grid(row=4, column=0, sticky="w", pady=2)
        mp_lbl = ttk.Label(player_frame, text="")
        mp_lbl.grid(row=4, column=1, sticky="e", padx=(8,0), pady=2)
        self.mp_label = mp_lbl

        ttk.Label(player_frame, text="Session EXP:").grid(row=5, column=0, sticky="w", pady=(8, 2))
        session_exp_lbl = ttk.Label(player_frame, text="0")
        session_exp_lbl.grid(row=5, column=1, sticky="e", padx=(8,0), pady=(8, 2))
        self.session_exp_label = session_exp_lbl

        ttk.Label(player_frame, text="EXP/hr:").grid(row=6, column=0, sticky="w", pady=2)
        session_exp_hr_lbl = ttk.Label(player_frame, text="0")
        session_exp_hr_lbl.grid(row=6, column=1, sticky="e", padx=(8,0), pady=2)
        self.session_exp_hour_label = session_exp_hr_lbl

        stats_frame = ttk.LabelFrame(info_row, text="Player Stats", padding=6)
        stats_frame.grid(row=0, column=1, sticky="nsew")

        stats = [
            "exp","level","tnl","weight","vit","dex","acc","def","pwr","crit",
            "armor","eva","hit_rate","max_dmg","min_dmg","aura","max_hp","max_mana","eon"
        ]

        STAT_COLS = 2  # change to 3 to make it even shorter
        rows_per_col = (len(stats) + STAT_COLS - 1) // STAT_COLS  # ceil

        self.stats_labels = {}
        for idx, stat in enumerate(stats):
            r = idx % rows_per_col
            c = (idx // rows_per_col) * 2  # each stat uses 2 grid columns (label, value)

            ttk.Label(stats_frame, text=f"{stat.upper()}:").grid(
                row=r, column=c, sticky="w", padx=(0,6), pady=(2,1)
            )
            lbl = ttk.Label(stats_frame, text="N/A", anchor="w")
            lbl.grid(row=r, column=c+1, sticky="w", padx=(0,8), pady=(2,1))
            self.stats_labels[stat] = lbl

        for i in range(STAT_COLS * 2):
            stats_frame.columnconfigure(i, weight=1 if i % 2 else 0)

        chat_frame = ttk.LabelFrame(right, text="Recent Chat", padding=6)
        chat_frame.grid(row=2, column=0, sticky="nsew", padx=PADX, pady=PADY)
        chat_frame.rowconfigure(0, weight=1)
        chat_frame.columnconfigure(0, weight=1)

        chat_wrap = ttk.Frame(chat_frame)
        chat_wrap.grid(row=0, column=0, sticky="nsew")
        chat_wrap.rowconfigure(0, weight=1)
        chat_wrap.columnconfigure(0, weight=1)

        self.chat_list = tk.Listbox(
            chat_wrap,
            height=9,  # ensure visible at first paint
            bg="#0f132a",
            fg="#f5f7ff",
            selectbackground="#2563eb",
            selectforeground="#ffffff",
            highlightthickness=0,
            relief="flat",
        )
        self.chat_list.grid(row=0, column=0, sticky="nsew")
        sb = ttk.Scrollbar(chat_wrap, orient="vertical", command=self.chat_list.yview)
        sb.grid(row=0, column=1, sticky="ns")
        self.chat_list.configure(yscrollcommand=sb.set)

        self.last_speech_lbl = ttk.Label(chat_frame, text="Last:")
        self.last_speech_lbl.grid(row=1, column=0, sticky="w", pady=(6,0))

        self.speech_quarantine_lbl = ttk.Label(chat_frame, text="Quarantine: OFF", foreground="#7CFC00")
        self.speech_quarantine_lbl.grid(row=2, column=0, sticky="w", pady=(2,0))

    def _create_hotkeys_tab(self, parent):
        """Create the Hotkeys configuration tab with bind/delete controls."""
        parent.columnconfigure(0, weight=1)
        
        title_lbl = ttk.Label(parent, text="Hotkey Bindings (Function Keys 1-8)", font=("Arial", 11, "bold"))
        title_lbl.grid(row=0, column=0, sticky="w", padx=10, pady=(10, 5))
        
        info_lbl = ttk.Label(parent, text="Customize which F-key is bound to each function", foreground="gray")
        info_lbl.grid(row=1, column=0, sticky="w", padx=10, pady=(0, 10))
        
        container = ttk.Frame(parent)
        container.grid(row=2, column=0, sticky="nsew", padx=10, pady=5)
        container.columnconfigure(0, weight=1)
        parent.rowconfigure(2, weight=1)
        
        self.hotkey_controls = {}
        hotkey_list = [
            ("mine", "Mining Tool", "F1"),
            ("chop", "Chopping Tool", "F2"),
            ("hp_buff", "HP Buff / Potion", "F3"),
            ("buff", "Self Heal Buff", "F5"),
            ("buff_self", "Tiny Regen Buff", "F6"),
            ("sit_cancel", "Switch To Sit Item", "F7"),
            ("weapon", "Switch To Combat Item", "F8"),
            ("stand", "Sit Down/Stand Up", "F11"),
        ]

        row = 0
        for key, label, default_f_key in hotkey_list:
            lbl = ttk.Label(container, text=f"{label}:", width=25)
            lbl.grid(row=row, column=0, sticky="w", pady=5)
            
            current_key = HOTKEY_BINDINGS.get(key, default_f_key)
            current_lbl = ttk.Label(container, text=current_key.upper(), foreground="red", width=6)
            current_lbl.grid(row=row, column=1, sticky="w", padx=(5, 5))
            
            change_btn = ttk.Button(container, text="Change", width=8,
                                   command=lambda k=key, l=current_lbl: self._open_hotkey_dialog(k, l))
            change_btn.grid(row=row, column=2, padx=(2, 2))
            
            reset_btn = ttk.Button(container, text="Reset", width=8,
                                  command=lambda k=key, d=default_f_key, l=current_lbl: self._reset_hotkey(k, d, l))
            reset_btn.grid(row=row, column=3, padx=(2, 2))
            
            self.hotkey_controls[key] = {
                'label': current_lbl,
                'default': default_f_key,
                'key': key
            }
            
            row += 1
        
        button_frame = ttk.Frame(container)
        button_frame.grid(row=row, column=0, columnspan=4, sticky="ew", pady=(15, 5))
        
        ttk.Button(button_frame, text="Save All Changes", 
                  command=self._save_all_hotkeys).pack(side="left", padx=5)
        ttk.Button(button_frame, text="Reset All to Default",
                  command=self._reset_all_hotkeys).pack(side="left", padx=5)
        
    def _open_hotkey_dialog(self, hotkey_key, label_widget):
        """Open dialog to set a new hotkey for the given function."""
        dialog = tk.Toplevel(self.root)
        dialog.title(f"Set Hotkey for {hotkey_key.replace('_', ' ').title()}")
        dialog.geometry("400x200")
        dialog.resizable(False, False)
        
        dialog.transient(self.root)
        dialog.grab_set()
        
        frame = ttk.Frame(dialog, padding=20)
        frame.pack(fill="both", expand=True)
        
        ttk.Label(frame, text="Press the F-key you want to bind to this function:", 
                 wraplength=350).pack(pady=(0, 20))
        
        current_key = HOTKEY_BINDINGS.get(hotkey_key, "Unknown")
        ttk.Label(frame, text=f"Current: {current_key.upper()}", 
                 foreground="red", font=("Arial", 10, "bold")).pack(pady=(0, 20))
        
        status_lbl = ttk.Label(frame, text="Waiting for key press...", foreground="orange")
        status_lbl.pack(pady=10)
        
        entry = ttk.Entry(frame, width=20, justify="center")
        entry.pack(pady=10)
        entry.focus()
        
        def on_key_press(event):
            """Capture the key pressed and validate it's an F-key."""
            key_name = event.keysym.lower()
            
            if key_name.startswith('f') and key_name[1:].isdigit():
                f_num = int(key_name[1:])
                if 1 <= f_num <= 12:
                    entry.delete(0, tk.END)
                    entry.insert(0, key_name)
                    status_lbl.config(text=f"OK: {key_name.upper()} selected", foreground="green")
                    return
            
            status_lbl.config(text="Invalid! Press an F-key (F1-F12)", foreground="red")
        
        entry.bind("<KeyPress>", on_key_press)
        
        btn_frame = ttk.Frame(frame)
        btn_frame.pack(pady=(20, 0))
        
        def apply_hotkey():
            """Apply the selected hotkey."""
            key_val = entry.get().lower()
            if key_val.startswith('f') and key_val[1:].isdigit():
                HOTKEY_BINDINGS[hotkey_key] = key_val
                label_widget.config(text=key_val.upper(), foreground="green")
                status_lbl.config(text=f"OK: Hotkey set to {key_val.upper()}", foreground="green")
                dialog.after(500, dialog.destroy)
            else:
                status_lbl.config(text="Please press a valid F-key", foreground="red")
        
        ttk.Button(btn_frame, text="Apply", command=apply_hotkey).pack(side="left", padx=5)
        ttk.Button(btn_frame, text="Cancel", command=dialog.destroy).pack(side="left", padx=5)
    
    def _reset_hotkey(self, hotkey_key, default_key, label_widget):
        """Reset a single hotkey to its default."""
        HOTKEY_BINDINGS[hotkey_key] = default_key
        label_widget.config(text=default_key.upper(), foreground="red")
        _log_info(f"[GUI] Reset hotkey '{hotkey_key}' to {default_key.upper()}")
    
    def _save_all_hotkeys(self):
        """Save all hotkey changes to the config file."""
        try:
            save_settings()
            
            _log_info("[GUI] Hotkey bindings saved to config.json")
            for control in self.hotkey_controls.values():
                control['label'].config(foreground="green")
                self.root.after(1500, lambda: control['label'].config(foreground="red"))
        except Exception as e:
            _log_warn(f"[GUI] Error saving hotkeys: {e}")
    
    def _reset_all_hotkeys(self):
        """Reset all hotkeys to their default values."""
        defaults = {
            "mine": "f1",
            "chop": "f2",
            "hp_buff": "f3",
            "buff": "f5",
            "buff_self": "f6",
            "sit_cancel": "f7",
            "weapon": "f8",
            "stand": "f11",
        }

        HOTKEY_BINDINGS.clear()
        HOTKEY_BINDINGS.update(defaults)
        
        for key, control in self.hotkey_controls.items():
            control['label'].config(text=defaults[key].upper(), foreground="red")
        
        _log_info("[GUI] All hotkeys reset to defaults")
        self._save_all_hotkeys()

    def _set_global_bool(self, global_name: str, value: bool, log_message: Optional[str] = None, *, status_label=None, on_text: str = "Status: ENABLED", off_text: str = "Status: DISABLED", state_on: str = "ENABLED", state_off: str = "DISABLED", post_apply=None):
        value = bool(value)
        _set_config_value(global_name, value)
        if status_label is not None:
            self._set_bool_status(status_label, value, on_text, off_text)
        if post_apply is not None:
            try:
                post_apply(value)
            except Exception:
                pass
        if log_message:
            _log_info(log_message.format(value=value, state=state_on if value else state_off))
        save_settings()

    def _apply_capped_seconds_setting(
        self,
        *,
        tk_var,
        global_name: str,
        status_label,
        label_name: str,
        cap: int = 300,
    ):
        """Shared GUI handler for positive integer second settings with upper cap."""
        current_value = int(_read_setting(global_name, 0))
        try:
            new_value = int(tk_var.get())
            if 0 < new_value <= cap:
                _set_config_value(global_name, new_value)
                status_label.config(text=f"Current: {new_value}s", foreground="green")
                _log_info(f"[GUI] {label_name} set to {new_value}s")
                save_settings()
                return

            tk_var.set(str(current_value))
            if new_value > cap:
                status_label.config(text=f"Max {cap}s allowed. Reset to {current_value}s", foreground="red")
                _log_info(f"[GUI] {label_name} too high (max {cap}s). Reset to {current_value}s")
            else:
                status_label.config(text=f"Must be positive. Reset to {current_value}s", foreground="red")
                _log_info(f"[GUI] {label_name} must be positive. Reset to {current_value}s")
        except ValueError:
            tk_var.set(str(current_value))
            status_label.config(text=f"Must be integer. Reset to {current_value}s", foreground="red")
            _log_info(f"[GUI] {label_name} must be an integer. Reset to {current_value}s")

    def _apply_bounded_int_setting(
        self,
        *,
        tk_var,
        global_name: str,
        min_value: int,
        max_value: int,
        status_label=None,
        status_fmt: str = "Current: {value}",
        clamp: bool = True,
    ):
        current_value = int(_read_setting(global_name, min_value))
        try:
            new_value = int(tk_var.get())
            if clamp:
                new_value = max(min_value, min(max_value, new_value))
            elif not (min_value <= new_value <= max_value):
                tk_var.set(str(current_value))
                if status_label:
                    status_label.config(text=f"Must be {min_value}-{max_value}. Kept: {current_value}", foreground="red")
                return False

            _set_config_value(global_name, new_value)
            if status_label:
                status_label.config(text=status_fmt.format(value=new_value), foreground="green")
            return True
        except ValueError:
            tk_var.set(str(current_value))
            if status_label:
                status_label.config(text=f"Must be integer. Kept: {current_value}", foreground="red")
            return False

    def _apply_bounded_float_setting(
        self,
        *,
        tk_var,
        global_name: str,
        min_value: float,
        max_value: float,
        status_label=None,
        status_fmt: str = "Current: {value}",
    ):
        current_value = float(_read_setting(global_name, min_value))
        try:
            new_value = float(tk_var.get())
            new_value = max(min_value, min(max_value, new_value))
            _set_config_value(global_name, new_value)
            if status_label:
                status_label.config(text=status_fmt.format(value=new_value), foreground="green")
            return True
        except ValueError:
            tk_var.set(str(current_value))
            if status_label:
                status_label.config(text=f"Must be number. Kept: {int(current_value)}s", foreground="red")
            return False

    def _finalize_setting_change(
        self,
        ok: bool,
        *,
        success_message: Optional[str] = None,
        failure_message: Optional[str] = None,
    ) -> bool:
        if ok:
            save_settings()
            if success_message:
                _log_info(success_message)
            return True
        if failure_message:
            _log_warn(failure_message)
        return False

    def _apply_simple_float_setting(self, *, tk_var, global_name: str, fallback_value: float, min_value: float, max_value: float, invalid_message: str, success_message: str, validator=None) -> bool:
        try:
            value = float(tk_var.get())
            if value < min_value or value > max_value:
                raise ValueError
            if validator and not validator(value):
                raise ValueError
        except ValueError:
            tk_var.set(str(fallback_value))
            _log_warn(invalid_message.format(value=fallback_value))
            return False

        _set_config_value(global_name, value)
        _log_info(success_message.format(value=value))
        save_settings()
        return True

    def _update_targets_display(self):
        if not hasattr(self, "targets_display"):
            return
        if MOB_ID_FILTERS:
            self.targets_display.config(text=", ".join(map(str, sorted(MOB_ID_FILTERS))), foreground="green")
        else:
            self.targets_display.config(text="No targets set", foreground="red")

    def on_home_toggle(self):
        self._set_global_bool(
            CFG_RUN_HOME_AFTER_KILL,
            self.home_toggle_var.get(),
            log_message="[TOGGLE] RUN_HOME_AFTER_KILL = {value}",
        )

    def _refresh_protection_status(self):
        if self.ignore_prot_var.get():
            self.protection_status.config(text="Protection: DISABLED (boss mode)", foreground="red")
        else:
            self.protection_status.config(text="Protection: ENABLED", foreground="green")

    def on_f5_taps_change(self, event=None):
        ok = self._apply_bounded_int_setting(
            tk_var=self.f5_taps_var,
            global_name=CFG_F5_TAP_COUNT,
            min_value=0,
            max_value=50,
            status_label=self.f5_taps_status,
            status_fmt="Current: {value}",
            clamp=True,
        )
        self._finalize_setting_change(
            ok,
            success_message=f"[GUI] F5 tap count set to {F5_TAP_COUNT}",
            failure_message="[GUI] F5 tap count must be an integer",
        )

    def on_kills_per_home_change(self, event=None):
        ok = self._apply_bounded_int_setting(
            tk_var=self.kills_per_home_var,
            global_name=CFG_HOME_AFTER_KILLS_N,
            min_value=1,
            max_value=999,
            status_label=self.kills_per_home_status,
            status_fmt="Current: {value}",
            clamp=True,
        )
        self._finalize_setting_change(
            ok,
            success_message=f"[GUI] Home after N kills set to {HOME_AFTER_KILLS_N}",
            failure_message="[GUI] Home-after-kills must be an integer",
        )

    def on_hp_home_toggle(self):
        self._set_global_bool(
            CFG_HP_HOME_ENABLED,
            self.hp_home_toggle_var.get(),
            log_message="[TOGGLE] HP_HOME_ENABLED = {value}",
        )

    def on_hp_home_thresholds_change(self, event=None):
        try:
            low = max(1.0, min(float(self.hp_home_low_var.get()), 99.0))
            high = max(low + 1.0, min(float(self.hp_home_high_var.get()), 99.0))
            _set_config_value(CFG_HP_HOME_LOW_PCT, low)
            _set_config_value(CFG_HP_HOME_HIGH_PCT, high)
            self.hp_home_low_var.set(str(int(low)))
            self.hp_home_high_var.set(str(int(high)))
            self.hp_home_status.config(text=f"Trigger < {int(low)}%, stand at >= {int(high)}%", foreground="green")
            _log_info(f"[GUI] HP home thresholds set to low={low}%, high={high}%")
            save_settings()
        except ValueError:
            self.hp_home_low_var.set(str(int(HP_HOME_LOW_PCT)))
            self.hp_home_high_var.set(str(int(HP_HOME_HIGH_PCT)))
            self.hp_home_status.config(text=f"Trigger < {int(HP_HOME_LOW_PCT)}%, stand at >= {int(HP_HOME_HIGH_PCT)}% (invalid input)", foreground="red")
            _log_warn("[GUI] Invalid HP home thresholds; reverting.")

    def on_wander_timeout_change(self, event=None):
        ok = self._apply_bounded_float_setting(
            tk_var=self.wander_timeout_var,
            global_name=CFG_WANDER_TIMEOUT_S,
            min_value=2.0,
            max_value=300.0,
            status_label=self.wander_timeout_status,
            status_fmt="Current: {value:.0f}s",
        )
        self._finalize_setting_change(
            ok,
            success_message=f"[GUI] Wander timeout set to {WANDER_TIMEOUT_S:.0f}s",
            failure_message="[GUI] Wander timeout must be a number",
        )

    def on_protection_toggle(self):
        self._set_global_bool(
            CFG_IGNORE_PROTECTION,
            self.ignore_prot_var.get(),
            log_message="[GUI] Protection: {state}",
            state_on="DISABLED (boss mode)",
            state_off="ENABLED",
            post_apply=lambda value: manager.set_ignore_protection(value),
        )
        self._refresh_protection_status()

    def create_styles(self):
        style = ttk.Style(self.root)
        style.theme_use('clam')
        if DARK_MODE:
            colors = {
                'bg_primary': '#1a1f2e',
                'bg_secondary': '#2d3442',
                'bg_tertiary': '#3a4454',
                'fg_primary': '#e8eef7',
                'fg_secondary': '#b4bcc9',
                'fg_muted': '#7a8599',
                'accent_success': '#10b981',
                'accent_danger': '#ef4444',
                'accent_warning': '#f59e0b',
                'accent_info': '#3b82f6',
                'accent_hover': '#f0f4f8',
                'border': '#3a4454',
                'border_light': '#4a5568',
                'shadow': '#00000040',
                'shadow_light': '#00000020',
                'hover': '#3a4454',
                'focus': '#3b82f6',
                'disabled_fg': '#5a6577',
                'disabled_bg': '#252d3a',
            }
        else:
            colors = {
                'bg_primary': '#f8f9fa',
                'bg_secondary': '#ffffff',
                'bg_tertiary': '#f1f3f5',
                'fg_primary': '#1a202c',
                'fg_secondary': '#4a5568',
                'fg_muted': '#a0aec0',
                'accent_success': '#10b981',
                'accent_danger': '#ef4444',
                'accent_warning': '#f59e0b',
                'accent_info': '#3b82f6',
                'accent_hover': '#060e27',
                'border': '#e2e8f0',
                'border_light': '#f1f5f9',
                'shadow': '#00000015',
                'shadow_light': '#0000000a',
                'hover': '#f0f4f8',
                'focus': '#3b82f6',
                'disabled_fg': '#cbd5e0',
                'disabled_bg': '#edf2f7',
            }

        self.root.configure(bg=colors['bg_primary'])
        def _cfg(style_name: str, **kwargs):
            style.configure(style_name, **kwargs)

        def _map(style_name: str, **kwargs):
            style.map(style_name, **kwargs)

        def _button_style(style_name: str, bg: str, active: str, pressed: str, *, fg: str = "white", font=("Segoe UI", 10), padding: int = 6):
            _cfg(style_name, background=bg, foreground=fg, font=font, borderwidth=1, relief='ridge', padding=padding, anchor='center')
            _map(
                style_name,
                background=[('!disabled', bg), ('active', active), ('pressed', pressed), ('disabled', colors['disabled_bg'])],
                foreground=[('!disabled', fg), ('disabled', colors['disabled_fg'])],
                relief=[('pressed', 'sunken'), ('!disabled', 'ridge')],
            )

        _cfg('TLabel', background=colors['bg_secondary'], foreground=colors['fg_primary'], font=('Segoe UI', 10))
        _cfg('Heading.TLabel', background=colors['bg_secondary'], foreground=colors['fg_primary'], font=('Segoe UI', 11, 'bold'))
        _cfg('Muted.TLabel', background=colors['bg_secondary'], foreground=colors['fg_muted'], font=('Segoe UI', 9))
        _cfg('TFrame', background=colors['bg_secondary'])
        _cfg('Card.TFrame', background=colors['bg_secondary'], relief='flat', borderwidth=0)
        _cfg(
            'TLabelframe',
            background=colors['bg_secondary'],
            foreground=colors['fg_primary'],
            font=('Segoe UI', 11, 'bold'),
            borderwidth=1,
            relief='solid',
            lightcolor='#f5f7fa',
            darkcolor='#d0d8e0',
        )
        _cfg('TLabelframe.Label', background=colors['bg_secondary'], foreground=colors['fg_primary'], font=('Segoe UI', 11, 'bold'), padding=4)
        _map(
            'TLabelframe',
            background=[('!disabled', colors['bg_secondary']), ('disabled', colors['disabled_bg'])],
            foreground=[('!disabled', colors['fg_primary']), ('disabled', colors['disabled_fg'])],
        )

        _button_style('success.TButton', colors['accent_success'], '#059669', '#047857', font=('Segoe UI', 10, 'bold'))
        _button_style('danger.TButton', colors['accent_danger'], '#dc2626', '#b91c1c', font=('Segoe UI', 10, 'bold'))
        _button_style('TButton', colors['accent_info'], '#2563eb', '#1d4ed8')
        _button_style('secondary.TButton', colors['bg_secondary'], colors['hover'], colors['border_light'], fg=colors['fg_primary'], padding=5)

        _cfg(
            'TEntry',
            font=('Segoe UI', 10),
            fieldbackground=colors['bg_secondary'],
            background=colors['bg_secondary'],
            foreground=colors['fg_primary'],
            borderwidth=1,
            relief='groove',
            padding=3,
            insertcolor=colors['fg_primary'],
        )
        _map(
            'TEntry',
            fieldbackground=[('focus', colors['bg_secondary']), ('!disabled', colors['bg_secondary']), ('disabled', colors['disabled_bg'])],
            background=[('focus', colors['bg_secondary']), ('!disabled', colors['bg_secondary']), ('disabled', colors['disabled_bg'])],
            foreground=[('!disabled', colors['fg_primary']), ('disabled', colors['disabled_fg'])],
            bordercolor=[('focus', colors['accent_info']), ('!focus', colors['border'])],
        )
        _cfg(
            'TCombobox',
            font=('Segoe UI', 10),
            fieldbackground=colors['bg_secondary'],
            background=colors['accent_info'],
            foreground=colors['fg_primary'],
            borderwidth=1,
            relief='groove',
            padding=3,
        )
        _map(
            'TCombobox',
            fieldbackground=[('focus', colors['bg_secondary']), ('!disabled', colors['bg_secondary']), ('disabled', colors['disabled_bg'])],
            background=[('focus', colors['accent_info']), ('disabled', colors['disabled_bg'])],
            foreground=[('!disabled', colors['fg_primary']), ('disabled', colors['disabled_fg'])],
            bordercolor=[('focus', colors['accent_info']), ('!focus', colors['border'])],
        )

        for toggle_style in ('TCheckbutton', 'TRadiobutton'):
            _cfg(
                toggle_style,
                background=colors['bg_secondary'],
                foreground=colors['fg_primary'],
                font=('Segoe UI', 10),
                focuscolor='none',
                padding=2,
                relief='ridge',
                borderwidth=1,
            )
            _map(
                toggle_style,
                background=[('active', colors['bg_secondary']), ('disabled', colors['disabled_bg']), ('!disabled', colors['bg_secondary'])],
                foreground=[('disabled', colors['disabled_fg']), ('!disabled', colors['fg_primary'])],
            )

        _cfg(
            'TProgressbar',
            background=colors['accent_info'],
            troughcolor=colors['border_light'],
            bordercolor=colors['border'],
            lightcolor=colors['accent_info'],
            darkcolor=colors['shadow'],
            borderwidth=2,
            relief='groove',
        )
        for pb_style, pb_color in (
            ('success.Horizontal.TProgressbar', colors['accent_success']),
            ('warning.Horizontal.TProgressbar', colors['accent_warning']),
        ):
            _cfg(pb_style, background=pb_color, troughcolor=colors['border_light'], bordercolor=colors['border'], borderwidth=2, relief='groove')

        _cfg('TScale', background=colors['bg_secondary'], troughcolor=colors['border'], borderwidth=2, relief='groove', lightcolor='#ffffff', darkcolor=colors['shadow'])
        _cfg('TPanedwindow', background=colors['bg_primary'], relief='flat', borderwidth=0)
        _cfg('TScrollbar', background=colors['bg_secondary'], troughcolor=colors['border_light'], borderwidth=0, lightcolor=colors['bg_secondary'], darkcolor=colors['bg_secondary'])
        _map('TScrollbar', background=[('active', colors['accent_info']), ('!disabled', colors['bg_secondary'])])
        _cfg(
            'Treeview',
            background=colors['bg_secondary'],
            foreground=colors['fg_primary'],
            fieldbackground=colors['bg_secondary'],
            font=('Segoe UI', 10),
            rowheight=24,
            borderwidth=1,
            relief='groove',
        )
        _cfg('Treeview.Heading', background=colors['bg_tertiary'], foreground=colors['fg_primary'], font=('Segoe UI', 10, 'bold'), borderwidth=1, relief='ridge')
        _map('Treeview', background=[('selected', colors['accent_info']), ('!disabled', colors['bg_secondary'])], foreground=[('selected', 'white'), ('!disabled', colors['fg_primary'])])
        _map('Treeview.Heading', background=[('active', colors['hover']), ('!disabled', colors['bg_tertiary'])])

    def on_click_toggle(self):
        self._set_global_bool(
            CFG_CLICKING_ENABLED,
            self.click_toggle_var.get(),
            log_message="[TOGGLE] CLICKING_ENABLED = {value}",
        )

    def on_fast_click_toggle(self):
        self._set_global_bool(
            CFG_FAST_CLICK,
            self.fast_click_var.get(),
            log_message="[TOGGLE] FAST_CLICK = {value}",
        )

    def on_hp_buff_toggle(self):
        self._set_global_bool(
            CFG_HP_BUFFS_ENABLED,
            self.hp_buff_var.get(),
            log_message="[TOGGLE] HP_BUFFS_ENABLED = {value}",
        )

    def on_hp_buff_threshold_change(self, event=None):
        self._apply_simple_float_setting(
            tk_var=self.hp_buff_threshold_var,
            global_name=CFG_HP_BUFF_THRESHOLD_PCT,
            fallback_value=HP_BUFF_THRESHOLD_PCT,
            min_value=0.001,
            max_value=100.0,
            invalid_message="[HP BUFF] Invalid threshold; keeping {value}",
            success_message="[HP BUFF] HP_BUFF_THRESHOLD_PCT = {value}",
        )

    def on_hp_buff_target_change(self, event=None):
        threshold = float(_read_setting(CFG_HP_BUFF_THRESHOLD_PCT, HP_BUFF_THRESHOLD_PCT))
        self._apply_simple_float_setting(
            tk_var=self.hp_buff_target_var,
            global_name=CFG_HP_BUFF_TARGET_PCT,
            fallback_value=HP_BUFF_TARGET_PCT,
            min_value=0.001,
            max_value=100.0,
            invalid_message="[HP BUFF] Invalid target; keeping {value}",
            success_message="[HP BUFF] HP_BUFF_TARGET_PCT = {value}",
            validator=lambda value: value > threshold,
        )

    def on_buff_click_toggle(self):
        self._set_global_bool(
            CFG_CLICK_BUFFS_ENABLED,
            self.buff_click_var.get(),
            log_message="[TOGGLE] CLICK_BUFFS_ENABLED = {value}",
        )

    def on_buff_interval_change(self, event=None):
        self._apply_simple_float_setting(
            tk_var=self.buff_interval_var,
            global_name=CFG_CLICK_BUFF_INTERVAL_S,
            fallback_value=CLICK_BUFF_INTERVAL_S,
            min_value=0.001,
            max_value=3600.0,
            invalid_message="[BUFF] Invalid interval; keeping {value}",
            success_message="[BUFF] CLICK_BUFF_INTERVAL_S = {value}",
        )

    def on_avoid_players_toggle(self):
        self._set_global_bool(
            CFG_AVOID_OTHER_PLAYERS,
            self.avoid_players_var.get(),
            log_message="[GUI] Avoid other players: {state}",
        )

    def _refresh_other_players_panel(self):
        """Refresh live other-player list, keyed by player name to avoid duplicate rows."""
        if not hasattr(self, "other_players_tree"):
            return

        try:
            _, map_snapshot = _get_map_snapshot()
            snapshot = [item for item in map_snapshot if item.get("type") == "other_player"]
        except Exception:
            snapshot = []

        try:
            self_addr = (self_player_address or "").upper()
            self_name = (self_player_name or "").strip()
            self_meta = {}
            if self_addr:
                self_meta = _get_other_player_meta(self_addr)

            self_xy = self.player_data_manager.get_data() or {}
            snapshot.append({
                "type": "other_player",
                "name": self_name or self_meta.get("name") or "ME",
                "level": self_meta.get("level"),
                "facing": self_meta.get("facing") if isinstance(self_meta.get("facing"), int) else self_xy.get("direction"),
                "X": self_xy.get("x"),
                "Y": self_xy.get("y"),
                "address_x": self_addr or "",
                "_is_self": True,
            })
        except Exception:
            pass

        def _fmt_addr(addr_hex: str) -> str:
            if not addr_hex:
                return "0x?"
            try:
                return f"0x{int(str(addr_hex), 16):X}"
            except Exception:
                return str(addr_hex)

        merged: Dict[str, Dict[str, Any]] = {}
        for item in snapshot:
            try:
                name = (item.get("name") or "").strip()
                level = item.get("level")
                facing = item.get("facing")
                x = item.get("X")
                y = item.get("Y")
                addr = (item.get("address_x") or "").upper()
                is_self = bool(item.get("_is_self", False))

                name_key = _player_name_key(name)
                key = f"name:{name_key}" if name_key else f"addr:{addr or id(item)}"

                row = merged.get(key)
                if row is None:
                    merged[key] = {
                        "name": name or "?",
                        "addr": addr,
                        "level": level if isinstance(level, int) else None,
                        "facing": facing if isinstance(facing, int) else None,
                        "x": x,
                        "y": y,
                        "is_self": is_self,
                    }
                else:
                    if name and row.get("name") == "?":
                        row["name"] = name
                    if addr and not row.get("addr"):
                        row["addr"] = addr
                    if isinstance(level, int):
                        row["level"] = level
                    if isinstance(facing, int):
                        row["facing"] = facing
                    if x is not None and y is not None:
                        row["x"] = x
                        row["y"] = y
                    if is_self:
                        row["is_self"] = True
            except Exception:
                continue

        active_keys = set(merged.keys())
        existing_keys = set(self._other_player_row_ids.keys())
        tree = self.other_players_tree

        for key in (existing_keys - active_keys):
            iid = self._other_player_row_ids.pop(key, None)
            if iid:
                try:
                    tree.delete(iid)
                except Exception:
                    pass

        sorted_keys = sorted(active_keys, key=lambda k: (
            0 if merged[k].get("is_self") else 1,
            str(merged[k].get("name") or "").casefold(),
            str(k),
        ))

        for idx, key in enumerate(sorted_keys):
            row = merged[key]
            name_display = f"{row.get('name') or '?'}({_fmt_addr(row.get('addr') or '')})"
            values = (
                name_display,
                row.get("level") if isinstance(row.get("level"), int) else "?",
                row.get("facing") if isinstance(row.get("facing"), int) else "?",
                row.get("x") if row.get("x") is not None else "?",
                row.get("y") if row.get("y") is not None else "?",
            )
            iid = self._other_player_row_ids.get(key)
            if iid:
                try:
                    tree.item(iid, values=values)
                except Exception:
                    iid = None
            if not iid:
                iid = tree.insert("", "end", values=values)
                self._other_player_row_ids[key] = iid
            try:
                tree.move(iid, "", idx)
            except Exception:
                pass

        self._set_label_cached("other_players:summary", self.other_players_summary, f"Active: {len(sorted_keys)}")

    def on_fast_click_params_change(self, event=None):
        ok_burst = self._apply_bounded_int_setting(
            tk_var=self.fast_click_burst_var,
            global_name=CFG_FAST_CLICK_BURST_COUNT,
            min_value=1,
            max_value=10,
            clamp=True,
        )
        ok_gap = self._apply_bounded_float_setting(
            tk_var=self.fast_click_gap_var,
            global_name=CFG_FAST_CLICK_GAP_S,
            min_value=0.02,
            max_value=1.0,
        )
        if ok_burst or ok_gap:
            _log_info(f"[FAST_CLICK] burst={FAST_CLICK_BURST_COUNT} gap={FAST_CLICK_GAP_S:.3f}s")
            save_settings()
        else:
            _log_warn("[FAST_CLICK] Invalid burst/gap; keeping current values.")

    def _update_session_exp_metrics(self, stats: Optional[Dict[str, Any]], now_ts: float):
        """Update session EXP and EXP/hr labels while session tracking is active."""
        if not self._session_exp_active or not stats:
            return

        exp_raw = stats.get("exp")
        try:
            exp_now = int(exp_raw)
        except Exception:
            return

        if self._session_exp_last_value is None:
            self._session_exp_last_value = exp_now
        else:
            if exp_now >= self._session_exp_last_value:
                self._session_exp_total += (exp_now - self._session_exp_last_value)
            self._session_exp_last_value = exp_now

        started_ts = self._session_exp_started_at if self._session_exp_started_at is not None else now_ts
        elapsed_s = max(1.0, float(now_ts - started_ts))
        exp_per_hour = int((self._session_exp_total * 3600.0) / elapsed_s)

        try:
            self.session_exp_label.config(text=f"{self._session_exp_total:,}")
            self.session_exp_hour_label.config(text=f"{exp_per_hour:,}")
        except Exception:
            pass

    def _set_bool_status(self, label_widget, enabled: bool, on_text: str, off_text: str):
        self._set_label_cached(
            key=f"label:{id(label_widget)}",
            label_widget=label_widget,
            text=(on_text if enabled else off_text),
            foreground=("green" if enabled else "red"),
        )

    def _set_var_if_unfocused(self, focused_widget, entry_attr: str, tk_var, value: Any):
        entry_widget = getattr(self, entry_attr, None)
        if entry_widget is None or focused_widget is not entry_widget:
            self._set_var_cached(f"var:{id(tk_var)}", tk_var, str(value))

    def _set_var_cached(self, key: str, tk_var, value: Any):
        if self._ui_cache.get(key) != value:
            tk_var.set(value)
            self._ui_cache[key] = value

    def _set_label_cached(self, key: str, label_widget, text: str, foreground: Optional[str] = None):
        target = (text, foreground)
        if self._ui_cache.get(key) == target:
            return
        kwargs = {"text": text}
        if foreground is not None:
            kwargs["foreground"] = foreground
        label_widget.config(**kwargs)
        self._ui_cache[key] = target

    def _set_button_state_cached(self, key: str, button_widget, state: str):
        if self._ui_cache.get(key) != state:
            button_widget.config(state=state)
            self._ui_cache[key] = state

    def _refresh_runtime_status_labels(self):
        self._set_label_cached("status:flank_range", self.flank_range_status, f"Current: {FLANK_RANGE}")
        self._set_bool_status(self.boss_aggro_status, bool(BOSS_AGGRO_TOGGLE), "Status: ENABLED", "Status: DISABLED")
        self._set_label_cached("status:sit_timer", self.sit_timer_status, f"Current: {SIT_TIMER_SECONDS}s")
        self._set_label_cached("status:last_moved", self.last_moved_timer_status, f"Current: {LAST_MOVED_TIMER_SECONDS}s")
        self._set_label_cached("status:f5_taps", self.f5_taps_status, f"Current: {F5_TAP_COUNT}")
        self._set_label_cached("status:wander_timeout", self.wander_timeout_status, f"Current: {int(WANDER_TIMEOUT_S)}s")
        self._set_label_cached("status:kills_home", self.kills_per_home_status, f"Current: {HOME_AFTER_KILLS_N}")
        self._set_label_cached("status:home_pos", self.home_status, f"Current: ({HOME_POS[0]}, {HOME_POS[1]})")
        if bot_running:
            self._set_label_cached("status:bot", self.bot_status_label, "Status: RUNNING", "green")
            self._set_button_state_cached("state:start_btn", self.start_bot_button, tk.DISABLED)
            self._set_button_state_cached("state:stop_btn", self.stop_bot_button, tk.NORMAL)
        else:
            self._set_label_cached("status:bot", self.bot_status_label, "Status: STOPPED", "red")
            self._set_button_state_cached("state:start_btn", self.start_bot_button, tk.NORMAL)
            self._set_button_state_cached("state:stop_btn", self.stop_bot_button, tk.DISABLED)

    def _refresh_quarantine_label(self, now_ts: float):
        try:
            remaining_quarantine = float(speech_quarantine_until) - now_ts
            if remaining_quarantine > 0:
                src = (speech_quarantine_source or "??").strip()
                reason = (speech_quarantine_reason or "").strip()
                reason_short = reason[:56]
                secs_left = int(remaining_quarantine) if remaining_quarantine.is_integer() else int(remaining_quarantine) + 1
                text = f"Quarantine: ACTIVE ({secs_left}s) from {src}"
                if reason_short:
                    text = f"{text} | {reason_short}"
                self._set_label_cached("speech:quarantine", self.speech_quarantine_lbl, text, "#ff5f5f")
            else:
                self._set_label_cached("speech:quarantine", self.speech_quarantine_lbl, "Quarantine: OFF", "#7CFC00")
        except Exception:
            pass

    def _refresh_chat_panel(self):
        try:
            current_chat = list(recent_speech_log)[-30:]
            if current_chat == self._last_chat_snapshot:
                return
            self.chat_list.delete(0, tk.END)
            for ts, who, text in current_chat:
                hh = time.strftime("%H:%M:%S", time.localtime(ts))
                who_label = str(who).strip() if who else "??"
                self.chat_list.insert(tk.END, f"{hh} {who_label}: {text[:70]}")
            if recent_speech_log:
                ts, who, text = recent_speech_log[-1]
                self._set_label_cached("speech:last", self.last_speech_lbl, f"Last: {text[:80]}")
            else:
                self._set_label_cached("speech:last", self.last_speech_lbl, "Last: ")
            self._last_chat_snapshot = current_chat
        except Exception:
            pass

    def _map_render_signature(self, player_data: Dict[str, Any]):
        """Lightweight signature used to skip redundant map redraws."""
        map_ver = _get_map_version()
        path_len = len(current_path_tiles)
        path_head = current_path_tiles[0] if path_len else None
        path_tail = current_path_tiles[-1] if path_len else None
        return (
            map_ver,
            int(player_data.get("x", 0)),
            int(player_data.get("y", 0)),
            int(player_data.get("direction", 0)),
            self.show_coords_var.get() if hasattr(self, "show_coords_var") else False,
            self._hovered_tile,
            path_len,
            path_head,
            path_tail,
            self.canvas.winfo_width(),
            self.canvas.winfo_height(),
        )

    def update_ui(self):
        """
        Event-driven UI updates for efficiency:
        - Map/NPCs: 10 Hz (100ms)
        - Stats: 2 Hz (500ms)  
        - Chat: only when new messages
        - Player position: 10 Hz (100ms)
        """
        if not getattr(self, "_ui_running", True):
            return

        now = time.time()
        
        data = self.player_data_manager.get_data()
        self._set_label_cached("player:x", self.labels["X"], str(data["x"]))
        self._set_label_cached("player:y", self.labels["Y"], str(data["y"]))
        self._set_label_cached("player:dir", self.labels["Direction"], str(data["direction"]))
        self._refresh_walkable_record_status(now)
        self._refresh_map_id_ui_and_autoload()

        if now - self._last_runtime_update > UI_RUNTIME_REFRESH_S:
            self._set_var_cached("var:click_toggle", self.click_toggle_var, bool(CLICKING_ENABLED))
            self._set_var_cached("var:fast_click", self.fast_click_var, bool(FAST_CLICK))
            if hasattr(self, "auto_mapid_var"):
                self._set_var_cached("var:auto_mapid", self.auto_mapid_var, bool(AUTO_LOAD_MAP_BY_ID))
            self._refresh_runtime_status_labels()
            self._refresh_walkable_warning_label()

            try:
                focused = self.root.focus_get()
            except Exception:
                focused = None
            self._set_var_if_unfocused(focused, "fast_click_burst_entry", self.fast_click_burst_var, FAST_CLICK_BURST_COUNT)
            self._set_var_if_unfocused(focused, "fast_click_gap_entry", self.fast_click_gap_var, FAST_CLICK_GAP_S)
            self._refresh_quarantine_label(now)
            self._last_runtime_update = now

        if now - self._last_map_draw > UI_MAP_REFRESH_S:
            sig = self._map_render_signature(data)
            if sig != self._last_map_signature:
                self.draw_map()
                self._last_map_signature = sig
            self._last_map_draw = now
        if now - self._last_other_players_update > UI_OTHER_PLAYERS_REFRESH_S:
            self._refresh_other_players_panel()
            self._last_other_players_update = now
        if now - self._last_stats_update > UI_STATS_REFRESH_S:
            stats = read_all_stats()
            if stats:
                for key, val in stats.items():
                    if key in self.stats_labels:
                        self._set_label_cached(f"stats:{key}", self.stats_labels[key], str(val if val is not None else "N/A"))
                self._update_session_exp_metrics(stats, now)
            
            try:
                curr_hp = read_current_hp()  # Get HP from Frida hook
                curr_mp = read_current_mana()  # Get mana from Frida hook
                max_hp = stats.get('max_hp', 0) if stats else 0
                max_mp = stats.get('max_mana', 0) if stats else 0
                
                if curr_hp is not None and max_hp:
                    hp_text = f"{curr_hp}/{max_hp}"
                else:
                    hp_text = "N/A"
                self._set_label_cached("player:hp_text", self.hp_mp_label, hp_text)
                
                if curr_mp is not None and max_mp:
                    mp_text = f"{curr_mp}/{max_mp}"
                else:
                    mp_text = "N/A"
                self._set_label_cached("player:mp_text", self.mp_label, mp_text)
            except Exception as e:
                _warn_throttled("ui:hpmp", f"[UI] HP/MP panel refresh error: {e}", interval_s=5.0)
            
            self._last_stats_update = now
        if now - self._last_chat_update > UI_CHAT_REFRESH_S:
            self._refresh_chat_panel()
            self._last_chat_update = now

        try:
            if self._ui_running:
                self.root.after(UI_UPDATE_INTERVAL_MS, self.update_ui)
        except Exception as e:
            _warn_throttled("ui:schedule", f"[UI] update scheduling error: {e}", interval_s=5.0)

    def _collect_map_snapshots(self):
        """Capture map snapshots once per frame for consistent render/counts."""
        try:
            _, map_snapshot = _get_map_snapshot()
            npc_snapshot = []
            other_players_snapshot = []
            for item in map_snapshot:
                item_type = item.get("type")
                if item_type == "npc":
                    npc_snapshot.append(item)
                elif item_type == "other_player":
                    other_players_snapshot.append(item)
        except Exception:
            npc_snapshot = []
            other_players_snapshot = []

        try:
            map_info_snapshot = list(MAP_INFO_ENTITIES or [])
        except Exception:
            map_info_snapshot = []
        return npc_snapshot, other_players_snapshot, map_info_snapshot

    def _update_entity_counts(self, npc_snapshot=None, other_players_snapshot=None):
        """Update the player and NPC count labels."""
        try:
            if npc_snapshot is None or other_players_snapshot is None:
                npc_snapshot, other_players_snapshot, _ = self._collect_map_snapshots()
            npc_count = len(npc_snapshot)
            player_count = 1 + len(other_players_snapshot)  # include self
            self._set_label_cached("map:player_count", self.player_count_label, str(player_count))
            self._set_label_cached("map:npc_count", self.npc_count_label, str(npc_count))
        except Exception:
            pass

    def draw_map(self):
        npc_snapshot, other_players_snapshot, map_info_snapshot = self._collect_map_snapshots()
        self._update_entity_counts(npc_snapshot, other_players_snapshot)

        canvas = self.canvas
        canvas.delete("all")
        canvas_w = max(canvas.winfo_width(), 1)
        canvas_h = max(canvas.winfo_height(), 1)
        tile_w = self._map_tile_w
        tile_h = tile_w / 2
        grid_radius = self._map_grid_radius
        cx = (canvas_w - tile_w) / 2
        cy = (canvas_h - tile_h) / 2
        px, py = self._player_coords()
        show_coords = bool(self.show_coords_var.get())

        create_rectangle = canvas.create_rectangle
        create_polygon = canvas.create_polygon
        create_text = canvas.create_text
        create_oval = canvas.create_oval
        create_line = canvas.create_line
        create_rectangle(0, 0, canvas_w, canvas_h, fill="#0f132a", outline="")

        safe_coords = self._walkable_coords_cache
        hovered = self._hovered_tile
        mob_filters = MOB_ID_FILTERS

        def _in_view(tx, ty):
            return abs(tx - px) <= grid_radius + 1 and abs(ty - py) <= grid_radius + 1

        def _poly(tx, ty):
            return self._tile_polygon(px, py, tx, ty, tile_w, tile_h, cx, cy)

        def _center(tx, ty):
            return self._tile_center(px, py, tx, ty, tile_w, tile_h, cx, cy)

        def _center_ok(center):
            if not center:
                return False
            cx0, cy0 = center
            if cx0 is None or cy0 is None:
                return False
            if isinstance(cx0, float) and (cx0 != cx0 or abs(cx0) > 10000):
                return False
            return True

        for entity in map_info_snapshot:
            try:
                ex, ey = entity['x'], entity['y']
                if not _in_view(ex, ey):
                    continue
                create_polygon(_poly(ex, ey), fill="", outline="#00FFFF", width=2, dash=(2, 2))
                center = _center(ex, ey)
                if _center_ok(center):
                    direction = entity.get('direction', '?')
                    create_text(center[0], center[1] - 10, text=f"ID:{entity['id']}\nD:{direction}", fill="#00FFFF", font=("Arial", 7, "bold"))
            except Exception:
                pass

        for dx in range(-grid_radius, grid_radius + 1):
            for dy in range(-grid_radius, grid_radius + 1):
                tx = px + dx
                ty = py + dy
                try:
                    fill = "#30405c" if (tx, ty) in safe_coords else "#1a1f2a"
                    if hovered == (tx, ty):
                        fill = "#fff4a0"
                    create_polygon(_poly(tx, ty), fill=fill, outline="#2b3348", width=1)
                    if show_coords:
                        center = _center(tx, ty)
                        if _center_ok(center):
                            text_color = "#000" if (tx, ty) in safe_coords else "#fff"
                            create_text(center[0], center[1], text=f"{tx},{ty}", fill=text_color, font=("Arial", 8, "bold"))
                except Exception:
                    pass
        path_color = '#ffb347'
        path_fade_time = 1.0
        now = time.time()
        show_path = current_path_tiles and (path_fade_timestamp is None or (now - path_fade_timestamp < path_fade_time))
        if show_path:
            path_points = []
            for pt in current_path_tiles:
                center = _center(pt[0], pt[1])
                path_points.append(center)
                create_oval(center[0]-3, center[1]-3, center[0]+3, center[1]+3, fill=path_color, outline='#999', width=1)
            if len(path_points) > 1:
                flattened = [coord for point in path_points for coord in point]
                create_line(*flattened, fill=path_color, width=5, capstyle='round', joinstyle='round')

        try:
            create_polygon(_poly(px, py), fill="#3cff9b", outline="#81ffbf", width=2)
            center = _center(px, py)
            if _center_ok(center):
                label_text = f"{px},{py}" if show_coords else "ME"
                create_text(center[0], center[1], text=label_text, fill="#000", font=("Arial", 8, "bold"))
        except Exception:
            pass

        for item in npc_snapshot:
            try:
                nx, ny = item.get("X", px), item.get("Y", py)
                mob_id = item.get("unique_id")
                if not _in_view(nx, ny):
                    continue
                tracked = mob_id in mob_filters
                fill_color = "#ff2222" if tracked else "#fff9c4"
                create_polygon(_poly(nx, ny), fill=fill_color, outline="#555", width=1)
                center = _center(nx, ny)
                if _center_ok(center):
                    text_color = "#fff" if tracked else "#000"
                    id_text = str(mob_id) if mob_id is not None else "?"
                    if show_coords:
                        label_text = f"{nx},{ny}\nID:{id_text}"
                    elif tracked:
                        label_text = f"T:{id_text}"
                    else:
                        label_text = f"ID:{id_text}"
                    create_text(center[0], center[1], text=label_text, fill=text_color, font=("Arial", 7, "bold"))
            except Exception:
                pass
        for item in other_players_snapshot:
            try:
                player_x, player_y = item.get("X"), item.get("Y")
                player_name = (item.get("name") or "").strip()
                player_level = item.get("level")
                if not _in_view(player_x, player_y):
                    continue
                create_polygon(_poly(player_x, player_y), fill="#87CEEB", outline="#1E90FF", width=2)
                center = _center(player_x, player_y)
                if _center_ok(center):
                    if player_name:
                        core = f"{player_name}\nL{player_level}" if isinstance(player_level, int) else player_name
                    else:
                        core = f"L{player_level}" if isinstance(player_level, int) else "PLAYER"
                    label_text = f"{player_x},{player_y}\n{core}" if show_coords else core
                    create_text(
                        center[0],
                        center[1],
                        text=label_text,
                        fill="#fff",
                        font=("Arial", 7, "bold"),
                        justify="center",
                        anchor="center",
                        width=max(36, int(tile_w * 0.9)),
                    )
            except Exception:
                pass

    def _player_coords(self):
        try:
            data = self.player_data_manager.get_data() or {}
            x = int(round(float(data.get("x", 0))))
            y = int(round(float(data.get("y", 0))))
            return x, y
        except Exception:
            return 0, 0

    def _tile_polygon(self, px, py, tx, ty, tile_w, tile_h, cx, cy):
        dx = tx - px
        dy = ty - py
        iso_x = cx + (dx - dy) * (tile_w / 2)
        iso_y = cy + (dx + dy) * (tile_h / 2)
        half_w = tile_w / 2
        half_h = tile_h / 2
        return [
            (iso_x, iso_y + half_h),
            (iso_x + half_w, iso_y),
            (iso_x + tile_w, iso_y + half_h),
            (iso_x + half_w, iso_y + tile_h),
        ]

    def _tile_center(self, px, py, tx, ty, tile_w, tile_h, cx, cy):
        dx = tx - px
        dy = ty - py
        iso_x = cx + (dx - dy) * (tile_w / 2)
        iso_y = cy + (dx + dy) * (tile_h / 2)
        return iso_x + tile_w / 2, iso_y + tile_h / 2

    def _point_in_poly(self, x, y, poly):
        inside = False
        n = len(poly)
        for i in range(n):
            x1, y1 = poly[i]
            x2, y2 = poly[(i + 1) % n]
            if ((y1 > y) != (y2 > y)) and (x < (x2 - x1) * (y - y1) / (y2 - y1) + x1):
                inside = not inside
        return inside

    def _allow_map_mouse_update(self) -> bool:
        now = time.perf_counter()
        if (now - self._last_map_mouse_ts) < self._map_mouse_interval_s:
            return False
        self._last_map_mouse_ts = now
        return True

    def _tile_from_event(self, event):
        px, py = self._player_coords()
        tile_w = self._map_tile_w
        tile_h = tile_w / 2
        cx = (max(self.canvas.winfo_width(), 1) - tile_w) / 2
        cy = (max(self.canvas.winfo_height(), 1) - tile_h) / 2
        grid_radius = self._map_grid_radius
        for dx in range(-grid_radius, grid_radius + 1):
            for dy in range(-grid_radius, grid_radius + 1):
                tx = px + dx
                ty = py + dy
                poly = self._tile_polygon(px, py, tx, ty, tile_w, tile_h, cx, cy)
                if self._point_in_poly(event.x, event.y, poly):
                    return (tx, ty)
        return None

    def _line_between(self, start, end):
        if not start or not end:
            return []
        return list(bresenham.bresenham(start[0], start[1], end[0], end[1]))

    def _toggle_tile(self, coord):
        if coord is None:
            return
        if coord in self._walkable_coords_cache:
            self._walkable_coords_cache.discard(coord)
        else:
            self._walkable_coords_cache.add(coord)

    def _handle_simple_click(self, coord):
        if coord:
            self._toggle_tile(coord)
            self._save_walkable_tiles()

    def _on_map_mouse_drag_start(self, event):
        self._last_map_mouse_ts = 0.0
        tile = self._tile_from_event(event)
        if tile:
            self._drag_mode = 'remove' if tile in self._walkable_coords_cache else 'add'
            self._drag_start_tile = tile
            self._last_drag_tile = tile
        else:
            self._drag_mode = None
            self._drag_start_tile = None
            self._last_drag_tile = None
        self._dragged_tiles.clear()
        self._dragging = True
        self._hovered_tile = tile
        self.draw_map()

    def _on_map_mouse_drag_motion(self, event):
        if not self._allow_map_mouse_update():
            return
        if not self._dragging:
            return
        tile = self._tile_from_event(event)
        if tile and tile != self._last_drag_tile:
            segment = self._line_between(self._last_drag_tile or tile, tile)
            self._dragged_tiles.update(segment)
            self._last_drag_tile = tile
            self._hovered_tile = tile
            self.draw_map()

    def _on_map_mouse_drag_end(self, event):
        if not self._dragging:
            return
        self._dragging = False
        end_tile = self._tile_from_event(event)
        if end_tile and self._drag_start_tile:
            segment = self._line_between(self._drag_start_tile, end_tile)
            self._dragged_tiles.update(segment)
        if self._dragged_tiles and self._drag_mode:
            for coord in self._dragged_tiles:
                if self._drag_mode == 'add':
                    self._walkable_coords_cache.add(coord)
                else:
                    self._walkable_coords_cache.discard(coord)
            self._save_walkable_tiles()
        else:
            self._handle_simple_click(end_tile or self._hovered_tile)
        self._drag_mode = None
        self._dragged_tiles.clear()
        self._drag_start_tile = None
        self._last_drag_tile = None
        self.draw_map()
        self.root.after(50, self._bring_to_front)

    def _on_map_mouse_move(self, event):
        if not self._allow_map_mouse_update():
            return
        tile = self._tile_from_event(event)
        if tile != self._hovered_tile:
            self._hovered_tile = tile
            self.draw_map()

    def _on_map_mouse_leave(self, event):
        if self._hovered_tile is not None:
            self._hovered_tile = None
            self.draw_map()

    def run(self):
        self.root.mainloop()

    def _run_on_ui_thread(self, callback) -> bool:
        try:
            if not self._ui_running or not self.root.winfo_exists():
                return False
            self.root.after(0, callback)
            return True
        except Exception:
            return False

    def _set_bot_ui_state(self, running: bool):
        self.start_bot_button.config(state=(tk.DISABLED if running else tk.NORMAL))
        self.stop_bot_button.config(state=(tk.NORMAL if running else tk.DISABLED))
        self.bot_status_label.config(
            text=("Status: RUNNING" if running else "Status: STOPPED"),
            foreground=("green" if running else "red"),
        )

    def on_boss_aggro_toggle(self):
        self._set_global_bool(
            CFG_BOSS_AGGRO_TOGGLE,
            self.boss_aggro_var.get(),
            log_message="[GUI] Is Boss aggro?: {state}",
            status_label=self.boss_aggro_status,
        )

    def on_flank_range_change(self, event=None):
        ok = self._apply_bounded_int_setting(
            tk_var=self.flank_range_var,
            global_name=CFG_FLANK_RANGE,
            min_value=1,
            max_value=5,
            status_label=self.flank_range_status,
            status_fmt="Current: {value}",
            clamp=False,
        )
        self._finalize_setting_change(ok, success_message=f"[GUI] Flank range set to {FLANK_RANGE}")

    def on_start_bot(self):
        self._session_exp_active = True
        self._session_exp_started_at = time.time()
        self._session_exp_total = 0
        self._session_exp_last_value = None
        self._stop_in_progress = False
        try:
            self.session_exp_label.config(text="0")
            self.session_exp_hour_label.config(text="0")
        except Exception:
            pass
        start_bot()
        self._set_bot_ui_state(True)
        _log_info("[GUI] Bot started")

    def on_stop_bot(self):
        if self._stop_in_progress:
            return
        self._stop_in_progress = True
        self.stop_bot_button.config(state=tk.DISABLED)

        def _apply_stopped_ui():
            try:
                self._set_bot_ui_state(False)
            except Exception:
                pass
            self._stop_in_progress = False
            _log_info("[GUI] Bot stopped")

        def _stop_in_bg():
            self._session_exp_active = False
            try:
                stop_bot()
            except Exception as e:
                _log_warn(f"[GUI] Stop error: {e}")
            if not self._run_on_ui_thread(_apply_stopped_ui):
                self._stop_in_progress = False
        threading.Thread(target=_stop_in_bg, daemon=True).start()

    def on_rerecord_click_points(self):
        try:
            def record_in_bg():
                try:
                    record_direction_points()
                except Exception as e:
                    _log_warn(f"[GUI] Error recording click points: {e}")
            
            threading.Thread(target=record_in_bg, daemon=True).start()
            _log_info("[GUI] Click point recording started...")
        except Exception as e:
            _log_warn(f"[GUI] Error: {e}")

    def on_last_moved_timer_change(self, event):
        self._apply_capped_seconds_setting(
            tk_var=self.last_moved_timer_var,
            global_name=CFG_LAST_MOVED_TIMER_SECONDS,
            status_label=self.last_moved_timer_status,
            label_name="Last moved timer",
        )

    def on_sit_timer_change(self, event):
        self._apply_capped_seconds_setting(
            tk_var=self.sit_timer_var,
            global_name=CFG_SIT_TIMER_SECONDS,
            status_label=self.sit_timer_status,
            label_name="Sit timer",
        )

    def _change_npc_target(self, tk_var, *, add: bool):
        npc_id = tk_var.get().strip()
        if not npc_id:
            return
        try:
            npc_id_int = int(npc_id)
        except ValueError:
            _log_warn(f"[GUI] Invalid NPC ID format: {npc_id}")
            return
        finally:
            tk_var.set("")

        in_targets = npc_id_int in MOB_ID_FILTERS
        if add and not in_targets:
            MOB_ID_FILTERS.add(npc_id_int)
            action = "Added"
        elif (not add) and in_targets:
            MOB_ID_FILTERS.remove(npc_id_int)
            action = "Removed"
        else:
            _log_info(
                f"[GUI] NPC ID {npc_id_int} "
                + ("is already in the target list." if add else "not found in the target list.")
            )
            return

        _sync_config_state()
        self._update_targets_display()
        _log_info(f"[GUI] {action} NPC ID {npc_id_int} {'to' if add else 'from'} targets.")
        save_settings()

    def add_npc_target(self, event=None):
        self._change_npc_target(self.add_npc_var, add=True)

    def remove_npc_target(self, event=None):
        self._change_npc_target(self.remove_npc_var, add=False)

    def on_closing(self):
        if self._close_in_progress:
            return
        self._close_in_progress = True
        self._ui_running = False
        self._walkable_recording = False

        try:
            self.root.protocol("WM_DELETE_WINDOW", lambda: None)
        except Exception:
            pass
        try:
            self.root.withdraw()
        except Exception:
            pass

        try:
            stop_bot(detach_hooks=False)
        except Exception:
            pass
        try:
            save_settings()
        except Exception:
            pass

        def _detach_in_bg():
            try:
                _detach_tracked_frida_hooks()
            except Exception:
                pass
        threading.Thread(target=_detach_in_bg, daemon=True).start()

        try:
            self.root.after(0, self.root.destroy)
        except Exception:
            try:
                self.root.destroy()
            except Exception:
                pass

    def _apply_home_position(self, new_x: int, new_y: int, log_message: str):
        _set_config_value(CFG_HOME_POS, (new_x, new_y))
        self.home_x_var.set(str(new_x))
        self.home_y_var.set(str(new_y))
        self.home_status.config(text=f"Current: ({HOME_POS[0]}, {HOME_POS[1]})", foreground="green")
        _log_info(log_message.format(pos=HOME_POS))
        save_settings()

    def on_home_change(self, event=None):
        try:
            self._apply_home_position(
                int(self.home_x_var.get().strip()),
                int(self.home_y_var.get().strip()),
                "[GUI] Home location set to {pos}",
            )
        except ValueError:
            self.home_x_var.set(str(HOME_POS[0]))
            self.home_y_var.set(str(HOME_POS[1]))
            self.home_status.config(text=f"Invalid input. Current: ({HOME_POS[0]}, {HOME_POS[1]})", foreground="red")
            _log_warn("[GUI] Invalid home location; must be integers.")

    def set_home_from_current(self):
        try:
            data = self.player_data_manager.get_data()
            self._apply_home_position(
                int(data.get("x", HOME_POS[0])),
                int(data.get("y", HOME_POS[1])),
                "[GUI] Home location set from current position: {pos}",
            )
        except Exception as e:
            self.home_status.config(text=f"Failed to set from current pos. Current: ({HOME_POS[0]}, {HOME_POS[1]})", foreground="red")
            _log_warn(f"[GUI] Failed to set home from current pos: {e}")

def check_player_data(x_address, y_address):
    import time
    global directional_address, self_player_address, self_player_name, self_player_last_seen_ts, RECENT_REMOVALS

    FUNC = "check_player_data"

    def _log(msg):
        _log_info(f"[{FUNC}][{time.strftime('%H:%M:%S')}] {msg}")

    def _ids_look_valid(uid: int, suid: int) -> bool:
        return not (uid in (0, -1, 0xFFFF) or suid in (0, -1, 0xFFFF))

    def _instant_not_in_live_remove(addr_hex: str, now: float, reason: str = "not in live"):
        RECENT_REMOVALS[addr_hex] = (reason, now)

        try:
            if addr_hex == current_target_npc:
                last_k = RECENTLY_KILLED.get(addr_hex, 0.0)
                if (time.monotonic() - last_k) >= KILL_QUARANTINE_SEC and not _in_immunity(addr_hex):
                    _fire_kill_once(addr_hex, reason=reason.upper())
        except Exception:
            pass

        try:
            manager.remove_address(addr_hex)
        except Exception as e:
            _log(f"REMOVE_ERR({reason}): {addr_hex} | {e}")

    def _build_live_info():
        live_info = {}
        with manager._lock:
            addr_snapshot = [
                (addr_hex, meta.get("paired_address"))
                for addr_hex, meta in manager.addresses.items()
            ]
        for addr_hex, paired_hex in addr_snapshot:
            try:
                ax = int(addr_hex, 16)
                if not paired_hex:
                    continue
                ay = int(paired_hex, 16)

                x = pm.read_short(ax)
                y = pm.read_short(ay)
                uid  = pm.read_short(ax - MOB_ID_OFFSET)
                suid = pm.read_short(ax - SPAWN_UID_OFFSET)

                if not _ids_look_valid(uid, suid):
                    continue
                if _coords_oob(x, y):
                    continue

                live_info[addr_hex] = (x, y, uid, suid)
            except Exception:
                continue
        return live_info

    global pm
    initialize_pymem()

    try:
        while True:
            try:
                dir_addr = int(directional_address, 16) if isinstance(directional_address, str) else directional_address
                px = pm.read_short(x_address)
                py = pm.read_short(y_address)

                raw_dir = 0
                try:
                    raw_dir = pm.read_bytes(dir_addr, 1)[0]
                except Exception:
                    raw_dir = 0

                direction = _normalize_direction(raw_dir)

                player_data_manager.update(px, py, direction)

                live_info = _build_live_info()
                live_addrs = set(live_info.keys())

                next_frame = [{
                    "type": "player",
                    "X": px,
                    "Y": py,
                    "direction": direction,
                }]

                now = time.time()

                for addr_hex in sorted(live_addrs):
                    with manager._lock:
                        meta = manager.addresses.get(addr_hex)
                    if meta is None:
                        continue

                    x, y, uid, suid = live_info[addr_hex]

                    should_remove = False
                    remove_reason = ""
                    with manager._lock:
                        meta_live = manager.addresses.get(addr_hex)
                        if meta_live is None:
                            continue
                        last_uid = meta_live.get("last_unique_id")
                        last_suid = meta_live.get("last_spawn_uid")

                        if last_uid is None and last_suid is None:
                            meta_live["last_unique_id"] = uid
                            meta_live["last_spawn_uid"] = suid
                        elif uid != last_uid or suid != last_suid:
                            should_remove = True
                            remove_reason = f"| suid {last_suid}"
                        else:
                            meta_live["last_unique_id"] = uid
                            meta_live["last_spawn_uid"] = suid

                        pc = meta_live.get("protected_cleared_at")
                        snap_suid = meta_live.get("suid_at_protect")
                        if (not should_remove) and pc and (snap_suid is not None) and (suid != snap_suid):
                            should_remove = True
                            remove_reason = "protect_suid_shift"

                        meta_live.setdefault("first_seen_ts", now)
                        prev_got_hit = meta_live.get("got_hit")

                    if should_remove:
                        _instant_not_in_live_remove(addr_hex, now, reason=remove_reason)
                        continue

                    use_x, use_y = x, y

                    try:
                        got_hit = pm.read_int(int(addr_hex, 16) + 0x1D0)  # same offset as 5.3
                    except Exception:
                        got_hit = prev_got_hit  # keep prior if unreadable

                    should_mark_protect = False
                    with manager._lock:
                        meta_live = manager.addresses.get(addr_hex)
                        if meta_live is None:
                            continue

                        meta_live["got_hit"] = got_hit

                        if (
                            isinstance(got_hit, int) and isinstance(prev_got_hit, int) and got_hit > prev_got_hit
                            and not manager.ignore_protection
                        ):
                            me_recent = recently_attacking(addr_hex, window=0.40)  # a hair longer than 0.30
                            should_mark_protect = not me_recent

                        lx, ly = meta_live.get("last_x"), meta_live.get("last_y")
                        if (lx != use_x) or (ly != use_y):
                            meta_live["last_x"] = use_x
                            meta_live["last_y"] = use_y
                            meta_live["last_moved"] = now
                        else:
                            meta_live.setdefault("last_moved", now)

                        paired_address = meta_live["paired_address"]
                        speech_text = meta_live.get("last_speech")
                        speech_ts = meta_live.get("last_speech_ts")
                        npc_name = meta_live.get("name")

                    if should_mark_protect:
                        manager.mark_protected(
                            addr_hex,
                            seconds=3,
                            reason="got_hit",
                            meta={"delta": got_hit - prev_got_hit, "uid_at_protect": uid, "suid_at_protect": suid},
                        )
                        with manager._lock:
                            meta_live = manager.addresses.get(addr_hex)
                            if meta_live is not None:
                                meta_live["uid_at_protect"] = uid
                                meta_live["suid_at_protect"] = suid

                    next_frame.append({
                        "type": "npc",
                        "X": use_x,
                        "Y": use_y,
                        "unique_id": uid,
                        "spawn_uid": suid,
                        "address_x": addr_hex,
                        "address_y": paired_address,
                        "speech": speech_text,
                        "speech_ts": speech_ts,
                        "name": npc_name,
                    })
                others_snapshot = _get_other_players_snapshot()

                for addr_hex, meta2 in others_snapshot:
                    meta_updates: Dict[str, Any] = {}
                    paired_address = meta2.get("paired_address")
                    display_name = meta2.get("name")
                    display_level = meta2.get("level")
                    display_facing = meta2.get("facing")

                    def _flush_meta_updates():
                        if meta_updates:
                            _update_other_player_meta(addr_hex, meta_updates)

                    try:
                        ax = int(addr_hex, 16)
                        if not paired_address:
                            continue
                        ay = int(paired_address, 16)
                        ox = pm.read_short(ax)
                        oy = pm.read_short(ay)
                    except Exception:
                        continue

                    if now >= float(meta2.get("meta_refresh_due", 0.0)):
                        fresh = _read_other_player_meta(addr_hex)
                        if fresh.get("name"):
                            display_name = fresh["name"]
                            meta_updates["name"] = display_name
                        if fresh.get("level") is not None:
                            display_level = fresh["level"]
                            meta_updates["level"] = display_level
                        if fresh.get("facing") is not None:
                            display_facing = fresh["facing"]
                            meta_updates["facing"] = display_facing
                        meta_updates["meta_refresh_due"] = now + 1.5

                    if _coords_oob(ox, oy):
                        _flush_meta_updates()
                        continue

                    name_key = _player_name_key(display_name)
                    self_name_key = _player_name_key(self_player_name)

                    if self_name_key and name_key and name_key == self_name_key and ox == px and oy == py:
                        if addr_hex == self_player_address:
                            self_player_last_seen_ts = now
                        else:
                            can_switch = (
                                self_player_address is None
                                or (now - float(self_player_last_seen_ts)) > 1.5
                            )
                            if can_switch:
                                old_self = self_player_address
                                self_player_address = addr_hex
                                self_player_last_seen_ts = now
                                if old_self and old_self != addr_hex:
                                    _pop_other_player(old_self)
                                    position_match_count.pop(old_self, None)
                        _flush_meta_updates()
                        continue

                    if not self_name_key and ox == px and oy == py:
                        position_match_count[addr_hex] = position_match_count.get(addr_hex, 0) + 1

                        if position_match_count[addr_hex] >= 5:
                            if self_player_address != addr_hex:
                                self_player_address = addr_hex
                                self_player_last_seen_ts = now
                                if name_key:
                                    self_player_name = (display_name or "").strip() or self_player_name
                            _flush_meta_updates()
                            continue
                    else:
                        position_match_count[addr_hex] = 0

                    if self_player_address and addr_hex == self_player_address:
                        _flush_meta_updates()
                        continue

                    if max(abs(ox - px), abs(oy - py)) > 9:
                        _flush_meta_updates()
                        continue

                    meta_updates["last_x"] = ox
                    meta_updates["last_y"] = oy
                    meta_updates["last_seen"] = now
                    _update_other_player_meta(addr_hex, meta_updates)

                    next_frame.append({
                        "type": "other_player",
                        "X": ox,
                        "Y": oy,
                        "address_x": addr_hex,
                        "address_y": paired_address,
                        "name": display_name,
                        "level": display_level,
                        "facing": display_facing,
                    })

                _publish_map_frame(next_frame)

            except Exception as e:
                _warn_throttled("check_player_data:tick", f"[{FUNC}] tick error: {e}", interval_s=2.0)

            time.sleep(0.1)

    except Exception as e:
        _log_error(f"[{FUNC}] failed to initialize: {e}")

def on_message_npc(message, data):
    if message['type'] == 'send':
        payload = message['payload']
        action = payload.get('action')
        address = payload.get('address')
        if action == 'add' and address is not None:
            manager.add_address(address)

def start_frida_session_xy(walk_rva):
    if not isinstance(walk_rva, int):
        _log_warn("[XY] Invalid RVA type:", type(walk_rva))
        return

    session = frida_attach_target()

    script_code = f"""
    var mod = Process.getModuleByName("Endless.exe");
    var base = mod.base;
    var target = base.add(ptr({walk_rva}));

    Interceptor.attach(target, {{
        onEnter: function (args) {{
            var ecx = this.context.ecx || this.context.rcx;
            if (!ecx) return;

            var xPtr = ecx.add(0x08);
            var yPtr = ecx.add(0x0C);

            send({{
                type: "xy_found",
                x: xPtr.toString(),
                y: yPtr.toString()
            }});
        }}
    }});
    """

    _load_frida_script(session, script_code, on_message_xy, label="xy-session")

    _log_info("XY hook installed.")

def start_frida(npc_address):
    _log_info("Npc Started")
    frida_script = f"""
Interceptor.attach(Module.findBaseAddress("Endless.exe").add({npc_address}), {{
    onEnter: function(args) {{
        var eax = this.context.eax.toInt32();
        var offset = {NPC_VAR_OFFSET};
        var address = eax + offset;
        var addressHex = '0x' + address.toString(16).toUpperCase();
        send({{action: 'add', address: addressHex}});
    }}
}});
"""
    session = frida_attach_target()

    _load_frida_script(session, frida_script, on_message_npc, label="npc-monitor")

def _clicking_enabled() -> bool:
    if not CLICKING_ENABLED:
        return False
    try:
        runtime_flags = _get_runtime_flags()
        return time.monotonic() >= float(runtime_flags["no_click_until"])
    except Exception:
        return True

def _ensure_clicks_event():
    """Return a shared clicks-in-progress event, creating it if missing."""
    global clicks_in_progress
    ev = clicks_in_progress
    if ev is None:
        clicks_in_progress = threading.Event()
        ev = clicks_in_progress
    return ev

def _set_clicks_busy(active: bool):
    ev = _ensure_clicks_event()
    if active:
        ev.set()
    else:
        ev.clear()

def _safe_pause_for_clicks(*, skip_pause: bool, settle_delay: float):
    if not skip_pause:
        try:
            _pause_movement(settle_delay=settle_delay)
        except Exception:
            try:
                movement_allowed.clear()
            except Exception:
                pass
    try:
        release_key('ctrl')
    except Exception:
        pass

def _safe_resume_after_clicks(*, skip_pause: bool):
    if skip_pause:
        return
    try:
        _resume_movement()
    except Exception:
        try:
            movement_allowed.set()
        except Exception:
            pass

def _activate_game_window(game_win, delay_s: float = 0.05):
    # Background-only mode: never force foreground activation.
    return

def _pick_directional_point(
    points,
    facing: int,
    *,
    require_full_set: bool = True,
    warn_if_missing: bool = True,
):
    """
    Returns one (x, y) point based on facing.
    Expected full set order: [Up, Right, Down, Left].
    """
    pts = list(points)[:4] if require_full_set else list(points)
    min_needed = 4 if require_full_set else 1
    if len(pts) < min_needed:
        if warn_if_missing:
            _log_info("[LOOT] Need 4 resurrect points (Up,Right,Down,Left).")
        return None
    try:
        slot = DIR_TO_SLOT.get(int(facing) % 4, 0)
    except Exception:
        slot = 0
    if slot < 0 or slot >= len(pts):
        slot = 0
    return pts[slot]

def _pick_point_from_direction(points, facing: int):
    return _pick_directional_point(points, facing, require_full_set=True, warn_if_missing=True)

def _do_clicks(game_win, points, tag="CLICK"):
    """
    Perform exactly 4 corpse/loot clicks in background.

    IMPORTANT:
    - If CLICKING_ENABLED is False, do NOTHING (no flags, no sleep, no prints).
    - Only gate other threads (clicks_in_progress) when we are actually clicking.
    """
    if not _clicking_enabled():
        return

    pts = list(points)[:4]
    if len(pts) < 4:
        _log_warn(f"[WARN] only {len(pts)} saved points - skipping {tag} clicks")
        return

    _set_clicks_busy(True)
    try:
        _safe_pause_for_clicks(skip_pause=False, settle_delay=0.01)

        total = len(pts)  # should be 4
        for idx, pt in enumerate(pts, start=1):
            cxy = _resolve_client_point(pt)
            if not cxy:
                continue
            cx, cy = cxy
            _log_debug(f"[{tag}] clicking point {idx}/{total} at client=({cx},{cy})")
            try:
                for i in range(3):
                    click_client_point(cx, cy)
                    if i < 2:
                        time.sleep(0.10)
            except Exception as e:
                _warn_throttled(f"{tag}:click_fail:{idx}", f"[{tag}] click {idx} failed: {e}", interval_s=2.0)
            time.sleep(0.20)

        time.sleep(0.08)

    finally:
        _safe_resume_after_clicks(skip_pause=False)
        _set_clicks_busy(False)

def _do_directional_loot(game_win, points, facing, hold_seconds=4.75, tag="D-LOOT", log_context: Optional[dict] = None, skip_pause: bool = False):
    """
    If CLICKING_ENABLED is False: return immediately (no flags, no sleeps, no prints).

    If CLICKING_ENABLED is True:
      - When FAST_CLICK is True: perform a fast 3x burst on the directional point and return.
      - Otherwise: hold-click the point for `hold_seconds` like before.
    """
    if not _clicking_enabled():
        return

    target = _pick_point_from_direction(points, facing)
    if not target:
        return
    cxy = _resolve_client_point(target)
    if not cxy:
        return
    cx, cy = cxy

    _set_clicks_busy(True)
    try:
        _safe_pause_for_clicks(skip_pause=skip_pause, settle_delay=0.02)
        if FAST_CLICK:
            _log_debug(f"[{tag}] FAST_CLICK enabled: burst {FAST_CLICK_BURST_COUNT} at client=({cx},{cy})")
            for _ in range(int(FAST_CLICK_BURST_COUNT)):
                try:
                    click_client_point(cx, cy)
                except Exception as e:
                    _warn_throttled(f"{tag}:burst_err", f"[{tag}] burst click err: {e}", interval_s=2.0)
                time.sleep(float(FAST_CLICK_GAP_S))
            time.sleep(0.03)
            return
        t0 = time.monotonic()
        _log_debug(f"[{tag}] directional loot hold started @ client=({cx},{cy})")
        while (time.monotonic() - t0) < float(hold_seconds):
            try:
                click_client_point(cx, cy)
            except Exception as e:
                _warn_throttled(f"{tag}:hold_err", f"[{tag}] click err: {e}", interval_s=2.0)
            time.sleep(0.08)

        time.sleep(0.03)

    finally:
        _safe_resume_after_clicks(skip_pause=skip_pause)
        _set_clicks_busy(False)

def _do_fast_click_burst(game_win, pts, facing, burst, gap, tag="KILL"):
    """
    Clicks the directional loot point 'burst' times with 'gap' seconds between clicks.
    Uses clicks_in_progress to gate other routines similar to the hold-click logic.
    """
    _set_clicks_busy(True)

    try:
        target = _pick_directional_point(
            pts,
            facing,
            require_full_set=False,
            warn_if_missing=False,
        )
        if not target:
            return

        cxy = _resolve_client_point(target)
        if not cxy:
            return
        cx, cy = cxy

        for _ in range(int(burst)):
            try:
                click_client_point(cx, cy)
            except Exception:
                pass
            time.sleep(float(gap))

    finally:
        _set_clicks_busy(False)

def load_walkable_tiles(file_path: Optional[str] = None):
    """
    Loads walkable tiles from JSON, robust across platforms and launch methods.
    - Accepts optional file_path (absolute or relative).
    - If relative, or not given, we resolve via _resolve_walkable_path.
    - Falls back to a 101x101 grid if not found or invalid.
    """
    path: Path | None
    if file_path:
        p = Path(os.path.expandvars(os.path.expanduser(file_path)))
        path = p if p.is_absolute() else (APP_BASE_DIR / p)
        path = path.resolve()
    else:
        path = _resolve_walkable_path(WALKABLE_ARG)

    try:
        if path is None:
            raise FileNotFoundError("walkable.json not found by resolver")

        with path.open("r", encoding="utf-8") as f:
            data = json.load(f)

        tiles = data.get("safe_tiles") or []
        if tiles:
            out = {(int(t["X"]), int(t["Y"])) for t in tiles}
            _set_walkable_source_state("file", path=path)
            return out

        _log_info(f"[WALKABLE] No tiles in {path}; using default grid.")
        _set_walkable_source_state(
            "default_grid",
            message="WARNING: using default grid. Please enable auto load or select JSON from Walkable Maps tab.",
            path=path,
        )
    except Exception as e:
        msg = f"{e.__class__.__name__}: {e}"
        _log_warn(f"[WALKABLE] Error loading tiles ({msg}). Using default grid.")
        _set_walkable_source_state(
            "default_grid",
            message="WARNING: using default grid. Please enable auto load or select JSON from Walkable Maps tab.",
            path=path,
        )

    return {
        (x, y)
        for x in range(1, INVALID_COORD_LIMIT + 1)
        for y in range(1, INVALID_COORD_LIMIT + 1)
    }

def _invalidate_walkable_cache():
    global _WALKABLE_CACHE_TILES, _WALKABLE_CACHE_PATH, _WALKABLE_CACHE_MTIME
    with _WALKABLE_CACHE_LOCK:
        _WALKABLE_CACHE_TILES = None
        _WALKABLE_CACHE_PATH = None
        _WALKABLE_CACHE_MTIME = None

def get_walkable_tiles_cached() -> Set[Tuple[int, int]]:
    """
    Cached walkable-tile loader keyed by resolved path + file mtime.
    Returns a copy for callers that mutate the set.
    """
    global _WALKABLE_CACHE_TILES, _WALKABLE_CACHE_PATH, _WALKABLE_CACHE_MTIME

    path = _resolve_walkable_path(WALKABLE_ARG)
    mtime: Optional[float] = None
    if path is not None:
        try:
            mtime = float(path.stat().st_mtime)
        except Exception:
            mtime = None

    with _WALKABLE_CACHE_LOCK:
        if (
            _WALKABLE_CACHE_TILES is not None
            and _WALKABLE_CACHE_PATH == path
            and _WALKABLE_CACHE_MTIME == mtime
        ):
            return set(_WALKABLE_CACHE_TILES)

    tiles = load_walkable_tiles(str(path) if path is not None else None)
    tiles = set(tiles or set())

    with _WALKABLE_CACHE_LOCK:
        _WALKABLE_CACHE_TILES = set(tiles)
        _WALKABLE_CACHE_PATH = path
        _WALKABLE_CACHE_MTIME = mtime

    return set(tiles)

def _coords_oob(xv: int, yv: int) -> bool:
    """Simple global check: invalid map coordinates."""
    return (
        xv is None or yv is None or
        xv <= 0 or yv <= 0 or
        xv > INVALID_COORD_LIMIT or yv > INVALID_COORD_LIMIT
    )

def get_nearby_players(px: int, py: int, radius: int = 9, include_self: bool = False):
    """
    Snapshot of valid other players within <radius> tiles of (px, py).
    Uses last_x/last_y from the Frida-fed tracking table.
    """
    results: List[Dict[str, Any]] = []
    snapshot = _get_other_players_snapshot()

    for addr_hex, meta in snapshot:
        meta_name = meta.get("name")
        if not include_self and addr_hex == self_player_address:
            continue
        ox = meta.get("last_x")
        oy = meta.get("last_y")
        if ox is None or oy is None:
            continue
        if _coords_oob(ox, oy):
            continue
        if (
            not include_self
            and _player_name_key(self_player_name)
            and _player_name_key(meta_name) == _player_name_key(self_player_name)
            and int(ox) == int(px) and int(oy) == int(py)
        ):
            continue
        if max(abs(ox - px), abs(oy - py)) > radius:
            continue

        results.append({
            "type": "other_player",
            "X": int(ox),
            "Y": int(oy),
            "last_x": int(ox),
            "last_y": int(oy),
            "address_x": addr_hex,
            "address_y": meta.get("paired_address"),
            "name": meta_name,
            "level": meta.get("level"),
            "facing": meta.get("facing"),
        })

    return results

def heuristic(a, b):
    return abs(a[0] - b[0]) + abs(a[1] - b[1])

def astar_pathfinding(
    start: Optional[Tuple[int, int]],
    goal: Optional[Tuple[int, int]],
    walkable_tiles: Set[Tuple[int, int]],
    blocked_tiles: Optional[Set[Tuple[int, int]]] = None,
):
    """A* over cardinal movement with optional temporary blockers."""
    if start is None or goal is None:
        return None
    if _coords_oob(start[0], start[1]) or _coords_oob(goal[0], goal[1]):
        return None

    walkable: Set[Tuple[int, int]] = set(walkable_tiles or set())
    if start not in walkable:
        walkable.add(start)
    if goal not in walkable:
        return None
    if start == goal:
        return [start]

    dynamic_blocked: Set[Tuple[int, int]] = set(blocked_tiles or set())
    if AVOID_OTHER_PLAYERS:
        dynamic_blocked.update(_other_player_tiles_near(start[0], start[1], radius=15))
    dynamic_blocked.discard(start)
    dynamic_blocked.discard(goal)

    def _run_astar(blocked_now: Set[Tuple[int, int]]):
        import heapq
        open_heap: List[Tuple[int, int, Tuple[int, int]]] = []
        heapq.heappush(open_heap, (heuristic(start, goal), 0, start))

        came_from: Dict[Tuple[int, int], Tuple[int, int]] = {}
        g_score: Dict[Tuple[int, int], int] = {start: 0}
        closed: Set[Tuple[int, int]] = set()

        while open_heap:
            _, cur_g, current = heapq.heappop(open_heap)
            if current in closed:
                continue
            closed.add(current)

            if current == goal:
                path = [current]
                while current in came_from:
                    current = came_from[current]
                    path.append(current)
                path.reverse()
                return path

            for dx, dy in ((0, 1), (1, 0), (0, -1), (-1, 0)):
                neighbor = (current[0] + dx, current[1] + dy)
                if neighbor not in walkable or neighbor in blocked_now:
                    continue

                tentative_g = cur_g + 1
                if tentative_g >= g_score.get(neighbor, 10**9):
                    continue

                came_from[neighbor] = current
                g_score[neighbor] = tentative_g
                heapq.heappush(open_heap, (tentative_g + heuristic(neighbor, goal), tentative_g, neighbor))

        return None

    path = _run_astar(dynamic_blocked)
    if path:
        return path
    if dynamic_blocked:
        return _run_astar(set())
    return None

def find_closest_npc(player_x, player_y, npcs):
    closest_npc = None
    min_distance = float('inf')
    for npc in npcs:
        distance = abs(player_x - npc['X']) + abs(player_y - npc['Y'])
        if distance < min_distance:
            min_distance = distance
            closest_npc = npc
    return closest_npc

def key_listener():
    kb = None
    warned_missing = False
    warned_runtime = False
    while True:
        runtime_flags = _get_runtime_flags()
        if not runtime_flags["bot_running"]:
            time.sleep(0.1)
            continue

        if kb is None:
            try:
                import keyboard as kb_mod
                kb = kb_mod
            except Exception as e:
                if not warned_missing:
                    _log_info(f"[HOTKEY] keyboard module unavailable ({e}). Pause hotkey disabled.")
                    warned_missing = True
                time.sleep(1.0)
                continue

        try:
            if kb.is_pressed(','):
                _log_info("Pausing for 1 minute...")
                time.sleep(60)
                _log_info("Resuming combat...")
        except Exception as e:
            if not warned_runtime:
                _log_warn(f"[HOTKEY] keyboard runtime error ({e}). Pause hotkey disabled.")
                warned_runtime = True
            kb = None
        time.sleep(0.1)

last_combat_time = time.time()
sitting = False

def _click_buff_thread():
    """
    Background loop:
      - While bot_running and CLICK_BUFFS_ENABLED:
          every CLICK_BUFF_INTERVAL_S seconds
          press F6 and click on `player_click_point`.

    IMPORTANT:
      - Skips entirely while the home/heal routine is running
        or HP_HOME_ACTIVE is True (HP-based home).
    """
    import time
    global player_click_point
    _log_info("[BUFF] Click buff thread started")
    buff_busy = threading.Lock()

    def _fire_self_buff_once(pt):
        """Fire timed self-buff without pausing movement/combat threads."""
        if not buff_busy.acquire(blocking=False):
            return
        try:
            cxy = _resolve_client_point(pt)
            if not cxy:
                return
            cx, cy = cxy
            key = HOTKEY_BINDINGS.get("buff_self", "f6")

            press_key(key, presses=1, delay=0.0, interval=0.0)
            click_client_point(cx, cy)
        except Exception as e:
            _warn_throttled("click_buff:fire_error", f"[BUFF] ERROR firing timed self-buff: {e}", interval_s=2.0)
        finally:
            buff_busy.release()

    while True:
        runtime_flags = _get_runtime_flags()
        if (not runtime_flags["bot_running"] or not CLICK_BUFFS_ENABLED):
            time.sleep(0.5)
            continue

        try:
            if runtime_flags["home_running"] or HP_HOME_ACTIVE:
                time.sleep(0.5)
                continue
        except NameError:
            pass

        interval = float(CLICK_BUFF_INTERVAL_S)
        waited = 0.0
        step = 0.2
        should_skip = False
        while waited < interval:
            runtime_flags = _get_runtime_flags()
            if (not runtime_flags["bot_running"]
                    or not CLICK_BUFFS_ENABLED
                    or runtime_flags["home_running"]
                    or HP_HOME_ACTIVE):
                should_skip = True
                break
            time.sleep(step)
            waited += step
        
        if not should_skip:
            pt = player_click_point
            if not pt:
                continue

            try:
                ev = clicks_in_progress
                if ev is not None and ev.is_set():
                    continue
            except Exception:
                pass

            _fire_self_buff_once(pt)

def _hp_buff_thread():
    import time
    healing = False
    next_allowed_press = 0.0

    while True:
        runtime_flags = _get_runtime_flags()
        if not runtime_flags["bot_running"]:
            healing = False
            next_allowed_press = 0.0
            time.sleep(0.2)
            continue

        try:
            if not HP_BUFFS_ENABLED:
                if healing:
                    healing = False
                    try:
                        _resume_movement()
                    except Exception:
                        movement_allowed.set()
                next_allowed_press = 0.0
                time.sleep(0.2)
                continue

            cur_hp = read_current_hp()
            max_hp = read_stat("max_hp")
            if cur_hp is None or max_hp is None or max_hp <= 0:
                time.sleep(0.2)
                continue

            hp_pct = (cur_hp / max_hp) * 100.0
            low = float(HP_BUFF_THRESHOLD_PCT)
            target = float(HP_BUFF_TARGET_PCT)
            cooldown = max(0.25, float(HP_BUFF_COOLDOWN_S))

            if not healing and hp_pct < low:
                healing = True
                next_allowed_press = 0.0
                _log_info(f"[HP BUFF] ENTER healing: {hp_pct:.1f}%")
                try:
                    _pause_movement(tag="HPBUFF")
                except Exception:
                    movement_allowed.clear()

            if healing and hp_pct >= target:
                healing = False
                next_allowed_press = 0.0
                _log_info(f"[HP BUFF] EXIT healing: {hp_pct:.1f}%")
                try:
                    _resume_movement()
                except Exception:
                    movement_allowed.set()
                time.sleep(0.2)
                continue

            if healing:
                now = time.time()
                if now < next_allowed_press:
                    wait_s = min(0.2, max(0.05, next_allowed_press - now))
                    time.sleep(wait_s)
                    continue

                key = HOTKEY_BINDINGS.get("hp_buff", "f3")
                _log_debug(f"[HP BUFF] {hp_pct:.1f}% -> pressing {key.upper()} (single tap)")
                if press_key(key, presses=1, delay=0.0, interval=0.0):
                    next_allowed_press = time.time() + cooldown
                    # Allow HP/memory to update before the next evaluation.
                    settle = min(0.35, max(0.10, cooldown * 0.35))
                    time.sleep(settle)
                else:
                    next_allowed_press = now + max(0.5, cooldown)
                    time.sleep(0.2)
                continue

            time.sleep(0.15)

        except Exception as e:
            _warn_throttled("hp_buff:error", f"[HP BUFF] ERROR: {e}", interval_s=2.0)
            time.sleep(0.5)

def combat_thread():
    """
    EXP-less combat loop:
      - Picks the closest valid NPC (filtered by MOB_ID_FILTERS and walkable tiles).
      - If adjacent with clear LOS -> face + hold CTRL to attack.
      - Otherwise path toward an adjacent flank tile next to the NPC.
      - If target disappears, immediately yield so loot/home can run (no stepping first).
      - Smart wandering when no valid NPCs are present.
    """
    import time, random
    from collections import deque
    global last_combat_time, sitting, current_target_npc, movement_allowed, _wander_damage_abort, HP_HOME_ACTIVE
    global _target_immunity_until, IMMUNITY_SEC, speech_quarantine_until, last_attack_time, last_attack_addr

    try:
        _ = _target_immunity_until
    except NameError:
        _target_immunity_until = {}
    try:
        _ = IMMUNITY_SEC
    except NameError:
        IMMUNITY_SEC = 5.0

    base_walkable = set(load_walkable_tiles() or [])
    if not base_walkable:
        base_walkable = {
            (x, y)
            for x in range(1, INVALID_COORD_LIMIT + 1)
            for y in range(1, INVALID_COORD_LIMIT + 1)
        }
    
    wandering_target = None
    stuck_timer_start = None
    last_position = None
    ctrl_pressed = False
    ctrl_pressed_since = 0.0 
    CTRL_MISALIGN_TIMEOUT = 0.35
    blocked_tiles = {}         # (x, y) -> expiry_time
    movement_start_time = None
    target_tile = None
    _wander_since = None
    target_move_info = {}
    last_seen_map_version = -1
    _was_home_routine_running = False  # Track home routine state transition
    _just_returned_from_home = False  # Flag to ensure F8 is pressed once after home

    def _begin_attack(target_addr):
        """
        Start attacking: hold CTRL, tell manager to ignore protection,
        and stamp last_attack_* for 'my hit' detection elsewhere.
        """
        nonlocal ctrl_pressed, ctrl_pressed_since
        try:
            manager.set_ignore_protection(True)
        except Exception:
            pass
        hold_key('ctrl')
        ctrl_pressed = True
        ctrl_pressed_since = time.time()
        _set_attack_state(True, target_addr=target_addr, attack_time=ctrl_pressed_since)

    def _end_attack():
        """
        Stop attacking: release CTRL if needed and restore protection handling.
        Safe to call even if we aren't currently holding CTRL.
        """
        nonlocal ctrl_pressed, ctrl_pressed_since
        if ctrl_pressed:
            try:
                release_key('ctrl')
            except Exception:
                pass
            ctrl_pressed = False
            ctrl_pressed_since = 0.0
        _set_attack_state(False)
        try:
            manager.set_ignore_protection(False)
        except Exception:
            pass

    def _adjacent_and_facing(ply_x, ply_y, npc_x, npc_y, live_dir):
        want = _desired_facing(ply_x, ply_y, npc_x, npc_y)
        if want is None:
            return False  # same tile / ambiguous
        dx = abs(ply_x - npc_x)
        dy = abs(ply_y - npc_y)
        dist = max(dx, dy)
        on_line = (ply_x == npc_x) or (ply_y == npc_y)
        return (live_dir == want) and on_line and (dist == 1)
    
    def _move_one_step_continuous(move_dir, from_pos, to_pos):
        """Move one tile using continuous hold (matching go_to_target flow).
        Returns immediately once we detect movement, or after timeout.
        Returns True if we reached the target, False otherwise.
        """
        if not move_dir:
            return False
        
        hold_key(move_dir)
        deadline = time.monotonic() + 0.15  # Reduced to 150ms per tile - fast detection
        reached = False
        try:
            start_xy = _live_xy()
            while time.monotonic() < deadline:
                xy = _live_xy()
                if xy and xy == to_pos:
                    reached = True
                    break
                elif xy and xy != start_xy:
                    break
                time.sleep(STEP_POLL_S)
        finally:
            release_key(move_dir)
        return reached

    def _flank_candidates(npc_x, npc_y, radius):
        return [
            (npc_x - radius, npc_y), (npc_x + radius, npc_y),
            (npc_x, npc_y - radius), (npc_x, npc_y + radius),
        ]

    def _has_los(ax, ay, bx, by, walkable):
        los = list(bresenham.bresenham(ax, ay, bx, by))
        return all((x, y) in walkable for x, y in los)

    def _best_flank_path(ply_xy, npc_xy, radius, preferred_tiles, path_tiles, prefer_farther=False):
        candidates = _flank_candidates(npc_xy[0], npc_xy[1], radius)
        if prefer_farther:
            nx, ny = npc_xy
            candidates.sort(key=lambda p: -max(abs(p[0] - nx), abs(p[1] - ny)))
        primary = [pos for pos in candidates if pos in preferred_tiles]
        fallback = [pos for pos in candidates if pos in path_tiles]
        return _shortest_path_to_any(ply_xy, primary, path_tiles) or _shortest_path_to_any(ply_xy, fallback, path_tiles)

    def _best_los_vantage_path(
        ply_xy: Tuple[int, int],
        npc_xy: Tuple[int, int],
        engage_range: int,
        los_tiles: Set[Tuple[int, int]],
        preferred_tiles: Set[Tuple[int, int]],
        path_tiles: Set[Tuple[int, int]],
    ):
        """
        Find a shortest path to any tile that can attack this NPC:
        - same row/column as NPC
        - within engage range
        - line of sight through map-walkable tiles
        """
        nx, ny = int(npc_xy[0]), int(npc_xy[1])
        rng = max(1, int(engage_range))
        candidates: List[Tuple[int, int]] = []

        for d in range(1, rng + 1):
            candidates.extend([
                (nx - d, ny),
                (nx + d, ny),
                (nx, ny - d),
                (nx, ny + d),
            ])

        filtered = []
        for pos in candidates:
            if pos not in path_tiles:
                continue
            if _has_los(pos[0], pos[1], nx, ny, los_tiles):
                filtered.append(pos)

        if not filtered:
            return None

        primary = [pos for pos in filtered if pos in preferred_tiles]
        return _shortest_path_to_any(ply_xy, primary, path_tiles) or _shortest_path_to_any(ply_xy, filtered, path_tiles)

    def _apply_path_step(best, now_ts, from_xy):
        nonlocal movement_start_time, target_tile
        global current_path_tiles, path_fade_timestamp

        if not best or not best[0] or len(best[0]) < 2:
            movement_start_time = None
            return False

        best_path, _ = best
        step_xy = best_path[1]

        if step_xy != target_tile:
            movement_start_time = now_ts
            target_tile = step_xy
            try:
                current_path_tiles = best_path[1:]
                path_fade_timestamp = None
            except Exception:
                pass

        move_dir = _direction_key(from_xy, step_xy)
        if move_dir:
            _move_one_step_continuous(move_dir, from_xy, step_xy)

        if movement_start_time and (now_ts - movement_start_time) > 2.0:
            live_player = map_data_indexer.get_player() or {"X": from_xy[0], "Y": from_xy[1]}
            if (live_player.get("X"), live_player.get("Y")) != step_xy:
                blocked_tiles[step_xy] = now_ts + 3.0
            movement_start_time = None

        return bool(move_dir)

    def _clear_motion_intent(reset_wander: bool = False):
        nonlocal movement_start_time, target_tile, wandering_target
        movement_start_time = None
        target_tile = None
        if reset_wander:
            wandering_target = None

    def _end_attack_wait(delay: float = 0.02):
        _end_attack()
        if delay > 0:
            time.sleep(delay)

    def _step_if_found(best, now_ts, from_xy):
        if best:
            _apply_path_step(best, now_ts, from_xy)
            return True
        return False

    def _step_retreat_path(ply_xy, npc_xy, engage_range, now_ts, extended_tiles, path_tiles):
        best = _best_flank_path(
            ply_xy,
            npc_xy,
            engage_range,
            extended_tiles,
            path_tiles,
            prefer_farther=True,
        )
        return _step_if_found(best, now_ts, ply_xy)

    def _step_los_blocked_path(ply_xy, npc_xy, engage_range, now_ts, los_tiles, extended_tiles, path_tiles):
        best = _best_los_vantage_path(
            ply_xy,
            npc_xy,
            engage_range,
            los_tiles,
            extended_tiles,
            path_tiles,
        )
        if not best:
            best = _best_flank_path(
                ply_xy,
                npc_xy,
                max(engage_range + 1, FLANK_RANGE + 1),
                extended_tiles,
                path_tiles,
            )
        return _step_if_found(best, now_ts, ply_xy)

    def _step_approach_path(ply_xy, npc_xy, engage_range, now_ts, los_tiles, extended_tiles, path_tiles):
        best = _best_flank_path(
            ply_xy,
            npc_xy,
            engage_range,
            extended_tiles,
            path_tiles,
        )
        if not best:
            best = _best_los_vantage_path(
                ply_xy,
                npc_xy,
                engage_range,
                los_tiles,
                extended_tiles,
                path_tiles,
            )
        return _step_if_found(best, now_ts, ply_xy)

    def _step_default_path(ply_xy, npc_xy, engage_range, now_ts, los_tiles, extended_tiles, path_tiles):
        best = _best_flank_path(
            ply_xy,
            npc_xy,
            FLANK_RANGE,
            extended_tiles,
            path_tiles,
        )
        if not best:
            best = _best_los_vantage_path(
                ply_xy,
                npc_xy,
                engage_range,
                los_tiles,
                extended_tiles,
                path_tiles,
        )
        return _step_if_found(best, now_ts, ply_xy)

    def _step_with_attack_end(step_fn, *step_args, delay: float = 0.0):
        _end_attack()
        step_fn(*step_args)
        if delay > 0:
            time.sleep(delay)

    def _select_target_obj(valid_npcs, player_x: int, player_y: int):
        """Choose/retain target and return its live NPC object if available."""
        global current_target_npc, path_fade_timestamp

        chosen = None
        if current_target_npc and RANGE_MODE.get(current_target_npc) == "retreating":
            chosen = next(
                (n for n in valid_npcs if n.get("address_x") == current_target_npc),
                None,
            )
        if not chosen:
            chosen = find_closest_npc(player_x, player_y, valid_npcs)

        new_target = chosen.get("address_x") if chosen else None
        if new_target != current_target_npc:
            if current_target_npc:
                RANGE_MODE.pop(current_target_npc, None)
            if new_target:
                _target_immunity_until[new_target] = time.monotonic() + IMMUNITY_SEC
                tap_key_async('f8', times=1)
            current_target_npc = new_target

        if not current_target_npc:
            return None

        return next((n for n in valid_npcs if n.get("address_x") == current_target_npc), None)

    def _live_direction(default: int = 0) -> int:
        try:
            return int(player_data_manager.get_data().get('direction', default))
        except Exception:
            return int(default)

    def _retarget_after_alignment_fail(message: str, delay: float = 0.02):
        """Release attack and force a retarget when alignment logic fails."""
        global current_target_npc
        _log_debug(message)
        _end_attack()
        _clear_motion_intent(reset_wander=True)
        current_target_npc = None
        time.sleep(delay)

    def _watchdog_realign(ply_x: int, ply_y: int, npc_x: int, npc_y: int, fallback_live_dir: int):
        """Quick release/face/reapply used by misaligned-CTRL watchdog."""
        target_dir_idx = _desired_facing(ply_x, ply_y, npc_x, npc_y)
        if target_dir_idx is not None:
            _face_in_game_best_effort(target_dir_idx)
            time.sleep(0.03)
            live_dir2 = _live_direction(fallback_live_dir)
            if _adjacent_and_facing(ply_x, ply_y, npc_x, npc_y, live_dir2):
                _begin_attack(current_target_npc)

    def _handle_vanished_target(npcs_snapshot) -> bool:
        """
        Drop target immediately when it disappears from live NPC list.
        Count as kill only if we were recently attacking this same target.
        """
        global current_target_npc
        if not current_target_npc:
            return False

        present_addrs = {n.get("address_x") for n in npcs_snapshot}
        if current_target_npc in present_addrs:
            return False

        vanished_addr = current_target_npc
        _end_attack()
        _clear_motion_intent()

        try:
            path_fade_timestamp = time.time()
        except Exception:
            pass

        if recently_attacking(vanished_addr):
            _fire_kill_once(vanished_addr, reason="VANISH")

        current_target_npc = None
        time.sleep(0.05)
        return True

    def _handle_stale_target(valid_npcs, now_ts: float, ply_x: int, ply_y: int, npc_x: int, npc_y: int) -> bool:
        """
        Track per-target movement and remove stale targets that haven't moved long enough.
        Returns True when stale-handled and caller should continue loop.
        """
        nonlocal _wander_since
        global current_target_npc

        info = target_move_info.get(current_target_npc)
        pos_now = (npc_x, npc_y)

        if info is None:
            target_move_info[current_target_npc] = {"pos": pos_now, "ts": now_ts}
            return False

        if info["pos"] != pos_now:
            info["pos"] = pos_now
            info["ts"] = now_ts

        if (now_ts - info["ts"]) < LAST_MOVED_TIMER_SECONDS:
            return False

        _log_info(f"[STALE] Target {current_target_npc} unmoved for {LAST_MOVED_TIMER_SECONDS}s - removing")
        _end_attack()

        try:
            if manager and current_target_npc:
                manager.remove_address(current_target_npc)
        except Exception as e:
            _warn_throttled("combat:stale_remove_err", f"[WARN] failed to remove stale target {current_target_npc}: {e}", interval_s=2.0)

        try:
            RECENT_REMOVALS[current_target_npc] = ("stale", time.monotonic())
        except Exception:
            pass

        _clear_motion_intent(reset_wander=True)
        current_target_npc = None

        if valid_npcs:
            valid_npcs.sort(key=lambda n: abs(ply_x - n['X']) + abs(ply_y - n['Y']))
            new_target = valid_npcs[0]
            current_target_npc = new_target.get('address_x')
            _log_debug(f"[TARGET] Switching to new target after stale: {current_target_npc}")
        else:
            _wander_since = time.monotonic()
            _clear_motion_intent(reset_wander=True)
            _log_debug("[TARGET] No valid targets after stale removal, wandering...")

        time.sleep(0.02)
        return True

    while True:
        runtime_flags = _get_runtime_flags()

        if not runtime_flags["bot_running"]:
            _end_attack_wait(0.1)
            continue
            
        if runtime_flags["clicks_in_progress"] or runtime_flags["home_running"]:
            _end_attack()
            _clear_motion_intent()
            _was_home_routine_running = True  # Mark that home was running
            time.sleep(0.02)
            continue
        
        if _was_home_routine_running and not runtime_flags["home_running"]:
            if not _just_returned_from_home:
                _just_returned_from_home = True
            _was_home_routine_running = False

        if not runtime_flags["movement_allowed"]:
            _end_attack()
            time.sleep(0.05)
            continue

        now = time.time()

        blocked_tiles = {tile: t for tile, t in blocked_tiles.items() if t > now}
        adjusted_walkable = base_walkable.difference(blocked_tiles.keys())
        los_walkable = base_walkable

        frame_version, frame_snapshot = _get_map_snapshot_if_changed(last_seen_map_version)

        if frame_snapshot is not None:
            if not frame_snapshot:
                _end_attack_wait(0.05)
                continue
            map_data_indexer.update(frame_snapshot)
            last_seen_map_version = frame_version

        player = map_data_indexer.get_player()
        if not player:
            _end_attack_wait(0.05)
            continue

        if AVOID_OTHER_PLAYERS:
            other_players = map_data_indexer.get_other_players()
            if other_players:
                player_tiles = {(int(p['X']), int(p['Y'])) for p in other_players if p.get('X') is not None and p.get('Y') is not None}
                player_tiles.discard((int(player['X']), int(player['Y'])))
                adjusted_walkable = adjusted_walkable.difference(player_tiles)

        all_npcs = map_data_indexer.get_npcs()
        npcs = [n for n in all_npcs if not MOB_ID_FILTERS or n.get("unique_id") in MOB_ID_FILTERS]

        quarantined = (time.time() < speech_quarantine_until)

        if quarantined:
            valid_npcs = []
        else:
            valid_npcs = [npc for npc in npcs if (npc['X'], npc['Y']) in adjusted_walkable]

            if IGNORE_PROTECTION:
                valid_npcs = [npc for npc in valid_npcs if npc.get('address_x')]
            else:
                filtered = []
                for npc in valid_npcs:
                    addr = npc.get('address_x')
                    if not addr:
                        continue
                    if manager.is_protected(addr) and not (
                        addr == current_target_npc and (is_attacking() or recently_attacking(addr))
                    ):
                        continue
                    filtered.append(npc)
                valid_npcs = filtered

        if valid_npcs and _just_returned_from_home:
            _just_returned_from_home = False

        if ctrl_pressed and not current_target_npc:
            _end_attack()

        if target_tile and _distance_tiles((player['X'], player['Y']), target_tile) <= 0.5:
            _clear_motion_intent()
            try:
                current_path_tiles = []
                path_fade_timestamp = time.time()
            except Exception:
                pass

        if _handle_vanished_target(npcs):
            continue

        if not valid_npcs:
            current_target_npc = None  # clear any stale choice

            _end_attack()

            if _wander_damage_abort:
                _wander_damage_abort = False
                _wander_since = time.monotonic()
                _log_info("[COMBAT] Damage detected during sit - entering wander mode for timeout duration")

            if _wander_since is None:
                _wander_since = time.monotonic()
            elif (time.monotonic() - _wander_since) >= WANDER_TIMEOUT_S:
                if RUN_HOME_AFTER_KILL and _start_home_routine_if_idle(delay_s=0.25):
                    _wander_since = None
                    continue  # skip doing a wander step this tick

        try:
            if HP_HOME_ENABLED and not home_routine_running.is_set():
                at_home_with_nearby = False

                try:
                    px, py = _get_xy_safe()
                    if px is not None and py is not None:
                        px, py = int(px), int(py)
                        if _distance_tiles((px, py), HOME_POS) <= HOME_NEAR_THRESH:
                            try:
                                if _has_nearby_target():
                                    at_home_with_nearby = True
                            except NameError:
                                pass
                except Exception:
                    pass

                if at_home_with_nearby:
                    pass
                else:
                    max_hp = read_stat('max_hp')
                    cur_hp = read_current_hp()
                    if max_hp and max_hp > 0 and cur_hp is not None:
                        hp_pct = (cur_hp / max_hp) * 100.0
                        low_thresh = float(HP_HOME_LOW_PCT)
                        if hp_pct <= low_thresh:
                            HP_HOME_ACTIVE = True       # <- mark strict HP-home
                            _start_home_routine_if_idle(delay_s=0.25)
                            continue

        except Exception as e:
            _warn_throttled("combat:hp_home", f"[COMBAT] HP-home gate error: {e}", interval_s=3.0)

        if not valid_npcs:
            if quarantined:
                danger = {(n['X'], n['Y']) for n in npcs}
                danger |= {(x+1, y) for (x, y) in danger}
                danger |= {(x-1, y) for (x, y) in danger}
                danger |= {(x, y+1) for (x, y) in danger}
                danger |= {(x, y-1) for (x, y) in danger}
                tiles_for_wander = adjusted_walkable.difference(danger) or adjusted_walkable
            else:
                tiles_for_wander = adjusted_walkable

            cur_pos = (player['X'], player['Y'])
            if last_position and cur_pos == last_position:
                if not stuck_timer_start:
                    stuck_timer_start = now
                elif now - stuck_timer_start > 0.5:
                    wandering_target = random.choice(list(tiles_for_wander))
                    stuck_timer_start = None
            else:
                stuck_timer_start = None
                last_position = cur_pos

            if not wandering_target or cur_pos == wandering_target:
                wandering_target = random.choice(list(tiles_for_wander))

            path_to_wander = astar_pathfinding(cur_pos, wandering_target, adjusted_walkable)
            if path_to_wander and len(path_to_wander) > 1:
                step_x, step_y = path_to_wander[1]
                move_dir = _direction_key(cur_pos, (step_x, step_y))

                if move_dir:
                    _move_one_step_continuous(move_dir, cur_pos, (step_x, step_y))

            continue  # end wander tick

        if not sitting:
            _wander_since = None
            npc_positions = {(n['X'], n['Y']) for n in valid_npcs}
            extended_walkable = adjusted_walkable.difference(npc_positions)

            target_obj = _select_target_obj(valid_npcs, int(player['X']), int(player['Y']))

            if not current_target_npc:
                _end_attack_wait(0.02)
                continue

            if not target_obj:
                _end_attack_wait(0.02)
                continue

            npc_x, npc_y = target_obj['X'], target_obj['Y']
            ply_x, ply_y = player['X'], player['Y']

            if ctrl_pressed:
                live_dir = _live_direction(0)
                if not _adjacent_and_facing(ply_x, ply_y, npc_x, npc_y, live_dir):
                    if (time.time() - ctrl_pressed_since) > CTRL_MISALIGN_TIMEOUT:
                        _warn_throttled("combat:watchdog", "[watchdog] misaligned while CTRL held -> release", interval_s=1.5)
                        _end_attack()
                        _watchdog_realign(ply_x, ply_y, npc_x, npc_y, live_dir)
                        _clear_motion_intent(reset_wander=True)
                        time.sleep(0.01)
                        continue

            if _handle_stale_target(valid_npcs, now, ply_x, ply_y, npc_x, npc_y):
                continue

            dx = abs(ply_x - npc_x)
            dy = abs(ply_y - npc_y)

            if ctrl_pressed and (now - ctrl_pressed_since) >= 0.8:
                target_dir_idx = _desired_facing(ply_x, ply_y, npc_x, npc_y)

                live_dir = _live_direction(0)

                if target_dir_idx is not None and live_dir != target_dir_idx:
                    _log_debug(f"[face] safety re-face: live {live_dir} -> want {target_dir_idx}")

                    _log_debug("[face] releasing ctrl")
                    _end_attack()
                    time.sleep(0.03)  # debounce so release registers

                    desired = target_dir_idx
                    dir_key = ['down', 'left', 'up', 'right'][desired]

                    turned = False
                    for attempt in range(1, 3):
                        _log_debug(f"[face] tap {dir_key} (attempt {attempt}/2)")
                        press_key(dir_key, 1, 0.05)

                        t0 = time.time()
                        while time.time() - t0 < 0.30:
                            new_dir = _live_direction(live_dir)
                            if new_dir == desired:
                                _log_debug(f"[face] turned OK -> {new_dir}")
                                turned = True
                                break
                            time.sleep(0.02)
                        if turned:
                            break

                    live = _live_direction(live_dir)
                    ply_x, ply_y = player['X'], player['Y']
                    npc_x, npc_y = target_obj['X'], target_obj['Y']

                    if _adjacent_and_facing(ply_x, ply_y, npc_x, npc_y, live):
                        _begin_attack(current_target_npc)

                        t0 = time.time()
                        ok = False
                        while time.time() - t0 < 0.16:           # ~100-160ms sanity window
                            d = _live_direction(live)
                            ply_x, ply_y = player['X'], player['Y']
                            npc_x, npc_y = target_obj['X'], target_obj['Y']
                            if _adjacent_and_facing(ply_x, ply_y, npc_x, npc_y, d):
                                ok = True
                                break
                            time.sleep(0.02)

                        if not ok:
                            _retarget_after_alignment_fail("[face] post-hold failed (target moved) -> release + retarget")
                            continue
                    else:
                        _retarget_after_alignment_fail("[face] not aligned/adjacent -> NO hold; retarget")
                        continue

            ENGAGE_RANGE = FLANK_RANGE
            RETREAT_TRIGGER = 0 if ENGAGE_RANGE == 1 else 1

            on_line = (ply_y == npc_y) or (ply_x == npc_x)
            dist = max(dx, dy)
            los_ok = _has_los(ply_x, ply_y, npc_x, npc_y, los_walkable)

            state = RANGE_MODE.get(current_target_npc)
            if state == "retreating" and dist >= ENGAGE_RANGE:
                RANGE_MODE.pop(current_target_npc, None)
                state = None

            if on_line and los_ok and (dist <= RETREAT_TRIGGER or (state == "retreating" and dist < ENGAGE_RANGE)):
                RANGE_MODE[current_target_npc] = "retreating"
                _step_with_attack_end(
                    _step_retreat_path,
                    (ply_x, ply_y), (npc_x, npc_y), ENGAGE_RANGE, now, extended_walkable, adjusted_walkable,
                )
                continue

            if RANGE_MODE.get(current_target_npc) != "retreating" and on_line and 1 <= dist <= ENGAGE_RANGE and los_ok:
                fresh_player = map_data_indexer.get_player()
                if fresh_player:
                    ply_x, ply_y = fresh_player['X'], fresh_player['Y']

                target_dir_idx = _desired_facing(ply_x, ply_y, npc_x, npc_y)

                if target_dir_idx is not None:
                    _face_in_game_best_effort(target_dir_idx)
                    time.sleep(0.05)
                    if not ctrl_pressed:
                        _begin_attack(current_target_npc)
                    last_combat_time = now
                time.sleep(0.02)
                continue

            if RANGE_MODE.get(current_target_npc) != "retreating" and on_line and 1 <= dist <= ENGAGE_RANGE and not los_ok:
                _step_with_attack_end(
                    _step_los_blocked_path,
                    (ply_x, ply_y), (npc_x, npc_y), ENGAGE_RANGE, now, los_walkable, extended_walkable, adjusted_walkable,
                    delay=0.02,
                )
                continue

            if dist > ENGAGE_RANGE:
                _step_with_attack_end(
                    _step_approach_path,
                    (ply_x, ply_y), (npc_x, npc_y), ENGAGE_RANGE, now, los_walkable, extended_walkable, adjusted_walkable,
                )
                continue

            _step_default_path((ply_x, ply_y), (npc_x, npc_y), ENGAGE_RANGE, now, los_walkable, extended_walkable, adjusted_walkable)
            continue

        _end_attack_wait(0.02)

def _ensure_supported_frida_version() -> None:
    version = str(getattr(frida, "__version__", "") or "").strip()
    if not version:
        return
    major = version.split(".", 1)[0]
    if major != "16":
        raise RuntimeError(
            f"Unsupported Frida version detected ({version}). Use frida==16.1.4."
        )

def main_full_bot():
    global BOT_GUI
    _set_bot_running(False)

    try:
        _ensure_supported_frida_version()
    except Exception as e:
        _log_error(f"[ERROR] {e}")
        return

    load_settings()

    if not resurrect_points or len(resurrect_points) != 4:
        record_direction_points()

    select_target_pid_preboot()
    patch_adds_with_nops()
    initialize_pymem()

    resolve_all_aobs()
    if not walkAddress or not npcAddress or not speechAddress:
        _log_error("[ERROR] AOB resolution failed.")
        return
    if not initialize_background_input(TARGET_PID):
        _log_error("[INPUT] Background backend unavailable; aborting startup (no legacy fallback).")
        return
    try:
        start_frida_exp()
        start_frida_session_xy(walkAddress)
        start_frida_session_directional(directionalAddress)
        start_frida_map_id()

        for target, args in ((start_frida, (npcAddress,)), (start_frida_other_players, ()), (start_frida_speech_monitor, ())):
            threading.Thread(target=target, args=args, daemon=True).start()

        timeout = time.time() + 10
        while (x_address is None or y_address is None or directional_address is None):
            if time.time() > timeout:
                _log_error("[ERROR] Pointer initialization timeout.")
                return
            time.sleep(0.1)

        runtime_threads = [
            (check_player_data, (x_address, y_address)),
            (start_frida_current_hp, ()),
            (start_frida_current_mana, ()),
            (combat_thread, ()),
            (_click_buff_thread, ()),
            (_hp_buff_thread, ()),
            (key_listener, ()),
        ]
        for target, args in runtime_threads:
            threading.Thread(target=target, args=args, daemon=True).start()

        BOT_GUI = PlayerDataPopup(player_data_manager)
        BOT_GUI.run()
    finally:
        shutdown_background_input()

def main():
    main_full_bot()

if __name__ == "__main__":
    main()


