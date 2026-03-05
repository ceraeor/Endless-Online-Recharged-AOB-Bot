'use strict';

// Frida script: Background Input for Endless Online
// Strategy:
// 1. Suppress "Lose Focus" messages (WM_KILLFOCUS, WM_ACTIVATE(inactive)).
// 2. Inject "Gain Focus" messages on startup.
// 3. Inject WM_CHAR for typing.
// 4. Spoof GetForegroundWindow/GetActiveWindow/GetFocus.

var user32 = Module.load('user32.dll');
var PeekMessageA = user32.findExportByName('PeekMessageA');
var PeekMessageW = user32.findExportByName('PeekMessageW');
var GetMessageA = user32.findExportByName('GetMessageA');
var GetMessageW = user32.findExportByName('GetMessageW');
var GetForegroundWindow = user32.findExportByName('GetForegroundWindow');
var GetActiveWindow = user32.findExportByName('GetActiveWindow');
var GetFocus = user32.findExportByName('GetFocus');
var FindWindowA = user32.findExportByName('FindWindowA');
var PostMessageA = user32.findExportByName('PostMessageA');
var MapVirtualKeyA = user32.findExportByName('MapVirtualKeyA');
var GetGUIThreadInfo = user32.findExportByName('GetGUIThreadInfo');
var EnumWindows = user32.findExportByName('EnumWindows');
var GetWindowThreadProcessId = user32.findExportByName('GetWindowThreadProcessId');
var kernel32 = Module.load('kernel32.dll');
var GetCurrentProcessId = kernel32.findExportByName('GetCurrentProcessId');

// NativeFunctions
var findWindow = new NativeFunction(FindWindowA, 'pointer', ['pointer', 'pointer']);
var postMessage = new NativeFunction(PostMessageA, 'int', ['pointer', 'uint', 'uint', 'uint']);
var mapVirtualKey = new NativeFunction(MapVirtualKeyA, 'uint', ['uint', 'uint']);
var enumWindows = new NativeFunction(EnumWindows, 'int', ['pointer', 'int']);
var getWindowThreadProcessId = new NativeFunction(GetWindowThreadProcessId, 'uint', ['pointer', 'pointer']);
var getCurrentProcessId = new NativeFunction(GetCurrentProcessId, 'uint', []);

// Constants
var WM_NULL = 0x0000;
var WM_ACTIVATE = 0x0006;
var WM_SETFOCUS = 0x0007;
var WM_KILLFOCUS = 0x0008;
var WM_ACTIVATEAPP = 0x001C;
var WM_NCACTIVATE = 0x0086;
var WM_KEYFIRST = 0x0100;
var WM_KEYDOWN = 0x0100;
var WM_KEYUP = 0x0101;
var WM_CHAR = 0x0102;
var WM_KEYLAST = 0x0109;
var WM_MOUSEMOVE = 0x0200;
var WM_LBUTTONDOWN = 0x0201;
var WM_LBUTTONUP = 0x0202;
var WM_RBUTTONDOWN = 0x0204;
var WM_RBUTTONUP = 0x0205;

var WA_INACTIVE = 0;
var WA_ACTIVE = 1;
var WA_CLICKACTIVE = 2;

// Game HWND (lazy loaded)
var gameHwnd = ptr(0);
var isSpoofing = true;
var lastHeartbeat = Date.now();
var HEARTBEAT_TIMEOUT = 5000; // 5 seconds timeout

// Store all attach listeners for proper cleanup
var GetForegroundWindow_listener = null;
var GetActiveWindow_listener = null;
var GetFocus_listener = null;
var GetGUIThreadInfo_listener = null;
var GetKeyState_listener = null;
var GetAsyncKeyState_listener = null;
var GetKeyboardState_listener = null;
var DefWindowProcA_listener = null;
var IsIconic_listener = null;
var IsWindowVisible_listener = null;
var GetCursorPos_listener = null;
var Sleep_listener = null;

// Store timer IDs for cleanup
var keepAliveTimerId = null;
var watchdogTimerId = null;

// Store message hook listeners
var PeekMessageA_listener = null;
var PeekMessageW_listener = null;
var GetMessageA_listener = null;
var GetMessageW_listener = null;

function getGameHwnd() {
    if (gameHwnd.isNull()) {
        var myPid = getCurrentProcessId();
        var foundHwnd = ptr(0);
        
        var callback = new NativeCallback(function(hwnd, lParam) {
            var pidPtr = Memory.alloc(4);
            getWindowThreadProcessId(hwnd, pidPtr);
            var pid = pidPtr.readU32();
            
            if (pid === myPid) {
                foundHwnd = hwnd;
                return 0;
            }
            return 1; // Continue
        }, 'int', ['pointer', 'int'], 'stdcall');
        
        enumWindows(callback, 0);
        
        if (!foundHwnd.isNull()) {
            gameHwnd = foundHwnd;
            send({ type: 'info', message: 'Found Game HWND via PID (' + myPid + '): ' + gameHwnd });
        } else {
            // Fallback to FindWindow if Enum failed (unlikely)
            var title = Memory.allocUtf8String("Endless Online");
            gameHwnd = findWindow(ptr(0), title);
            if (!gameHwnd.isNull()) {
                send({ type: 'info', message: 'Found Game HWND via FindWindow (Fallback): ' + gameHwnd });
            }
        }
    }
    return gameHwnd;
}

// --- Module Listing ---
function listInputModules() {
    Process.enumerateModules({
        onMatch: function(module) {
            var name = module.name.toLowerCase();
            if (name.indexOf('dinput') !== -1 || name.indexOf('xinput') !== -1) {
                send({ type: 'info', message: 'Found Input Module: ' + module.name + ' at ' + module.base });
            }
        },
        onComplete: function() {}
    });
}
setTimeout(listInputModules, 1000);

var SetWindowLongA = user32.findExportByName('SetWindowLongA');
var CallWindowProcA = user32.findExportByName('CallWindowProcA');
var GWL_WNDPROC = -4;

var originalWndProc = null;
var wndProcCallback = null;

function setupWndProcHook() {
    var hwnd = getGameHwnd();
    if (hwnd.isNull()) {
        // Retry later if window not found yet
        setTimeout(setupWndProcHook, 1000);
        return;
    }

    if (originalWndProc !== null) return;

    if (SetWindowLongA && CallWindowProcA) {
        var setWindowLong = new NativeFunction(SetWindowLongA, 'int', ['pointer', 'int', 'pointer']);
        var callWindowProc = new NativeFunction(CallWindowProcA, 'pointer', ['pointer', 'pointer', 'uint', 'uint', 'uint']);

        wndProcCallback = new NativeCallback(function(hwnd, msg, wParam, lParam) {
            try {
                if (originalWndProc === null || originalWndProc.isNull()) {
                    return 0;
                }

                if (isSpoofing) {
                    if (msg === WM_KILLFOCUS) {
                        send({ type: 'info', message: 'WndProc: Blocking WM_KILLFOCUS' });
                        return ptr(0);
                    }
                    
                    if (msg === WM_ACTIVATE) {
                        var low = wParam & 0xFFFF;
                        if (low === WA_INACTIVE) {
                            send({ type: 'info', message: 'WndProc: Forcing WM_ACTIVATE(INACTIVE) -> ACTIVE' });
                            wParam = WA_ACTIVE;
                        }
                    }

                    if (msg === WM_ACTIVATEAPP) {
                        if (wParam === 0) {
                            send({ type: 'info', message: 'WndProc: Forcing WM_ACTIVATEAPP(FALSE) -> TRUE' });
                            wParam = 1;
                        }
                    }

                    if (msg === WM_NCACTIVATE) {
                        if (wParam === 0) {
                            send({ type: 'info', message: 'WndProc: Forcing WM_NCACTIVATE(FALSE) -> TRUE' });
                            wParam = 1;
                        }
                    }
                }

                return callWindowProc(originalWndProc, hwnd, msg, wParam, lParam);
            } catch (e) {
                return 0;
            }
        }, 'pointer', ['pointer', 'uint', 'uint', 'uint']);

        var oldProc = setWindowLong(hwnd, GWL_WNDPROC, wndProcCallback);
        if (oldProc !== 0) {
            originalWndProc = ptr(oldProc);
            send({ type: 'info', message: 'WndProc hooked successfully! Original: ' + originalWndProc });
        } else {
            send({ type: 'error', message: 'Failed to set GWL_WNDPROC' });
        }
    }
}

// Start the hook attempt (Removed setTimeout, now triggered by PeekMessage)
// setTimeout(setupWndProcHook, 2000);

// --- Message Queue ---
var messageQueue = []; 

function enqueueFocusRestore() {
    messageQueue.push({ msg: WM_NCACTIVATE, wParam: 1, lParam: 0 });
    messageQueue.push({ msg: 0x001C, wParam: 1, lParam: 0 });
    messageQueue.push({ msg: WM_ACTIVATE, wParam: WA_ACTIVE, lParam: 0 });
    messageQueue.push({ msg: WM_SETFOCUS, wParam: 0, lParam: 0 });
}

function enqueueChar(char) {
    var c = char.charCodeAt(0);
    messageQueue.push({ msg: WM_CHAR, wParam: c, lParam: 0x00000001 });
}

function enqueueKey(vk, down) {
    var scanCode = mapVirtualKey(vk, 0);
    var repeat = 1;
    var lParam = repeat | (scanCode << 16);
    
    if (vk >= 0x21 && vk <= 0x2E) {
        lParam |= (1 << 24);
    }
    
    if (!down) {
        lParam |= (1 << 30);
        lParam |= (1 << 31);
    }
    
    var msg = down ? WM_KEYDOWN : WM_KEYUP;
    messageQueue.push({ msg: msg, wParam: vk, lParam: lParam });
    setVirtualKeyState(vk, down);
}

var lastMouseX = -1;
var lastMouseY = -1;
var mouseState = 0; // Bitmap of MK_ flags

function enqueueMouse(msg, x, y) {
    if (msg === WM_LBUTTONDOWN) mouseState |= 0x0001;
    if (msg === WM_LBUTTONUP)   mouseState &= ~0x0001;
    if (msg === WM_RBUTTONDOWN) mouseState |= 0x0002;
    if (msg === WM_RBUTTONUP)   mouseState &= ~0x0002;

    var lParam = (y << 16) | (x & 0xFFFF);
    var wParam = mouseState;
    if (getVirtualKeyState(0x11)) wParam |= 0x0008;
    if (getVirtualKeyState(0x10)) wParam |= 0x0004;

    messageQueue.push({ msg: msg, wParam: wParam, lParam: lParam });
    lastMouseX = x;
    lastMouseY = y;

    if (msg === WM_LBUTTONDOWN) setVirtualKeyState(0x01, true);
    if (msg === WM_LBUTTONUP)   setVirtualKeyState(0x01, false);
    if (msg === WM_RBUTTONDOWN) setVirtualKeyState(0x02, true);
    if (msg === WM_RBUTTONUP)   setVirtualKeyState(0x02, false);
}

function processQueue() {
    var hwnd = getGameHwnd();
    if (!hwnd.isNull() && messageQueue.length > 0) {
        postMessage(hwnd, WM_NULL, 0, 0);
    }
}

function handleMessage(lpMsg, retval) {
    if (!isSpoofing) return;
    
    var retBool = retval.toInt32();
    var msgAddr = lpMsg.add(4);
    var wParamAddr = lpMsg.add(8);
    var msg = 0;
    var wParam = 0;

    if (retBool !== 0 && retBool !== -1) {
        msg = msgAddr.readU32();
        wParam = wParamAddr.readU32();

        if (msg === WM_KILLFOCUS) {
            msgAddr.writeU32(WM_NULL);
            return;
        }
        
        if (msg === WM_ACTIVATE) {
            var low = wParam & 0xFFFF;
            if (low === WA_INACTIVE) {
                wParamAddr.writeU32(WA_ACTIVE);
            }
        }

        if (msg === WM_NCACTIVATE && wParam === 0) {
            wParamAddr.writeU32(1);
        }

        if (msg === WM_ACTIVATEAPP && wParam === 0) {
            wParamAddr.writeU32(1);
        }
    }

    var canInject = (retBool === 0) || (retBool !== -1 && msg === WM_NULL);

    if (canInject && messageQueue.length > 0) {
        var nextMsg = messageQueue.shift();
        var hwnd = getGameHwnd();

        lpMsg.add(0).writePointer(hwnd);
        lpMsg.add(4).writeU32(nextMsg.msg);
        lpMsg.add(8).writeU32(nextMsg.wParam);
        lpMsg.add(12).writeU32(nextMsg.lParam >>> 0);
        lpMsg.add(16).writeU32(0);
        lpMsg.add(20).writeU32(0);
        lpMsg.add(24).writeU32(0);

        retval.replace(ptr(1));
        
        if (messageQueue.length > 0) {
            postMessage(hwnd, WM_NULL, 0, 0);
        }
    }
}

// --- Virtual Key State (for polling hooks) ---
var virtualKeyStates = {}; // vk -> bool

function setVirtualKeyState(vk, down) {
    virtualKeyStates[vk] = down;
}

function getVirtualKeyState(vk) {
    return virtualKeyStates[vk] || false;
}

// --- Hooks ---

// 0. Input Polling Hooks (GetKeyState / GetAsyncKeyState)
var GetKeyState = user32.findExportByName('GetKeyState');
var GetAsyncKeyState = user32.findExportByName('GetAsyncKeyState');

function spoofKeyState(args, retval) {
    var vk = args[0].toInt32() & 0xFF;
    if (getVirtualKeyState(vk)) {
        retval.replace(ptr(0x8001));
    }
}

if (GetKeyState) {
    GetKeyState_listener = Interceptor.attach(GetKeyState, {
        onEnter: function(args) { this.vk = args[0]; },
        onLeave: function(retval) { spoofKeyState([this.vk], retval); }
    });
}

if (GetAsyncKeyState) {
    GetAsyncKeyState_listener = Interceptor.attach(GetAsyncKeyState, {
        onEnter: function(args) { this.vk = args[0]; },
        onLeave: function(retval) { spoofKeyState([this.vk], retval); }
    });
}

var GetKeyboardState = user32.findExportByName('GetKeyboardState');
if (GetKeyboardState) {
    GetKeyboardState_listener = Interceptor.attach(GetKeyboardState, {
        onEnter: function(args) {
            this.lpKeyState = args[0];
        },
        onLeave: function(retval) {
            if (!isSpoofing) return;
            if (retval.toInt32() !== 0) {
                for (var vk in virtualKeyStates) {
                    if (virtualKeyStates[vk]) {
                        var vkInt = parseInt(vk);
                        this.lpKeyState.add(vkInt).writeU8(0x81);
                    }
                }
            }
        }
    });
}

// 1. Focus Spoofing
var isCheckingRealFocus = false;

function getRealForegroundWindow() {
    if (GetForegroundWindow) {
        isCheckingRealFocus = true;
        var fw = new NativeFunction(GetForegroundWindow, 'pointer', [])();
        isCheckingRealFocus = false;
        return fw;
    }
    return ptr(0);
}

function spoofFocus(retval) {
    if (!isSpoofing) return;
    if (isCheckingRealFocus) return;
    var hwnd = getGameHwnd();
    if (!hwnd.isNull()) {
        retval.replace(hwnd);
    }
}

if (GetForegroundWindow) GetForegroundWindow_listener = Interceptor.attach(GetForegroundWindow, { onLeave: spoofFocus });
if (GetActiveWindow) GetActiveWindow_listener = Interceptor.attach(GetActiveWindow, { onLeave: spoofFocus });
if (GetFocus) GetFocus_listener = Interceptor.attach(GetFocus, { onLeave: spoofFocus });

if (GetGUIThreadInfo) {
    GetGUIThreadInfo_listener = Interceptor.attach(GetGUIThreadInfo, {
        onEnter: function(args) {
            this.pGui = args[1];
        },
        onLeave: function(retval) {
            if (retval.toInt32() !== 0) {
                var hwnd = getGameHwnd();
                if (!hwnd.isNull()) {
                    this.pGui.add(8).writePointer(hwnd);
                    this.pGui.add(12).writePointer(hwnd);
                }
            }
        }
    });
}

// 2. Message Loop Hooks
var wndProcHooked = false;

function attachMessageHooks(funcPtr, isGetMessage) {
    if (!funcPtr) return null;
    return Interceptor.attach(funcPtr, {
        onEnter: function(args) {
            this.lpMsg = args[0];
            if (!isGetMessage) {
                this.removeMsg = args[4].toInt32();
            }
            
            // Try to hook WndProc from the main thread (where PeekMessage runs)
            if (!wndProcHooked && typeof setupWndProcHook === 'function') {
                setupWndProcHook();
                wndProcHooked = true;
            }
        },
        onLeave: function(retval) {
            var shouldProcess = isGetMessage ? (retval.toInt32() !== -1) : (this.removeMsg & 1);
            if (shouldProcess) {
                handleMessage(this.lpMsg, retval);
            }
        }
    });
}

if (PeekMessageA) PeekMessageA_listener = attachMessageHooks(PeekMessageA, false);
if (PeekMessageW) PeekMessageW_listener = attachMessageHooks(PeekMessageW, false);
if (GetMessageA) GetMessageA_listener = attachMessageHooks(GetMessageA, true);
if (GetMessageW) GetMessageW_listener = attachMessageHooks(GetMessageW, true);

// --- Keep Alive Loop ---
// Prevents GetMessage/WaitMessage from blocking indefinitely in background
// And constantly reminds the game it is active
function keepAlive() {
    var hwnd = getGameHwnd();
    if (!hwnd.isNull()) {
        postMessage(hwnd, WM_NULL, 0, 0);
        
        // Periodically force activation state (every ~1 second)
        // We don't want to spam this too hard or it might flood the queue
        if (Math.random() < 0.1) {
             postMessage(hwnd, WM_NCACTIVATE, 1, 0);
             postMessage(hwnd, WM_ACTIVATE, WA_ACTIVE, 0);
        }
    }
    if (isSpoofing) {
        keepAliveTimerId = setTimeout(keepAlive, 100);
    }
}
keepAliveTimerId = setTimeout(keepAlive, 2000);

var Sleep = kernel32.findExportByName('Sleep');
var SLEEP_CAP = 10;

if (Sleep) {
    Sleep_listener = Interceptor.attach(Sleep, {
        onEnter: function(args) {
            var duration = args[0].toInt32();
            if (duration > 30 && SLEEP_CAP > 0) { 
                args[0] = ptr(SLEEP_CAP);
            }
        }
    });
}

var DefWindowProcA = user32.findExportByName('DefWindowProcA');
if (DefWindowProcA) {
    DefWindowProcA_listener = Interceptor.attach(DefWindowProcA, {
        onEnter: function(args) {
            if (!isSpoofing) return;
            var msg = args[1].toInt32();
            if (msg === WM_KILLFOCUS) {
                args[1] = ptr(WM_NULL);
            }
        }
    });
}

var IsIconic = user32.findExportByName('IsIconic');
var IsWindowVisible = user32.findExportByName('IsWindowVisible');
var GetCursorPos = user32.findExportByName('GetCursorPos');
var ClientToScreen = user32.findExportByName('ClientToScreen');
var clientToScreen = new NativeFunction(ClientToScreen, 'int', ['pointer', 'pointer'], 'stdcall');

if (IsIconic) {
    IsIconic_listener = Interceptor.attach(IsIconic, {
        onLeave: function(retval) {
            if (!isSpoofing) return;
            retval.replace(ptr(0));
        }
    });
}

if (IsWindowVisible) {
    IsWindowVisible_listener = Interceptor.attach(IsWindowVisible, {
        onLeave: function(retval) {
            if (!isSpoofing) return;
            retval.replace(ptr(1));
        }
    });
}

if (GetCursorPos) {
    GetCursorPos_listener = Interceptor.attach(GetCursorPos, {
        onEnter: function(args) {
            this.lpPoint = args[0];
        },
        onLeave: function(retval) {
            if (!isSpoofing) return;
            var hwnd = getGameHwnd();
            if (!hwnd.isNull()) {
                if (lastMouseX !== -1 && lastMouseY !== -1) {
                    var pt = Memory.alloc(8);
                    pt.writeS32(lastMouseX);
                    pt.add(4).writeS32(lastMouseY);
                    
                    var res = clientToScreen(hwnd, pt);
                    
                    if (res !== 0) {
                        var screenX = pt.readS32();
                        var screenY = pt.add(4).readS32();
                        
                        this.lpPoint.writeS32(screenX);
                        this.lpPoint.add(4).writeS32(screenY);
                        
                        retval.replace(ptr(1));
                        return;
                    }
                }
                
                if (retval.toInt32() === 0) retval.replace(ptr(1));
            }
        }
    });
}

// --- DirectInput Hooks (Late Injection Support) ---
var dinput = Module.load("DINPUT.DLL");
var DirectInputCreateA_addr = dinput.findExportByName("DirectInputCreateA");

// Try to load dinput8.dll as well
var dinput8 = null;
try {
    dinput8 = Module.load("dinput8.dll");
} catch (e) {
    send({ type: 'info', message: 'dinput8.dll not found or load failed' });
}
var DirectInput8Create_addr = dinput8 ? dinput8.findExportByName("DirectInput8Create") : null;

var GetDeviceState_addr = null;
var GetDeviceData_addr = null;
var SetCooperativeLevel_addr = null;
var Acquire_addr = null;
var Unacquire_addr = null;
var fixedDevices = new Set();
var lastDevice = ptr(0);
var zeroBuffer = Memory.alloc(1024); // Pre-allocated zero buffer for clearing input
var isCleaningUp = false;

// Store attach listeners for proper cleanup
var Unacquire_listener = null;
var GetDeviceState_listener = null;
var GetDeviceData_listener = null;
var SetCooperativeLevel_listener = null;
var SetCooperativeLevel8_listener = null;

function hookUnacquire_Implementation(impl_ptr) {
    if (impl_ptr.isNull()) return;
    if (Unacquire_listener !== null) return; // Already hooked
    send({ type: 'info', message: 'Hooking Unacquire at ' + impl_ptr });
    
    // Use Interceptor.attach (NOT replace) so it can be properly detached during cleanup
    Unacquire_listener = Interceptor.attach(impl_ptr, {
        onEnter: function(args) {
            if (!isSpoofing || isCleaningUp) {
                // Allow unacquire during cleanup or when not spoofing
                return;
            }
            // Block unacquire while spoofing is active
            send({ type: 'info', message: 'Blocking Unacquire call (spoofing active)' });
            // Set return value to DI_OK and skip original function
            this.skip = true;
        },
        onLeave: function(retval) {
            if (this.skip) {
                retval.replace(ptr(0)); // DI_OK
            }
        }
    });
}

function hookGetDeviceState_Implementation(impl_ptr) {
    if (GetDeviceState_addr !== null && GetDeviceState_addr.equals(impl_ptr)) return;
    if (GetDeviceState_listener !== null) return; // Already hooked
    GetDeviceState_addr = impl_ptr;
    
    send({ type: 'info', message: 'Hooking GetDeviceState implementation at ' + impl_ptr });
    
    GetDeviceState_listener = Interceptor.attach(impl_ptr, {
        onEnter: function(args) {
            this.device = args[0];
            lastDevice = this.device;
            this.cbData = args[1].toInt32();
            this.lpData = args[2];
            
            // Fix Cooperative Level on the fly
            var deviceId = this.device.toString();
            if (!fixedDevices.has(deviceId) && SetCooperativeLevel_addr) {
                fixedDevices.add(deviceId); // Mark as fixed immediately to prevent spam
                send({ type: 'info', message: 'Checking Cooperative Level for device ' + deviceId });
                
                var hwnd = getGameHwnd();
                if (!hwnd.isNull() && Unacquire_addr && Acquire_addr) {
                     var Func_SetCooperativeLevel = new NativeFunction(SetCooperativeLevel_addr, 'int', ['pointer', 'pointer', 'uint'], 'stdcall');
                     var Func_Acquire = new NativeFunction(Acquire_addr, 'int', ['pointer'], 'stdcall');
                     var Func_Unacquire = new NativeFunction(Unacquire_addr, 'int', ['pointer'], 'stdcall');
                     
                     // Try to set background mode (DISCL_BACKGROUND | DISCL_NONEXCLUSIVE = 10)
                     var hr = Func_SetCooperativeLevel(this.device, hwnd, 10);
                     
                     if (hr !== 0) {
                         // If failed with E_INVALIDARG (0x80070057 = -2147024809), try NULL HWND
                         if (hr === -2147024809) {
                             send({ type: 'info', message: 'SetCooperativeLevel failed with E_INVALIDARG. Retrying with NULL HWND...' });
                             hr = Func_SetCooperativeLevel(this.device, ptr("0"), 10);
                             if (hr === 0) {
                                 send({ type: 'info', message: 'SetCooperativeLevel(NULL, BACKGROUND) success' });
                             }
                         }
                         
                         if (hr !== 0) {
                             send({ type: 'info', message: 'SetCooperativeLevel failed (' + hr + '). Attempting to Unacquire and retry...' });
                             
                             // Temporarily allow Unacquire by setting flag
                             var wasCleaningUp = isCleaningUp;
                             isCleaningUp = true;
                             
                             // Call Unacquire (hook will allow it since isCleaningUp is true)
                             Func_Unacquire(this.device);
                             
                             // Restore flag
                             isCleaningUp = wasCleaningUp;
                             
                             // Retry SetCooperativeLevel with HWND
                             hr = Func_SetCooperativeLevel(this.device, hwnd, 10);
                             
                             // If still failed, try NULL HWND
                             if (hr !== 0 && hr === -2147024809) {
                                 try {
                                     hr = Func_SetCooperativeLevel(this.device, ptr("0"), 10);
                                 } catch (e) {
                                     send({ type: 'error', message: 'SetCooperativeLevel(NULL) crashed: ' + e });
                                 }
                             }
                             
                             if (hr === 0) {
                                 send({ type: 'info', message: 'SetCooperativeLevel success after Unacquire!' });
                             } else {
                                 send({ type: 'error', message: 'SetCooperativeLevel failed even after Unacquire: ' + hr + ' (HWND: ' + hwnd + ')' });
                             }
                             
                             // Re-Acquire
                             Func_Acquire(this.device);
                             
                             // Re-apply the hook
                             hookUnacquire_Implementation(Unacquire_addr);
                         }
                     } else {
                         send({ type: 'info', message: 'SetCooperativeLevel(BACKGROUND) success' });
                         Func_Acquire(this.device);
                     }
                }
            }
        },
        onLeave: function(retval) {
            var hr = retval.toInt32();
            
            // If GetDeviceState failed (e.g. Not Acquired, Input Lost), we MUST fake success
            if (hr !== 0) {
                if (Acquire_addr) {
                    var Acquire = new NativeFunction(Acquire_addr, 'int', ['pointer'], 'stdcall');
                    Acquire(this.device);
                }
                if (this.cbData <= 1024) {
                    Memory.copy(this.lpData, zeroBuffer, this.cbData);
                }
                retval.replace(ptr(0));
            } else {
                // SUCCESS: Check if we should filter real input
                if (!isSpoofing) return; // Don't filter after cleanup
                // If we are in background (real foreground != game), zero out the buffer
                // to prevent "leaking" input from other windows.
                var realFg = getRealForegroundWindow();
                var gameHwnd = getGameHwnd();
                
                if (!realFg.isNull() && !gameHwnd.isNull() && !realFg.equals(gameHwnd)) {
                    // We are in background. Zero out the buffer.
                    if (this.cbData <= 1024) {
                        Memory.copy(this.lpData, zeroBuffer, this.cbData);
                    }
                }
            }

            // Always apply our keys (Only for Keyboard)
            if (this.cbData === 256) { // Keyboard buffer size
                for (var vk in virtualKeyStates) {
                    if (virtualKeyStates[vk]) {
                        var vkInt = parseInt(vk);
                        var scanCode = mapVirtualKey(vkInt, 0);
                        
                        // Fix for Extended Keys (Arrows)
                        if (vkInt === 0x25) scanCode = 0xCB; // Left
                        else if (vkInt === 0x26) scanCode = 0xC8; // Up
                        else if (vkInt === 0x27) scanCode = 0xCD; // Right
                        else if (vkInt === 0x28) scanCode = 0xD0; // Down
                        else if (vkInt === 0x11) scanCode = 0x1D; // L-Ctrl
                        else if (vkInt === 0x10) scanCode = 0x2A; // L-Shift
                        else if (vkInt === 0x12) scanCode = 0x38; // L-Alt
                        else if (vkInt === 0x0D) scanCode = 0x1C; // Enter
                        else if (vkInt === 0x1B) scanCode = 0x01; // Esc
                        else if (vkInt === 0x20) scanCode = 0x39; // Space
                        
                        if (scanCode !== 0 && scanCode < 256) {
                            this.lpData.add(scanCode).writeU8(0x80);
                        }
                    }
                }
            }
            
            // Mouse (16 or 20 bytes)
            if (this.cbData === 16 || this.cbData === 20) {
                 // Offset 12 is rgbButtons
                 // rgbButtons[0] = Left (VK_LBUTTON = 0x01)
                 // rgbButtons[1] = Right (VK_RBUTTON = 0x02)
                 
                 if (getVirtualKeyState(0x01)) {
                     this.lpData.add(12).writeU8(0x80);
                 }
                 if (getVirtualKeyState(0x02)) {
                     this.lpData.add(13).writeU8(0x80);
                 }
            }
        }
    });
}

function hookGetDeviceData_Implementation(impl_ptr) {
    if (GetDeviceData_addr !== null && GetDeviceData_addr.equals(impl_ptr)) return;
    if (GetDeviceData_listener !== null) return; // Already hooked
    GetDeviceData_addr = impl_ptr;
    send({ type: 'info', message: 'Hooking GetDeviceData implementation at ' + impl_ptr });
    
    GetDeviceData_listener = Interceptor.attach(impl_ptr, {
        onEnter: function(args) {
            this.device = args[0];
            this.cbObjectData = args[1].toInt32(); 
            this.rgdod = args[2]; 
            this.pdwInOut = args[3]; 
            this.dwFlags = args[4].toInt32();
        },
        onLeave: function(retval) {
            var hr = retval.toInt32();
            if (hr !== 0) {
                 if (Acquire_addr) {
                    var Acquire = new NativeFunction(Acquire_addr, 'int', ['pointer']);
                    Acquire(this.device);
                }
                retval.replace(ptr(0)); // Fake success
                if (!this.pdwInOut.isNull()) this.pdwInOut.writeU32(0); // Return 0 events
            }
        }
    });
}

function setupDirectInputHooks() {
    var mainModule = Process.enumerateModules()[0];
    var hInst = mainModule.base;
    
    // --- DirectInput 1-7 ---
    if (DirectInputCreateA_addr) {
        var DirectInputCreateA = new NativeFunction(DirectInputCreateA_addr, 'int', ['pointer', 'uint', 'pointer', 'pointer']);
        var ppDI = Memory.alloc(Process.pointerSize);
        var ppDevice = Memory.alloc(Process.pointerSize);
        
        var hr = DirectInputCreateA(hInst, 0x0300, ppDI, ptr(0));
        if (hr !== 0) hr = DirectInputCreateA(hInst, 0x0500, ppDI, ptr(0));
        
        if (hr === 0) {
            var pDI = ppDI.readPointer();
            var vtable = pDI.readPointer();
            var CreateDevice_addr = vtable.add(3 * Process.pointerSize).readPointer();
            var CreateDevice = new NativeFunction(CreateDevice_addr, 'int', ['pointer', 'pointer', 'pointer', 'pointer']);
            
            var GUID_SysKeyboard = Memory.alloc(16);
            GUID_SysKeyboard.writeU32(0x6F1D2B61);
            GUID_SysKeyboard.add(4).writeU16(0xD5A0);
            GUID_SysKeyboard.add(6).writeU16(0x11CF);
            GUID_SysKeyboard.add(8).writeByteArray([0xBF, 0xC7, 0x44, 0x45, 0x53, 0x54, 0x00, 0x00]);
            
            hr = CreateDevice(pDI, GUID_SysKeyboard, ppDevice, ptr(0));
            
            if (hr === 0) {
                var pDevice = ppDevice.readPointer();
                var devVtable = pDevice.readPointer();
                
                Acquire_addr = devVtable.add(7 * Process.pointerSize).readPointer();
                Unacquire_addr = devVtable.add(8 * Process.pointerSize).readPointer();
                SetCooperativeLevel_addr = devVtable.add(13 * Process.pointerSize).readPointer();
                
                hookUnacquire_Implementation(Unacquire_addr);
                
                SetCooperativeLevel_listener = Interceptor.attach(SetCooperativeLevel_addr, {
                    onEnter: function(args) {
                        if (isCleaningUp) return;
                        var flags = args[2].toInt32();
                        var newFlags = (flags & ~5) | 10;
                        if (newFlags !== flags) {
                            send({ type: 'info', message: 'Hooked SetCooperativeLevel: Forcing flags ' + flags + ' -> ' + newFlags });
                            args[2] = ptr(newFlags);
                        }
                    }
                });

                hookGetDeviceState_Implementation(devVtable.add(9 * Process.pointerSize).readPointer());
                hookGetDeviceData_Implementation(devVtable.add(10 * Process.pointerSize).readPointer());
            }
        }
    }

    // --- DirectInput 8 ---
    if (DirectInput8Create_addr) {
        send({ type: 'info', message: 'Found DirectInput8Create, attempting to hook DI8...' });
        var DirectInput8Create = new NativeFunction(DirectInput8Create_addr, 'int', ['pointer', 'uint', 'pointer', 'pointer', 'pointer']);
        var ppDI8 = Memory.alloc(Process.pointerSize);
        var ppDevice8 = Memory.alloc(Process.pointerSize);
        
        // IID_IDirectInput8A: {BF798030-483A-4DA2-AA99-5D64ED369700}
        var IID_IDirectInput8A = Memory.alloc(16);
        IID_IDirectInput8A.writeU32(0xBF798030);
        IID_IDirectInput8A.add(4).writeU16(0x483A);
        IID_IDirectInput8A.add(6).writeU16(0x4DA2);
        IID_IDirectInput8A.add(8).writeByteArray([0xAA, 0x99, 0x5D, 0x64, 0xED, 0x36, 0x97, 0x00]);

        var hr8 = DirectInput8Create(hInst, 0x0800, IID_IDirectInput8A, ppDI8, ptr(0));
        
        if (hr8 === 0) {
            var pDI8 = ppDI8.readPointer();
            var vtable8 = pDI8.readPointer();
            var CreateDevice8_addr = vtable8.add(3 * Process.pointerSize).readPointer();
            var CreateDevice8 = new NativeFunction(CreateDevice8_addr, 'int', ['pointer', 'pointer', 'pointer', 'pointer']);
            
            var GUID_SysKeyboard = Memory.alloc(16);
            GUID_SysKeyboard.writeU32(0x6F1D2B61);
            GUID_SysKeyboard.add(4).writeU16(0xD5A0);
            GUID_SysKeyboard.add(6).writeU16(0x11CF);
            GUID_SysKeyboard.add(8).writeByteArray([0xBF, 0xC7, 0x44, 0x45, 0x53, 0x54, 0x00, 0x00]);
            
            hr8 = CreateDevice8(pDI8, GUID_SysKeyboard, ppDevice8, ptr(0));
            
            if (hr8 === 0) {
                var pDevice8 = ppDevice8.readPointer();
                var devVtable8 = pDevice8.readPointer();
                
                // DI8 VTable offsets are generally the same for these methods
                Acquire_addr = devVtable8.add(7 * Process.pointerSize).readPointer();
                Unacquire_addr = devVtable8.add(8 * Process.pointerSize).readPointer();
                SetCooperativeLevel_addr = devVtable8.add(13 * Process.pointerSize).readPointer();
                
                hookUnacquire_Implementation(Unacquire_addr);
                
                SetCooperativeLevel8_listener = Interceptor.attach(SetCooperativeLevel_addr, {
                    onEnter: function(args) {
                        if (isCleaningUp) return;
                        var flags = args[2].toInt32();
                        var newFlags = (flags & ~5) | 10;
                        if (newFlags !== flags) {
                            send({ type: 'info', message: 'Hooked SetCooperativeLevel (DI8): Forcing flags ' + flags + ' -> ' + newFlags });
                            args[2] = ptr(newFlags);
                        }
                    }
                });

                hookGetDeviceState_Implementation(devVtable8.add(9 * Process.pointerSize).readPointer());
                hookGetDeviceData_Implementation(devVtable8.add(10 * Process.pointerSize).readPointer());
                
                send({ type: 'info', message: 'DirectInput8 hooks installed successfully' });
            } else {
                send({ type: 'error', message: 'Dummy CreateDevice8 failed: ' + hr8 });
            }
        } else {
             send({ type: 'error', message: 'Dummy DirectInput8Create failed: ' + hr8 });
        }
    }
}

// Run setup
setTimeout(setupDirectInputHooks, 500);

// --- Cleanup & Watchdog ---

function performCleanup() {
    if (isCleaningUp) {
        send({ type: 'warning', message: 'Cleanup already in progress, skipping duplicate call' });
        return;
    }
    isCleaningUp = true;
    send({ type: 'info', message: 'Cleanup requested. Disabling spoofing and releasing all resources...' });
    
    // STEP 0: Disable spoofing IMMEDIATELY to stop all hook behaviors
    isSpoofing = false;
    send({ type: 'info', message: 'isSpoofing set to FALSE - all hooks will now pass through' });
    
    // CRITICAL: Stop all timers that might still be running
    if (keepAliveTimerId !== null) {
        clearTimeout(keepAliveTimerId);
        keepAliveTimerId = null;
        send({ type: 'info', message: 'Stopped keepAlive timer' });
    }
    if (watchdogTimerId !== null) {
        clearInterval(watchdogTimerId);
        watchdogTimerId = null;
        send({ type: 'info', message: 'Stopped watchdog timer' });
    }
    
    var hwnd = getGameHwnd();

    // 0. Release ALL held keys before cleanup to prevent input leakage
    try {
        var keysToRelease = [];
        for (var vk in virtualKeyStates) {
            if (virtualKeyStates[vk] === true) {
                keysToRelease.push(parseInt(vk));
            }
        }
        
        if (keysToRelease.length > 0) {
            send({ type: 'info', message: 'Releasing ' + keysToRelease.length + ' held keys: ' + JSON.stringify(keysToRelease) });
            
            for (var i = 0; i < keysToRelease.length; i++) {
                var vk = keysToRelease[i];
                try {
                    // Send WM_KEYUP to release the key
                    postKeyEvent(vk, false);
                    virtualKeyStates[vk] = false;
                } catch (e) {
                    send({ type: 'error', message: 'Failed to release VK=' + vk + ': ' + e });
                }
            }
            
            send({ type: 'info', message: 'All keys released successfully' });
        } else {
            send({ type: 'info', message: 'No keys were held down' });
        }
        
        // CRITICAL: Clear virtualKeyStates to stop keyboard state spoofing
        virtualKeyStates = {};
        send({ type: 'info', message: 'Cleared virtualKeyStates to stop keyboard spoofing' });
    } catch (e) {
        send({ type: 'error', message: 'Error during key release: ' + e });
    }

    // 1. Restore WndProc FIRST to stop intercepting messages
    if (originalWndProc !== null && !hwnd.isNull() && SetWindowLongA) {
        try {
            var setWindowLong = new NativeFunction(SetWindowLongA, 'int', ['pointer', 'int', 'pointer']);
            var result = setWindowLong(hwnd, GWL_WNDPROC, originalWndProc);
            if (result !== 0) {
                send({ type: 'info', message: 'Restored original WndProc: ' + originalWndProc });
            } else {
                send({ type: 'error', message: 'SetWindowLong failed to restore WndProc' });
            }
            originalWndProc = null;
            
            // CRITICAL: Don't just set to null - explicitly delete the callback reference
            var tempCallback = wndProcCallback;
            wndProcCallback = null;
            
            // Force garbage collection hint
            send({ type: 'info', message: 'WndProc callback cleared and marked for cleanup' });
            
            // NOW send deactivation messages - WndProc is restored so they won't be blocked!
            if (PostMessageA) {
                var postMsg = new NativeFunction(PostMessageA, 'int', ['pointer', 'uint', 'uint', 'uint']);
                postMsg(hwnd, WM_KILLFOCUS, 0, 0);
                postMsg(hwnd, WM_NCACTIVATE, 0, 0);
                postMsg(hwnd, WM_ACTIVATEAPP, 0, 0);
                postMsg(hwnd, WM_ACTIVATE, WA_INACTIVE, 0);
                send({ type: 'info', message: 'Sent deactivation messages to reverse keepAlive effects' });
            }
        } catch (e) {
            send({ type: 'error', message: 'Error restoring WndProc: ' + e });
        }
    }
    
    // 1.1 Detach ALL Interceptor.attach() hooks to fully release input control
    var hooksToRevert = [
        { name: 'GetForegroundWindow', listener: GetForegroundWindow_listener },
        { name: 'GetActiveWindow', listener: GetActiveWindow_listener },
        { name: 'GetFocus', listener: GetFocus_listener },
        { name: 'GetGUIThreadInfo', listener: GetGUIThreadInfo_listener },
        { name: 'GetKeyState', listener: GetKeyState_listener },
        { name: 'GetAsyncKeyState', listener: GetAsyncKeyState_listener },
        { name: 'GetKeyboardState', listener: GetKeyboardState_listener },
        { name: 'DefWindowProcA', listener: DefWindowProcA_listener },
        { name: 'IsIconic', listener: IsIconic_listener },
        { name: 'IsWindowVisible', listener: IsWindowVisible_listener },
        { name: 'GetCursorPos', listener: GetCursorPos_listener },
        { name: 'Sleep', listener: Sleep_listener },
        { name: 'PeekMessageA', listener: PeekMessageA_listener },
        { name: 'PeekMessageW', listener: PeekMessageW_listener },
        { name: 'GetMessageA', listener: GetMessageA_listener },
        { name: 'GetMessageW', listener: GetMessageW_listener }
    ];
    
    for (var i = 0; i < hooksToRevert.length; i++) {
        var hook = hooksToRevert[i];
        if (hook.listener) {
            try {
                hook.listener.detach();
                send({ type: 'info', message: 'Detached ' + hook.name + ' hook' });
            } catch (e) {
                send({ type: 'error', message: 'Error detaching ' + hook.name + ': ' + e });
            }
        }
    }
    
    // Explicitly null out all listener references
    GetForegroundWindow_listener = null;
    GetActiveWindow_listener = null;
    GetFocus_listener = null;
    GetGUIThreadInfo_listener = null;
    GetKeyState_listener = null;
    GetAsyncKeyState_listener = null;
    GetKeyboardState_listener = null;
    DefWindowProcA_listener = null;
    IsIconic_listener = null;
    IsWindowVisible_listener = null;
    GetCursorPos_listener = null;
    Sleep_listener = null;
    PeekMessageA_listener = null;
    PeekMessageW_listener = null;
    GetMessageA_listener = null;
    GetMessageW_listener = null;
    send({ type: 'info', message: 'All listener references cleared' });
    
    // Revert DirectInput hooks if they exist
    if (GetDeviceState_listener) {
        try {
            GetDeviceState_listener.detach();
            GetDeviceState_listener = null;
            send({ type: 'info', message: 'Detached GetDeviceState hook' });
        } catch (e) {
            send({ type: 'error', message: 'Error detaching GetDeviceState: ' + e });
        }
    }
    
    if (GetDeviceData_listener) {
        try {
            GetDeviceData_listener.detach();
            GetDeviceData_listener = null;
            send({ type: 'info', message: 'Detached GetDeviceData hook' });
        } catch (e) {
            send({ type: 'error', message: 'Error detaching GetDeviceData: ' + e });
        }
    }
    
    if (SetCooperativeLevel_listener) {
        try {
            SetCooperativeLevel_listener.detach();
            SetCooperativeLevel_listener = null;
            send({ type: 'info', message: 'Detached SetCooperativeLevel hook' });
        } catch (e) {
            send({ type: 'error', message: 'Error detaching SetCooperativeLevel: ' + e });
        }
    }
    
    if (SetCooperativeLevel8_listener) {
        try {
            SetCooperativeLevel8_listener.detach();
            SetCooperativeLevel8_listener = null;
            send({ type: 'info', message: 'Detached SetCooperativeLevel8 hook' });
        } catch (e) {
            send({ type: 'error', message: 'Error detaching SetCooperativeLevel8: ' + e });
        }
    }
    
    if (Unacquire_listener) {
        try {
            Unacquire_listener.detach();
            Unacquire_listener = null;
            send({ type: 'info', message: 'Detached Unacquire hook' });
        } catch (e) {
            send({ type: 'error', message: 'Error detaching Unacquire: ' + e });
        }
    }
    
    send({ type: 'info', message: '=== ALL INTERCEPTOR HOOKS DETACHED ===' });
    
    // CRITICAL: Detach SetCooperativeLevel hooks BEFORE trying to restore foreground mode
    if (SetCooperativeLevel_listener) {
        try {
            SetCooperativeLevel_listener.detach();
            SetCooperativeLevel_listener = null;
            send({ type: 'info', message: 'Detached SetCooperativeLevel hook' });
        } catch (e) {
            send({ type: 'error', message: 'Error detaching SetCooperativeLevel: ' + e });
        }
    }
    
    if (SetCooperativeLevel8_listener) {
        try {
            SetCooperativeLevel8_listener.detach();
            SetCooperativeLevel8_listener = null;
            send({ type: 'info', message: 'Detached SetCooperativeLevel8 hook' });
        } catch (e) {
            send({ type: 'error', message: 'Error detaching SetCooperativeLevel8: ' + e });
        }
    }
    
    // 1.2 Clear message queue to remove any pending input messages
    try {
        if (!hwnd.isNull()) {
            var user32 = Process.getModuleByName('user32.dll');
            var PeekMessageA = user32.findExportByName('PeekMessageA');
            if (PeekMessageA) {
                var peekMessage = new NativeFunction(PeekMessageA, 'int', ['pointer', 'pointer', 'uint', 'uint', 'uint']);
                var MSG = Memory.alloc(48); // sizeof(MSG) structure
                var PM_REMOVE = 0x0001;
                
                // Clear all keyboard and char messages from queue
                var cleared = 0;
                while (peekMessage(MSG, hwnd, WM_KEYFIRST, WM_KEYLAST, PM_REMOVE) !== 0) {
                    cleared++;
                    if (cleared > 100) break; // Safety limit
                }
                if (cleared > 0) {
                    send({ type: 'info', message: 'Cleared ' + cleared + ' pending keyboard messages from queue' });
                }
            }
        }
    } catch (e) {
        send({ type: 'info', message: 'Error clearing message queue: ' + e });
    }
    
    // Note: WndProc was already restored earlier, no need to do it again here

    // 2. Restore DirectInput Cooperative Level BACK to FOREGROUND mode
    // During operation, we changed it to BACKGROUND - we must change it back!
    if (typeof lastDevice !== 'undefined' && !lastDevice.isNull() && SetCooperativeLevel_addr && Unacquire_addr) {
        var SetCooperativeLevel = new NativeFunction(SetCooperativeLevel_addr, 'int', ['pointer', 'pointer', 'uint'], 'stdcall');
        var Unacquire = new NativeFunction(Unacquire_addr, 'int', ['pointer'], 'stdcall');
        
        try {
            // CRITICAL: SetCooperativeLevel hooks are ALREADY DETACHED above
            // So this call will NOT be intercepted and forced back to BACKGROUND
            
            // Restore to FOREGROUND | NONEXCLUSIVE (flag 6)
            // This is the normal mode - only captures input when window has focus
            var hr = SetCooperativeLevel(lastDevice, hwnd.isNull() ? ptr(0) : hwnd, 6);
            send({ type: 'info', message: 'Restored DirectInput to FOREGROUND mode, result: ' + hr });
            
            // Give DirectInput time to process the mode change
            Thread.sleep(0.05);
            
            // Now unacquire to release control
            var unacquireResult = Unacquire(lastDevice);
            send({ type: 'info', message: 'Unacquired DirectInput device, result: ' + unacquireResult });
            
            // Give DirectInput time to fully release
            Thread.sleep(0.05);
            
            // Device is now in FOREGROUND mode and unacquired
            // Game still has its reference to the device
            // When game uses it next, it will only capture input when game has actual focus
            send({ type: 'info', message: 'DirectInput device restored to FOREGROUND mode - will only capture when game has focus' });
        } catch (e) {
            send({ type: 'error', message: 'Error during DirectInput cleanup: ' + e });
        }
    }
    
    // Small delay before focus removal to ensure DirectInput changes are committed
    Thread.sleep(0.1);
    
    // 3. Aggressively remove window focus and restore normal focus handling
    if (!hwnd.isNull()) {
        try {
            var user32 = Process.getModuleByName('user32.dll');
            
            // First, try to set focus to desktop/shell window
            var GetShellWindow = user32.findExportByName('GetShellWindow');
            var SetForegroundWindow = user32.findExportByName('SetForegroundWindow');
            var SetActiveWindow = user32.findExportByName('SetActiveWindow');
            var SetFocus = user32.findExportByName('SetFocus');
            
            // Remove focus from game window
            if (SetFocus) {
                var setFocus = new NativeFunction(SetFocus, 'pointer', ['pointer']);
                setFocus(ptr(0));
                send({ type: 'info', message: 'Removed focus from game window via SetFocus(NULL)' });
            }
            
            // Find and activate the shell/desktop window
            if (GetShellWindow && SetForegroundWindow) {
                var getShellWindow = new NativeFunction(GetShellWindow, 'pointer', []);
                var setForegroundWindow = new NativeFunction(SetForegroundWindow, 'int', ['pointer']);
                
                var shellWindow = getShellWindow();
                if (!shellWindow.isNull()) {
                    var result = setForegroundWindow(shellWindow);
                    send({ type: 'info', message: 'Set foreground to shell window: ' + result });
                }
            }
            
            // Note: Deactivation messages already sent earlier after WndProc restoration
            
            // Detach thread input to completely separate keyboard focus
            var AttachThreadInput = user32.findExportByName('AttachThreadInput');
            var GetWindowThreadProcessId = user32.findExportByName('GetWindowThreadProcessId');
            var GetCurrentThreadId = kernel32.findExportByName('GetCurrentThreadId');
            
            if (AttachThreadInput && GetWindowThreadProcessId && GetCurrentThreadId) {
                try {
                    var attachThreadInput = new NativeFunction(AttachThreadInput, 'int', ['uint', 'uint', 'int']);
                    var getWindowThreadProcessId = new NativeFunction(GetWindowThreadProcessId, 'uint', ['pointer', 'pointer']);
                    var getCurrentThreadId = new NativeFunction(GetCurrentThreadId, 'uint', []);
                    
                    var gameThreadId = getWindowThreadProcessId(hwnd, ptr(0));
                    var currentThreadId = getCurrentThreadId();
                    
                    // Detach our thread from the game's thread
                    if (gameThreadId !== currentThreadId) {
                        attachThreadInput(currentThreadId, gameThreadId, 0); // 0 = detach
                        send({ type: 'info', message: 'Detached thread input from game thread' });
                    }
                } catch (e) {
                    send({ type: 'info', message: 'AttachThreadInput detach not needed or failed: ' + e });
                }
            }
            
            // Unregister Raw Input devices to prevent background input capture
            var RegisterRawInputDevices = user32.findExportByName('RegisterRawInputDevices');
            if (RegisterRawInputDevices) {
                try {
                    var registerRawInputDevices = new NativeFunction(RegisterRawInputDevices, 'int', ['pointer', 'uint', 'uint']);
                    
                    // RAWINPUTDEVICE structure for keyboard (usUsagePage=1, usUsage=6)
                    var rid = Memory.alloc(12); // sizeof(RAWINPUTDEVICE)
                    rid.writeU16(1); // usUsagePage = HID_USAGE_PAGE_GENERIC
                    rid.add(2).writeU16(6); // usUsage = HID_USAGE_GENERIC_KEYBOARD
                    rid.add(4).writeU32(0x00000001); // dwFlags = RIDEV_REMOVE
                    rid.add(8).writePointer(ptr(0)); // hwndTarget = NULL
                    
                    var result = registerRawInputDevices(rid, 1, 12);
                    if (result !== 0) {
                        send({ type: 'info', message: 'Unregistered Raw Input keyboard device' });
                    }
                    
                    // Also remove mouse raw input
                    rid.add(2).writeU16(2); // usUsage = HID_USAGE_GENERIC_MOUSE
                    registerRawInputDevices(rid, 1, 12);
                } catch (e) {
                    send({ type: 'info', message: 'Raw Input cleanup not needed or failed: ' + e });
                }
            }
            
        } catch (e) {
            send({ type: 'info', message: 'Error during focus removal: ' + e });
        }
    }
    
    send({ type: 'info', message: 'Cleanup complete - all hooks detached, input released, spoofing disabled' });
}

// Watchdog
watchdogTimerId = setInterval(function() {
    if (isSpoofing && (Date.now() - lastHeartbeat > HEARTBEAT_TIMEOUT)) {
        send({ type: 'warning', message: 'Heartbeat lost! Disabling spoofing to prevent input leak.' });
        performCleanup();
    }
}, 1000);

// --- Control Interface ---
function onMessage(message) {
    try {
        var payload = message.payload || message;
        function safePtr(v) {
            try {
                if (v === null || v === undefined) return ptr(0);
                if (typeof v === 'string') {
                    var s = v.trim();
                    if (s.length === 0) return ptr(0);
                    return ptr(s);
                }
                if (typeof v === 'number') {
                    if (!isFinite(v) || v === 0) return ptr(0);
                    return ptr('0x' + (Math.floor(v) >>> 0).toString(16));
                }
                return ptr(v.toString());
            } catch (_e) {
                return ptr(0);
            }
        }
        if (payload.cmd === 'heartbeat') {
            lastHeartbeat = Date.now();
            if (!isSpoofing) {
                isSpoofing = true;
                send({ type: 'info', message: 'Heartbeat restored. Re-enabling spoofing.' });
            }
        } else if (payload.cmd === 'set_hwnd') {
            var newHwnd = safePtr(payload.hwnd);
            if (!newHwnd.isNull()) {
                gameHwnd = newHwnd;
                send({ type: 'info', message: 'Explicitly set Game HWND to: ' + gameHwnd });
            }
        } else if (payload.cmd === 'type_text' && typeof payload.text === 'string') {
            // Ensure we are "focused" first
            enqueueFocusRestore();
            
            for (var i = 0; i < payload.text.length; i++) {
                enqueueChar(payload.text[i]);
            }
            send({ type: 'info', message: 'Enqueued "' + payload.text + '"' });
            processQueue();
        } else if (payload.cmd === 'key_event') {
            // payload: { vk: int, down: bool }
            send({ type: 'info', message: 'Key Event: VK=' + payload.vk + ' Down=' + payload.down });
            enqueueKey(payload.vk, payload.down);
            processQueue();
        } else if (payload.cmd === 'mouse_event') {
            // payload: { msg: int, x: int, y: int }
            // Update internal cursor state if it's a move event
            if (payload.msg === WM_MOUSEMOVE) {
                lastMouseX = payload.x;
                lastMouseY = payload.y;
            }
            enqueueMouse(payload.msg, payload.x, payload.y);
            processQueue();
        } else if (payload.cmd === 'update_cursor') {
            lastMouseX = payload.x;
            lastMouseY = payload.y;
        } else if (payload.cmd === 'clear') {
            messageQueue = [];
            send({ type: 'info', message: 'Cleared queue' });
        } else if (payload.cmd === 'force_focus') {
            enqueueFocusRestore();
            send({ type: 'info', message: 'Enqueued Focus Restore' });
            processQueue();
        } else if (payload.cmd === 'cleanup') {
            performCleanup();
        } else if (payload.cmd === 'set_sleep_cap') {
            SLEEP_CAP = payload.val;
            send({ type: 'info', message: 'Set Sleep Cap to ' + SLEEP_CAP });
        } else if (payload.cmd === 'press_key') {
            // payload: { vk: int, count: int, interval: int }
            var count = payload.count || 1;
            var interval = payload.interval || 50;
            var vk = payload.vk;
            
            function doPress(i) {
                if (i >= count) return;
                enqueueKey(vk, true);
                processQueue();
                
                setTimeout(function() {
                    enqueueKey(vk, false);
                    processQueue();
                    if (i + 1 < count) {
                        setTimeout(function() { doPress(i + 1); }, interval);
                    }
                }, 40); // 40ms hold
            }
            doPress(0);

        } else if (payload.cmd === 'click_mouse') {
            send({ type: 'info', message: 'Received click_mouse command: x=' + payload.x + ', y=' + payload.y + ', button=' + payload.button + ', count=' + payload.count + ', isSpoofing=' + isSpoofing });
            
            var btn = payload.button || 'left';
            var count = payload.count || 1;
            var x = payload.x;
            var y = payload.y;
            
            lastMouseX = x;
            lastMouseY = y;
            
            enqueueMouse(WM_MOUSEMOVE, x, y);
            send({ type: 'info', message: 'Enqueued mouse move to (' + x + ', ' + y + ')' });
            
            var downMsg = (btn === 'left') ? WM_LBUTTONDOWN : WM_RBUTTONDOWN;
            var upMsg = (btn === 'left') ? WM_LBUTTONUP : WM_RBUTTONUP;
            
            function doClick(i) {
                if (i >= count) {
                    send({ type: 'info', message: 'Completed ' + count + ' click(s) at (' + x + ', ' + y + ')' });
                    return;
                }
                send({ type: 'info', message: 'Click ' + (i+1) + ': DOWN at (' + x + ', ' + y + '), queue length before=' + messageQueue.length });
                enqueueMouse(downMsg, x, y);
                processQueue();
                
                setTimeout(function() {
                    send({ type: 'info', message: 'Click ' + (i+1) + ': UP at (' + x + ', ' + y + '), queue length before=' + messageQueue.length });
                    enqueueMouse(upMsg, x, y);
                    processQueue();
                    if (i + 1 < count) {
                        setTimeout(function() { doClick(i + 1); }, 50);
                    }
                }, 50);
            }
            doClick(0);
        }
    } catch (e) {
        send({ type: 'error', message: 'Handler error: ' + e });
    }
    recv(onMessage);
}
recv(onMessage);
