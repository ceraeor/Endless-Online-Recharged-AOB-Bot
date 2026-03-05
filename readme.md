# Endless Online Recharged - AOB Bot (CeraBot) ⚔️

An advanced Array of Bytes (AOB) memory-reading and automation bot designed specifically for [Endless Online Recharged](https://game.endless-online.com/). 

Built with Python, this bot uses **Frida** and **Pymem** for dynamic memory hooking and reading, bypassing the need for static pointers. It features a full graphical user interface (GUI), A* pathfinding, and background input simulation so you can use your PC while the bot runs.

## 🌟 Features

* **Full GUI Control Panel:** Manage settings, hotkeys, and monitor live stats via a custom dark-mode Tkinter dashboard.
* **AOB Memory Scanning:** Dynamically resolves pointers for player coordinates, HP/MP, map IDs, NPCs, and chat, making it highly resilient to minor game updates.
* **Background Execution:** Uses an embedded Frida script (`input_spoofer.js`) to send mouse and keyboard inputs directly to the game window, even when minimized or out of focus.
* **Smart Combat & Pathfinding:** Utilizes A* pathfinding and Bresenham's line algorithm to navigate around obstacles and establish line-of-sight for attacks.
* **Walkable Map Recorder:** Built-in tool to record and save safe "walkable" tiles directly from the GUI.
* **Advanced Auto-Looting:** Supports directional looting and fast-click bursts.
* **Safety & Avoidance Systems:** * Avoid other players (stays 1 tile away).
  * Party Training mode (clears targets if "you received" appears in the chatlog).
  * HP Emergency Home (runs to a safe coordinate if HP drops below a set percentage).
* **Dynamic Weight Lock:** Actively locks inventory weight to 0 while the bot is running.

## ⚠️ Disclaimer

**Educational Purposes Only.** Using third-party software, bots, or memory scanners is against the Terms of Service of Endless Online Recharged. Using this bot on official servers may result in your account being permanently banned. The creator (`ceraeor`) is not responsible for any bans, damages, or account losses incurred by using this software. Use at your own risk.

## 🛠️ Prerequisites

Before running the bot, ensure you have the following installed:

* Python 3.8+
* An active Endless Online Recharged client window.

### Required Python Packages
Install the dependencies using pip:
`pip install pydirectinput pymem frida pyautogui bresenham ttkthemes pynput pywin32`

## 🚀 Installation & Usage

1.  **Clone the repository:**
    ```bash
    git clone [https://github.com/ceraeor/Endless-Online-Recharged-AOB-Bot.git](https://github.com/ceraeor/Endless-Online-Recharged-AOB-Bot.git)
    cd Endless-Online-Recharged-AOB-Bot
    ```
2.  **Ensure `input_spoofer.js` is present:** The bot requires this JavaScript file in the root directory to handle background inputs.
3.  **Run the Bot (Requires Administrator Privileges):**
    ```bash
    python CeraBot-v19.py
    ```
    *Note: Administrator privileges are strictly required for `pymem` and `frida` to read the game's process memory.*
4.  **Select the Game Process:** If multiple Endless clients are open, the bot will prompt you to click the desired window and press `F12` to bind to that specific PID.
5.  **Record Click Points:** On first launch, click "Record Click Points" in the GUI to teach the bot where to click for directional looting.

## ⌨️ Default Hotkeys

All hotkeys can be fully customized and rebound within the **Hotkeys tab** of the GUI. 

* `F1` - Mining Tool
* `F2` - Chopping Tool
* `F3` - HP Buff / Potion
* `F5` - Self Heal Buff
* `F6` - Tiny Regen Buff
* `F7` - Switch To Sit Item
* `F8` - Switch To Combat Item
* `F11` - Sit Down/Stand Up
* `F12` - Capture Window PID (Boot Phase Only)

## 🤝 Contributing

Contributions, issues, and feature requests are welcome! 
Feel free to check out the [issues page](https://github.com/ceraeor/Endless-Online-Recharged-AOB-Bot/issues).

## 📝 License

Distributed under the MIT License. See `LICENSE` for more information.

---
*Created by [ceraeor](https://github.com/ceraeor)*
