# Endless Online Recharged - AOB Bot (CeraBot) ⚔️

An advanced Array of Bytes (AOB) memory-reading and automation bot designed specifically for Endless Online Recharged.

Built with Python, this bot uses Frida and Pymem for dynamic memory hooking and reading, bypassing the need for static pointers. It features a full graphical user interface (GUI), A* pathfinding, and background input simulation so you can use your PC while the bot runs.

------------------------------------------------------------

🌟 Features

Full GUI Control Panel  
Manage settings, hotkeys, and monitor live stats via a custom dark-mode Tkinter dashboard.

AOB Memory Scanning  
Dynamically resolves pointers for player coordinates, HP/MP, map IDs, NPCs, and chat. This makes the bot highly resilient to minor game updates because it does not rely on static memory pointers.

Background Execution  
Uses an embedded Frida script (input_spoofer.js) to send mouse and keyboard inputs directly to the game window even when:

• The game window is minimized  
• The game window is not focused  
• You are using your computer for other tasks  

Smart Combat & Pathfinding  
Utilizes A* pathfinding and Bresenham's line algorithm to navigate around obstacles and establish line-of-sight for attacks.

Walkable Map Recorder  
Built-in tool to record and save safe “walkable” tiles directly from the GUI.

Advanced Auto-Looting  
Supports directional looting and fast-click bursts for faster item pickup.

Safety & Avoidance Systems

• Avoid other players (stays 1 tile away)  
• Party Training mode (clears targets if "you received" appears in the chatlog)  
• HP Emergency Home (runs to a safe coordinate if HP drops below a set percentage)  
• Dynamic Weight Lock (actively locks inventory weight to 0 while the bot is running)

------------------------------------------------------------

⚠️ Disclaimer

Educational Purposes Only.

Using third-party software, bots, or memory scanners is against the Terms of Service of Endless Online Recharged.

Using this bot on official servers may result in your account being permanently banned.

The creator (ceraeor) is not responsible for any bans, damages, or account losses incurred by using this software.

Use at your own risk.

------------------------------------------------------------

🛠️ System Requirements

Operating System
Windows only (required for Win32 API calls used by the bot)

Python
Python 3.10 or Python 3.11 recommended

Game Client
An active Endless Online Recharged client window

Administrator Privileges
The bot must be run as Administrator because:

• pymem reads process memory
• frida attaches to the running process

------------------------------------------------------------

⚠️ IMPORTANT FRIDA VERSION

The bot requires:

frida version 16.x

Frida version 17 is NOT compatible and will break the bot.

Install the correct version using:

pip uninstall frida
pip install frida==16.1.4

------------------------------------------------------------

📦 Python Dependencies

The bot requires the following Python packages:

• frida
• pymem
• pydirectinput
• pyautogui
• bresenham
• pynput
• ttkthemes
• pywin32

The easiest way to install everything is using the provided requirements.txt file.

Install with:

pip install -r requirements.txt

------------------------------------------------------------

📂 Folder Structure

Your folder should look like this:

Endless-Online-Recharged-AOB-Bot/

CeraBot-v19.py  
input_spoofer.js  
requirements.txt  
README.md  

config/  
walkable_maps/  

The bot will automatically create the config and walkable_maps folders if they do not already exist.

------------------------------------------------------------

🚀 Installation

1) Clone the repository

git clone https://github.com/ceraeor/Endless-Online-Recharged-AOB-Bot.git

2) Enter the project folder

cd Endless-Online-Recharged-AOB-Bot

3) Install dependencies

pip install -r requirements.txt

------------------------------------------------------------

▶ Running the Bot

1) Start Endless Online Recharged first.

2) Run the bot as Administrator.

python CeraBot-v19.py

------------------------------------------------------------

🧠 How Background Input Works

The bot loads a Frida script called:

input_spoofer.js

This script performs several actions:

• Prevents the game from losing focus  
• Sends keyboard events to the game  
• Sends mouse click events to the game  
• Hooks the Windows message loop  
• Spoofs foreground window detection  

This allows the bot to control the game even when the window is minimized or unfocused.

------------------------------------------------------------

🎯 First Time Setup

When launching the bot for the first time:

1) Select the Game Process

If multiple Endless clients are open, the bot will prompt you to click the correct window and press:

F12

This binds the bot to the correct process ID.

2) Record Click Points

Click the GUI button:

Record Click Points

This teaches the bot where to click for directional looting.

------------------------------------------------------------

⌨️ Default Hotkeys

All hotkeys can be customized inside the Hotkeys tab of the GUI.

F1  - Mining Tool  
F2  - Chopping Tool  
F3  - HP Buff / Potion  
F5  - Self Heal Buff  
F6  - Tiny Regen Buff  
F7  - Switch To Sit Item  
F8  - Switch To Combat Item  
F11 - Sit Down / Stand Up  
F12 - Capture Window PID (Boot Phase Only)

------------------------------------------------------------

🗺 Walkable Maps

Walkable map files should be placed inside:

walkable_maps/

These maps define which tiles the bot is allowed to move across when pathfinding.

Maps can be recorded directly from the GUI using the Walkable Map Recorder.

------------------------------------------------------------

⚙️ Config Files

Settings are saved in:

config/cerabot_config.json

The bot will automatically create this file when you save settings from the GUI.

------------------------------------------------------------

🛠 Troubleshooting

Frida Attach Failed

Make sure you are using Frida 16:

pip uninstall frida
pip install frida==16.1.4


input_spoofer.js Missing

Ensure this file exists in the same directory as the bot:

input_spoofer.js


Bot Not Sending Inputs

Possible causes:

• Game started after bot  
• Frida failed to attach  
• Running without administrator privileges  
• input_spoofer.js missing  


pywin32 Errors

Install manually:

pip install pywin32


Module Not Found Errors

Reinstall dependencies:

pip install -r requirements.txt --upgrade

------------------------------------------------------------

🤝 Contributing

Contributions, issues, and feature requests are welcome.

Feel free to check out the issues page or submit improvements.

------------------------------------------------------------

📝 License

Distributed under the MIT License.

See LICENSE for more information.

------------------------------------------------------------

Created by ceraeor

Join the Discord! 
https://discord.gg/TxEttS4jNe
