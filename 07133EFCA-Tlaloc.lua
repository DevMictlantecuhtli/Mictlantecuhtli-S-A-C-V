--[[                                                                                                                                                                                                                                                                                           
MMP""MM""YMM `7MMF'            db      `7MMF'        .g8""8q.     .g8"""bgd      .M"""bgd   .g8"""bgd `7MM"""Mq.  `7MMF'`7MM"""Mq. MMP""MM""YMM 
P'   MM   `7   MM             ;MM:       MM        .dP'    `YM. .dP'     `M     ,MI    "Y .dP'     `M   MM   `MM.   MM    MM   `MM.P'   MM   `7 
     MM        MM            ,V^MM.      MM        dM'      `MM dM'       `     `MMb.     dM'       `   MM   ,M9    MM    MM   ,M9      MM      
     MM        MM           ,M  `MM      MM        MM        MM MM                `YMMNq. MM            MMmmdM9     MM    MMmmdM9       MM      
     MM        MM      ,    AbmmmqMA     MM      , MM.      ,MP MM.             .     `MM MM.           MM  YM.     MM    MM            MM      
     MM        MM     ,M   A'     VML    MM     ,M `Mb.    ,dP' `Mb.     ,'     Mb     dM `Mb.     ,'   MM   `Mb.   MM    MM            MM      
   .JMML.    .JMMmmmmMMM .AMA.   .AMMA..JMMmmmmMMM   `"bmmd"'     `"bmmmd'      P"Ybmmd"    `"bmmmd'  .JMML. .JMM..JMML..JMML.        .JMML.                                                                                                                                                   
   
   
   ____           ____            __  ____      __  __            __                  __    __  ___ 
   / __ )__  __   / __ \___ _   __/  |/  (_)____/ /_/ /___ _____  / /____  _______  __/ /_  / /_/ (_)
  / __  / / / /  / / / / _ \ | / / /|_/ / / ___/ __/ / __ `/ __ \/ __/ _ \/ ___/ / / / __ \/ __/ / / 
 / /_/ / /_/ /  / /_/ /  __/ |/ / /  / / / /__/ /_/ / /_/ / / / / /_/  __/ /__/ /_/ / / / / /_/ / /  
/_____/\__, /  /_____/\___/|___/_/  /_/_/\___/\__/_/\__,_/_/ /_/\__/\___/\___/\__,_/_/ /_/\__/_/_/   
      /____/                                                                                         
                                                                                                                                               
_/\/\/\/\/\____________________/\/\/\/\/\____________________________/\/\______/\/\__/\/\__________________/\/\______/\/\______________________________/\
_/\/\____/\/\__/\/\__/\/\______/\/\____/\/\____/\/\/\____/\/\__/\/\__/\/\/\__/\/\/\____________/\/\/\/\__/\/\/\/\/\__/\/\____/\/\/\______/\/\/\/\____/\/\|
_/\/\/\/\/\____/\/\__/\/\______/\/\____/\/\__/\/\/\/\/\__/\/\__/\/\__/\/\/\/\/\/\/\__/\/\____/\/\__________/\/\______/\/\________/\/\____/\/\__/\/\____/\|
_/\/\____/\/\____/\/\/\/\______/\/\____/\/\__/\/\__________/\/\/\____/\/\__/\__/\/\__/\/\____/\/\__________/\/\______/\/\____/\/\/\/\____/\/\__/\/\____/\| 
_/\/\/\/\/\__________/\/\______/\/\/\/\/\______/\/\/\/\______/\______/\/\______/\/\__/\/\/\____/\/\/\/\____/\/\/\____/\/\/\__/\/\/\/\/\__/\/\__/\/\____/\|
_______________/\/\/\/\__________________________________________________________________________________________________________________________________|
]]--


local Library = loadstring(game:HttpGet("https://raw.githubusercontent.com/xHeptc/Kavo-UI-Library/main/source.lua"))()
local Window = Library.CreateLib("|TLALOC| |LECHUGAFRIA|  ", "DarkTheme")
local Tab = Window:NewTab("AutoFarm")
local MainSection = Tab:NewSection("AutoFarmNPC")
local TargetTab = Window:NewTab("Players")
local TargetSection = TargetTab:NewSection("Jugadores")
local STab = Window:NewTab("Options")
local SSection = STab:NewSection("Opciones")
local StatTab = Window:NewTab("AutoStats")
local StatSection = StatTab:NewSection("AutoStats")
local TTab = Window:NewTab("Teleport")
local TSection = TTab:NewSection("Teleport")
local KTab = Window:NewTab("Keybind")
local KSection = KTab:NewSection("Teclas")
local MTab = Window:NewTab("Extras")
local MSection = MTab:NewSection("Extras")
local GTab = Window:NewTab("Scripts")
local GSection = GTab:NewSection("Scripts")
local Players = game:GetService("Players")
local ReplicatedStorage = game:GetService("ReplicatedStorage")
local RunService = game:GetService("RunService")
local Module = require(ReplicatedStorage.Modules.SharedLocal)
local punchEvent = ReplicatedStorage.Events.Punch
local upgradeEvent = ReplicatedStorage.Events.UpgradeAbility
local player = Players.LocalPlayer
local AutoClickToggle = false
local player = game.Players.LocalPlayer
local upperTorso = player.Character and player.Character:FindFirstChild("UpperTorso")
local Players = game:GetService("Players")
local UserInputService = game:GetService("UserInputService")
local flyStatus = false
local flyAnimator = nil
local speed = 10
_G.CToggle = false
_G.metalskin = false
_G.LOCALPLAYER = game.Players.LocalPlayer.Name
_G.bring = false
_G.player = game.Players.LocalPlayer
_G.AOH = true
_G.AOHValue = true
_G.gyrospeed = 200
_G.Rapidvalue = 10
_G.rotationAngle = 90
_G.Punchval = 0.1
_G.metalskin = false
_G.SelectedLocation = nil
_G.speed = 16
_G.jump = 50
_G.Rotationspeed = 0.10
_G.Rotationrange = 10
_G.TelekinesisCarry = false
_G.Stat = nil
_G.AntiTelePlayers = {}
_G.Point = nil
_G.CToggle = false
_G.metalskin = false
_G.LOCALPLAYER = game.Players.LocalPlayer.Name
_G.bring = false
_G.TRUELOOP = true
_G.LWS = false
_G.tplayer = nil
_G.gplayer = nil
_G.auto = nil
for _, connection in next, getconnections(player.Idled) do
    connection:Disable()
end
local introScript = player:FindFirstChild("PlayerScripts"):FindFirstChild("IntroScript")
if not player.Character then
    wait(1)
    if introScript and introScript:IsA("ModuleScript") then
        getsenv(introScript).Play()
    end
end
local function breakVelocity()
    local V3 = Vector3.new(0, 0, 0)
    wait(1)
    for _, part in ipairs(player.Character:GetDescendants()) do
        if part:IsA("BasePart") then
            part.Velocity, part.RotVelocity = V3, V3
        end
    end
end
spawn(breakVelocity)
local plrlist = {}
local plrnum = 0
local function getNearPlayer(maxDistance)
    pcall(
        function()
            if player and player.Character then
                local playerLocation = player.Character.HumanoidRootPart.Position
                for _, otherPlayer in pairs(game.Players:GetPlayers()) do
                    if otherPlayer.Character and otherPlayer.Character:FindFirstChild("Humanoid") then
                        local location = otherPlayer.Character.HumanoidRootPart.Position
                        local distance = (location - playerLocation).Magnitude
                        if distance <= maxDistance and otherPlayer.Character.Humanoid.Health > 0 then
                            pcall(
                                function()
                                    if otherPlayer == player then
                                    else
                                        local teleExist =
                                            game:GetService("Workspace"):FindPartOnRayWithIgnoreList(
                                            Ray.new(playerLocation, location - playerLocation),
                                            {player.Character, otherPlayer.Character}
                                        )
                                        if not teleExist and otherPlayer.Character.Humanoid.Health > 0 then
                                            plrnum = plrnum + 1
                                            table.insert(plrlist, otherPlayer.Character)
                                        end
                                    end
                                end
                            )
                        end
                    end
                end
            end
        end
    )
end
local function GetList()
    dropdown = {}
    for _, player in pairs(game.Players:GetPlayers()) do
        if player:IsA("Player") then
            table.insert(dropdown, player.Name)
        end
    end
end
GetList = function()
    x = 1
    Plyr = game.Players:GetPlayers()
    dropdown = {}
    for value in pairs(Plyr) do
        PLR = Plyr[x].Name
        x = x + 1
        table.insert(dropdown, PLR)
    end
end
local function MOVEPLAYERSINTELE(POSFORPLAYER, playerName)
    pcall(
        function()
            local playerToMove = game.Players:FindFirstChild(playerName)
            if playerToMove and playerToMove.Character and playerToMove.Character:FindFirstChild("HumanoidRootPart") then
                playerToMove.Character.HumanoidRootPart.telekinesisPosition.Position = POSFORPLAYER
            end
        end
    )
end

local function HandleZoneSelection(currentOption)
    _G.selectedstat = currentOption
end


local function HandleTeleportToggle(state)
    _G.bring = state
end


local function teleportPlayers(position, bring)
    for _, player in pairs(plrlist) do
        local humanoidRootPart = game:GetService("Workspace")[player.Name].HumanoidRootPart

        if bring then
            humanoidRootPart.telekinesisPosition:Destroy()
        end

        humanoidRootPart.CFrame = CFrame.new(position)
        wait(0.2)
        game:GetService("ReplicatedStorage").Events.ToggleTelekinesis:InvokeServer(
            Vector3.new(1, 1, 1),
            false,
            game.Players[player.Name].Character
        )
    end
end


local safezoneDropdown =
    TSection:NewDropdown(
    "Safezone Locations",
    "",
    {
        "Bar",
        "Building Park",
        "City Square",
        "Evil Lair",
        "Field",
        "Hero HQ",
        "Hero Lair",
        "Motel",
        "Mountain",
        "Mountain-2",
        "Park",
        "Plains",
        "Prison"
    },
    function(currentOption)
        _G.selectedstat = currentOption
    end
)

local otherLocationsDropdown =
    TSection:NewDropdown(
    "Other Locations",
    "",
    {
        "Construction Building",
        "Corner-1",
        "Corner-2",
        "Corner-3",
        "Corner-4",
        "Ignite Tower",
        "Military Base",
        "Mountain Hole",
        "Police Department",
        "Cave"
    },
    function(currentOption)
        _G.selectedstat = currentOption
    end
)

local unfortunateLocationsDropdown =
    TSection:NewDropdown(
    "Unfortunate Locations",
    "",
    {"Secret Area", "In Building", "Trap", "Space", "Under Map", "Dead End", "Box", "Arena", "Backrooms", "Sex Dungeon"},
    function(currentOption)
        _G.selectedstat = "Unfortunate Spot (" .. currentOption .. ")"
    end
)

-- Toggle for Teleport Player
TSection:NewToggle(
    "Teleport Player",
    "",
    function(state)
        _G.bring = state
    end
)

-- Button to initiate teleportation
TSection:NewButton(
    "Teleport",
    "",
    function()
        getNearPlayer(999999999999999999999999)

        local locations = {
            ["Bar"] = Vector3.new(-1313, 197, 149),
            ["Building Park"] = Vector3.new(-1751, 442, 1266),
            ["City Square"] = Vector3.new(-385, 86, 256),
            ["Evil Lair"] = Vector3.new(-905, 94, -1086),
            ["Field"] = Vector3.new(2355, 81, 4),
            ["Hero HQ"] = Vector3.new(259, 169, 2748),
            ["Hero Lair"] = Vector3.new(2351, 39, -1855),
            ["Motel"] = Vector3.new(-1750, 94, -1349),
            ["Mountain"] = Vector3.new(-2206, 817, -2425),
            ["Mountain-2"] = Vector3.new(-2429, 762, -2363),
            ["Park"] = Vector3.new(1399, 94, 1154),
            ["Plains"] = Vector3.new(-3683, 97, -144),
            ["Prison"] = Vector3.new(-779, 269, -2594),
            ["Construction Building"] = Vector3.new(650, 779, 284),
            ["Corner-1"] = Vector3.new(2773, 96, -4996),
            ["Corner-2"] = Vector3.new(-3757, 97, -3801),
            ["Corner-3"] = Vector3.new(-3650, 97, 2764),
            ["Corner-4"] = Vector3.new(2810, 102, 2821),
            ["Ignite Tower"] = Vector3.new(-70, 616, -247),
            ["Military Base"] = Vector3.new(259, 99, -4639),
            ["Mountain Hole"] = Vector3.new(-2732, 256, -1776),
            ["Police Department"] = Vector3.new(-62, 94, -480),
            ["Cave"] = Vector3.new(269, -59, 2729),
            ["Unfortunate Spot (Secret Area)"] = Vector3.new(-1100, 61, -1169),
            ["Unfortunate Spot (In Building)"] = Vector3.new(-494, 96, -98),
            ["Unfortunate Spot (Trap)"] = Vector3.new(-790, 135, -2769),
            ["Unfortunate Spot (Space)"] = Vector3.new(0, 9999999, 0),
            ["Unfortunate Spot (Under Map)"] = Vector3.new(0, 0, 0),
            ["Unfortunate Spot (Dead End)"] = Vector3.new(1453, 98, -2506),
            ["Unfortunate Spot (Box)"] = Vector3.new(-1695, 94, -1309),
            ["Unfortunate Spot (Arena)"] = Vector3.new(-1728, 94, -1188),
            ["Unfortunate Spot (Backrooms)"] = Vector3.new(-1519, 95, -1072),
            ["Unfortunate Spot (Sex Dungeon)"] = Vector3.new(-1585, 95, -1159)
        }

        local selectedLocation = locations[_G.selectedstat]

        if selectedLocation then
            if _G.bring then
                teleportPlayers(selectedLocation, true)
            else
                game.Players.LocalPlayer.Character.HumanoidRootPart.CFrame = CFrame.new(selectedLocation)
                breakvelocity()
            end
        end

        plrlist = {}
    end
)

StatSection:NewDropdown(
    "AutoStats",
    "",
    {
        "vitality",
        "healing",
        "strength",
        "energy",
        "flight",
        "speed",
        "climbing",
        "swinging",
        "fireball",
        "frost",
        "lightning",
        "power",
        "telekinesis",
        "shield",
        "laserVision",
        "metalSkin"
    },
    function(currentOption)
        selectedstat = currentOption
    end
)

local function upgradeStatisticFast(stat, totalIncrements)
    if stat == nil or totalIncrements == nil then
        return
    end
    local invokeServer = game:GetService("ReplicatedStorage").Events.UpgradeAbility.InvokeServer

    local incrementsPerRequest = 10
    local remainingIncrements = totalIncrements

    while remainingIncrements > 0 do
        local currentIncrements = math.min(incrementsPerRequest, remainingIncrements)
        task.spawn(
            function()
                for _ = 1, currentIncrements do
                    invokeServer(game:GetService("ReplicatedStorage").Events.UpgradeAbility, stat)
                end
            end
        )

        remainingIncrements = remainingIncrements - currentIncrements

       
        local lastTwoDigits = tonumber(tostring(remainingIncrements):sub(-2))

       
        wait(lastTwoDigits > 10 and 0.2 or 0.1)
    end
end

StatSection:NewToggle(
    "AutoStat :D",
    "",
    function(state)
        if state then
            getgenv().AutoStatsFast = true
            while AutoStatsFast do
                wait(0.5)
                spawn(
                    function()
                        upgradeStatisticFast(selectedstat, 1000) 
                    end
                )
            end
        else
           
            getgenv().AutoStatsFast = false
        end
    end
)

local function toggleLogic()
    local Noclip = nil
    local Clip = nil
    local Antifling = true
    local function noclip()
        Clip = false
        local function Nocl()
            if Clip == false and game.Players.LocalPlayer.Character then
                for _, v in pairs(game.Players.LocalPlayer.Character:GetDescendants()) do
                    if v:IsA("BasePart") and v.CanCollide and v.Name ~= floatName then
                        v.CanCollide = false
                    end
                end
            end
            wait(0.21)
        end
        Noclip = game:GetService("RunService").Stepped:Connect(Nocl)
    end

    local function clip()
        if Noclip then
            Noclip:Disconnect()
            if game.Players.LocalPlayer.Character then
                for _, v in pairs(game.Players.LocalPlayer.Character:GetDescendants()) do
                    if v:IsA("BasePart") and v.Name ~= floatName then
                        v.CanCollide = true
                    end
                end
            end
        end
        Clip = true
    end

    local function antiflingLogic()
        while Antifling do
            game:GetService("RunService").Stepped:Wait()
            for _, player in pairs(game:GetService("Players"):GetPlayers()) do
                if player ~= game.Players.LocalPlayer then
                    pcall(
                        function()
                            for _, descendant in pairs(player.Character:GetDescendants()) do
                                pcall(
                                    function()
                                        if descendant:IsA("BasePart") and descendant.CanCollide then
                                            descendant.CanCollide = false
                                        end
                                    end
                                )
                            end
                        end
                    )
                end
            end
        end
    end

    if Toggle then
        noclip()
        spawn(
            function()
                antiflingLogic()
            end
        )
    else
        clip()
        Antifling = false
    end
end

SSection:NewToggle(
    "Noclip & Antifling",
    "",
    function(state)
        Toggle = state
        toggleLogic()
    end
)


local directionTable = {
    [Enum.KeyCode.W] = Vector3.new(0, 0, 1),
    [Enum.KeyCode.S] = Vector3.new(0, 0, -1),
    [Enum.KeyCode.D] = Vector3.new(1, 0, 0),
    [Enum.KeyCode.A] = Vector3.new(-1, 0, 0),
    [Enum.KeyCode.Space] = Vector3.new(0, 1, 0),
    [Enum.KeyCode.LeftControl] = Vector3.new(0, -1, 0)
}

local function startFlyAnimation()
    local animation = game:GetService("ReplicatedStorage").Animations.flyLoop
    local character = game.Players.LocalPlayer.Character

    if character and character:FindFirstChild("Humanoid") then
        local animator = character.Humanoid.Animator
        local animationTrack = animator:LoadAnimation(animation)

        if animationTrack then
            animationTrack.Looped = false
            animationTrack:Play(0.1, 1, 0)
            return animationTrack
        end
    end

    return nil
end

local function setupFlyComponents()
    local hrp = game.Players.LocalPlayer.Character.HumanoidRootPart
    local bp = Instance.new("BodyPosition", hrp)
    local br = Instance.new("BodyGyro", hrp)

    bp.MaxForce = Vector3.new(1000000, 1000000, 1000000)
    bp.P = 1000000

    br.D = 100
    br.P = 1000
    br.MaxTorque = Vector3.new(1000000, 1000000, 1000000)

    return bp, br
end

local function onKeyPress(input, isPressed)
    local direction = directionTable[input.KeyCode]

    if direction then
        directionTable[input.KeyCode] = isPressed
    end
end

local function onCharacterDied()
    wait(6) 
    if flyStatus then
        flyAnimator = startFlyAnimation()
        flyThread()
    end
end

local function flyThread()
    local hrp = game.Players.LocalPlayer.Character.HumanoidRootPart
    local humanoid = game.Players.LocalPlayer.Character:WaitForChild("Humanoid")
    local bp, br = setupFlyComponents()

    humanoid.PlatformStand = true
    br.CFrame = game.Workspace.CurrentCamera.CFrame

    game:GetService("UserInputService").InputBegan:Connect(
        function(input)
            onKeyPress(input, true)
        end
    )

    game:GetService("UserInputService").InputEnded:Connect(
        function(input)
            onKeyPress(input, false)
        end
    )

    humanoid.Died:Connect(onCharacterDied)

    while flyStatus do
        local totalDirection = Vector3.new()

        for key, direction in pairs(directionTable) do
            if directionTable[key] then
                totalDirection = totalDirection + direction
            end
        end

        bp.Position = hrp.Position + totalDirection * speed
        wait()
    end

    humanoid.PlatformStand = false
    bp:Destroy()
    br:Destroy()

    if flyAnimator then
        flyAnimator:Stop()
        flyAnimator = nil
    end
end

SSection:NewToggle(
    "Fly",
    "",
    function(state)
        flyStatus = state

        if flyStatus then
            flyAnimator = startFlyAnimation()
            flyThread()
        end
    end
)

local userInputService = game:GetService("UserInputService")

local function simulateTouchTap()
    local touchInput = Instance.new("InputObjectEvent")
    touchInput.UserInputType = Enum.UserInputType.Touch
    touchInput.UserInputState = Enum.UserInputState.Begin
    touchInput.Position = Vector2.new()

    userInputService.InputBegan:Fire(touchInput)
end

local AutoClickToggle = false

local function AutoClickLogic()
    while AutoClickToggle do
        wait(600) 
        
        simulateTouchTap()
    end
end
local function AutoClickLogic()
    while AutoClickToggle do
        wait(600)

        mouse1press()
        userInputService.InputBegan:Fire(Vector2.new(), Enum.UserInputType.Touch)
        wait(0.1)
        mouse1release()
        userInputService.InputEnded:Fire(Vector2.new(), Enum.UserInputType.Touch)
    end
end

-- Crear un toggle para activar/desactivar el autoclick
SSection:NewToggle(
    "ANTI-AFK",
    "close menu(phone)|(emulator)put the arrow in the free zone",
    function(state)
        AutoClickToggle = state
        if AutoClickToggle then
            spawn(AutoClickLogic)
        end
    end
)

MainSection:NewToggle(
    "Laser NPC Farm",
    "",
    function(state)
        if state then
            while true do
                local event = game:GetService("ReplicatedStorage").Events.ToggleLaserVision
                local part = event:InvokeServer(true)
                local endTime = os.time() + 600 

                while os.time() < endTime do
                    wait()
                    for _, v in pairs(game.Workspace:GetChildren()) do
                        if
                            v:IsA("Model") and (v.Name == "Civilian" or v.Name == "Police" or v.Name == "Thug") and
                                v:FindFirstChild("Humanoid") and
                                (v.Humanoid.Health > 0)
                         then
                            part.Position = v.HumanoidRootPart.Position
                        end
                    end
                end
                event:InvokeServer(false)
                wait(600) 
            end
        else
            spawn(
                function()
                    getgenv().LaserFarm = false
                end
            )
            breakvelocity()
        end
    end
)

local function teleportOrbs()
    local player = game.Players.LocalPlayer
    if player then
        while true do
            local success, _ =
                pcall(
                function()
                    local character = player.Character
                    local orb = game:GetService("Workspace").ExperienceOrbs:FindFirstChild("experienceOrb")

                    if character and orb then
                        orb.CFrame = CFrame.new(character.HumanoidRootPart.Position)
                    end
                end
            )

            wait(0.2)
        end
    end
end

MainSection:NewToggle("Teleport Orbs", "", teleportOrbs)

local function spawnPoint(state)
    if state then
        getgenv().Deathcheck = true

        local varPosition = upperTorso and upperTorso.Position
        if not varPosition then
            warn("UpperTorso not found. Make sure the character is loaded.")
            return
        end

        spawn(
            function()
                while getgenv().Deathcheck do
                    local playerHealth =
                        player.Character and player.Character:FindFirstChild("Humanoid") and
                        player.Character.Humanoid.Health
                    if playerHealth and playerHealth == 0 then
                        wait(5)
                        player.Character:MoveTo(varPosition)
                    end
                    wait(1)
                end
            end
        )
    else
        getgenv().Deathcheck = false
    end
end
TSection:NewToggle("Spawn Point", "", spawnPoint)

local function AutoClickLogic()
    wait(8)

    while AutoClickToggle do
        for _ = 1, 8 do
            
            mouse1press()
            wait(0.1)
            mouse1release()
            wait(0.2)
        end
    end
end

local userInputService = game:GetService("UserInputService")


SSection:NewToggle(
    "Auto Punch",
    "",
    function(state)
        AutoClickToggle = state
        if AutoClickToggle then
            spawn(AutoClickLogic)
        end
    end
)


KSection:NewKeybind(
    "Auto Punch",
    "",
    Enum.KeyCode.LeftControl,
    function()
        if AutoClickToggle then
            AutoClickToggle = not AutoClickToggle
            if AutoClickToggle then
                spawn(AutoClickLogic)
            end
        end
    end
)

SSection:NewToggle(
    "Kill Aura",
    "",
    function(state)
        getgenv().killaura = state
        local function calculateDistance(pos1, pos2)
            return (pos1 - pos2).Magnitude
        end
        local function isCloseEnough(player, localPosition)
            local playerCharacter = player.Character
            if playerCharacter then
                local playerRootPart = playerCharacter:FindFirstChild("HumanoidRootPart")
                if playerRootPart then
                    local playerPosition = playerRootPart.Position
                    local distance = calculateDistance(localPosition, playerPosition)
                    return distance <= 8
                end
            end
            return false
        end
        if state then
            while getgenv().killaura do
                pcall(
                    function()
                        local LocalPlayer = Players.LocalPlayer
                        local LocalRootPart =
                            LocalPlayer.Character and LocalPlayer.Character:FindFirstChild("HumanoidRootPart")
                        local localPosition = LocalRootPart and LocalRootPart.Position
                        if localPosition then
                            for _, player in ipairs(Players:GetPlayers()) do
                                if player ~= LocalPlayer and isCloseEnough(player, localPosition) then
                                    ReplicatedStorage.Events.Punch:FireServer(0.4, 0.1, 1)
                                end
                            end
                        end
                    end
                )
                wait()
            end
        end
    end
)
local function getRoot(character)
    return character:FindFirstChild("HumanoidRootPart") or character:FindFirstChild("Torso") or
        character:FindFirstChild("UpperTorso")
end
SSection:NewToggle(
    "Anti-Tele",
    "",
    function(state)
        if state then
            getgenv().localtele = true
            spawn(
                function()
                    while localtele do
                        game:GetService("ReplicatedStorage").Events.ToggleTelekinesis:InvokeServer(
                            Vector3.new(1, 1, 1),
                            false,
                            game.Players[_G.LOCALPLAYER].Character
                        )
                        wait()
                    end
                end
            )
        else
            spawn(
                function()
                    getgenv().localtele = false
                end
            )
        end
    end
)
SSection:NewToggle(
    "Auto MetalSkin",
    "",
    function(state)
        if state then
            getgenv().metal = true
            while metal do
                wait(0.2)
                spawn(
                    function()
                        game:GetService("ReplicatedStorage").Events.Transform:FireServer("metalSkin", true)
                    end
                )
            end
        else
            spawn(
                function()
                    getgenv().metal = false
                    wait(0.2)
                    game:GetService("ReplicatedStorage").Events.Transform:FireServer("metalSkin", false)
                end
            )
        end
    end
)
SSection:NewToggle(
    "Disable Telekinesis",
    "",
    function(state)
        spawn(
            function()
                if state then
                    Players = game:GetService("Players")
                    for i, player in pairs(Players:GetPlayers()) do
                        getgenv().LToggle = true
                        spawn(
                            function()
                                while LToggle do
                                    wait()
                                    game:GetService("ReplicatedStorage").Events.ToggleTelekinesis:InvokeServer(
                                        Vector3.new(1, 1, 1),
                                        false,
                                        game.Players[player.Name].Character
                                    )
                                end
                            end
                        )
                    end
                else
                    spawn(
                        function()
                            getgenv().LToggle = false
                        end
                    )
                end
            end
        )
    end
)
SSection:NewToggle(
    "Anti-Knockback",
    "",
    function(state)
        if state then
            getgenv().AntiKnockback = true
            while AntiKnockback do
                task.wait()
                spawn(
                    function()
                        local PrimaryPart = player.Character.PrimaryPart
                        if
                            ((PrimaryPart.AssemblyLinearVelocity.Magnitude > 250) or
                                (PrimaryPart.AssemblyAngularVelocity.Magnitude > 250))
                         then
                            PrimaryPart.AssemblyAngularVelocity = Vector3.new(0, 0, 0)
                            PrimaryPart.AssemblyLinearVelocity = Vector3.new(0, 0, 0)
                            PrimaryPart.CFrame = LastPosition
                        elseif
                            ((PrimaryPart.AssemblyLinearVelocity.Magnitude < 50) or
                                (PrimaryPart.AssemblyAngularVelocity.Magnitude > 50))
                         then
                            LastPosition = PrimaryPart.CFrame
                        end
                    end
                )
            end
        else
            spawn(
                function()
                    getgenv().AntiKnockback = false
                end
            )
        end
    end
)
GetList()
local slcplr =
    TargetSection:NewDropdown(
    "Player List",
    "",
    dropdown,
    function(currentOption)
        spawn(
            function()
                _G.tplayer = currentOption
            end
        )
    end
)
MSection:NewSlider(
    "Speed",
    "",
    2000,
    16,
    function(s)
        game.Players.LocalPlayer.Character.Humanoid.WalkSpeed = s
    end
)
MSection:NewSlider(
    "Jump",
    "",
    700,
    50,
    function(s)
        game.Players.LocalPlayer.Character.Humanoid.JumpPower = s
    end
)
MSection:NewButton(
    "Inf jump",
    "",
    function()
        game:GetService("UserInputService").JumpRequest:connect(
            function()
                game:GetService("Players").LocalPlayer.Character:FindFirstChildOfClass("Humanoid"):ChangeState(
                    "Jumping"
                )
            end
        )
    end
)
MSection:NewButton(
    "Shield Aura",
    "",
    function(state)
        game:GetService("ReplicatedStorage").Events.ToggleBlocking:FireServer("true")
    end
)
MSection:NewButton(
    "Break Velocity",
    "",
    function()
        breakvelocity()
    end
)
MSection:NewButton(
    "Reset",
    "",
    function()
        player.Character:BreakJoints()
    end
)
TargetSection:NewButton(
    "Update Player List",
    "",
    function()
        spawn(
            function()
                GetList()
                slcplr:Refresh(dropdown)
            end
        )
    end
)
TargetSection:NewButton(
    "Teleport To Player",
    "",
    function()
        spawn(
            function()
                local p1 = game.Players.LocalPlayer.Character.HumanoidRootPart
                p1.CFrame = game.Players[_G.tplayer].Character.HumanoidRootPart.CFrame
                breakvelocity()
            end
        )
    end
)
TargetSection:NewToggle(
    "Loop TP to Player",
    "",
    function(state)
        if state then
            getgenv().loopgoto = true
            local varX = player.Character.HumanoidRootPart.Position["X"]
            local varY = player.Character.HumanoidRootPart.Position["Y"]
            local varZ = player.Character.HumanoidRootPart.Position["Z"]
            wait()
            local p1 = game.Players.LocalPlayer.Character.HumanoidRootPart
            local pos = p1.CFrame
            getgenv().breakv = true
            spawn(
                function()
                    while breakv do
                        wait(1)
                        breakvelocity()
                    end
                end
            )
            while loopgoto do
                task.wait()
                spawn(
                    function()
                        pcall(
                            function()
                                for i, v in pairs(game.Workspace:GetChildren()) do
                                    if
                                        ((v.Name == _G.tplayer) and v:FindFirstChild("Humanoid") and
                                            (v.Humanoid.Health > 0))
                                     then
                                        game:GetService("Players").LocalPlayer.Character.HumanoidRootPart.CFrame =
                                            v.HumanoidRootPart.CFrame * CFrame.new(0, 0, 3)
                                    end
                                end
                            end
                        )
                    end
                )
                spawn(
                    function()
                        if (loopgoto == false) then
                            game.Players.LocalPlayer.Character.HumanoidRootPart.CFrame = CFrame.new(varX, varY, varZ)
                        end
                    end
                )
            end
        else
            spawn(
                function()
                    getgenv().breakv = false
                    wait(0.2)
                    getgenv().loopgoto = false
                    wait(0.1)
                    getgenv().loopgoto = true
                    breakvelocity()
                end
            )
        end
    end
)
TargetSection:NewToggle(
    "Laser",
    "",
    function(state)
        spawn(
            function()
                if state then
                    getgenv().LaserL = true
                    wait()
                    coroutine.resume(
                        coroutine.create(
                            function()
                                local event = game:GetService("ReplicatedStorage").Events.ToggleLaserVision
                                local part = event:InvokeServer(true)
                                getgenv().LaserL = true
                                while LaserL and part and _G.tplayer do
                                    wait()
                                    local target = game.Players:FindFirstChild(_G.tplayer)
                                    if
                                        (target and target.Character and
                                            target.Character:FindFirstChild("HumanoidRootPart"))
                                     then
                                        part.Position = target.Character.HumanoidRootPart.Position
                                    end
                                end
                                event:InvokeServer(false)
                            end
                        )
                    )
                else
                    spawn(
                        function()
                            getgenv().LaserL = false
                        end
                    )
                end
            end
        )
    end
)
TargetSection:NewToggle(
    "Kill Player (Heavy)",
    "",
    function(state)
        if state then
            getgenv().killplr = true
            local varX = player.Character.HumanoidRootPart.Position["X"]
            local varY = player.Character.HumanoidRootPart.Position["Y"]
            local varZ = player.Character.HumanoidRootPart.Position["Z"]
            wait()
            local p1 = game.Players.LocalPlayer.Character.HumanoidRootPart
            local pos = p1.CFrame
            getgenv().breakv = true
            spawn(
                function()
                    while breakv do
                        breakvelocity()
                        game:GetService("ReplicatedStorage").Events.Transform:FireServer("metalSkin", true)
                        wait(1)
                    end
                end
            )
            spawn(
                function()
                    while killplr do
                        task.wait()
                        task.wait()
                        task.wait()
                        task.wait()
                        task.wait()
                        task.wait()
                        spawn(
                            function()
                                pcall(
                                    function()
                                        for i, v in pairs(game.Workspace:GetChildren()) do
                                            if
                                                ((v.Name == _G.tplayer) and v:FindFirstChild("Humanoid") and
                                                    (v.Humanoid.Health > 0))
                                             then
                                                game:GetService("Players").LocalPlayer.Character.HumanoidRootPart.CFrame =
                                                    v.HumanoidRootPart.CFrame * CFrame.new(0, 0, 1)
                                            end
                                        end
                                    end
                                )
                            end
                        )
                        spawn(
                            function()
                                game:GetService("ReplicatedStorage").Events.Punch:FireServer(0.4, 0.1, 1)
                                game:GetService("ReplicatedStorage").Events.Punch:FireServer(0.4, 0.1, 1)
                                game:GetService("ReplicatedStorage").Events.Punch:FireServer(0.4, 0.1, 1)
                                game:GetService("ReplicatedStorage").Events.Punch:FireServer(0.4, 0.1, 1)
                                game:GetService("ReplicatedStorage").Events.Punch:FireServer(0.4, 0.1, 1)
                            end
                        )
                        spawn(
                            function()
                                local LookVector = game.Workspace.Camera.CFrame.LookVector
                                game:GetService("ReplicatedStorage").Events.ToggleTelekinesis:InvokeServer(
                                    LookVector,
                                    true
                                )
                                game:GetService("ReplicatedStorage").Events.ToggleTelekinesis:InvokeServer(
                                    LookVector,
                                    false
                                )
                            end
                        )
                        spawn(
                            function()
                                if (killplr == false) then
                                    game.Players.LocalPlayer.Character.HumanoidRootPart.CFrame =
                                        CFrame.new(varX, varY, varZ)
                                end
                            end
                        )
                    end
                end
            )
        else
            spawn(
                function()
                    getgenv().breakv = false
                    wait(0.2)
                    getgenv().killplr = false
                    wait(0.1)
                    getgenv().killplr = true
                    breakvelocity()
                end
            )
        end
    end
)
KSection:NewKeybind(
    "MetalSkin",
    "",
    Enum.KeyCode["R"],
    function()
        if (_G.metalskin == false) then
            game:GetService("ReplicatedStorage").Events.Transform:FireServer("metalSkin", true)
            _G.metalskin = true
        else
            game:GetService("ReplicatedStorage").Events.Transform:FireServer("metalSkin", false)
            _G.metalskin = false
        end
    end
)
KSection:NewKeybind(
    "Tele-Off",
    "",
    Enum.KeyCode["C"],
    function()
        plrlist = {}
        Players = game:GetService("Players")
        for i, player in pairs(Players:GetPlayers()) do
            spawn(
                function()
                    game:GetService("ReplicatedStorage").Events.ToggleTelekinesis:InvokeServer(
                        Vector3.new(1, 1, 1),
                        false,
                        game.Players[player.Name].Character
                    )
                end
            )
        end
    end
)
KSection:NewKeybind(
    "Teleport To Motel",
    "",
    Enum.KeyCode.Z,
    function()
        if (_G.bring == true) then
            game:GetService("Workspace")[_G.teleportplayer].HumanoidRootPart.telekinesisPosition:Destroy()
            game:GetService("Workspace")[_G.teleportplayer].HumanoidRootPart.CFrame = CFrame.new(-1745, 95, -1530)
            wait(0.2)
            game:GetService("ReplicatedStorage").Events.ToggleTelekinesis:InvokeServer(
                Vector3.new(1, 1, 1),
                false,
                game.Players[_G.teleportplayer].Character
            )
        else
            game.Players.LocalPlayer.Character.HumanoidRootPart.CFrame = CFrame.new(-1745, 95, -1530)
        end
        breakvelocity()
    end
)
KSection:NewKeybind(
    "Teleport Middle",
    "",
    Enum.KeyCode.V,
    function()
        if (_G.bring == true) then
            game:GetService("Workspace")[_G.teleportplayer].HumanoidRootPart.telekinesisPosition:Destroy()
            game:GetService("Workspace")[_G.teleportplayer].HumanoidRootPart.CFrame = CFrame.new(-376, 94, 91)
            wait(0.2)
            game:GetService("ReplicatedStorage").Events.ToggleTelekinesis:InvokeServer(
                Vector3.new(1, 1, 1),
                false,
                game.Players[_G.teleportplayer].Character
            )
        else
            game.Players.LocalPlayer.Character.HumanoidRootPart.CFrame = CFrame.new(-376, 94, 91)
        end
        breakvelocity()
    end
)
KSection:NewKeybind(
    "Teleport To the Selected player",
    "",
    Enum.KeyCode.P,
    function()
        spawn(
            function()
                local targetPlayer = game.Players:FindFirstChild(_G.tplayer)
                if targetPlayer then
                    local p1 = game.Players.LocalPlayer.Character.HumanoidRootPart
                    local p2 = targetPlayer.Character and targetPlayer.Character:FindFirstChild("HumanoidRootPart")
                    if p1 and p2 then
                        p1.CFrame = p2.CFrame
                        game.Players.LocalPlayer.Character.Humanoid:ChangeState(11)
                    end
                end
            end
        )
    end
)
KSection:NewKeybind(
    "Hide UI",
    "",
    Enum.KeyCode.LeftShift,
    function()
        Library:ToggleUI()
    end
)

GSection:NewButton(
    "Infinite Yield",
    "",
    function()
        loadstring(game:HttpGet("https://raw.githubusercontent.com/EdgeIY/infiniteyield/master/source"))()
    end
)

GSection:NewButton(
    "Script Nebbia",
    "",
    function()
        loadstring(
            game:HttpGet(
                "https://raw.githubusercontent.com/DevMictlantecuhtli/Mictlantecuhtli-S-A-C-V/Aq/3D0604214CFA5FBDA726A8F9127596A47477C8D7F09407B42420595317705F8F.lua"
            )
        )()
    end
)

GSection:NewButton(
    "Cylindrical By Lechugafria",
    "",
    function()
        loadstring(
            game:HttpGet(
                "https://raw.githubusercontent.com/DevMictlantecuhtli/Mictlantecuhtli-S-A-C-V/Aq/ED85D6B053B72AD7DA385DA7B441280D2FC147FCC227B29B56DD1C4F52BDFEC1.lua"
            )
        )()
    end
)
local MainSection = Tab:NewSection("User: " .. game.Players.LocalPlayer.Name)
local TargetSection = TargetTab:NewSection("User: " .. game.Players.LocalPlayer.Name)
local SSection = STab:NewSection("User: " .. game.Players.LocalPlayer.Name)
local StatSection = StatTab:NewSection("User: " .. game.Players.LocalPlayer.Name)
local KSection = KTab:NewSection("User: " .. game.Players.LocalPlayer.Name)
local GSection = GTab:NewSection("User: " .. game.Players.LocalPlayer.Name)
-- |SCRIPT| °|TLALOC|° |By| |LECHUGAFRIA </>
