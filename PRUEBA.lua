local Library = loadstring(game:HttpGet("https://raw.githubusercontent.com/GhostDuckyy/Ui-Librarys/main/Gerad's/source.lua"))()
_G.Farm =  false
_G.Rapid = false
_G.Anti = false
_G.ModTel = false
_G.Inf = false
_G.Invisble = false
game:GetService("UserInputService").JumpRequest:connect(function()
    
    game:GetService"Players".LocalPlayer.Character:FindFirstChildOfClass'Humanoid':ChangeState("Jumping")		
end)
local Window = Library:CreateWindow('PRUEBA') -- :CreateWindow(Title)

local Section = Window:Section('123') -- :Section(Title)

-- Label
Section:Label('Little Sunshine') -- :Label(Text)

-- Button
Section:Button('LOL', function() -- :Button(Title, callback)
    print('Clicked Button')
end)

-- Toggle
-- Agregar un toggle a la sección
local Toggle = Section:Toggle('Rapid Punch', {flag = 'Toggle'}, function(value)
    if value then
        print('True')
        _G.Rapid = true
    else
        print('False')
        _G.Rapid = false
    end
end)
local mouse = game:GetService("Players").LocalPlayer:GetMouse()

mouse.Button1Down:Connect(function()
if _G.Rapid == true then
local A_1 = 0.4
local A_2 = 0.1
local A_3 = 1
local Event = game:GetService("ReplicatedStorage").Events.Punch
Event:FireServer(A_1, A_2, A_3)

local A_1 = 0.4
local A_2 = 0.1
local A_3 = 1
local Event = game:GetService("ReplicatedStorage").Events.Punch
Event:FireServer(A_1, A_2, A_3)

local A_1 = 0.4
local A_2 = 0.1
local A_3 = 1
local Event = game:GetService("ReplicatedStorage").Events.Punch
Event:FireServer(A_1, A_2, A_3)

local A_1 = 0.4
local A_2 = 0.1
local A_3 = 1
local Event = game:GetService("ReplicatedStorage").Events.Punch
Event:FireServer(A_1, A_2, A_3)

local A_1 = 0.4
local A_2 = 0.1
local A_3 = 1
local Event = game:GetService("ReplicatedStorage").Events.Punch
Event:FireServer(A_1, A_2, A_3)

local A_1 = 0.4
local A_2 = 0.1
local A_3 = 1
local Event = game:GetService("ReplicatedStorage").Events.Punch
Event:FireServer(A_1, A_2, A_3)

local A_1 = 0.4
local A_2 = 0.1
local A_3 = 1
local Event = game:GetService("ReplicatedStorage").Events.Punch
Event:FireServer(A_1, A_2, A_3)

local A_1 = 0.4
local A_2 = 0.1
local A_3 = 1
local Event = game:GetService("ReplicatedStorage").Events.Punch
Event:FireServer(A_1, A_2, A_3)

local A_1 = 0.4
local A_2 = 0.1
local A_3 = 1
local Event = game:GetService("ReplicatedStorage").Events.Punch
Event:FireServer(A_1, A_2, A_3)
end
end)







-- Print status
Section:Button('Status', function()
    print('Toggle - ',Library.flags.Toggle)
    print('Slider - ',Library.flags.Slider)
    print('TxtBox - ',Library.flags.Box)
    print('Dropdown - ',Library.flags.DROP)
    print('Bind - ',Library.flags.BIND)
    print('ColorPicker - ',Library.flags.PICKER)
end)