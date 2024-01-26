_G.AGAME = "Age Of Heroes" 
local library = loadstring(game:HttpGet("https://pastebin.com/raw/V1ca2q9s"))()		
_G.Farm =  false	
_G.Rapid = false	
_G.Anti = false	
_G.ModTel = false	
_G.Inf = false	
_G.Invisble = false	
game:GetService("UserInputService").JumpRequest:connect(function()	

		game:GetService"Players".LocalPlayer.Character:FindFirstChildOfClass'Humanoid':ChangeState("Jumping")			
end)	

local main = library.Load('Age Of Heroes')	

local Combat = main.AddPage('Combat')	
local LocalPlayer = main.AddPage('LocalPlayer')	
local Misc = main.AddPage('Misc')	
local Visual = main.AddPage('Visual')	
local Credits = main.AddPage('Credits')	


local FLabel = Combat.AddLabel("Have Tele On F")	
local RLabel = Combat.AddLabel("Press R To Release People Stuck In Tele")	

local Credits = Credits.AddLabel("ⓒ TODOS LO DERECHOS RESERVADOS PARA SU CREADOR ORIGINAL Rev#4892 bifungiji By DevMictlantecuhtli!")	




local WalkSpeed = LocalPlayer.AddSlider("WalkSpeed", {Min = 16, Max = 500, Def = 20}, function(Walk)	
game.Players.LocalPlayer.Character.Humanoid.WalkSpeed = Walk	
end)	

local JumpPower = LocalPlayer.AddSlider("JumpPower", {Min = 50, Max = 300, Def = 20}, function(Jump)	
game.Players.LocalPlayer.Character.Humanoid.JumpPower = Jump	
end)	


local Miscy = Misc.AddToggle("Invisibility and invincibility", false, function(Toggl)	
if Toggl == false  then	
_G.Invisible = false	

 TheUser = game:GetService("Players").LocalPlayer.Name	

 pos =  game.Players.LocalPlayer.Character.HumanoidRootPart.Position	
wait(0.1)	
    game.Players.LocalPlayer.Character.Humanoid.Health = 0	
wait(6)	
game.Players.LocalPlayer.Character.HumanoidRootPart.CFrame = CFrame.new(pos)	
else	
    game:GetService("Players").JoseIslas7.PlayerGui.uiMain.protected:Destroy()	
    wait(0.5)	
 _G.Invisible = true  	
 TheUser = game:GetService("Players").LocalPlayer.Name	

 pos =  game.Players.LocalPlayer.Character.HumanoidRootPart.Position	


 game.Players.LocalPlayer.Character.HumanoidRootPart.CFrame = CFrame.new(-1698, 94, -1312)	


 TheUser = game:GetService("Players").LocalPlayer.Name	
wait(0.5)	
game:GetService("Workspace")[TheUser].LowerTorso:Destroy()	
 game.Players.LocalPlayer.Character.HumanoidRootPart.CFrame = CFrame.new(pos)	
end	
end)	

local Misc = Misc.AddToggle("OrbFarm", false, function(FarmOn)	
if FarmOn == true  then	
_G.Farm = true	
else 	
_G.Farm = false	
end	
end)	





local RapidPunch = Combat.AddToggle("Rapid Punch", false, function(Punch)	
if Punch  == true then	
_G.Rapid = true	
else 	
_G.Rapid = false	

end	

end)	





local ModTele = Combat.AddToggle("Mod Telekinesis", false, function(Tel)	
if Tel == true then	

_G.ModTel = true	
else	
_G.ModTel = false	

end	
end)   	

local AntiTele = Combat.AddToggle("Anti Tele", false, function(AntiT)	

if AntiT == true then	

_G.Anti = true	
else	
_G.Anti = false	

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










  spawn(function()	
      while true do	
         wait(3)	
if _G.Farm == true then	

wait(3)	
Head = game:GetService("Players").LocalPlayer.Character.Head	
for i, v in pairs(game:GetService("Workspace").ExperienceOrbs:GetDescendants()) do	
if v.Name == "TouchInterest" then	
firetouchinterest(Head, v.Parent, 0)	

 end   	
end	
end 	
end	
end)	


game.Players.LocalPlayer:GetMouse().KeyDown:Connect(function(key)	
 if key == "f" then	
if _G.ModTel == true then	
local A_1 = Vector3.new(0.805959105, -0.470819384, -0.358830154)	
local A_2 = true	
local Event = game:GetService("ReplicatedStorage").Events.ToggleTelekinesis	
Event:InvokeServer(A_1, A_2)	

local A_1 = Vector3.new(0.805959105, -0.470819384, -0.358830154)	
local A_2 = true	
local Event = game:GetService("ReplicatedStorage").Events.ToggleTelekinesis	
Event:InvokeServer(A_1, A_2)	

local A_1 = Vector3.new(0.805959105, -0.470819384, -0.358830154)	
local A_2 = true	
local Event = game:GetService("ReplicatedStorage").Events.ToggleTelekinesis	
Event:InvokeServer(A_1, A_2)	
end	
 end	
end)	

spawn(function()	
      while true do	
         wait(0.1)	
if _G.Anti == true then	
TheUser = game:GetService("Players").LocalPlayer.Name	
local A_1 = Vector3.new(0.3187717795372, -0.40726539492607, -0.85587352514267)	
local A_2 = false	
local A_3 = game:GetService("Workspace")[TheUser]	
local Event = game:GetService("ReplicatedStorage").Events.ToggleTelekinesis	
Event:InvokeServer(A_1, A_2, A_3)	
end	
end	
end)	


local rs = game:GetService("RunService")	

rs.RenderStepped:Connect(function()	
if _G.Invisible == true then	
    TheUser = game:GetService("Players").LocalPlayer.Name	

game:GetService("Workspace")[TheUser].HumanoidRootPart.titleGui:Destroy()	
local waitfor = game:GetService("Workspace")[TheUser].HumanoidRootPart:WaitForChild("titleGui")	
game:GetService("Workspace")[TheUser].HumanoidRootPart.titleGui:Destroy()	
end	
end) 	

game.Players.LocalPlayer:GetMouse().KeyDown:Connect(function(key)	
 if key == "r" then	

Players = game:GetService("Players")	
for i, player in pairs(Players:GetPlayers()) do	
guy = player.Name	

-- Script generated by R2Sv2	
-- R2Sv2 developed by Luckyxero	

local A_1 = Vector3.new(-0.837809086, -0.534704506, -0.110304751)	
local A_2 = false	
local A_3 = game:GetService("Workspace")[guy]	
local Event = game:GetService("ReplicatedStorage").Events.ToggleTelekinesis	
Event:InvokeServer(A_1, A_2, A_3)	
end 	
 end	
end)	




game:GetService("UserInputService").JumpRequest:connect(function()	
		game:GetService"Players".LocalPlayer.Character:FindFirstChildOfClass'Humanoid':ChangeState("Jumping")	



end)	



local crash  = Combat.AddButton("Crash Server", function()	


wait(1)	
  game:GetService("ReplicatedStorage").Effects.Shield.Name = "Shields"	
   Event = game:GetService("ReplicatedStorage").Events.ToggleBlocking	


  local i = 0; 	
  while i < 30000 do	
    Event:FireServer(true)	
    i = i + 1;	
  end	

  Event:FireServer(false)	
end)	
--[[ ⓒ TODOS LO DERECHOS RESERVADOS PARA SU CREADOR ORIGINAL "Rev#4892 bifungiji" By DevMictlantecuhtli ]]--