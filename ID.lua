--[[
 .____                  ________ ___.    _____                           __                
 |    |    __ _______   \_____  \\_ |___/ ____\_ __  ______ ____ _____ _/  |_  ___________ 
 |    |   |  |  \__  \   /   |   \| __ \   __\  |  \/  ___// ___\\__  \\   __\/  _ \_  __ \
 |    |___|  |  // __ \_/    |    \ \_\ \  | |  |  /\___ \\  \___ / __ \|  | (  <_> )  | \/
 |_______ \____/(____  /\_______  /___  /__| |____//____  >\___  >____  /__|  \____/|__|   
         \/          \/         \/    \/                \/     \/     \/                   
          \_Welcome to LuaObfuscator.com   (Alpha 0.9.19) ~  Much Love, Ferib 

]]--

local v0=tonumber;local v1=string.byte;local v2=string.char;local v3=string.sub;local v4=string.gsub;local v5=string.rep;local v6=table.concat;local v7=table.insert;local v8=math.ldexp;local v9=getfenv or function()return _ENV;end ;local v10=setmetatable;local v11=pcall;local v12=select;local v13=unpack or table.unpack ;local v14=tonumber;local function v15(v16,v17,...)local v18=1;local v19;v16=v4(v3(v16,5),"..",function(v30)if (v1(v30,2)==79) then local v80=0;while true do if (v80==0) then v19=v0(v3(v30,1,1));return "";end end else local v81=v2(v0(v30,16));if v19 then local v88=0;local v89;while true do if (v88==1) then return v89;end if (v88==0) then v89=v5(v81,v19);v19=nil;v88=1;end end else return v81;end end end);local function v20(v31,v32,v33)if v33 then local v82=(v31/((1 + 1)^(v32-(2 -(4 -3)))))%((879 -(282 + 595))^(((v33-(2 -1)) -(v32-(1 -0))) + (2 -(118 -(32 + 85))))) ;return v82-(v82%1) ;else local v83=619 -(555 + 64) ;local v84;while true do if (v83==(931 -(857 + 74))) then v84=((559 + 11) -(367 + 201))^(v32-1) ;return (((v31%(v84 + v84))>=v84) and (928 -(214 + 713))) or (1270 -(226 + 1044)) ;end end end end local function v21()local v34=v1(v16,v18,v18);v18=v18 + 1 ;return v34;end local function v22()local v35,v36=v1(v16,v18,v18 + 2 );v18=v18 + 1 + 1 ;return (v36 * (1213 -(892 + 65))) + v35 ;end local function v23()local v37,v38,v39,v40=v1(v16,v18,v18 + (183 -(67 + 113)) );v18=v18 + (9 -5) ;return (v40 * (31011612 -14234396)) + (v39 * (120312 -54776)) + (v38 * (606 -(87 + 193 + 70))) + v37 ;end local function v24()local v41=v23();local v42=v23();local v43=2 -1 ;local v44=(v20(v42,1 + 0 ,20) * ((7 -5)^((3785 -2801) -(802 + 150)))) + v41 ;local v45=v20(v42,(498 -(416 + 26)) -35 ,31);local v46=((v20(v42,57 -25 )==(1 + 0)) and  -1) or ((3186 -2188) -(915 + 82)) ;if (v45==0) then if (v44==(0 -0)) then return v46 * (0 + 0 + 0) ;else local v90=0 -0 ;while true do if (v90==(1187 -(1069 + (208 -90)))) then v45=(440 -(145 + 293)) -1 ;v43=0 -0 ;break;end end end elseif (v45==(356 + 1691)) then return ((v44==((430 -(44 + 386)) -0)) and (v46 * (1/(0 + 0)))) or (v46 * NaN) ;end return v8(v46,v45-(1814 -(368 + 423)) ) * (v43 + (v44/(((1492 -(998 + 488)) -4)^(70 -(10 + 8))))) ;end local function v25(v47)local v48=0 + 0 ;local v49;local v50;while true do if (v48==0) then v49=nil;if  not v47 then v47=v23();if (v47==(0 + 0)) then return "";end end v48=(2744 -1971) -(201 + 571) ;end if (v48==3) then return v6(v50);end if (v48==(1140 -(116 + 1022))) then v50={};for v91=4 -3 , #v49 do v50[v91]=v2(v1(v3(v49,v91,v91)));end v48=2 + 1 ;end if (v48==((862 -(814 + 45)) -2)) then v49=v3(v16,v18,(v18 + v47) -1 );v18=v18 + v47 ;v48=2;end end end local v26=v23;local function v27(...)return {...},v12("#",...);end local function v28()local v51=0 -0 ;local v52;local v53;local v54;local v55;local v56;local v57;local v58;local v59;while true do if (v51==(2 + 1)) then v58=nil;v59=nil;v51=4;end if (v51~=4) then else while true do if (v52==(1 + 1)) then v57=nil;v58=nil;v52=3;end if (v52==1) then local v97=0 + 0 ;while true do if (v97==0) then v55=nil;v56=nil;v97=1 + 0 ;end if (v97==1) then v52=28 -(11 + 15) ;break;end end end if (v52==(197 -(26 + 168))) then v59=nil;while true do local v99=0 -0 ;while true do if (v99==0) then if (v53~=(881 -(284 + 594))) then else local v100=0 -0 ;while true do if (v100~=0) then else local v180=0;while true do if (v180~=0) then else for v210=1,v23() do v55[v210-(2 -1) ]=v28();end return v57;end end end end end if (v53==(166 -(122 + 44))) then local v101=0 -0 ;while true do if (v101~=(0 -0)) then else v54={};v55={};v101=1 + 0 ;end if (v101==(1 + 0)) then v56={};v53=1;break;end end end v99=1;end if (v99==1) then if (v53==2) then local v102=0 -0 ;while true do if (v102~=(66 -(30 + 35))) then else for v194=1 + 0 ,v23() do local v195=1257 -(1043 + 214) ;local v196;local v197;while true do if ((3 -2)==v195) then while true do if (v196~=0) then else v197=v21();if (v20(v197,1213 -(323 + 889) ,1)==(0 -0)) then local v213=580 -(361 + 219) ;local v214;local v215;local v216;local v217;local v218;local v219;while true do if ((320 -(53 + 267))==v213) then v214=0;v215=nil;v213=1 + 0 ;end if (2~=v213) then else v218=nil;v219=nil;v213=416 -(15 + 398) ;end if (v213~=(985 -(18 + 964))) then else while true do if (v214==(3 -2)) then v217=nil;v218=nil;v214=2;end if (v214~=(2 + 0)) then else v219=nil;while true do if (v215==1) then local v226=0 + 0 ;while true do if (1==v226) then v215=2;break;end if (v226~=(850 -(20 + 830))) then else v218=nil;v219=nil;v226=1 + 0 ;end end end if (v215~=(128 -(116 + 10))) then else while true do if (v216==3) then if (v20(v218,3,3)==(1 + 0)) then v219[4]=v59[v219[4]];end v54[v194]=v219;break;end if ((739 -(542 + 196))==v216) then local v229=0;local v230;while true do if (0==v229) then v230=0;while true do if (v230==0) then local v238=0 -0 ;local v239;while true do if (0==v238) then v239=0 + 0 ;while true do if (v239==0) then local v247=0 + 0 ;while true do if (v247~=(0 + 0)) then else v219={v22(),v22(),nil,nil};if (v217==(0 -0)) then local v249=0;local v250;local v251;while true do if ((1121 -(118 + 1003))==v249) then v250=0 -0 ;v251=nil;v249=378 -(142 + 235) ;end if (v249~=1) then else while true do if (v250==0) then v251=0 -0 ;while true do if (v251==0) then v219[1 + 2 ]=v22();v219[4]=v22();break;end end break;end end break;end end elseif (v217==(978 -(553 + 424))) then v219[3]=v23();elseif (v217==(3 -1)) then v219[3]=v23() -(2^16) ;elseif (v217==3) then local v254=0;local v255;local v256;while true do if (v254~=1) then else while true do if (v255==0) then v256=0 + 0 ;while true do if (0==v256) then v219[3]=v23() -(2^16) ;v219[4 + 0 ]=v22();break;end end break;end end break;end if (v254==(0 + 0)) then local v259=0;while true do if (v259~=1) then else v254=1 + 0 ;break;end if (v259==(0 + 0)) then v255=0 -0 ;v256=nil;v259=2 -1 ;end end end end end v247=2 -1 ;end if ((1 + 0)==v247) then v239=1;break;end end end if (v239==(4 -3)) then v230=754 -(239 + 514) ;break;end end break;end end end if (v230~=(1 + 0)) then else v216=2;break;end end break;end end end if (v216==0) then local v231=0;local v232;while true do if (v231~=(1329 -(797 + 532))) then else v232=0;while true do if ((0 + 0)==v232) then local v240=0 + 0 ;local v241;while true do if (v240==(0 -0)) then v241=1202 -(373 + 829) ;while true do if (v241~=(731 -(476 + 255))) then else local v248=1130 -(369 + 761) ;while true do if (v248==1) then v241=1 + 0 ;break;end if (v248==(0 -0)) then v217=v20(v197,3 -1 ,3);v218=v20(v197,242 -(64 + 174) ,6);v248=1 + 0 ;end end end if (v241==(1 -0)) then v232=1;break;end end break;end end end if (v232~=1) then else v216=337 -(144 + 192) ;break;end end break;end end end if (v216==(218 -(42 + 174))) then local v233=0 + 0 ;while true do if (v233==0) then local v237=0 + 0 ;while true do if (v237~=(0 + 0)) then else local v242=1504 -(363 + 1141) ;while true do if (v242~=1) then else v237=1581 -(1183 + 397) ;break;end if (v242==(0 -0)) then if (v20(v218,1,1 + 0 )==1) then v219[2]=v59[v219[2 + 0 ]];end if (v20(v218,2,2)==1) then v219[3]=v59[v219[3]];end v242=1976 -(1913 + 62) ;end end end if (v237~=1) then else v233=1;break;end end end if (v233==(1 + 0)) then v216=7 -4 ;break;end end end end break;end if (0~=v215) then else v216=0;v217=nil;v215=1;end end break;end if (v214==(1933 -(565 + 1368))) then local v225=0;while true do if (v225==1) then v214=1;break;end if (v225==(0 -0)) then v215=0;v216=nil;v225=1;end end end end break;end if (v213==(1662 -(1477 + 184))) then v216=nil;v217=nil;v213=2;end end end break;end end break;end if (v195==0) then v196=0;v197=nil;v195=1;end end end v53=3 -0 ;break;end if (v102==(0 + 0)) then for v198=857 -(564 + 292) ,v58 do local v199=0 -0 ;local v200;local v201;local v202;local v203;while true do if (v199==(0 -0)) then v200=304 -(244 + 60) ;v201=nil;v199=1 + 0 ;end if (v199==1) then v202=nil;v203=nil;v199=478 -(41 + 435) ;end if ((1003 -(938 + 63))==v199) then while true do if (v200==0) then local v212=0;while true do if (v212==(1 + 0)) then v200=1126 -(936 + 189) ;break;end if ((0 + 0)==v212) then local v220=1613 -(1565 + 48) ;while true do if (v220==0) then v201=0;v202=nil;v220=1 + 0 ;end if (v220~=(1139 -(782 + 356))) then else v212=268 -(176 + 91) ;break;end end end end end if (v200~=(2 -1)) then else v203=nil;while true do if (v201==0) then local v221=0 -0 ;local v222;local v223;while true do if (v221~=(1092 -(975 + 117))) then else v222=0;v223=nil;v221=1876 -(157 + 1718) ;end if (v221==1) then while true do if (0==v222) then v223=0 + 0 ;while true do if (v223==(0 -0)) then local v227=0;while true do if (v227==(0 -0)) then local v234=0;while true do if (v234==(1018 -(697 + 321))) then v202=v21();v203=nil;v234=2 -1 ;end if (v234~=(1 -0)) then else v227=1;break;end end end if ((2 -1)==v227) then v223=1;break;end end end if (1==v223) then v201=1;break;end end break;end end break;end end end if (v201~=(1 + 0)) then else if (v202==1) then v203=v21()~=(0 -0) ;elseif (v202==(5 -3)) then v203=v24();elseif (v202~=(1230 -(322 + 905))) then else v203=v25();end v59[v198]=v203;break;end end break;end end break;end end end v57[3]=v21();v102=1;end end end if (v53==1) then v57={v54,v55,nil,v56};v58=v23();v59={};v53=2;end break;end end end break;end if (v52~=0) then else local v98=1189 -(449 + 740) ;while true do if (v98~=(872 -(826 + 46))) then else v53=947 -(245 + 702) ;v54=nil;v98=1;end if (v98==(3 -2)) then v52=1;break;end end end end break;end if (v51~=(0 + 0)) then else v52=0;v53=nil;v51=1;end if (v51~=1) then else v54=nil;v55=nil;v51=1900 -(260 + 1638) ;end if ((442 -(382 + 58))==v51) then v56=nil;v57=nil;v51=3;end end end local function v29(v60,v61,v62)local v63=v60[1];local v64=v60[2];local v65=v60[3];return function(...)local v66=v63;local v67=v64;local v68=v65;local v69=v27;local v70=1;local v71= -1;local v72={};local v73={...};local v74=v12("#",...) -1 ;local v75={};local v76={};for v85=0,v74 do if (v85>=v68) then v72[v85-v68 ]=v73[v85 + 1 ];else v76[v85]=v73[v85 + 1 ];end end local v77=(v74-v68) + 1 ;local v78;local v79;while true do v78=v66[v70];v79=v78[1];if (v79<=18) then if (v79<=8) then if (v79<=3) then if (v79<=1) then if (v79==0) then if ((v78[3]=="_ENV") or (v78[3]=="getfenv")) then v76[v78[2]]=v62;else v76[v78[2]]=v62[v78[3]];end elseif (v78[2]==v76[v78[4]]) then v70=v70 + 1 ;else v70=v78[3];end elseif (v79>2) then v76[v78[2]]=v78[3]~=0 ;else v76[v78[2]]=v76[v78[3]][v76[v78[4]]];end elseif (v79<=5) then if (v79==4) then v76[v78[2]]={};else local v107=0;local v108;while true do if (0==v107) then v108=v78[2];v76[v108](v13(v76,v108 + 1 ,v78[3]));break;end end end elseif (v79<=6) then local v109=v78[2];local v110=v78[4];local v111=v109 + 2 ;local v112={v76[v109](v76[v109 + 1 ],v76[v111])};for v140=1,v110 do v76[v111 + v140 ]=v112[v140];end local v113=v112[1];if v113 then v76[v111]=v113;v70=v78[3];else v70=v70 + 1 ;end elseif (v79>7) then local v155=v78[2];local v156=v76[v78[3]];v76[v155 + 1 ]=v156;v76[v155]=v156[v78[4]];else do return;end end elseif (v79<=13) then if (v79<=10) then if (v79>9) then v76[v78[2]]=v76[v78[3]][v78[4]];else v70=v78[3];end elseif (v79<=11) then v76[v78[2]]=v76[v78[3]][v78[4]];elseif (v79>12) then v70=v78[3];elseif  not v76[v78[2]] then v70=v70 + 1 ;else v70=v78[3];end elseif (v79<=15) then if (v79==14) then v76[v78[2]]=v76[v78[3]];else v76[v78[2]]=v76[v78[3]][v76[v78[4]]];end elseif (v79<=16) then if (v76[v78[2]]==v76[v78[4]]) then v70=v70 + 1 ;else v70=v78[3];end elseif (v79==17) then for v183=v78[2],v78[3] do v76[v183]=nil;end else v76[v78[2]]=v78[3];end elseif (v79<=27) then if (v79<=22) then if (v79<=20) then if (v79==19) then if (v78[2]==v76[v78[4]]) then v70=v70 + 1 ;else v70=v78[3];end else local v123=0;local v124;local v125;while true do if (v123==0) then v124=v78[2];v125=v76[v78[3]];v123=1;end if (v123==1) then v76[v124 + 1 ]=v125;v76[v124]=v125[v78[4]];break;end end end elseif (v79>21) then v76[v78[2]]=v76[v78[3]];else v76[v78[2]]=v78[3];end elseif (v79<=24) then if (v79==23) then if ((v78[3]=="_ENV") or (v78[3]=="getfenv")) then v76[v78[2]]=v62;else v76[v78[2]]=v62[v78[3]];end else v76[v78[2]]=v78[3]~=0 ;end elseif (v79<=25) then if (v76[v78[2]]==v78[4]) then v70=v70 + 1 ;else v70=v78[3];end elseif (v79==26) then if  not v76[v78[2]] then v70=v70 + 1 ;else v70=v78[3];end else v76[v78[2]][v78[3]]=v78[4];end elseif (v79<=32) then if (v79<=29) then if (v79>28) then local v131=v78[2];local v132=v78[4];local v133=v131 + 2 ;local v134={v76[v131](v76[v131 + 1 ],v76[v133])};for v143=1,v132 do v76[v133 + v143 ]=v134[v143];end local v135=v134[1];if v135 then local v171=0;while true do if (v171==0) then v76[v133]=v135;v70=v78[3];break;end end else v70=v70 + 1 ;end else do return;end end elseif (v79<=30) then local v136=v78[2];local v137={v76[v136](v76[v136 + 1 ])};local v138=0;for v146=v136,v78[4] do v138=v138 + 1 ;v76[v146]=v137[v138];end elseif (v79>31) then v76[v78[2]]={};else local v173=v78[2];local v174={v76[v173](v76[v173 + 1 ])};local v175=0;for v190=v173,v78[4] do local v191=0;while true do if (v191==0) then v175=v175 + 1 ;v76[v190]=v174[v175];break;end end end end elseif (v79<=34) then if (v79>33) then if (v76[v78[2]]==v76[v78[4]]) then v70=v70 + 1 ;else v70=v78[3];end else local v139=v78[2];v76[v139](v13(v76,v139 + 1 ,v78[3]));end elseif (v79<=35) then if (v76[v78[2]]==v78[4]) then v70=v70 + 1 ;else v70=v78[3];end elseif (v79==36) then for v192=v78[2],v78[3] do v76[v192]=nil;end else v76[v78[2]][v78[3]]=v78[4];end v70=v70 + 1 ;end end;end return v29(v28(),{},v17)(...);end v15("LOL!3F3O00028O00027O004003053O00706169727303043O0067616D6503073O00506C6179657273030B3O004C6F63616C506C6179657203063O0055736572496403043O004B69636B030B3O0050454E44454A4F204C4F4C026O00F03F022O00E0DF0BE2E6412O01023O002747ABE241023O00A2DC99D741022O0080255800C141022O00B0EE9D94F041022O00E069E36AE841022O00E0212250EC41022O00C019CF88DC41022O0020C43923EA41022O00C0A275FAD041023O006E4FFFBE41022O00807911D2DB41022O0050AC5E5FF341023O00244005AC41023O00D70D77B441022O00400EC1D6F041022O0080AB965ED141022O00E045061FE541022O00804197CEE841023O00214A69D841022O00C01EBB61D541023O008FA98CD741023O0014F0FCB041022O00C0308921EE41022O0050A18229F041022O00A06D4662E541022O00800470B3D941022O0080EF7B01D141023O009F618FB341022O00803E2FD2D941022O0080F9B6F9CA41023O000DBB0CD641022O00E06B54AAE341023O00A3582BB141022O00A0BABE38EF41022O00C05D7B6CDB41022O006092D670EA41022O00806F310FDD41022O00807B08C0D441023O00763546B741023O0060226EC541022O00604DAD8DE141023O00B6FAB7D941023O002BB73FD341022O00E0244ABCF141022O008070D993C841023O004C5AAFD741022O00802F229CC541022O00A0FACC8AE341022O004095784BDE41023O00A43963D541023O004FBD86B04100693O0012153O00014O0024000100043O0026193O00260001000200040D3O0026000100122O000500034O0016000600014O001E00050002000700040D3O0010000100122O000A00043O00200B000A000A000500200B000A000A000600200B000A000A0007000610000A00100001000900040D3O001000012O0018000400013O00040D3O0012000100061D000500080001000200040D3O0008000100061A000400680001000100040D3O00680001001215000500014O0024000600063O000E01000100160001000500040D3O00160001001215000600013O002619000600190001000100040D3O0019000100122O000700043O00200B00070007000500200B000700070006002014000700070008001215000900094O00210007000900012O001C3O00013O00040D3O0019000100040D3O0068000100040D3O0016000100040D3O006800010026193O002B0001000A00040D3O002B000100200B0003000200072O000F0004000100030012153O00023O0026193O00020001000100040D3O000200012O000400053O001D00301B0005000B000C00301B0005000D000C00301B0005000E000C00301B0005000F000C00301B00050010000C00301B00050011000C00301B00050012000C00301B00050013000C00301B00050014000C00301B00050015000C00301B00050016000C00301B00050017000C00301B00050018000C00301B00050019000C00301B0005001A000C00301B0005001B000C00301B0005001C000C00301B0005001D000C00301B0005001E000C00301B0005001F000C00301B00050020000C00301B00050021000C00301B00050022000C00301B00050023000C00301B00050024000C00301B00050025000C00301B00050026000C00301B00050027000C00301B00050028000C00301B00050029000C00301B0005002A000C00301B0005002B000C00301B0005002C000C00301B0005002D000C00301B0005002E000C00301B0005002F000C00301B00050030000C00301B00050031000C00301B00050032000C00301B00050033000C00301B00050034000C00301B00050035000C00301B00050036000C00301B00050037000C00301B00050038000C00301B00050039000C00301B0005003A000C00301B0005003B000C00301B0005003C000C00301B0005003D000C00301B0005003E000C00301B0005003F000C2O0016000100053O00122O000500043O00200B00050005000500200B0002000500060012153O000A3O00040D3O000200012O001C3O00017O00",v9(),...);