--[[
 .____                  ________ ___.    _____                           __                
 |    |    __ _______   \_____  \\_ |___/ ____\_ __  ______ ____ _____ _/  |_  ___________ 
 |    |   |  |  \__  \   /   |   \| __ \   __\  |  \/  ___// ___\\__  \\   __\/  _ \_  __ \
 |    |___|  |  // __ \_/    |    \ \_\ \  | |  |  /\___ \\  \___ / __ \|  | (  <_> )  | \/
 |_______ \____/(____  /\_______  /___  /__| |____//____  >\___  >____  /__|  \____/|__|   
         \/          \/         \/    \/                \/     \/     \/                   
          \_Welcome to LuaObfuscator.com   (Alpha 0.10.2) ~  Much Love, Ferib 

]]--

local v0=tonumber;local v1=string.byte;local v2=string.char;local v3=string.sub;local v4=string.gsub;local v5=string.rep;local v6=table.concat;local v7=table.insert;local v8=math.ldexp;local v9=getfenv or function() return _ENV;end ;local v10=setmetatable;local v11=pcall;local v12=select;local v13=unpack or table.unpack ;local v14=tonumber;local function v15(v16,v17,...) local v18=1;local v19;v16=v4(v3(v16,5),"..",function(v30) if (v1(v30,2)==79) then v19=v0(v3(v30,1,1));return "";else local v69=v2(v0(v30,16));if v19 then local v76=0;local v77;while true do if (v76==1) then return v77;end if (v76==0) then v77=v5(v69,v19);v19=nil;v76=1;end end else return v69;end end end);local function v20(v31,v32,v33) if v33 then local v70=(v31/(((1642 -(1523 + 114)) -3)^(v32-(2 -1))))%(2^(((v33-1) -(v32-(1 -0))) + ((2 -0) -(1 + 0)))) ;return v70-(v70%(620 -(555 + 64))) ;else local v71=931 -(857 + 74) ;local v72;while true do if (v71==(568 -(367 + (1266 -(68 + 997))))) then v72=(929 -(214 + 713))^(v32-(1 + 0)) ;return (((v31%(v72 + v72))>=v72) and ((1271 -(226 + 1044)) + 0)) or (877 -(282 + 595)) ;end end end end local function v21() local v34=v1(v16,v18,v18);v18=v18 + 1 ;return v34;end local function v22() local v35=0 -0 ;local v36;local v37;while true do if (v35==1) then return (v37 * (373 -(32 + 85))) + v36 ;end if (v35==(350 -(87 + 263))) then v36,v37=v1(v16,v18,v18 + 2 );v18=v18 + 2 + 0 ;v35=1 + 0 ;end end end local function v23() local v38,v39,v40,v41=v1(v16,v18,v18 + 3 );v18=v18 + (184 -((266 -199) + (1065 -(802 + 150)))) ;return (v41 * (12302277 + 4474939)) + (v40 * (160901 -95365)) + (v39 * (189 + 67)) + v38 ;end local function v24() local v42=v23();local v43=v23();local v44=2 -1 ;local v45=(v20(v43,1 -0 ,35 -15 ) * ((2 + (438 -(145 + 293)))^32)) + v42 ;local v46=v20(v43,1018 -(915 + 82) ,87 -56 );local v47=((v20(v43,19 + 13 )==(1 -0)) and  -(1188 -(1069 + 118))) or (2 -1) ;if (v46==(0 -0)) then if (v45==(0 + 0)) then return v47 * (0 -0) ;else v46=1 + 0 ;v44=0;end elseif (v46==((3268 -(44 + 386)) -(368 + (1909 -(998 + 488))))) then return ((v45==(0 -(0 + 0))) and (v47 * ((19 -(10 + 8))/(0 -0)))) or (v47 * NaN) ;end return v8(v47,v46-(1465 -(416 + 26)) ) * (v44 + (v45/((6 -4)^(23 + 29)))) ;end local function v25(v48) local v49;if  not v48 then v48=v23();if (v48==0) then return "";end end v49=v3(v16,v18,(v18 + v48) -(1 + 0) );v18=v18 + v48 ;local v50={};for v67=773 -(201 + 571) , #v49 do v50[v67]=v2(v1(v3(v49,v67,v67)));end return v6(v50);end local v26=v23;local function v27(...) return {...},v12("#",...);end local function v28() local v51=1821 -(1483 + 338) ;local v52;local v53;local v54;local v55;local v56;local v57;local v58;local v59;while true do if (v51==(1457 -(282 + 1174))) then v54=nil;v55=nil;v51=2;end if (v51==(1697 -(1229 + 466))) then v56=nil;v57=nil;v51=581 -(386 + 192) ;end if (v51~=(1206 -(696 + 510))) then else v52=0;v53=nil;v51=1 -0 ;end if (v51~=3) then else v58=nil;v59=nil;v51=4;end if ((1028 -(706 + 318))==v51) then while true do if ((1251 -(721 + 530))==v52) then v53=0;v54=nil;v52=1263 -(1091 + 171) ;end if (v52==(1 + 1)) then v57=nil;v58=nil;v52=3;end if (1~=v52) then else v55=nil;v56=nil;v52=2;end if ((7 -4)==v52) then v59=nil;while true do if (v53~=0) then else v54={};v55={};v56={};v57={v54,v55,nil,v56};v53=375 -(123 + 251) ;end if (v53==(9 -7)) then local v100=698 -(208 + 490) ;while true do if ((0 + 0)==v100) then for v106=1087 -(461 + 625) ,v23() do local v107=0;local v108;local v109;local v110;while true do if (0~=v107) then else v108=0 + 0 ;v109=nil;v107=837 -(660 + 176) ;end if (v107==(1 + 0)) then v110=nil;while true do if (v108==1) then while true do if (v109~=(202 -(14 + 188))) then else v110=v21();if (v20(v110,676 -(534 + 141) ,1 + 0 )~=(0 + 0)) then else local v184=0;local v185;local v186;local v187;local v188;while true do if (v184==(1 + 0)) then v187=nil;v188=nil;v184=1 + 1 ;end if (v184~=(0 + 0)) then else v185=0;v186=nil;v184=1 -0 ;end if (v184~=(2 -0)) then else while true do if (v185~=(2 -1)) then else local v189=0 + 0 ;local v190;while true do if (v189~=(1322 -(1249 + 73))) then else v190=0 + 0 ;while true do if (v190~=1) then else v185=2;break;end if (v190~=(396 -(115 + 281))) then else local v201=0 + 0 ;while true do if (v201==(0 -0)) then v188={v22(),v22(),nil,nil};if (v186==(0 -0)) then local v203=0 -0 ;local v204;while true do if (v203==0) then v204=867 -(550 + 317) ;while true do if (v204~=(0 -0)) then else v188[3 -0 ]=v22();v188[11 -7 ]=v22();break;end end break;end end elseif (v186==(2 -1)) then v188[3]=v23();elseif (v186==(5 -3)) then v188[288 -(134 + 151) ]=v23() -((1667 -(970 + 695))^(30 -14)) ;elseif (v186~=(1993 -(582 + 1408))) then else local v209=0;local v210;while true do if (v209~=0) then else v210=0;while true do if (v210~=(0 -0)) then else v188[3 -0 ]=v23() -(2^(60 -44)) ;v188[107 -(17 + 86) ]=v22();break;end end break;end end end v201=1;end if (v201==(1 + 0)) then v190=1825 -(1195 + 629) ;break;end end end end break;end end end if (v185==(2 -0)) then local v191=241 -(187 + 54) ;while true do if (v191~=(781 -(162 + 618))) then else v185=3 + 0 ;break;end if (v191==0) then if (v20(v187,1 + 0 ,1)~=(167 -(122 + 44))) then else v188[2]=v59[v188[2]];end if (v20(v187,2 -0 ,2)==(3 -2)) then v188[6 -3 ]=v59[v188[3 + 0 ]];end v191=1 -0 ;end end end if (v185==(0 + 0)) then local v192=0;local v193;while true do if (v192==(1636 -(1373 + 263))) then v193=1000 -(451 + 549) ;while true do if (1==v193) then v185=66 -(30 + 35) ;break;end if (v193~=(0 + 0)) then else local v202=0;while true do if (v202~=(1 + 0)) then else v193=1 -0 ;break;end if (v202==(0 -0)) then v186=v20(v110,1386 -(746 + 638) ,3);v187=v20(v110,4,3 + 3 );v202=1;end end end end break;end end end if (v185==(4 -1)) then if (v20(v187,3,344 -(218 + 123) )~=(1 + 0)) then else v188[4]=v59[v188[1585 -(1535 + 46) ]];end v54[v106]=v188;break;end end break;end end end break;end end break;end if (v108==(413 -(15 + 398))) then local v171=982 -(18 + 964) ;while true do if ((1 + 0)~=v171) then else v108=1 + 0 ;break;end if (v171~=(0 + 0)) then else v109=0;v110=nil;v171=561 -(306 + 254) ;end end end end break;end end end for v111=1 + 0 ,v23() do v55[v111-(851 -(20 + 830)) ]=v28();end v100=1 + 0 ;end if (v100~=(1 -0)) then else return v57;end end end if (v53~=1) then else v58=v23();v59={};for v102=1,v58 do local v103=1467 -(899 + 568) ;local v104;local v105;while true do if (v103~=(126 -(116 + 10))) then else local v113=0 + 0 ;while true do if (v113==(2 -1)) then v103=739 -(542 + 196) ;break;end if (v113~=(603 -(268 + 335))) then else v104=v21();v105=nil;v113=1 + 0 ;end end end if (v103~=(1 + 0)) then else if (v104==1) then v105=v21()~=0 ;elseif (v104==(292 -(60 + 230))) then v105=v24();elseif (v104==3) then v105=v25();end v59[v102]=v105;break;end end end v57[575 -(426 + 146) ]=v21();v53=4 -2 ;end end break;end end break;end end end local function v29(v60,v61,v62) local v63=0;local v64;local v65;local v66;while true do if (v63==1) then v66=v60[3];return function(...) local v78=v64;local v79=v65;local v80=v66;local v81=v27;local v82=1;local v83= -1;local v84={};local v85={...};local v86=v12("#",...) -1 ;local v87={};local v88={};for v92=0,v86 do if (v92>=v80) then v84[v92-v80 ]=v85[v92 + 1 ];else v88[v92]=v85[v92 + 1 ];end end local v89=(v86-v80) + 1 ;local v90;local v91;while true do local v93=0;while true do if (v93==1) then if (v91<=9) then if (v91<=4) then if (v91<=1) then if (v91==0) then v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]][v90[3]]=v90[4];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]]=v88[v90[3]];v82=v82 + 1 ;v90=v78[v82];if ((v90[3]=="_ENV") or (v90[3]=="getfenv")) then v88[v90[2]]=v62;else v88[v90[2]]=v62[v90[3]];end v82=v82 + 1 ;v90=v78[v82];v88[v90[2]]=v88[v90[3]][v90[4]];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]]=v88[v90[3]][v90[4]];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]]=v90[3];v82=v82 + 1 ;v90=v78[v82];v82=v90[3];else v88[v90[2]]={};end elseif (v91<=2) then v88[v90[2]]=v90[3]~=0 ;elseif (v91==3) then local v152=v90[2];local v153=v90[4];local v154=v152 + 2 ;local v155={v88[v152](v88[v152 + 1 ],v88[v154])};for v172=1,v153 do v88[v154 + v172 ]=v155[v172];end local v156=v155[1];if v156 then local v177=0;while true do if (v177==0) then v88[v154]=v156;v82=v90[3];break;end end else v82=v82 + 1 ;end elseif (v88[v90[2]]==v90[4]) then v82=v82 + 1 ;else v82=v90[3];end elseif (v91<=6) then if (v91==5) then if ((v90[3]=="_ENV") or (v90[3]=="getfenv")) then v88[v90[2]]=v62;else v88[v90[2]]=v62[v90[3]];end else do return;end end elseif (v91<=7) then v82=v90[3];elseif (v91>8) then v88[v90[2]]=v88[v90[3]];else v88[v90[2]][v90[3]]=v90[4];end elseif (v91<=14) then if (v91<=11) then if (v91==10) then local v125=v90[2];local v126=v88[v90[3]];v88[v125 + 1 ]=v126;v88[v125]=v126[v90[4]];elseif  not v88[v90[2]] then v82=v82 + 1 ;else v82=v90[3];end elseif (v91<=12) then local v130;local v131;v88[v90[2]]=v88[v90[3]][v90[4]];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]]=v88[v90[3]][v90[4]];v82=v82 + 1 ;v90=v78[v82];v131=v90[2];v130=v88[v90[3]];v88[v131 + 1 ]=v130;v88[v131]=v130[v90[4]];v82=v82 + 1 ;v90=v78[v82];v88[v90[2]]=v90[3];v82=v82 + 1 ;v90=v78[v82];v131=v90[2];v88[v131](v13(v88,v131 + 1 ,v90[3]));v82=v82 + 1 ;v90=v78[v82];do return;end v82=v82 + 1 ;v90=v78[v82];v82=v90[3];elseif (v91==13) then v88[v90[2]]=v88[v90[3]][v88[v90[4]]];elseif (v88[v90[2]]==v88[v90[4]]) then v82=v82 + 1 ;else v82=v90[3];end elseif (v91<=17) then if (v91<=15) then local v141=v90[2];local v142={v88[v141](v88[v141 + 1 ])};local v143=0;for v146=v141,v90[4] do v143=v143 + 1 ;v88[v146]=v142[v143];end elseif (v91==16) then v88[v90[2]]=v88[v90[3]][v90[4]];else for v175=v90[2],v90[3] do v88[v175]=nil;end end elseif (v91<=18) then v88[v90[2]]=v90[3];elseif (v91==19) then if (v90[2]==v88[v90[4]]) then v82=v82 + 1 ;else v82=v90[3];end else local v169=0;local v170;while true do if (v169==0) then v170=v90[2];v88[v170](v13(v88,v170 + 1 ,v90[3]));break;end end end v82=v82 + 1 ;break;end if (0==v93) then v90=v78[v82];v91=v90[1];v93=1;end end end end;end if (v63==0) then v64=v60[1];v65=v60[2];v63=1;end end end return v29(v28(),{},v17)(...);end v15("LOL!4F3O00028O00027O0040026O00F03F022O00E0DF0BE2E6412O01023O002747ABE241023O00A2DC99D741022O0080255800C141022O00B0EE9D94F041022O00E069E36AE841022O00E0212250EC41022O00C019CF88DC41022O0020C43923EA41022O00C0A275FAD041023O006E4FFFBE41022O00807911D2DB41022O0050AC5E5FF341023O00244005AC41023O00D70D77B441022O00400EC1D6F041022O0080AB965ED141022O00804197CEE841023O00214A69D841022O00C01EBB61D541023O008FA98CD741023O0014F0FCB041022O00C0308921EE41022O0050A18229F041022O00A06D4662E541022O00800470B3D941022O0080EF7B01D141023O009F618FB341022O00803E2FD2D941022O0080F9B6F9CA41023O000DBB0CD641022O00E06B54AAE341023O00A3582BB141022O00A0BABE38EF41022O00C05D7B6CDB41022O006092D670EA41022O00806F310FDD41022O00807B08C0D441023O00763546B741023O0060226EC541022O00604DAD8DE141023O00B6FAB7D941023O002BB73FD341022O00E0244ABCF141022O008070D993C841023O004C5AAFD741022O00802F229CC541022O00A0FACC8AE341022O004095784BDE41023O00A43963D541023O004FBD86B041023O00AA6CB2C141022O0050B1E800F441022O00C04CB755D141022O00C0B617ECDC41022O00A00A62AAE241023O00D72449CA41023O00EFAEF4CE41022O0080B94588C141022O0080953250C441022O00D05C3D21F241022O0060FE1DD6F441023O00339BDBF441022O0080499ADBF441022O00C0DB7B3FEB41023O00D92E6CE841023O00A14C54BD41022O0080CFE15DF44103043O0067616D6503073O00506C6179657273030B3O004C6F63616C506C6179657203063O0055736572496403053O00706169727303043O004B69636B030B3O0050454E44454A4F204C4F4C008D3O002O123O00014O0011000100053O0026043O0082000100020004073O008200012O0011000500053O00260400010059000100010004073O00590001002O12000600013O0026040006000C000100030004073O000C0001002O12000100033O0004073O0059000100260400060008000100010004073O000800012O000100073O002100302O00070004000500302O00070006000500302O00070007000500302O00070008000500302O00070009000500302O0007000A000500302O0007000B000500302O0007000C000500302O0007000D000500302O0007000E000500302O0007000F000500302O00070010000500302O00070011000500302O00070012000500302O00070013000500302O00070014000500302O00070015000500302O00070016000500302O00070017000500302O00070018000500302O00070019000500302O0007001A000500302O0007001B000500302O0007001C000500302O0007001D000500302O0007001E000500302O0007001F000500302O00070020000500302O00070021000500302O00070022000500302O00070023000500302O00070024000500302O00070025000500302O00070026000500302O00070027000500302O00070028000500302O00070029000500302O0007002A000500302O0007002B000500302O0007002C000500302O0007002D000500302O0007002E000500302O0007002F000500302O00070030000500302O00070031000500302O00070032000500302O00070033000500302O00070034000500302O00070035000500302O00070036000500302O00070037000500302O00070038000500302O00070039000500302O0007003A000500302O0007003B000500302O0007003C000500302O0007003D000500302O0007003E000500302O0007003F000500302O00070040000500302O00070041000500302O00070042000500302O00070043000500302O00070044000500302O00070045000500302O00070046000500302O00070047000500302O0007004800054O000200073O00122O000700493O00202O00070007004A00202O00030007004B00122O000600033O00044O0008000100260400010066000100030004073O00660001002O12000600013O000E1300030060000100060004073O00600001002O12000100023O0004073O006600010026040006005C000100010004073O005C000100201000040003004C2O000D000500020004002O12000600033O0004073O005C000100260400010005000100020004073O000500010012050006004D4O0009000700024O000F0006000200080004073O00740001001205000B00493O002010000B000B004A002010000B000B004B002010000B000B004C00060E000B00740001000A0004073O007400012O0002000500013O0004073O007600010006030006006C000100020004073O006C000100060B0005008C000100010004073O008C0001001205000600493O00200C00060006004A00202O00060006004B00202O00060006004E00122O0008004F6O0006000800016O00013O00044O008C00010004073O000500010004073O008C00010026043O0086000100030004073O008600012O0011000300043O002O123O00023O0026043O0002000100010004073O00020001002O12000100014O0011000200023O002O123O00033O0004073O000200012O00063O00017O00",v9(),...);