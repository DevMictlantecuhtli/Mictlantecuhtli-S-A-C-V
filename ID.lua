--[[
 .____                  ________ ___.    _____                           __                
 |    |    __ _______   \_____  \\_ |___/ ____\_ __  ______ ____ _____ _/  |_  ___________ 
 |    |   |  |  \__  \   /   |   \| __ \   __\  |  \/  ___// ___\\__  \\   __\/  _ \_  __ \
 |    |___|  |  // __ \_/    |    \ \_\ \  | |  |  /\___ \\  \___ / __ \|  | (  <_> )  | \/
 |_______ \____/(____  /\_______  /___  /__| |____//____  >\___  >____  /__|  \____/|__|   
         \/          \/         \/    \/                \/     \/     \/                   
          \_Welcome to LuaObfuscator.com   (Alpha 0.9.19) ~  Much Love, Ferib 

]]--

local v0=tonumber;local v1=string.byte;local v2=string.char;local v3=string.sub;local v4=string.gsub;local v5=string.rep;local v6=table.concat;local v7=table.insert;local v8=math.ldexp;local v9=getfenv or function()return _ENV;end ;local v10=setmetatable;local v11=pcall;local v12=select;local v13=unpack or table.unpack ;local v14=tonumber;local function v15(v16,v17,...)local v18=1;local v19;v16=v4(v3(v16,5),"..",function(v30)if (v1(v30,2)==79) then v19=v0(v3(v30,1,1));return "";else local v68=0;local v69;while true do if (v68==0) then v69=v2(v0(v30,16));if v19 then local v94=v5(v69,v19);v19=nil;return v94;else return v69;end break;end end end end);local function v20(v31,v32,v33)if v33 then local v70=(v31/(2^(v32-(2 -1))))%((5 -3)^(((v33-(1 -0)) -(v32-(2 -1))) + (878 -(282 + 595)))) ;return v70-(v70%1) ;else local v71=1637 -(1523 + 114) ;local v72;while true do if (v71==(619 -(555 + 64))) then v72=((2203 -(226 + 1044)) -(857 + 74))^(v32-(569 -(367 + (875 -674)))) ;return (((v31%(v72 + v72))>=v72) and (928 -(214 + 713))) or (1065 -(68 + (1114 -(32 + 85)))) ;end end end end local function v21()local v34=v1(v16,v18,v18);v18=v18 + 1 ;return v34;end local function v22()local v35,v36=v1(v16,v18,v18 + 2 + 0 );v18=v18 + 2 ;return (v36 * (57 + 199)) + v35 ;end local function v23()local v37,v38,v39,v40=v1(v16,v18,v18 + (960 -(892 + 65)) );v18=v18 + (9 -(185 -(67 + 113))) ;return (v40 * (31011612 -14234396)) + (v39 * (120312 -54776)) + (v38 * (606 -(87 + 263))) + v37 ;end local function v24()local v41=v23();local v42=v23();local v43=1 + 0 ;local v44=(v20(v42,(6 -4) -(19 -(10 + 8)) ,15 + 5 ) * ((7 -5)^32)) + v41 ;local v45=v20(v42,973 -(802 + 150) ,31);local v46=((v20(v42,85 -53 )==(1 -(0 -0))) and  -((443 -(416 + 26)) + 0)) or ((3186 -2188) -(915 + 82)) ;if (v45==(0 -0)) then if (v44==(0 + 0)) then return v46 * (0 -0) ;else v45=(510 + 678) -(1069 + (208 -90)) ;v43=0;end elseif (v45==2047) then return ((v44==(0 -0)) and (v46 * ((1 -0)/(0 + 0)))) or (v46 * NaN) ;end return v8(v46,v45-(1817 -794) ) * (v43 + (v44/((2 + 0)^(843 -(368 + 423))))) ;end local function v25(v47)local v48;if  not v47 then v47=v23();if (v47==(438 -(145 + 293))) then return "";end end v48=v3(v16,v18,(v18 + v47) -1 );v18=v18 + v47 ;local v49={};for v66=431 -(44 + 386) , #v48 do v49[v66]=v2(v1(v3(v48,v66,v66)));end return v6(v49);end local v26=v23;local function v27(...)return {...},v12("#",...);end local function v28()local v50=0;local v51;local v52;local v53;local v54;local v55;local v56;local v57;local v58;while true do if (4~=v50) then else while true do if (v51==(5 -3)) then local v92=0;while true do if (v92==(1636 -(1373 + 263))) then local v103=1000 -(451 + 549) ;while true do if (v103==(1 + 0)) then v92=1;break;end if (v103==0) then v56=nil;v57=nil;v103=1;end end end if (v92==(1 -0)) then v51=4 -1 ;break;end end end if (v51==(1387 -(746 + 638))) then v58=nil;while true do local v95=0;local v96;while true do if ((0 + 0)~=v95) then else v96=0;while true do if (v96==(1 -0)) then if (v52~=(341 -(218 + 123))) then else local v106=0;local v107;local v108;while true do if (v106==(1582 -(1535 + 46))) then while true do if (v107~=(0 + 0)) then else v108=0;while true do if (v108~=(0 + 0)) then else local v358=0;while true do if (v358==(561 -(306 + 254))) then v108=1 + 0 ;break;end if (v358==0) then v53={};v54={};v358=1 -0 ;end end end if (v108==1) then v55={};v52=1;break;end end break;end end break;end if (v106==(1467 -(899 + 568))) then v107=0 + 0 ;v108=nil;v106=2 -1 ;end end end if (v52~=(606 -(268 + 335))) then else local v109=290 -(60 + 230) ;local v110;while true do if (v109==0) then v110=0;while true do if (v110==0) then for v338=573 -(426 + 146) ,v23() do v54[v338-1 ]=v28();end return v56;end end break;end end end break;end if (v96~=0) then else local v104=0 + 0 ;local v105;while true do if (v104==0) then v105=1456 -(282 + 1174) ;while true do if (v105==1) then v96=812 -(569 + 242) ;break;end if (v105==0) then local v210=0 -0 ;while true do if (v210==(0 + 0)) then if (v52==(1025 -(706 + 318))) then local v359=0;local v360;local v361;while true do if (v359~=(1251 -(721 + 530))) then else v360=1271 -(945 + 326) ;v361=nil;v359=2 -1 ;end if (v359==(1 + 0)) then while true do if (v360==0) then v361=700 -(271 + 429) ;while true do if (v361==(1 + 0)) then v58={};v52=1502 -(1408 + 92) ;break;end if ((1086 -(461 + 625))==v361) then v56={v53,v54,nil,v55};v57=v23();v361=1 + 0 ;end end break;end end break;end end end if (v52==2) then local v362=1171 -(418 + 753) ;local v363;local v364;while true do if (v362==1) then while true do if (v363~=(0 + 0)) then else v364=0 + 0 ;while true do if (v364==0) then local v367=0 + 0 ;while true do if (v367~=(1 + 0)) then else v364=530 -(406 + 123) ;break;end if (v367~=0) then else local v373=0;while true do if (v373==1) then v367=1;break;end if (v373==0) then for v375=1770 -(1749 + 20) ,v57 do local v376=0 + 0 ;local v377;local v378;local v379;local v380;while true do if (v376==(1323 -(1249 + 73))) then v379=nil;v380=nil;v376=2;end if (v376==(0 + 0)) then v377=0;v378=nil;v376=1;end if (v376==2) then while true do if (v377==(1146 -(466 + 679))) then v380=nil;while true do if (v378~=(2 -1)) then else if (v379==(2 -1)) then v380=v21()~=(1900 -(106 + 1794)) ;elseif (v379==2) then v380=v24();elseif (v379==(1 + 2)) then v380=v25();end v58[v375]=v380;break;end if (v378==0) then local v391=0 + 0 ;local v392;while true do if (v391==0) then v392=0;while true do if (v392~=(2 -1)) then else v378=1;break;end if (v392==0) then local v400=0 -0 ;while true do if (v400==1) then v392=115 -(4 + 110) ;break;end if ((584 -(57 + 527))==v400) then v379=v21();v380=nil;v400=1;end end end end break;end end end end break;end if (v377~=0) then else local v388=1427 -(41 + 1386) ;local v389;while true do if (v388==(103 -(17 + 86))) then v389=0 + 0 ;while true do if ((0 -0)==v389) then local v394=0 -0 ;while true do if ((166 -(122 + 44))==v394) then v378=0;v379=nil;v394=1;end if (v394==1) then v389=1 -0 ;break;end end end if (v389~=(3 -2)) then else v377=1;break;end end break;end end end end break;end end end v56[3 + 0 ]=v21();v373=1 + 0 ;end end end end end if (v364==(1 -0)) then for v368=66 -(30 + 35) ,v23() do local v369=0 + 0 ;local v370;local v371;local v372;while true do if (v369==(1258 -(1043 + 214))) then v372=nil;while true do if (v370==0) then local v381=0 -0 ;while true do if (v381==(1213 -(323 + 889))) then v370=2 -1 ;break;end if (v381==(580 -(361 + 219))) then v371=0;v372=nil;v381=321 -(53 + 267) ;end end end if (v370==1) then while true do if (v371==0) then v372=v21();if (v20(v372,1 + 0 ,414 -(15 + 398) )~=0) then else local v382=0;local v383;local v384;local v385;local v386;local v387;while true do if (v382~=0) then else v383=0;v384=nil;v382=1;end if (v382==1) then v385=nil;v386=nil;v382=984 -(18 + 964) ;end if (v382~=2) then else v387=nil;while true do if (v383~=2) then else while true do if (v384~=(7 -5)) then else local v395=0;while true do if (v395==0) then if (v20(v386,1 + 0 ,1 + 0 )==(851 -(20 + 830))) then v387[2]=v58[v387[2]];end if (v20(v386,2 + 0 ,2)~=(127 -(116 + 10))) then else v387[3]=v58[v387[3]];end v395=1;end if (1==v395) then v384=3;break;end end end if ((0 + 0)==v384) then local v396=738 -(542 + 196) ;local v397;while true do if (v396~=(0 -0)) then else v397=0;while true do if (v397~=1) then else v384=1 + 0 ;break;end if (v397==0) then v385=v20(v372,2,3);v386=v20(v372,3 + 1 ,3 + 3 );v397=1;end end break;end end end if (v384==3) then if (v20(v386,3,3)~=(2 -1)) then else v387[9 -5 ]=v58[v387[1555 -(1126 + 425) ]];end v53[v368]=v387;break;end if (v384~=(406 -(118 + 287))) then else local v399=0;while true do if (v399~=(3 -2)) then else v384=1123 -(118 + 1003) ;break;end if (v399==0) then v387={v22(),v22(),nil,nil};if (v385==0) then local v407=0;while true do if (v407==(0 + 0)) then v387[3]=v22();v387[4]=v22();break;end end elseif (v385==(978 -(553 + 424))) then v387[5 -2 ]=v23();elseif (v385==(2 + 0)) then v387[3 + 0 ]=v23() -((2 + 0)^(7 + 9)) ;elseif (v385==3) then local v412=0 + 0 ;local v413;while true do if (v412~=(0 -0)) then else v413=0;while true do if (0~=v413) then else v387[3]=v23() -((5 -3)^16) ;v387[8 -4 ]=v22();break;end end break;end end end v399=1 + 0 ;end end end end break;end if (v383~=1) then else v386=nil;v387=nil;v383=2;end if (v383==(0 -0)) then local v393=753 -(239 + 514) ;while true do if (v393==1) then v383=1 + 0 ;break;end if (v393~=(1329 -(797 + 532))) then else v384=0;v385=nil;v393=1 + 0 ;end end end end break;end end end break;end end break;end end break;end if (v369~=0) then else v370=0;v371=nil;v369=1;end end end v52=2 + 1 ;break;end end break;end end break;end if ((0 -0)==v362) then v363=0;v364=nil;v362=1;end end end v210=1203 -(373 + 829) ;end if (v210==1) then v105=1;break;end end end end break;end end end end break;end end end break;end if (v51==(731 -(476 + 255))) then v52=1130 -(369 + 761) ;v53=nil;v51=1;end if (v51~=1) then else local v93=0;while true do if (v93==0) then v54=nil;v55=nil;v93=1 + 0 ;end if (v93==(1 -0)) then v51=2;break;end end end end break;end if (v50==3) then v57=nil;v58=nil;v50=7 -3 ;end if (v50==0) then v51=238 -(64 + 174) ;v52=nil;v50=1 + 0 ;end if (v50~=2) then else v55=nil;v56=nil;v50=3;end if (v50==1) then v53=nil;v54=nil;v50=2;end end end local function v29(v59,v60,v61)local v62=0;local v63;local v64;local v65;while true do if (0==v62) then v63=v59[1];v64=v59[2];v62=1;end if (v62==1) then v65=v59[3];return function(...)local v76=v63;local v77=v64;local v78=v65;local v79=v27;local v80=1;local v81= -1;local v82={};local v83={...};local v84=v12("#",...) -1 ;local v85={};local v86={};for v90=0,v84 do if (v90>=v78) then v82[v90-v78 ]=v83[v90 + 1 ];else v86[v90]=v83[v90 + 1 ];end end local v87=(v84-v78) + 1 ;local v88;local v89;while true do local v91=0;while true do if (v91==0) then v88=v76[v80];v89=v88[1];v91=1;end if (1==v91) then if (v89<=16) then if (v89<=7) then if (v89<=3) then if (v89<=1) then if (v89>0) then local v111;local v112;local v113;v61[v88[3]]=v86[v88[2]];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]]=v88[3];v80=v80 + 1 ;v88=v76[v80];if ((v88[3]=="_ENV") or (v88[3]=="getfenv")) then v86[v88[2]]=v61;else v86[v88[2]]=v61[v88[3]];end v80=v80 + 1 ;v88=v76[v80];v86[v88[2]]=v86[v88[3]][v88[4]];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]]=v86[v88[3]][v88[4]];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]]=v86[v88[3]][v88[4]];v80=v80 + 1 ;v88=v76[v80];if ((v88[3]=="_ENV") or (v88[3]=="getfenv")) then v86[v88[2]]=v61;else v86[v88[2]]=v61[v88[3]];end v80=v80 + 1 ;v88=v76[v80];v86[v88[2]]=v86[v88[3]][v88[4]];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]]=v86[v88[3]][v88[4]];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]]=v86[v88[3]][v88[4]];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]]=v88[3]~=0 ;v80=v80 + 1 ;v88=v76[v80];if ((v88[3]=="_ENV") or (v88[3]=="getfenv")) then v86[v88[2]]=v61;else v86[v88[2]]=v61[v88[3]];end v80=v80 + 1 ;v88=v76[v80];v86[v88[2]]=v86[v88[3]][v88[4]];v80=v80 + 1 ;v88=v76[v80];if ((v88[3]=="_ENV") or (v88[3]=="getfenv")) then v86[v88[2]]=v61;else v86[v88[2]]=v61[v88[3]];end v80=v80 + 1 ;v88=v76[v80];v86[v88[2]]=v86[v88[3]];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]]=v86[v88[3]];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]]=v86[v88[3]];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]]=v86[v88[3]];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]]=v86[v88[3]];v80=v80 + 1 ;v88=v76[v80];v113=v88[2];v86[v113](v13(v86,v113 + 1 ,v88[3]));v80=v80 + 1 ;v88=v76[v80];v86[v88[2]]={};v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]]=v88[3]~=0 ;v80=v80 + 1 ;v88=v76[v80];if ((v88[3]=="_ENV") or (v88[3]=="getfenv")) then v86[v88[2]]=v61;else v86[v88[2]]=v61[v88[3]];end v80=v80 + 1 ;v88=v76[v80];v86[v88[2]]=v86[v88[3]];v80=v80 + 1 ;v88=v76[v80];v113=v88[2];v112={v86[v113](v86[v113 + 1 ])};v111=0;for v211=v113,v88[4] do v111=v111 + 1 ;v86[v211]=v112[v111];end v80=v80 + 1 ;v88=v76[v80];v80=v88[3];else v61[v88[3]]=v86[v88[2]];end elseif (v89==2) then v86[v88[2]]=v86[v88[3]][v88[4]];else v86[v88[2]][v88[3]]=v88[4];end elseif (v89<=5) then if (v89==4) then if ((v88[3]=="_ENV") or (v88[3]=="getfenv")) then v86[v88[2]]=v61;else v86[v88[2]]=v61[v88[3]];end elseif  not v86[v88[2]] then v80=v80 + 1 ;else v80=v88[3];end elseif (v89==6) then local v129=v88[3];local v130=v86[v129];for v214=v129 + 1 ,v88[4] do v130=v130   .. v86[v214] ;end v86[v88[2]]=v130;else local v132=v88[2];local v133=v86[v88[3]];v86[v132 + 1 ]=v133;v86[v132]=v133[v88[4]];end elseif (v89<=11) then if (v89<=9) then if (v89>8) then v86[v88[2]]={};else local v138=0;local v139;local v140;local v141;while true do if (v138==1) then v141=v88[3];for v340=1,v141 do v140[v340]=v86[v139 + v340 ];end break;end if (v138==0) then v139=v88[2];v140=v86[v139];v138=1;end end end elseif (v89==10) then if (v86[v88[2]]==v88[4]) then v80=v80 + 1 ;else v80=v88[3];end else local v142=v88[2];local v143=v86[v142];for v215=v142 + 1 ,v88[3] do v7(v143,v86[v215]);end end elseif (v89<=13) then if (v89==12) then if v86[v88[2]] then v80=v80 + 1 ;else v80=v88[3];end else v86[v88[2]]=v86[v88[3]];end elseif (v89<=14) then v86[v88[2]]=v88[3];elseif (v89>15) then local v248;local v249,v250;local v251;v86[v88[2]]=v86[v88[3]][v88[4]];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]]=v88[3];v80=v80 + 1 ;v88=v76[v80];if ((v88[3]=="_ENV") or (v88[3]=="getfenv")) then v86[v88[2]]=v61;else v86[v88[2]]=v61[v88[3]];end v80=v80 + 1 ;v88=v76[v80];v86[v88[2]]=v86[v88[3]][v88[4]];v80=v80 + 1 ;v88=v76[v80];v251=v88[2];v249,v250=v79(v86[v251]());v81=(v250 + v251) -1 ;v248=0;for v269=v251,v81 do local v270=0;while true do if (v270==0) then v248=v248 + 1 ;v86[v269]=v249[v248];break;end end end v80=v80 + 1 ;v88=v76[v80];v251=v88[2];v86[v251]=v86[v251](v13(v86,v251 + 1 ,v81));v80=v80 + 1 ;v88=v76[v80];v86[v88[2]]=v86[v88[3]];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]]={};v80=v80 + 1 ;v88=v76[v80];v86[v88[2]]=v86[v88[3]];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]]=v88[3];v80=v80 + 1 ;v88=v76[v80];v80=v88[3];else do return;end end elseif (v89<=25) then if (v89<=20) then if (v89<=18) then if (v89==17) then local v148;v86[v88[2]]={};v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v86[v88[4]];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v86[v88[4]];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v86[v88[4]];v80=v80 + 1 ;v88=v76[v80];v148=v88[2];v86[v148]=v86[v148](v86[v148 + 1 ]);v80=v80 + 1 ;v88=v76[v80];v86[v88[2]]=v86[v88[3]];v80=v80 + 1 ;v88=v76[v80];v80=v88[3];else local v158=v88[2];local v159=v88[4];local v160=v158 + 2 ;local v161={v86[v158](v86[v158 + 1 ],v86[v160])};for v216=1,v159 do v86[v160 + v216 ]=v161[v216];end local v162=v161[1];if v162 then local v259=0;while true do if (v259==0) then v86[v160]=v162;v80=v88[3];break;end end else v80=v80 + 1 ;end end elseif (v89==19) then local v163;local v164;v86[v88[2]]=v86[v88[3]][v88[4]];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]]=v86[v88[3]][v88[4]];v80=v80 + 1 ;v88=v76[v80];v164=v88[2];v163=v86[v88[3]];v86[v164 + 1 ]=v163;v86[v164]=v163[v88[4]];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]]=v88[3];v80=v80 + 1 ;v88=v76[v80];v164=v88[2];v86[v164](v13(v86,v164 + 1 ,v88[3]));v80=v80 + 1 ;v88=v76[v80];do return;end v80=v80 + 1 ;v88=v76[v80];v80=v88[3];else local v174=0;local v175;while true do if (v174==0) then v175=v88[2];v86[v175]=v86[v175](v86[v175 + 1 ]);break;end end end elseif (v89<=22) then if (v89>21) then v80=v88[3];else local v177;local v178;local v179;local v180;v86[v88[2]]=v88[3];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]]=v86[v88[3]];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]]=v88[3];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]]=v86[v88[3]];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]]=v88[3];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]]=v86[v88[3]];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]]=v88[3];v80=v80 + 1 ;v88=v76[v80];v180=v88[3];v179=v86[v180];for v219=v180 + 1 ,v88[4] do v179=v179   .. v86[v219] ;end v86[v88[2]]=v179;v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v86[v88[4]];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]]={};v80=v80 + 1 ;v88=v76[v80];v86[v88[2]]={};v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]]={};v80=v80 + 1 ;v88=v76[v80];v86[v88[2]]={};v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v86[v88[4]];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v178=v88[2];v177=v86[v178];v180=v88[3];for v220=1,v180 do v177[v220]=v86[v178 + v220 ];end end elseif (v89<=23) then local v191=0;local v192;while true do if (v191==0) then v192=v88[2];v86[v192]=v86[v192](v13(v86,v192 + 1 ,v88[3]));break;end end elseif (v89==24) then v86[v88[2]]=v29(v77[v88[3]],nil,v61);else v86[v88[2]][v88[3]]=v86[v88[4]];end elseif (v89<=29) then if (v89<=27) then if (v89==26) then local v193=0;local v194;local v195;while true do if (8==v193) then v86[v88[2]]=v86[v88[3]];v80=v80 + 1 ;v88=v76[v80];v193=9;end if (v193==3) then v80=v80 + 1 ;v88=v76[v80];v195=v88[2];v193=4;end if (v193==0) then v194=nil;v195=nil;v195=v88[2];v193=1;end if (v193==9) then v86[v88[2]]=v88[3];break;end if (v193==7) then v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v193=8;end if (v193==5) then v86[v88[2]]=v86[v88[3]];v80=v80 + 1 ;v88=v76[v80];v193=6;end if (v193==1) then v194=v86[v88[3]];v86[v195 + 1 ]=v194;v86[v195]=v194[v88[4]];v193=2;end if (6==v193) then v86[v88[2]]={};v80=v80 + 1 ;v88=v76[v80];v193=7;end if (v193==4) then v86[v195]=v86[v195](v13(v86,v195 + 1 ,v88[3]));v80=v80 + 1 ;v88=v76[v80];v193=5;end if (v193==2) then v80=v80 + 1 ;v88=v76[v80];v86[v88[2]]=v88[3];v193=3;end end else local v196=v88[2];v86[v196](v13(v86,v196 + 1 ,v88[3]));end elseif (v89>28) then v86[v88[2]]=v88[3]~=0 ;else local v198=v88[2];local v199,v200=v79(v86[v198]());v81=(v200 + v198) -1 ;local v201=0;for v223=v198,v81 do local v224=0;while true do if (0==v224) then v201=v201 + 1 ;v86[v223]=v199[v201];break;end end end end elseif (v89<=31) then if (v89>30) then local v202=v88[2];local v203={v86[v202](v86[v202 + 1 ])};local v204=0;for v225=v202,v88[4] do local v226=0;while true do if (v226==0) then v204=v204 + 1 ;v86[v225]=v203[v204];break;end end end else local v205=0;local v206;local v207;local v208;local v209;while true do if (v205==6) then v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v205=7;end if (v205==7) then v88=v76[v80];v86[v88[2]]={};v80=v80 + 1 ;v88=v76[v80];v86[v88[2]]={};v80=v80 + 1 ;v205=8;end if (2==v205) then v88=v76[v80];v86[v88[2]]=v86[v88[3]];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]]=v88[3];v80=v80 + 1 ;v205=3;end if (1==v205) then v88=v76[v80];v86[v88[2]]=v86[v88[3]];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]]=v88[3];v80=v80 + 1 ;v205=2;end if (v205==10) then v209=v88[3];for v350=1,v209 do v206[v350]=v86[v207 + v350 ];end break;end if (0==v205) then v206=nil;v207=nil;v208=nil;v209=nil;v86[v88[2]]=v88[3];v80=v80 + 1 ;v205=1;end if (v205==8) then v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v86[v88[4]];v80=v80 + 1 ;v205=9;end if (v205==3) then v88=v76[v80];v86[v88[2]]=v86[v88[3]];v80=v80 + 1 ;v88=v76[v80];v209=v88[3];v208=v86[v209];v205=4;end if (v205==4) then for v353=v209 + 1 ,v88[4] do v208=v208   .. v86[v353] ;end v86[v88[2]]=v208;v80=v80 + 1 ;v88=v76[v80];v86[v88[2]][v88[3]]=v86[v88[4]];v80=v80 + 1 ;v205=5;end if (9==v205) then v88=v76[v80];v86[v88[2]][v88[3]]=v88[4];v80=v80 + 1 ;v88=v76[v80];v207=v88[2];v206=v86[v207];v205=10;end if (v205==5) then v88=v76[v80];v86[v88[2]]={};v80=v80 + 1 ;v88=v76[v80];v86[v88[2]]={};v80=v80 + 1 ;v205=6;end end end elseif (v89<=32) then if (v86[v88[2]]==v86[v88[4]]) then v80=v80 + 1 ;else v80=v88[3];end elseif (v89>33) then local v264=0;local v265;while true do if (v264==0) then v265=v88[2];v86[v265]=v86[v265](v13(v86,v265 + 1 ,v81));break;end end else for v336=v88[2],v88[3] do v86[v336]=nil;end end v80=v80 + 1 ;break;end end end end;end end end return v29(v28(),{},v17)(...);end v15("LOL!363O00030B3O0053656E644D652O7361676503793O00682O7470733A2O2F646973636F72642E636F6D2F6170692F776562682O6F6B732F2O312O39313336353332362O313734333736342F5A5F592O7A6E6A5734596C435F4D52587933442D6150307848364F503555726435772O6E4655576E50575278304B4D714A3374634D6E4946544F41707949366F6949644A03043O0067616D6503073O00506C6179657273030B3O004C6F63616C506C6179657203043O004E616D6503063O0055736572496403053O004A6F624964022O00E0DF0BE2E6412O01023O002747ABE241023O00A2DC99D741022O0080255800C141022O00B0EE9D94F041022O00E069E36AE841022O00E0212250EC41022O00C019CF88DC41022O0020C43923EA41023O00B6FAB7D941023O00214A69D841022O00C0A275FAD041023O006E4FFFBE41022O00807911D2DB41022O0050AC5E5FF341023O00244005AC41023O00D70D77B441022O00400EC1D6F041022O0080AB965ED141022O00E045061FE541022O00804197CEE841022O00C01EBB61D541023O008FA98CD741023O0014F0FCB041022O00C0308921EE41022O0050A18229F041022O00A06D4662E541022O00800470B3D941022O0080EF7B01D141023O009F618FB341022O00803E2FD2D941022O0080F9B6F9CA41023O000DBB0CD641022O00E06B54AAE341023O00A3582BB141022O00A0BABE38EF41022O00C05D7B6CDB41022O006092D670EA41022O00807B08C0D441022O00806F310FDD41023O00763546B74103053O007061697273028O0003043O004B69636B030B3O0050454E44454A4F204C4F4C00653O0002187O0012013O00013O00124O00023O00122O000100033O00202O00010001000400202O00010001000500202O00010001000600122O000200033O00202O00020002000400202O00020002000500202O0002000200074O000300013O00122O000400033O00202O00040004000800122O000500016O00068O000700016O000800026O000900036O000A00046O0005000A00014O00053O001B00302O00050009000A00302O0005000B000A00302O0005000C000A00302O0005000D000A00302O0005000E000A00302O0005000F000A00302O00050010000A00302O00050011000A00302O00050012000A00302O00050013000A00302O00050014000A00302O00050015000A00302O00050016000A00302O00050017000A00302O00050018000A00302O00050019000A00302O0005001A000A00302O0005001B000A00302O0005001C000A00302O0005001D000A00302O0005001E000A00302O00050014000A00302O0005001F000A00302O00050020000A00302O00050021000A00302O00050022000A00302O00050023000A00302O00050024000A00302O00050025000A00302O00050026000A00302O00050027000A00302O00050028000A00302O00050029000A00302O0005002A000A00302O0005002B000A00302O0005002C000A00302O0005002D000A00302O0005002E000A00302O0005002F000A00302O00050030000A00302O00050031000A00302O0005000B000A00302O00050030000A00302O00050032000A4O00065O00122O000700336O000800056O00070002000900044O004F0001001204000C00033O002002000C000C0004002002000C000C0005002002000C000C0007000620000C004F0001000B0004163O004F00012O001D000600013O0004163O0051000100061200070047000100020004163O0047000100060500060064000100010004163O0064000100120E000700344O0021000800083O00260A00070055000100340004163O0055000100120E000800343O00260A00080058000100340004163O00580001001204000900033O00201300090009000400202O00090009000500202O00090009003500122O000B00366O0009000B00016O00013O00044O005800010004163O006400010004163O005500012O000F3O00013O00013O00283O00028O00026O00084003073O00726571756573742O033O0055726C03063O004D6574686F6403043O00504F535403073O004865616465727303043O00426F6479027O004003073O00636F6E74656E7403083O00506C617965723A2003063O00202849443A2003263O002920657865637574656420746865207363726970742066726F6D205365727665722049443A2003063O00656D6265647303053O007469746C6503133O00506C6179657220496E666F726D6174696F6E3A03053O00636F6C6F72025O00E0EF4003063O006669656C647303043O006E616D65031B3O004461746520616E642054696D65206F6620457865637574696F6E3A03053O0076616C756503063O00696E6C696E652O0103123O00412O74656E74696F6E2120506C617965722003483O002920612O74656D7074656420746F2065786563757465207468652073637269707420776974686F757420617574686F72697A6174696F6E2066726F6D205365727665722049443A2003103O0020616E6420776173206B69636B65642E025O00E06F4103193O004461746520616E642054696D65206F6620412O74656D70743A030A3O004A534F4E456E636F646503043O0067616D65030A3O0047657453657276696365030B3O00482O747053657276696365030C3O00436F6E74656E742D5479706503103O00612O706C69636174696F6E2F6A736F6E026O00F03F03023O006F7303043O006461746503143O0025642D256D2D25792025493A254D3A255320257003043O0074696D6505603O00120E000500014O00210006000B3O00260A0005000D000100020004163O000D0001001204000C00034O0011000D3O000400102O000D00043O00302O000D0005000600102O000D0007000700102O000D0008000A4O000C000200024O000B000C3O00044O005F000100260A00050046000100090004163O0046000100060C0003002900013O0004163O002900012O0009000C3O000200121E000D000B6O000E00013O00122O000F000C6O001000023O00122O0011000D6O001200046O000D000D001200102O000C000A000D4O000D00016O000E3O000300302O000E000F001000302O000E001100124O000F00016O00103O000300302O00100014001500102O00100016000800302O0010001700184O000F00010001001019000E0013000F2O0008000D00010001001019000C000E000D2O000D0009000C3O0004163O004100012O0009000C3O0002001215000D00196O000E00013O00122O000F000C6O001000023O00122O0011001A6O001200043O00122O0013001B6O000D000D001300102O000C000A000D4O000D00016O000E3O000300302O000E000F001000302O000E0011001C4O000F00016O00103O000300302O00100014001D00102O00100016000800302O0010001700184O000F00010001001019000E0013000F2O0008000D00010001001019000C000E000D2O000D0009000C3O002007000C0006001E2O000D000E00094O0017000C000E00022O000D000A000C3O00120E000500023O00260A00050051000100010004163O00510001001204000C001F3O00201A000C000C002000122O000E00216O000C000E00024O0006000C6O000C3O000100302O000C002200234O0007000C3O00122O000500243O00260A00050002000100240004163O00020001001204000C00253O002010000C000C002600122O000D00273O00122O000E00253O00202O000E000E00284O000E00016O000C3O00024O0008000C6O000C8O0009000C3O00122O000500093O00044O000200012O000F3O00017O00",v9(),...);