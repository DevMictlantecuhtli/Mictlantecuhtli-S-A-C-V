--[[
 .____                  ________ ___.    _____                           __                
 |    |    __ _______   \_____  \\_ |___/ ____\_ __  ______ ____ _____ _/  |_  ___________ 
 |    |   |  |  \__  \   /   |   \| __ \   __\  |  \/  ___// ___\\__  \\   __\/  _ \_  __ \
 |    |___|  |  // __ \_/    |    \ \_\ \  | |  |  /\___ \\  \___ / __ \|  | (  <_> )  | \/
 |_______ \____/(____  /\_______  /___  /__| |____//____  >\___  >____  /__|  \____/|__|   
         \/          \/         \/    \/                \/     \/     \/                   
          \_Welcome to LuaObfuscator.com   (Alpha 0.10.3) ~  Much Love, Ferib 

]]--

local v0 = tonumber;
local v1 = string.byte;
local v2 = string.char;
local v3 = string.sub;
local v4 = string.gsub;
local v5 = string.rep;
local v6 = table.concat;
local v7 = table.insert;
local v8 = math.ldexp;
local v9 = getfenv or function()
	return _ENV;
end;
local v10 = setmetatable;
local v11 = pcall;
local v12 = select;
local v13 = unpack or table.unpack;
local v14 = tonumber;
local function v15(v16, v17, ...)
	local v18 = 0;
	local v19;
	local v20;
	local v21;
	local v22;
	local v23;
	local v24;
	local v25;
	local v26;
	local v27;
	local v28;
	local v29;
	local v30;
	while true do
		if (v18 == 5) then
			v27 = v24;
			v28 = nil;
			function v28(...)
				return {...}, v12("#", ...);
			end
			v18 = 6;
		end
		if (v18 == 1) then
			v21 = nil;
			function v21(v31, v32, v33)
				if v33 then
					local v73 = (v31 / ((5 - (1 + 2)) ^ (v32 - (2 - 1)))) % ((3 - 1) ^ (((v33 - (2 - 1)) - (v32 - (620 - (555 + (941 - (282 + 595)))))) + (932 - (857 + 74))));
					return v73 - (v73 % 1);
				else
					local v74 = (570 - (367 + 201)) ^ (v32 - ((2565 - (1523 + 114)) - (214 + 713)));
					return (((v31 % (v74 + v74)) >= v74) and 1) or (0 + 0);
				end
			end
			v22 = nil;
			v18 = 2;
		end
		if (v18 == 3) then
			v24 = nil;
			function v24()
				local v34 = 0 + 0;
				local v35;
				local v36;
				local v37;
				local v38;
				while true do
					if (v34 == (0 - 0)) then
						v35, v36, v37, v38 = v1(v16, v19, v19 + (1068 - ((125 - 57) + 997)));
						v19 = v19 + (1274 - (226 + 1044));
						v34 = 4 - 3;
					end
					if ((118 - (32 + 85)) == v34) then
						return (v38 * (16441815 + 335401)) + (v37 * (14533 + 51003)) + (v36 * (1213 - ((2127 - 1235) + 65))) + v35;
					end
				end
			end
			v25 = nil;
			v18 = 4;
		end
		if (v18 == 6) then
			v29 = nil;
			function v29()
				local v39 = 0;
				local v40;
				local v41;
				local v42;
				local v43;
				local v44;
				local v45;
				local v46;
				local v47;
				while true do
					if (v39 == 4) then
						while true do
							if (v40 ~= (2 + 0)) then
							else
								local v98 = 254 - (163 + 91);
								while true do
									if (v98 ~= 1) then
									else
										v40 = 3;
										break;
									end
									if (v98 ~= (1930 - (1869 + 61))) then
									else
										v45 = nil;
										v46 = nil;
										v98 = 1 + 0;
									end
								end
							end
							if (v40 ~= 3) then
							else
								v47 = nil;
								while true do
									local v100 = 0 - 0;
									while true do
										if (1 == v100) then
											if (v41 == 0) then
												v42 = {};
												v43 = {};
												v44 = {};
												v45 = {v42,v43,nil,v44};
												v41 = 1;
											end
											break;
										end
										if (v100 == (0 - 0)) then
											if (v41 == 1) then
												local v108 = 0 + 0;
												local v109;
												while true do
													if (v108 ~= (0 - 0)) then
													else
														v109 = 0 + 0;
														while true do
															if (v109 ~= 0) then
															else
																v46 = v24();
																v47 = {};
																v109 = 1;
															end
															if ((1475 - (1329 + 145)) == v109) then
																local v134 = 971 - (140 + 831);
																while true do
																	if (v134 == (1851 - (1409 + 441))) then
																		v109 = 720 - (15 + 703);
																		break;
																	end
																	if (v134 ~= (0 + 0)) then
																	else
																		for v281 = 1, v46 do
																			local v282 = 438 - (262 + 176);
																			local v283;
																			local v284;
																			local v285;
																			while true do
																				if ((1721 - (345 + 1376)) == v282) then
																					v283 = 688 - (198 + 490);
																					v284 = nil;
																					v282 = 1;
																				end
																				if (v282 == 1) then
																					v285 = nil;
																					while true do
																						if (v283 ~= (4 - 3)) then
																						else
																							if (v284 == 1) then
																								v285 = v22() ~= 0;
																							elseif (v284 == 2) then
																								v285 = v25();
																							elseif (v284 == 3) then
																								v285 = v26();
																							end
																							v47[v281] = v285;
																							break;
																						end
																						if (v283 == 0) then
																							local v297 = 0;
																							local v298;
																							while true do
																								if (0 == v297) then
																									v298 = 0;
																									while true do
																										if (1 ~= v298) then
																										else
																											v283 = 1;
																											break;
																										end
																										if (v298 == (0 - 0)) then
																											local v305 = 1206 - (696 + 510);
																											while true do
																												if (v305 ~= 0) then
																												else
																													v284 = v22();
																													v285 = nil;
																													v305 = 1;
																												end
																												if (v305 ~= 1) then
																												else
																													v298 = 1 - 0;
																													break;
																												end
																											end
																										end
																									end
																									break;
																								end
																							end
																						end
																					end
																					break;
																				end
																			end
																		end
																		v45[3] = v22();
																		v134 = 1;
																	end
																end
															end
															if (v109 ~= 2) then
															else
																v41 = 2;
																break;
															end
														end
														break;
													end
												end
											end
											if (v41 ~= (1264 - (1091 + 171))) then
											else
												local v110 = 0 + 0;
												local v111;
												while true do
													if (v110 ~= 0) then
													else
														v111 = 0 - 0;
														while true do
															local v112 = 0;
															while true do
																if (v112 == 0) then
																	if (v111 == (0 - 0)) then
																		local v170 = 374 - (123 + 251);
																		while true do
																			if (v170 == 0) then
																				for v288 = 4 - 3, v24() do
																					local v289 = 698 - (208 + 490);
																					local v290;
																					local v291;
																					while true do
																						if (v289 == (0 + 0)) then
																							local v299 = 0;
																							while true do
																								if (v299 ~= (0 + 0)) then
																								else
																									v290 = 836 - (660 + 176);
																									v291 = nil;
																									v299 = 1 + 0;
																								end
																								if ((203 - (14 + 188)) ~= v299) then
																								else
																									v289 = 1;
																									break;
																								end
																							end
																						end
																						if (v289 == (676 - (534 + 141))) then
																							while true do
																								if (0 == v290) then
																									v291 = v22();
																									if (v21(v291, 1 + 0, 1 + 0) == (0 + 0)) then
																										local v300 = 0 - 0;
																										local v301;
																										local v302;
																										local v303;
																										local v304;
																										while true do
																											if ((2 - 0) == v300) then
																												while true do
																													if (v301 ~= (5 - 3)) then
																													else
																														local v306 = 0 + 0;
																														while true do
																															if (v306 == (1 + 0)) then
																																v301 = 3;
																																break;
																															end
																															if (v306 == (396 - (115 + 281))) then
																																local v311 = 0 - 0;
																																while true do
																																	if (v311 ~= (0 + 0)) then
																																	else
																																		if (v21(v303, 2 - 1, 1) ~= (3 - 2)) then
																																		else
																																			v304[869 - (550 + 317)] = v47[v304[2 - 0]];
																																		end
																																		if (v21(v303, 2, 2 - 0) ~= (2 - 1)) then
																																		else
																																			v304[288 - (134 + 151)] = v47[v304[1668 - (970 + 695)]];
																																		end
																																		v311 = 1 - 0;
																																	end
																																	if ((1991 - (582 + 1408)) ~= v311) then
																																	else
																																		v306 = 1;
																																		break;
																																	end
																																end
																															end
																														end
																													end
																													if (v301 ~= 1) then
																													else
																														local v307 = 0 - 0;
																														while true do
																															if (v307 ~= 1) then
																															else
																																v301 = 2;
																																break;
																															end
																															if (v307 == 0) then
																																local v312 = 0;
																																while true do
																																	if (v312 == (1 - 0)) then
																																		v307 = 3 - 2;
																																		break;
																																	end
																																	if (v312 ~= (1824 - (1195 + 629))) then
																																	else
																																		v304 = {v23(),v23(),nil,nil};
																																		if (v302 == (0 + 0)) then
																																			local v317 = 0;
																																			local v318;
																																			local v319;
																																			while true do
																																				if (v317 ~= (1 - 0)) then
																																				else
																																					while true do
																																						if (v318 ~= 0) then
																																						else
																																							v319 = 0 - 0;
																																							while true do
																																								if (v319 ~= 0) then
																																								else
																																									v304[1 + 2] = v23();
																																									v304[1640 - (1373 + 263)] = v23();
																																									break;
																																								end
																																							end
																																							break;
																																						end
																																					end
																																					break;
																																				end
																																				if (v317 ~= (1000 - (451 + 549))) then
																																				else
																																					v318 = 0 + 0;
																																					v319 = nil;
																																					v317 = 1 - 0;
																																				end
																																			end
																																		elseif (v302 == (1 - 0)) then
																																			v304[1387 - (746 + 638)] = v24();
																																		elseif (v302 == (1 + 1)) then
																																			v304[4 - 1] = v24() - (2 ^ (357 - (218 + 123)));
																																		elseif (v302 == (1584 - (1535 + 46))) then
																																			local v322 = 0;
																																			local v323;
																																			while true do
																																				if (0 ~= v322) then
																																				else
																																					v323 = 0;
																																					while true do
																																						if ((0 + 0) == v323) then
																																							v304[3] = v24() - (2 ^ (3 + 13));
																																							v304[564 - (306 + 254)] = v23();
																																							break;
																																						end
																																					end
																																					break;
																																				end
																																			end
																																		end
																																		v312 = 1 + 0;
																																	end
																																end
																															end
																														end
																													end
																													if (0 == v301) then
																														v302 = v21(v291, 2, 5 - 2);
																														v303 = v21(v291, 4, 1473 - (899 + 568));
																														v301 = 1 + 0;
																													end
																													if (v301 == (7 - 4)) then
																														if (v21(v303, 606 - (268 + 335), 3) ~= 1) then
																														else
																															v304[294 - (60 + 230)] = v47[v304[4]];
																														end
																														v42[v288] = v304;
																														break;
																													end
																												end
																												break;
																											end
																											if (v300 ~= 1) then
																											else
																												v303 = nil;
																												v304 = nil;
																												v300 = 2;
																											end
																											if (v300 ~= 0) then
																											else
																												v301 = 0;
																												v302 = nil;
																												v300 = 1;
																											end
																										end
																									end
																									break;
																								end
																							end
																							break;
																						end
																					end
																				end
																				for v292 = 1, v24() do
																					v43[v292 - (573 - (426 + 146))] = v29();
																				end
																				v170 = 1 + 0;
																			end
																			if ((1457 - (282 + 1174)) == v170) then
																				v111 = 1;
																				break;
																			end
																		end
																	end
																	if (v111 ~= 1) then
																	else
																		return v45;
																	end
																	break;
																end
															end
														end
														break;
													end
												end
											end
											v100 = 1;
										end
									end
								end
								break;
							end
							if (v40 ~= (811 - (569 + 242))) then
							else
								local v99 = 0 - 0;
								while true do
									if (v99 == (0 + 0)) then
										v41 = 1024 - (706 + 318);
										v42 = nil;
										v99 = 1252 - (721 + 530);
									end
									if (v99 == 1) then
										v40 = 1272 - (945 + 326);
										break;
									end
								end
							end
							if (v40 == 1) then
								v43 = nil;
								v44 = nil;
								v40 = 2;
							end
						end
						break;
					end
					if (v39 ~= 0) then
					else
						v40 = 0 - 0;
						v41 = nil;
						v39 = 1 + 0;
					end
					if (v39 ~= (702 - (271 + 429))) then
					else
						v44 = nil;
						v45 = nil;
						v39 = 3;
					end
					if (v39 ~= (1 + 0)) then
					else
						v42 = nil;
						v43 = nil;
						v39 = 2;
					end
					if (v39 ~= 3) then
					else
						v46 = nil;
						v47 = nil;
						v39 = 1504 - (1408 + 92);
					end
				end
			end
			v30 = nil;
			v18 = 7;
		end
		if (v18 == 4) then
			function v25()
				local v48 = 1086 - (461 + 625);
				local v49;
				local v50;
				local v51;
				local v52;
				local v53;
				local v54;
				while true do
					if (v48 == (1291 - (993 + 295))) then
						if (v53 == (0 + 0)) then
							if (v52 == (1171 - (418 + 753))) then
								return v54 * (0 + 0);
							else
								local v101 = 0 + 0;
								while true do
									if (v101 == 0) then
										v53 = 1;
										v51 = (0 - 0) + 0;
										break;
									end
								end
							end
						elseif (v53 == (518 + 1529)) then
							return ((v52 == (529 - (406 + 123))) and (v54 * ((1770 - ((5064 - 3315) + 20)) / 0))) or (v54 * NaN);
						end
						return v8(v54, v53 - (243 + (946 - (122 + 44)))) * (v51 + (v52 / ((2 - 0) ^ (1374 - (1249 + 73)))));
					end
					if (v48 == (1 + 0)) then
						v51 = 1146 - (466 + 679);
						v52 = (v21(v50, 2 - 1, 57 - 37) * ((1902 - (106 + 1794)) ^ (11 + 21))) + v49;
						v48 = 1 + 1;
					end
					if (v48 == (0 - 0)) then
						v49 = v24();
						v50 = v24();
						v48 = 2 - 1;
					end
					if (v48 == 2) then
						v53 = v21(v50, 135 - (4 + 110), (2040 - 1425) - (57 + 527));
						v54 = ((v21(v50, 27 + 5) == 1) and -(1428 - (41 + 201 + 1185))) or (104 - (17 + 86));
						v48 = (5 - 2) + 0;
					end
				end
			end
			v26 = nil;
			function v26(v55)
				local v56;
				if not v55 then
					local v75 = 65 - (30 + 35);
					while true do
						if (v75 == (0 + 0)) then
							v55 = v24();
							if (v55 == (1257 - (1043 + 214))) then
								return "";
							end
							break;
						end
					end
				end
				v56 = v3(v16, v19, (v19 + v55) - (3 - (5 - 3)));
				v19 = v19 + v55;
				local v57 = {};
				for v71 = 1213 - (323 + 889), #v56 do
					v57[v71] = v2(v1(v3(v56, v71, v71)));
				end
				return v6(v57);
			end
			v18 = 5;
		end
		if (v18 == 2) then
			function v22()
				local v58 = (1562 - (18 + 964)) - (361 + 219);
				local v59;
				while true do
					if (v58 == 0) then
						v59 = v1(v16, v19, v19);
						v19 = v19 + (321 - (53 + 267));
						v58 = 1 + 0;
					end
					if (v58 == (414 - (15 + (1498 - 1100)))) then
						return v59;
					end
				end
			end
			v23 = nil;
			function v23()
				local v60 = 0 + 0;
				local v61;
				local v62;
				while true do
					if ((738 - (542 + 196)) == v60) then
						v61, v62 = v1(v16, v19, v19 + 2 + 0);
						v19 = v19 + (852 - (20 + 830));
						v60 = 1 + 0;
					end
					if (v60 == (127 - (116 + 10))) then
						return (v62 * (19 + 237)) + v61;
					end
				end
			end
			v18 = 3;
		end
		if (v18 == 0) then
			v19 = 1;
			v20 = nil;
			v16 = v4(v3(v16, 5), "..", function(v63)
				if (v1(v63, 2) == 79) then
					v20 = v0(v3(v63, 1, 1));
					return "";
				else
					local v76 = v2(v0(v63, 16));
					if v20 then
						local v80 = 0;
						local v81;
						while true do
							if (v80 == 0) then
								v81 = v5(v76, v20);
								v20 = nil;
								v80 = 1;
							end
							if (v80 == 1) then
								return v81;
							end
						end
					else
						return v76;
					end
				end
			end);
			v18 = 1;
		end
		if (v18 == 7) then
			function v30(v64, v65, v66)
				local v67 = 0;
				local v68;
				local v69;
				local v70;
				while true do
					if (v67 == 0) then
						v68 = v64[1];
						v69 = v64[2];
						v67 = 1;
					end
					if (v67 == 1) then
						v70 = v64[3];
						return function(...)
							local v82 = v68;
							local v83 = v69;
							local v84 = v70;
							local v85 = v28;
							local v86 = 1;
							local v87 = -1;
							local v88 = {};
							local v89 = {...};
							local v90 = v12("#", ...) - 1;
							local v91 = {};
							local v92 = {};
							for v96 = 0, v90 do
								if (v96 >= v84) then
									v88[v96 - v84] = v89[v96 + 1];
								else
									v92[v96] = v89[v96 + 1];
								end
							end
							local v93 = (v90 - v84) + 1;
							local v94;
							local v95;
							while true do
								local v97 = 0;
								while true do
									if (v97 == 1) then
										if (v95 <= 9) then
											if (v95 <= 4) then
												if (v95 <= 1) then
													if (v95 > 0) then
														local v113 = 0;
														local v114;
														local v115;
														while true do
															if (v113 == 0) then
																v114 = v94[2];
																v115 = v92[v94[3]];
																v113 = 1;
															end
															if (v113 == 1) then
																v92[v114 + 1] = v115;
																v92[v114] = v115[v94[4]];
																break;
															end
														end
													else
														do
															return;
														end
													end
												elseif (v95 <= 2) then
													if (v92[v94[2]] == v92[v94[4]]) then
														v86 = v86 + 1;
													else
														v86 = v94[3];
													end
												elseif (v95 > 3) then
													local v136 = 0;
													local v137;
													local v138;
													while true do
														if (v136 == 3) then
															v137 = v92[v94[3]];
															v92[v138 + 1] = v137;
															v92[v138] = v137[v94[4]];
															v136 = 4;
														end
														if (v136 == 7) then
															do
																return;
															end
															v86 = v86 + 1;
															v94 = v82[v86];
															v136 = 8;
														end
														if (v136 == 5) then
															v86 = v86 + 1;
															v94 = v82[v86];
															v138 = v94[2];
															v136 = 6;
														end
														if (v136 == 4) then
															v86 = v86 + 1;
															v94 = v82[v86];
															v92[v94[2]] = v94[3];
															v136 = 5;
														end
														if (0 == v136) then
															v137 = nil;
															v138 = nil;
															v92[v94[2]] = v92[v94[3]][v94[4]];
															v136 = 1;
														end
														if (v136 == 6) then
															v92[v138](v13(v92, v138 + 1, v94[3]));
															v86 = v86 + 1;
															v94 = v82[v86];
															v136 = 7;
														end
														if (v136 == 8) then
															v86 = v94[3];
															break;
														end
														if (v136 == 2) then
															v86 = v86 + 1;
															v94 = v82[v86];
															v138 = v94[2];
															v136 = 3;
														end
														if (v136 == 1) then
															v86 = v86 + 1;
															v94 = v82[v86];
															v92[v94[2]] = v92[v94[3]][v94[4]];
															v136 = 2;
														end
													end
												else
													local v139 = 0;
													local v140;
													local v141;
													local v142;
													while true do
														if (0 == v139) then
															v140 = v94[2];
															v141 = {v92[v140](v92[v140 + 1])};
															v139 = 1;
														end
														if (v139 == 1) then
															v142 = 0;
															for v286 = v140, v94[4] do
																local v287 = 0;
																while true do
																	if (v287 == 0) then
																		v142 = v142 + 1;
																		v92[v286] = v141[v142];
																		break;
																	end
																end
															end
															break;
														end
													end
												end
											elseif (v95 <= 6) then
												if (v95 == 5) then
													v92[v94[2]] = v94[3] ~= 0;
												else
													local v117 = v94[2];
													v92[v117](v13(v92, v117 + 1, v94[3]));
												end
											elseif (v95 <= 7) then
												v92[v94[2]] = v92[v94[3]][v92[v94[4]]];
											elseif (v95 == 8) then
												v92[v94[2]] = v92[v94[3]][v94[4]];
											else
												for v165 = v94[2], v94[3] do
													v92[v165] = nil;
												end
											end
										elseif (v95 <= 14) then
											if (v95 <= 11) then
												if (v95 > 10) then
													v92[v94[2]] = v66[v94[3]];
												else
													v86 = v94[3];
												end
											elseif (v95 <= 12) then
												local v123 = v94[2];
												local v124 = v94[4];
												local v125 = v123 + 2;
												local v126 = {v92[v123](v92[v123 + 1], v92[v125])};
												for v131 = 1, v124 do
													v92[v125 + v131] = v126[v131];
												end
												local v127 = v126[1];
												if v127 then
													v92[v125] = v127;
													v86 = v94[3];
												else
													v86 = v86 + 1;
												end
											elseif (v95 > 13) then
												if (v92[v94[2]] == v94[4]) then
													v86 = v86 + 1;
												else
													v86 = v94[3];
												end
											elseif not v92[v94[2]] then
												v86 = v86 + 1;
											else
												v86 = v94[3];
											end
										elseif (v95 <= 17) then
											if (v95 <= 15) then
												v92[v94[2]] = {};
											elseif (v95 == 16) then
												v92[v94[2]][v94[3]] = v94[4];
												v86 = v86 + 1;
												v94 = v82[v86];
												v92[v94[2]][v94[3]] = v94[4];
												v86 = v86 + 1;
												v94 = v82[v86];
												v92[v94[2]] = v92[v94[3]];
												v86 = v86 + 1;
												v94 = v82[v86];
												v92[v94[2]] = v66[v94[3]];
												v86 = v86 + 1;
												v94 = v82[v86];
												v92[v94[2]] = v92[v94[3]][v94[4]];
												v86 = v86 + 1;
												v94 = v82[v86];
												v92[v94[2]] = v92[v94[3]][v94[4]];
												v86 = v86 + 1;
												v94 = v82[v86];
												v92[v94[2]] = v94[3];
												v86 = v86 + 1;
												v94 = v82[v86];
												v86 = v94[3];
											else
												v92[v94[2]] = v92[v94[3]];
											end
										elseif (v95 <= 18) then
											v92[v94[2]] = v94[3];
										elseif (v95 > 19) then
											v92[v94[2]][v94[3]] = v94[4];
										else
											local v159 = 0;
											while true do
												if (11 == v159) then
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v159 = 12;
												end
												if (v159 == 8) then
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v159 = 9;
												end
												if (v159 == 27) then
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v159 = 28;
												end
												if (v159 == 6) then
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v159 = 7;
												end
												if (v159 == 15) then
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v159 = 16;
												end
												if (v159 == 4) then
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v159 = 5;
												end
												if (v159 == 25) then
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v159 = 26;
												end
												if (v159 == 24) then
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v159 = 25;
												end
												if (v159 == 0) then
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v159 = 1;
												end
												if (v159 == 16) then
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v159 = 17;
												end
												if (v159 == 12) then
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v159 = 13;
												end
												if (v159 == 13) then
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v159 = 14;
												end
												if (v159 == 17) then
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v159 = 18;
												end
												if (v159 == 3) then
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v159 = 4;
												end
												if (v159 == 2) then
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v159 = 3;
												end
												if (v159 == 9) then
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v159 = 10;
												end
												if (28 == v159) then
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v159 = 29;
												end
												if (v159 == 20) then
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v159 = 21;
												end
												if (29 == v159) then
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													break;
												end
												if (v159 == 26) then
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v159 = 27;
												end
												if (14 == v159) then
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v159 = 15;
												end
												if (v159 == 1) then
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v159 = 2;
												end
												if (10 == v159) then
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v159 = 11;
												end
												if (v159 == 21) then
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v159 = 22;
												end
												if (v159 == 23) then
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v159 = 24;
												end
												if (v159 == 5) then
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v159 = 6;
												end
												if (v159 == 7) then
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v159 = 8;
												end
												if (19 == v159) then
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v159 = 20;
												end
												if (v159 == 18) then
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v159 = 19;
												end
												if (v159 == 22) then
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v86 = v86 + 1;
													v94 = v82[v86];
													v92[v94[2]][v94[3]] = v94[4];
													v159 = 23;
												end
											end
										end
										v86 = v86 + 1;
										break;
									end
									if (v97 == 0) then
										v94 = v82[v86];
										v95 = v94[1];
										v97 = 1;
									end
								end
							end
						end;
					end
				end
			end
			return v30(v29(), {}, v17)(...);
		end
	end
end
return v15("LOL!5D3O00028O00027O004003053O00706169727303043O0067616D6503073O00506C6179657273030B3O004C6F63616C506C6179657203063O0055736572496403043O004B69636B030B3O0050454E44454A4F204C4F4C026O00F03F022O00E0DF0BE2E6412O01023O002747ABE241023O00A2DC99D741022O0080255800C141022O00B0EE9D94F041022O00E0212250EC41022O00C019CF88DC41022O0020C43923EA41022O00C0A275FAD041023O006E4FFFBE41022O00807911D2DB41022O0050AC5E5FF341023O00244005AC41023O00D70D77B441022O00400EC1D6F041022O0080AB965ED141022O00804197CEE841023O00214A69D841022O00C01EBB61D541023O008FA98CD741023O0014F0FCB041022O00C0308921EE41022O0050A18229F041022O00A06D4662E541022O00800470B3D941022O0080EF7B01D141023O009F618FB341022O00803E2FD2D941022O0080F9B6F9CA41023O000DBB0CD641022O00E06B54AAE341023O00A3582BB141022O00A0BABE38EF41022O00C05D7B6CDB41022O006092D670EA41022O00806F310FDD41022O00807B08C0D441023O00763546B741023O0060226EC541022O00604DAD8DE141023O00B6FAB7D941023O002BB73FD341022O00E0244ABCF141022O008070D993C841023O004C5AAFD741022O00802F229CC541022O00A0FACC8AE341022O004095784BDE41023O00A43963D541023O004FBD86B041023O00AA6CB2C141022O0050B1E800F441022O00C04CB755D141022O00C0B617ECDC41022O00A00A62AAE241023O00D72449CA41023O00EFAEF4CE41022O0080B94588C141022O0080953250C441022O00D05C3D21F241022O0060FE1DD6F441023O00339BDBF441022O0080499ADBF441022O00C0DB7B3FEB41023O00D92E6CE841022O0080CFE15DF441022O0020C41E16E241023O00A14C54BD41022O00609B4814E541022O00A0C4491EE441022O00A0D02EB1EE41022O00400427C5D241022O0020A31687ED41022O0080AD1FD4D641022O00C047130BF341022O0080AF7AFEF141022O0020737CA2E441022O00E069E36AE841022O00406E5E01F241022O00A0F57DECEB41022O00E045061FE541022O00C0A27A3AD441008B3O002O123O00014O0009000100043O00260E3O002A0001000200040A3O002A000100120B000500034O0011000600014O000300050002000700040A3O0010000100120B000A00043O002008000A000A0005002008000A000A0006002008000A000A0007000602000A00100001000900040A3O001000012O0005000400013O00040A3O0012000100060C000500080001000200040A3O0008000100060D0004008A0001000100040A3O008A0001002O12000500014O0009000600063O00260E000500160001000100040A3O00160001002O12000600013O00260E000600190001000100040A3O00190001002O12000700013O00260E0007001C0001000100040A3O001C000100120B000800043O00200400080008000500202O00080008000600202O00080008000800122O000A00096O0008000A00016O00013O00044O001C000100040A3O0019000100040A3O008A000100040A3O0016000100040A3O008A000100260E3O002F0001000A00040A3O002F00010020080003000200072O0007000400010003002O123O00023O00260E3O00020001000100040A3O000200012O000F00053O00230030130005000B000C00302O0005000D000C00302O0005000E000C00302O0005000F000C00302O00050010000C00302O00050011000C00302O00050012000C00302O00050013000C00302O00050014000C00302O00050015000C00302O00050016000C00302O00050017000C00302O00050018000C00302O00050019000C00302O0005001A000C00302O0005001B000C00302O0005001C000C00302O0005001D000C00302O0005001E000C00302O0005001F000C00302O00050020000C00302O00050021000C00302O00050022000C00302O00050023000C00302O00050024000C00302O00050025000C00302O00050026000C00302O00050027000C00302O00050028000C00302O00050029000C00302O0005002A000C00302O0005002B000C00302O0005002C000C00302O0005002D000C00302O0005002E000C00302O0005002F000C00302O00050030000C00302O00050031000C00302O00050032000C00302O00050033000C00302O00050034000C00302O00050035000C00302O00050036000C00302O00050037000C00302O00050038000C00302O00050039000C00302O0005003A000C00302O0005003B000C00302O0005003C000C00302O0005003D000C00302O0005003E000C00302O0005003F000C00302O00050040000C00302O00050041000C00302O00050042000C00302O00050043000C00302O00050044000C00302O00050045000C00302O00050046000C00302O00050047000C00302O00050048000C00302O00050049000C00302O0005004A000C00302O0005004B000C00302O0005004C000C00302O0005004D000C00302O0005004E000C00302O0005004F000C00302O00050050000C00302O00050051000C00302O00050052000C00302O00050053000C00302O00050054000C00302O00050055000C00302O00050056000C00302O00050057000C00302O00050058000C00302O00050059000C00302O0005005A000C00302O0005005B000C0030100005005C000C00302O0005005D000C4O000100053O00122O000500043O00202O00050005000500202O00020005000600124O000A3O00044O000200016O00017O00", v9(), ...);