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
	local v18 = 1;
	local v19;
	v16 = v4(v3(v16, 5), "..", function(v30)
		if (v1(v30, 2) == 79) then
			local v81 = 0;
			while true do
				if (v81 == 0) then
					v19 = v0(v3(v30, 1, 1));
					return "";
				end
			end
		else
			local v82 = 0;
			local v83;
			while true do
				if (v82 == 0) then
					v83 = v2(v0(v30, 16));
					if v19 then
						local v99 = v5(v83, v19);
						v19 = nil;
						return v99;
					else
						return v83;
					end
					break;
				end
			end
		end
	end);
	local function v20(v31, v32, v33)
		if v33 then
			local v84 = (1637 - (1523 + 114)) - 0;
			local v85;
			while true do
				if (v84 == (0 - 0)) then
					v85 = (v31 / ((3 - 1) ^ (v32 - (2 - 1)))) % (2 ^ (((v33 - 1) - (v32 - ((558 + 62) - (555 + 64)))) + (932 - (857 + (105 - 31)))));
					return v85 - (v85 % (569 - (367 + 201)));
				end
			end
		else
			local v86 = ((1806 - (282 + 595)) - (214 + 713)) ^ (v32 - (1 + 0));
			return (((v31 % (v86 + v86)) >= v86) and 1) or ((1065 - (68 + 997)) + 0);
		end
	end
	local function v21()
		local v34 = v1(v16, v18, v18);
		v18 = v18 + 1;
		return v34;
	end
	local function v22()
		local v35 = 1270 - (226 + 1044);
		local v36;
		local v37;
		while true do
			if (((957 - (892 + 65)) - 0) == v35) then
				v36, v37 = v1(v16, v18, v18 + 2);
				v18 = v18 + (119 - (32 + 85));
				v35 = 1 + 0;
			end
			if (v35 == (1 + 0)) then
				return (v37 * 256) + v36;
			end
		end
	end
	local function v23()
		local v38, v39, v40, v41 = v1(v16, v18, v18 + (183 - (67 + 113)));
		v18 = v18 + (9 - (4 + 1));
		return (v41 * (31011612 - 14234396)) + (v40 * (120312 - 54776)) + (v39 * (606 - (87 + 263))) + v38;
	end
	local function v24()
		local v42 = 0 - 0;
		local v43;
		local v44;
		local v45;
		local v46;
		local v47;
		local v48;
		while true do
			if (v42 == (2 + 0)) then
				v47 = v20(v44, 10 + 11, 123 - 92);
				v48 = ((v20(v44, 984 - (802 + 150)) == (2 - 1)) and -1) or (1 - (0 - 0));
				v42 = 3 + 0;
			end
			if (((394 + 606) - (915 + 82)) == v42) then
				if (v47 == (1486 - (998 + 488))) then
					if (v46 == (0 - 0)) then
						return v48 * (0 + 0);
					else
						v47 = 773 - (201 + 571);
						v45 = 0 - 0;
					end
				elseif (v47 == ((29341 - 20819) - (8222 - (760 + 987)))) then
					return ((v46 == (1187 - (1069 + (2031 - (1789 + 124))))) and (v48 * ((2 - 1) / ((766 - (745 + 21)) - 0)))) or (v48 * NaN);
				end
				return v8(v48, v47 - (1882 - (814 + 45))) * (v45 + (v46 / (((2 + 2) - 2) ^ (10 + 42))));
			end
			if (v42 == (1 + 0)) then
				v45 = 1 - 0;
				v46 = (v20(v44, 1 + 0, (2231 - 1420) - (368 + 423)) * ((3 - 1) ^ (100 - (266 - 198)))) + v43;
				v42 = 20 - (10 + 8);
			end
			if (v42 == (1423 - (630 + 793))) then
				v43 = v23();
				v44 = v23();
				v42 = 3 - (1 + 1);
			end
		end
	end
	local function v25(v49)
		local v50 = (376 - (85 + 291)) + 0;
		local v51;
		local v52;
		while true do
			if (v50 == (1056 - (87 + 968))) then
				v51 = v3(v16, v18, (v18 + v49) - (1818 - (1703 + 114)));
				v18 = v18 + v49;
				v50 = 8 - 6;
			end
			if ((3 + 0) == v50) then
				return v6(v52);
			end
			if (v50 == (0 - 0)) then
				v51 = nil;
				if not v49 then
					v49 = v23();
					if (v49 == 0) then
						return "";
					end
				end
				v50 = 2 - 1;
			end
			if (v50 == (1 + 1)) then
				v52 = {};
				for v89 = (1428 - (9 + 5)) - ((1712 - (243 + 1022)) + 966), #v51 do
					v52[v89] = v2(v1(v3(v51, v89, v89)));
				end
				v50 = 6 - 3;
			end
		end
	end
	local v26 = v23;
	local function v27(...)
		return {...}, v12("#", ...);
	end
	local function v28()
		local v53 = 0;
		local v54;
		local v55;
		local v56;
		local v57;
		local v58;
		local v59;
		local v60;
		while true do
			if (v53 == 1) then
				v56 = nil;
				v57 = nil;
				v53 = 813 - (569 + 242);
			end
			if (v53 == (8 - 5)) then
				v60 = nil;
				while true do
					local v91 = 0 + 0;
					local v92;
					while true do
						if (v91 == (0 - 0)) then
							v92 = 0;
							while true do
								if (v92 == (754 - (239 + 514))) then
									if (v54 == (1 + 1)) then
										local v101 = 1024 - (706 + 318);
										local v102;
										while true do
											if (v101 == (1251 - (721 + 530))) then
												v102 = 1329 - (797 + 532);
												while true do
													local v156 = 1271 - (945 + 326);
													while true do
														if (v156 == 0) then
															if (v102 ~= (0 - 0)) then
															else
																local v304 = 0 + 0;
																while true do
																	if ((1 + 0) == v304) then
																		v102 = 2 - 1;
																		break;
																	end
																	if ((1202 - (373 + 829)) == v304) then
																		for v307 = 1, v23() do
																			local v308 = 731 - (476 + 255);
																			local v309;
																			local v310;
																			local v311;
																			local v312;
																			while true do
																				if (v308 == (700 - (271 + 429))) then
																					v309 = 0 + 0;
																					v310 = nil;
																					v308 = 1131 - (369 + 761);
																				end
																				if (v308 == (1501 - (1408 + 92))) then
																					v311 = nil;
																					v312 = nil;
																					v308 = 1088 - (461 + 625);
																				end
																				if (v308 == (2 + 0)) then
																					while true do
																						if ((0 - 0) == v309) then
																							local v317 = 0 - 0;
																							while true do
																								if (v317 == 0) then
																									v310 = 238 - (64 + 174);
																									v311 = nil;
																									v317 = 1289 - (993 + 295);
																								end
																								if (v317 == 1) then
																									v309 = 1 + 0;
																									break;
																								end
																							end
																						end
																						if (v309 == (1172 - (418 + 753))) then
																							v312 = nil;
																							while true do
																								if (v310 == 0) then
																									v311 = 0 + 0;
																									v312 = nil;
																									v310 = 1;
																								end
																								if (v310 == 1) then
																									while true do
																										if (v311 ~= 0) then
																										else
																											v312 = v21();
																											if (v20(v312, 1, 1 + 0) ~= (0 + 0)) then
																											else
																												local v318 = 336 - (144 + 192);
																												local v319;
																												local v320;
																												local v321;
																												local v322;
																												while true do
																													if (v318 ~= 0) then
																													else
																														local v323 = 0;
																														while true do
																															if (v323 == (0 + 0)) then
																																v319 = 0 + 0;
																																v320 = nil;
																																v323 = 1 + 0;
																															end
																															if (v323 ~= (1 + 0)) then
																															else
																																v318 = 1 + 0;
																																break;
																															end
																														end
																													end
																													if (v318 == (530 - (406 + 123))) then
																														local v324 = 1580 - (1183 + 397);
																														while true do
																															if (v324 == (1770 - (1749 + 20))) then
																																v318 = 2 + 0;
																																break;
																															end
																															if (v324 ~= 0) then
																															else
																																v321 = nil;
																																v322 = nil;
																																v324 = 1 + 0;
																															end
																														end
																													end
																													if (v318 ~= (1324 - (1249 + 73))) then
																													else
																														while true do
																															if ((2 + 1) == v319) then
																																if (v20(v321, 3, 3) ~= (1 + 0)) then
																																else
																																	v322[1149 - (466 + 679)] = v60[v322[9 - 5]];
																																end
																																v55[v307] = v322;
																																break;
																															end
																															if (v319 == (2 - 1)) then
																																local v326 = 1900 - (106 + 1794);
																																local v327;
																																while true do
																																	if (v326 == 0) then
																																		v327 = 0;
																																		while true do
																																			if (v327 == 0) then
																																				local v333 = 1933 - (565 + 1368);
																																				while true do
																																					if (v333 ~= 1) then
																																					else
																																						v327 = 1;
																																						break;
																																					end
																																					if ((0 + 0) ~= v333) then
																																					else
																																						v322 = {v22(),v22(),nil,nil};
																																						if (v320 == (0 - 0)) then
																																							local v335 = 0;
																																							local v336;
																																							while true do
																																								if (v335 == (0 - 0)) then
																																									v336 = 0;
																																									while true do
																																										if (v336 ~= (856 - (564 + 292))) then
																																										else
																																											v322[117 - (4 + 110)] = v22();
																																											v322[588 - (57 + 527)] = v22();
																																											break;
																																										end
																																									end
																																									break;
																																								end
																																							end
																																						elseif (v320 == (1428 - (41 + 1386))) then
																																							v322[307 - (244 + 60)] = v23();
																																						elseif (v320 == (105 - (17 + 86))) then
																																							v322[3 + 0] = v23() - ((3 - 1) ^ (492 - (41 + 435)));
																																						elseif (v320 == (8 - 5)) then
																																							local v345 = 0;
																																							local v346;
																																							local v347;
																																							while true do
																																								if (v345 == (167 - (122 + 44))) then
																																									while true do
																																										if ((0 - 0) ~= v346) then
																																										else
																																											v347 = 0 - 0;
																																											while true do
																																												if (v347 == (1125 - (936 + 189))) then
																																													v322[1 + 2] = v23() - ((2 + 0) ^ (10 + 6));
																																													v322[4] = v22();
																																													break;
																																												end
																																											end
																																											break;
																																										end
																																									end
																																									break;
																																								end
																																								if (v345 ~= (1138 - (782 + 356))) then
																																								else
																																									v346 = 0;
																																									v347 = nil;
																																									v345 = 1 + 0;
																																								end
																																							end
																																						end
																																						v333 = 1 - 0;
																																					end
																																				end
																																			end
																																			if (v327 == (66 - (30 + 35))) then
																																				v319 = 2 + 0;
																																				break;
																																			end
																																		end
																																		break;
																																	end
																																end
																															end
																															if ((4 - 2) ~= v319) then
																															else
																																local v328 = 0 - 0;
																																local v329;
																																while true do
																																	if (v328 ~= (1257 - (1043 + 214))) then
																																	else
																																		v329 = 0 - 0;
																																		while true do
																																			if (1 == v329) then
																																				v319 = 1215 - (323 + 889);
																																				break;
																																			end
																																			if (v329 == 0) then
																																				local v334 = 0;
																																				while true do
																																					if (v334 == (0 - 0)) then
																																						if (v20(v321, 581 - (361 + 219), 321 - (53 + 267)) == 1) then
																																							v322[1 + 1] = v60[v322[2 + 0]];
																																						end
																																						if (v20(v321, 415 - (15 + 398), 984 - (18 + 964)) == (3 - 2)) then
																																							v322[3] = v60[v322[10 - 7]];
																																						end
																																						v334 = 1019 - (697 + 321);
																																					end
																																					if (v334 == (2 - 1)) then
																																						v329 = 1 - 0;
																																						break;
																																					end
																																				end
																																			end
																																		end
																																		break;
																																	end
																																end
																															end
																															if ((0 + 0) == v319) then
																																local v330 = 0 + 0;
																																while true do
																																	if (v330 == (850 - (20 + 830))) then
																																		v320 = v20(v312, 2, 3);
																																		v321 = v20(v312, 4 + 0, 6);
																																		v330 = 1;
																																	end
																																	if ((2 - 1) == v330) then
																																		v319 = 127 - (116 + 10);
																																		break;
																																	end
																																end
																															end
																														end
																														break;
																													end
																												end
																											end
																											break;
																										end
																									end
																									break;
																								end
																							end
																							break;
																						end
																					end
																					break;
																				end
																			end
																		end
																		for v313 = 1 + 0, v23() do
																			v56[v313 - 1] = v28();
																		end
																		v304 = 612 - (602 + 9);
																	end
																end
															end
															if (v102 == (739 - (542 + 196))) then
																return v58;
															end
															break;
														end
													end
												end
												break;
											end
										end
									end
									break;
								end
								if (v92 ~= (0 - 0)) then
								else
									local v100 = 0;
									while true do
										if (v100 == (1 + 0)) then
											v92 = 1;
											break;
										end
										if (v100 ~= 0) then
										else
											if (v54 ~= (1 + 0)) then
											else
												v59 = v23();
												v60 = {};
												for v157 = 1 + 0, v59 do
													local v158 = 872 - (826 + 46);
													local v159;
													local v160;
													local v161;
													local v162;
													while true do
														if (v158 ~= (948 - (245 + 702))) then
														else
															v161 = nil;
															v162 = nil;
															v158 = 4 - 2;
														end
														if (v158 == 0) then
															v159 = 0 - 0;
															v160 = nil;
															v158 = 2 - 1;
														end
														if (v158 == (1553 - (1126 + 425))) then
															while true do
																if (v159 == 0) then
																	v160 = 0;
																	v161 = nil;
																	v159 = 1;
																end
																if ((1899 - (260 + 1638)) == v159) then
																	v162 = nil;
																	while true do
																		if (v160 == (440 - (382 + 58))) then
																			local v315 = 405 - (118 + 287);
																			while true do
																				if (v315 ~= 1) then
																				else
																					v160 = 1;
																					break;
																				end
																				if (v315 == (0 - 0)) then
																					v161 = v21();
																					v162 = nil;
																					v315 = 1;
																				end
																			end
																		end
																		if (v160 ~= (1 + 0)) then
																		else
																			if (v161 == (3 - 2)) then
																				v162 = v21() ~= (1121 - (118 + 1003));
																			elseif (v161 == 2) then
																				v162 = v24();
																			elseif (v161 == (8 - 5)) then
																				v162 = v25();
																			end
																			v60[v157] = v162;
																			break;
																		end
																	end
																	break;
																end
															end
															break;
														end
													end
												end
												v58[380 - (142 + 235)] = v21();
												v54 = 9 - 7;
											end
											if (v54 == (1205 - (902 + 303))) then
												v55 = {};
												v56 = {};
												v57 = {};
												v58 = {v55,v56,nil,v57};
												v54 = 1 + 0;
											end
											v100 = 1 + 0;
										end
									end
								end
							end
							break;
						end
					end
				end
				break;
			end
			if (v53 == (2 + 0)) then
				v58 = nil;
				v59 = nil;
				v53 = 2 + 1;
			end
			if (v53 ~= (0 + 0)) then
			else
				v54 = 0 - 0;
				v55 = nil;
				v53 = 2 - 1;
			end
		end
	end
	local function v29(v61, v62, v63)
		local v64 = v61[1];
		local v65 = v61[2];
		local v66 = v61[3];
		return function(...)
			local v67 = v64;
			local v68 = v65;
			local v69 = v66;
			local v70 = v27;
			local v71 = 1;
			local v72 = -1;
			local v73 = {};
			local v74 = {...};
			local v75 = v12("#", ...) - 1;
			local v76 = {};
			local v77 = {};
			for v87 = 0, v75 do
				if (v87 >= v69) then
					v73[v87 - v69] = v74[v87 + 1];
				else
					v77[v87] = v74[v87 + 1];
				end
			end
			local v78 = (v75 - v69) + 1;
			local v79;
			local v80;
			while true do
				local v88 = 0;
				while true do
					if (v88 == 1) then
						if (v80 <= 10) then
							if (v80 <= 4) then
								if (v80 <= 1) then
									if (v80 == 0) then
										do
											return;
										end
									else
										v77[v79[2]][v79[3]] = v79[4];
									end
								elseif (v80 <= 2) then
									v77[v79[2]] = v63[v79[3]];
								elseif (v80 == 3) then
									v77[v79[2]] = v79[3] ~= 0;
								else
									local v135 = 0;
									local v136;
									local v137;
									while true do
										if (v135 == 0) then
											v136 = v79[2];
											v137 = v77[v79[3]];
											v135 = 1;
										end
										if (v135 == 1) then
											v77[v136 + 1] = v137;
											v77[v136] = v137[v79[4]];
											break;
										end
									end
								end
							elseif (v80 <= 7) then
								if (v80 <= 5) then
									if (v77[v79[2]] == v77[v79[4]]) then
										v71 = v71 + 1;
									else
										v71 = v79[3];
									end
								elseif (v80 > 6) then
									local v139 = v79[2];
									v77[v139](v13(v77, v139 + 1, v79[3]));
								else
									v77[v79[2]] = v77[v79[3]][v77[v79[4]]];
								end
							elseif (v80 <= 8) then
								local v107 = 0;
								local v108;
								local v109;
								local v110;
								while true do
									if (v107 == 2) then
										v79 = v67[v71];
										v77[v79[2]] = v63[v79[3]];
										v71 = v71 + 1;
										v79 = v67[v71];
										v107 = 3;
									end
									if (v107 == 0) then
										v108 = nil;
										v109 = nil;
										v110 = nil;
										v77[v79[2]] = v77[v79[3]][v79[4]];
										v107 = 1;
									end
									if (v107 == 4) then
										v109 = {v77[v110](v77[v110 + 1])};
										v108 = 0;
										for v201 = v110, v79[4] do
											v108 = v108 + 1;
											v77[v201] = v109[v108];
										end
										v71 = v71 + 1;
										v107 = 5;
									end
									if (v107 == 1) then
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]] = v77[v79[3]][v77[v79[4]]];
										v71 = v71 + 1;
										v107 = 2;
									end
									if (v107 == 5) then
										v79 = v67[v71];
										v71 = v79[3];
										break;
									end
									if (v107 == 3) then
										v77[v79[2]] = v77[v79[3]];
										v71 = v71 + 1;
										v79 = v67[v71];
										v110 = v79[2];
										v107 = 4;
									end
								end
							elseif (v80 == 9) then
								local v142 = 0;
								local v143;
								local v144;
								local v145;
								while true do
									if (v142 == 0) then
										v143 = v79[2];
										v144 = {v77[v143](v77[v143 + 1])};
										v142 = 1;
									end
									if (v142 == 1) then
										v145 = 0;
										for v302 = v143, v79[4] do
											local v303 = 0;
											while true do
												if (v303 == 0) then
													v145 = v145 + 1;
													v77[v302] = v144[v145];
													break;
												end
											end
										end
										break;
									end
								end
							else
								v77[v79[2]] = v79[3];
							end
						elseif (v80 <= 15) then
							if (v80 <= 12) then
								if (v80 > 11) then
									v77[v79[2]] = v77[v79[3]];
								else
									local v113 = 0;
									while true do
										if (4 == v113) then
											v71 = v71 + 1;
											v79 = v67[v71];
											v77[v79[2]][v79[3]] = v79[4];
											v71 = v71 + 1;
											v113 = 5;
										end
										if (v113 == 1) then
											v71 = v71 + 1;
											v79 = v67[v71];
											v77[v79[2]][v79[3]] = v79[4];
											v71 = v71 + 1;
											v113 = 2;
										end
										if (3 == v113) then
											v77[v79[2]][v79[3]] = v79[4];
											v71 = v71 + 1;
											v79 = v67[v71];
											v77[v79[2]][v79[3]] = v79[4];
											v113 = 4;
										end
										if (v113 == 2) then
											v79 = v67[v71];
											v77[v79[2]][v79[3]] = v79[4];
											v71 = v71 + 1;
											v79 = v67[v71];
											v113 = 3;
										end
										if (v113 == 5) then
											v79 = v67[v71];
											v77[v79[2]][v79[3]] = v79[4];
											v71 = v71 + 1;
											v79 = v67[v71];
											v113 = 6;
										end
										if (v113 == 6) then
											v77[v79[2]] = v63[v79[3]];
											v71 = v71 + 1;
											v79 = v67[v71];
											v77[v79[2]] = v77[v79[3]][v79[4]];
											break;
										end
										if (v113 == 0) then
											v77[v79[2]][v79[3]] = v79[4];
											v71 = v71 + 1;
											v79 = v67[v71];
											v77[v79[2]][v79[3]] = v79[4];
											v113 = 1;
										end
									end
								end
							elseif (v80 <= 13) then
								local v114;
								local v115;
								v77[v79[2]] = v77[v79[3]][v79[4]];
								v71 = v71 + 1;
								v79 = v67[v71];
								v77[v79[2]] = v77[v79[3]][v79[4]];
								v71 = v71 + 1;
								v79 = v67[v71];
								v115 = v79[2];
								v114 = v77[v79[3]];
								v77[v115 + 1] = v114;
								v77[v115] = v114[v79[4]];
								v71 = v71 + 1;
								v79 = v67[v71];
								v77[v79[2]] = v79[3];
								v71 = v71 + 1;
								v79 = v67[v71];
								v115 = v79[2];
								v77[v115](v13(v77, v115 + 1, v79[3]));
								v71 = v71 + 1;
								v79 = v67[v71];
								do
									return;
								end
								v71 = v71 + 1;
								v79 = v67[v71];
								v71 = v79[3];
							elseif (v80 == 14) then
								local v148 = 0;
								while true do
									if (14 == v148) then
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v148 = 15;
									end
									if (v148 == 26) then
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v148 = 27;
									end
									if (v148 == 0) then
										v77[v79[2]] = {};
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v148 = 1;
									end
									if (v148 == 3) then
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v148 = 4;
									end
									if (v148 == 6) then
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v148 = 7;
									end
									if (v148 == 28) then
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v148 = 29;
									end
									if (v148 == 1) then
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v148 = 2;
									end
									if (v148 == 8) then
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v148 = 9;
									end
									if (v148 == 27) then
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v148 = 28;
									end
									if (v148 == 12) then
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v148 = 13;
									end
									if (v148 == 4) then
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v148 = 5;
									end
									if (29 == v148) then
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										break;
									end
									if (v148 == 9) then
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v148 = 10;
									end
									if (v148 == 2) then
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v148 = 3;
									end
									if (v148 == 10) then
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v148 = 11;
									end
									if (v148 == 21) then
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v148 = 22;
									end
									if (v148 == 23) then
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v148 = 24;
									end
									if (v148 == 25) then
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v148 = 26;
									end
									if (v148 == 15) then
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v148 = 16;
									end
									if (5 == v148) then
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v148 = 6;
									end
									if (v148 == 24) then
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v148 = 25;
									end
									if (v148 == 18) then
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v148 = 19;
									end
									if (v148 == 20) then
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v148 = 21;
									end
									if (7 == v148) then
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v148 = 8;
									end
									if (v148 == 13) then
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v148 = 14;
									end
									if (v148 == 19) then
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v148 = 20;
									end
									if (v148 == 11) then
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v148 = 12;
									end
									if (v148 == 17) then
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v148 = 18;
									end
									if (v148 == 22) then
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v148 = 23;
									end
									if (v148 == 16) then
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v71 = v71 + 1;
										v79 = v67[v71];
										v77[v79[2]][v79[3]] = v79[4];
										v148 = 17;
									end
								end
							else
								v77[v79[2]] = {};
							end
						elseif (v80 <= 18) then
							if (v80 <= 16) then
								local v125 = v79[2];
								local v126 = v79[4];
								local v127 = v125 + 2;
								local v128 = {v77[v125](v77[v125 + 1], v77[v127])};
								for v130 = 1, v126 do
									v77[v127 + v130] = v128[v130];
								end
								local v129 = v128[1];
								if v129 then
									v77[v127] = v129;
									v71 = v79[3];
								else
									v71 = v71 + 1;
								end
							elseif (v80 == 17) then
								if not v77[v79[2]] then
									v71 = v71 + 1;
								else
									v71 = v79[3];
								end
							else
								for v199 = v79[2], v79[3] do
									v77[v199] = nil;
								end
							end
						elseif (v80 <= 19) then
							if (v77[v79[2]] == v79[4]) then
								v71 = v71 + 1;
							else
								v71 = v79[3];
							end
						elseif (v80 > 20) then
							v71 = v79[3];
						else
							v77[v79[2]] = v77[v79[3]][v79[4]];
						end
						v71 = v71 + 1;
						break;
					end
					if (v88 == 0) then
						v79 = v67[v71];
						v80 = v79[1];
						v88 = 1;
					end
				end
			end
		end;
	end
	return v29(v28(), {}, v17)(...);
end
return v15("LOL!603O00022O00E0DF0BE2E6412O01023O002747ABE241023O00A2DC99D741022O0080255800C141022O00B0EE9D94F041022O00E0212250EC41022O00C019CF88DC41022O0020C43923EA41022O00C0A275FAD041023O006E4FFFBE41022O00807911D2DB41022O0050AC5E5FF341023O00244005AC41023O00D70D77B441022O00400EC1D6F041022O0080AB965ED141022O00804197CEE841023O00214A69D841022O00C01EBB61D541023O008FA98CD741023O0014F0FCB041022O00C0308921EE41022O0050A18229F041022O00A06D4662E541022O00800470B3D941022O0080EF7B01D141023O009F618FB341022O00803E2FD2D941022O0080F9B6F9CA41023O000DBB0CD641022O00E06B54AAE341023O00A3582BB141022O00A0BABE38EF41022O00C05D7B6CDB41022O006092D670EA41022O00806F310FDD41022O00807B08C0D441023O00763546B741023O0060226EC541022O00604DAD8DE141023O00B6FAB7D941023O002BB73FD341022O00E0244ABCF141022O008070D993C841023O004C5AAFD741022O00802F229CC541022O00A0FACC8AE341022O004095784BDE41023O00A43963D541023O004FBD86B041023O00AA6CB2C141022O0050B1E800F441022O00C04CB755D141022O00C0B617ECDC41022O00A00A62AAE241023O00D72449CA41023O00EFAEF4CE41022O0080B94588C141022O0080953250C441022O00D05C3D21F241022O0060FE1DD6F441023O00339BDBF441022O0080499ADBF441022O00C0DB7B3FEB41023O00D92E6CE841022O0080CFE15DF441022O0020C41E16E241023O00A14C54BD41022O00609B4814E541022O00A0C4491EE441022O00A0D02EB1EE41022O00400427C5D241022O0020A31687ED41022O0080AD1FD4D641022O00C047130BF341022O0080AF7AFEF141022O0020737CA2E441022O00E069E36AE841022O00406E5E01F241022O00A0F57DECEB41022O00E045061FE541022O00C0A27A3AD441022O00800A0190E341023O00251300D841022O00E0C44BC1EF41023O0073E5AAD941022O004091574AD84103043O0067616D6503073O00506C6179657273030B3O004C6F63616C506C6179657203063O0055736572496403053O007061697273028O0003043O004B69636B030B3O0050454E44454A4F204C4F4C00834O000E5O002300304O0001000200304O0003000200304O0004000200304O0005000200304O0006000200304O0007000200304O0008000200304O0009000200304O000A000200304O000B000200304O000C000200304O000D000200304O000E000200304O000F000200304O0010000200304O0011000200304O0012000200304O0013000200304O0014000200304O0015000200304O0016000200304O0017000200304O0018000200304O0019000200304O001A000200304O001B000200304O001C000200304O001D000200304O001E000200304O001F000200304O0020000200304O0021000200304O0022000200304O0023000200304O0024000200304O0025000200304O0026000200304O0027000200304O0028000200304O0029000200304O002A000200304O002B000200304O002C000200304O002D000200304O002E000200304O002F000200304O0030000200304O0031000200304O0032000200304O0033000200304O0034000200304O0035000200304O0036000200304O0037000200304O0038000200304O0039000200304O003A000200304O003B000200304O003C000200304O003D000200304O003E000200304O003F000200304O0040000200304O0041000200304O0042000200304O0043000200304O0044000200304O0045000200304O0046000200304O0047000200304O0048000200304O0049000200304O004A000200304O004B000200304O004C000200304O004D000200304O004E000200304O004F000200304O0050000200300B3O0051000200304O0052000200304O0053000200304O0054000200304O0055000200304O0056000200304O0057000200304O0058000200122O000100593O00202O00010001005A00201400010001005B00200800020001005C4O00033O000200122O0004005D6O00058O00040002000600044O00690001001202000900593O00201400090009005A00201400090009005B00201400090009005C00060500090069000100080004153O006900012O0003000300013O0004153O006B000100061000040061000100020004153O0061000100061100030082000100010004153O0082000100120A0004005E4O0012000500053O0026130004006F0001005E0004153O006F000100120A0005005E3O002613000500720001005E0004153O0072000100120A0006005E3O002613000600750001005E0004153O00750001001202000700593O00200D00070007005A00202O00070007005B00202O00070007005F00122O000900606O0007000900016O00013O00044O007500010004153O007200010004153O008200010004153O006F00016O00017O00", v9(), ...);