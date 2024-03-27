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
			v19 = v0(v3(v30, 1, 1));
			return "";
		else
			local v70 = v2(v0(v30, 16));
			if v19 then
				local v76 = v5(v70, v19);
				v19 = nil;
				return v76;
			else
				return v70;
			end
		end
	end);
	local function v20(v31, v32, v33)
		if v33 then
			local v71 = (v31 / ((5 - (1 + 2)) ^ (v32 - (2 - 1)))) % ((1 + 1) ^ (((v33 - 1) - (v32 - (1 - 0))) + (2 - 1)));
			return v71 - (v71 % (620 - (555 + 64)));
		else
			local v72 = (879 - (282 + 595)) ^ (v32 - (932 - ((2494 - (1523 + 114)) + 74)));
			return (((v31 % (v72 + v72)) >= v72) and (569 - (367 + 201))) or (927 - (214 + 641 + 72));
		end
	end
	local function v21()
		local v34 = v1(v16, v18, v18);
		v18 = v18 + 1;
		return v34;
	end
	local function v22()
		local v35 = 0 - 0;
		local v36;
		local v37;
		while true do
			if (v35 == (1 - 0)) then
				return (v37 * (1321 - ((124 - 56) + 997))) + v36;
			end
			if (v35 == (1270 - (226 + 1044))) then
				v36, v37 = v1(v16, v18, v18 + (959 - ((1242 - (87 + 263)) + 65)));
				v18 = v18 + (4 - 2);
				v35 = (181 - (67 + 113)) - 0;
			end
		end
	end
	local function v23()
		local v38, v39, v40, v41 = v1(v16, v18, v18 + 3);
		v18 = v18 + 3 + 1;
		return (v41 * (41190819 - 24413603)) + (v40 * (48199 + 17337)) + (v39 * (1017 - 761)) + v38;
	end
	local function v24()
		local v42 = v23();
		local v43 = v23();
		local v44 = 953 - (802 + 150);
		local v45 = (v20(v43, 2 - 1, 36 - 16) * ((2 + (0 - 0)) ^ (1029 - (915 + 82)))) + v42;
		local v46 = v20(v43, (1545 - (998 + 488)) - 38, 19 + 12);
		local v47 = ((v20(v43, 41 - 9) == (1188 - (1069 + 118))) and -((1 + 1) - 1)) or (1 - 0);
		if (v46 == (0 + 0)) then
			if (v45 == 0) then
				return v47 * (0 - 0);
			else
				local v77 = 0;
				while true do
					if (v77 == (0 + 0)) then
						v46 = 792 - (302 + 66 + 423);
						v44 = 0 - 0;
						break;
					end
				end
			end
		elseif (v46 == ((2503 - (145 + 293)) - (10 + 8))) then
			return ((v45 == (1138 - (116 + 1022))) and (v47 * (1 / (0 - 0)))) or (v47 * NaN);
		end
		return v8(v47, v46 - (1465 - (416 + 26))) * (v44 + (v45 / ((6 - 4) ^ ((453 - (44 + 386)) + 29))));
	end
	local function v25(v48)
		local v49;
		if not v48 then
			v48 = v23();
			if (v48 == (0 - 0)) then
				return "";
			end
		end
		v49 = v3(v16, v18, (v18 + v48) - (1 + 0));
		v18 = v18 + v48;
		local v50 = {};
		for v68 = 3 - 2, #v49 do
			v50[v68] = v2(v1(v3(v49, v68, v68)));
		end
		return v6(v50);
	end
	local v26 = v23;
	local function v27(...)
		return {...}, v12("#", ...);
	end
	local function v28()
		local v51 = 0 + 0;
		local v52;
		local v53;
		local v54;
		local v55;
		local v56;
		local v57;
		local v58;
		local v59;
		local v60;
		while true do
			if (v51 == (3 - 1)) then
				v56 = nil;
				v57 = nil;
				v51 = 3;
			end
			if (v51 == (1691 - (209 + 1481))) then
				v54 = nil;
				v55 = nil;
				v51 = 2;
			end
			if ((11 - 7) ~= v51) then
			else
				v60 = nil;
				while true do
					if (1 ~= v52) then
					else
						local v95 = 0 + 0;
						while true do
							if (v95 == (1637 - (1373 + 263))) then
								v52 = 1002 - (451 + 549);
								break;
							end
							if (v95 == (0 + 0)) then
								v55 = nil;
								v56 = nil;
								v95 = 1 - 0;
							end
						end
					end
					if (v52 ~= (0 - 0)) then
					else
						local v96 = 0;
						while true do
							if ((1384 - (746 + 638)) ~= v96) then
							else
								v53 = 0;
								v54 = nil;
								v96 = 1 + 0;
							end
							if (v96 == (2 - 1)) then
								v52 = 1 - 0;
								break;
							end
						end
					end
					if (v52 == (345 - (218 + 123))) then
						while true do
							if (v53 == (1584 - (1535 + 46))) then
								v60 = nil;
								while true do
									local v106 = 0 + 0;
									local v107;
									while true do
										if (v106 == (0 + 0)) then
											v107 = 0;
											while true do
												if (v107 ~= (560 - (306 + 254))) then
												else
													local v159 = 0 + 0;
													local v160;
													while true do
														if (v159 ~= (1329 - (797 + 532))) then
														else
															v160 = 0 - 0;
															while true do
																if (v160 ~= (1468 - (899 + 568))) then
																else
																	v107 = 1;
																	break;
																end
																if (v160 ~= 0) then
																else
																	local v177 = 0 + 0;
																	while true do
																		if (v177 == (1 + 0)) then
																			v160 = 2 - 1;
																			break;
																		end
																		if (v177 ~= (603 - (268 + 335))) then
																		else
																			if (v54 == (1203 - (373 + 829))) then
																				local v178 = 0;
																				while true do
																					if (v178 ~= 0) then
																					else
																						v59 = v23();
																						v60 = {};
																						v178 = 291 - (60 + 230);
																					end
																					if (v178 == (574 - (426 + 146))) then
																						v54 = 1132 - (369 + 761);
																						break;
																					end
																					if (v178 ~= (1 + 0)) then
																					else
																						local v183 = 0 - 0;
																						while true do
																							if (v183 ~= (1 - 0)) then
																							else
																								v178 = 2;
																								break;
																							end
																							if (v183 ~= (0 + 0)) then
																							else
																								for v186 = 1, v59 do
																									local v187 = 0 + 0;
																									local v188;
																									local v189;
																									while true do
																										if (0 ~= v187) then
																										else
																											local v191 = 1456 - (282 + 1174);
																											while true do
																												if (0 == v191) then
																													v188 = v21();
																													v189 = nil;
																													v191 = 1;
																												end
																												if (v191 ~= (812 - (569 + 242))) then
																												else
																													v187 = 1;
																													break;
																												end
																											end
																										end
																										if (1 ~= v187) then
																										else
																											if (v188 == (2 - 1)) then
																												v189 = v21() ~= 0;
																											elseif (v188 == (218 - (42 + 174))) then
																												v189 = v24();
																											elseif (v188 == 3) then
																												v189 = v25();
																											end
																											v60[v186] = v189;
																											break;
																										end
																									end
																								end
																								v58[3 + 0] = v21();
																								v183 = 1 + 0;
																							end
																						end
																					end
																				end
																			end
																			if ((1026 - (706 + 318)) == v54) then
																				local v179 = 1251 - (721 + 530);
																				local v180;
																				while true do
																					if (v179 ~= (1271 - (945 + 326))) then
																					else
																						v180 = 0;
																						while true do
																							local v184 = 0 - 0;
																							while true do
																								if (v184 == (0 + 0)) then
																									if (v180 == 1) then
																										return v58;
																									end
																									if (v180 == (700 - (271 + 429))) then
																										local v190 = 0 + 0;
																										while true do
																											if (v190 ~= (1501 - (1408 + 92))) then
																											else
																												v180 = 1;
																												break;
																											end
																											if (v190 == (1086 - (461 + 625))) then
																												local v193 = 0;
																												while true do
																													if (v193 == 1) then
																														v190 = 1289 - (993 + 295);
																														break;
																													end
																													if (v193 == (1975 - (1913 + 62))) then
																														for v194 = 1, v23() do
																															local v195 = 0 + 0;
																															local v196;
																															while true do
																																if (v195 == (0 + 0)) then
																																	v196 = v21();
																																	if (v20(v196, 2 - 1, 1934 - (565 + 1368)) ~= (1171 - (418 + 753))) then
																																	else
																																		local v199 = 0;
																																		local v200;
																																		local v201;
																																		local v202;
																																		local v203;
																																		while true do
																																			if (v199 == (1 + 0)) then
																																				v202 = nil;
																																				v203 = nil;
																																				v199 = 1 + 1;
																																			end
																																			if (v199 == (1661 - (1477 + 184))) then
																																				v200 = 0;
																																				v201 = nil;
																																				v199 = 1 + 0;
																																			end
																																			if (v199 ~= (2 - 0)) then
																																			else
																																				while true do
																																					if (v200 == 1) then
																																						local v204 = 0 + 0;
																																						local v205;
																																						while true do
																																							if (v204 == (0 + 0)) then
																																								v205 = 529 - (406 + 123);
																																								while true do
																																									if (v205 == (0 - 0)) then
																																										v203 = {v22(),v22(),nil,nil};
																																										if (v201 == 0) then
																																											local v217 = 0;
																																											local v218;
																																											while true do
																																												if (v217 == (0 + 0)) then
																																													v218 = 0;
																																													while true do
																																														if (v218 ~= (476 - (41 + 435))) then
																																														else
																																															v203[2 + 1] = v22();
																																															v203[1149 - (466 + 679)] = v22();
																																															break;
																																														end
																																													end
																																													break;
																																												end
																																											end
																																										elseif (v201 == 1) then
																																											v203[6 - 3] = v23();
																																										elseif (v201 == (2 + 0)) then
																																											v203[8 - 5] = v23() - ((1902 - (106 + 1794)) ^ (6 + 10));
																																										elseif (v201 ~= (1 + 2)) then
																																										else
																																											local v223 = 0 - 0;
																																											local v224;
																																											while true do
																																												if (v223 == (0 - 0)) then
																																													v224 = 114 - (4 + 110);
																																													while true do
																																														if (v224 ~= 0) then
																																														else
																																															v203[3] = v23() - (2 ^ 16);
																																															v203[588 - (57 + 527)] = v22();
																																															break;
																																														end
																																													end
																																													break;
																																												end
																																											end
																																										end
																																										v205 = 1428 - (41 + 1386);
																																									end
																																									if (v205 == 1) then
																																										v200 = 2;
																																										break;
																																									end
																																								end
																																								break;
																																							end
																																						end
																																					end
																																					if (v200 ~= (103 - (17 + 86))) then
																																					else
																																						local v206 = 0 - 0;
																																						local v207;
																																						while true do
																																							if (v206 ~= (0 + 0)) then
																																							else
																																								v207 = 1092 - (975 + 117);
																																								while true do
																																									if ((1876 - (157 + 1718)) ~= v207) then
																																									else
																																										v200 = 1 + 0;
																																										break;
																																									end
																																									if ((0 - 0) == v207) then
																																										local v216 = 0 - 0;
																																										while true do
																																											if (v216 ~= (0 - 0)) then
																																											else
																																												v201 = v20(v196, 1020 - (697 + 321), 7 - 4);
																																												v202 = v20(v196, 8 - 4, 172 - (122 + 44));
																																												v216 = 1;
																																											end
																																											if (v216 == 1) then
																																												v207 = 1;
																																												break;
																																											end
																																										end
																																									end
																																								end
																																								break;
																																							end
																																						end
																																					end
																																					if (v200 == 3) then
																																						if (v20(v202, 5 - 2, 3) ~= 1) then
																																						else
																																							v203[2 + 2] = v60[v203[4]];
																																						end
																																						v55[v194] = v203;
																																						break;
																																					end
																																					if (v200 ~= 2) then
																																					else
																																						local v209 = 0;
																																						while true do
																																							if ((1 - 0) == v209) then
																																								v200 = 7 - 4;
																																								break;
																																							end
																																							if (v209 == (1227 - (322 + 905))) then
																																								if (v20(v202, 3 - 2, 612 - (602 + 9)) ~= 1) then
																																								else
																																									v203[2] = v60[v203[2 + 0]];
																																								end
																																								if (v20(v202, 1 + 1, 3 - 1) == (66 - (30 + 35))) then
																																									v203[3 + 0] = v60[v203[1260 - (1043 + 214)]];
																																								end
																																								v209 = 3 - 2;
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
																														end
																														for v197 = 3 - 2, v23() do
																															v56[v197 - (1213 - (323 + 889))] = v28();
																														end
																														v193 = 1 + 0;
																													end
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
																			end
																			v177 = 2 - 1;
																		end
																	end
																end
															end
															break;
														end
													end
												end
												if (v107 ~= (1899 - (260 + 1638))) then
												else
													if (v54 ~= (440 - (382 + 58))) then
													else
														local v174 = 580 - (361 + 219);
														local v175;
														local v176;
														while true do
															if (v174 ~= 0) then
															else
																v175 = 0;
																v176 = nil;
																v174 = 3 - 2;
															end
															if (v174 ~= (321 - (53 + 267))) then
															else
																while true do
																	if (v175 == (0 + 0)) then
																		v176 = 413 - (15 + 398);
																		while true do
																			if (v176 == (984 - (18 + 964))) then
																				v54 = 3 - 2;
																				break;
																			end
																			if (v176 == (0 + 0)) then
																				local v181 = 0 - 0;
																				while true do
																					if ((1 + 0) ~= v181) then
																					else
																						v176 = 1691 - (1121 + 569);
																						break;
																					end
																					if (v181 ~= 0) then
																					else
																						v55 = {};
																						v56 = {};
																						v181 = 215 - (22 + 192);
																					end
																				end
																			end
																			if (1 ~= v176) then
																			else
																				local v182 = 0;
																				while true do
																					if ((851 - (20 + 830)) == v182) then
																						v176 = 2 + 0;
																						break;
																					end
																					if (v182 ~= (126 - (116 + 10))) then
																					else
																						v57 = {};
																						v58 = {v55,v56,nil,v57};
																						v182 = 1;
																					end
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
													break;
												end
											end
											break;
										end
									end
								end
								break;
							end
							if (v53 == (738 - (542 + 196))) then
								local v103 = 0 - 0;
								while true do
									if (v103 == (0 - 0)) then
										v54 = 765 - (468 + 297);
										v55 = nil;
										v103 = 1 + 0;
									end
									if (1 ~= v103) then
									else
										v53 = 1 + 0;
										break;
									end
								end
							end
							if (v53 == (2 - 1)) then
								v56 = nil;
								v57 = nil;
								v53 = 2 - 0;
							end
							if (v53 ~= (1 + 1)) then
							else
								local v104 = 0;
								local v105;
								while true do
									if ((0 + 0) ~= v104) then
									else
										v105 = 0;
										while true do
											if (v105 ~= (2 - 1)) then
											else
												v53 = 3 + 0;
												break;
											end
											if (0 ~= v105) then
											else
												local v126 = 0 - 0;
												while true do
													if (v126 ~= (0 - 0)) then
													else
														v58 = nil;
														v59 = nil;
														v126 = 2 - 1;
													end
													if ((1552 - (1126 + 425)) == v126) then
														v105 = 406 - (118 + 287);
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
					if (2 ~= v52) then
					else
						local v97 = 0;
						while true do
							if ((0 - 0) ~= v97) then
							else
								v57 = nil;
								v58 = nil;
								v97 = 1122 - (118 + 1003);
							end
							if (v97 == (2 - 1)) then
								v52 = 3 + 0;
								break;
							end
						end
					end
					if (v52 == (2 + 1)) then
						local v98 = 0 - 0;
						while true do
							if (v98 == 1) then
								v52 = 11 - 7;
								break;
							end
							if (v98 ~= (163 - (92 + 71))) then
							else
								v59 = nil;
								v60 = nil;
								v98 = 378 - (142 + 235);
							end
						end
					end
				end
				break;
			end
			if (0 == v51) then
				v52 = 0 - 0;
				v53 = nil;
				v51 = 1 + 0;
			end
			if (v51 ~= (980 - (553 + 424))) then
			else
				v58 = nil;
				v59 = nil;
				v51 = 4;
			end
		end
	end
	local function v29(v61, v62, v63)
		local v64 = 0;
		local v65;
		local v66;
		local v67;
		while true do
			if (v64 == 0) then
				v65 = v61[1];
				v66 = v61[2];
				v64 = 1;
			end
			if (v64 == 1) then
				v67 = v61[3];
				return function(...)
					local v78 = v65;
					local v79 = v66;
					local v80 = v67;
					local v81 = v27;
					local v82 = 1;
					local v83 = -1;
					local v84 = {};
					local v85 = {...};
					local v86 = v12("#", ...) - 1;
					local v87 = {};
					local v88 = {};
					for v92 = 0, v86 do
						if (v92 >= v80) then
							v84[v92 - v80] = v85[v92 + 1];
						else
							v88[v92] = v85[v92 + 1];
						end
					end
					local v89 = (v86 - v80) + 1;
					local v90;
					local v91;
					while true do
						v90 = v78[v82];
						v91 = v90[1];
						if (v91 <= 10) then
							if (v91 <= 4) then
								if (v91 <= 1) then
									if (v91 == 0) then
										v88[v90[2]] = v88[v90[3]][v90[4]];
									else
										v88[v90[2]] = v90[3] ~= 0;
									end
								elseif (v91 <= 2) then
									v88[v90[2]][v90[3]] = v90[4];
								elseif (v91 > 3) then
									v88[v90[2]] = v63[v90[3]];
								elseif (v88[v90[2]] == v90[4]) then
									v82 = v82 + 1;
								else
									v82 = v90[3];
								end
							elseif (v91 <= 7) then
								if (v91 <= 5) then
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]][v90[3]] = v90[4];
								elseif (v91 > 6) then
									local v129;
									local v130;
									v88[v90[2]] = v88[v90[3]][v90[4]];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]] = v88[v90[3]][v90[4]];
									v82 = v82 + 1;
									v90 = v78[v82];
									v130 = v90[2];
									v129 = v88[v90[3]];
									v88[v130 + 1] = v129;
									v88[v130] = v129[v90[4]];
									v82 = v82 + 1;
									v90 = v78[v82];
									v88[v90[2]] = v90[3];
									v82 = v82 + 1;
									v90 = v78[v82];
									v130 = v90[2];
									v88[v130](v13(v88, v130 + 1, v90[3]));
									v82 = v82 + 1;
									v90 = v78[v82];
									do
										return;
									end
									v82 = v82 + 1;
									v90 = v78[v82];
									v82 = v90[3];
								else
									local v140 = v90[2];
									local v141 = v90[4];
									local v142 = v140 + 2;
									local v143 = {v88[v140](v88[v140 + 1], v88[v142])};
									for v161 = 1, v141 do
										v88[v142 + v161] = v143[v161];
									end
									local v144 = v143[1];
									if v144 then
										v88[v142] = v144;
										v82 = v90[3];
									else
										v82 = v82 + 1;
									end
								end
							elseif (v91 <= 8) then
								v88[v90[2]] = v88[v90[3]][v88[v90[4]]];
							elseif (v91 == 9) then
								v82 = v90[3];
							else
								local v146 = v90[2];
								local v147 = {v88[v146](v88[v146 + 1])};
								local v148 = 0;
								for v164 = v146, v90[4] do
									v148 = v148 + 1;
									v88[v164] = v147[v148];
								end
							end
						elseif (v91 <= 15) then
							if (v91 <= 12) then
								if (v91 > 11) then
									do
										return;
									end
								else
									v88[v90[2]] = v88[v90[3]];
								end
							elseif (v91 <= 13) then
								local v120 = v90[2];
								v88[v120](v13(v88, v120 + 1, v90[3]));
							elseif (v91 == 14) then
								if not v88[v90[2]] then
									v82 = v82 + 1;
								else
									v82 = v90[3];
								end
							elseif (v90[2] == v88[v90[4]]) then
								v82 = v82 + 1;
							else
								v82 = v90[3];
							end
						elseif (v91 <= 18) then
							if (v91 <= 16) then
								local v121 = v90[2];
								local v122 = v88[v90[3]];
								v88[v121 + 1] = v122;
								v88[v121] = v122[v90[4]];
							elseif (v91 > 17) then
								v88[v90[2]] = {};
							else
								v88[v90[2]][v90[3]] = v90[4];
								v82 = v82 + 1;
								v90 = v78[v82];
								v88[v90[2]][v90[3]] = v90[4];
								v82 = v82 + 1;
								v90 = v78[v82];
								v88[v90[2]][v90[3]] = v90[4];
								v82 = v82 + 1;
								v90 = v78[v82];
								v88[v90[2]][v90[3]] = v90[4];
								v82 = v82 + 1;
								v90 = v78[v82];
								v88[v90[2]][v90[3]] = v90[4];
								v82 = v82 + 1;
								v90 = v78[v82];
								v88[v90[2]][v90[3]] = v90[4];
								v82 = v82 + 1;
								v90 = v78[v82];
								v88[v90[2]][v90[3]] = v90[4];
								v82 = v82 + 1;
								v90 = v78[v82];
								v88[v90[2]][v90[3]] = v90[4];
								v82 = v82 + 1;
								v90 = v78[v82];
								v88[v90[2]] = v88[v90[3]];
								v82 = v82 + 1;
								v90 = v78[v82];
								v88[v90[2]] = v63[v90[3]];
							end
						elseif (v91 <= 19) then
							if (v88[v90[2]] == v88[v90[4]]) then
								v82 = v82 + 1;
							else
								v82 = v90[3];
							end
						elseif (v91 > 20) then
							for v167 = v90[2], v90[3] do
								v88[v167] = nil;
							end
						else
							v88[v90[2]] = v90[3];
						end
						v82 = v82 + 1;
					end
				end;
			end
		end
	end
	return v29(v28(), {}, v17)(...);
end
return v15("LOL!633O00028O00026O00F03F03063O00557365724964027O0040022O00E0DF0BE2E6412O01023O002747ABE241023O00A2DC99D741022O0080255800C141022O00B0EE9D94F041022O00E0212250EC41022O00C019CF88DC41022O0020C43923EA41022O00C0A275FAD041023O006E4FFFBE41022O00807911D2DB41022O0050AC5E5FF341023O00244005AC41023O00D70D77B441022O00400EC1D6F041022O0080AB965ED141022O00804197CEE841023O00214A69D841022O00C01EBB61D541023O008FA98CD741023O0014F0FCB041022O00C0308921EE41022O0050A18229F041022O00A06D4662E541022O00800470B3D941022O0080EF7B01D141023O009F618FB341022O00803E2FD2D941022O0080F9B6F9CA41023O000DBB0CD641022O00E06B54AAE341023O00A3582BB141022O00A0BABE38EF41022O00C05D7B6CDB41022O006092D670EA41022O00806F310FDD41022O00807B08C0D441023O00763546B741023O0060226EC541022O00604DAD8DE141023O00B6FAB7D941023O002BB73FD341022O00E0244ABCF141022O008070D993C841023O004C5AAFD741022O00802F229CC541022O00A0FACC8AE341022O004095784BDE41023O00A43963D541023O004FBD86B041023O00AA6CB2C141022O0050B1E800F441022O00C04CB755D141022O00C0B617ECDC41022O00A00A62AAE241023O00D72449CA41023O00EFAEF4CE41022O0080B94588C141022O0080953250C441022O00D05C3D21F241022O0060FE1DD6F441023O00339BDBF441022O0080499ADBF441022O00C0DB7B3FEB41023O00D92E6CE841022O0080CFE15DF441022O0020C41E16E241023O00A14C54BD41022O00609B4814E541022O00A0C4491EE441022O00A0D02EB1EE41022O00400427C5D241022O0020A31687ED41022O0080AD1FD4D641022O00C047130BF341022O0080AF7AFEF141022O0020737CA2E441022O00E069E36AE841022O00406E5E01F241022O00A0F57DECEB41022O00E045061FE541022O00C0A27A3AD441022O00800A0190E341023O00251300D841022O00E0C44BC1EF41023O0073E5AAD941022O004091574AD841023O00E96467B24103043O0067616D6503073O00506C6179657273030B3O004C6F63616C506C6179657203053O00706169727303043O004B69636B030B3O0050454E44454A4F204C4F4C008B3O0012143O00014O0015000100043O0026033O0007000100020004093O0007000100202O0003000200032O00080004000100030012143O00043O0026033O0067000100010004093O006700012O001200053O002300300500050005000600302O00050007000600302O00050008000600302O00050009000600302O0005000A000600302O0005000B000600302O0005000C000600302O0005000D000600302O0005000E000600302O0005000F000600302O00050010000600302O00050011000600302O00050012000600302O00050013000600302O00050014000600302O00050015000600302O00050016000600302O00050017000600302O00050018000600302O00050019000600302O0005001A000600302O0005001B000600302O0005001C000600302O0005001D000600302O0005001E000600302O0005001F000600302O00050020000600302O00050021000600302O00050022000600302O00050023000600302O00050024000600302O00050025000600302O00050026000600302O00050027000600302O00050028000600302O00050029000600302O0005002A000600302O0005002B000600302O0005002C000600302O0005002D000600302O0005002E000600302O0005002F000600302O00050030000600302O00050031000600302O00050032000600302O00050033000600302O00050034000600302O00050035000600302O00050036000600302O00050037000600302O00050038000600302O00050039000600302O0005003A000600302O0005003B000600302O0005003C000600302O0005003D000600302O0005003E000600302O0005003F000600302O00050040000600302O00050041000600302O00050042000600302O00050043000600302O00050044000600302O00050045000600302O00050046000600302O00050047000600302O00050048000600302O00050049000600302O0005004A000600302O0005004B000600302O0005004C000600302O0005004D000600302O0005004E000600302O0005004F000600302O00050050000600302O00050051000600302O00050052000600302O00050053000600302O00050054000600302O00050055000600301100050056000600302O00050057000600302O00050058000600302O00050059000600302O0005005A000600302O0005005B000600302O0005005C000600302O0005005D00064O000100053O00122O0005005E3O00202O00050005005F00202O0002000500600012143O00023O0026033O0002000100040004093O00020001001204000500614O000B000600014O000A0005000200070004093O00750001001204000A005E3O00202O000A000A005F00202O000A000A006000202O000A000A0003000613000A0075000100090004093O007500012O0001000400013O0004093O00770001002O060005006D000100020004093O006D000100060E0004008A000100010004093O008A0001001214000500013O0026030005007A000100010004093O007A0001001214000600013O000E0F0001007D000100060004093O007D00010012040007005E3O00200700070007005F00202O00070007006000202O00070007006200122O000900636O0007000900016O00013O00044O007D00010004093O007A00010004093O008A00010004093O000200012O000C3O00017O00", v9(), ...);