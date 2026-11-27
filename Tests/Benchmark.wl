(* ::Package:: *)
(* Reusable benchmark suite for parts B-E.
   Usage: wolfram.exe -script Tests/Benchmark.wl [pacletDir] *)

envDir = Environment["FPG_PACLET_DIR"];
dir = Which[
	StringQ[envDir] && DirectoryQ[envDir], envDir,
	Length[$ScriptCommandLine] >= 2 && DirectoryQ[$ScriptCommandLine[[2]]], $ScriptCommandLine[[2]],
	True, DirectoryName[DirectoryName[ExpandFileName[$InputFileName]]]
];

Do[Quiet @ PacletDirectoryUnload[p["Location"]], {p, PacletFind["Taggar/FinitelyPresentedGroups"]}];
PacletDirectoryLoad[dir];
Needs["Taggar`FinitelyPresentedGroups`"];

Print["Loaded paclet: ", FindFile["Taggar`FinitelyPresentedGroups`"]];

SetAttributes[bench, HoldAll];
bench[name_String, expr_, timeLim_ : 10, memLimMB_ : 512] := Module[
	{t, mem, res},
	mem = MaxMemoryUsed[
		{t, res} = AbsoluteTiming[
			TimeConstrained[
				MemoryConstrained[Quiet[expr], memLimMB * 1024^2, $MemLimit],
				timeLim,
				$TimedOut
			]
		]
	];
	Print[name, " | ", ToString @ NumberForm[t, {5, 4}], " s | ",
		ToString @ NumberForm[N[mem / 1024.^2], {5, 2}], " MB | ",
		If[ByteCount[res] < 200, ToString[res, InputForm], ToString[Head[res]]]];
	<|"Name" -> name, "Time" -> t, "MemoryMB" -> N[mem / 1024.^2], "Result" -> res|>
];

(* Warm up WVM/C compilation so first-call compile cost does not skew C1 *)
Quiet @ CosetTable[FinitelyPresentedGroup[{x}, {x^2}], {}];

(* --- B: Core words and presentations --- *)
gens20 = Symbol["g" <> ToString[#]] & /@ Range[20];
relsB = Join[
	Table[gens20[[i]]^5, {i, 20}],
	Table[(gens20[[i]] ** gens20[[Mod[i, 20] + 1]])^3, {i, 20}],
	Flatten[Table[gens20[[i]] ** gens20[[j]] ** gens20[[i]]^(-1) ** gens20[[j]]^(-1), {i, 1, 10}, {j, i + 1, i + 4}], 1]
];
longWordExpr = NonCommutativeMultiply @@ Table[gens20[[Mod[i, 20] + 1]]^If[EvenQ[i], 2, -2], {i, 100}];

bench["B1-Construct50", Do[FinitelyPresentedGroup[gens20, relsB], {50}]; True];
gB = FinitelyPresentedGroup[gens20, relsB];
bench["B2-AbelianInv20", Table[gB["AbelianInvariants"], {20}][[1]]];
gPairs = Table[With[{s = Symbol["p" <> ToString[i]]}, FinitelyPresentedGroup[{s}, {s^(i + 1)}]], {i, 8}];
bench["B3-FreeProd8", (Fold[NonCommutativeMultiply, gPairs])["GeneratorCount"]];
bench["B4-WordParse100", Do[GroupElementToWord[gB, longWordExpr], {100}]; True];

(* --- C: CosetTable --- *)
gColl = FinitelyPresentedGroup[{a, b}, {a^2, b^3, (a ** b)^7, (a ** b ** a^(-1) ** b^(-1))^8}];
gSmall = FinitelyPresentedGroup[{a, b}, {a^2, b^3, (a ** b)^7, (a ** b ** a^(-1) ** b^(-1))^4}];
s7 = FinitelyPresentedGroup[SymmetricGroup[7]];

bench["C1-Collapses10752", Length @ CosetTable[gColl, {}], 15];
bench["C2-SmallBudget400", Length @ CosetTable[gSmall, {}, "MaxCosets" -> 400], 10];
bench["C3-S7CosetTable", Length @ CosetTable[s7, {}], 15];

(* --- D: GroupOrder --- *)
s6 = FinitelyPresentedGroup[SymmetricGroup[6]];
s8 = FinitelyPresentedGroup[SymmetricGroup[8]];
s5 = FinitelyPresentedGroup[SymmetricGroup[5]];
u5 = FinitelyPresentedGroup[{u1, u2, u3, u4},
	{u1^2, u2^2, u3^2, u4^2, (u1 ** u2)^3, (u2 ** u3)^3, (u3 ** u4)^3,
	 (u1 ** u3)^2, (u1 ** u4)^2, (u2 ** u4)^2}];
s5sq = FinitelyPresentedGroup[
	Join[s5["GeneratorList"], u5["GeneratorList"]],
	Join[s5["RelatorList"], u5["RelatorList"],
		Flatten @ Table[g ** u ** g^(-1) ** u^(-1), {g, s5["GeneratorList"]}, {u, u5["GeneratorList"]}]]
];
(* S5^2 only has commutators between s5 and u_i on the right, Wait: s5**... is fine because s5 has gens x_i and u_i are disjoint *)

bench["D1-OrderS6", GroupOrder[s6], 10];
bench["D2-OrderS7", GroupOrder[s7], 15];
bench["D3-OrderS8", GroupOrder[s8], 15];
bench["D4-OrderS5xS5", GroupOrder[s5sq], 15];

v5 = FinitelyPresentedGroup[{v1, v2, v3, v4},
	{v1^2, v2^2, v3^2, v4^2, (v1 ** v2)^3, (v2 ** v3)^3, (v3 ** v4)^3,
	 (v1 ** v3)^2, (v1 ** v4)^2, (v2 ** v4)^2}];
comm[a_, b_] := Flatten @ Table[x ** y ** x^(-1) ** y^(-1), {x, a["GeneratorList"]}, {y, b["GeneratorList"]}];
s5cube = FinitelyPresentedGroup[
	Join[s5sq["GeneratorList"], v5["GeneratorList"]],
	Join[s5sq["RelatorList"], v5["RelatorList"], comm[s5, v5], comm[u5, v5]]
];
bench["D5-OrderS5xS5xS5", GroupOrder[s5cube], 25];

(* --- E: ElementReduce & ElementEqualQ --- *)
s6x = With[{s = {x1, x2, x3, x4, x5}},
	FinitelyPresentedGroup[s,
		Join[{x1^2, x2^2, x3^2, x4^2, x5^2, (x1 ** x2)^3, (x2 ** x3)^3, (x3 ** x4)^3, (x4 ** x5)^3},
		 Flatten @ Table[(s[[i]] ** s[[j]])^2, {i, 5}, {j, i + 2, 5}]]]];
wLong = Flatten @ ConstantArray[{1, 2, 3, -1, 4, 2, 1, -3}, 25];
gZ2 = FinitelyPresentedGroup[{a, b}, {a^2 ** b^(-2)}];

If[NameQ["Taggar`FinitelyPresentedGroups`ElementReduce"],
	bench["E1-ReduceS6x50", Do[ElementReduce[s6x, wLong], {50}]; Length @ ElementReduce[s6x, wLong]];
	bench["E2-EqualQS6x20", Table[ElementEqualQ[s6x, x1 ** x2 ** x1, x2 ** x1 ** x2], {20}][[1]]];
	bench["E3-EqualQAbelianInf", ElementEqualQ[gZ2, a, b]];
	,
	(* Original 8515ecc API fallback *)
	bench["E1-ReduceS6x50", Do[FPGWordReduce[s6x, wLong], {50}]; Length @ FPGWordReduce[s6x, wLong]["Word"]];
	bench["E2-EqualQS6x20", Table[FPGWord[s6x, x1 ** x2 ** x1] == FPGWord[s6x, x2 ** x1 ** x2], {20}][[1]]];
	bench["E3-EqualQAbelianInf", FPGWord[gZ2, a] == FPGWord[gZ2, b]];
];
