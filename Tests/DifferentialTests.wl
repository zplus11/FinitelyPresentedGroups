(* ::Package:: *)
(* Randomised differential and soundness tests with recorded seeds. *)

Do[Quiet @ PacletDirectoryUnload[p["Location"]], {p, PacletFind["Taggar/FinitelyPresentedGroups"]}];
PacletDirectoryLoad[DirectoryName[DirectoryName[ExpandFileName[$InputFileName]]]];
Needs["Taggar`FinitelyPresentedGroups`"];

passCount = 0;
failCount = 0;
check[name_String, cond_] := If[TrueQ[cond], passCount++, failCount++; Print["FAIL: ", name]];

(* 1. GroupOrder differential tests: compare RS path against direct CosetTable / known orders *)
SeedRandom[20261127];
Do[
	Module[{n1 = RandomInteger[{3, 8}], n2 = RandomInteger[{3, 8}], g1, g2, prod, ord},
		g1 = FinitelyPresentedGroup[DihedralGroup[n1]];
		g2 = FinitelyPresentedGroup[DihedralGroup[n2]];
		prod = FinitelyPresentedGroup[
			Join[g1["GeneratorList"], g2["GeneratorList"]],
			Join[g1["RelatorList"], g2["RelatorList"],
				Flatten @ Table[x ** y ** x^(-1) ** y^(-1), {x, g1["GeneratorList"]}, {y, g2["GeneratorList"]}]]
		];
		ord = GroupOrder[prod];
		check["GroupOrder-DihedralProd-" <> ToString[k], ord === 4 n1 n2];
		(* Also force ReidemeisterSchreier path directly via CosetTable on a subgroup *)
		With[{t = CosetTable[prod, {prod["GeneratorList"][[1]], prod["GeneratorList"][[2]]}]},
			With[{rs = Taggar`FinitelyPresentedGroups`Private`ReidemeisterSchreier[t,
				DeleteCases[Taggar`FinitelyPresentedGroups`Private`NormaliseRelators[prod], {}],
				prod["GeneratorCount"]]},
				check["GroupOrder-ForcedRS-" <> ToString[k],
					Length[t] * Taggar`FinitelyPresentedGroups`Private`EnumerateOrderWords[rs[[1]], rs[[2]], 1] === 4 n1 n2]]];
	],
	{k, 6}
];

(* Test GroupOrder > 65536 forcing top-level RS: S4 x S4 x S5 = 24*24*120 = 69,120 *)
s4a = FinitelyPresentedGroup[{a1, a2, a3}, {a1^2, a2^2, a3^2, (a1 ** a2)^3, (a2 ** a3)^3, (a1 ** a3)^2}];
s4b = FinitelyPresentedGroup[{b1, b2, b3}, {b1^2, b2^2, b3^2, (b1 ** b2)^3, (b2 ** b3)^3, (b1 ** b3)^2}];
s5c = FinitelyPresentedGroup[{c1, c2, c3, c4}, {c1^2, c2^2, c3^2, c4^2, (c1 ** c2)^3, (c2 ** c3)^3, (c3 ** c4)^3, (c1 ** c3)^2, (c1 ** c4)^2, (c2 ** c4)^2}];
comm[g1_, g2_] := Flatten @ Table[x ** y ** x^(-1) ** y^(-1), {x, g1["GeneratorList"]}, {y, g2["GeneratorList"]}];
s445 = FinitelyPresentedGroup[
	Join[s4a["GeneratorList"], s4b["GeneratorList"], s5c["GeneratorList"]],
	Join[s4a["RelatorList"], s4b["RelatorList"], s5c["RelatorList"], comm[s4a, s4b], comm[s4a, s5c], comm[s4b, s5c]]
];
check["GroupOrder-S4xS4xS5-69120", GroupOrder[s445] === 69120];

(* 2. Randomised ElementReduce & ElementEqualQ vs independent CosetTable regular action *)
SeedRandom[1337];
finGroups = {
	FinitelyPresentedGroup[{r, s}, {r^3, s^2, (r ** s)^2}],
	FinitelyPresentedGroup[{a, b}, {a^4, a^2 ** b^(-2), a ** b ** a^(-1) ** b}],
	FinitelyPresentedGroup[SymmetricGroup[4]],
	FinitelyPresentedGroup[AlternatingGroup[5]]
};
Do[
	With[{G = finGroups[[gi]], t = CosetTable[finGroups[[gi]], {}]},
		With[{ng = G["GeneratorCount"], nc = 2 G["GeneratorCount"]},
			trace[w_] := Fold[t[[#1, #2]] &, 1, If[# > 0, #, nc + 1 + #] & /@ w];
			alpha = Join[Range[ng], -Range[ng]];
			Do[
				u = RandomChoice[alpha, RandomInteger[{0, 15}]];
				v = RandomChoice[alpha, RandomInteger[{0, 15}]];
				ru = ElementReduce[G, u];
				check["ElementReduce-Valid-" <> ToString[gi] <> "-" <> ToString[i],
					trace[ru] === trace[u] && Length[ru] <= Length[u]];
				check["ElementEqualQ-Diff-" <> ToString[gi] <> "-" <> ToString[i],
					ElementEqualQ[G, u, v] === (trace[u] === trace[v])],
				{i, 25}
			]
		]
	],
	{gi, Length[finGroups]}
];

(* 3. Infinite group oracle checks: Z^2 and Z_2 x Z *)
z2 = FinitelyPresentedGroup[{a, b}, {a ** b ** a^(-1) ** b^(-1)}];
SeedRandom[999];
Do[
	u = RandomChoice[{1, -1, 2, -2}, RandomInteger[{0, 14}]];
	v = RandomChoice[{1, -1, 2, -2}, RandomInteger[{0, 14}]];
	expVec[w_] := {Count[w, 1] - Count[w, -1], Count[w, 2] - Count[w, -2]};
	check["Z2-EqualQ-" <> ToString[i], ElementEqualQ[z2, u, v] === (expVec[u] === expVec[v])],
	{i, 30}
];

(* 4. Knuth-Bendix soundness: incomplete KB must never report Confluent->True or false inequality *)
Block[
	{Taggar`FinitelyPresentedGroups`Private`$KBMaxSteps = 2},
	With[{kb = Taggar`FinitelyPresentedGroups`Private`KBSystem[finGroups[[4]]]},
		check["KB-IncompleteNotConfluent", kb["Confluent"] === False];
	]
];
(* Containment overlap test *)
check["KB-ContainmentOverlap",
	Length[Taggar`FinitelyPresentedGroups`Private`KBOverlaps[{1, 2, 1}, {}, {2}, {}]] >= 1];

(* 5. CosetTable Method -> "Felsch" differential & completeness checks *)
SeedRandom[20261128];
Do[
	Module[{ng = RandomInteger[{2, 3}], gens, rels, G, hgens, rw, tf, th, nc, relCols, subCols, ok},
		gens = Symbol["$fg" <> ToString[#]] & /@ Range[ng];
		rw[] := NonCommutativeMultiply @@ RandomChoice[Join[gens, gens^(-1)], RandomInteger[{2, 6}]];
		rels = Join[Table[g^RandomInteger[{2, 4}], {g, gens}], Table[rw[], {RandomInteger[{1, 3}]}]];
		G = FinitelyPresentedGroup[gens, rels];
		hgens = If[RandomReal[] < 0.5, {}, {RandomChoice[gens] ** RandomChoice[gens]}];
		tf = Quiet @ CosetTable[G, hgens, "MaxCosets" -> 5000, Method -> "Felsch"];
		th = Quiet @ CosetTable[G, hgens, "MaxCosets" -> 5000, Method -> "HLT"];
		ok = If[tf === $Failed, th === $Failed,
			MatrixQ[th] && Length[tf] === Length[th] && MatrixQ[tf, IntegerQ] &&
			(nc = 2 ng; AllTrue[Flatten[tf], 1 <= # <= Length[tf] &]) &&
			AllTrue[Tuples[{Range[Length[tf]], Range[nc]}], tf[[tf[[#[[1]], #[[2]]]], nc + 1 - #[[2]]]] === #[[1]] &] &&
			(relCols = Taggar`FinitelyPresentedGroups`Private`ToColumns[#, nc] & /@
				DeleteCases[Taggar`FinitelyPresentedGroups`Private`NormaliseRelators[G], {}];
			 AllTrue[Tuples[{Range[Length[tf]], relCols}], Fold[tf[[#1, #2]] &, #[[1]], #[[2]]] === #[[1]] &]) &&
			(subCols = Taggar`FinitelyPresentedGroups`Private`ToColumns[#, nc] & /@
				DeleteCases[Taggar`FinitelyPresentedGroups`Private`FreeReduce /@
					Taggar`FinitelyPresentedGroups`Private`SubgroupWords[G, hgens], {}];
			 AllTrue[subCols, Fold[tf[[#1, #2]] &, 1, #] === 1 &])];
		check["Felsch-Rand-" <> ToString[k], ok]
	],
	{k, 10}
];
(* Small budget case where Felsch succeeds and HLT overflows *)
With[{gSmall = FinitelyPresentedGroup[{a, b}, {a^2, b^3, (a ** b)^7, (a ** b ** a^(-1) ** b^(-1))^4}]},
	check["Felsch-SmallBudget200", Length[CosetTable[gSmall, {}, "MaxCosets" -> 200, Method -> "Felsch"]] === 168];
];

Print["Differential tests: ", passCount, " passed, ", failCount, " failed."];
If[failCount > 0, Exit[1]];
