PacletDirectoryLoad[DirectoryName[DirectoryName[$TestFileName]]];
Needs["Taggar`FinitelyPresentedGroups`"];

s3 = FinitelyPresentedGroup[{r, s}, {r^3, s^2, (r ** s)^2}];
f = FreeGroup[{a, b}];

TestCreate[{s3["GeneratorList"], s3["GeneratorCount"], s3["RelatorCount"]}, {{r, s}, 2, 3}, TestID -> "FinitelyPresentedGroup-Properties"]
TestCreate[FinitelyPresentedGroup[{a, a}, {a^2}], $Failed, {FinitelyPresentedGroup::DuplicateGenerators}, TestID -> "FinitelyPresentedGroup-DuplicateGenerators"]
TestCreate[FinitelyPresentedGroup[{a, b + c}, {a^2}], $Failed, {FinitelyPresentedGroup::BadGenerators}, TestID -> "FinitelyPresentedGroup-NonatomicGenerators"]
TestCreate[FinitelyPresentedGroup[{a, b}, {c^2}], $Failed, {FinitelyPresentedGroup::BadRelators}, TestID -> "FinitelyPresentedGroup-InvalidRelators"]

TestCreate[ElementReduce[s3, {1, -1}], {}, TestID -> "ElementReduce-Free"]
TestCreate[ElementReduce[s3, {1, 1}], {-1}, TestID -> "ElementReduce-Dehn"]
TestCreate[ElementEqualQ[s3, r ** s, s ** r^-1], True, TestID -> "ElementEqualQ-Finite"]
TestCreate[ElementEqualQ[f, a ** b, b ** a], False, TestID -> "ElementEqualQ-Free"]
TestCreate[ElementEqualQ[FinitelyPresentedGroup[{a, b}, {a ** b ** a^(-1) ** b^(-1)}], a ** b, b ** a], True, TestID -> "ElementEqualQ-KBEqual"]
TestCreate[ElementEqualQ[FinitelyPresentedGroup[{a, b}, {a ** b ** a^(-1) ** b^(-1)}], a ** b, a], False, TestID -> "ElementEqualQ-KBNotEqual"]
TestCreate[ElementEqualQ[FinitelyPresentedGroup[{a, b}, {a^2 ** b^(-2)}], a, b], False, TestID -> "ElementEqualQ-AbelianInequality"]

TestCreate[Length @ CosetTable[s3, {r}], 2, TestID -> "CosetTable-Index"]
TestCreate[CosetTable[f, {a}, "MaxCosets" -> 50], $Failed, {CosetTable::Overflow}, TestID -> "CosetTable-Overflow"]
TestCreate[Length @ CosetTable[FinitelyPresentedGroup[{a, b}, {a^2, b^3, (a ** b)^7, (a ** b ** a^(-1) ** b^(-1))^8}], {}], 10752, TestID -> "CosetTable-Collapses"]
TestCreate[Length @ CosetTable[FinitelyPresentedGroup[{a, b}, {a^2, b^3, (a ** b)^7, (a ** b ** a^(-1) ** b^(-1))^4}], {}, "MaxCosets" -> 400], 168, TestID -> "CosetTable-SmallBudget"]

TestCreate[GroupOrder[s3], 6, TestID -> "GroupOrder-S3"]
TestCreate[GroupOrder @ FinitelyPresentedGroup[{a}, {a^1000}], 1000, TestID -> "GroupOrder-Cyclic"]
TestCreate[GroupOrder @ FinitelyPresentedGroup[{a, b}, {a^2 == b^2, a^4, a ** b ** a^-1 == b^-1}], 8, TestID -> "GroupOrder-Quaternion"]
TestCreate[GroupOrder @ FinitelyPresentedGroup[{a, b}, {a ** b ** a^-1 == b^2, b ** a ** b^-1 == a^2}], 1, TestID -> "GroupOrder-Trivial"]
TestCreate[GroupOrder @ FinitelyPresentedGroup[{a, b}, {a^2, b^2}], Infinity, TestID -> "GroupOrder-InfiniteDihedral"]
TestCreate[GroupOrder @ FinitelyPresentedGroup[{a, b}, {a^2 == 1, b^3 == 1, a ** b == b ** a}], 6, TestID -> "EquationRelators"]
TestCreate[GroupOrder @ FinitelyPresentedGroup[SymmetricGroup[8]], 40320, TestID -> "GroupOrder-S8"]

TestCreate[GroupOrder /@ FinitelyPresentedGroup /@ {CyclicGroup[1000], DihedralGroup[7], AbelianGroup[{2, 2, 4}], SymmetricGroup[6]}, {1000, 14, 16, 720}, TestID -> "DirectPresentations"]
TestCreate[GroupOrder /@ FinitelyPresentedGroup /@ {AlternatingGroup[5], AlternatingGroup[7], MathieuGroupM11[]}, {60, 2520, 7920}, TestID -> "PermutationPresentations"]
(* the images of the FPG generators must be the original permutations, in the same convention *)
TestCreate[
	With[{p = {Cycles[{{1, 2, 3}}], Cycles[{{3, 4, 5}}]}},
		With[{h = FinitelyPresentedGroup[PermutationGroup[p]]},
			AllTrue[h["RelatorList"],
				(# /. Thread[h["GeneratorList"] -> p] /. {
					Power[c_Cycles, n_Integer] :> PermutationPower[c, n],
					NonCommutativeMultiply -> PermutationProduct}) === Cycles[{}] &]]],
	True, TestID -> "PermutationPresentation-Convention"]

TestCreate[{f["AbelianInvariants"], s3["AbelianInvariants"], FinitelyPresentedGroup[AbelianGroup[{2, 2, 4}]]["AbelianInvariants"]}, {{0, 0}, {2}, {2, 2, 4}}, TestID -> "AbelianInvariants"]
TestCreate[(FinitelyPresentedGroup[{z}, {z^2}] ** FinitelyPresentedGroup[{a}, {a^3}])["GeneratorList"], {z, a}, TestID -> "FreeProduct-Order"]
TestCreate[{GroupOrder @ PermutationGroup[s3], Length @ GroupOrbits @ PermutationGroup[s3]}, {6, 1}, TestID -> "PermutationGroup-RegularAction"]
TestCreate[
	With[{mt = GroupMultiplicationTable[s3], el = GroupElements[s3]},
		Length[el] === 6 && AllTrue[Flatten @ Table[GroupElementPosition[s3, el[[i]] ** el[[j]]] === mt[[i, j]], {i, 6}, {j, 6}], TrueQ]],
	True, TestID -> "GroupMultiplicationTable-Consistent"]
TestCreate[{VertexCount @ CayleyGraph[s3], EdgeCount @ CayleyGraph[s3]}, {6, 12}, TestID -> "CayleyGraph-S3"]
TestCreate[
	With[{sim = TietzeSimplify @ FinitelyPresentedGroup[{x, y, z}, {x^2, y^3, z == x ** y, (x ** y)^2}]},
		{sim["GeneratorCount"], GroupOrder[sim]}],
	{2, 6}, TestID -> "TietzeSimplify-PreservesOrder"]
TestCreate[
	With[{mats = {{{1, 1}, {0, 1}}, {{1, 0}, {1, 1}}}, id2 = IdentityMatrix[2], u = a ** b ** a^(-1), v = b^(-1) ** a},
		With[{df = FoxD[f, #, a, mats, "Multiply" -> Dot, "Invert" -> Inverse, "One" -> id2] &,
		      dg = FoxD[f, #, b, mats, "Multiply" -> Dot, "Invert" -> Inverse, "One" -> id2] &},
			With[{ev = Fold[Dot, id2, If[# > 0, mats[[#]], Inverse[mats[[-#]]]] & /@ GroupElementToWord[f, #]] &},
				df[u ** v] === (df[u] + ev[u] . df[v]) &&
				(df[u ** v] . (mats[[1]] - id2) + dg[u ** v] . (mats[[2]] - id2)) === (ev[u ** v] - id2)]]],
	True, TestID -> "FoxD-ProductRuleAndFundamentalFormula"]
TestCreate[
	With[{pg = PermutationGroup[FinitelyPresentedGroup[SymmetricGroup[6]]]},
		{GroupOrder[pg], PermutationMax[pg] <= 6}],
	{720, True}, TestID -> "PermutationGroup-LowerDegree"]
TestCreate[
	With[{p = GroupGenerators[MathieuGroupM12[]]},
		With[{h = FinitelyPresentedGroup[MathieuGroupM12[]]},
			AllTrue[h["RelatorList"],
				(# /. Thread[h["GeneratorList"] -> p] /. {
					Power[c_Cycles, n_Integer] :> PermutationPower[c, n],
					NonCommutativeMultiply -> PermutationProduct}) === Cycles[{}] &]]],
	True, TestID -> "PermutationPresentation-M12Convention"]
