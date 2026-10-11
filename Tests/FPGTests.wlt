PacletDirectoryLoad[DirectoryName[DirectoryName[$TestFileName]]];
Needs["Taggar`FinitelyPresentedGroups`"];

g = FinitelyPresentedGroup[{a, b}, {a^2, b^2, (a ** b)^2}];
g3 = FinitelyPresentedGroup[{a, b}, {a^2, b^3, (a ** b)^2}];
f = FreeGroup[{a, b}];

TestCreate[{g["GeneratorList"], g["GeneratorCount"], g["RelatorCount"]}, {{a, b}, 2, 3}, TestID -> "FinitelyPresentedGroup-Properties"]
TestCreate[FinitelyPresentedGroup[{a, a}, {a^2}], $Failed, {FinitelyPresentedGroup::DuplicateGenerators}, TestID -> "FinitelyPresentedGroup-DuplicateGenerators"]
TestCreate[FinitelyPresentedGroup[{a, b + c}, {a^2}], $Failed, {FinitelyPresentedGroup::BadGenerators}, TestID -> "FinitelyPresentedGroup-NonatomicGenerators"]
TestCreate[FinitelyPresentedGroup[{a, b}, {c^2}], $Failed, {FinitelyPresentedGroup::BadRelators}, TestID -> "FinitelyPresentedGroup-InvalidRelators"]

TestCreate[FPGWord[g, a ** b ** a^-1], FPGWord[g, {1, 2, -1}], TestID -> "FPGWord-Parse"]
TestCreate[FPGWord[g, 1], FPGWord[g, {}], TestID -> "FPGWord-Identity"]
TestCreate[FPGWord[g, {1, 0}], $Failed, {FPGWord::BadWord}, TestID -> "FPGWord-ZeroIndex"]
TestCreate[FPGWord[g, c], $Failed, {FPGWord::BadWord}, TestID -> "FPGWord-UnknownGenerator"]

TestCreate[FPGWordReduce[FPGWord[g, {1, -1}]], FPGWord[g, {}], TestID -> "FPGWordReduce-FreeCancellation"]
TestCreate[FPGWordReduce[FPGWord[g, {1, 1}]], FPGWord[g, {}], TestID -> "FPGWordReduce-Relator"]
TestCreate[FPGWordReduce[FPGWord[g, {2, 1, 2, 1}]], FPGWord[g, {}], TestID -> "FPGWordReduce-CyclicRelator"]
TestCreate[FPGWordReduce[FPGWord[g, {2, 1, 1, -2, 2}]], FPGWord[g, {2}], TestID -> "FPGWordReduce-FreeAndRelator"]
TestCreate[FPGWordReduce[g, {1, 1, 2}], FPGWord[g, {2}], TestID -> "FPGWordReduce-TwoArguments"]

TestCreate[Inverse[FPGWord[g, {1, 2}]], FPGWord[g, {-2, -1}], TestID -> "FPGWord-Inverse"]
TestCreate[Inverse[Inverse[FPGWord[g, {1, 2}]]], FPGWord[g, {1, 2}], TestID -> "FPGWord-InverseInvolution"]
TestCreate[FPGWord[g, {1}] ** FPGWord[g, {2}], FPGWord[g, {1, 2}], TestID -> "FPGWord-Product"]
TestCreate[FPGWordReduce[FPGWord[g, {1}] ** FPGWord[g, {1}]], FPGWord[g, {}], TestID -> "FPGWord-ProductReduces"]
TestCreate[FPGWord[g, {1, 2}]^3, FPGWord[g, {1, 2, 1, 2, 1, 2}], TestID -> "FPGWord-Power"]
TestCreate[FPGWord[g, {1, 2}] == FPGWord[g, {-2, -1}], True, TestID -> "FPGWord-EqualByRelator"]
TestCreate[FPGWord[f, {1}] == FPGWord[f, {2}], False, TestID -> "FPGWord-EqualFreeGroup"]

TestCreate[Length @ CosetTable[g3, {a}], 3, TestID -> "CosetTable-Index"]
TestCreate[GroupOrder[g3], 6, TestID -> "CosetTable-GroupOrder"]
TestCreate[With[{t = CosetTable[g3, {a}]}, Fold[t[[#1, #2]] &, 1, #] == 1 & /@ {{2, 1, 2, -1}, {2}}], {True, False}, TestID -> "CosetTable-Membership"]
TestCreate[GroupOrder @ PermutationGroup[PermutationCycles /@ Transpose[CosetTable[g3, {}]][[;; 2]]], 6, TestID -> "CosetTable-Permutations"]
TestCreate[CosetTable[f, {a}, "MaxCosets" -> 50], $Failed, {CosetTable::Overflow}, TestID -> "CosetTable-Overflow"]