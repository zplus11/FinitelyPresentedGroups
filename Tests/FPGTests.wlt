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
TestCreate[FPGWord[g, {1, 2}]^3, FPGWord[g, {1, 2}], TestID -> "FPGWord-Power"]
TestCreate[FPGWord[g, {1, 2}] == FPGWord[g, {-2, -1}], True, TestID -> "FPGWord-EqualByRelator"]
TestCreate[FPGWord[f, {1}] == FPGWord[f, {2}], False, TestID -> "FPGWord-EqualFreeGroup"]

TestCreate[Length @ CosetTable[g3, {a}], 3, TestID -> "CosetTable-Index"]
TestCreate[GroupOrder[g3], 6, TestID -> "CosetTable-GroupOrder"]
TestCreate[With[{t = CosetTable[g3, {a}]}, Fold[t[[#1, #2]] &, 1, #] == 1 & /@ {{2, 1, 2, -1}, {2}}], {True, False}, TestID -> "CosetTable-Membership"]
TestCreate[GroupOrder @ PermutationGroup[PermutationCycles /@ Transpose[CosetTable[g3, {}]][[;; 2]]], 6, TestID -> "CosetTable-Permutations"]
TestCreate[CosetTable[f, {a}, "MaxCosets" -> 50], $Failed, {CosetTable::Overflow}, TestID -> "CosetTable-Overflow"]

TestCreate[GroupOrder @ FinitelyPresentedGroup[{a, b}, {a^2 == 1, b^3 == 1, a ** b == b ** a}], 6, TestID -> "EquationRelators"]
TestCreate[GroupOrder /@ FinitelyPresentedGroup /@ {CyclicGroup[1000], DihedralGroup[7], AbelianGroup[{2, 2, 4}], SymmetricGroup[6]}, {1000, 14, 16, 720}, TestID -> "DirectPresentations"]
TestCreate[{FreeGroup[{a, b}]["AbelianInvariants"], S3["AbelianInvariants"], FinitelyPresentedGroup[AbelianGroup[{2, 2, 4}]]["AbelianInvariants"]}, {{0, 0}, {2}, {2, 2, 4}}, TestID -> "AbelianInvariants"]
TestCreate[FPGWord[S3, r]["Order"] == 3 && FPGWord[S3, r ** s]["Order"] == 2 && FPGWord[S3, {}]["Order"] == 1, True, TestID -> "ElementOrder"]
TestCreate[{GroupOrder @ PermutationGroup[S3], Length @ GroupOrbits @ PermutationGroup[S3]}, {6, 1}, TestID -> "PermutationGroup-regular-action"]