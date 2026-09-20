PacletDirectoryLoad[DirectoryName[DirectoryName[$TestFileName]]];
Needs["Taggar`FinitelyPresentedGroups`"];

g = FinitelyPresentedGroup[{a, b}, {a^2, b^2, (a ** b)^2}];
g2 = FinitelyPresentedGroup[{x, y}, {x^2, y^2}];

TestCreate[FinitelyPresentedGroup[{a, b}, {a^2, b^2, (a ** b)^2}], g, TestID -> "FinitelyPresentedGroup-Valid"]
TestCreate[FinitelyPresentedGroup[{a, a}, {a^2}], $Failed, {FinitelyPresentedGroup::DuplicateGenerators}, TestID -> "FinitelyPresentedGroup-DuplicateGenerators"]
TestCreate[FinitelyPresentedGroup[{a, b + c}, {a^2}], $Failed, {FinitelyPresentedGroup::BadGenerators}, TestID -> "FinitelyPresentedGroup-NonatomicGenerators"]
TestCreate[FinitelyPresentedGroup[{a, b}, {c^2}], $Failed, {FinitelyPresentedGroup::BadRelators}, TestID -> "FinitelyPresentedGroup-InvalidRelators"]

TestCreate[FPGWord[g, {1, 2, -1}], FPGWord[g, {1, 2, -1}], TestID -> "FPGWord-Valid"]
TestCreate[FPGWord[g, {1, 0}], $Failed, {FPGWord::BadWord}, TestID -> "FPGWord-ZeroIndex"]
TestCreate[FPGWord[g, {1, 3}], $Failed, {FPGWord::BadWord}, TestID -> "FPGWord-IndexOutOfRange"]
TestCreate[FPGWord[g, {1, -2, 2, -1}], FPGWord[g, {1, -2, 2, -1}], TestID -> "FPGWord-NegativeIndices-Valid"]

TestCreate[FPGWordReduce[FPGWord[g, {1, -1}]], FPGWord[g, {}], TestID -> "FPGWordReduce-FreeCancellation"]
TestCreate[FPGWordReduce[FPGWord[g, {1, 1}]], FPGWord[g, {}], TestID -> "FPGWordReduce-Relator"]
TestCreate[FPGWordReduce[FPGWord[g, {2, 2}]], FPGWord[g, {}], TestID -> "FPGWordReduce-RelatorInverse"]
TestCreate[FPGWordReduce[FPGWord[g, {1, 2, 1, 2}]], FPGWord[g, {}], TestID -> "FPGWordReduce-CyclicRelator"]
TestCreate[FPGWordReduce[FPGWord[g, {1, 1, -1}]], FPGWord[g, {1}], TestID -> "FPGWordReduce-FreeAndRelator"]
TestCreate[FPGWordReduce[FPGWord[g, {}]], FPGWord[g, {}], TestID -> "FPGWordReduce-Identity"]

TestCreate[Inverse[FPGWord[g, {1, 2}]], FPGWord[g, {-2, -1}], TestID -> "FPGWord-Inverse"]
TestCreate[Inverse[Inverse[FPGWord[g, {1, 2}]]], FPGWord[g, {1, 2}], TestID -> "FPGWord-InverseInvolution"]
TestCreate[FPGWord[g, {1, 2}] ** Inverse[FPGWord[g, {1, 2}]], FPGWord[g, {}], TestID -> "FPGWord-InverseCancellation"]

TestCreate[FPGWord[g, {1}] ** FPGWord[g, {1}], FPGWord[g, {}], TestID -> "FPGWord-MultiplicationRelator"]
TestCreate[FPGWord[g, {1, 2}] ** FPGWord[g, {-2, -1}], FPGWord[g, {}], TestID -> "FPGWord-MultiplicationInverse"]
TestCreate[FPGWord[g, {1, 2}] ** FPGWord[g, {2, 1}], FPGWord[g, {}], TestID -> "FPGWord-Multiplication"]

TestCreate[FPGWord[g, {1}]^0, FPGWord[g, {}], TestID -> "FPGWord-PowerZero"]
TestCreate[FPGWord[g, {1}]^1, FPGWord[g, {1}], TestID -> "FPGWord-PowerOne"]
TestCreate[FPGWord[g, {1}]^2, FPGWord[g, {}], TestID -> "FPGWord-PowerRelator"]
TestCreate[FPGWord[g, {1}]^-1, FPGWord[g, {-1}], TestID -> "FPGWord-PowerNegativeOne"]
TestCreate[FPGWord[g, {1, 2}]^-1, FPGWord[g, {-2, -1}], TestID -> "FPGWord-PowerNegative"]

TestCreate[FPGWord[g, {1, 2}] ** FPGWord[g, {-2, 1}], FPGWord[g, {}], TestID -> "FPGWord-ProductReducesToIdentity"]
TestCreate[FPGWord[g, {1}]^2, FPGWord[g, {}], TestID -> "FPGWord-GeneratorSquare"]
TestCreate[FPGWord[g, {2}]^2, FPGWord[g, {}], TestID -> "FPGWord-GeneratorSquareSecond"]

TestCreate[FPGSubgroup[g, {FPGWord[g, {1}]}]["ParentGroup"], g, TestID -> "FPGSubgroup-ParentGroup"]
TestCreate[FPGSubgroup[g, {FPGWord[g, {1}], FPGWord[g, {2}]}]["Generators"], {FPGWord[g, {1}], FPGWord[g, {2}]}, TestID -> "FPGSubgroup-Generators"]
TestCreate[FPGSubgroup[g, {FPGWord[g, {1}], FPGWord[g, {2}]}]["GeneratorCount"], 2, TestID -> "FPGSubgroup-GeneratorCount"]
TestCreate[FPGSubgroup[g, {}]["GeneratorCount"], 0, TestID -> "FPGSubgroup-Trivial"]

TestCreate[FPGSubgroup[g, {FPGWord[g, {1}], FPGWord[g, {2}]}], FPGSubgroup[g, {FPGWord[g, {1}], FPGWord[g, {2}]}], TestID -> "FPGSubgroup-Valid"]
TestCreate[FPGSubgroup[g, {FPGWord[g2, {1}]}], $Failed, ExpectedMessages -> {FPGSubgroup::BadGenerators}, TestID -> "FPGSubgroup-WrongParentGroup"]