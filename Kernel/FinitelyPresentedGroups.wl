(* ::Package:: *)

(* ::Section:: *)
(*Package Header*)


BeginPackage["Taggar`FinitelyPresentedGroups`"];


(* ::Text:: *)
(*Declare your public symbols here:*)


FinitelyPresentedGroup;
FPGWord;
FPGWordReduce;


Begin["`Private`"];


(* ::Section:: *)
(*Definitions*)


(* ::Text:: *)
(*Define your public and private symbols here:*)


ClearAll[FinitelyPresentedGroup];
FinitelyPresentedGroup::usage =
	"FinitelyPresentedGroup[generators, relators] represents a finitely presented group.";
FinitelyPresentedGroup::DuplicateGenerators =
	"The generators must be distinct.";
FinitelyPresentedGroup::BadGenerators =
	"Each generator must be an atomic expression.";
FinitelyPresentedGroup::BadRelators =
	"The relators must be valid words in the generators.";


(* ::Text:: *)
(*Some properties*)


FinitelyPresentedGroup /: FinitelyPresentedGroup[gens_List, _]["Generators"] :=
	gens
FinitelyPresentedGroup /: FinitelyPresentedGroup[_, rels_List]["Relators"] :=
	rels
FinitelyPresentedGroup /: FinitelyPresentedGroup[gens_List, _]["GeneratorCount"] :=
	Length[gens]
FinitelyPresentedGroup /: FinitelyPresentedGroup[_, rels_List]["RelatorCount"] :=
	Length[rels]


(* ::Text:: *)
(*Parsing group words*)


ParseWord[1, _Association] :=
	{}
ParseWord[x_, map_Association] /; KeyExistsQ[map, x] :=
	{map[x]}
ParseWord[NonCommutativeMultiply[args___], map_Association] :=
	Flatten[ParseWord[#, map] & /@ {args}]
ParseWord[Inverse[x_], map_Association] :=
	Reverse[-ParseWord[x, map]];
ParseWord[x_^n_Integer, map_Association] :=
	If[n >= 0,
		Flatten[ConstantArray[ParseWord[x, map], n]],
		Flatten[ConstantArray[Reverse[-ParseWord[x, map]], -n]]]
ParseWord[x_, map_Association] /; IntegerQ[x] :=
	{x}


(* ::Text:: *)
(*Free reduction*)


FreeReduce[word_List] :=
	Module[
		{stack = {}, x},
		
		Do[
			If[stack =!= {} && Last[stack] === -x,
				stack = Most[stack], (* else *) AppendTo[stack, x]],
			{x, word}];
		stack]


ValidRelatorsQ[gens_List, rels_List] :=
	Module[
		{map},
		
		map = AssociationThread[gens, Range[Length[gens]]];
		And @@ (ValidRelatorQ[#, map] & /@ rels)]
ValidRelatorQ[rel_, map_Association] :=
	MatchQ[
		Quiet @ Check[ParseWord[rel, map], $Failed],
		{___Integer}]


(* ::Text:: *)
(*Invalid forms:*)


FinitelyPresentedGroup[gens_List, rels_List] /; !DuplicateFreeQ[gens] :=
	(Message[FinitelyPresentedGroup::DuplicateGenerators]; $Failed)
FinitelyPresentedGroup[gens_List, rels_List] /; !And @@ (AtomQ /@ gens) :=
	(Message[FinitelyPresentedGroup::BadGenerators]; $Failed)
FinitelyPresentedGroup[gens_List, rels_List] /; !ValidRelatorsQ[gens, rels] :=
	(Message[FinitelyPresentedGroup::BadRelators]; $Failed)


(* ::Text:: *)
(*Group words*)


ClearAll[FPGWord];
FPGWord::usage =
	"FPGWord[G, indices] represents a group word in G determined by indices.";
FPGWord::BadWord =
	"The word contains an invalid generator index.";


FPGWord[FinitelyPresentedGroup[gens_List, rels_List], ints_List] /;
	\[Not] And @@ (IntegerQ[#] && # =!= 0 && Abs[#] <= Length[gens] &
		/@ ints) :=
			(Message[FPGWord::BadWord]; $Failed)


(* ::Text:: *)
(*Word reduction*)


CyclicConjugates[word_List] :=
	If[word === {}, {}, RotateLeft[word, #] & /@ Range[0, Length[word] - 1]]


NormaliseRelator[lhs_ == rhs_, map_Association] :=
	FreeReduce[Join[ParseWord[lhs, map], Reverse[-ParseWord[rhs, map]]]]
NormaliseRelator[rel_, map_Association] :=
	FreeReduce[ParseWord[rel, map]];


NormaliseRelators[FinitelyPresentedGroup[gens_List, rels_List]] :=
	Module[
		{map},
		
		map = AssociationThread[gens, Range[Length[gens]]];
		NormaliseRelator[#, map] & /@ rels]


RelatorRules[G_FinitelyPresentedGroup] :=
	Module[
		{rs},
		
		rs = DeleteCases[NormaliseRelators[G], {}];
		
		DeleteDuplicates[
			Join @@ (
				Function[r, Join[CyclicConjugates[r],
						CyclicConjugates[Reverse[-r]]]] /@ rs
			)]]


ReduceByRelators[G_FinitelyPresentedGroup, word_List] :=
	Module[
		{rules = RelatorRules[G], w = FreeReduce[word], changed = True, pos, r},

		While[changed,
			changed = False;

			For[r = 1, r <= Length[rules], r++,
				If[(pos = SequencePosition[w, rules[[r]]]) =!= {},
					pos = First[pos];
					w = Join[
						Take[w, pos[[1]] - 1],
						Drop[w, pos[[2]]]
					];
					w = FreeReduce[w];
					changed = True;
					Break[]]]];

		w]


ClearAll[FPGWordReduce];
FPGWordReduce::usage =
	"FPGWordReduce[word] reduces the given group word.
FPGWordReduce[G, indices] reduces the word given by indices in G.";


FPGWordReduce[FPGWord[G_FinitelyPresentedGroup, word_List]] :=
	FPGWord[G, ReduceByRelators[G, word]]
FPGWordReduce[G_FinitelyPresentedGroup, word_List] :=
	FPGWordReduce[FPGWord[G, word]]


(* ::Text:: *)
(*Algebra of words*)


FPGWord /:
	Inverse[FPGWord[
		G : FinitelyPresentedGroup[gens_List, rels_List],
		word_List
	]] :=
		FPGWordReduce @ FPGWord[G, Reverse[-word]]


FPGWord /:
	FPGWord[G : FinitelyPresentedGroup[gens_List, rels_List], word1_List] **
		FPGWord[G : FinitelyPresentedGroup[gens_List, rels_List], word2_List] :=
			FPGWordReduce @ FPGWord[G, Join[word1, word2]]


FPGWord /:
	Power[
		FPGWord[G : FinitelyPresentedGroup[gens_List, rels_List], word_List],
		n_Integer] :=
			FPGWordReduce @ FPGWord[
				G,
				If[n >= 0,
					Flatten[ConstantArray[word, n]],
					Flatten[ConstantArray[Reverse[-word], -n]]]]


(* ::Section::Closed:: *)
(*Package Footer*)


End[];
EndPackage[];
