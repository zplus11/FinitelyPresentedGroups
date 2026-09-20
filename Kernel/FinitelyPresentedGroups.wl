(* ::Package:: *)

(* ::Section:: *)
(*Package Header*)


BeginPackage["Taggar`FinitelyPresentedGroups`"];


(* ::Text:: *)
(*Declare your public symbols here:*)


FinitelyPresentedGroup;
FPGHomomorphism;
FPGSubgroup;
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


FinitelyPresentedGroup /: FinitelyPresentedGroup[gens_List, _]["GeneratorList"] :=
	gens
FinitelyPresentedGroup /: FinitelyPresentedGroup[_, rels_List]["RelatorList"] :=
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


(* ::Subsection:: *)
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


ClearAll[FPGWordQ, FPGWordLength, FPGWordGenerators];
FPGWordQ[FPGWord[G_FinitelyPresentedGroup, word_List]] := True
FPGWordQ[_] := False
FPGWordLength[FPGWord[_, word_List]] := Length[word]
FPGWordGenerators[FPGWord[G_FinitelyPresentedGroup, word_List]] :=
	DeleteDuplicates[Abs /@ word]


ClearAll[SubstituteWord];
SubstituteWord[word_List, images_List] :=
	Flatten[Replace[word, {
		i_Integer /; i > 0 :> images[[i, 2]],
		i_Integer /; i < 0 :> Reverse[-images[[-i, 2]]]
	}, {1}]]


(* ::Text:: *)
(*Formatting*)


FPGWord /:
	MakeBoxes[FPGWord[FinitelyPresentedGroup[gens_List, rels_List], word_List], StandardForm] :=
		If[word === {}, ToBoxes[1],
			RowBox@Riffle[
				Replace[Split[word], x : {i_Integer ..} :>
					If[Length[x] == 1,
						ToBoxes[If[i > 0, gens[[i]], Superscript[gens[[-i]], -1]]],
						SuperscriptBox[ToBoxes[If[i > 0, gens[[i]], Superscript[gens[[-i]], -1]]], ToBoxes[Length[x]]]
					], {1}],
				"\[ThinSpace]"]]


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


FPGWordReduce[$Failed] := $Failed


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


(* ::Subsection:: *)
(*Subgroups*)


ClearAll[FPGSubgroup];
FPGSubgroup::usage =
	"FPGSubgroup[G, generators] represents a subgroup of G generated by generators.";
FPGSubgroup::BadGenerators =
	"The subgroup generators must be FPGWord expressions belonging to the same group.";


FPGSubgroup[G_FinitelyPresentedGroup, gens_List] /;
	!And @@ (MatchQ[#, FPGWord[G, _List]] & /@ gens) :=
		(Message[FPGSubgroup::BadGenerators]; $Failed)


FPGSubgroup /: FPGSubgroup[G_FinitelyPresentedGroup, gens_List]["ParentGroup"] :=
	G
FPGSubgroup /: FPGSubgroup[G_FinitelyPresentedGroup, gens_List]["GeneratorList"] :=
	gens
FPGSubgroup /: FPGSubgroup[G_FinitelyPresentedGroup, gens_List]["GeneratorCount"] :=
	Length[gens]


(* ::Subsection:: *)
(*Homomorphisms*)


ClearAll[FPGHomomorphism];
FPGHomomorphism::usage =
	"FPGHomomorphism[G, H, images] represents a homomorphism from G to H determined by images.";
FPGHomomorphism::BadImages =
	"The images must be valid FPGWord expressions in the target group.";
FPGHomomorphism::NotHomomorphism =
	"The proposed generator images do not satisfy the relators of the source group.";
FPGHomomorphism::WrongDomain =
	"The word must belong to the domain of the homomorphism.";


FPGHomomorphism[
	G : FinitelyPresentedGroup[gens_List, rels_List],
	H : FinitelyPresentedGroup[_, _],
	images_List
] /; Length[images] =!= Length[gens] :=
	(Message[FPGHomomorphism::BadImages]; $Failed)
FPGHomomorphism[
	G : FinitelyPresentedGroup[gens_List, rels_List],
	H : FinitelyPresentedGroup[_, _],
	images_List
] /; \[Not] And @@ (MatchQ[#, FPGWord[H, _List]] & /@ images) :=
	(Message[FPGHomomorphism::BadImages]; $Failed)
FPGHomomorphism[
	G : FinitelyPresentedGroup[gens_List, rels_List],
	H_FinitelyPresentedGroup,
	images_List
] /; \[Not] And @@ (
	FPGWordReduce[
		FPGWord[H, SubstituteWord[
			ParseWord[#, AssociationThread[gens, Range[Length[gens]]]],
			images]]
	] === FPGWord[H, {}] & /@ rels) :=
	(Message[FPGHomomorphism::NotHomomorphism]; $Failed)


FPGHomomorphism /:
	h : FPGHomomorphism[G_FinitelyPresentedGroup, H_FinitelyPresentedGroup, images_List][
		FPGWord[K_FinitelyPresentedGroup, word_List]
	] /; K =!= G :=
	(Message[FPGHomomorphism::WrongDomain]; $Failed)


FPGHomomorphism /:
	h_FPGHomomorphism[word_FPGWord] :=
		Module[
			{G, H, images},
			
			{G, H, images} = List @@ h;
			FPGWordReduce[FPGWord[H, SubstituteWord[word[[2]], images]]]]


(* ::Section::Closed:: *)
(*Package Footer*)


End[];
EndPackage[];
