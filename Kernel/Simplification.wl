(* ::Package:: *)

(* ::Section:: *)
(*Package Header*)


Begin["Taggar`FinitelyPresentedGroups`Private`"];


(* ::Section:: *)
(*Definitions*)


(* ::Subsection:: *)
(*Word helpers*)


(* ::Text:: *)
(*Cyclic reduction of a word by removing inverse pairs at the two ends:*)


ClearAll[CyclicReduce];
CyclicReduce[word_List] :=
	Module[
		{w = FreeReduce[word], n, k = 0},

		n = Length[w];
		While[2 k + 2 <= n && w[[k + 1]] + w[[n - k]] == 0, k++];
		w[[k + 1 ;; n - k]]]


(* ::Text:: *)
(*Two cyclically reduced relators have the same normal closure if one is a cyclic conjugate of the other or of its inverse. The key is the smallest such conjugate:*)


ClearAll[RelatorKey];
RelatorKey[word_List] :=
	If[word === {},
		{},
		First @ Sort @ Join[CyclicConjugates[word], CyclicConjugates[InvertWord[word]]]]


(* ::Text:: *)
(*Free and cyclic reduction, removal of trivial relators and of duplicates up to rotation and inversion. The result is sorted by length so that it is deterministic:*)


ClearAll[TietzeNormalise];
TietzeNormalise[rels_List] :=
	SortBy[
		DeleteDuplicatesBy[DeleteCases[CyclicReduce /@ rels, {}], RelatorKey],
		{Length, Identity}]


(* ::Text:: *)
(*A candidate is {relator index,generator index,position} *)


ClearAll[TietzeCandidates];
TietzeCandidates[rels_List] :=
	Join @@ MapIndexed[
		Function[{r, idx},
			{First @ idx, #, First @ FirstPosition[Abs[r], #]} & /@
				Keys @ Select[Counts[Abs[r]], # == 1 &]],
		rels]


ClearAll[TietzeCost];
TietzeCost[rels_List, {ri_Integer, g_Integer, _Integer}] :=
	With[
		{len = Length @ rels[[ri]],
		occ = Total[Count[Abs[#], g] & /@ Delete[rels, ri]]},

		(len - 2) occ - len]


(* ::Text:: *)
(*Substitution:*)


ClearAll[TietzeSubstitute];
TietzeSubstitute[word_List, g_Integer, rep_List] :=
	Flatten[
		Replace[word, {g -> rep, -g -> InvertWord[rep], x_ :> {x}}, {1}],
		1]


(* ::Text:: *)
(*Elimination:*)


ClearAll[TietzeEliminate];
TietzeEliminate[{gens_List, rels_List}, {ri_Integer, g_Integer, p_Integer}] :=
	Module[
		{r = rels[[ri]], s, w, rep, shift, rest},

		s = Sign @ r[[p]];
		w = Join[InvertWord @ Take[r, p - 1], InvertWord @ Drop[r, p]];
		rep = If[s == 1, w, InvertWord[w]];
		shift = If[Abs[#] > g, # - Sign[#], #] &;
		rest = Map[
			Function[rel,
				If[MemberQ[rel, g | -g],
					shift /@ CyclicReduce[TietzeSubstitute[rel, g, rep]],
					shift /@ rel]],
			Delete[rels, ri]];
		{Delete[gens, g],
		SortBy[DeleteDuplicatesBy[DeleteCases[rest, {}], RelatorKey], {Length, Identity}]}]


(* ::Text:: *)
(*An elimination which would increase the total length by more than $TietzeMaxGrowth is skipped:*)


$TietzeMaxGrowth = 100;


ClearAll[TietzeEliminateAll];
TietzeEliminateAll[state : {_List, _List}] :=
	Module[
		{s = state, rels, cands, occ, shortCand, costs, bestIdx},

		While[True,
			rels = s[[2]];
			cands = TietzeCandidates[rels];
			If[cands === {}, Break[]];
			(* Length <= 2 relators always have non-positive growth; eliminate immediately *)
			shortCand = SelectFirst[cands, Length[rels[[#[[1]]]]] <= 2 &, None];
			If[shortCand =!= None,
				s = TietzeEliminate[s, shortCand];
				Continue[]];
			occ = Counts[Abs[Flatten[rels]]];
			costs = ((Length[rels[[#[[1]]]]] - 2) (Lookup[occ, #[[2]], 1] - 1) - Length[rels[[#[[1]]]]]) & /@ cands;
			bestIdx = First @ Ordering[costs, 1];
			If[costs[[bestIdx]] > $TietzeMaxGrowth, Break[]];
			s = TietzeEliminate[s, cands[[bestIdx]]]];
		s]


(* ::Subsection:: *)
(*Relator manipulations*)


(* ::Text:: *)
(*Replace a relator Subscript[r, i] by (a conjugate of Subscript[r, i])(a conjugate of \!\(\*SuperscriptBox[*)
(*SubscriptBox[\(r\), \(j\)], \(\[PlusMinus]1\)]\)), j!=i. Rotations are conjugates, so the normal closure is unchanged. Only a strict decrease of the length is accepted, and one best replacement is applied per call...*)


ClearAll[TietzeShorten];
TietzeShorten[rels_List] :=
	Module[
		{n = Length[rels], conj, invConj, genSets, best = {0}, cand, gain},

		If[n <= 1, Return[rels]];
		conj = CyclicConjugates /@ rels;
		invConj = CyclicConjugates @* InvertWord /@ rels;
		genSets = DeleteDuplicates @* Abs /@ rels;
		Do[
			If[i != j && IntersectingQ[genSets[[i]], genSets[[j]]],
				Do[
					Do[
						If[a[[-1]] + b[[1]] == 0 || b[[-1]] + a[[1]] == 0,
							cand = CyclicReduce[Join[a, b]];
							gain = Length[rels[[i]]] - Length[cand];
							If[gain > best[[1]], best = {gain, i, cand}]],
						{a, conj[[i]]}, {b, s}],
					{s, {conj[[j]], invConj[[j]]}}]],
			{i, n}, {j, n}];
		If[best === {0}, rels, ReplacePart[rels, best[[2]] -> best[[3]]]]]


(* ::Text:: *)
(*Every effective step lowers the total length by at least one, which bounds the number of iterations:*)


ClearAll[TietzeShortenAll];
TietzeShortenAll[rels_List] :=
	FixedPoint[TietzeNormalise @ TietzeShorten[#] &, rels, 1 + Total[Length /@ rels]]


(* ::Subsection:: *)
(*TietzeSimplify*)


ClearAll[TietzeRound];
TietzeRound[state : {_List, _List}] :=
	With[{s = TietzeEliminateAll[state]}, {s[[1]], TietzeShortenAll[s[[2]]]}]


ClearAll[TietzeSimplify];
TietzeSimplify::usage =
	"TietzeSimplify[group] returns a FinitelyPresentedGroup isomorphic to group.";


TietzeSimplify[G : _FinitelyPresentedGroup] :=
	Module[
		{state},

		state = FixedPoint[TietzeRound,
			{G["GeneratorList"], TietzeNormalise @ NormaliseRelators[G]}];
		FinitelyPresentedGroup[state[[1]], WordToExpression[state[[1]], #] & /@ state[[2]]]]


(* ::Text:: *)
(*A free group cannot be simplified:*)


TietzeSimplify[G : _FreeGroup] := G


(* ::Section:: *)
(*Package Footer*)


End[];
