(* ::Package:: *)

(* ::Section:: *)
(*Package Header*)


BeginPackage["Taggar`FinitelyPresentedGroups`"];


(* ::Text:: *)
(*Declare your public symbols here:*)


AlexanderMatrix;
CosetTable;
ElementEqualQ;
ElementReduce;
FinitelyPresentedGroup;
FoxD;
FreeGroup;
TietzeSimplify;


Begin["`Private`"];


(* ::Section:: *)
(*Definitions*)


(* ::Text:: *)
(*Load other files:*)


Get /@ {
	"Taggar`FinitelyPresentedGroups`CosetTable`",
	"Taggar`FinitelyPresentedGroups`Simplification`"
}


(* ::Text:: *)
(*Main head*)


ClearAll[FinitelyPresentedGroup];
FinitelyPresentedGroup::usage =
	"FinitelyPresentedGroup[generators, relators] represents a finitely presented group.";
FinitelyPresentedGroup::DuplicateGenerators =
	"The generators must be distinct.";
FinitelyPresentedGroup::BadGenerators =
	"Each generator must be an atomic expression.";
FinitelyPresentedGroup::BadRelators =
	"The relators must be valid words in the generators.";
FinitelyPresentedGroup::SymbolDefined =
	"The generator symbol `1` already has definitions or attributes. Clearing them.";
FinitelyPresentedGroup::NotEnumerable =
	"The group could not be enumerated within `1` cosets; it may be infinite.";


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


If[\[Not] AssociationQ @ $AbelianInvariantsCache,
	$AbelianInvariantsCache = <||>];

FinitelyPresentedGroup /: (G : FinitelyPresentedGroup[gens_List, _])["AbelianInvariants"] :=
	If[KeyExistsQ[$AbelianInvariantsCache, G],
		$AbelianInvariantsCache[G],
		Module[
			{ng = Length[gens], rels, m, res},

			rels = DeleteCases[NormaliseRelators[G], {}];
			res = If[rels === {},
				ConstantArray[0, ng],
				m = Table[
					Module[{row = ConstantArray[0, ng]},
						Do[If[x > 0, row[[x]]++, row[[-x]]--], {x, w}];
						row],
					{w, rels}];
				DeleteCases[PadRight[Abs @ Diagonal @ SmithDecomposition[m][[2]], ng], 1]];
			If[Length[$AbelianInvariantsCache] > 200, $AbelianInvariantsCache = <||>];
			$AbelianInvariantsCache[G] = res]]


(* ::Text:: *)
(*Parsing group words*)


ClearAll[GeneratorMap];
If[\[Not] AssociationQ @ $GeneratorMapCache,
	$GeneratorMapCache = <||>];
GeneratorMap[G : _FinitelyPresentedGroup | _FreeGroup] :=
	If[KeyExistsQ[$GeneratorMapCache, G],
		$GeneratorMapCache[G],
		If[Length[$GeneratorMapCache] > 200, $GeneratorMapCache = <||>];
		$GeneratorMapCache[G] = AssociationThread[G["GeneratorList"], Range @ G["GeneratorCount"]]]


ClearAll[ParseWord];
ParseWord[1, _Association] :=
	{}
ParseWord[x_, map_Association] /; KeyExistsQ[map, x] :=
	{map[x]}
ParseWord[x_^0, _Association] :=
	{}
ParseWord[x_^n_Integer, map_Association] /; KeyExistsQ[map, x] :=
	If[n > 0, ConstantArray[map[x], n], ConstantArray[-map[x], -n]]
ParseWord[NonCommutativeMultiply[args___], map_Association] :=
	Flatten[ParseWord[#, map] & /@ {args}]
ParseWord[Inverse[x_], map_Association] :=
	Reverse[-ParseWord[x, map]]
ParseWord[x_^n_Integer, map_Association] :=
	If[n >= 0,
		Flatten[ConstantArray[ParseWord[x, map], n]],
		Flatten[ConstantArray[Reverse[-ParseWord[x, map]], -n]]]
ParseWord[w : {___Integer}, map_Association] /;
	w === {} || (Min[w] >= -Length[map] && Max[w] <= Length[map] && FreeQ[w, 0]) :=
		w
ParseWord[_, _Association] :=
	$Failed


ClearAll[ToWord];
ToWord[G : _FinitelyPresentedGroup | _FreeGroup, x_] :=
	With[{w = Quiet @ Check[ParseWord[x, GeneratorMap[G]], $Failed]},
		If[MatchQ[w, {___Integer}], w, $Failed]]


ClearAll[WordToExpression];
WordToExpression[_List, {}] :=
	1
WordToExpression[gens_List, w_List] :=
	With[
		{factors = With[{x = First[#], m = Length[#]}, gens[[Abs[x]]]^(Sign[x] m)] & /@ Split[w]},

		If[Length[factors] == 1, First[factors], NonCommutativeMultiply @@ factors]]


(* ::Text:: *)
(*Free reduction*)


ClearAll[FreeReduce];
FreeReduce[word_List] :=
	Module[
		{stack, top = 0, x},

		stack = ConstantArray[0, Length[word]];
		Do[
			If[top > 0 && stack[[top]] + x == 0,
				top--,
				top++; stack[[top]] = x],
			{x, word}];
		Take[stack, top]]


ClearAll[ValidRelatorsQ];
ValidRelatorsQ[gens_List, rels_List] :=
	With[{map = AssociationThread[gens, Range[Length[gens]]]},
		AllTrue[rels, ValidRelatorQ[#, map] &]]
ClearAll[ValidRelatorQ];
ValidRelatorQ[rel_, map_Association] :=
	MatchQ[
		Quiet @ Check[ParseWord[rel, map], $Failed],
		{___Integer}]
ValidRelatorQ[lhs_ == rhs_, map_Association] :=
	ValidRelatorQ[lhs, map] && ValidRelatorQ[rhs, map]


(* ::Text:: *)
(*Invalid forms:*)


FinitelyPresentedGroup[gens_List, rels_List] /; \[Not] DuplicateFreeQ[gens] :=
	(Message[FinitelyPresentedGroup::DuplicateGenerators]; $Failed)
FinitelyPresentedGroup[gens_List, rels_List] /; \[Not] And @@ (AtomQ /@ gens) :=
	(Message[FinitelyPresentedGroup::BadGenerators]; $Failed)
FinitelyPresentedGroup[gens_List, rels_List] /; \[Not] ValidRelatorsQ[gens, rels] :=
	(Message[FinitelyPresentedGroup::BadRelators]; $Failed)


(* ::Text:: *)
(*Free group on generators is then the finitely presented group generated by generators subject to no relators:*)


ClearAll[FreeGroup];
FreeGroup::usage =
	"FreeGroup[generators] represents the free group on generators. It is a finitely presented group without relators and can be used wherever a FinitelyPresentedGroup is expected.";
FreeGroup::DuplicateGenerators =
	"The generators must be distinct.";
FreeGroup::BadGenerators =
	"Each generator must be an atomic expression.";


(* ::Text:: *)
(*Invalid forms:*)


FreeGroup[gens_List] /; \[Not] DuplicateFreeQ[gens] :=
	(Message[FreeGroup::DuplicateGenerators]; $Failed)
FreeGroup[gens_List] /; \[Not] And @@ (AtomQ /@ gens) :=
	(Message[FreeGroup::BadGenerators]; $Failed)


(* ::Text:: *)
(*Properties:*)


FreeGroup /: FreeGroup[gens_List]["GeneratorList"] :=
	gens
FreeGroup /: FreeGroup[_List]["RelatorList"] :=
	{}
FreeGroup /: FreeGroup[gens_List]["GeneratorCount"] :=
	Length[gens]
FreeGroup /: FreeGroup[_List]["RelatorCount"] :=
	0
FreeGroup /: FreeGroup[gens_List]["AbelianInvariants"] :=
	ConstantArray[0, Length[gens]]


(* ::Text:: *)
(*Conversion to the explicit presentation:*)


FinitelyPresentedGroup[FreeGroup[gens_List]] :=
	FinitelyPresentedGroup[gens, {}]


(* ::Text:: *)
(*A free product of two finitely presented groups is merely concatenation of the generators and relators. For this purpose, we demand that the generator sets must be disjoint:*)


FinitelyPresentedGroup::DisjointGenerators =
	"The generators of underlying groups are expected to be disjoint.";
FinitelyPresentedGroup /:
	NonCommutativeMultiply[G1_FinitelyPresentedGroup, G2_FinitelyPresentedGroup] /;
	G1["GeneratorList"] \[Intersection] G2["GeneratorList"] != {} :=
		(Message[FinitelyPresentedGroup::DisjointGenerators]; $Failed)


FinitelyPresentedGroup /:
	NonCommutativeMultiply[G1_FinitelyPresentedGroup, G2_FinitelyPresentedGroup] :=
		FinitelyPresentedGroup[Join[G1["GeneratorList"], G2["GeneratorList"]],
			Join[G1["RelatorList"], G2["RelatorList"]]]
FinitelyPresentedGroup /:
	NonCommutativeMultiply[G1_FinitelyPresentedGroup, G2_FreeGroup] :=
		NonCommutativeMultiply[G1, FinitelyPresentedGroup[G2]]
FinitelyPresentedGroup /:
	NonCommutativeMultiply[G1_FreeGroup, G2_FinitelyPresentedGroup] :=
		NonCommutativeMultiply[FinitelyPresentedGroup[G1], G2]
FreeGroup /:
	NonCommutativeMultiply[G1_FreeGroup, G2_FreeGroup] :=
		NonCommutativeMultiply[FinitelyPresentedGroup[G1], FinitelyPresentedGroup[G2]]


(* ::Subsection:: *)
(*PermutationGroup -> FinitelyPresentedGroup*)


ClearAll[GeneratorSymbols];
GeneratorSymbols[k_Integer] :=
	Table[Unique["x"], k]


FinitelyPresentedGroup[CyclicGroup[n_Integer?Positive]] :=
	Module[
		{a = GeneratorSymbols[1]},
		
		FinitelyPresentedGroup[a, a^n]]


FinitelyPresentedGroup[DihedralGroup[n_Integer?Positive]] :=
	Module[
		{a, b},
		
		{a, b} = GeneratorSymbols[2];
		FinitelyPresentedGroup[{a, b}, {a^n, b^2, NonCommutativeMultiply[a, b]^2}]]


FinitelyPresentedGroup[AbelianGroup[ns : {__Integer?Positive}]] :=
	Module[
		{x = GeneratorSymbols[Length[ns]]},
		
		FinitelyPresentedGroup[x,
			Join[
				MapThread[#1^#2 &, {x, ns}],
				NonCommutativeMultiply[#1, #2, #1^-1, #2^-1] & @@@ Subsets[x, {2}]]]]


FinitelyPresentedGroup[SymmetricGroup[n_Integer /; n >= 2]] :=
	Module[
		{s = GeneratorSymbols[n - 1]},
		
		FinitelyPresentedGroup[s,
			Join[
				#^2 & /@ s,
				Table[NonCommutativeMultiply[s[[i]], s[[i + 1]]]^3, {i, n - 2}],
				Flatten @ Table[NonCommutativeMultiply[s[[i]], s[[j]]]^2, {i, n - 1}, {j, i + 2, n - 1}]]]]


(* ::Text:: *)
(*Cannon's method. The Cayley graph is known, so an edge is "proved" once its Schreier generator is known to follow from the chosen relators. Tree edges are proved from the start. A relator traced from any vertex which runs through exactly one unproved edge proves that edge. Only when no more deductions are possible is a new relator taken from the shortest unproved edge. When every edge is proved the presentation is complete, and no coset enumeration is needed:*)


$MaxPermutationOrder = 10^7;
$DirectCayleyOrderLimit = 20000;
FinitelyPresentedGroup::TooLarge =
	"The group has order `1`, which exceeds the limit `2` for conversion.";


ClearAll[CayleyData];
CayleyData[perms_List, degree_Integer, order_Integer] :=
	Module[
		{k = Length[perms], elements, index, next, prev, words, count = 1, h, j},

		elements = ConstantArray[Range[degree], order];
		index = <|Range[degree] -> 1|>;
		next = ConstantArray[0, {order, k}];
		prev = ConstantArray[0, {order, k}];
		words = ConstantArray[{}, order];
		Do[
			Do[
				(* apply elements[[v]] first and then the generator, as in PermutationProduct *)
				h = perms[[i]][[elements[[v]]]];
				j = Lookup[index, Key[h], 0];
				If[j == 0,
					j = ++count;
					elements[[j]] = h;
					index[h] = j;
					words[[j]] = Append[words[[v]], i]];
				next[[v, i]] = j;
				prev[[j, i]] = v,
				{i, k}],
			{v, order}];
		{next, prev, words}]


ClearAll[MakeCannonDeducer, CannonDeduce];
MakeCannonDeducer[target_String] :=
	Compile[
		{{next, _Integer, 2}, {prev, _Integer, 2}, {wordsFlat, _Integer, 1},
		{wordsStarts, _Integer, 1}, {powLens, _Integer, 1}, {sortedEdges, _Integer, 2},
		{order, _Integer}, {k, _Integer}},
		Module[
			{proved, queue, head = 1, tail = 0, nEdges = order k,
			relsFlat, relsLen = 0, relsCap = 1024,
			relStart, relEnd, nRels = 0, relCap = 256,
			occHead, occRel, occPos, occNext, nOcc = 0, occCap = 1024,
			cand, candLen = 0, candCap = 256,
			v = 0, i = 0, m = 0, e = 0, x = 0, w = 0, open = 0, found = 0,
			p = 0, q = 0, o = 0, rIdx = 0, start = 0, r0 = 0, r1 = 0,
			u0 = 0, u1 = 0, w0 = 0, w1 = 0, c1 = 0, c2 = 0, cur = 0,
			ei = 0, out, outPos = 1},

			proved = ConstantArray[0, nEdges];
			queue = ConstantArray[0, nEdges];
			relsFlat = ConstantArray[0, relsCap];
			relStart = ConstantArray[0, relCap];
			relEnd = ConstantArray[0, relCap];
			occHead = ConstantArray[0, k];
			occRel = ConstantArray[0, occCap];
			occPos = ConstantArray[0, occCap];
			occNext = ConstantArray[0, occCap];
			cand = ConstantArray[0, candCap];

			(* Mark tree edges as proved *)
			For[v = 1, v <= order, v++,
				u0 = wordsStarts[[v]];
				u1 = wordsStarts[[v + 1]] - 1;
				For[i = 1, i <= k, i++,
					w = next[[v, i]];
					w0 = wordsStarts[[w]];
					w1 = wordsStarts[[w + 1]] - 1;
					If[w1 >= w0 && w1 - w0 == u1 - u0 + 1 && wordsFlat[[w1]] == i,
						(* Check prefix equality *)
						open = 1;
						For[p = 0, p <= u1 - u0, p++,
							If[wordsFlat[[u0 + p]] != wordsFlat[[w0 + p]], open = 0; Break[]]];
						If[open == 1,
							e = (v - 1) k + i;
							If[proved[[e]] == 0, proved[[e]] = 1; tail++; queue[[tail]] = e]]]]];

			(* Helper macro-pattern: scan & propagate; start with power relators then sorted edges *)
			For[ei = 1 - k, ei <= nEdges, ei++,
				candLen = 0;
				If[ei <= 0,
					i = ei + k;
					m = powLens[[i]];
					If[m > candCap, candCap = 2 m; cand = ConstantArray[0, candCap]];
					For[p = 1, p <= m, p++, cand[[p]] = i];
					candLen = m,

					v = sortedEdges[[ei, 1]];
					i = sortedEdges[[ei, 2]];
					If[proved[[(v - 1) k + i]] == 0,
						u0 = wordsStarts[[v]];
						u1 = wordsStarts[[v + 1]] - 1;
						w = next[[v, i]];
						w0 = wordsStarts[[w]];
						w1 = wordsStarts[[w + 1]] - 1;
						(* CyclicReduce of words[[v]] . {i} . Invert[words[[w]]] *)
						m = (u1 - u0 + 1) + 1 + (w1 - w0 + 1);
						If[m > candCap, candCap = 2 m; cand = ConstantArray[0, candCap]];
						For[p = u0, p <= u1, p++,
							x = wordsFlat[[p]];
							If[candLen > 0 && cand[[candLen]] + x == 0, candLen--, candLen++; cand[[candLen]] = x]];
						If[candLen > 0 && cand[[candLen]] + i == 0, candLen--, candLen++; cand[[candLen]] = i];
						For[p = w1, p >= w0, p--,
							x = -wordsFlat[[p]];
							If[candLen > 0 && cand[[candLen]] + x == 0, candLen--, candLen++; cand[[candLen]] = x]];
						(* Cyclic reduction *)
						c1 = 1; c2 = candLen;
						While[c1 < c2 && cand[[c1]] + cand[[c2]] == 0, c1++; c2--];
						If[c1 > 1,
							For[p = c1, p <= c2, p++, cand[[p - c1 + 1]] = cand[[p]]]];
						candLen = Max[0, c2 - c1 + 1]]];

				If[candLen > 0,
					(* Add relator *)
					nRels++;
					If[nRels > relCap,
						relStart = Join[relStart, ConstantArray[0, relCap]];
						relEnd = Join[relEnd, ConstantArray[0, relCap]];
						relCap = 2 relCap];
					While[relsLen + candLen > relsCap,
						relsFlat = Join[relsFlat, ConstantArray[0, relsCap]];
						relsCap = 2 relsCap];
					relStart[[nRels]] = relsLen + 1;
					For[p = 1, p <= candLen, p++,
						relsLen++;
						relsFlat[[relsLen]] = cand[[p]];
						x = Abs[cand[[p]]];
						nOcc++;
						If[nOcc > occCap,
							occRel = Join[occRel, ConstantArray[0, occCap]];
							occPos = Join[occPos, ConstantArray[0, occCap]];
							occNext = Join[occNext, ConstantArray[0, occCap]];
							occCap = 2 occCap];
						occRel[[nOcc]] = nRels;
						occPos[[nOcc]] = p;
						occNext[[nOcc]] = occHead[[x]];
						occHead[[x]] = nOcc];
					relEnd[[nRels]] = relsLen;

					(* Scan new relator from every vertex *)
					r0 = relStart[[nRels]];
					r1 = relEnd[[nRels]];
					For[start = 1, start <= order, start++,
						cur = start; open = 0; found = 0;
						For[p = r0, p <= r1, p++,
							x = relsFlat[[p]];
							w = If[x > 0, next[[cur, x]], prev[[cur, -x]]];
							e = If[x > 0, (cur - 1) k + x, (w - 1) k - x];
							If[proved[[e]] == 0,
								open++; found = e;
								If[open > 1, Break[]]];
							cur = w];
						If[open == 1 && proved[[found]] == 0,
							proved[[found]] = 1; tail++; queue[[tail]] = found]];

					(* Propagate all newly proved edges *)
					While[head <= tail,
						e = queue[[head]];
						head++;
						v = Quotient[e - 1, k] + 1;
						i = e - (v - 1) k;
						o = occHead[[i]];
						While[o != 0,
							rIdx = occRel[[o]];
							p = occPos[[o]];
							r0 = relStart[[rIdx]];
							r1 = relEnd[[rIdx]];
							start = If[relsFlat[[r0 + p - 1]] > 0, v, next[[v, i]]];
							For[q = r0 + p - 2, q >= r0, q--,
								x = relsFlat[[q]];
								start = If[x > 0, prev[[start, x]], next[[start, -x]]]];
							cur = start; open = 0; found = 0;
							For[q = r0, q <= r1, q++,
								x = relsFlat[[q]];
								w = If[x > 0, next[[cur, x]], prev[[cur, -x]]];
								e = If[x > 0, (cur - 1) k + x, (w - 1) k - x];
								If[proved[[e]] == 0,
									open++; found = e;
									If[open > 1, Break[]]];
								cur = w];
							If[open == 1 && proved[[found]] == 0,
								proved[[found]] = 1; tail++; queue[[tail]] = found];
							o = occNext[[o]]]]]];

			out = ConstantArray[0, nRels + relsLen + 1];
			out[[1]] = nRels;
			outPos = 2;
			For[rIdx = 1, rIdx <= nRels, rIdx++,
				r0 = relStart[[rIdx]];
				r1 = relEnd[[rIdx]];
				out[[outPos]] = r1 - r0 + 1;
				outPos++;
				For[p = r0, p <= r1, p++,
					out[[outPos]] = relsFlat[[p]];
					outPos++]];
			out],
		CompilationTarget -> target,
		RuntimeOptions -> "Speed"]


CannonDeduce :=
	CannonDeduce = Quiet @ Check[MakeCannonDeducer["C"], MakeCannonDeducer["WVM"]]


ClearAll[PresentationWords];
PresentationWords[perms_List, degree_Integer, order_Integer] :=
	Module[
		{k = Length[perms], next, prev, words, powLens, wordsFlat, wordsStarts,
		sortedEdges, flatOut, nRels, pos = 2, len, rels},

		If[k == 0, Return[{}]];
		{next, prev, words} = CayleyData[perms, degree, order];
		powLens = Table[
			Module[{v = next[[1, i]], m = 1},
				While[v != 1, v = next[[v, i]]; m++];
				m],
			{i, k}];
		wordsFlat = Flatten[words];
		wordsStarts = 1 + Prepend[Accumulate[Length /@ words], 0];
		sortedEdges = SortBy[
			Flatten[Table[{v, i}, {v, order}, {i, k}], 1],
			Length[words[[#[[1]]]]] + Length[words[[next[[#[[1]], #[[2]]]]]]] &];
		flatOut = CannonDeduce[next, prev, wordsFlat, wordsStarts, powLens, sortedEdges, order, k];
		nRels = flatOut[[1]];
		rels = Table[
			len = flatOut[[pos++]];
			Take[flatOut, {pos, (pos += len) - 1}],
			{nRels}];
		rels]


ClearAll[OrbitSchreier];
OrbitSchreier[perms_List, degree_Integer, base_Integer] :=
	Module[
		{k = Length[perms], orbPos, orb = {base}, words = {{}}, head = 1,
		p, q, i, next, w},

		orbPos = ConstantArray[0, degree];
		orbPos[[base]] = 1;
		While[head <= Length[orb],
			p = orb[[head]];
			w = words[[head]];
			head++;
			For[i = 1, i <= k, i++,
				q = perms[[i, p]];
				If[orbPos[[q]] == 0,
					AppendTo[orb, q];
					AppendTo[words, Append[w, i]];
					orbPos[[q]] = Length[orb]]]];
		<|"Orbit" -> orb, "Pos" -> orbPos, "Words" -> words|>]


ClearAll[ApplyPermWord];
ApplyPermWord[perms_List, invPerms_List, degree_Integer, word_List] :=
	Fold[
		If[#2 > 0, perms[[#2]][[#1]], invPerms[[-#2]][[#1]]] &,
		Range[degree],
		word]


ClearAll[InvertPermList];
InvertPermList[p_List] :=
	Module[{inv = ConstantArray[0, Length[p]]},
		inv[[p]] = Range[Length[p]];
		inv]


ClearAll[StabChainBuild];
StabChainBuild[perms_List, degree_Integer, order_Integer] :=
	Module[
		{k = Length[perms], invPerms, base, sch, n, subOrder, orb, words, orbPos,
		sWord, sPerm, rawGens = {}, rawWords = {}, chosenPerms = {}, chosenWords = {},
		curOrd = 1, newOrd, subChain, sift, idPerm = Range[degree],
		rels = {}, subRels, subToParent, w, sIdx},

		If[order <= $DirectCayleyOrderLimit,
			Module[{elements, index, next, prev, cWords, count = 1, h, j},
				elements = ConstantArray[idPerm, order];
				index = <|idPerm -> 1|>;
				cWords = ConstantArray[{}, order];
				For[v = 1, v <= order, v++,
					For[i = 1, i <= k, i++,
						h = perms[[i]][[elements[[v]]]];
						If[\[Not] KeyExistsQ[index, h],
							count++;
							elements[[count]] = h;
							index[h] = count;
							cWords[[count]] = Append[cWords[[v]], i]]]];
				Return[<|
					"Relators" -> PresentationWords[perms, degree, order],
					"Sift" -> Function[perm, cWords[[index[perm]]]]|>]]];

		invPerms = InvertPermList /@ perms;
		base = SelectFirst[Range[degree], Function[pt, AnyTrue[perms, #[[pt]] != pt &]]];
		sch = OrbitSchreier[perms, degree, base];
		orb = sch["Orbit"];
		orbPos = sch["Pos"];
		words = sch["Words"];
		n = Length[orb];
		subOrder = order / n;

		(* Collect non-trivial Schreier generators *)
		Do[
			sWord = FreeReduce @ Join[words[[v]], {i}, InvertWord[words[[orbPos[[perms[[i, orb[[v]]]]]]]]]];
			If[sWord =!= {},
				sPerm = ApplyPermWord[perms, invPerms, degree, sWord];
				If[sPerm =!= idPerm,
					AppendTo[rawGens, sPerm];
					AppendTo[rawWords, sWord]]],
			{v, n}, {i, k}];

		(* Pick a minimal subset generating the stabiliser of order subOrder *)
		Do[
			If[\[Not] MemberQ[chosenPerms, rawGens[[idx]]],
				newOrd = GroupOrder[PermutationGroup[PermutationCycles /@ Append[chosenPerms, rawGens[[idx]]]]];
				If[newOrd > curOrd,
					AppendTo[chosenPerms, rawGens[[idx]]];
					AppendTo[chosenWords, rawWords[[idx]]];
					curOrd = newOrd;
					If[curOrd === subOrder, Break[]]]],
			{idx, Length[rawGens]}];

		subChain = StabChainBuild[chosenPerms, degree, subOrder];
		subToParent[sw_List] :=
			FreeReduce @ Flatten[If[# > 0, chosenWords[[#]], InvertWord[chosenWords[[-#]]]] & /@ sw];

		(* Lift defining relators of the stabiliser *)
		rels = subToParent /@ subChain["Relators"];

		(* Add Schreier consistency relators s_i == word(s_i in chosenPerms) *)
		Do[
			AppendTo[rels,
				CyclicReduce @ Join[rawWords[[idx]], InvertWord[subToParent[subChain["Sift"][rawGens[[idx]]]]]]],
			{idx, Length[rawGens]}];
		rels = DeleteDuplicates @ DeleteCases[rels, {}];

		(* Build sifter for G using this level + subChain *)
		sift = Function[perm,
			Module[{img = perm[[base]], w1, rem},
				w1 = words[[orbPos[[img]]]];
				rem = InvertPermList[ApplyPermWord[perms, invPerms, degree, w1]][[perm]];
				Join[subToParent[subChain["Sift"][rem]], w1]]];

		<|"Relators" -> rels, "Sift" -> sift|>]


ClearAll[PresentPermutations];
PresentPermutations[gens_List, order_Integer] :=
	Module[
		{degree, perms, syms, relWords},

		degree = Max[1, PermutationMax /@ gens];
		perms = PermutationList[#, degree] & /@ gens;
		syms = GeneratorSymbols[Length[perms]];
		relWords = If[order <= $DirectCayleyOrderLimit,
			PresentationWords[perms, degree, order],
			StabChainBuild[perms, degree, order]["Relators"]];
		FinitelyPresentedGroup[syms, WordToExpression[syms, #] & /@ relWords]]


FinitelyPresentedGroup[group : Alternatives[
	_PermutationGroup, _CyclicGroup, _DihedralGroup, _SymmetricGroup,
	_AlternatingGroup, _AbelianGroup, _MathieuGroupM11, _MathieuGroupM12,
	_MathieuGroupM22, _MathieuGroupM23, _MathieuGroupM24, _HigmanSimsGroupHS,
	_McLaughlinGroupMcL, _JankoGroupJ1, _JankoGroupJ2, _JankoGroupJ3,
	_JankoGroupJ4, _ConwayGroupCo1, _ConwayGroupCo2, _ConwayGroupCo3,
	_SuzukiGroupSuz, _HeldGroupHe, _RudvalisGroupRu, _FischerGroupFi22,
	_FischerGroupFi23, _FischerGroupFi24Prime, _TitsGroupT, _ONanGroupON,
	_HaradaNortonGroupHN, _ThompsonGroupTh, _LyonsGroupLy, _BabyMonsterGroupB,
	_MonsterGroupM
]] :=
	With[
		{order = GroupOrder[group]},

		If[order > $MaxPermutationOrder,
			Message[FinitelyPresentedGroup::TooLarge, order, $MaxPermutationOrder];
			$Failed,
			PresentPermutations[GroupGenerators[group], order]]]


(* ::Subsection:: *)
(*Group properties*)


(* ::Text:: *)
(*Order of a finitely presented group is the index of a cyclic subgroup times the order of that subgroup:*)


FinitelyPresentedGroup /: GroupOrder[G_FinitelyPresentedGroup] :=
	(* if the abelian invariants contain a zero, G is infite: *)
	If[\[Not] FreeQ[G["AbelianInvariants"], 0], Infinity,
		(* otherwise *)
		EnumerateOrder[G]]


FinitelyPresentedGroup /: GroupGenerators[G_FinitelyPresentedGroup] :=
	G["GeneratorList"]


$MaxGroupElements = 50000;
$MaxMultiplicationTableOrder = 2500;
$MaxCayleyGraphOrder = 20000;
FinitelyPresentedGroup::TooLargeOutput =
	"The group has order `1`, which exceeds the limit `2` for `3`.";


FinitelyPresentedGroup /: GroupElements[G_FinitelyPresentedGroup] :=
	With[{d = RegularData[G]},
		If[AssociationQ[d],
			With[{n = Length[d["Table"]], gens = G["GeneratorList"]},
				If[n > $MaxGroupElements,
					Message[FinitelyPresentedGroup::TooLargeOutput, n, $MaxGroupElements, "GroupElements"];
					$Failed,
					WordToExpression[gens, #] & /@ RegularWords[d]]],
			$Failed]]


FinitelyPresentedGroup /: GroupElementQ[G_FinitelyPresentedGroup, x_] :=
	ToWord[G, x] =!= $Failed


FinitelyPresentedGroup /: GroupElementPosition[G_FinitelyPresentedGroup, x_] :=
	With[{w = ToWord[G, x], d = RegularData[G]},
		If[w =!= $Failed && AssociationQ[d],
			ElementPosition[d["Table"], 2 G["GeneratorCount"], w],
			$Failed]]


FinitelyPresentedGroup /: GroupElementToWord[G_FinitelyPresentedGroup, x_] :=
	With[{w = ToWord[G, x]}, If[w === $Failed, $Failed, FreeReduce[w]]]


FinitelyPresentedGroup /: GroupElementFromWord[G_FinitelyPresentedGroup, w : {___Integer}] /;
	ToWord[G, w] =!= $Failed :=
		WordToExpression[G["GeneratorList"], w]


FinitelyPresentedGroup /: GroupMultiplicationTable[G_FinitelyPresentedGroup] :=
	With[{d = RegularData[G]},
		If[AssociationQ[d],
			Module[
				{t = d["Table"], n, parent = d["Parent"], edgeCol = d["EdgeCol"],
				bfsOrder = d["BFSOrder"], cols},

				n = Length[t];
				If[n > $MaxMultiplicationTableOrder,
					Message[FinitelyPresentedGroup::TooLargeOutput, n, $MaxMultiplicationTableOrder, "GroupMultiplicationTable"];
					Return[$Failed]];
				cols = ConstantArray[{}, n];
				cols[[1]] = Range[n];
				Do[
					cols[[v]] = t[[cols[[parent[[v]]]], edgeCol[[v]]]],
					{v, Rest[bfsOrder]}];
				Transpose[cols]],
			$Failed]]


FinitelyPresentedGroup /: CayleyGraph[G_FinitelyPresentedGroup] :=
	With[{d = RegularData[G]},
		If[AssociationQ[d],
			With[{t = d["Table"], n = Length[d["Table"]], ng = G["GeneratorCount"]},
				If[n > $MaxCayleyGraphOrder,
					Message[FinitelyPresentedGroup::TooLargeOutput, n, $MaxCayleyGraphOrder, "CayleyGraph"];
					$Failed,
					Graph[Range[n],
						Flatten @ Table[DirectedEdge[v, t[[v, g]]], {v, n}, {g, ng}]]]],
			$Failed]]


FinitelyPresentedGroup /: PermutationGroup[G_FinitelyPresentedGroup] :=
	Module[
		{ord = GroupOrder[G], ng = G["GeneratorCount"], rels, cands, t, pg,
		accGens, accDeg = 0, accOrd = 1, curPerms, d},

		If[IntegerQ[ord] && ord > 1,
			rels = DeleteDuplicates @ DeleteCases[NormaliseRelators[G], {}];
			cands = DeleteDuplicates @ Join[
				LargerSubgroupCandidates[rels, ng],
				List /@ SubgroupCandidates[rels, ng]];
			accGens = ConstantArray[{}, ng];
			Catch[
				Do[
					t = Quiet @ CosetTable[G, u, "MaxCosets" -> Min[ord - 1, 2000]];
					If[MatrixQ[t, IntegerQ] && 1 < Length[t] < ord,
						curPerms = Transpose[t[[All, ;; ng]]];
						pg = PermutationGroup[PermutationCycles /@ curPerms];
						If[GroupOrder[pg] === ord, Throw[pg, "FPGPerm"]];
						If[accDeg + Length[t] < ord,
							Module[{shifted = MapIndexed[Join[accGens[[First[#2]]], #1 + accDeg] &, curPerms], candPg},
								candPg = PermutationGroup[PermutationCycles /@ shifted];
								If[GroupOrder[candPg] > accOrd,
									accGens = shifted;
									accDeg += Length[t];
									accOrd = GroupOrder[candPg];
									If[accOrd === ord, Throw[candPg, "FPGPerm"]]]]]],
					{u, cands}];
				Null,
				"FPGPerm"] // If[# =!= Null, Return[#, Module]] &];

		d = RegularData[G];
		If[AssociationQ[d],
			PermutationGroup[
				PermutationCycles /@ Transpose[d["Table"][[All, ;; ng]]]],
			$Failed]]


(* ::Text:: *)
(*Extension to free groups:*)


FreeGroup /:
	(f : (GroupGenerators | GroupOrder | GroupElements | GroupElementQ |
		GroupElementPosition | GroupElementToWord | GroupElementFromWord |
		GroupMultiplicationTable | CayleyGraph | PermutationGroup))[G_FreeGroup, args___] :=
			f[FinitelyPresentedGroup[G], args]


(* ::Subsection:: *)
(*Words*)


CyclicConjugates[word_List] :=
	If[word === {}, {}, RotateLeft[word, #] & /@ Range[0, Length[word] - 1]]


NormaliseRelator[lhs_ == rhs_, map_Association] :=
	FreeReduce[Join[ParseWord[lhs, map], Reverse[-ParseWord[rhs, map]]]]
NormaliseRelator[rel_, map_Association] :=
	FreeReduce[ParseWord[rel, map]];


If[\[Not] AssociationQ @ $NormalisedRelatorsCache,
	$NormalisedRelatorsCache = <||>];
NormaliseRelators[G : _FinitelyPresentedGroup | _FreeGroup] :=
	If[KeyExistsQ[$NormalisedRelatorsCache, G],
		$NormalisedRelatorsCache[G],
		If[Length[$NormalisedRelatorsCache] > 200, $NormalisedRelatorsCache = <||>];
		With[{map = GeneratorMap[G]},
			$NormalisedRelatorsCache[G] = NormaliseRelator[#, map] & /@ G["RelatorList"]]]


$RelatorRulesCache = <||>;
ComputeRelatorRules[G : _FinitelyPresentedGroup | _FreeGroup] :=
	Module[
		{raw, pairs},

		raw = DeleteDuplicates[
			Join @@ (
				Function[r, Join[CyclicConjugates[r], CyclicConjugates[InvertWord[r]]]] /@
					DeleteCases[NormaliseRelators[G], {}])];
		pairs = Map[
			Function[r,
				With[{m = Quotient[Length[r], 2] + 1},
					Take[r, m] -> InvertWord[Drop[r, m]]]],
			raw];
		SortBy[DeleteDuplicatesBy[pairs, First], -Length[First[#]] &]]


RelatorRules[G : _FinitelyPresentedGroup | _FreeGroup] :=
	Module[
		{cached = Lookup[$RelatorRulesCache, G, None], rules},

		If[cached =!= None,
			cached,
			rules = ComputeRelatorRules[G];
			If[MatchQ[rules, {(_List -> _List) ...}],
				If[Length[$RelatorRulesCache] > 200, $RelatorRulesCache = <||>];
				$RelatorRulesCache[G] = rules];
			rules]]


ReduceByRelators[G : _FinitelyPresentedGroup | _FreeGroup, word_List] :=
	Module[
		{rules = RelatorRules[G], w = FreeReduce[word], changed = True, pos, lhs, rhs, r},

		If[rules === {}, Return[w]];
		While[changed,
			changed = False;
			For[r = 1, r <= Length[rules], r++,
				{lhs, rhs} = List @@ rules[[r]];
				If[(pos = SequencePosition[w, lhs, 1]) =!= {},
					pos = First[pos];
					w = FreeReduce[Join[Take[w, pos[[1]] - 1], rhs, Drop[w, pos[[2]]]]];
					changed = True;
					Break[]]]];
		w]


ClearAll[ElementReduce];
ElementReduce::usage =
	"ElementReduce[group, word] reduces word using the relators of group (and cached confluent shortlex Knuth-Bendix rules when available).";
FinitelyPresentedGroup::BadWord =
	"The word is not valid in the generators of the group.";


ElementReduce[G : _FinitelyPresentedGroup | _FreeGroup, x_] :=
	With[{w = ToWord[G, x]},
		If[w === $Failed,
			(Message[FinitelyPresentedGroup::BadWord]; $Failed),
			With[{kbKey = {G, $KBMaxRules, $KBMaxSteps, $KBMaxRuleLen, $KBMaxTime}},
				With[{r = If[KeyExistsQ[$KBCache, kbKey] && $KBCache[kbKey]["Confluent"],
						KBReduce[$KBCache[kbKey]["Rules"], w],
						ReduceByRelators[G, w]]},
					If[MatchQ[x, {___Integer}], r, WordToExpression[G["GeneratorList"], r]]]]]]


If[\[Not] AssociationQ @ $AbelianHNF,
	$AbelianHNF = <||>];
AbelianHNF[G : _FinitelyPresentedGroup | _FreeGroup] :=
	If[KeyExistsQ[$AbelianHNF, G],
		$AbelianHNF[G],
		Module[
			{ng = G["GeneratorCount"], rels, m, h},

			rels = DeleteCases[NormaliseRelators[G], {}];
			h = If[rels === {} || ng == 0,
				{},
				m = Table[
					Module[{row = ConstantArray[0, ng]},
						Do[If[x > 0, row[[x]]++, row[[-x]]--], {x, w}];
						row],
					{w, rels}];
				Select[Last @ HermiteDecomposition[m], AnyTrue[#, # != 0 &] &]];
			If[Length[$AbelianHNF] > 200, $AbelianHNF = <||>];
			$AbelianHNF[G] = h]]


ClearAll[AbelianTrivialQ];
AbelianTrivialQ[G : _FinitelyPresentedGroup | _FreeGroup, word_List] :=
	Module[
		{ng = G["GeneratorCount"], vec, h, piv, q},

		If[ng == 0, Return[True]];
		vec = ConstantArray[0, ng];
		Do[If[x > 0, vec[[x]]++, vec[[-x]]--], {x, word}];
		If[vec === ConstantArray[0, ng], Return[True]];
		h = AbelianHNF[G];
		If[h === {}, Return[False]];
		Do[
			piv = First @ FirstPosition[row, _?(# != 0 &)];
			If[vec[[piv]] != 0,
				If[Mod[vec[[piv]], row[[piv]]] != 0, Return[False, Module]];
				q = Quotient[vec[[piv]], row[[piv]]];
				vec -= q row],
			{row, h}];
		vec === ConstantArray[0, ng]]


(* ::Text:: *)
(*Bounded shortlex Knuth-Bendix completion. Normal forms are claimed only when completion is proved confluent:*)


$KBMaxRules = 40;
$KBMaxSteps = 200;
$KBMaxRuleLen = 14;
$KBMaxTime = 0.25;
If[\[Not] AssociationQ @ $KBCache,
	$KBCache = <||>];


ClearAll[ShortLexLessQ];
ShortLexLessQ[u_List, v_List] :=
	If[Length[u] != Length[v],
		Length[u] < Length[v],
		With[{a = 2 Abs[u] - UnitStep[u], b = 2 Abs[v] - UnitStep[v]},
			Order[a, b] === 1]]


ClearAll[KBReduce];
KBReduce[rules_List, word_List] :=
	Module[
		{w = FreeReduce[word], changed = True, pos, lhs, rhs, r},

		While[changed,
			changed = False;
			For[r = 1, r <= Length[rules], r++,
				{lhs, rhs} = List @@ rules[[r]];
				If[(pos = SequencePosition[w, lhs, 1]) =!= {},
					pos = First[pos];
					w = FreeReduce[Join[Take[w, pos[[1]] - 1], rhs, Drop[w, pos[[2]]]]];
					changed = True;
					Break[]]]];
		w]


ClearAll[KBOverlaps];
KBOverlaps[l1_List, r1_List, l2_List, r2_List] :=
	Module[
		{n1 = Length[l1], n2 = Length[l2], pairs = {}, k, pos},

		For[k = 1, k <= Min[n1, n2] - 1, k++,
			If[Take[l1, -k] === Take[l2, k],
				AppendTo[pairs, {Join[r1, Drop[l2, k]], Join[Drop[l1, -k], r2]}]]];
		If[n1 >= n2 && n2 > 0,
			Do[
				AppendTo[pairs, {r1, Join[Take[l1, pos[[1]] - 1], r2, Drop[l1, pos[[2]]]]}],
				{pos, SequencePosition[l1, l2]}]];
		pairs]


ClearAll[KBVerifyConfluent];
KBVerifyConfluent[rules_List] :=
	Module[
		{n = Length[rules], i, j, l1, r1, l2, r2, pairs, p},

		For[i = 1, i <= n, i++,
			{l1, r1} = List @@ rules[[i]];
			For[j = 1, j <= n, j++,
				{l2, r2} = List @@ rules[[j]];
				pairs = KBOverlaps[l1, r1, l2, r2];
				For[p = 1, p <= Length[pairs], p++,
					If[KBReduce[rules, pairs[[p, 1]]] =!= KBReduce[rules, pairs[[p, 2]]],
						Return[False, Module]]]]];
		True]


ClearAll[KBComplete];
KBComplete[G : _FinitelyPresentedGroup | _FreeGroup] :=
	Module[
		{ng = G["GeneratorCount"], rels, freeRules, rules = {}, sortedRules = {},
		queue = {}, steps = 0, dropped = False, pair, u, v, lhs, rhs, keep,
		confluent},

		rels = DeleteCases[NormaliseRelators[G], {}];
		freeRules = Join @@ Table[{{i, -i} -> {}, {-i, i} -> {}}, {i, ng}];
		If[rels === {},
			Return[<|"Rules" -> freeRules, "Confluent" -> True|>]];

		(* Seed queue with relators, inverses, and cyclic conjugates *)
		Do[
			AppendTo[queue, {r, {}}];
			AppendTo[queue, {InvertWord[r], {}}];
			With[{m = Quotient[Length[r], 2] + 1},
				AppendTo[queue, {Take[r, m], InvertWord[Drop[r, m]]}]],
			{r, rels}];

		TimeConstrained[
			While[queue =!= {} && steps < $KBMaxSteps && Length[rules] < $KBMaxRules,
				steps++;
				pair = First[queue];
				queue = Rest[queue];
				u = KBReduce[sortedRules, pair[[1]]];
				v = KBReduce[sortedRules, pair[[2]]];
				If[u =!= v,
					If[ShortLexLessQ[v, u], {lhs, rhs} = {u, v}, {lhs, rhs} = {v, u}];
					If[Length[lhs] > $KBMaxRuleLen,
						dropped = True,
						(* Interreduce existing rules whose LHS contains the new LHS *)
						keep = {};
						Do[
							If[SequencePosition[First[rule], lhs, 1] =!= {},
								AppendTo[queue, List @@ rule],
								AppendTo[keep, rule]],
							{rule, rules}];
						rules = Append[keep, lhs -> rhs];
						sortedRules = SortBy[rules, {-Length[First[#]] &, Identity}];
						(* Add overlaps with existing rules and free inverse rules *)
						Do[
							queue = Join[queue,
								KBOverlaps[lhs, rhs, First[rule], Last[rule]],
								KBOverlaps[First[rule], Last[rule], lhs, rhs]],
							{rule, rules}];
						Do[
							queue = Join[queue,
								KBOverlaps[lhs, rhs, First[rule], Last[rule]],
								KBOverlaps[First[rule], Last[rule], lhs, rhs]],
							{rule, freeRules}]]]],
			$KBMaxTime,
			dropped = True];

		confluent = queue === {} && \[Not] dropped && KBVerifyConfluent[Join[freeRules, sortedRules]];
		<|"Rules" -> sortedRules, "Confluent" -> confluent|>]


ClearAll[KBSystem];
KBSystem[G : _FinitelyPresentedGroup | _FreeGroup] :=
	With[{key = {G, $KBMaxRules, $KBMaxSteps, $KBMaxRuleLen, $KBMaxTime}},
		If[KeyExistsQ[$KBCache, key],
			$KBCache[key],
			If[Length[$KBCache] > 100, $KBCache = <||>];
			$KBCache[key] = KBComplete[G]]]


ClearAll[ElementEqualQ];
ElementEqualQ::usage =
	"ElementEqualQ[group, x, y] checks whether x and y are equal in group, returning True, False, or $Failed if undecided within resource limits.";


ElementEqualQ[G : _FinitelyPresentedGroup | _FreeGroup, x_, y_] :=
	With[{u = ToWord[G, x], v = ToWord[G, y]},
		If[u === $Failed || v === $Failed,
			(Message[FinitelyPresentedGroup::BadWord]; $Failed),
			If[u === v, Return[True]];
			If[KeyExistsQ[$WordProblemCache, G] && MatrixQ[$WordProblemCache[G], IntegerQ],
				Return[WordProblem[G, Join[u, InvertWord[v]]]]];
			With[{r = ReduceByRelators[G, Join[u, InvertWord[v]]]},
				Which[
					r === {}, True,
					RelatorRules[G] === {}, False,
					\[Not] AbelianTrivialQ[G, r], False,
					True,
					With[{wp = If[FreeQ[G["AbelianInvariants"], 0], WordProblem[G, r], $Failed]},
						If[BooleanQ[wp],
							wp,
							With[{kb = KBSystem[G]},
								With[{ru = KBReduce[kb["Rules"], u], rv = KBReduce[kb["Rules"], v]},
									Which[
										ru === rv, True,
										kb["Confluent"], False,
										True, $Failed]]]]]]]]]


(* ::Subsection:: *)
(*Fox derivatives*)


(* ::Text:: *)
(*The Fox derivative d/dx_j is determined by d(x_j) = 1, d(x_k) = 0 for k != j and d(uv) = d(u) + u d(v). For a freely reduced word l_1 ... l_n this gives d(w) = Sum_k prefix_{k-1} d(l_k), where d(x_j^-1) = -x_j^-1. The result is returned as a list of {coefficient, prefix word} terms, with equal prefixes merged:*)


ClearAll[FoxTerms];
FoxTerms[word_List, j_Integer] :=
	Module[
		{w = FreeReduce[word], terms},

		terms = Reap[
			Do[
				Which[
					w[[k]] == j, Sow[Take[w, k - 1] -> 1],
					w[[k]] == -j, Sow[Take[w, k] -> -1]],
				{k, Length[w]}]][[2]];
		If[terms === {},
			{},
			KeyValueMap[{#2, #1} &, DeleteCases[Merge[First[terms], Total], 0]]]]


ClearAll[FoxTermsRow];
FoxTermsRow[word_List, ng_Integer] :=
	Module[
		{w = FreeReduce[word], terms, x},

		terms = Reap[
			Do[
				x = w[[k]];
				If[x > 0,
					Sow[Take[w, k - 1] -> 1, x],
					Sow[Take[w, k] -> -1, -x]],
				{k, Length[w]}],
			Range[ng]][[2]];
		If[# === {}, {}, KeyValueMap[{#2, #1} &, DeleteCases[Merge[First[#], Total], 0]]] & /@ terms]


(* ::Text:: *)
(*Evaluation of a word in a ring: the images of the generators are multiplied with the option "Multiply" (default Times), inverted with "Invert" (default 1/#&), and "One" is the identity of the ring. For matrices use e.g. "Multiply" -> Dot, "Invert" -> Inverse, "One" -> IdentityMatrix[n]:*)


ClearAll[EvaluateWord];
EvaluateWord[word_List, images_List, mult_, inv_, one_] :=
	Fold[
		mult[#1, If[#2 > 0, images[[#2]], inv[images[[-#2]]]]] &,
		one,
		word]


ClearAll[FoxEvaluate];
FoxEvaluate[G : _FinitelyPresentedGroup | _FreeGroup, terms_List, None, _, _, _] :=
	Total[#1 WordToExpression[G["GeneratorList"], #2] & @@@ terms]
FoxEvaluate[_, terms_List, images_List, mult_, inv_, one_] :=
	If[terms === {},
		0 one,
		Total[#1 EvaluateWord[#2, images, mult, inv, one] & @@@ terms]]


ClearAll[FoxD];
FoxD::usage =
	"FoxD[group, word, g] gives the Fox derivative of word with respect to the generator g in group.
FoxD[group, word, g, images] evaluates the result by sending the generators of group to images.";
FoxD::BadGenerator =
	"`1` is not a generator of the group.";
FoxD::BadImages =
	"The images must be a list with one entry per generator.";
Options[FoxD] = {"Multiply" -> Times, "Invert" -> (1/# &), "One" -> 1};


GeneratorIndex[G : _FinitelyPresentedGroup | _FreeGroup, g_] :=
	Which[
		IntegerQ[g] && 1 <= g <= G["GeneratorCount"], g,
		True, First[FirstPosition[G["GeneratorList"], g, {$Failed}]]]


FoxD[G : _FinitelyPresentedGroup | _FreeGroup, x_, g_, images : (_List | None) : None, OptionsPattern[]] :=
	Module[
		{w = ToWord[G, x], j = GeneratorIndex[G, g]},

		Which[
			w === $Failed,
			Message[FinitelyPresentedGroup::BadWord]; $Failed,
			\[Not] IntegerQ[j],
			Message[FoxD::BadGenerator, g]; $Failed,
			images =!= None && Length[images] =!= G["GeneratorCount"],
			Message[FoxD::BadImages]; $Failed,
			True,
			FoxEvaluate[G, FoxTerms[w, j], images,
				OptionValue["Multiply"], OptionValue["Invert"], OptionValue["One"]]]]


(* ::Subsection:: *)
(*Alexander matrix*)


ClearAll[AlexanderMatrix];
AlexanderMatrix::usage =
	"AlexanderMatrix[group] gives the Alexander matrix of group.
AlexanderMatrix[group, images] sends the generators of group to images.";
AlexanderMatrix::BadImages =
	"The images must be a list with one entry per generator.";
Options[AlexanderMatrix] = {"Multiply" -> Times, "Invert" -> (1/# &), "One" -> 1};


AlexanderMatrix[G : _FinitelyPresentedGroup | _FreeGroup, images : (_List | None) : None, OptionsPattern[]] :=
	Module[
		{ng = G["GeneratorCount"], rels = NormaliseRelators[G]},

		If[images =!= None && Length[images] =!= ng,
			Message[AlexanderMatrix::BadImages];
			$Failed,
			With[{mult = OptionValue["Multiply"], inv = OptionValue["Invert"], one = OptionValue["One"]},
				Map[FoxEvaluate[G, #, images, mult, inv, one] &, FoxTermsRow[#, ng] & /@ rels, {2}]]]]


(* ::Section::Closed:: *)
(*Package Footer*)


End[];
EndPackage[];
