(* ::Package:: *)

(* ::Section:: *)
(*Package Header*)


Begin["Taggar`FinitelyPresentedGroups`Private`"];


(* ::Section:: *)
(*Definitions*)


(* ::Subsection:: *)
(*Helper functions*)


ClearAll[InvertWord];
InvertWord[word_List] :=
	Reverse[-word]


(* ::Text:: *)
(*Subgroup generators may be integer lists, FPGWord objects of the group, or words in the generators:*)


ClearAll[ParseSubgroupWord, SubgroupWords, ValidSubgroupWordQ, ValidSubgroupWordsQ, ToColumns];

ParseSubgroupWord[G_, FPGWord[G_, w_List], _Association] :=
	w
ParseSubgroupWord[_, w : {___Integer}, _Association] :=
	w
ParseSubgroupWord[_, w_, map_Association] :=
	Quiet @ Check[ParseWord[w, map], $Failed]

SubgroupWords[G_FinitelyPresentedGroup, hgens_List] :=
	Module[
		{map},

		map = AssociationThread[G["GeneratorList"], Range @ G["GeneratorCount"]];
		ParseSubgroupWord[G, #, map] & /@ hgens]

ValidSubgroupWordQ[w_, n_Integer] :=
	MatchQ[w, {___Integer}] && AllTrue[w, 0 < Abs[#] <= n &]

ValidSubgroupWordsQ[G_FinitelyPresentedGroup, hgens_List] :=
	And @@ (ValidSubgroupWordQ[#, G["GeneratorCount"]] & /@ SubgroupWords[G, hgens])

ToColumns[word_List, nc_Integer] :=
	If[# > 0, #, nc + 1 + #] & /@ word


(* ::Subsection:: *)
(*Enumeration*)


ClearAll[MakeEnumerator, CosetEnumerate];
MakeEnumerator[target_String] :=
	Compile[
		{{flat, _Integer, 1}, {starts, _Integer, 1}, {nsubs, _Integer},
		{nw, _Integer}, {nc, _Integer}, {max, _Integer}},
		Module[
			{ct, cap, ncos = 1, overflow = False, alpha = 1, k = 1, w0 = 0,
			w1 = 0, f = 0, b = 0, i = 0, j = 0, need = False, scanning = False,
			newcap = 0, pend1 = 0, pend2 = 0, havePend = False, qfirst = 0,
			qtail = 0, cur = 0, x = 0, inCoin = False, r1 = 0, r2 = 0, t = 0,
			nx = 0, mu = 0, nu = 0, d = 0, m = 0, n2 = 0},

			cap = Min[max, 1024];
			ct = ConstantArray[0, {cap, nc + 2}];
			ct[[1, nc + 1]] = 1;

			While[alpha <= ncos && ! overflow,
				If[ct[[alpha, nc + 1]] != alpha || k > nw,
					alpha++;
					k = nsubs + 1,

					w0 = starts[[k]];
					w1 = starts[[k + 1]] - 1;
					f = alpha;
					b = alpha;
					i = w0;
					j = w1;
					need = False;
					scanning = True;
					While[scanning,
						While[i <= j && ct[[f, flat[[i]]]] != 0,
							f = ct[[f, flat[[i]]]];
							i++];
						If[i > j,
							If[f != b, need = True];
							scanning = False,

							While[j >= i && ct[[b, nc + 1 - flat[[j]]]] != 0,
								b = ct[[b, nc + 1 - flat[[j]]]];
								j--];
							Which[
								j < i,
								If[f != b, need = True];
								scanning = False,
								j == i,
								ct[[f, flat[[i]]]] = b;
								ct[[b, nc + 1 - flat[[i]]]] = f;
								scanning = False,
								True,
								If[ncos >= cap,
									If[cap >= max,
										overflow = True;
										scanning = False,
										newcap = Min[2 cap, max];
										ct = Join[ct, ConstantArray[0, {newcap - cap, nc + 2}]];
										cap = newcap]];
								If[! overflow,
									ncos++;
									ct[[ncos, nc + 1]] = ncos;
									ct[[f, flat[[i]]]] = ncos;
									ct[[ncos, nc + 1 - flat[[i]]]] = f]]]];
					k++;

					If[need && ! overflow,
						pend1 = f;
						pend2 = b;
						havePend = True;
						qfirst = 0;
						qtail = 0;
						cur = 0;
						x = 1;
						inCoin = True;
						While[inCoin,
							If[havePend,
								r1 = pend1;
								While[ct[[r1, nc + 1]] != r1, r1 = ct[[r1, nc + 1]]];
								t = pend1;
								While[t != r1, nx = ct[[t, nc + 1]]; ct[[t, nc + 1]] = r1; t = nx];
								r2 = pend2;
								While[ct[[r2, nc + 1]] != r2, r2 = ct[[r2, nc + 1]]];
								t = pend2;
								While[t != r2, nx = ct[[t, nc + 1]]; ct[[t, nc + 1]] = r2; t = nx];
								If[r1 != r2,
									mu = Min[r1, r2];
									nu = Max[r1, r2];
									ct[[nu, nc + 1]] = mu;
									If[qtail == 0, qfirst = nu, ct[[qtail, nc + 2]] = nu];
									qtail = nu;
									ct[[nu, nc + 2]] = 0];
								havePend = False;
								If[cur == 0,
									If[qfirst == 0,
										inCoin = False,
										cur = qfirst;
										x = 1]],

								If[x > nc,
									cur = ct[[cur, nc + 2]];
									x = 1;
									If[cur == 0, inCoin = False],

									d = ct[[cur, x]];
									If[d != 0,
										ct[[d, nc + 1 - x]] = 0;
										mu = cur;
										While[ct[[mu, nc + 1]] != mu, mu = ct[[mu, nc + 1]]];
										t = cur;
										While[t != mu, nx = ct[[t, nc + 1]]; ct[[t, nc + 1]] = mu; t = nx];
										nu = d;
										While[ct[[nu, nc + 1]] != nu, nu = ct[[nu, nc + 1]]];
										t = d;
										While[t != nu, nx = ct[[t, nc + 1]]; ct[[t, nc + 1]] = nu; t = nx];
										m = ct[[mu, x]];
										If[m != 0,
											pend1 = nu;
											pend2 = m;
											havePend = True,
											n2 = ct[[nu, nc + 1 - x]];
											If[n2 != 0,
												pend1 = mu;
												pend2 = n2;
												havePend = True,
												ct[[mu, x]] = nu;
												ct[[nu, nc + 1 - x]] = mu]]];
									x++]]]]]];

			If[overflow, {{-1}}, ct[[;; ncos, ;; nc + 1]]]],
		CompilationTarget -> target,
		RuntimeOptions -> "Speed"]


(* ::Text:: *)
(*The compiled function is built on first use. The C target is tried first and needs a C compiler, otherwise the virtual machine target is used:*)


CosetEnumerate :=
	CosetEnumerate = Quiet @ Check[MakeEnumerator["C"], MakeEnumerator["WVM"]]


(* ::Subsection:: *)
(*Coset table*)


ClearAll[CosetTable];
CosetTable::usage =
	"CosetTable[G, subgroupGenerators] enumerates the cosets in G of the subgroup generated by subgroupGenerators using the Todd-Coxeter algorithm, and returns the coset table as a matrix.";
CosetTable::BadSubgroupGenerators =
	"The subgroup generators must be valid words in the generators of the group.";
CosetTable::Overflow =
	"More than `1` cosets were needed; the enumeration was aborted.";
Options[CosetTable] = {"MaxCosets" -> 1000000};


(* ::Text:: *)
(*Invalid forms:*)


CosetTable[G_FinitelyPresentedGroup, hgens_List, OptionsPattern[]] /;
	\[Not] ValidSubgroupWordsQ[G, hgens] :=
		(Message[CosetTable::BadSubgroupGenerators]; $Failed)


CosetTable[G_FinitelyPresentedGroup, hgens_List, OptionsPattern[]] :=
	Module[
		{ng, nc, max, subs, rels, words, res, n, live, renum, table},

		ng = G["GeneratorCount"];
		nc = 2 ng;
		max = Max[1, OptionValue["MaxCosets"]];
		subs = DeleteCases[FreeReduce /@ SubgroupWords[G, hgens], {}];
		rels = DeleteDuplicates @ DeleteCases[NormaliseRelators[G], {}];
		words = Join[
			ToColumns[#, nc] & /@ subs,
			ToColumns[#, nc] & /@ rels,
			Table[{c, nc + 1 - c}, {c, ng}]];

		res = CosetEnumerate[
			Append[Join @@ words, 1],
			1 + Prepend[Accumulate[Length /@ words], 0],
			Length[subs], Length[words], nc, max];

		If[res === {{-1}},
			Message[CosetTable::Overflow, max];
			$Failed,
			n = Length[res];
			live = Pick[Range[n], res[[All, nc + 1]] - Range[n], 0];
			renum = ConstantArray[0, n];
			renum[[live]] = Range @ Length[live];
			table = res[[live, ;; nc]];
			ArrayReshape[renum[[Flatten @ table]], Dimensions[table]]]]


(* ::Subsection:: *)
(*Word problem*)


(* ::Text:: *)
(*The coset table of the trivial subgroup is the regular action of a finite group, so a word is trivial exactly when tracing it from coset 1 returns to coset 1. The table is cached per group; failures (infinite or too large groups) are cached too, so they are not retried:*)


$WordProblemCache = <||>;
WordProblemTable[G_FinitelyPresentedGroup] :=
	If[KeyExistsQ[$WordProblemCache, G],
		$WordProblemCache[G],
		If[Length[$WordProblemCache] > 50, $WordProblemCache = <||>];
		$WordProblemCache[G] = Quiet @ CosetTable[G, {}, "MaxCosets" -> 20000]]

(* True or False if the group could be enumerated, $Failed otherwise *)
WordProblem[G_FinitelyPresentedGroup, word_List] :=
	With[{t = WordProblemTable[G]},
		If[MatrixQ[t, IntegerQ],
			Fold[t[[#1, #2]] &, 1, ToColumns[word, 2 G["GeneratorCount"]]] === 1,
			$Failed]]


(* ::Section:: *)
(*Package Footer*)


End[];
