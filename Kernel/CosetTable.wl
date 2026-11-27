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
(*Subgroup generators may be integer lists or words in the generators:*)


ClearAll[SubgroupWords, ToColumns];
SubgroupWords[G : _FinitelyPresentedGroup | _FreeGroup, hgens_List] :=
	ToWord[G, #] & /@ hgens
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
			nx = 0, mu = 0, nu = 0, d = 0, m = 0, n2 = 0,
			ndead = 0, nnew = 0, before = 0, live = False, c = 0, y = 0, v = 0, maxRel = 1},

			For[k = 1, k <= nw, k++,
				If[starts[[k + 1]] - starts[[k]] > maxRel,
					maxRel = starts[[k + 1]] - starts[[k]]]];
			k = 1;
			cap = Min[max, 1024];
			ct = ConstantArray[0, {cap, nc + 2}];
			ct[[1, nc + 1]] = 1;

			While[alpha <= ncos && ! overflow,

				(* lazy compaction: grow below max, compact only under pressure at max capacity *)
				If[cap >= max && 16 ndead >= ncos && ndead > 0 &&
					ncos >= cap - Max[Quotient[cap, 8], maxRel],
					live = ct[[alpha, nc + 1]] == alpha;
					nnew = 0;
					before = 0;
					(* column nc+2 is free outside coincidence processing, it holds the new numbers *)
					For[c = 1, c <= ncos, c++,
						If[ct[[c, nc + 1]] == c,
							nnew++;
							ct[[c, nc + 2]] = nnew;
							If[c < alpha, before++]]];
					For[c = 1, c <= ncos, c++,
						If[ct[[c, nc + 1]] == c,
							m = ct[[c, nc + 2]];
							For[y = 1, y <= nc, y++,
								v = ct[[c, y]];
								ct[[m, y]] = If[v == 0, 0, ct[[v, nc + 2]]]];
							ct[[m, nc + 1]] = m]];
					For[c = nnew + 1, c <= ncos, c++,
						For[y = 1, y <= nc + 2, y++,
							ct[[c, y]] = 0]];
					ncos = nnew;
					ndead = 0;
					alpha = before + 1;
					If[! live, k = nsubs + 1]];

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
									ndead++;
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

			If[overflow,
				{{-1}},
				If[ndead > 0,
					nnew = 0;
					For[c = 1, c <= ncos, c++,
						If[ct[[c, nc + 1]] == c,
							nnew++;
							ct[[c, nc + 2]] = nnew]];
					For[c = 1, c <= ncos, c++,
						If[ct[[c, nc + 1]] == c,
							m = ct[[c, nc + 2]];
							For[y = 1, y <= nc, y++,
								v = ct[[c, y]];
								ct[[m, y]] = If[v == 0, 0, ct[[v, nc + 2]]]];
							ct[[m, nc + 1]] = m]];
					ncos = nnew];
				ct[[;; ncos, ;; nc]]]],
		CompilationTarget -> target,
		RuntimeOptions -> "Speed"]


(* ::Text:: *)
(*The compiled function is built on first use. The C target is tried first and needs a C compiler, otherwise the virtual machine target is used:*)


CosetEnumerate :=
	CosetEnumerate = Quiet @ Check[MakeEnumerator["C"], MakeEnumerator["WVM"]]


(* ::Text:: *)
(*Felsch strategy with cyclic-conjugate occurrence index and deduction stack:*)


ClearAll[BuildFelschData, MakeFelschEnumerator, CosetEnumerateFelsch];
BuildFelschData[subs_List, rels_List, nc_Integer] :=
	Module[
		{subCols, relCols, rots = {}, rotSet = <||>, byCol, rFlat, rStarts, occList, occStarts, id},

		subCols = ToColumns[#, nc] & /@ subs;
		relCols = ToColumns[#, nc] & /@ rels;
		byCol = ConstantArray[{}, nc];
		Do[
			Module[{inv = Reverse[nc + 1 - r], len = Length[r]},
				Do[
					With[{rot = RotateLeft[r, p - 1]},
						If[\[Not] KeyExistsQ[rotSet, rot],
							AppendTo[rots, rot];
							id = Length[rots];
							rotSet[rot] = id;
							AppendTo[byCol[[rot[[1]]]], id]]];
					With[{rot = RotateLeft[inv, p - 1]},
						If[\[Not] KeyExistsQ[rotSet, rot],
							AppendTo[rots, rot];
							id = Length[rots];
							rotSet[rot] = id;
							AppendTo[byCol[[rot[[1]]]], id]]],
					{p, len}]],
			{r, relCols}];
		rFlat = Append[Join @@ Join[subCols, rots], 1];
		rStarts = 1 + Prepend[Accumulate[Length /@ Join[subCols, rots]], 0];
		occList = Append[Flatten[byCol] + Length[subCols], 1];
		occStarts = 1 + Prepend[Accumulate[Length /@ byCol], 0];
		{rFlat, rStarts, Length[subCols], occList, occStarts}]


MakeFelschEnumerator[target_String] :=
	Compile[
		{{flat, _Integer, 1}, {starts, _Integer, 1}, {nsubs, _Integer},
		{occList, _Integer, 1}, {occStarts, _Integer, 1}, {nc, _Integer}, {max, _Integer}},
		Module[
			{ct, cap, ncos = 1, overflow = False,
			dedC, dedX, dedTop = 0, dedCap = 4096,
			alpha = 1, col = 1, k = 1,
			w0 = 0, w1 = 0, f = 0, b = 0, i = 0, j = 0, need = False,
			pend1 = 0, pend2 = 0, havePend = False, qfirst = 0, qtail = 0, cur = 0,
			x = 0, inCoin = False, r1 = 0, r2 = 0, t = 0, nx = 0, mu = 0, nu = 0,
			d = 0, m = 0, n2 = 0, ndead = 0, nnew = 0, before = 0, c = 0, y = 0, v = 0,
			newcap = 0, oi = 0, o0 = 0, o1 = 0, rot = 0, dc = 0, dx = 0},

			cap = Min[max, 1024];
			ct = ConstantArray[0, {cap, nc + 2}];
			ct[[1, nc + 1]] = 1;
			dedC = ConstantArray[0, dedCap];
			dedX = ConstantArray[0, dedCap];

			For[k = 1, k <= nsubs && ! overflow, k++,
				w0 = starts[[k]]; w1 = starts[[k + 1]] - 1;
				f = 1; b = 1; i = w0; j = w1;
				c = 1;
				While[c == 1,
					While[i <= j && ct[[f, flat[[i]]]] != 0, f = ct[[f, flat[[i]]]]; i++];
					If[i > j,
						If[f != b, need = True]; c = 0,
						While[j >= i && ct[[b, nc + 1 - flat[[j]]]] != 0, b = ct[[b, nc + 1 - flat[[j]]]]; j--];
						Which[
							j < i, If[f != b, need = True]; c = 0,
							j == i,
							ct[[f, flat[[i]]]] = b; ct[[b, nc + 1 - flat[[i]]]] = f;
							If[dedTop + 2 > dedCap,
								dedC = Join[dedC, ConstantArray[0, dedCap]];
								dedX = Join[dedX, ConstantArray[0, dedCap]];
								dedCap = 2 dedCap];
							dedTop++; dedC[[dedTop]] = f; dedX[[dedTop]] = flat[[i]];
							dedTop++; dedC[[dedTop]] = b; dedX[[dedTop]] = nc + 1 - flat[[i]];
							c = 0,
							True,
							If[ncos >= cap,
								If[cap >= max, overflow = True; c = 0,
									newcap = Min[2 cap, max];
									ct = Join[ct, ConstantArray[0, {newcap - cap, nc + 2}]];
									cap = newcap]];
							If[! overflow,
								ncos++;
								ct[[ncos, nc + 1]] = ncos;
								ct[[f, flat[[i]]]] = ncos;
								ct[[ncos, nc + 1 - flat[[i]]]] = f;
								If[dedTop + 2 > dedCap,
									dedC = Join[dedC, ConstantArray[0, dedCap]];
									dedX = Join[dedX, ConstantArray[0, dedCap]];
									dedCap = 2 dedCap];
								dedTop++; dedC[[dedTop]] = f; dedX[[dedTop]] = flat[[i]];
								dedTop++; dedC[[dedTop]] = ncos; dedX[[dedTop]] = nc + 1 - flat[[i]]]]]]
				];
				If[need && ! overflow,
					need = False;
					pend1 = f; pend2 = b; havePend = True;
					qfirst = 0; qtail = 0; cur = 0; x = 1; inCoin = True;
					While[inCoin,
						If[havePend,
							r1 = pend1; While[ct[[r1, nc + 1]] != r1, r1 = ct[[r1, nc + 1]]];
							t = pend1; While[t != r1, nx = ct[[t, nc + 1]]; ct[[t, nc + 1]] = r1; t = nx];
							r2 = pend2; While[ct[[r2, nc + 1]] != r2, r2 = ct[[r2, nc + 1]]];
							t = pend2; While[t != r2, nx = ct[[t, nc + 1]]; ct[[t, nc + 1]] = r2; t = nx];
							If[r1 != r2,
								mu = Min[r1, r2]; nu = Max[r1, r2];
								ct[[nu, nc + 1]] = mu; ndead++;
								If[qtail == 0, qfirst = nu, ct[[qtail, nc + 2]] = nu];
								qtail = nu; ct[[nu, nc + 2]] = 0];
							havePend = False;
							If[cur == 0, If[qfirst == 0, inCoin = False, cur = qfirst; x = 1]],
							If[x > nc,
								cur = ct[[cur, nc + 2]]; x = 1;
								If[cur == 0, inCoin = False],
								d = ct[[cur, x]];
								If[d != 0,
									ct[[d, nc + 1 - x]] = 0;
									mu = cur; While[ct[[mu, nc + 1]] != mu, mu = ct[[mu, nc + 1]]];
									t = cur; While[t != mu, nx = ct[[t, nc + 1]]; ct[[t, nc + 1]] = mu; t = nx];
									nu = d; While[ct[[nu, nc + 1]] != nu, nu = ct[[nu, nc + 1]]];
									t = d; While[t != nu, nx = ct[[t, nc + 1]]; ct[[t, nc + 1]] = nu; t = nx];
									m = ct[[mu, x]];
									If[m != 0,
										pend1 = nu; pend2 = m; havePend = True,
										n2 = ct[[nu, nc + 1 - x]];
										If[n2 != 0,
											pend1 = mu; pend2 = n2; havePend = True,
											ct[[mu, x]] = nu; ct[[nu, nc + 1 - x]] = mu;
											If[dedTop + 2 > dedCap,
												dedC = Join[dedC, ConstantArray[0, dedCap]];
												dedX = Join[dedX, ConstantArray[0, dedCap]];
												dedCap = 2 dedCap];
											dedTop++; dedC[[dedTop]] = mu; dedX[[dedTop]] = x;
											dedTop++; dedC[[dedTop]] = nu; dedX[[dedTop]] = nc + 1 - x]]];
								x++]]]];

			c = 1;
			While[c == 1 && ! overflow,
				While[dedTop > 0 && ! overflow,
					dc = dedC[[dedTop]]; dx = dedX[[dedTop]]; dedTop--;
					While[ct[[dc, nc + 1]] != dc, dc = ct[[dc, nc + 1]]];
					If[ct[[dc, dx]] != 0,
						o0 = occStarts[[dx]]; o1 = occStarts[[dx + 1]] - 1;
						For[oi = o0, oi <= o1 && ct[[dc, dx]] != 0, oi++,
							rot = occList[[oi]];
							w0 = starts[[rot]]; w1 = starts[[rot + 1]] - 1;
							f = dc; b = dc; i = w0; j = w1;
							While[i <= j && ct[[f, flat[[i]]]] != 0, f = ct[[f, flat[[i]]]]; i++];
							If[i > j,
								If[f != b, need = True],
								While[j >= i && ct[[b, nc + 1 - flat[[j]]]] != 0, b = ct[[b, nc + 1 - flat[[j]]]]; j--];
								Which[
									j < i, If[f != b, need = True],
									j == i,
									ct[[f, flat[[i]]]] = b; ct[[b, nc + 1 - flat[[i]]]] = f;
									If[dedTop + 2 > dedCap,
										dedC = Join[dedC, ConstantArray[0, dedCap]];
										dedX = Join[dedX, ConstantArray[0, dedCap]];
										dedCap = 2 dedCap];
									dedTop++; dedC[[dedTop]] = f; dedX[[dedTop]] = flat[[i]];
									dedTop++; dedC[[dedTop]] = b; dedX[[dedTop]] = nc + 1 - flat[[i]],
									True, Null]];
							If[need,
								need = False;
								pend1 = f; pend2 = b; havePend = True;
								qfirst = 0; qtail = 0; cur = 0; x = 1; inCoin = True;
								While[inCoin,
									If[havePend,
										r1 = pend1; While[ct[[r1, nc + 1]] != r1, r1 = ct[[r1, nc + 1]]];
										t = pend1; While[t != r1, nx = ct[[t, nc + 1]]; ct[[t, nc + 1]] = r1; t = nx];
										r2 = pend2; While[ct[[r2, nc + 1]] != r2, r2 = ct[[r2, nc + 1]]];
										t = pend2; While[t != r2, nx = ct[[t, nc + 1]]; ct[[t, nc + 1]] = r2; t = nx];
										If[r1 != r2,
											mu = Min[r1, r2]; nu = Max[r1, r2];
											ct[[nu, nc + 1]] = mu; ndead++;
											If[qtail == 0, qfirst = nu, ct[[qtail, nc + 2]] = nu];
											qtail = nu; ct[[nu, nc + 2]] = 0];
										havePend = False;
										If[cur == 0, If[qfirst == 0, inCoin = False, cur = qfirst; x = 1]],
										If[x > nc,
											cur = ct[[cur, nc + 2]]; x = 1;
											If[cur == 0, inCoin = False],
											d = ct[[cur, x]];
											If[d != 0,
												ct[[d, nc + 1 - x]] = 0;
												mu = cur; While[ct[[mu, nc + 1]] != mu, mu = ct[[mu, nc + 1]]];
												t = cur; While[t != mu, nx = ct[[t, nc + 1]]; ct[[t, nc + 1]] = mu; t = nx];
												nu = d; While[ct[[nu, nc + 1]] != nu, nu = ct[[nu, nc + 1]]];
												t = d; While[t != nu, nx = ct[[t, nc + 1]]; ct[[t, nc + 1]] = nu; t = nx];
												m = ct[[mu, x]];
												If[m != 0,
													pend1 = nu; pend2 = m; havePend = True,
													n2 = ct[[nu, nc + 1 - x]];
													If[n2 != 0,
														pend1 = mu; pend2 = n2; havePend = True,
														ct[[mu, x]] = nu; ct[[nu, nc + 1 - x]] = mu;
														If[dedTop + 2 > dedCap,
															dedC = Join[dedC, ConstantArray[0, dedCap]];
															dedX = Join[dedX, ConstantArray[0, dedCap]];
															dedCap = 2 dedCap];
														dedTop++; dedC[[dedTop]] = mu; dedX[[dedTop]] = x;
														dedTop++; dedC[[dedTop]] = nu; dedX[[dedTop]] = nc + 1 - x]]];
											x++]]];
								While[ct[[dc, nc + 1]] != dc, dc = ct[[dc, nc + 1]]]]]]];

				While[alpha <= ncos && (ct[[alpha, nc + 1]] != alpha || ct[[alpha, col]] != 0),
					col++; If[col > nc, col = 1; alpha++]];
				If[alpha > ncos,
					c = 0,
					If[ncos >= cap && (4 ndead >= ncos || (cap >= max && 16 ndead >= ncos && ndead > 0)),
						nnew = 0; before = 0;
						For[y = 1, y <= ncos, y++,
							If[ct[[y, nc + 1]] == y, nnew++; ct[[y, nc + 2]] = nnew; If[y < alpha, before++]]];
						For[y = 1, y <= ncos, y++,
							If[ct[[y, nc + 1]] == y,
								m = ct[[y, nc + 2]];
								For[x = 1, x <= nc, x++,
									v = ct[[y, x]]; ct[[m, x]] = If[v == 0, 0, ct[[v, nc + 2]]]];
								ct[[m, nc + 1]] = m]];
						For[y = nnew + 1, y <= ncos, y++,
							For[x = 1, x <= nc + 2, x++, ct[[y, x]] = 0]];
						ncos = nnew; ndead = 0; alpha = before + 1; col = 1,
						If[ncos >= cap,
							If[cap >= max, overflow = True,
								newcap = Min[2 cap, max];
								ct = Join[ct, ConstantArray[0, {newcap - cap, nc + 2}]];
								cap = newcap]];
						If[! overflow,
							ncos++; ct[[ncos, nc + 1]] = ncos;
							ct[[alpha, col]] = ncos; ct[[ncos, nc + 1 - col]] = alpha;
							If[dedTop + 2 > dedCap,
								dedC = Join[dedC, ConstantArray[0, dedCap]];
								dedX = Join[dedX, ConstantArray[0, dedCap]];
								dedCap = 2 dedCap];
							dedTop++; dedC[[dedTop]] = alpha; dedX[[dedTop]] = col;
							dedTop++; dedC[[dedTop]] = ncos; dedX[[dedTop]] = nc + 1 - col]]]];

			If[overflow,
				{{-1}},
				If[ndead > 0,
					nnew = 0;
					For[y = 1, y <= ncos, y++, If[ct[[y, nc + 1]] == y, nnew++; ct[[y, nc + 2]] = nnew]];
					For[y = 1, y <= ncos, y++,
						If[ct[[y, nc + 1]] == y,
							m = ct[[y, nc + 2]];
							For[x = 1, x <= nc, x++, v = ct[[y, x]]; ct[[m, x]] = If[v == 0, 0, ct[[v, nc + 2]]]];
							ct[[m, nc + 1]] = m]];
					ncos = nnew];
				ct[[;; ncos, ;; nc]]]],
		CompilationTarget -> target,
		RuntimeOptions -> "Speed"]


CosetEnumerateFelsch :=
	CosetEnumerateFelsch = Quiet @ Check[MakeFelschEnumerator["C"], MakeFelschEnumerator["WVM"]]


(* ::Subsection:: *)
(*Coset table*)


ClearAll[CosetTable];
CosetTable::usage =
	"CosetTable[group, generators] enumerates the cosets in group of the subgroup generated by generators (option \"MaxCosets\" -> 1000000).";
CosetTable::BadSubgroupGenerators =
	"The subgroup generators must be valid words in the generators of the group.";
CosetTable::Overflow =
	"More than `1` cosets were needed; the enumeration was aborted.";
CosetTable::BadMethod =
	"Method `1` should be \"HLT\", \"Felsch\", or Automatic.";
Options[CosetTable] = {"MaxCosets" -> 1000000, Method -> "HLT"};


(* ::Text:: *)
(*Invalid forms:*)


CosetTable[G : _FinitelyPresentedGroup | _FreeGroup, hgens_List, OptionsPattern[]] /;
	MemberQ[SubgroupWords[G, hgens], $Failed] :=
		(Message[CosetTable::BadSubgroupGenerators]; $Failed)


CosetTable[G : _FinitelyPresentedGroup | _FreeGroup, hgens_List, OptionsPattern[]] :=
	Module[
		{ng, nc, max, method, subs, rels, words, d, res},

		ng = G["GeneratorCount"];
		nc = 2 ng;
		max = Max[1, OptionValue["MaxCosets"]];
		method = OptionValue[Method];
		subs = DeleteCases[FreeReduce /@ SubgroupWords[G, hgens], {}];
		rels = DeleteDuplicates @ DeleteCases[NormaliseRelators[G], {}];

		res = Which[
			method === "HLT" || method === Automatic,
			words = Join[
				ToColumns[#, nc] & /@ subs,
				ToColumns[#, nc] & /@ rels,
				Table[{c, nc + 1 - c}, {c, ng}]];
			CosetEnumerate[
				Append[Join @@ words, 1],
				1 + Prepend[Accumulate[Length /@ words], 0],
				Length[subs], Length[words], nc, max],
			method === "Felsch",
			d = BuildFelschData[subs, rels, nc];
			CosetEnumerateFelsch[d[[1]], d[[2]], d[[3]], d[[4]], d[[5]], nc, max],
			True,
			Message[CosetTable::BadMethod, method];
			Return[$Failed]];

		If[res === {{-1}},
			Message[CosetTable::Overflow, max];
			$Failed,
			res]]


(* ::Subsection:: *)
(*Order through a cyclic subgroup*)


(* ::Text:: *)
(*If H = <u> has finite index n, then |G| = n |H|. The Reidemeister-Schreier presentation of H can be read off the completed coset table: its generators are the edges outside a spanning tree, and its relators are the relators of G traced from every coset. Since H is cyclic, it is equal to its abelianisation, so |H| is determined by this sparse integer relation matrix. No presentation of H has to be written down:*)


ClearAll[SchreierTree];
SchreierTree[t_List, ng_Integer] :=
	Module[
		{n = Length[t], nc = 2 ng, tree, seen, queue, head = 1, tail = 1, c, d},

		(* tree[[(c-1) ng + g]] is True if the edge c -> c.g is in the tree *)
		tree = ConstantArray[False, n ng];
		seen = ConstantArray[False, n];
		queue = ConstantArray[1, n];
		seen[[1]] = True;
		While[head <= tail,
			c = queue[[head++]];
			Do[
				d = t[[c, col]];
				If[\[Not] seen[[d]],
					seen[[d]] = True;
					queue[[++tail]] = d;
					If[col <= ng,
						tree[[(c - 1) ng + col]] = True,
						tree[[(d - 1) ng + nc + 1 - col]] = True]],
				{col, nc}]];
		tree]


ClearAll[SchreierRow];
SchreierRow[t_, tree_, ng_Integer, start_Integer, word_List] :=
	Module[
		{c = start, d, e, row = <||>},

		Do[
			If[x > 0,
				e = (c - 1) ng + x;
				c = t[[c, x]];
				If[\[Not] tree[[e]], row[e] = Lookup[row, e, 0] + 1],

				d = t[[c, 2 ng + 1 + x]];
				e = (d - 1) ng - x;
				c = d;
				If[\[Not] tree[[e]], row[e] = Lookup[row, e, 0] - 1]],
			{x, word}];
		DeleteCases[row, 0]]


(* ::Text:: *)
(*Order of the abelian group with ncols generators and the given sparse relations. Rows with a unit entry are used to eliminate a generator, which keeps all arithmetic in the integers. Only the small remainder goes to the dense normal form routines:*)


ClearAll[AbelianOrder];
AbelianOrder[relations_List, ncols_Integer] :=
	Module[
		{list, rows, colRows = <||>, changed = True, pivots = 0, row, new, units, p, factor, cols, left, m, diag},

		list = DeleteDuplicates @ DeleteCases[relations, <||>];
		rows = AssociationThread[Range @ Length @ list, list];
		Do[
			Do[
				If[\[Not] KeyExistsQ[colRows, col], colRows[col] = <||>];
				colRows[col, id] = True,
				{col, Keys @ rows[id]}],
			{id, Keys @ rows}];

		While[changed,
			changed = False;
			Do[
				If[KeyExistsQ[rows, id],
					row = rows[id];
					units = Keys @ Select[row, Abs[#] == 1 &];
					If[units =!= {},
						p = First @ MinimalBy[units, Length[colRows[#]] &];
						Do[
							If[other =!= id,
								factor = rows[other][p] row[p];
								new = DeleteCases[Merge[{rows[other], (-factor) # & /@ row}, Total], 0];
								Do[colRows[col] = KeyDrop[colRows[col], other], {col, Keys @ rows[other]}];
								Do[colRows[col, other] = True, {col, Keys @ new}];
								If[new === <||>,
									KeyDropFrom[rows, other],
									rows[other] = new]],
							{other, Keys @ colRows[p]}];
						Do[colRows[col] = KeyDrop[colRows[col], id], {col, Keys @ row}];
						KeyDropFrom[rows, id];
						pivots++;
						changed = True]],
				{id, SortBy[Keys @ rows, Length[rows[#]] &]}]];

		left = ncols - pivots;
		cols = Union @@ Prepend[Keys /@ Values[rows], {}];
		Which[
			left == 0, 1,
			Length[cols] < left, Infinity,
			True,
			m = Table[Lookup[r, col, 0], {r, Values[rows]}, {col, cols}];
			m = Select[Last @ HermiteDecomposition[m], AnyTrue[#, # != 0 &] &];
			If[Length[m] < left,
				Infinity,
				diag = Diagonal @ SmithDecomposition[m][[2]];
				Abs[Times @@ diag]]]]


ClearAll[CyclicSubgroupOrder];
CyclicSubgroupOrder[t_List, rels_List, ng_Integer] :=
	Module[
		{n = Length[t], tree = SchreierTree[t, ng], rows},

		rows = Flatten @ Table[SchreierRow[t, tree, ng, c, r], {c, n}, {r, rels}];
		AbelianOrder[rows, n ng - (n - 1)]]


(* ::Text:: *)
(*Likely good subgroups come from relators which are proper powers u^m: u has order dividing m, and a larger order gives a smaller coset table. Generators are the fallback:*)


ClearAll[PowerRoot];
PowerRoot[word_List] :=
	Module[
		{n = Length[word], p},

		p = SelectFirst[Divisors[n], RotateLeft[word, #] === word &];
		{Take[word, p], n / p}]


ClearAll[SubgroupCandidates];
SubgroupCandidates[rels_List, ng_Integer] :=
	Module[
		{powers},

		powers = Select[PowerRoot @* CyclicReduce /@ DeleteCases[CyclicReduce /@ rels, {}], Last[#] > 1 &];
		powers = SortBy[powers, {-Last[#] &, Length @ First[#] &}];
		DeleteDuplicates @ Join[
			Take[DeleteDuplicates @ Join[First /@ powers, List /@ Range[ng]], UpTo[$SubgroupTries]],
			(* the product of two generators: in the infinite dihedral group only this has finite index *)
			If[ng >= 2, {{1, 2}}, {}]]]


$SubgroupTries = 3;
$OrderCosetLimits = {10^4, 10^5, 10^6};


(* ::Text:: *)
(*All candidates are tried with a small budget before any of them gets a larger one:*)


ClearAll[SchreierWord];
SchreierWord[t_, tree_, edgeMap_, ng_Integer, start_Integer, word_List] :=
	Module[
		{c = start, d, e, out = {}},

		Do[
			If[x > 0,
				e = (c - 1) ng + x;
				c = t[[c, x]];
				If[\[Not] tree[[e]], AppendTo[out, edgeMap[[e]]]],

				d = t[[c, 2 ng + 1 + x]];
				e = (d - 1) ng - x;
				c = d;
				If[\[Not] tree[[e]], AppendTo[out, -edgeMap[[e]]]]],
			{x, word}];
		out]


ClearAll[ReidemeisterSchreier];
ReidemeisterSchreier[t_List, rels_List, ng_Integer] :=
	Module[
		{n = Length[t], tree, edgeMap, m = 0, rsRels, gens, sim},

		tree = SchreierTree[t, ng];
		edgeMap = ConstantArray[0, n ng];
		Do[
			If[\[Not] tree[[e]], edgeMap[[e]] = ++m],
			{e, n ng}];
		rsRels = Flatten[
			Table[SchreierWord[t, tree, edgeMap, ng, c, r], {c, n}, {r, rels}],
			1];
		gens = Range[m];
		sim = TietzeEliminateAll[{gens, TietzeNormalise[rsRels]}];
		{Length @ sim[[1]], sim[[2]]}]


ClearAll[LargerSubgroupCandidates];
LargerSubgroupCandidates[rels_List, ng_Integer] :=
	Module[
		{allButOne, pairs, singles, powers},

		allButOne = If[ng >= 2, Table[Delete[List /@ Range[ng], i], {i, Min[ng, 6]}], {}];
		pairs = If[ng >= 3,
			Take[Flatten[Table[{{i}, {j}}, {i, Min[ng, 4]}, {j, i + 1, Min[ng, 4]}], 1], UpTo[6]],
			{}];
		powers = Select[PowerRoot @* CyclicReduce /@ DeleteCases[CyclicReduce /@ rels, {}], Last[#] > 1 &];
		powers = SortBy[powers, {-Last[#] &, Length @ First[#] &}];
		singles = List /@ Take[DeleteDuplicates @ Join[First /@ powers, List /@ Range[Min[ng, 4]]], UpTo[4]];
		Take[DeleteDuplicates @ Join[allButOne, pairs, singles], UpTo[12]]]


$MaxOrderDepth = 8;
$MaxRSIndex = 120;
$SubgroupCosetLimits = {100, 1000};
$OrderTimeLimit = 30;


ClearAll[CosetIndex];
CosetIndex[G : _FinitelyPresentedGroup | _FreeGroup, maxCosets_Integer] :=
	Module[
		{ng, nc, max, rels, words, res, n},

		ng = G["GeneratorCount"];
		nc = 2 ng;
		max = Max[1, maxCosets];
		rels = DeleteDuplicates @ DeleteCases[NormaliseRelators[G], {}];
		words = Join[
			ToColumns[#, nc] & /@ rels,
			Table[{c, nc + 1 - c}, {c, ng}]];
		res = CosetEnumerate[
			Append[Join @@ words, 1],
			1 + Prepend[Accumulate[Length /@ words], 0],
			0, Length[words], nc, max];
		If[res === {{-1}},
			$Failed,
			Length[res]]]


ClearAll[EnumerateOrderWords];
EnumerateOrderWords[ng_Integer, rels_List, depth_Integer : 0, deadline_ : Infinity] :=
	Module[
		{G, t, idx, cands, rs, subOrd, cycCands},

		If[ng == 0, Return[1]];
		If[rels === {}, Return[Infinity]];
		If[AbsoluteTime[] > deadline, Return[$Failed]];
		G = FinitelyPresentedGroup[Symbol["$rs" <> ToString[#]] & /@ Range[ng], rels];
		If[\[Not] FreeQ[G["AbelianInvariants"], 0], Return[Infinity]];

		(* Fast path for small/medium groups at top level *)
		idx = CosetIndex[G, If[depth == 0, 65536, 1500]];
		If[IntegerQ[idx], Return[idx]];

		(* Recursive Reidemeister-Schreier on small-index subgroups *)
		If[depth < $MaxOrderDepth && AbsoluteTime[] < deadline,
			cands = LargerSubgroupCandidates[rels, ng];
			Catch[
				Do[
					If[AbsoluteTime[] > deadline, Throw[Null, "FPGOrder"]];
					t = Quiet @ CosetTable[G, u, "MaxCosets" -> limit];
					If[MatrixQ[t, IntegerQ] && 1 < Length[t] <= $MaxRSIndex,
						rs = ReidemeisterSchreier[t, rels, ng];
						subOrd = EnumerateOrderWords[rs[[1]], rs[[2]], depth + 1, deadline];
						If[IntegerQ[subOrd] || subOrd === Infinity,
							Throw[Length[t] * subOrd, "FPGOrder"]]],
					{limit, $SubgroupCosetLimits}, {u, cands}];
				Null,
				"FPGOrder"] // If[# =!= Null, Return[#]] &];

		(* Medium direct enumeration before cyclic fallback (at top level) *)
		If[depth == 0 && AbsoluteTime[] < deadline,
			t = Quiet @ CosetTable[G, {}, "MaxCosets" -> 15000];
			If[MatrixQ[t, IntegerQ], Return[Length[t]]]];

		(* Cyclic subgroup fallback *)
		cycCands = SubgroupCandidates[rels, ng];
		Catch[
			Do[
				If[AbsoluteTime[] > deadline, Throw[$Failed, "FPGOrder"]];
				t = Quiet @ CosetTable[G, {u}, "MaxCosets" -> limit];
				If[MatrixQ[t, IntegerQ],
					Throw[Length[t] CyclicSubgroupOrder[t, rels, ng], "FPGOrder"]],
				{limit, $OrderCosetLimits}, {u, cycCands}];
			If[depth == 0, Message[CosetTable::Overflow, Last[$OrderCosetLimits]]];
			$Failed,
			"FPGOrder"]]


ClearAll[EnumerateOrder];
EnumerateOrder[G_FinitelyPresentedGroup] :=
	EnumerateOrderWords[
		G["GeneratorCount"],
		DeleteDuplicates @ DeleteCases[NormaliseRelators[G], {}],
		0,
		AbsoluteTime[] + $OrderTimeLimit]


(* ::Subsection:: *)
(*Word problem*)


(* ::Text:: *)
(*The coset table of the trivial subgroup is the regular action of a finite group, so a word is trivial exactly when tracing it from coset 1 returns to coset 1. The table is cached per group; failures (infinite or too large groups) are cached too, so they are not retried:*)


If[\[Not] AssociationQ @ $WordProblemCache,
	$WordProblemCache = <||>];
WordProblemTable[G : _FinitelyPresentedGroup | _FreeGroup] :=
	If[KeyExistsQ[$WordProblemCache, G],
		$WordProblemCache[G],
		If[Length[$WordProblemCache] > 50, $WordProblemCache = <||>];
		$WordProblemCache[G] = Quiet @ CosetTable[G, {}, "MaxCosets" -> 20000]]

(* True or False if the group could be enumerated, $Failed otherwise *)
WordProblem[G : _FinitelyPresentedGroup | _FreeGroup, word_List] :=
	With[{t = WordProblemTable[G]},
		If[MatrixQ[t, IntegerQ],
			Fold[t[[#1, #2]] &, 1, ToColumns[word, 2 G["GeneratorCount"]]] === 1,
			$Failed]]


(* ::Subsection:: *)
(*Regular enumeration*)


$RegularCosetLimit = 100000;
If[\[Not] AssociationQ @ $RegularCache,
	$RegularCache = <||>];


ElementPosition[t_, nc_Integer, w_List] :=
	Fold[t[[#1, #2]] &, 1, ToColumns[w, nc]]


RegularData[G : _FinitelyPresentedGroup | _FreeGroup] :=
	Module[
		{ng, nc, t, n, parent, edgeGen, edgeCol, bfsOrder, head = 1, tail = 1, c, next, key = {G, $RegularCosetLimit}},

		If[\[Not] KeyExistsQ[$RegularCache, key],
			If[Length[$RegularCache] > 50, $RegularCache = <||>];
			ng = G["GeneratorCount"];
			nc = 2 ng;
			t = Quiet @ CosetTable[G, {}, "MaxCosets" -> $RegularCosetLimit];
			$RegularCache[key] =
				If[\[Not] MatrixQ[t, IntegerQ],
					$Failed,
					n = Length[t];
					parent = ConstantArray[0, n];
					edgeGen = ConstantArray[0, n];
					edgeCol = ConstantArray[0, n];
					bfsOrder = ConstantArray[0, n];
					parent[[1]] = -1;
					bfsOrder[[1]] = 1;
					While[head <= tail,
						c = bfsOrder[[head++]];
						Do[
							next = t[[c, col]];
							If[parent[[next]] == 0,
								parent[[next]] = c;
								edgeCol[[next]] = col;
								edgeGen[[next]] = If[col <= ng, col, col - nc - 1];
								bfsOrder[[++tail]] = next],
							{col, nc}]];
					<|"Table" -> t, "Parent" -> parent, "EdgeGen" -> edgeGen,
					"EdgeCol" -> edgeCol, "BFSOrder" -> bfsOrder|>]];

		If[$RegularCache[key] === $Failed,
			Message[FinitelyPresentedGroup::NotEnumerable, $RegularCosetLimit]];
		$RegularCache[key]]


ClearAll[RegularWords];
RegularWords[d_Association] :=
	Module[
		{n = Length[d["Table"]], parent = d["Parent"], edgeGen = d["EdgeGen"],
		bfsOrder = d["BFSOrder"], words},

		words = ConstantArray[{}, n];
		Do[
			words[[v]] = Append[words[[parent[[v]]]], edgeGen[[v]]],
			{v, Rest[bfsOrder]}];
		words]


(* ::Section:: *)
(*Package Footer*)


End[];
