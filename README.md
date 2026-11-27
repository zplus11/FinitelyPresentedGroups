# Finitely Presented Groups

FinitelyPresentedGroups is a Wolfram language paclet (package) for working with finitely presented groups: defining a group by generators and relators, manipulating group words, and enumerating cosets of subgroups using the Todd-Coxeter algorithm.

On Wolfram Paclet Repository: https://resources.wolframcloud.com/PacletRepository/resources/Taggar/FinitelyPresentedGroups/

## Installation

Run in any mathematica notebook (local or cloud):

```mathematica
PacletInstall["Taggar/FinitelyPresentedGroups"]
```

## Usage

Import the package by running

```mathematica
In[]:= <<Taggar`FinitelyPresentedGroups`
```

### General usage

Define a group by its generators and relators, here the symmetric group of degree 3:

```mathematica
In[]:= G = FinitelyPresentedGroup[{r, s}, {r^3, s^2, (r ** s)^2}];
```

or convert a permutation group (or a named group) to a presentation:

```mathematica
In[]:= GroupOrder[FinitelyPresentedGroup[SymmetricGroup[4]]]
Out[]= 24
```

Make round trips between a permutation group and the corresponding FPG:

```mathematica
In[]:= CyclicGroup[3]
% // FinitelyPresentedGroup
% // PermutationGroup
% // FinitelyPresentedGroup
Out[]= CyclicGroup[3]
Out[]= FinitelyPresentedGroup[{x1}, {x1^3}]
Out[]= PermutationGroup[{Cycles[{{1, 2, 3}}]}]
Out[]= FinitelyPresentedGroup[{x1}, {x1^3}]
```

Reduce a word using the relators of the group:

```mathematica
In[]:= ElementReduce[G, r^10 ** s^5]
Out[]= r ** s
```

Check whether two words are equal in the group (returns `$Failed` if undecided within resource limits):

```mathematica
In[]:= ElementEqualQ[G, r ** s, s ** r^-1]
Out[]= True
```

### Resource limits & conversions

- Permutation-to-FP conversion supports groups up to order `10^7` (using compiled Cannon deduction up to `20,000` and Schreier-Sims stabiliser chains above that).
- `PermutationGroup[G]` searches for a verified faithful lower-degree coset action before falling back to the regular representation.
- Output-bound functions guard against memory blowups (`GroupElements` limit `50,000`, `CayleyGraph` limit `20,000`, `GroupMultiplicationTable` limit `2,500`).

### Free groups

Define free groups:

```mathematica
In[]:= F3 = FreeGroup[{a, b, c}]
Out[]= FreeGroup[{a, b, c}]
```

The free group is infinite and not abelian:

```mathematica
In[]:= GroupOrder[F3]
Out[]= Infinity

In[]:= ElementEqualQ[F3, a ** b, b ** a]
Out[]= False
```

### Coset tables

Enumerate the cosets of a subgroup. The result is a matrix with one row per coset, whose columns correspond to the generators followed by their inverses in reverse order:

```mathematica
In[]:= t = CosetTable[G, {a}]
Out[]= {{1, 2, 3, 1}, {3, 3, 1, 3}, {2, 1, 2, 2}}
```

The index of the subgroup is the number of rows, and the order of the group is the index of the trivial subgroup:

```mathematica
In[]:= Length[t]
Out[]= 3

In[]:= GroupOrder[G]
Out[]= 6
```

Check if a word lies in the subgroup by following it through the table from the first coset:

```mathematica
In[]:= Fold[t[[#1, #2]] &, 1, {2, 1, 2, -1}] == 1
Out[]= True
```

### Tietze simplification

Define a group:

```mathematica
In[]:= FinitelyPresentedGroup[{a}, {a^4, a^8}]
Out[]= FinitelyPresentedGroup[{a}, {a^4, a^8}]
```

This works, but the relator `a^8` is redundant since $a^8=(a^4)^2=1^2=1$ as it is. Therefore, this presentation can be simplified further:

```mathematica
In[]:= TietzeSimplify[%]
Out[]= FinitelyPresentedGroup[{a}, {a^4}]
```

Get rid of redundant generators:

```mathematica
In[]:= FinitelyPresentedGroup[{a, b}, {a == b}] // TietzeSimplify
Out[]= FinitelyPresentedGroup[{b}, {}]
```

### Fox derivatives

Find the Fox derivative in a finitely presented group:

```mathematica
In[]:= Table[FoxD[F3, x, y],{x, {a, b, c}}, {y,{a, b, c}}]
Out[]= {{1, 0, 0}, {0, 1, 0}, {0, 0, 1}}
```

Powers give geometric sums, and inverses give negative ones:

```mathematica
In[]:= FoxD[G, a^3, a]
Out[]= 1 + a + a^2

In[]:= FoxD[G, a^-3, a]
Out[]= -(1/a^3) - 1/a^2 - 1/a
```

Find the Alexander matrix of a group:

```mathematica
In[]:= AlexanderMatrix[FinitelyPresentedGroup[{a, b}, {a ** b ** (a^-1) ** (b^-1)}]]
Out[]= {{1 - a ** b ** (1/a), a - a ** b ** (1/a) ** (1/b)}}
```

Send the generators to a commuting symbol:

```mathematica
In[]:= AlexanderMatrix[..., {t1, t2}]
Out[]= {{1 - t2, -1 + t1}}
```

## Contributions

Please feel free to give your feedback on the package, or to contribute with an issue or a PR! The test files are in [Tests/](Tests/) directory and may be run to ensure everything functions correctly.

## Version log

**Version 1.3.0,** *on 26 November, 2026* &mdash; Some general purpose updates; add `TietzeSimplify` to simplify presentations. [log](https://github.com/zplus11/FinitelyPresentedGroups/compare/v1.2.0...v1.3.0)

**v1.2.0,** *on 30 October, 2026* &mdash; API change: `FPGWord` is removed in favour of simplicity, and `FreeGroup` stays as a head rather than getting evaluated to `FinitelyPresentedGroup`. [log](https://github.com/zplus11/FinitelyPresentedGroups/compare/v1.1.0...v1.2.0)

**v1.1.0,** *on 19 October, 2026* &mdash; order of an element; convert named groups to FPG, round trips between permutation groups and FPGs. [log](https://github.com/zplus11/FinitelyPresentedGroups/compare/v1.0.0...v1.1.0)

**v1.0.0,** *on 11 October, 2026* &mdash; first release.

**v0.0.2,** *on 10 October, 2026* &mdash; coset enumeration.

**v0.0.1,** *on 15 August, 2026* &mdash; initial upload with `FinitelyPresentedGroup` and `FPGWord`s.