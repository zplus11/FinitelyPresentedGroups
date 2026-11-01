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
In[1]:= <<Taggar`FinitelyPresentedGroups`
```

Define a group by its generators and relators, here the symmetric group of degree 3:

```mathematica
In[2]:= G = FinitelyPresentedGroup[{r, s}, {r^3, s^2, (r ** s)^2}];
```

or convert a permutation group (or a named group) to a presentation:

```mathematica
In[3]:= GroupOrder[FinitelyPresentedGroup[SymmetricGroup[4]]]
Out[3]= 24
```

Make round trips between a permutation group and the corresponding FPG:

```mathematica
In[4]:= CyclicGroup[3]
% // FinitelyPresentedGroup
% // PermutationGroup
% // FinitelyPresentedGroup
Out[4]= CyclicGroup[3]
Out[5]= FinitelyPresentedGroup[{x1}, {x1^3}]
Out[6]= PermutationGroup[{Cycles[{{1, 2, 3}}]}]
Out[7]= FinitelyPresentedGroup[{x1}, {x1^3}]
```

Reduce a word using the relators of the group:

```mathematica
In[8]:= ElementReduce[G, r^10 ** s^5]
Out[8]= r ** s
```

Check whether two words are equal in the group:

```mathematica
In[9]:= ElementEqualQ[G, r ** s, s ** r^-1]
Out[9]= True
```

--

Define free groups:

```mathematica
In[10]:= F3 = FreeGroup[{a, b, c}]
Out[10]= FreeGroup[{a, b, c}]
```

The free group is infinite and not abelian:

```mathematica
In[11]:= GroupOrder[F3]
Out[11]= Infinity

In[12]:= ElementEqualQ[F3, a ** b, b ** a]
Out[12]= False
```

--

Enumerate the cosets of a subgroup. The result is a matrix with one row per coset, whose columns correspond to the generators followed by their inverses in reverse order:

```mathematica
In[13]:= t = CosetTable[G, {a}]
Out[13]= {{1, 2, 3, 1}, {3, 3, 1, 3}, {2, 1, 2, 2}}
```

The index of the subgroup is the number of rows, and the order of the group is the index of the trivial subgroup:

```mathematica
In[14]:= Length[t]
Out[14]= 3

In[15]:= GroupOrder[G]
Out[15]= 6
```

Check if a word lies in the subgroup by following it through the table from the first coset:

```mathematica
In[16]:= Fold[t[[#1, #2]] &, 1, {2, 1, 2, -1}] == 1
Out[16]= True
```

--

Find the Fox derivative in a finitely presented group:

```mathematica
In[17]:= Table[FoxD[F3, x, y],{x, {a, b, c}}, {y,{a, b, c}}]
Out[17]= {{1, 0, 0}, {0, 1, 0}, {0, 0, 1}}
```

Powers give geometric sums, and inverses give negative ones:

```mathematica
In[18]:= FoxD[G, a^3, a]
Out[18]= 1 + a + a^2

In[19]:= FoxD[G, a^-3, a]
Out[19]= -(1/a^3) - 1/a^2 - 1/a
```

Find the Alexander matrix of a group:

```mathematica
In[20]:= AlexanderMatrix[FinitelyPresentedGroup[{a, b}, {a ** b ** (a^-1) ** (b^-1)}]]
Out[20]= {{1 - a ** b ** (1/a), a - a ** b ** (1/a) ** (1/b)}}
```

Send the generators to a commuting symbol:

```mathematica
In[21]:= AlexanderMatrix[..., {t1, t2}]
Out[21]= {{1 - t2, -1 + t1}}
```

## Contributions

Please feel free to give your feedback on the package, or to contribute with an issue or a PR! The test files are in [Tests/](Tests/) directory and may be run to ensure everything functions correctly.

## Version log

**Version 1.2.0,** *on 30 October, 2026* *mdash; API change: `FPGWord` is removed in favour of simplicity, and `FreeGroup` stays as a head rather than getting evaluated to `FinitelyPresentedGroup`. [log](https://github.com/zplus11/FinitelyPresentedGroups/compare/v1.1.0...v1.2.0)

**v1.1.0,** *on 19 October, 2026* &mdash; order of an element; convert named groups to FPG, round trips between permutation groups and FPGs. [log](https://github.com/zplus11/FinitelyPresentedGroups/compare/v1.0.0...v1.1.0)

**v1.0.0,** *on 11 October, 2026* &mdash; first release.

**v0.0.2,** *on 10 October, 2026* &mdash; coset enumeration.

**v0.0.1,** *on 15 August, 2026* &mdash; initial upload with `FinitelyPresentedGroup` and `FPGWord`s.