# Finitely Presented Groups

FinitelyPresentedGroups is a Wolfram language paclet (package) for working with finitely presented groups: defining a group by generators and relators, manipulating group words, and enumerating cosets of subgroups using the Todd-Coxeter algorithm.

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
In[2]:= G = FinitelyPresentedGroup[{a, b}, {a^2, b^3, (a ** b)^2}];
```

or convert a permutation group (or a named group) to a presentation:

```mathematica
In[3]:= GroupOrder[FinitelyPresentedGroup[SymmetricGroup[4]]]
Out[3]= 24
```

Create group words using generator indices (negative for inverses) or the generators themselves, and reduce them using the relators:

```mathematica
In[4]:= w = FPGWord[G, a^10 ** b^5];
In[5]:= FPGWordReduce[w]
```

Words can be multiplied, inverted, raised to powers and compared:

```mathematica
In[6]:= FPGWord[G, {1, 2}] == FPGWord[G, {-2, -1}]
Out[6]= True
```

Enumerate the cosets of a subgroup. The result is a matrix with one row per coset, whose columns correspond to the generators followed by their inverses in reverse order:

```mathematica
In[7]:= t = CosetTable[G, {a}]
Out[7]= {{1, 2, 3, 1}, {3, 3, 1, 3}, {2, 1, 2, 2}}
```

The index of the subgroup is the number of rows, and the order of the group is the index of the trivial subgroup:

```mathematica
In[8]:= Length[t]
Out[8]= 3

In[9]:= GroupOrder[G]
Out[9]= 6
```

Check if a word lies in the subgroup by following it through the table from the first coset:

```mathematica
In[10]:= Fold[t[[#1, #2]] &, 1, {2, 1, 2, -1}] == 1
Out[10]= True
```

## Contributions

Please feel free to give your feedback on the package, or to contribute with an issue or a PR! The test files are in [Tests/](Tests/) directory and may be run to ensure everything functions correctly.

## Version log
 
**Version 1.0.0,** *on 11 October, 2026* &mdash; first release.

**v0.0.2,** *on 10 October, 2026* &mdash; coset enumeration.

**v0.0.1,** *on 15 August, 2026* &mdash; initial upload with `FinitelyPresentedGroup` and `FPGWord`s.