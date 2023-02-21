# The long exact sequence of Yoneda Ext

This repository contains the formalisation of the long exact sequence of Yoneda Ext in univalent foundations following the proof of theorem XII.5.1 in Mac Lane's "Homology".
The following is a brief overview of the files:

- `Lemmas.v` contains two general lemmas, and a proof that `loops_abses` is a group isomorphism along with related facts.
- `EquivalenceRelation.v` contains basic results we need about the equivalence relation generated from a relation
- `ES.v` contains the definition and basic theory of the type `ES n` whose quotient is `Ext n`
- `HigherExt.v` contains the definition of `Ext n` using `ES.v`
- `XII_5.v` contains the key lemmas (XII.5.3-5) which go into proving the long exact sequence; they are first proved on the level of `ES n` and then deduced for `Ext n`
- `LES.v` contains the proof of exactness of the long exact sequence

This version has been tested with Coq 8.16.1 against commit 3062f0a15 of HoTT-Coq from Feb 19, 2023.
