# The long exact sequence of Yoneda Ext

This repository mainly contains material related to section 5 of the paper [Formalising Yoneda Ext in Univalent Foundations](https://arxiv.org/abs/2302.12678) ([doi](https://drops.dagstuhl.de/opus/volltexte/2023/18391/)) which pertains to the long exact sequence of Ext groups.
Our formalisation follows the proof of theorem XII.5.1 in Mac Lane's "Homology".
The following is a brief overview of the files:

- `Lemmas.v` contains two general lemmas, and a proof that `loops_abses` is a group isomorphism along with related facts.
- `EquivalenceRelation.v` contains basic results we need about the equivalence relation generated from a relation
- `ES.v` contains the definition and basic theory of the type `ES n` whose quotient is `Ext n`
- `HigherExt.v` contains the definition of `Ext n` using `ES.v`
- `XII_5.v` contains the key lemmas (XII.5.3-5) which go into proving the long exact sequence; they are first proved on the level of `ES n` and then deduced for `Ext n`
- `LES.v` contains the proof of exactness of the long exact sequence

This version has been tested with Coq 8.16.1 against commit 3062f0a15 of HoTT-Coq from Feb 19, 2023.

## Build instructions
1. Install Coq 8.16.1.

The can be done by first installing `opam` (see https://opam.ocaml.org/) and then running `opam install coq`. If the current version is no longer 8.16.1, then you need to run `opam pin add coq 8.16.1` before the install command. (Though things may well work with a newer version of Coq.)

2. Build the [Coq-HoTT library](https://github.com/HoTT/Coq-HoTT/tree/master).

It will probably work to install the Coq-HoTT library through `opam`, as described [here](https://github.com/HoTT/Coq-HoTT/blob/master/INSTALL.md#2-installation-of-hott-library-using-opam). If not, follow the instructions there for manually buildling the library, and use commit 3062f0a15 from Feb 19, 2023.

3. Clone and set up this repository.

Run `git clone https://github.com/jarlg/Yoneda-Ext`, then remove the second line of `_CoqProject` if you installed `coq-hott` via `opam` or change it to point to your local copy of the Coq-HoTT library if you built it manually.

4. Build this project by running `make`.

After `make` has finished, you can step through the various files using e.g. `coqide` or Emacs with [Proof General](https://proofgeneral.github.io/).
