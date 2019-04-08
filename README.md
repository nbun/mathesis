# Master's Thesis: Modelling Call-Time Choice as Effect using Scoped Free Monads

This repository contains the code presented in [Modelling Call-Time Choice as Effect using Scoped Free Monads](Thesis/Mathesis.pdf).
The initial motivation and goals can be found [here](Goals.md).

## Structure

The directory structure is as follows.

* Coq: Two approaches to modeling call-time choice semantics in Coq.
  1. Fully functional implementation which uses explicit scope delimiters
  2. Higher-Order version without lifted recursive data types
* Curry: Sharing test suite as well as permutation sort and QuickSort examples
* Haskell: Three approaches to modeling call-time choice semantics in Haskell.
  1. Explicit scope delimiters
  2. Higher-Order
  3. Hybrid (does not work, kept for documentation purposes)
* Presentation: LaTeX source for slides of proposal and final presentation
* Thesis: LaTeX source for thesis

More detailed information about the contents of a directory can be found in the respective README file.

## Compilation

The code can be compiled with the following tools.

* Curry: KiCS2, version 2.0.0-b17
* Haskell: GHC, version 8.4.3
* Coq: coqc, version 8.9.0
