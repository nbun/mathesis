# Haskell

This implementation is based on [Effect Handlers in Scope](https://people.cs.kuleuven.be/~tom.schrijvers/Research/papers/haskell2014.pdf).

* Data: Contains lifted lists, pairs and primitive types as well as lifted function definitions
* examples: Test suite as well as permutation sort and Quicksort algorithms
* thesis: Example definitions from "Purely Functional Non-Deterministic Lazy Programming" and the thesis

* Base.hs: Definition of the basic effect handler infrastructure
* CallTimeChoice.hs: Implementation of the call-time choice effect with explicit scope delimiters
* CallTimeChoiceHO.hs : Higher-Order implementation of the call-time choice effect
* CallTimeChoiceHybrid.hs: Hybrid implementation **DOES NOT WORK; ONLY KEPT FOR DOCUMENTATION PURPOSES**
* Convert.hs: Converting data types in the corresponding lifted representation
* HO.hs: Definition of the basic higher-order effect handler infrastructure
* Pretty.hs: Pretty printing of choice trees
* SharingInterface.hs: Interface for defining explicit sharing implementations
* Tree.hs: Definition of choice trees and the depth-first search algorithm
