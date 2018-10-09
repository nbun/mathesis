# Modelling Call-Time Choice as Effect using Scoped Free Monads

Effect handlers become more and more popular when working with the syntax and semantics of a language.
Syntax is usually represented with an AST-like data structure and the semantics is then described using effect handlers.
There are a variety of effects than can be described using this combination.
More recently, scoped effects (like the cut operator known from LP) became of interest (see [1,2]).
Fortunately, scoped effects turned out to be useful to describe call-time choice semantics known from FLP as well.
An executable semantics specification that combines scoped effects and the ideas introduced by Fischer et al. (see [3])
implemented in Haskell as well as a translation to Coq will be used as starting point for this thesis.
The Coq translation cannot use the ideas presented by Schrijvers et all [3], but needs to turn to a more verbose version used in (2) in order to
please Coq's termination checker.
The implementation follows the ideas introduced by Dylus et al. (see [5]). 
In order to see the specifcations in action, the laws of such a language with call-time choice,
which are described by Fischer et al. [3], were defined in Coq as axioms (if not trivally proven as true).
Using these axioms as equational rules, a simple library (see [4]) was implemented in this setting as well as some first attempts to
prove properties of the library.

This master's thesis builds upon these building blocks to reach the following goals.

(1) Implement a minimised version of the current code base that only has a handful of types/data structures.  
(2) Prove the equational laws from Fischer et al. in this minimised setting.  
(3) Prove the properties about the PFLP library in this minimised setting.  

It is pretty obvious that several new obstacles will arise that need to be tackled.
Furthermore, it is crucial to establish an understanding about the overall problem.

## Phase 1: Read the provided literature

* write a summary for each paper (you need this anyway later)

## Phase 2: Study the Haskell code

* start with the Haskell code and make sure to understand what's going on here
* implement HO-functors (see [2]) for call-time choice effect in Haskell

## Phase 3: Study the Coq code & implement a minimised Coq version (incremental process)

* try to follow an incremental approach; reimplement functionality only if it's really necessary
* use a project structure similar to the one provided
* decide on a subset of relevant types/data structures
* translate the HO-functors-approach to Coq (this may not work out as expected)

## Phase 4: Prove the equational laws

* fill in the magic here

## Phase 5: Everything in action

* implement simple Curry programs and prove properties about these programs
* prove the monad laws for PFLP library

## Phase 5: Write-up

* write
* you should be writing
* why aren't you writing?

[1] [Syntax and Semantics for Operations with Scopes](https://people.cs.kuleuven.be/~tom.schrijvers/Research/papers/lics2018.pdf)  
[2] [Effect Handlers in Scope](https://people.cs.kuleuven.be/~tom.schrijvers/Research/papers/haskell2014.pdf)  
[3] [Purely Functional Lazy Non-deterministic Programming](http://www-ps.informatik.uni-kiel.de/~sebf/data/pub/icfp09.pdf)  
[4] [Probabilistic Functional Logic Programming](http://www-ps.informatik.uni-kiel.de/~sad/padl2018-preprint.pdf)  
[5] [One Monad to Prove them All](https://arxiv.org/pdf/1805.08059.pdf)  