Formalizing _Types and Programming Languages_ in Isabelle/HOL
=================================

We formalize, using Isabelle/HOL, some languages present in the first two sections, namely "Untyped
Systems" and "Simple Types", of the book _Types and Programming Languages_ by Benjamin~C.~Pierce.
We first begin with a short tour of the lambda-calculus, type systems and the Isabelle/HOL theorem
prover before attacking the formalization _per se_. Starting with an arithmetic expressions language
offering Booleans and natural numbers, we pursue, after a brief digression to de Bruijn indices, to
the untyped lambda-calculus. Then, we return to a typed variant of the arithmetic expression
language before concluding with the simply typed lambda-calculu.
