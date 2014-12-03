(*<*)
theory Examples
  imports Main
begin
(*>*)

text {*
The theorem proving community can be subdivise in two groups: automatic theorem proving (ATP) and
interactive theorem proving (ITP). Each have their own set of motivation, goals, methodologies and
tools. In ATP, one must formulate it's context and equations in some logical formalisms and ask the
theorem to find a proof. The limiting factor will be the algorithm used by the tool. Example of such
provers include Z3, Vampire and SPASS. In ITP, one must also formulate it's context and equations in
some logical formalisms, although usually a stronger one, and will give instructions guiding the
prover, which explain the usual name of proof assistant. Here, the limiting factor will be the
ability of the human to guide it's tool. Example of interactive theorem provers include Isabelle,
Coq and Agda provers and the proof assistants.

Isabelle is a generic interactive theorem prover for implementing logical formalisms and
Isabelle/HOL is its specialization to higher order logic. We will now present the main notions
needed to read the comming formalizations. To this end, we will establish a comparaison with typical
programming languages from the ML family.

A Isabelle theory file serve as the basic unit of encapsulation of formalizations and reusable
libraries. Is analogous to modules in programming languages. Every definition and theorems
developped must belong to a theory and can be made accessible to other theories by importing them.

Types and function definitions serve to describe entities and how to operate on them. They work in
very similar way to their counterpart in functional programming languages. A new type is introduce
with the \texttt{datatype} command, followed by the name of the type and the different constructors
separated by a \texttt{|}. Following is the standard definition of the parametric \texttt{list}
datatype.

*}

datatype_new 'a list = Nil | Cons (head: 'a) (tail: "'a list")

text {*
Definitions can take many forms in isabelle/HOL. A primitively recursive function is introduced with
the \texttt{primrec} command and defined by pattern matching over its arguments. Each pattern match
entry must then provide the value to which the function evaluate. Following is a definition of the
\texttt{ordered} higher order function which checked if all the elements of a lis are ordered with
respect to a binary predicate provided as an argument.
*}

primrec ordered :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
  "ordered f Nil = True" |
  "ordered f (Cons x xs) = (case xs of
     Nil \<Rightarrow> True |
     Cons y ys \<Rightarrow> f x y \<and> ordered f xs)"

text {*
An way in which this function could have been defined is with an inductive definition. Introduced
with the \texttt{inductive} command, it allows to express boolean functions by providing an
inductive definition of when the function should evaluate to true, leaving all the other cases to
false. The definition consists of a base case and possibly many inductive cases. Following is the
same function, named \texttt{ordered'} this time, using an inductive definition.
*}

inductive ordered' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
  "ordered' f Nil" |
  "ordered' f (Cons x Nil)" |
  "f x1 x2 \<Longrightarrow> ordered' f (Cons x2 xs) \<Longrightarrow> ordered' f (Cons x1 (Cons x2 xs))"

text {*
Theorems, also named lemmas, are true facts involving the defined elements. They could be compare to
the asserts used in programming languages. The main difference is that asserts are validate by
evaluating the expression while theorems are validate by a formal proof. This is the point where the
analogy with programming languages stops since this concept is unique to theorem provers. In
Isabelle/HOL, a proof can take two forms: a low-level sequence of \texttt{apply} steps or
higher-level structured definition. Following is an example of a lemma that proved, using the
low-level style, that the list of increasing natural numbers are ordered with respect to the usual
comparison operation.
*}

lemma "ordered (\<lambda>x y. x < y) (Cons (1 :: nat) (Cons 2 (Cons 3 (Cons 4 Nil))))"
  apply (unfold ordered.simps)
  apply (unfold list.case)
  apply (rule conjI, simp)+
  apply (rule TrueI)
done

text {*
This proof is easilly verified by a computer but very hard to read for a human. For this reason,
the Isabelle/Isar structured proof language was designed to allow the writing of more human-friendly
proofs. Following is a theorem that, whenever the \texttt{ordered} function returns true for a given
predicate and list, the \texttt{ordered'} function will also return true.
*}

lemma primrec_imp_inductive:
  "ordered f xs \<Longrightarrow> ordered' f xs"
proof (induction xs rule: list.induct)
  case Nil
  thus ?case by (auto intro: ordered'.intros)
next
  case (Cons x xs)
  thus ?case by (cases xs rule: list.exhaust) (auto intro: ordered'.intros)
qed

text {*
This proof is still easilly verified by a computer but it is also more readable for a human. It is
easy to see that the proof work by induction on the list \texttt{xs}, that the base case is first
proved and that the inductive case performs a cases analysis of the values the argument \texttt{xs}
can take.

This section only presented briefly the most used constructions in the formalizations described in
this thesis. It is not expect from the reader without previous exposure to Isabelle/HOL to be able
to fully understand the the proofs presented in this report. It is sufficient to recognise core
concepts such as induction or cases analysis.

For a real introduction to Isabelle/HOL, the reader is encourage to start with the tutorial
\cite{???} distributed with the system and continue, for a deeper understanding, with the more
exaustive manual \cite{???}.
*}

(*<*)
end
(*>*)
