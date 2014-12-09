(*<*)
theory Examples
  imports Main
begin
(*>*)

text {*
This section only presents briefly the most used constructions in the formalizations described in
this thesis. It is not expected from the reader without previous exposure to Isabelle/HOL to be able
to fully understand the proofs presented in this report. It is sufficient to recognise core concepts
such as induction or cases analysis.

The theorem proving community can be subdivise in two groups: automatic theorem proving (ATP) and
interactive theorem proving (ITP). Each have their own set of motivation, goals, methodologies and
tools. In ATP, one must formulate it's context and equations in some logical formalisms and ask the
theorem to find a proof. The limiting factor is the algorithm used by the tool. Example of such
provers include Z3, Vampire and SPASS. In ITP, one must also formulate it's context and equations in
some logical formalisms, although usually a more expressive one, but must give instructions guiding
the prover. The term proof assistant is sometime used to highlight this collaboration between the
human and the machine. Here, the limiting factor is the ability of the human to guide it's tool.
Examples of interactive theorem provers include Isabelle, Coq and Agda.

Isabelle is a generic interactive theorem prover for implementing logical formalisms and
Isabelle/HOL is its specialization to higher order logic. We will now present the main notions
needed to read the comming formalizations. To this end, we will establish a comparaison with typical
programming languages from the ML family.

An Isabelle theory file serves as the basic unit of encapsulation of formalizations and reusable
libraries. Is analogous to modules in programming languages. Every definition and theorems
developped must belong to a theory and can be made accessible to other theories by importing them.

Types and function definitions serve to describe entities and how to operate on them. They work in
very similar way to their counterpart in functional programming languages. A new type is introduced
with the \texttt{datatype} command, followed by the name of the type and the different constructors
separated by a \texttt{|}. Following is the standard definition of the type of parametric
lists:\footnote{Prefixing an element with a descriptive name, as done for the arguments of the
@{text Cons} constructor, is a common pattern in Isabelle/HOL. The syntax is always
\texttt{name : element}.}
*}

datatype_new 'a list = Nil | Cons (head: 'a) (tail: "'a list")

text {*
Function definitions can take many forms in isabelle/HOL. A primitively recursive function is
introduced with the \texttt{primrec} command and defined by pattern matching over its arguments.
Each pattern match entry must then provide the value to which the function evaluate. Following is a
definition of a higher order function that check if all the elements of a list are ordered with
respect to a binary predicate provided as an argument:
*}

primrec ordered :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
  "ordered f Nil = True" |
  "ordered f (Cons x xs) = (case xs of
     Nil \<Rightarrow> True |
     Cons y ys \<Rightarrow> f x y \<and> ordered f xs)"

text {*
An alternative way in which this function could be defined is with an inductive definition.
Introduced with the \texttt{inductive} command, it allows to express boolean functions by providing
an inductive definition of when the function should evaluate to true, leaving all the other cases to
false. The definition consists of base cases and possibly many inductive cases. Following is the
same function defined by induction:\footnote{Here, a descriptive name have been given to each rule.
The base cases are @{text empty_list} and @{text singleton_list} while the inductive case is
@{text arbitrary_list}.}
*}

inductive ordered' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
  empty_list:
    "ordered' f Nil" |
  singleton_list:
    "ordered' f (Cons x Nil)" |
  arbitrary_list:
    "f x1 x2 \<Longrightarrow> ordered' f (Cons x2 xs) \<Longrightarrow> ordered' f (Cons x1 (Cons x2 xs))"

text {*
Theorems, also named lemmas, are true facts involving the defined elements. They could be compare to
the asserts used in programming languages. The main difference is that asserts are validate by
evaluating the expression while theorems are validate by a formal proof. This is the point where the
analogy with programming languages stops since this concept is unique to theorem provers. In
Isabelle/HOL, a proof can take two forms: a low-level sequence of \texttt{apply} steps or
higher-level structured definition. Following is an example of a lemma that proves, using the
low-level style, that the list of increasing natural numbers are ordered with respect to the usual
comparison operation:
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
proofs. Following is a theorem showing that, whenever the @{const ordered} function returns true for
a given predicate and list, the @{const ordered'} function will also return true:\footnote{In
Isabelle, every unbounded term is implicitly universally quantified:
@{prop [source] "n + 1 > n"}~$\equiv$~@{prop [source] "(\<And>n. n + 1 > n)"}.}
*}

lemma primrec_imp_inductive:
  "ordered f xs \<Longrightarrow> ordered' f xs"
proof (induction xs rule: list.induct)
  case Nil
  thus ?case by (auto intro: ordered'.intros)
next
  case (Cons y ys)
  thus ?case by (cases ys rule: list.exhaust) (auto intro: ordered'.intros)
qed

text {*
This proof is still easilly verified by a computer but is also more readable for a human. It is easy
to see that the proof work by induction on the list @{term xs}, that the base case (@{const Nil}) is
first proved and that in the inductive case @{const Cons}, a cases analysis of the values the
argument @{term ys} can take is performed.

For a more comprehensive introduction to Isabelle/HOL, the reader is encourage to start with the
tutorial \cite{nipkow-2014-prog-prove} distributed with the system and continue, for a deeper
understanding, with the more exaustive manual \cite{nipkow-et-al-2014-tutorial}.
*}

(*<*)
end
(*>*)
