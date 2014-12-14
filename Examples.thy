(*<*)
theory Examples
  imports Main
begin
hide_const Nil Cons
hide_type list
(*>*)

text {*
This section only presents briefly the most used constructions in the formalizations described in
this thesis. It is not expected from the reader to fully understand the proofs presented in this
report; it is sufficient to recognize key concepts such as induction and case analysis.

The theorem proving community is subdivided in two groups: automatic theorem proving (ATP) and
interactive theorem proving (ITP). Each has its own set of goals, motivations, methodologies,
tools and terminology. In ATP, one must formulate its context and equations in some logical
formalism and ask the theorem prover to find a proof. The limiting factor is the algorithm used by
the tool. Examples of such provers include SPASS, Vampire and Z3. In ITP, one must also formulate
its context and equations in some logical formalism, although usually a more expressive one, but
must also give instructions guiding the prover. The term proof assistant is sometime used to
highlight this collaboration between the human and the machine. Here, the limiting factor is the
ability of the human to guide its tool. Examples of interactive theorem provers include Agda, Coq
and Isabelle. Isabelle is a generic interactive theorem prover for implementing logical formalisms
and Isabelle/HOL is its specialization to a formalism called higher order logic.

An Isabelle theory file serves as the basic unit of encapsulation of formalizations and reusable
libraries. It is analogous to modules in programming languages. Every definition and theorem
developed must belong to a theory and can be made accessible to other theories by importing them.

Types and function definitions serve to describe entities and how to operate on them. They work in a
very similar way to their counterpart in functional programming languages. A new type is introduced
with the \texttt{datatype} command, followed by the name of the type and the different constructors
separated by a \texttt{|}. Following is the standard definition of the type of parametric
lists:\footnote{Prefixing an element with a descriptive name, as done for the arguments of the
@{text Cons} constructor, is a common pattern in Isabelle/HOL. The syntax is always
\texttt{name : element}.}
*}

datatype_new 'a list = Nil | Cons (head: 'a) (tail: "'a list")

text {*
The datatype consists of two constructors. The first one, @{const Nil}, is used to represent the
empty list while the second one, @{const Cons}, is used to add an element in front of an existing
list. Using those two primitives, a list can be created by successive application of the @{const
Cons} constructor (e.g. @{term [source] "Cons 1 (Cons 2 (Cons 3 Nil))"}). The \emph{'a} in front
of the name is a placeholder for a concrete type that must be provide later (e.g. the type of the
previous example could be @{typ "nat list"}).

Function definitions can take many forms in Isabelle/HOL. A primitively recursive function is
introduced with the \texttt{primrec} command and defined by pattern matching over its arguments.
Each pattern match entry must then provide the value to which the function evaluates. Following is a
definition of a higher order function (i.e. a function that takes a function as argument) that
checks if all the elements of a list are ordered with respect to a binary predicate provided as an
argument:
*}

primrec ordered :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
  "ordered p Nil = True" |
  "ordered p (Cons x xs) = (case xs of
     Nil \<Rightarrow> True |
     Cons y ys \<Rightarrow> p x y \<and> ordered p xs)"

text {*
An alternative way in which this function could be defined is inductively. Introduced with the
\texttt{inductive} command, it allows to express Boolean functions by providing an inductive
definition of when the function should evaluate to true, leaving all the other cases to false. The
definition consists of base cases and possibly many inductive cases. Following is the same function
defined inductively:\footnote{Here, a descriptive name have been given to each rule. The base
cases are @{text empty_list} and @{text singleton_list} while the inductive case is @{text
arbitrary_list}.}
*}

inductive ordered' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
  empty_list:
    "ordered' p Nil" |
  singleton_list:
    "ordered' p (Cons x Nil)" |
  arbitrary_list:
    "p x1 x2 \<Longrightarrow> ordered' p (Cons x2 xs) \<Longrightarrow> ordered' p (Cons x1 (Cons x2 xs))"

text {*
Theorems, also named lemmas, are true facts involving the defined elements. They could be compared
to the assertions used in programming languages. The main difference is that asserts are validate by
evaluating the expression while theorems are validated by a formal proof. This is the point where
the analogy with programming languages stops since this concept is unique to theorem provers. In
Isabelle/HOL, a proof can take two forms: a low level sequence of \texttt{apply} steps or higher
level structured definition. Following is an example of a lemma that proves, using the low level
style, that the list of increasing natural numbers are ordered with respect to the usual comparison
operation:
*}

lemma "ordered (\<lambda>x (y :: nat). x < y) (Cons 1 (Cons 2 (Cons 3 (Cons 4 Nil))))"
  apply (unfold ordered.simps)
  apply (unfold list.case)
  apply (rule conjI, simp)+
  apply (rule TrueI)
done

text {*
This proof is easily checked by a computer but very hard to read for a human. For this reason, the
alternative structured Isar proof language was designed to allow the writing of more human-friendly
proofs. Following is a theorem showing that, whenever the @{const ordered} function returns true for
a given predicate and list, the @{const ordered'} function will also return true:\footnote{In
Isabelle, every unbound term is implicitly universally quantified:
$n + 1 > n \: \equiv \: (\forall n. \ n + 1 > n)$.}
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
This proof is still easily checked by a computer but is also more readable for a human. It is easy
to see that the proof works by induction on the list @{term xs}, that the base case (@{const Nil})
is first proved and that in the inductive case (@{const Cons}), a cases analysis of the values the
argument @{term ys} can take is performed.

For a more comprehensive introduction to Isabelle/HOL, the reader is encourage to start with the
first part of the book \emph{Concrete Semantics} \cite{nipkow-klein-2014-concrete-semantics} and
continue, for a deeper understanding, with the more exhaustive tutorial
\cite{nipkow-et-al-2014-tutorial} distributed with the system.
*}

(*<*)
end
(*>*)
