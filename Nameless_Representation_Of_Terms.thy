(*<*)
theory Nameless_Representation_Of_Terms
imports Main
begin
(*>*)

chapter {* Nameless Representation of Terms *}

text {*
In the background section on lambda-calculus (section \label{sec:background-lambda-calculus}), we
presented the problem of name clashes that can arise when performing $\beta$-reduction. In its
definitions and proofs, the book only work up to $\alpha$-equivalence: assuming that the variables
would be implicitly renamed if such a name clash occured. In a separate chapter, a different
representation of terms that avoids such problem is presente. It is describe to as one possible
encoding that can be used when implementing an compiler for the lambda-calculus.

Even though we are not building a compiler, our computer verrified formalization requires us to
explicitly handle this problem. We choose to use this representation and, thus must also
formalize this chapter.

The idea behind this representation, known as "de Bruijn indices", is to make variables reference
directly their corresponding binder, rather than refering to them by name. This is accomplished by
using an index that refer to the $n$'th enclosing $\lambda$. Following is an example of
"de Bruijn indices" representation for the function composition combinator:

\begin{displaymath}
  \lambda x. \lambda y. \lambda z. x (y \text{ } z)
    \equiv \lambda. \lambda. \lambda. 2 (1 \text{ } 0)
\end{displaymath}

This representatin frees us from considering the case of variable name clashes at the expense of
being harder to read and having to maintain the correct indices when entering and leaving function
abstractions. We defined the syntax of the untyped lambda calculus as follow:\footnote{The prefix
\emph{ul} stands for \emph{untyped lambda-calculus}.}
*}

datatype ulterm =
  ULVar nat |
  ULAbs ulterm |
  ULApp ulterm ulterm

text {*
Which means that the same example of the function composition combinator would looks like this:

\begin{center}
  \small
  @{term "ULAbs (ULAbs (ULAbs (ULApp (ULVar 2) (ULApp (ULVar 1) (ULVar 0)))))"}  
\end{center}
*}

(*<*)
(* Definition 6.1.2 *)

inductive n_term :: "nat \<Rightarrow> ulterm \<Rightarrow> bool" where
  n_term_ULVar: "0 \<le> k \<Longrightarrow> k < n \<Longrightarrow> n_term n (ULVar k)" |
  n_term_ULAbs: "n_term n t \<Longrightarrow> n > 0 \<Longrightarrow> n_term (n - 1) (ULAbs t)" |
  n_term_ULApp: "n_term n t1 \<Longrightarrow> n_term n t2 \<Longrightarrow> n_term n (ULApp t1 t2)"
(*>*)

(* Definition 6.2.1 *)

text {*
We defined a shift function serving to increase, or decrease, all variables bigger than @{term c} in
a term by a fix amount @{term d}:
*}

primrec shift_UL :: "int \<Rightarrow> nat \<Rightarrow> ulterm \<Rightarrow> ulterm" where
  "shift_UL d c (ULVar k) = ULVar (if k < c then k else nat (int k + d))" |
  "shift_UL d c (ULAbs t) = ULAbs (shift_UL d (Suc c) t)" |
  "shift_UL d c (ULApp t1 t2) = ULApp (shift_UL d c t1) (shift_UL d c t2)"

text {*
An attentive reader will notice that there is a possible information loss in this definition. The
variables use a natural number as index but the function allows to shift both up and down, thus the
use of an integer as an argument. When a variable is encounter, we first convert the index from
natural number to integer, which is always safe, perform the integer addition, which correspond to a
subtraction if @{term d} is negative, and convert the result back to natural numbers to serve as the
new index. This last conversion is will convert every negative number to zero. We know this loss of
information is safe, since it makes no sence to speak of negative indices. Our @{const shift_UL}
function thus have an implicit assumption that it should not be called with a negative number bigger
than the smallest variable in the term. Following is an example of shifting up every variable by 2:
*}

(* Exercice 6.2.2 *)

lemma "shift_UL 2 0
  (ULAbs (ULAbs (ULApp (ULVar 1) (ULApp (ULVar 0) (ULVar 2))))) =
   ULAbs (ULAbs (ULApp (ULVar 1) (ULApp (ULVar 0) (ULVar 4))))"
  by simp
(*<*)

lemma "shift_UL 2 0
  (ULAbs (ULApp (ULVar 0) (ULApp (ULVar 1) (ULAbs (ULApp (ULVar 0) (ULApp (ULVar 1) (ULVar 2))))))) =
   ULAbs (ULApp (ULVar 0) (ULApp (ULVar 3) (ULAbs (ULApp (ULVar 0) (ULApp (ULVar 1) (ULVar 4))))))"
  by simp

(* Exercice 6.2.3 *)

lemma "n_term n t \<Longrightarrow> n_term (n + nat d) (shift_UL d c t)"
proof (induction n t arbitrary: d c rule: n_term.induct)
  case (n_term_ULVar k n)
  thus ?case by (auto intro: n_term.intros)
next
  case (n_term_ULAbs n t)
  thus ?case
    using n_term.n_term_ULAbs by (auto)
next
  case (n_term_ULApp n t1 t2)
  thus ?case by (auto intro: n_term.intros)
qed

(*>*)
text {*
We now define a substitution function that replaces every variable refering to the @{term j}'th
$\lambda$ by @{term s} in some term:
*}
(* Definition 6.2.4 *)

primrec subst_UL :: "nat \<Rightarrow> ulterm \<Rightarrow> ulterm \<Rightarrow> ulterm" where
  "subst_UL j s (ULVar k) = (if k = j then s else ULVar k)" |
  "subst_UL j s (ULAbs t) = ULAbs (subst_UL (Suc j) (shift_UL 1 0 s) t)" |
  "subst_UL j s (ULApp t1 t2) = ULApp (subst_UL j s t1) (subst_UL j s t2)"

(* Exercice 6.2.5 *)

text {*
Following is an example of substituing variable 0 by variable 1:
*}

lemma "subst_UL 0 (ULVar 1)
  (ULApp (ULVar 0) (ULAbs (ULAbs (ULVar 2)))) =
   ULApp (ULVar 1) (ULAbs (ULAbs (ULVar 3)))"
  by simp

text {*
Note that the indices are not absolute values, they are relative to their position in the term. This
is why @{term "ULVar 2"} is also substitute in the previous example: counting the number of
enclosing $\lambda$ shows us that this variable is, indeed, the same as @{term "ULVar 0"}. Of
course, we must maintain this invarient by incrementing variables in our substituting term
accordignly.
*}

(*<*)
lemma "subst_UL 0 (ULApp (ULVar 1) (ULAbs (ULVar 2)))
  (ULApp (ULVar 0) (ULAbs (ULVar 1))) =
   ULApp (ULApp (ULVar 1) (ULAbs (ULVar 2))) (ULAbs (ULApp (ULVar 2) (ULAbs (ULVar 3))))"
  by simp

lemma "subst_UL 0 (ULVar 1)
  (ULAbs (ULApp (ULVar 0) (ULVar 2))) =
   ULAbs (ULApp (ULVar 0) (ULVar 2))"
  by simp

lemma "subst_UL 0 (ULVar 1)
  (ULAbs (ULApp (ULVar 1) (ULVar 0))) =
   ULAbs (ULApp (ULVar 2) (ULVar 0))"
  by simp

(* Exercice 6.2.6 *)

lemma n_term_shift_UL: "n_term n t \<Longrightarrow> n_term (n + nat j) (shift_UL j i t)"
  by (induction n t arbitrary: j i rule: n_term.induct)
    (auto intro: n_term.intros n_term_ULAbs[unfolded One_nat_def])

lemma "n_term n t \<Longrightarrow> n_term n s \<Longrightarrow> j \<le> n \<Longrightarrow> n_term n (subst_UL j s t)"
proof (induction n t arbitrary: s j rule: n_term.induct)
  case (n_term_ULVar k n)
  thus ?case by (auto intro: n_term.n_term_ULVar)
next
  case (n_term_ULAbs n t)
  thus ?case
    using n_term.intros n_term_shift_UL[OF n_term_ULAbs.prems(1), where j = 1]
    by (auto
      intro: n_term_ULAbs.IH
      intro!: n_term.n_term_ULAbs[unfolded One_nat_def]
      simp: n_term_shift_UL[OF n_term_ULAbs.prems(1), where j = 1])
next
  case (n_term_ULApp n t1 t2)
  thus ?case by (simp add: n_term.intros)
qed

end
(*>*)
