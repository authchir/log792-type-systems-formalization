(* original Author: Martin Desharnais
    updated to version 2016 by Michaël Noël Divo
*)
(*<*)
theory Nameless_Representation_Of_Terms
imports Main
begin
(*>*)

section {* Nameless Representation of Terms *}
text {* \label{sec:nameless-rep-of-terms} *}

text {*
In the background section on $\lambda$-calculus (Section~\ref{sec:background-lambda-calculus}), we
presented the problem of name clashes that can arise when performing $\beta$-reduction. In its
definitions and proofs, the book only works up to $\alpha$-equivalence: assuming that the variables
would be implicitly renamed if such a name clash occurred. In a separate chapter, a different
representation of terms that avoids such problem is presented. It is described as one possible
encoding that can be used when implementing an compiler for the $\lambda$-calculus.

Even though we are not building a compiler, our computer-verified formalization requires us to
explicitly handle this problem. We chose to use this representation and, thus must also formalize
this chapter.

The idea behind this representation, known as de Bruijn indices, is to make variables reference
directly their corresponding binder, rather than referring to them by name. This is accomplished by
using an index that count the number of enclosing $\lambda$-abstractions between a variable and its
binder. Following is an example of de Bruijn indices representation for the function composition
combinator:
\begin{displaymath}
  \lambda f. \ \lambda g. \ \lambda x. \ f \ (g \ x)
    \equiv \lambda \ \lambda \ \lambda \ 2 \ (1 \ 0)
\end{displaymath}

This representation releases us from having to consider the case of variable name clashes at the
expense of being harder to read and having to maintain the correct indices when adding and removing
$\lambda$-abstractions. Using this representation, we define the syntax of the untyped lambda
calculus as follow:\footnote{The prefix \emph{ul} stands for \emph{untyped lambda-calculus}.}
*}

datatype ulterm =
  ULVar nat |
  ULAbs ulterm |
  ULApp ulterm ulterm

text {*
Using this syntax, the same example of the function composition combinator looks like this:

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

(* Definition 6.2.1 *)
(*>*)
text {*
We define a shift function serving to increase or decrease, by a fix amount @{term d}, all indices
larger than @{term c} in a term:
*}

primrec shift_UL :: "int \<Rightarrow> nat \<Rightarrow> ulterm \<Rightarrow> ulterm" where
  "shift_UL d c (ULVar k) = ULVar (if k < c then k else nat (int k + d))" |
  "shift_UL d c (ULAbs t) = ULAbs (shift_UL d (Suc c) t)" |
  "shift_UL d c (ULApp t1 t2) = ULApp (shift_UL d c t1) (shift_UL d c t2)"

text {*
In this definition, there is a possible information loss. The variables use a
natural number as index but the function allows to shift both up and down, thus the use of an
integer for the shift increment. When a variable is encountered, we first convert the index from
natural number to integer, which is always safe, perform the integer addition, which correspond to a
subtraction if @{term d} is negative, and convert the result back to natural numbers to serve as the
new index. This last operation converts negative numbers to zero. We know that this loss of
information is safe, since it makes no sense to speak of negative indices. Our @{const shift_UL}
function thus has an implicit assumption that it should not be called with a negative number larger
than the smallest free variable in the term. Following is an example of shifting up every free
variable by 2:
*}

(* Exercise 6.2.2 *)

lemma "shift_UL 2 0
  (ULAbs (ULAbs (ULApp (ULVar 1) (ULApp (ULVar 0) (ULVar 2))))) =
   ULAbs (ULAbs (ULApp (ULVar 1) (ULApp (ULVar 0) (ULVar 4))))"
  by simp

text {*
On a first reading, the previous example may seems broken: the variables @{term "ULVar 0"} and
@{term "ULVar 1"} are not incremented. This is because the shift function operates on free
variables, i.e. variables whose index refers to a non-existing $\lambda$-abstraction. Since the
binding referred by @{term "ULVar 1"} is in the term, it is not a free variable: it is bound.
*}
(*<*)

lemma "shift_UL 2 0
  (ULAbs (ULApp (ULVar 0) (ULApp (ULVar 1) (ULAbs (ULApp (ULVar 0) (ULApp (ULVar 1) (ULVar 2))))))) =
   ULAbs (ULApp (ULVar 0) (ULApp (ULVar 3) (ULAbs (ULApp (ULVar 0) (ULApp (ULVar 1) (ULVar 4))))))"
  by simp

(* Exercise 6.2.3 *)

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
We now define a substitution function that replaces every free variable with index @{term j} by
the term @{term s}:
\newpage
*}
(* Definition 6.2.4 *)

primrec subst_UL :: "nat \<Rightarrow> ulterm \<Rightarrow> ulterm \<Rightarrow> ulterm" where
  "subst_UL j s (ULVar k) = (if k = j then s else ULVar k)" |
  "subst_UL j s (ULAbs t) = ULAbs (subst_UL (Suc j) (shift_UL 1 0 s) t)" |
  "subst_UL j s (ULApp t1 t2) = ULApp (subst_UL j s t1) (subst_UL j s t2)"

(* Exercise 6.2.5 *)

text {*
Here is an example of substituting the variable 0 by the variable 1:
*}

lemma "subst_UL 0 (ULVar 1)
  (ULApp (ULVar 0) (ULAbs (ULAbs (ULVar 2)))) =
   ULApp (ULVar 1) (ULAbs (ULAbs (ULVar 3)))"
  by simp

text {*
Note that the indices are relative to their position in the term. This is why @{term "ULVar 2"} is
also substituted in the previous example: counting the number of enclosing $\lambda$-abstractions
shows us that this variable is, indeed, the same as @{term "ULVar 0"} outside the
$\lambda$-abstractions. Of course, we must maintain this invariant by incrementing variables in our
substituting term accordingly.
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

(* Exercise 6.2.6 *)

lemma n_term_shift_UL: "n_term n t \<Longrightarrow> n_term (n + nat j) (shift_UL j i t)"
  by (induction n t arbitrary: j i rule: n_term.induct)
    (auto intro: n_term.intros n_term_ULAbs[unfolded One_nat_def])

(* updated 
   changes: only Abstraction case left, other cases follow by auto
*)
lemma "n_term n t \<Longrightarrow> n_term n s \<Longrightarrow> j \<le> n \<Longrightarrow> n_term n (subst_UL j s t)"
proof (induction n t arbitrary: s j rule: n_term.induct) 
  case (n_term_ULAbs n t)
  thus ?case
   (* 
      other proof (possible with ver. 2016)
      by (smt Groups.add_ac(2) Nat.le_diff_conv2 One_nat_def Suc_leI add.right_neutral add_Suc_right 
        add_diff_inverse_nat linorder_not_less n_term.intros(2) n_term_shift_UL 
        subst_UL.simps(2) transfer_nat_int_numerals(2))
   *) 
      using n_term.intros n_term_shift_UL[OF n_term_ULAbs.prems(1), where j = 1]
      by (auto
        intro: n_term_ULAbs.IH
        intro!: n_term.n_term_ULAbs[unfolded One_nat_def]
        simp: n_term_shift_UL[OF n_term_ULAbs.prems(1), where j = 1])
    
qed (auto intro: n_term.intros)

end
(*>*)
