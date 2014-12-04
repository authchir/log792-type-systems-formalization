(*<*)
theory Untyped_Lambda_Calculus
imports Nameless_Representation_Of_Terms
begin
(*>*)

section {* Untyped Lambda Calculus *}

text {*
The untyped lambda calculus is the first core calculus we formalize. It directly imports the theory
on the nameless representation of terms (section \ref{sec:nameless-rep-of-terms}), which formalizes
the representation used for the syntax of the language.

We now turn to the semantics by, first, defining that only function abstractions are considered as
value:
*}

inductive is_value_UL :: "ulterm \<Rightarrow> bool" where
  "is_value_UL (ULAbs t)"

text {*
One may wonder why variables are not considered as values. In the lambda calculus, variables are a
way to refer to a specific of a function abstraction. Since function abstractions are values, we do
not need to consider their variable. The only ones we could consider as values are the unbounded
variables, i.e. variables refering to non-existing function abstractions. In the following examples,
every occurence of @{term w} is unbounded:

\begin{displaymath}
  w \qquad (\lambda x. x) w \qquad (\lambda x. \lambda y. \lambda z. w \ x \ y \ z)
\end{displaymath}

There is no concensus on how the semantic should handle such situations. By excluding them from the
set of values, the semantics described in the book defines that such term are meaningless. This
decision is consistent with many programming languages where the use of an undefined identifier
leads to an error either at compile-time or at run-time.

The single-step evaluation relation is defined, in the book, with the following inference rules
where \texttt{[x $\mapsto$ s] t} is the substitution of variable \texttt{x} by \texttt{s} in
\texttt{t}:

\begin{verbatim}
   t1 --> t1'
----------------
t1 t2 --> t1' t2

   t2 --> t2'
----------------
v1 t2 --> v1 t2'

(%x. t12) v2 --> [x |-> v2] t12
\end{verbatim}

We translate these rules with the following inductive definition:
*}

inductive eval1_UL :: "ulterm \<Rightarrow> ulterm \<Rightarrow> bool" where
  eval1_ULApp1: "eval1_UL t1 t1' \<Longrightarrow> eval1_UL (ULApp t1 t2) (ULApp t1' t2)" |
  eval1_ULApp2: "is_value_UL v1 \<Longrightarrow> eval1_UL t2 t2' \<Longrightarrow>
    eval1_UL (ULApp v1 t2) (ULApp v1 t2')" |
  eval1_ULApp_ULAbs: "is_value_UL v2 \<Longrightarrow>
    eval1_UL (ULApp (ULAbs t12) v2)
      (shift_UL (-1) 0 (subst_UL 0 (shift_UL 1 0 v2) t12))"

text {*
Appart from the explicit assumption on the nature of @{term v1}, the only difference is the
substitution in the third rule. This is the reason that pushed use to formalized the nameless
representation of terms in the first place. The book uses a high level definition of substitution
where name clashes are not considered. We replace this higher level operation by our concrete
substitution operation on "de Bruijn indices". We begin by shifting up by on the concrete argument
because, conceptually, it \emph{enters} the function abstraction. We then perform the proper
substitution of the function's variable , i.e. of indice zero. Finally, we shift down every variable
of the resulting body to, conceptually, remove the function abstraction we just applied.

The multi-step evaluation relation and the normal form definitions have the well-known shape:
*}

inductive eval_UL :: "ulterm \<Rightarrow> ulterm \<Rightarrow> bool" where
  eval_UL_base: "eval_UL t t" |
  eval_UL_step: "eval1_UL t t' \<Longrightarrow> eval_UL t' t'' \<Longrightarrow> eval_UL t t''"

definition is_normal_form_UL :: "ulterm \<Rightarrow> bool" where
  "is_normal_form_UL t \<longleftrightarrow> (\<forall>t'. \<not> eval1_UL t t')"

text {*
In the book, this chapter consists mainly of the presentation of the lambda-calculus, of which we
gave a short introduction in the background section (section \ref{sec:background-lambda-calculus}),
and does not contains meaningfull theorems. Nevertheless, we decided to reprove, or disprove, the
theorems introduced in the section on the arithmetic expression language
(\ref{sec:arith-expr-langauge}).
*}

(* Theorem 3.5.4 for Untyped Lambda Calculus *)

text {*
The determinacy of the single-step evaluation still holds:
*}

theorem determinacy_of_one_step_evaluation:
  "eval1_UL t t' \<Longrightarrow> eval1_UL t t'' \<Longrightarrow> t' = t''"
proof (induction t t' arbitrary: t'' rule: eval1_UL.induct)
  case (eval1_ULApp1 t1 t1' t2)
  from eval1_ULApp1.hyps eval1_ULApp1.prems show ?case
    by (auto elim: eval1_UL.cases is_value_UL.cases intro: eval1_ULApp1.IH)
next
  case (eval1_ULApp2 t1 t2 t2')
  from eval1_ULApp2.hyps eval1_ULApp2.prems show ?case
    by (auto elim: eval1_UL.cases is_value_UL.cases intro: eval1_ULApp2.IH)
next
  case (eval1_ULApp_ULAbs v2 t12)
  thus ?case by (auto elim: eval1_UL.cases simp: is_value_UL.simps)
qed

(* Definition 3.5.6 for Untyped Lambda Calculus *)

text {*
Every value is in normal form:
*}

(* Theorem 3.5.7 for Untyped Lambda Calculus *)

theorem value_imp_normal_form:
  "is_value_UL t \<Longrightarrow> is_normal_form_UL t"
by (auto elim: is_value_UL.cases eval1_UL.cases simp: is_normal_form_UL_def)

(* Theorem 3.5.8 does not hold for Untyped Lambda calculus *)
text {*
Meanwhile, the converse of the preceding theorem is not true since variables are in normal form but
are not values:
*}

theorem normal_form_does_not_imp_value:
  "\<exists>t. is_normal_form_UL t \<and> \<not> is_value_UL t" (is "\<exists>t. ?P t")
proof
  have a: "\<And>n. is_normal_form_UL (ULVar n)"
    by (auto simp: is_normal_form_UL_def elim: eval1_UL.cases)
  have b: "\<And>n. \<not> is_value_UL (ULVar n)"
    by (auto simp: is_normal_form_UL_def elim: is_value_UL.cases)
  from a b show "\<And>n. ?P (ULVar n)" by simp
qed

(* Corollary 3.5.11 for Untyped Lambda Calculus *)

text {*
The uniqueness of normal form still holds:
*}

corollary uniqueness_of_normal_form:
  "eval_UL t u \<Longrightarrow> eval_UL t u' \<Longrightarrow> is_normal_form_UL u \<Longrightarrow> is_normal_form_UL u' \<Longrightarrow> u = u'"
proof (induction t u rule: eval_UL.induct)
  case (eval_UL_base t)
  thus ?case by (metis eval_UL.simps is_normal_form_UL_def)
next
  case (eval_UL_step t1 t2 t3)
  thus ?case by (metis eval_UL.cases is_normal_form_UL_def determinacy_of_one_step_evaluation)
qed

(* Theorem 3.5.12 does not hold for Untyped Lambda calculus *)

text {*
This time, the evaluation relation could be non-terminating. A typical example of term whose
evaluation does not terminate is the self-application combinator (also known as $\omega$) applied to
itself (also known as $\Omega$):
*}

(*<*)
lemma eval1_UL_ULVarD: "eval1_UL (ULVar x) t \<Longrightarrow> P"
  by (induction "ULVar x" t rule: eval1_UL.induct)

lemma eval1_UL_ULAbsD: "eval1_UL (ULAbs x) t \<Longrightarrow> P"
  by (induction "ULAbs x" t rule: eval1_UL.induct)
(*>*)

definition \<omega> :: ulterm where
  "\<omega> \<equiv> ULAbs (ULApp (ULVar 0) (ULVar 0))"

definition \<Omega> :: ulterm where
  "\<Omega> \<equiv> ULApp \<omega> \<omega>"

text {*
A single step of evaluation will result in the same term:
*}

lemma eval1_UL_\<Omega>:
  "eval1_UL \<Omega> t \<Longrightarrow> \<Omega> = t"
by (induction \<Omega> t rule: eval1_UL.induct)
  (auto elim: eval1_UL_ULAbsD simp: \<omega>_def \<Omega>_def)

text {*
Since the single-step evaluation is equivalent to the identity, the multi-step evaluation relation
will loop infinitly:
*}

lemma eval_UL_\<Omega>:
  "eval_UL \<Omega> t \<Longrightarrow> \<Omega> = t"
by (induction \<Omega> t rule: eval_UL.induct) (blast dest: eval1_UL_\<Omega>)+

text {*
Based on this simple example, we can show that there exists some terms for which can not be reduce
to a normal form:
*}

theorem eval_does_not_always_terminate:
  "\<exists>t. \<forall>t'. eval_UL t t' \<longrightarrow> \<not> is_normal_form_UL t'" (is "\<exists>t. \<forall>t'. ?P t t'")
proof
  show "\<forall>t'. ?P \<Omega> t'"
    by (auto dest!: eval_UL_\<Omega>)
      (auto intro: eval1_UL.intros is_value_UL.intros simp: \<omega>_def \<Omega>_def is_normal_form_UL_def)
qed

(*<*)
end
(*>*)
