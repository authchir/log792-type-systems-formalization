(*<*)
theory Untyped_Lambda_Calculus
imports Nameless_Representation_Of_Terms
begin
(*>*)

section {* Untyped Lambda-Calculus *}
text {* \label{sec:untyped-lambda-calculus} *}

text {*
The untyped lambda calculus is the first core calculus we formalize. It imports the theory on the
nameless representation of terms (Section~\ref{sec:nameless-rep-of-terms}), which formalizes the
representation used for the syntax of the language. We complete the definitions by providing the
semantics and prove the determinacy of evaluation, the relation between values and normal form, the
uniqueness of normal form and the potentially non-terminating nature of evaluation.
*}

subsection {* Definitions *}

text {*
In the pure $\lambda$-calculus, only function abstractions are considered values:
*}

inductive is_value_UL :: "ulterm \<Rightarrow> bool" where
  "is_value_UL (ULAbs t)"

text {*
Variables are not part of this definition because they are a way to refer to a specific
$\lambda$-abstraction. Since abstractions are themselves values, we do not need to consider their
bound variables. The only ones we could consider as values are the free variables, i.e. variables
referring to non-existing $\lambda$-abstractions. In the following examples, every occurrence of
@{term w} is free:

\begin{displaymath}
  w \qquad (\lambda x. \ x) \ w \qquad (\lambda x. \lambda y. \lambda z. \ w \ x \ y \ z)
\end{displaymath}

There is no consensus on how the semantics should handle such situations. By excluding them from the
set of values, the semantics described in the book defines that such terms are meaningless. This
decision is consistent with many programming languages where the use of an undefined identifier
leads to an error, either at compile-time or at run-time.

The single-step evaluation relation is defined, in the book, with the following inference rules
where $[x \mapsto s] \ t$ is the replacement of variable $x$ by $s$ in $t$:
\setcounter{equation}{0}
\begin{gather}
  \inferrule {t_1 \implies t_1'}{t_1 \ t_2 \implies t_1' \ t_2} \\[0.8em]
  \inferrule {t_2 \implies t_2'}{v_1 \ t_2 \implies v_1 \ t_2'} \\[0.8em]
  \inferrule {}{(\lambda x. \ t_{12}) \ v_2 \implies [x \mapsto v_2] \ t_{12}}
\end{gather}

The first rule states that the left side of an application must be reduced first, the second rule
states that the right side of an application must be reduced second and the third rule states that
an application consists of replacing both the $\lambda$-abstraction and the argument by the
$\lambda$-abstraction's body where the substitution have been performed. We translate these rules
with the following inductive definition:
*}

inductive eval1_UL :: "ulterm \<Rightarrow> ulterm \<Rightarrow> bool" where
  eval1_ULApp1:
    "eval1_UL t1 t1' \<Longrightarrow> eval1_UL (ULApp t1 t2) (ULApp t1' t2)" |
  eval1_ULApp2:
    "is_value_UL v1 \<Longrightarrow> eval1_UL t2 t2' \<Longrightarrow> eval1_UL (ULApp v1 t2)
      (ULApp v1 t2')" |
  eval1_ULApp_ULAbs:
    "is_value_UL v2 \<Longrightarrow> eval1_UL (ULApp (ULAbs t12) v2)
      (shift_UL (-1) 0 (subst_UL 0 (shift_UL 1 0 v2) t12))"

text {*
Apart from the explicit assumption on the nature of @{term v1}, the only difference is the
substitution in the third rule. This is the reason that motivated us to formalize the nameless
representation of terms in the first place. The book uses a high level definition of substitution
where name clashes are not considered. We replace this higher level operation by our concrete
substitution operation on de Bruijn indices. We begin by shifting up by on the concrete argument
because, conceptually, it \emph{enters} the function abstraction. We then perform the proper
substitution of the function's variable, i.e. of index zero. Finally, we shift down every variable
of the resulting body to account for the removed $\lambda$-abstraction.

The multi-step evaluation relation and the normal form definitions follow the usual pattern:
*}

inductive eval_UL :: "ulterm \<Rightarrow> ulterm \<Rightarrow> bool" where
  eval_UL_base:
    "eval_UL t t" |
  eval_UL_step:
    "eval1_UL t t' \<Longrightarrow> eval_UL t' t'' \<Longrightarrow> eval_UL t t''"

definition is_normal_form_UL :: "ulterm \<Rightarrow> bool" where
  "is_normal_form_UL t \<longleftrightarrow> (\<forall>t'. \<not> eval1_UL t t')"

subsection {* Theorems *}

text {*
In the book, this chapter consists mainly of the presentation of the $\lambda$-calculus, of which we
gave a short introduction in the background section (Section~\ref{sec:background-lambda-calculus}),
and does not contains meaningful theorems. Nevertheless, we revisit the properties
introduced with the arithmetic expressions language (Section~\ref{sec:untyped-arith-expr}) and
either prove that they are still theorems or disprove them.
*}

(* Theorem 3.5.4 for Untyped Lambda Calculus *)

text {*
The determinacy of the single-step evaluation still holds:
*}

theorem eval1_UL_determinacy:
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
by (induction t u rule: eval_UL.induct)
  (metis eval_UL.cases is_normal_form_UL_def eval1_UL_determinacy)+


(* Theorem 3.5.12 does not hold for Untyped Lambda calculus *)

text {*
This time, the evaluation relation could be non-terminating. A typical example of term whose
evaluation does not terminate is the self-application combinator
($\omega \: \equiv \: \lambda x. \ x \ x$) applied to itself, resulting in a term called $\Omega$:
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
will loop infinitely (e.g. $\Omega \to \Omega \to \dots$):
*}

lemma eval_UL_\<Omega>:
  "eval_UL \<Omega> t \<Longrightarrow> \<Omega> = t"
by (induction \<Omega> t rule: eval_UL.induct) (blast dest: eval1_UL_\<Omega>)+

lemma
  "eval_UL \<Omega> \<Omega>"
by (rule eval_UL.intros)

text {*
Based on this simple example, we can show that there exists some terms which cannot be reduce to a
normal form:
*}

theorem eval_does_not_always_terminate:
  "\<exists>t. \<forall>t'. eval_UL t t' \<longrightarrow> \<not> is_normal_form_UL t'" (is "\<exists>t. \<forall>t'. ?P t t'")
proof
  show "\<forall>t'. ?P \<Omega> t'"
    by (auto dest!: eval_UL_\<Omega>)
      (auto
        intro: eval1_UL.intros is_value_UL.intros
        simp: \<omega>_def \<Omega>_def is_normal_form_UL_def)
qed

(*<*)
end
(*>*)
