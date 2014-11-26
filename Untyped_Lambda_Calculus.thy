(*<*)
theory Untyped_Lambda_Calculus
imports Main
begin
(*>*)

chapter {* Untyped Lambda Calculus *}

section {* Basics *}

section {* Programming in the Lambda-Calculus *}

section {* Formalities *}

subsection {* Syntax *}

datatype ulterm
  = ULVar nat
  | ULAbs ulterm
  | ULApp ulterm ulterm

text {* Definition 6.1.2 *}

inductive n_term :: "nat \<Rightarrow> ulterm \<Rightarrow> bool" where
  n_term_ULVar: "0 \<le> k \<Longrightarrow> k < n \<Longrightarrow> n_term n (ULVar k)" |
  n_term_ULAbs: "n_term n t \<Longrightarrow> n > 0 \<Longrightarrow> n_term (n - 1) (ULAbs t)" |
  n_term_ULApp: "n_term n t1 \<Longrightarrow> n_term n t2 \<Longrightarrow> n_term n (ULApp t1 t2)"

text {* Definition 6.2.1 *}

primrec shiftUL :: "int \<Rightarrow> nat \<Rightarrow> ulterm \<Rightarrow> ulterm" where
  "shiftUL d c (ULVar k) = ULVar (if k < c then k else nat (int k + d))" |
  "shiftUL d c (ULAbs t) = ULAbs (shiftUL d (Suc c) t)" |
  "shiftUL d c (ULApp t1 t2) = ULApp (shiftUL d c t1) (shiftUL d c t2)"

text {* Exercice 6.2.2 *}

lemma "shiftUL 2 0 (ULAbs (ULAbs (ULApp (ULVar 1) (ULApp (ULVar 0) (ULVar 2))))) =
  ULAbs (ULAbs (ULApp (ULVar 1) (ULApp (ULVar 0) (ULVar 4))))"
  by simp

lemma "shiftUL 2 0 (ULAbs (ULApp (ULVar 0) (ULApp (ULVar 1) (ULAbs (ULApp (ULVar 0) (ULApp (ULVar 1) (ULVar 2))))))) =
  ULAbs (ULApp (ULVar 0) (ULApp (ULVar 3) (ULAbs (ULApp (ULVar 0) (ULApp (ULVar 1) (ULVar 4))))))"
  by simp

text {* Exercice 6.2.3 *}

lemma "n_term n t \<Longrightarrow> n_term (n + nat d) (shiftUL d c t)"
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

text {* Definition 6.2.4 *}

primrec substUL :: "nat \<Rightarrow> ulterm \<Rightarrow> ulterm \<Rightarrow> ulterm" where
  "substUL j s (ULVar k) = (if k = j then s else ULVar k)" |
  "substUL j s (ULAbs t) = ULAbs (substUL (Suc j) (shiftUL 1 0 s) t)" |
  "substUL j s (ULApp t1 t2) = ULApp (substUL j s t1) (substUL j s t2)"

text {* Exercice 6.2.5 *}

lemma "substUL 0 (ULVar 1) (ULApp (ULVar 0) (ULAbs (ULAbs (ULVar 2)))) =
  ULApp (ULVar 1) (ULAbs (ULAbs (ULVar 3)))"
  by simp

lemma "substUL 0 (ULApp (ULVar 1) (ULAbs (ULVar 2))) (ULApp (ULVar 0) (ULAbs (ULVar 1))) =
  ULApp (ULApp (ULVar 1) (ULAbs (ULVar 2))) (ULAbs (ULApp (ULVar 2) (ULAbs (ULVar 3))))"
  by simp

lemma "substUL 0 (ULVar 1) (ULAbs (ULApp (ULVar 0) (ULVar 2))) = ULAbs (ULApp (ULVar 0) (ULVar 2))"
  by simp

lemma "substUL 0 (ULVar 1) (ULAbs (ULApp (ULVar 1) (ULVar 0))) = ULAbs (ULApp (ULVar 2) (ULVar 0))"
  by simp

text {* Exercice 6.2.6 *}

lemma n_term_shiftUL: "n_term n t \<Longrightarrow> n_term (n + nat j) (shiftUL j i t)"
  by (induction n t arbitrary: j i rule: n_term.induct)
    (auto intro: n_term.intros n_term_ULAbs[unfolded One_nat_def])

lemma "n_term n t \<Longrightarrow> n_term n s \<Longrightarrow> j \<le> n \<Longrightarrow> n_term n (substUL j s t)"
proof (induction n t arbitrary: s j rule: n_term.induct)
  case (n_term_ULVar k n)
  thus ?case by (auto intro: n_term.n_term_ULVar)
next
  case (n_term_ULAbs n t)
  thus ?case
    using n_term.intros n_term_shiftUL[OF n_term_ULAbs.prems(1), where j = 1]
    by (auto
      intro: n_term_ULAbs.IH
      intro!: n_term.n_term_ULAbs[unfolded One_nat_def]
      simp: n_term_shiftUL[OF n_term_ULAbs.prems(1), where j = 1])
next
  case (n_term_ULApp n t1 t2)
  thus ?case by (simp add: n_term.intros)
qed

text {* Single step evaluation *}

subsection {* Operational Semantics *}

inductive is_valueUL :: "ulterm \<Rightarrow> bool" where
  "is_valueUL (ULAbs t)"

inductive eval_onceUL :: "ulterm \<Rightarrow> ulterm \<Rightarrow> bool" where
  eval_once_ULApp1: "eval_onceUL t1 t1' \<Longrightarrow> eval_onceUL (ULApp t1 t2) (ULApp t1' t2)" |
  eval_once_ULApp2: "is_valueUL v1 \<Longrightarrow> eval_onceUL t2 t2' \<Longrightarrow> eval_onceUL (ULApp v1 t2) (ULApp v1 t2')" |
  eval_once_ULApp_ULAbs: "is_valueUL v2 \<Longrightarrow> eval_onceUL (ULApp (ULAbs t12) v2) (shiftUL (-1) 0 (substUL 0 (shiftUL 1 0 v2) t12))"

text {* Theorem 3.5.4 for Untyped Lambda Calculus *}

theorem eval_onceUL_right_unique:
  "eval_onceUL t t' \<Longrightarrow> eval_onceUL t t'' \<Longrightarrow> t' = t''"
proof (induction t t' arbitrary: t'' rule: eval_onceUL.induct)
  case (eval_once_ULApp1 t1 t1' t2)
  from eval_once_ULApp1.hyps eval_once_ULApp1.prems show ?case
    by (auto elim: eval_onceUL.cases is_valueUL.cases intro: eval_once_ULApp1.IH)
next
  case (eval_once_ULApp2 t1 t2 t2')
  from eval_once_ULApp2.hyps eval_once_ULApp2.prems show ?case
    by (auto elim: eval_onceUL.cases is_valueUL.cases intro: eval_once_ULApp2.IH)
next
  case (eval_once_ULApp_ULAbs v2 t12)
  thus ?case by (auto elim: eval_onceUL.cases simp: is_valueUL.simps)
qed

text {* Definition 3.5.6 for Untyped Lambda Calculus *}

definition is_normal_formUL :: "ulterm \<Rightarrow> bool" where
  "is_normal_formUL t \<longleftrightarrow> (\<forall>t'. \<not> eval_onceUL t t')"

text {* Theorem 3.5.7 for Untyped Lambda Calculus *}

theorem value_imp_normal_form: "is_valueUL t \<Longrightarrow> is_normal_formUL t"
  by (auto elim: is_valueUL.cases eval_onceUL.cases simp: is_normal_formUL_def)

text {* Theorem 3.5.8 does not hold for Untyped Lambda calculus *}

theorem normal_form_does_not_imp_value:
  "\<exists>t. is_normal_formUL t \<and> \<not> is_valueUL t" (is "\<exists>t. ?P t")
proof
  have a: "is_normal_formUL (ULVar 0)"
    by (auto simp: is_normal_formUL_def elim: eval_onceUL.cases)
  have b: "\<not> is_valueUL (ULVar 0)"
    by (auto simp: is_normal_formUL_def elim: is_valueUL.cases)
  from a b show "?P (ULVar 0)" by simp
qed

text {* Multistep evaluation *}

inductive eval :: "ulterm \<Rightarrow> ulterm \<Rightarrow> bool" where
  eval_base: "eval t t" |
  eval_step: "eval_onceUL t t' \<Longrightarrow> eval t' t'' \<Longrightarrow> eval t t''"

text {* Corollary 3.5.11 for Untyped Lambda Calculus *}

corollary uniqueness_of_normal_form:
  assumes
    "eval t u" and
    "eval t u'" and
    "is_normal_formUL u" and
    "is_normal_formUL u'"
  shows "u = u'"
using assms
proof (induction t u rule: eval.induct)
  case (eval_base t)
  thus ?case by (metis eval.simps is_normal_formUL_def)
next
  case (eval_step t1 t2 t3)
  thus ?case by (metis eval.cases is_normal_formUL_def eval_onceUL_right_unique)
qed

(* Theorem 3.5.12 does not hold for Untyped Lambda calculus *)

lemma eval_onceUL_ULVarD: "eval_onceUL (ULVar x) t \<Longrightarrow> P"
  by (induction "ULVar x" t rule: eval_onceUL.induct)

lemma eval_onceUL_ULAbsD: "eval_onceUL (ULAbs x) t \<Longrightarrow> P"
  by (induction "ULAbs x" t rule: eval_onceUL.induct)

theorem eval_does_not_always_terminate:
  "\<exists>t. \<forall>t'. eval t t' \<longrightarrow> \<not> is_normal_formUL t'" (is "\<exists>t. \<forall>t'. ?P t t'")
proof
  let ?\<omega> = "ULAbs (ULApp (ULVar 0) (ULVar 0))"
  let ?\<Omega> = "ULApp ?\<omega> ?\<omega>"
  { fix t
    have "eval_onceUL ?\<Omega> t \<Longrightarrow> ?\<Omega> = t"
      by (induction ?\<Omega> t rule: eval_onceUL.induct) (auto elim: eval_onceUL_ULAbsD)
  } note eval_onceUL_\<Omega> = this
  { fix t
    have eval_\<Omega>: "eval ?\<Omega> t \<Longrightarrow> ?\<Omega> = t"
      by (induction ?\<Omega> t rule: eval.induct) (blast dest: eval_onceUL_\<Omega>)+
  } note eval_\<Omega> = this
  show "\<forall>t'. ?P ?\<Omega> t'"
    by (auto
      simp: is_normal_formUL_def
      intro: eval_once_ULApp_ULAbs is_valueUL.intros
      dest!: eval_\<Omega>)
qed

end
