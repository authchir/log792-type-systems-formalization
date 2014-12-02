(*<*)
theory Untyped_Lambda_Calculus
imports Nameless_Representation_Of_Terms
begin
(*>*)

chapter {* Untyped Lambda Calculus *}

inductive is_valueUL :: "ulterm \<Rightarrow> bool" where
  "is_valueUL (ULAbs t)"

inductive eval_onceUL :: "ulterm \<Rightarrow> ulterm \<Rightarrow> bool" where
  eval_once_ULApp1: "eval_onceUL t1 t1' \<Longrightarrow> eval_onceUL (ULApp t1 t2) (ULApp t1' t2)" |
  eval_once_ULApp2: "is_valueUL v1 \<Longrightarrow> eval_onceUL t2 t2' \<Longrightarrow> eval_onceUL (ULApp v1 t2) (ULApp v1 t2')" |
  eval_once_ULApp_ULAbs: "is_valueUL v2 \<Longrightarrow> eval_onceUL (ULApp (ULAbs t12) v2) (shift_UL (-1) 0 (subst_UL 0 (shift_UL 1 0 v2) t12))"

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
  { fix t (* provide it as helper lemmas *)
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
