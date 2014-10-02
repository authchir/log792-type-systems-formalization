theory untyped_arithmetic_expressions
imports Main
begin

datatype B_term
  = BTrue
  | BFalse
  | BIf B_term B_term B_term

inductive is_value :: "B_term \<Rightarrow> bool" where
  is_value_BTrue: "is_value BTrue" |
  is_value_BFalse: "is_value BFalse"

inductive_cases is_value_BIfD: "is_value (BIf t1 t2 t3)"


inductive eval_once :: "B_term \<Rightarrow> B_term \<Rightarrow> bool" where
  e_if_true: "eval_once (BIf BTrue t2 t3) t2" |
  e_if_false: "eval_once (BIf BFalse t2 t3) t3" |
  e_if: "eval_once t1 t1' \<Longrightarrow> eval_once (BIf t1 t2 t3) (BIf t1' t2 t3)"

inductive_cases eval_once_BTrueD: "eval_once BTrue t"
inductive_cases eval_once_BFalseD: "eval_once BFalse t"


inductive eval :: "B_term \<Rightarrow> B_term \<Rightarrow> bool" where
  e_once: "eval_once t t' \<Longrightarrow> eval t t'" |
  e_self: "eval t t" |
  e_transitive: "eval t t' \<Longrightarrow> eval t' t'' \<Longrightarrow> eval t t''"

inductive eval' :: "B_term \<Rightarrow> B_term \<Rightarrow> bool" where
  e_base': "eval' t t" |
  e_step': "eval_once t t' \<Longrightarrow> eval' t' t'' \<Longrightarrow> eval' t t''"

lemma e_once': "eval_once t t' \<Longrightarrow> eval' t t'"
  by (simp add: e_base' e_step')

lemma e_transitive': "eval' t t' \<Longrightarrow> eval' t' t'' \<Longrightarrow> eval' t t''"
  using assms proof (induction t t' arbitrary: t'' rule: eval'.induct)
    case (e_base' t t'') thus ?case .
  next
    case (e_step' t t' t'' t''')
    thus ?case
      using eval'.e_step' by blast
  qed

lemma eval_eq_eval': "eval = eval'"
  apply (rule ext)+
  apply (rule iffI)
   apply (rename_tac t t')
   apply (erule eval.induct)
      apply (erule e_once')
    apply (rule e_base')
   apply (erule e_transitive')
   apply assumption
  apply (erule eval'.induct)
   apply (rule e_self)
  using e_once e_transitive by blast

definition is_normal_form :: "B_term \<Rightarrow> bool" where
  "is_normal_form t \<longleftrightarrow> (\<forall>t'. \<not> eval_once t t')"

lemma
  assumes
    s: "s = BIf BTrue BFalse BFalse" and
    t: "t = BIf s BTrue BTrue" and
    u: "u = BIf BFalse BTrue BTrue"
  shows "eval_once (BIf t BFalse BFalse) (BIf u BFalse BFalse)"
proof -
  have "eval_once s BFalse"
    unfolding s by (rule e_if_true)
  hence "eval_once t u"
    unfolding t u by (rule e_if)
  thus ?thesis
    by (rule e_if)
qed

lemma not_eval_once_BTrue: "\<not> eval_once BTrue t"
  by (blast dest: eval_once_BTrueD)

lemma not_eval_once_BFalse: "\<not> eval_once BFalse t"
  by (blast dest: eval_once_BFalseD)

(* Theorem 3.5.4 *)

theorem eval_single_determinacy:
  fixes t t' t'' :: B_term
  shows "eval_once t t' \<Longrightarrow> eval_once t t'' \<Longrightarrow> t' = t''"
proof (induction t t' arbitrary: t'' rule: eval_once.induct)
  case (e_if_true t1 t2)
  thus ?case by (auto dest: eval_once_BTrueD elim: eval_once.cases)
next
  case (e_if_false t1 t2)
  thus ?case by (auto simp: not_eval_once_BTrue elim: eval_once.cases)
next
  case (e_if t1 t1' t2 t3)
  show ?case
    apply (rule eval_once.cases[OF e_if.prems])
    using e_if.hyps by (auto dest: eval_once_BTrueD eval_once_BFalseD e_if.IH)
qed


(* Theorem 3.5.7 *)

theorem value_imp_normal_form:
  fixes t :: B_term
  shows "is_value t \<Longrightarrow> is_normal_form t"
  by (auto simp: is_normal_form_def elim: is_value.cases dest: eval_once_BTrueD eval_once_BFalseD)


(* Theorem 3.5.8 *)

theorem normal_form_imp_value:
  fixes t :: B_term
  shows "is_normal_form t \<Longrightarrow> is_value t"
proof (rule ccontr, induction t rule: B_term.induct)
  case BTrue
  thus ?case by (simp add: is_value_BTrue)
next
  case BFalse
  thus ?case by (simp add: is_value_BFalse)
next
  case (BIf t1 t2 t3)
  thus ?case by (metis e_if e_if_false e_if_true is_normal_form_def is_value.cases)
qed


(* Theorem 3.5.11 *)

corollary uniqueness_of_normal_form:
  fixes t u u' :: B_term
  assumes
    "eval t u" and
    "eval t u'" and
    "is_normal_form u" and
    "is_normal_form u'"
  shows "u = u'"
using assms
unfolding eval_eq_eval'
proof (induction t u rule: eval'.induct)
  case (e_base' t)
  thus ?case
    by (metis eval'.simps is_normal_form_def)
next
  case (e_step' t t' t'')
  thus ?case
    by (metis eval'.cases is_normal_form_def eval_single_determinacy)
qed

primrec size_B :: "B_term \<Rightarrow> nat" where
  "size_B BTrue = 1" |
  "size_B BFalse = 1" |
  "size_B (BIf t1 t2 t3) = size_B t1 + size_B t2 + size_B t3"

lemma size_B_nz[simp]: "size_B t \<noteq> 0"
  by (induct t) auto

lemma eval_once_size_B:
  assumes "eval_once t t'"
  shows "size_B t > size_B t'"
using assms
proof (induction rule: eval_once.induct)
  case e_if_true thus ?case by simp
next
  case e_if_false thus ?case by simp
next
  case e_if thus ?case by simp
qed


thm less_induct
thm Nat.measure_induct_rule

theorem "\<exists>t'. eval t t' \<and> is_normal_form t'"
  unfolding eval_eq_eval'
  apply (induct rule: measure_induct_rule[of size_B])
  apply (rename_tac t)
  apply (case_tac "is_normal_form t")
  apply (rule_tac x = t in exI)
  apply (rule conjI)
  apply (rule e_base')
  apply assumption
  apply (subst (asm) (2) is_normal_form_def)
  apply simp
  apply (erule exE)
  using e_step' eval_once_size_B by blast

find_theorems "\<not> (\<forall>x. _)"


theorem "\<exists>t'. eval t t' \<and> is_normal_form t'"
proof (induction t)
  case BTrue
  thus ?case using e_self is_value_BTrue value_imp_normal_form by auto
next
  case BFalse
  thus ?case using e_self is_value_BFalse value_imp_normal_form by auto
next
  case (BIf t1 t2 t3)
  thus ?case
  apply (cases t1)
    using e_if_true e_once e_transitive apply blast
   using e_if_false e_once e_transitive apply blast
   apply hypsubst
   apply auto
qed


end
