theory untyped_arithmetic_expressions
imports Main
begin

datatype B_term
  = BTrue
  | BFalse
  | BIf B_term B_term B_term


(* Definition 3.3.1 *)

primrec consts_B :: "B_term \<Rightarrow> B_term set" where
  "consts_B BTrue = {BTrue}" |
  "consts_B BFalse = {BFalse}" |
  "consts_B (BIf t1 t2 t3) = consts_B t1 \<union> consts_B t2 \<union> consts_B t3"


(* Definition 3.3.2 *)

primrec size_B :: "B_term \<Rightarrow> nat" where
  "size_B BTrue = 1" |
  "size_B BFalse = 1" |
  "size_B (BIf t1 t2 t3) = size_B t1 + size_B t2 + size_B t3"

primrec depth_B :: "B_term \<Rightarrow> nat" where
  "depth_B BTrue = 1" |
  "depth_B BFalse = 1" |
  "depth_B (BIf t1 t2 t3) = 1 + max (depth_B t1) (max (depth_B t2) (depth_B t3))"


(* Util *)

lemma card_union_leq_sum_card: "card (A \<union> B) \<le> card A + card B"
  by (cases "finite A \<and> finite B") (simp only: card_Un_Int, auto)

(* Lemma 3.3.3 *)

lemma "card (consts_B t) \<le> size_B t"
proof (induction t)
  case BTrue
  show ?case by simp
next
  case BFalse
  show ?case by simp
next
  case (BIf t1 t2 t3)
  show ?case
  proof -
    let ?t1 = "consts_B t1"
    let ?t2 = "consts_B t2"
    let ?t3 = "consts_B t3"
    have "card (?t1 \<union> ?t2 \<union> ?t3) \<le> card ?t1 + card ?t2 + card ?t3"
      by (smt card_union_leq_sum_card add_le_imp_le_right le_antisym le_trans nat_le_linear)
    also have "\<dots> \<le> size_B t1 + size_B t2 + size_B t3"
      using BIf.IH by simp
    finally show ?thesis by simp
  qed
qed

(* Definitions: Booleans *)

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
proof (induction t t' arbitrary: t'' rule: eval'.induct)
  case (e_base' t t'') thus ?case .
next
  case (e_step' t t' t'' t''')
  thus ?case using eval'.e_step' by blast
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


(* Example of definition 3.5.3 *)

lemma
  assumes
    s: "s = BIf BTrue BFalse BFalse" and
    t: "t = BIf s BTrue BTrue" and
    u: "u = BIf BFalse BTrue BTrue"
  shows "eval_once (BIf t BFalse BFalse) (BIf u BFalse BFalse)"
proof -
  have "eval_once s BFalse" unfolding s by (rule e_if_true)
  hence "eval_once t u" unfolding t u by (rule e_if)
  thus ?thesis by (rule e_if)
qed


(* Theorem 3.5.4 *)

theorem eval_single_determinacy:
  fixes t t' t'' :: B_term
  shows "eval_once t t' \<Longrightarrow> eval_once t t'' \<Longrightarrow> t' = t''"
proof (induction t t' arbitrary: t'' rule: eval_once.induct)
  case (e_if_true t1 t2)
  thus ?case by (auto elim: eval_once.cases)
next
  case (e_if_false t1 t2)
  thus ?case by (auto elim: eval_once.cases)
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


(* Corollary 3.5.11 *)

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
  thus ?case by (metis eval'.simps is_normal_form_def)
next
  case (e_step' t t' t'')
  thus ?case by (metis eval'.cases is_normal_form_def eval_single_determinacy)
qed


(* Util *)

lemma eval_once_size_B:
  assumes "eval_once t t'"
  shows "size_B t > size_B t'"
using assms
proof (induction rule: eval_once.induct)
  case e_if_true
  thus ?case by simp
next
  case e_if_false
  thus ?case by simp
next
  case e_if
  thus ?case by simp
qed


(* Theorem 3.5.12 *)

theorem eval_always_terminate:
  "\<exists>t'. eval t t' \<and> is_normal_form t'"
unfolding eval_eq_eval'
proof (induction rule: measure_induct_rule[of size_B])
  case (less t)
  show ?case
    apply (case_tac "is_normal_form t")
    using e_base' apply blast
    using e_step' is_normal_form_def eval_once_size_B less.IH by blast
qed


(* Definitions: Arithmetic Expressions *)

datatype NBTerm
  = NBTrue
  | NBFalse
  | NBIf NBTerm NBTerm NBTerm
  | NBZero
  | NBSucc NBTerm
  | NBPred NBTerm
  | NBIs_zero NBTerm

inductive is_numeric_value_NB :: "NBTerm \<Rightarrow> bool" where
  is_numeric_value_NBZero: "is_numeric_value_NB NBZero" |
  is_numeric_value_NBSucc: "is_numeric_value_NB nv \<Longrightarrow> is_numeric_value_NB (NBSucc nv)"

inductive is_value_NB :: "NBTerm \<Rightarrow> bool" where
  is_value_NBTrue: "is_value_NB NBTrue" |
  is_value_NBFalse: "is_value_NB NBFalse" |
  is_value_NB_numeric_value: "is_numeric_value_NB nv \<Longrightarrow> is_value_NB nv"

inductive eval_once_NB :: "NBTerm \<Rightarrow> NBTerm \<Rightarrow> bool" where
  eval_once_NBIf_NBTrue: "eval_once_NB (NBIf NBTrue t2 t3) t2" |
  eval_once_NBIf_NBFalse: "eval_once_NB (NBIf NBFalse t2 t3) t3" |
  eval_once_NBIf: "eval_once_NB t1 t1' \<Longrightarrow> eval_once_NB (NBIf t1 t2 t3) (NBIf t1' t2 t3)" |
  eval_once_NBSucc: "eval_once_NB t1 t1' \<Longrightarrow> eval_once_NB (NBSucc t1) (NBSucc t1')" |
  eval_once_NBPred_NBZero: "eval_once_NB (NBPred NBZero) NBZero" |
  eval_once_NBPred_NBSucc: "is_numeric_value_NB nv1 \<Longrightarrow> eval_once_NB (NBPred (NBSucc nv1)) nv1" |
  eval_once_NBPred: "eval_once_NB t1 t1' \<Longrightarrow> eval_once_NB (NBPred t1) (NBPred t1')" |
  eval_once_NBIs_zero_NBZero: "eval_once_NB (NBIs_zero NBZero) NBTrue" |
  eval_once_NBIs_zero_NBSucc: "is_numeric_value_NB nv1 \<Longrightarrow> eval_once_NB (NBIs_zero (NBSucc nv1)) NBFalse" |
  eval_once_NBIs_zero: "eval_once_NB t1 t1' \<Longrightarrow> eval_once_NB (NBIs_zero t1) (NBIs_zero t1')"

inductive_cases eval_once_NBTrueD: "eval_once_NB NBTrue t"
inductive_cases eval_once_NBFalseD: "eval_once_NB NBFalse t"
inductive_cases eval_once_NBZeroD: "eval_once_NB NBZero t"

lemma not_eval_once_numeric_value: "is_numeric_value_NB nv \<Longrightarrow> eval_once_NB nv t \<Longrightarrow> P"
proof (induction nv arbitrary: t rule: is_numeric_value_NB.induct)
  case is_numeric_value_NBZero
  thus ?case by (auto elim: eval_once_NB.cases)
next
  case is_numeric_value_NBSucc
  show ?case
    by (auto 
      intro: is_numeric_value_NBSucc.prems[THEN eval_once_NB.cases]
      elim: is_numeric_value_NBSucc.IH)
qed


(* Theorem 3.5.4 for Arithmetic Expressions *)

theorem eval_once_NB:
  fixes t t' t'' :: NBTerm
  shows "eval_once_NB t t' \<Longrightarrow> eval_once_NB t t'' \<Longrightarrow> t' = t''"
proof (induction t t' arbitrary: t'' rule: eval_once_NB.induct)
  case (eval_once_NBIf_NBTrue t1 t2)
  thus ?case by (auto elim: eval_once_NB.cases)
next
  case (eval_once_NBIf_NBFalse t1 t2)
  thus ?case by (auto elim: eval_once_NB.cases)
next
  case (eval_once_NBIf t1 t1' t2 t3)
  from eval_once_NBIf.prems eval_once_NBIf.hyps show ?case
    by (auto
      intro: eval_once_NB.cases
      dest: eval_once_NBTrueD eval_once_NBFalseD eval_once_NBIf.IH)
next
  case (eval_once_NBSucc t1 t2)
  from eval_once_NBSucc.prems eval_once_NBSucc.IH show ?case
    by (auto elim: eval_once_NB.cases)
next
  case eval_once_NBPred_NBZero
  thus ?case by (auto intro: eval_once_NB.cases dest: eval_once_NBZeroD)
next
  case (eval_once_NBPred_NBSucc nv1)
  show ?case
    apply (rule eval_once_NBPred_NBSucc.prems[THEN eval_once_NB.cases])
    using eval_once_NBPred_NBSucc.hyps
    by (auto elim: is_numeric_value_NBSucc not_eval_once_numeric_value[rotated])
next
  case (eval_once_NBPred t1 t2)
  show ?case
    apply (rule eval_once_NBPred.prems[THEN eval_once_NB.cases])
    using eval_once_NBPred.hyps is_numeric_value_NBZero
    by (auto intro: eval_once_NBPred.IH dest: not_eval_once_numeric_value is_numeric_value_NBSucc)
next
  case eval_once_NBIs_zero_NBZero
  thus ?case
    by (auto intro: eval_once_NB.cases dest: eval_once_NBZeroD)
next
  case (eval_once_NBIs_zero_NBSucc nv)
  thus ?case
    by (auto intro: eval_once_NB.cases not_eval_once_numeric_value dest: is_numeric_value_NBSucc)
next
  case (eval_once_NBIs_zero t1 t2)
  show ?case
    apply (rule eval_once_NBIs_zero.prems[THEN eval_once_NB.cases])
    using eval_once_NBIs_zero.hyps
    by (auto
      intro: eval_once_NBZeroD eval_once_NBIs_zero.IH
      elim: not_eval_once_numeric_value[rotated] is_numeric_value_NBSucc)
qed

end
