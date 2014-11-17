(*<*)
theory Untyped_Arithmetic_Expressions
imports Main
begin
(*>*)

chapter {* Untyped Arithmetic Expressions *}

text {* The language of untyped arithmetic expressions contains the boolean constants @{text true}
and @{text false}, the conditional expression @{text "if \<dots> then \<dots> else \<dots>"}, the numeric constant
@{text zero}, the arithmetic operators successor (@{text succ}) and predecessor (@{text pred}) and a
function @{text is_zero} that returns @{text true} when applied to @{text zero} and @{text false}
when applied to some other number. An arbitrary natural number $n$ can be expressed by applying the
@{text succ} operator $n$ times to @{text zero} (e.g. the number three is @{text "succ (succ (succ
zero))"}).*}

section {* Syntax *}

text {* The syntax of this language is represented by the @{term NBTerm} datatype \footnote{To
prevent name clashes with the \emph{Isabelle} constants of the same name, the types and type
constructors are prefix with @{text NB}, which stand for "Numeric and Booleans". Functions have a
use a suffix for the same purpose.}. *}

datatype NBTerm
  = NBTrue
  | NBFalse
  | NBIf NBTerm NBTerm NBTerm
  | NBZero
  | NBSucc NBTerm
  | NBPred NBTerm
  | NBIs_zero NBTerm

section {* Induction on Terms *}

(* Definition 3.3.1 *)

primrec const_NB :: "NBTerm \<Rightarrow> NBTerm set" where
  "const_NB NBTrue = {NBTrue}" |
  "const_NB NBFalse = {NBFalse}" |
  "const_NB NBZero = {NBZero}" |
  "const_NB (NBSucc t) = const_NB t" |
  "const_NB (NBPred t) = const_NB t" |
  "const_NB (NBIs_zero t) = const_NB t" |
  "const_NB (NBIf t1 t2 t3) = const_NB t1 \<union> const_NB t2 \<union> const_NB t3"

(* Definition 3.3.2 *)

primrec size_NB :: "NBTerm \<Rightarrow> nat" where
  "size_NB NBTrue = 1" |
  "size_NB NBFalse = 1" |
  "size_NB NBZero = 1" |
  "size_NB (NBSucc t) = size_NB t + 1" |
  "size_NB (NBPred t) = size_NB t + 1" |
  "size_NB (NBIs_zero t) = size_NB t + 1" |
  "size_NB (NBIf t1 t2 t3) = size_NB t1 + size_NB t2 + size_NB t3 + 1"

primrec depth_NB :: "NBTerm \<Rightarrow> nat" where
  "depth_NB NBTrue = 1" |
  "depth_NB NBFalse = 1" |
  "depth_NB NBZero = 1" |
  "depth_NB (NBSucc t) = depth_NB t + 1" |
  "depth_NB (NBPred t) = depth_NB t + 1" |
  "depth_NB (NBIs_zero t) = depth_NB t + 1" |
  "depth_NB (NBIf t1 t2 t3) = max (depth_NB t1) (max (depth_NB t2) (depth_NB t3)) + 1"

(* Lemma 3.3.3 *)

lemma card_union_leq_sum_card: "card (A \<union> B) \<le> card A + card B"
  by (cases "finite A \<and> finite B") (simp only: card_Un_Int, auto)

lemma "card (const_NB t) \<le> size_NB t"
proof (induction t)
  case NBTrue
  show ?case by simp
next
  case NBFalse
  show ?case by simp
next
  case NBZero
  show ?case by simp
next
  case (NBSucc t)
  thus ?case by (simp add: le_SucI)
next
  case (NBPred t)
  thus ?case by (simp add: le_SucI)
next
  case (NBIs_zero t)
  thus ?case by (simp add: le_SucI)
next
  case (NBIf t1 t2 t3)
  show ?case
  proof -
    let ?t1 = "const_NB t1"
    let ?t2 = "const_NB t2"
    let ?t3 = "const_NB t3"
    have "card (?t1 \<union> ?t2 \<union> ?t3) \<le> card ?t1 + card ?t2 + card ?t3"
      using card_union_leq_sum_card add_le_imp_le_right le_antisym le_trans nat_le_linear
      by (smt card_union_leq_sum_card add_le_imp_le_right le_antisym le_trans nat_le_linear)
    also have "\<dots> \<le> size_NB t1 + size_NB t2 + size_NB t3"
      using NBIf.IH by simp
    finally show ?thesis by simp
  qed
qed

(* Theorem 3.3.4 *)

theorems induct_depth = measure_induct_rule[of depth_NB]
theorems induct_size = measure_induct_rule[of size_NB]
theorems structural_induction = NBTerm.induct

section {* Semantic Styles *}

text {* Operational semantics is used exclusively in this book. [TAPL p.34] *}

section {* Evaluation *}

subsection {* Booleans *}

datatype_new BTerm
  = BTrue
  | BFalse
  | BIf BTerm BTerm BTerm

primrec size_B :: "BTerm \<Rightarrow> nat" where
  "size_B BTrue = 1" |
  "size_B BFalse = 1" |
  "size_B (BIf t1 t2 t3) = 1 + size_B t1 + size_B t2 + size_B t3"

inductive is_value :: "BTerm \<Rightarrow> bool" where
  is_value_BTrue: "is_value BTrue" |
  is_value_BFalse: "is_value BFalse"

inductive eval_once :: "BTerm \<Rightarrow> BTerm \<Rightarrow> bool" where
  e_if_true: "eval_once (BIf BTrue t2 t3) t2" |
  e_if_false: "eval_once (BIf BFalse t2 t3) t3" |
  e_if: "eval_once t1 t1' \<Longrightarrow> eval_once (BIf t1 t2 t3) (BIf t1' t2 t3)"

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

inductive_cases eval_once_BTrueE: "eval_once BTrue t"
inductive_cases eval_once_BFalseE: "eval_once BFalse t"

theorem eval_single_determinacy:
  fixes t t' t'' :: BTerm
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
    using e_if.hyps by (auto dest: eval_once_BTrueE eval_once_BFalseE e_if.IH)
qed

(* Theorem 3.5.7 *)

definition is_normal_form :: "BTerm \<Rightarrow> bool" where
  "is_normal_form t \<longleftrightarrow> (\<forall>t'. \<not> eval_once t t')"

theorem value_imp_normal_form:
  fixes t :: BTerm
  shows "is_value t \<Longrightarrow> is_normal_form t"
by (auto simp: is_normal_form_def elim: is_value.cases dest: eval_once_BTrueE eval_once_BFalseE)

(* Theorem 3.5.8 *)

theorem normal_form_imp_value:
  fixes t :: BTerm
  shows "is_normal_form t \<Longrightarrow> is_value t"
proof (rule ccontr, induction t rule: BTerm.induct)
  case BTrue
  thus ?case by (simp add: is_value_BTrue)
next
  case BFalse
  thus ?case by (simp add: is_value_BFalse)
next
  case (BIf t1 t2 t3)
  thus ?case by (metis e_if e_if_false e_if_true is_normal_form_def is_value.cases)
qed

(* Definition 3.5.9 *)

inductive eval :: "BTerm \<Rightarrow> BTerm \<Rightarrow> bool" where
  e_once: "eval_once t t' \<Longrightarrow> eval t t'" |
  e_self: "eval t t" |
  e_transitive: "eval t t' \<Longrightarrow> eval t' t'' \<Longrightarrow> eval t t''"

inductive eval' :: "BTerm \<Rightarrow> BTerm \<Rightarrow> bool" where
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

(* rewrite as an Isar proof *)
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


(* Corollary 3.5.11 *)

corollary uniqueness_of_normal_form:
  fixes t u u' :: BTerm
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
    apply (cases "is_normal_form t")
    using e_base' apply blast
    using e_step' is_normal_form_def eval_once_size_B less.IH by blast
qed

subsection {* Arithmetic Expressions *}

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

inductive eval_NB :: "NBTerm \<Rightarrow> NBTerm \<Rightarrow> bool" where
  eval_NB_base: "eval_NB t t" |
  eval_NB_step: "eval_once_NB t t' \<Longrightarrow> eval_NB t' t'' \<Longrightarrow> eval_NB t t''"

definition is_normal_form_NB :: "NBTerm \<Rightarrow> bool" where
  "is_normal_form_NB t \<longleftrightarrow> (\<forall>t'. \<not> eval_once_NB t t')"

(* Usefull lemmas *)

lemma eval_once_NB_impl_eval_NB: "eval_once_NB t t' \<Longrightarrow> eval_NB t t'"
  by (simp add: eval_NB_step eval_NB_base)

lemma eval_NB_transitive: "eval_NB t t' \<Longrightarrow> eval_NB t' t'' \<Longrightarrow> eval_NB t t''"
proof (induction t t' arbitrary: t'' rule: eval_NB.induct)
  case (eval_NB_base t t')
  thus ?case .
next
  case (eval_NB_step t1 t2 t3)
  thus ?case using eval_NB.eval_NB_step by blast
qed

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

theorem eval_once_NB_right_unique:
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
  from eval_once_NBPred.hyps eval_once_NBPred.prems show ?case
    using  is_numeric_value_NBZero
    by (auto
      intro: eval_once_NBPred.IH
      elim: eval_once_NB.cases
      dest: not_eval_once_numeric_value is_numeric_value_NBSucc)
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


(* Theorem 3.5.7 for Arithmetic Expressions *)

theorem value_imp_normal_form_NB:
  "is_value_NB t \<Longrightarrow> is_normal_form_NB t"
  by (auto
    simp: is_normal_form_NB_def
    elim: is_value_NB.cases
    dest: eval_once_NBFalseD eval_once_NBTrueD not_eval_once_numeric_value)


(* Theorem 3.5.8 does not hold for Arithmetic Expressions *)

theorem not_normal_form_imp_value_NB: "\<exists>t. is_normal_form_NB t \<and> \<not> is_value_NB t" (is "\<exists>t. ?P t")
proof
  have a: "is_normal_form_NB (NBSucc NBTrue)"
    by (auto elim: eval_once_NB.cases simp: is_normal_form_NB_def)
  have b: "\<not> is_value_NB (NBSucc NBTrue)"
    by (auto elim: is_numeric_value_NB.cases simp: is_value_NB.simps)
  from a b show "?P (NBSucc NBTrue)" by simp
qed


(* Corollary 3.5.11 for Arithmetic Expressions *)

corollary uniqueness_of_normal_form_NB:
  assumes
    "eval_NB t u" and
    "eval_NB t u'" and
    "is_normal_form_NB u" and
    "is_normal_form_NB u'"
  shows "u = u'"
using assms
proof (induction t u rule: eval_NB.induct)
  case (eval_NB_base t)
  thus ?case by (metis eval_NB.simps is_normal_form_NB_def)
next
  case (eval_NB_step t1 t2 t3)
  thus ?case by (metis eval_NB.cases is_normal_form_NB_def eval_once_NB_right_unique)
qed


(* Theorem 3.5.12 for Arithmetic Expressions *)

lemma eval_once_size_NB:
  "eval_once_NB t t' \<Longrightarrow> size_NB t > size_NB t'"
by (induction rule: eval_once_NB.induct) auto

theorem eval_NB_always_terminate:
  "\<exists>t'. eval_NB t t' \<and> is_normal_form_NB t'"
proof (induction rule: measure_induct_rule[of size_NB])
  case (less t)
  show ?case
    apply (case_tac "is_normal_form_NB t")
    using eval_NB_base apply blast
    using eval_NB_step eval_once_size_NB is_normal_form_NB_def less.IH by blast
qed

(*<*)
end
(*>*)
