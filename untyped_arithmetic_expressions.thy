theory untyped_arithmetic_expressions
imports Main
begin

datatype B_term
  = BTrue
  | BFalse
  | BIf B_term B_term B_term

inductive is_value :: "B_term \<Rightarrow> bool" where
  "is_value BTrue" |
  "is_value BFalse"

thm is_value.induct
thm is_value.intros
thm is_value.cases
thm is_value.simps

inductive_cases is_value_BIfD: "is_value (BIf t1 t2 t3)"

inductive eval_once :: "B_term \<Rightarrow> B_term \<Rightarrow> bool" where
  e_if_true: "eval_once (BIf BTrue t2 t3) t2" |
  e_if_false: "eval_once (BIf BFalse t2 t3) t3" |
  e_if: "eval_once t1 t1' \<Longrightarrow> eval_once (BIf t1 t2 t3) (BIf t1' t2 t3)"

thm eval_once.induct
thm eval_once.intros
thm eval_once.cases
thm eval_once.simps

inductive_cases eval_once_BTrueD: "eval_once BTrue t"
inductive_cases eval_once_BFalseD: "eval_once BFalse t"

inductive is_normal_form :: "B_term \<Rightarrow> bool" where
  "\<forall>t'. \<not> eval_once t t' \<Longrightarrow> is_normal_form t"

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

lemma
  fixes
    t t' t'' :: B_term
  shows "eval_once t t' \<Longrightarrow> eval_once t t'' \<Longrightarrow> t' = t''"
proof (induction t t' arbitrary: t'' rule: eval_once.induct)
  case (e_if_true t1 t2)
  thus ?case by (auto dest: eval_once_BTrueD elim: eval_once.cases)
    (* by (auto simp: not_eval_once_BTrue elim: eval_once.cases) *)
next
  case (e_if_false t1 t2)
  thus ?case by (auto simp: not_eval_once_BTrue elim: eval_once.cases)
next
  case (e_if t1 t1' t2 t3)
  show ?case
    apply (rule eval_once.cases[OF e_if.prems])
    using e_if.hyps by (auto dest: eval_once_BTrueD eval_once_BFalseD e_if.IH)
(*    using e_if.hyps apply (auto dest: eval_once_BTrueD)[1]
     using e_if.hyps apply (auto dest: eval_once_BFalseD)[1]
    apply auto
    apply (rename_tac t1'')
    apply (erule e_if.IH)
    done *)
qed

theorem
  fixes t :: B_term
  shows "is_value t \<Longrightarrow> is_normal_form t"
using eval_once_BFalseD eval_once_BTrueD is_normal_form.intros is_value.simps by fastforce

theorem
  fixes t :: B_term
  shows "is_normal_form t \<Longrightarrow> is_value t"
proof (rule ccontr, induction t rule: B_term.induct)
    case BTrue
    thus ?case by (simp add: is_value.intros(1))
  next
    case BFalse
    thus ?case by (simp add: is_value.intros(2))
  next
    case (BIf t1 t2 t3)
    thus ?case by (metis e_if e_if_false e_if_true is_normal_form.cases is_normal_form.intros is_value.cases)
qed

end
