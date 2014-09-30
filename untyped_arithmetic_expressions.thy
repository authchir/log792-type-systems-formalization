theory untyped_arithmetic_expressions
imports Main
begin

datatype B_term
  = BTrue
  | BFalse
  | BIf B_term B_term B_term

inductive eval_once :: "B_term \<Rightarrow> B_term \<Rightarrow> bool" where
  e_if_true: "eval_once (BIf BTrue t2 t3) t2" |
  e_if_false: "eval_once (BIf BFalse t2 t3) t3" |
  e_if: "eval_once t1 t1' \<Longrightarrow> eval_once (BIf t1 t2 t3) (BIf t1' t2 t3)"

thm eval_once.induct
thm eval_once.intros
thm eval_once.cases
thm eval_once.simps

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

inductive_cases eval_once_BTrueD: "eval_once BTrue t"
inductive_cases eval_once_BFalseD: "eval_once BFalse t"

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
  thus ?case
    by (auto dest: eval_once_BTrueD elim: eval_once.cases)
    (* by (auto simp: not_eval_once_BTrue elim: eval_once.cases) *)
next
  case (e_if_false t1 t2)
  thus ?case
    by (auto simp: not_eval_once_BTrue elim: eval_once.cases)
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

end
