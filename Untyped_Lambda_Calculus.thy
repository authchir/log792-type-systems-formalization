theory Untyped_Lambda_Calculus
imports Complex_Main
begin

datatype Term
  = Var nat
  | Abs Term
  | App Term Term

text {* Definition 6.1.2 | n_terms *}

inductive n_term :: "nat \<Rightarrow> Term \<Rightarrow> bool" where
  n_term_Var: "0 \<le> k \<Longrightarrow> k < n \<Longrightarrow> n_term n (Var k)" |
  n_term_Abs: "n_term n t \<Longrightarrow> n > 0 \<Longrightarrow> n_term (n - 1) (Abs t)" |
  n_term_App: "n_term n t1 \<Longrightarrow> n_term n t2 \<Longrightarrow> n_term n (App t1 t2)"

text {* Definition 6.2.1 | Shifting *}

primrec shift :: "int \<Rightarrow> nat \<Rightarrow> Term \<Rightarrow> Term" where
  shift_Var: "shift d c (Var k) = Var (if k < c then k else nat (k + d))" |
  shift_Abs: "shift d c (Abs t) = Abs (shift d (Suc c) t)" |
  shift_App: "shift d c (App t1 t2) = App (shift d c t1) (shift d c t2)"

text {* Exercice 6.2.2 *}

lemma "shift 2 0 (Abs (Abs (App (Var 1) (App (Var 0) (Var 2))))) =
                  Abs (Abs (App (Var 1) (App (Var 0) (Var 4))))"
  by simp

lemma "shift 2 0 (Abs (App (Var 0) (App (Var 1) (Abs (App (Var 0) (App (Var 1) (Var 2))))))) =
                  Abs (App (Var 0) (App (Var 3) (Abs (App (Var 0) (App (Var 1) (Var 4))))))"
  by simp

text {* Exercice 6.2.3 *}

lemma "n_term n t \<Longrightarrow> n_term (n + d) (shift d c t)"
proof (induction n t arbitrary: d c rule: n_term.induct)
  case (n_term_Var k n)
  from n_term_Var.hyps show ?case
    using  n_term.n_term_Var by simp
next
  case (n_term_Abs n t)
  from n_term_Abs.hyps show ?case
    using n_term.n_term_Abs  by (auto intro: n_term_Abs.IH)
next
  case (n_term_App n t1 t2)
  show ?case
    by (simp add: n_term.n_term_App n_term_App.IH)
qed

text {* Definition 6.2.4 | Substitution *}

primrec subst :: "nat \<Rightarrow> Term \<Rightarrow> Term \<Rightarrow> Term" where
  subst_Var: "subst j s (Var k) = (if k = j then s else Var k)" |
  subst_Abs: "subst j s (Abs t) = Abs (subst (Suc j) (shift 1 0 s) t)" |
  subst_App: "subst j s (App t1 t2) = App (subst j s t1) (subst j s t2)"

text {* Exercice 6.2.5 *}

lemma "subst 0 (Var 1) (App (Var 0) (Abs (Abs (Var 2)))) =
                        App (Var 1) (Abs (Abs (Var 3)))"
  by simp

lemma "subst 0 (App (Var 1) (Abs (Var 2))) (App (Var 0) (Abs (Var 1))) =
  App (App (Var 1) (Abs (Var 2))) (Abs (App (Var 2) (Abs (Var 3))))"
  by simp

lemma "subst 0 (Var 1) (Abs (App (Var 0) (Var 2))) =
                        Abs (App (Var 0) (Var 2))"
  by simp

lemma "subst 0 (Var 1) (Abs (App (Var 1) (Var 0))) =
                        Abs (App (Var 2) (Var 0))"
  by simp

text {* Exercice 6.2.6 *}

lemma n_term_shift: "n_term n t \<Longrightarrow> n_term (n + j) (shift j i t)"
  by (induction n t arbitrary: j i rule: n_term.induct)
    (auto intro: n_term_Var n_term_Abs[unfolded One_nat_def] n_term_App)

lemma "n_term n t \<Longrightarrow> n_term n s \<Longrightarrow> j \<le> n \<Longrightarrow> n_term n (subst j s t)"
proof (induction n t arbitrary: s j rule: n_term.induct)
  case (n_term_Var k n)
  thus ?case
    by (auto intro: n_term.n_term_Var)
next
  case (n_term_Abs n t)
  thus ?case
    using n_term.n_term_Abs n_term_shift[OF n_term_Abs.prems(1), where j = 1]
    by (auto
      intro: n_term_Abs.IH
      intro!: n_term.n_term_Abs[unfolded One_nat_def]
      simp: n_term_shift[OF n_term_Abs.prems(1), where j = 1])
next
  case (n_term_App n t1 t2)
  thus ?case
    by (simp add: n_term.n_term_App)
qed

text {* Single step evaluation *}

inductive is_value :: "Term \<Rightarrow> bool" where
  "is_value (Abs t)"

inductive eval_once :: "Term \<Rightarrow> Term \<Rightarrow> bool" where
  eval_once_App1: "eval_once t1 t1' \<Longrightarrow> eval_once (App t1 t2) (App t1' t2)" |
  eval_once_App2: "is_value v1 \<Longrightarrow> eval_once t2 t2' \<Longrightarrow> eval_once (App v1 t2) (App v1 t2')" |
  eval_once_App_Abs: "is_value v2 \<Longrightarrow> eval_once (App (Abs t12) v2) (shift (-1) 0 (subst 0 (shift 1 0 v2) t12))"

text {* Theorem 3.5.4 for Untyped Lambda Calculus *}

theorem eval_once_right_unique:
  "eval_once t t' \<Longrightarrow> eval_once t t'' \<Longrightarrow> t' = t''"
proof (induction t t' arbitrary: t'' rule: eval_once.induct)
  case (eval_once_App1 t1 t1' t2)
  from eval_once_App1.hyps eval_once_App1.prems show ?case
    by (auto elim: eval_once.cases is_value.cases intro: eval_once_App1.IH)
next
  case (eval_once_App2 t1 t2 t2')
  from eval_once_App2.hyps eval_once_App2.prems show ?case
    by (auto elim: eval_once.cases is_value.cases intro: eval_once_App2.IH)
next
  case (eval_once_App_Abs v2 t12)
  from eval_once_App_Abs.prems eval_once_App_Abs.hyps show ?case
    by (auto elim: eval_once.cases simp: is_value.simps)
qed

text {* Definition 3.5.6 for Untyped Lambda Calculus *}

definition is_normal_form :: "Term \<Rightarrow> bool" where
  "is_normal_form t \<longleftrightarrow> (\<forall>t'. \<not> eval_once t t')"

text {* Theorem 3.5.7 for Untyped Lambda Calculus *}

theorem value_imp_normal_form: "is_value t \<Longrightarrow> is_normal_form t"
  by (auto elim: is_value.cases eval_once.cases simp: is_normal_form_def)

text {* Theorem 3.5.8 does not hold for Untyped Lambda calculus *}

theorem normal_form_does_not_imp_value:
  "\<exists>t. is_normal_form t \<and> \<not> is_value t" (is "\<exists>t. ?P t")
proof
  have a: "is_normal_form (Var 0)"
    by (auto simp: is_normal_form_def elim: eval_once.cases)
  have b: "\<not> is_value (Var 0)"
    by (auto simp: is_normal_form_def dest: is_value.cases)
  from a b show "?P (Var 0)" by simp
qed

end
