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

end
