theory Typed_Lambda_Calculus
imports Complex_Main "~/afp-code/thys/List-Index/List_Index"
begin

text {* Definition 9.1.1 *}

datatype_new Type
  = Bool
  | Fun (domain: Type) (codomain: Type) (infixr "\<rightarrow>" 225)

datatype_new Term
  = LTrue
  | LFalse
  | LIf (cond: Term) (then_expr: Term) (else_expr: Term)
  | Var nat
  | Abs Type Term
  | App Term Term (infixl "$" 200)

primrec shift :: "int \<Rightarrow> nat \<Rightarrow> Term \<Rightarrow> Term" where
  shift_LTrue: "shift d c LTrue = LTrue" |
  shift_LFalse: "shift d c LFalse = LFalse" |
  shift_LIf: "shift d c (LIf t1 t2 t3) = LIf (shift d c t1) (shift d c t2) (shift d c t3)" |
  shift_Var: "shift d c (Var k) = Var (if k < c then k else nat (k + d))" |
  shift_Abs: "shift d c (Abs T t) = Abs T (shift d (Suc c) t)" |
  shift_App: "shift d c (App t1 t2) = App (shift d c t1) (shift d c t2)"

primrec subst :: "nat \<Rightarrow> Term \<Rightarrow> Term \<Rightarrow> Term" where
  subst_LTrue: "subst j s LTrue = LTrue" |
  subst_LFalse: "subst j s LFalse = LFalse" |
  subst_LIf: "subst j s (LIf t1 t2 t3) = LIf (subst j s t1) (subst j s t2) (subst j s t3)" |
  subst_Var: "subst j s (Var k) = (if k = j then s else Var k)" |
  subst_Abs: "subst j s (Abs T t) = Abs T (subst (Suc j) (shift 1 0 s) t)" |
  subst_App: "subst j s (App t1 t2) = App (subst j s t1) (subst j s t2)"

inductive is_value :: "Term \<Rightarrow> bool" where
  is_value_LTrue: "is_value LTrue" |
  is_value_LFalse: "is_value LFalse" |
  is_value_Abs: "is_value (Abs T t)"

inductive eval_once :: "Term \<Rightarrow> Term \<Rightarrow> bool" where
  eval_once_LIf_LTrue: "eval_once (LIf LTrue t2 t3) t2" |
  eval_once_LIf_LFalse: "eval_once (LIf LFalse t2 t3) t3" |
  eval_once_LIf: "eval_once t1 t1' \<Longrightarrow> eval_once (LIf t1 t2 t3) (LIf t1' t2 t3)" |
  eval_once_App1: "eval_once t1 t1' \<Longrightarrow> eval_once (App t1 t2) (App t1' t2)" |
  eval_once_App2: "is_value v1 \<Longrightarrow> eval_once t2 t2' \<Longrightarrow> eval_once (App v1 t2) (App v1 t2')" |
  eval_once_App_Abs: "is_value v2 \<Longrightarrow> eval_once (App (Abs T t12) v2) (shift (-1) 0 (subst 0 (shift 1 0 v2) t12))"

type_synonym Context = "Type list"
notation Nil ("\<emptyset>")
abbreviation cons :: "Context \<Rightarrow> Type \<Rightarrow> Context" (infixl "|,|" 200) where
  "cons \<Gamma> T \<equiv> T # \<Gamma>"
abbreviation elem :: "(nat \<times> Type) \<Rightarrow> Context \<Rightarrow> bool" (infix "|\<in>|" 200) where
  "elem p \<Gamma> \<equiv> fst p < length \<Gamma> \<and> nth \<Gamma> (fst p) = snd p"

inductive has_type :: "Context \<Rightarrow> Term \<Rightarrow> Type \<Rightarrow> bool" ("((_)/ \<turnstile> (_)/ |:| (_))" [150, 150, 150] 150) where
  has_type_LTrue: "\<Gamma> \<turnstile> LTrue |:| Bool" |
  has_type_LFalse: "\<Gamma> \<turnstile> LFalse |:| Bool" |
  has_type_LIf: "\<Gamma> \<turnstile> t1 |:| Bool \<Longrightarrow> \<Gamma> \<turnstile> t2 |:| T \<Longrightarrow> \<Gamma> \<turnstile> t3 |:| T \<Longrightarrow> \<Gamma> \<turnstile> (LIf t1 t2 t3) |:| T" |
  has_type_Var: "(x, T) |\<in>| \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> (Var x) |:| T" |
  has_type_Abs: "(\<Gamma> |,| T1) \<turnstile> t2 |:| T2 \<Longrightarrow> \<Gamma> \<turnstile> (Abs T1 t2) |:| (T1 \<rightarrow> T2)" |
  has_type_App: "\<Gamma> \<turnstile> t1 |:| (T11 \<rightarrow> T12) \<Longrightarrow> \<Gamma> \<turnstile> t2 |:| T11 \<Longrightarrow> \<Gamma> \<turnstile> (App t1 t2) |:| T12"

lemma "\<emptyset> \<turnstile> (App (Abs Bool (Var 0)) LTrue) |:| Bool"
  by (auto intro!: has_type.intros)

text {* Exercice 9.2.2 *}

lemma
  assumes "\<Gamma> = \<emptyset> |,| (Bool \<rightarrow> Bool)"
  shows "\<Gamma> \<turnstile> App (Var 0) (LIf LFalse LTrue LFalse) |:| Bool"
  by (auto intro!: has_type.intros simp: assms)

lemma
  assumes "\<Gamma> = \<emptyset> |,| (Bool \<rightarrow> Bool)"
  shows "\<Gamma> \<turnstile> Abs Bool (App (Var 1) (LIf (Var 0) LTrue LFalse)) |:| Bool \<rightarrow> Bool"
  by (auto intro!: has_type.intros simp: assms)

text {* Exercice 9.2.3 *}

lemma
  assumes "\<Gamma> = \<emptyset> |,| Bool \<rightarrow> Bool \<rightarrow> Bool |,| Bool |,| Bool"
  shows "\<Gamma> \<turnstile> App (App (Var 2) (Var 1)) (Var 0) |:| Bool"
  by (auto intro!: has_type.intros simp: assms)

text {* Lemma 9.3.1 *}

lemma inversion:
  "\<Gamma> \<turnstile> LTrue |:| R \<Longrightarrow> R = Bool"
  "\<Gamma> \<turnstile> LFalse |:| R \<Longrightarrow> R = Bool"
  "\<Gamma> \<turnstile> LIf t1 t2 t3 |:| R \<Longrightarrow> \<Gamma> \<turnstile> t1 |:| Bool \<and> \<Gamma> \<turnstile> t2 |:| R \<and> \<Gamma> \<turnstile> t3 |:| R"
  "\<Gamma> \<turnstile> Var x |:| R \<Longrightarrow> (x, R) |\<in>| \<Gamma>"
  "\<Gamma> \<turnstile> Abs T1 t2 |:| R \<Longrightarrow> \<exists>R2. R = T1 \<rightarrow> R2 \<and> \<Gamma> |,| T1 \<turnstile> t2 |:| R2"
  "\<Gamma> \<turnstile> App t1 t2 |:| R \<Longrightarrow> \<exists>T11. \<Gamma> \<turnstile> t1 |:| T11 \<rightarrow> R \<and> \<Gamma> \<turnstile> t2 |:| T11"
  "\<Gamma> \<turnstile> LTrue |:| R \<Longrightarrow> R = Bool"
  by (auto elim: has_type.cases)

text {* Exercise 9.3.2 *}

lemma "\<not> (\<Gamma> \<turnstile> App (Var 0) (Var 0) |:| T)"
proof
  assume "\<Gamma> \<turnstile> App (Var 0) (Var 0) |:| T"
  hence "\<exists>U. \<Gamma> \<turnstile> Var 0 |:| U \<rightarrow> T \<and> \<Gamma> \<turnstile> Var 0 |:| U" by (auto dest: inversion(6))
  hence "\<exists>U. (0, U \<rightarrow> T) |\<in>| \<Gamma> \<and> (0, U) |\<in>| \<Gamma>" by (auto dest!: inversion(4))
  hence "\<exists>U R. (0, R) |\<in>| \<Gamma> \<and> R = U \<rightarrow> T \<and> R = U" by simp
  hence "\<exists>U. U = U \<rightarrow> T" by auto
  thus "False" by (auto dest: arg_cong[of _ _ size])
qed

text {* Theorem 9.3.3 *}

theorem uniqueness_of_types:
  "\<Gamma> \<turnstile> t |:| T1 \<Longrightarrow> \<Gamma> \<turnstile> t |:| T2 \<Longrightarrow> T1 = T2"
proof (induction \<Gamma> t T1 arbitrary: T2 rule: has_type.induct)
  case (has_type_LTrue \<Gamma>)
  thus ?case by (auto dest: inversion(1))
next
  case (has_type_LFalse \<Gamma>)
  thus ?case by (auto dest: inversion(2))
next
  case (has_type_LIf \<Gamma> t1 t2 T t3)
  thus ?case by (metis inversion(3))
  (* from has_type_LIf.prems show ?case *)
  (* by (auto dest: inversion(3) has_type_LIf.IH) *)
next
  case (has_type_Var x T \<Gamma>)
  thus ?case by (auto dest: inversion(4))
next
  case (has_type_Abs \<Gamma> T1 t U)
  thus ?case by (metis inversion(5))
next
  case (has_type_App \<Gamma> t1 U1 U2 t2)
  thus ?case by (metis Type.sel(2) inversion(6))
qed

text {* Lemma 9.3.4 *}

lemma canonical_forms:
  "is_value v \<Longrightarrow> \<Gamma> \<turnstile> v |:| Bool \<Longrightarrow> v = LTrue \<or> v = LFalse"
  "is_value v \<Longrightarrow> \<Gamma> \<turnstile> v |:| T1 \<rightarrow> T2 \<Longrightarrow> \<exists>t2. v = Abs T1 t2"
  by (auto elim: has_type.cases is_value.cases)

text {* Theorem 9.3.5 *}

primrec FV :: "Term \<Rightarrow> nat set" where
  "FV LTrue = {}" |
  "FV LFalse = {}" |
  "FV (LIf t1 t2 t3) = FV t1 \<union> FV t2 \<union> FV t3" |
  "FV (Var x) = {x}" |
  "FV (Abs T t) = image (\<lambda>x. x - 1) (FV t - {0})" |
  "FV (App t1 t2) = FV t1 \<union> FV t2"

lemma "FV (Abs Bool (Abs Bool (LIf (Var 2) (Var 0) (Var 1)))) = {0}"
  by (simp add: insert_commute[of _ 0])

definition is_closed :: "Term \<Rightarrow> bool" where
  "is_closed t \<equiv> FV t = {}"

lemma "\<not> is_closed (Abs Bool (Abs Bool (LIf (Var 2) (Var 0) (Var 1))))"
  by (simp add: is_closed_def insert_commute[of _ 0])

lemma "is_closed (Abs Bool (Abs Bool (Abs Bool (LIf (Var 2) (Var 0) (Var 1)))))"
  by (simp add: is_closed_def insert_commute[of _ 0])

theorem progress:
   "\<emptyset> \<turnstile> t |:| T \<Longrightarrow> is_closed t \<Longrightarrow> is_value t \<or> (\<exists>t'. eval_once t t')"
proof (induction t T rule: has_type.induct)
  case (has_type_LIf \<Gamma> t1 t2 T t3)
  thus ?case by (cases "is_value t1")
    (auto intro: eval_once.intros dest: canonical_forms simp: is_closed_def)
next
  case (has_type_App \<Gamma> t1 T11 T12 t2)
  thus ?case by (cases "is_value t1", cases "is_value t2")
    (auto intro: eval_once.intros dest: canonical_forms(2) simp: is_closed_def)
qed (simp_all add: is_value.intros is_closed_def)

text {* Lemma 9.3.6 *}

lemma[simp]: "nat (int x + 1) = Suc x" by simp
lemma[simp]: "nat (1 + int x) = Suc x" by simp

(* 
value "Var 0 $ Var 1 $ Var 2 $ Var 3 $ Var 4 $ Var 5"
value "shift -3 2 (shift 2 3 (shift 1 0 (Var 0 $ Var 1 $ Var 2 $ Var 3 $ Var 4 $ Var 5)))"

lemma permutation:
  "\<Gamma> |,| U |,| S \<turnstile> t |:| T \<Longrightarrow> \<Gamma> |,| S |,| U \<turnstile> shift -3 2 (shift 2 3 (shift 1 0 t)) |:| T"
proof (induction "\<Gamma> |,| U |,| S" t T arbitrary: \<Gamma> U S rule: has_type.induct)
  case has_type_LTrue
  thus ?case by (simp add: has_type.intros)
next
  case has_type_LFalse
  thus ?case by (simp add: has_type.intros)
next
  case (has_type_LIf t1 t2 T t3)
  thus ?case by (simp add: has_type.intros)
next
  case (has_type_Var x T)
  thus ?case by (auto intro: has_type.intros)
next
  case (has_type_Abs V t2 T)
  show ?case
    apply (auto intro!: has_type.intros)
    using has_type_Abs.hyps
    apply simp
    sorry
next
  case (has_type_App t1 T11 T12 t2)
  thus ?case by (auto intro!: has_type.intros)
qed *)

text {* Lemma 9.3.7 *}

lemma weakening:
  "\<lbrakk>\<Gamma> \<turnstile> t |:| T; n \<le> length \<Gamma>\<rbrakk> \<Longrightarrow> insert_nth n S \<Gamma> \<turnstile> shift 1 n t |:| T"
proof (induction \<Gamma> t T arbitrary: n rule: has_type.induct)
  case (has_type_Var x T \<Gamma>)
  thus ?case by (auto simp: nth_append min_def intro: has_type.intros)
next
  case (has_type_Abs \<Gamma> T1 t2 T2)
  from has_type_Abs.prems has_type_Abs.hyps has_type_Abs.IH[where n="Suc n"] show ?case
    by (auto intro: has_type.intros)
qed (auto intro: has_type.intros)

text {* Lemma 9.3.8 *}

lemma substitution:
  "\<Gamma> \<turnstile> t |:| T \<Longrightarrow>  \<Gamma> \<turnstile> Var n |:| S \<Longrightarrow> n < length \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> s |:| S \<Longrightarrow> \<Gamma> \<turnstile> subst n s t |:| T"
proof (induction \<Gamma> t T arbitrary: s n rule: has_type.induct)
  case has_type_LTrue
  thus ?case by (auto intro: has_type.intros)
next
  case has_type_LFalse
  thus ?case by (auto intro: has_type.intros)
next
  case (has_type_LIf t1 t2 T t3)
  thus ?case by (auto intro: has_type.intros)
next
  case (has_type_Var x T \<Gamma>)
  thus ?case by (auto intro: has_type.has_type_Var dest: inversion(4))
next
  case (has_type_Abs \<Gamma> T1 t T2)
  thus ?case
    by (fastforce intro: has_type.intros
      weakening[where n=0, unfolded insert_nth_def nat.rec] dest: inversion(4))
next
  case (has_type_App t1 T11 T12 t2)
  thus ?case by (auto intro!: has_type.intros)
qed

text {* Theorem 9.3.9 *}

inductive_cases eval_once_LTrueE: "eval_once LTrue t"
inductive_cases eval_once_LFalseE: "eval_once LFalse t"
inductive_cases eval_once_VarE: "eval_once (Var x) t"
inductive_cases eval_once_AbsE: "eval_once (Abs T t) t'"
inductive_cases eval_once_AppE: "eval_once (App t1 t2) t"
(* 
primrec Consts :: "Term \<Rightarrow> Term set" where
  "Consts LTrue = {LTrue}" |
  "Consts LFalse = {LFalse}" |
  "Consts (LIf t1 t2 t3) = Consts t1 \<union> Consts t2 \<union> Consts t3" |
  "Consts (Var x) = {Var x}" |
  "Consts (Abs T t) = Consts t" |
  "Consts (App t1 t2) = Consts t1 \<union> Consts t2" *)
(* 
lemma Consts_subst: "Consts (subst 0 t u) = Consts t \<union> (Consts u - {Var 0})"
  sorry

lemma Consts_shift_n_0: "Consts (shift n 0 t) = image (\<lambda>t. case t of Var x \<Rightarrow> Var (Suc x) | x \<Rightarrow> x) (Consts t)"
  sorry *)

lemma[simp]: "nat (int x - 1) = x - 1" by simp

code_pred has_type .
values "{T. [Bool \<rightarrow> Bool] \<turnstile>  shift (- 1) 0 (Abs Bool LTrue) |:| T}"(*
lemma shift_down: "insert_nth n U \<Gamma> \<turnstile> t |:| T \<Longrightarrow> n \<le> length \<Gamma> \<Longrightarrow> (\<And>x. x \<in> FV t \<Longrightarrow> x > n) \<Longrightarrow>
   \<Gamma> \<turnstile> shift (- 1) n t |:| T"
proof (induction "insert_nth n U \<Gamma>" t T arbitrary: \<Gamma> n rule: has_type.induct)
  case has_type_LTrue
  thus ?case by (auto intro: has_type.intros)
next
  case has_type_LFalse
  thus ?case by (auto intro: has_type.intros)
next
  case (has_type_LIf t1 t2 T t3)
  thus ?case by (auto intro: has_type.intros)
next
  case (has_type_Var x T)
  thus ?case by (fastforce intro: has_type.intros simp: nth_append min_def)
next
  case (has_type_Abs V t T)
  from this(1,3,4) show ?case nitpick
    apply -
    unfolding shift.simps
    apply (rule has_type.intros)
    apply (rule has_type_Abs.hyps(2)[where n="Suc n"])
    apply simp
    apply (auto simp: gr0_conv_Suc image_iff)
    apply (drule meta_spec)
    apply (erule meta_mp)
    apply auto find_theorems "0 < _ <-> _" name: conv
    apply (auto intro!: has_type.intros has_type_Abs.hyps(2)[where n="Suc n"])
    apply (case_tac x) apply auto nitpick  sorry
next
  case (has_type_App t1 T11 T12 t2)
  thus ?case by (auto intro: has_type.intros)
qed
*)

theorem preservation:
  "\<Gamma> \<turnstile> t |:| T \<Longrightarrow> eval_once t t' \<Longrightarrow> \<Gamma> \<turnstile> t' |:| T"
proof (induction \<Gamma> t T arbitrary: t' rule: has_type.induct)
  case (has_type_LTrue \<Gamma>)
  thus ?case by (rule eval_once_LTrueE)
next
  case (has_type_LFalse \<Gamma>)
  thus ?case by (rule eval_once_LFalseE)
next
  case (has_type_LIf \<Gamma> t1 t2 T t3)
  thus ?case by (auto intro: has_type.has_type_LIf eval_once.cases[OF has_type_LIf.prems])
next
  case (has_type_Var x T \<Gamma>)
  thus ?case by (auto intro: eval_once_VarE)
next
  case (has_type_Abs \<Gamma> T1 t T2)
  thus ?case by (auto intro: eval_once_AbsE)
next
  case (has_type_App \<Gamma> t1 T11 T12 t2)
  thus ?case
    apply (auto elim!: eval_once_AppE)
    apply (rule has_type.has_type_App)
    apply assumption+
    apply (erule has_type.has_type_App)
    apply assumption
    apply (drule inversion)
    apply (erule exE)
    apply (erule conjE)
    unfolding Type.simps
    apply (erule conjE)
    apply hypsubst
    apply (drule weakening[where n=0, unfolded insert_nth_def nat.rec])
    apply simp
    apply (rule shift_down)
    apply (rule substitution)
    by (auto intro: has_type.intros simp: Consts_subst Consts_shift_n_0 split: Term.splits)
qed

text {* 9.5.1 *}

datatype_new UTerm
  = UTrue
  | UFalse
  | UIf (cond: UTerm) (then_expr: UTerm) (else_expr: UTerm)
  | UVar nat
  | UAbs UTerm
  | UApp UTerm UTerm

primrec shiftU :: "int \<Rightarrow> nat \<Rightarrow> UTerm \<Rightarrow> UTerm" where
  "shiftU d c UTrue = UTrue" |
  "shiftU d c UFalse = UFalse" |
  "shiftU d c (UIf t1 t2 t3) = UIf (shiftU d c t1) (shiftU d c t2) (shiftU d c t3)" |
  "shiftU d c (UVar k) = UVar (if k < c then k else nat (k + d))" |
  "shiftU d c (UAbs t) = UAbs (shiftU d (Suc c) t)" |
  "shiftU d c (UApp t1 t2) = UApp (shiftU d c t1) (shiftU d c t2)"

primrec substU :: "nat \<Rightarrow> UTerm \<Rightarrow> UTerm \<Rightarrow> UTerm" where
  "substU j s UTrue = UTrue" |
  "substU j s UFalse = UFalse" |
  "substU j s (UIf t1 t2 t3) = UIf (substU j s t1) (substU j s t2) (substU j s t3)" |
  "substU j s (UVar k) = (if k = j then s else UVar k)" |
  "substU j s (UAbs t) = UAbs (substU (Suc j) (shiftU 1 0 s) t)" |
  "substU j s (UApp t1 t2) = UApp (substU j s t1) (substU j s t2)"

inductive is_valueU :: "UTerm \<Rightarrow> bool" where
  "is_valueU UTrue" |
  "is_valueU UFalse" |
  "is_valueU (UAbs t)"

inductive eval_onceU :: "UTerm \<Rightarrow> UTerm \<Rightarrow> bool" where
  "eval_onceU (UIf UTrue t2 t3) t2" |
  "eval_onceU (UIf UFalse t2 t3) t3" |
  "eval_onceU t1 t1' \<Longrightarrow> eval_onceU (UIf t1 t2 t3) (UIf t1' t2 t3)" |
  "eval_onceU t1 t1' \<Longrightarrow> eval_onceU (UApp t1 t2) (UApp t1' t2)" |
  "is_valueU v1 \<Longrightarrow> eval_onceU t2 t2' \<Longrightarrow> eval_onceU (UApp v1 t2) (UApp v1 t2')" |
  "is_valueU v2 \<Longrightarrow> eval_onceU (UApp (UAbs t12) v2) (shiftU (-1) 0 (substU 0 (shiftU 1 0 v2) t12))"

primrec erase :: "Term \<Rightarrow> UTerm" where
  "erase LTrue = UTrue" |
  "erase LFalse = UFalse" |
  "erase (LIf t1 t2 t3) = (UIf (erase t1) (erase t2) (erase t3))" |
  "erase (Var x) = UVar x" |
  "erase (Abs _ t) = UAbs (erase t)" |
  "erase (App t1 t2) = UApp (erase t1) (erase t2)"

lemma shift_erasure: "erase (shift d c t) = shiftU d c (erase t)"
  apply (rule Term.induct)
  apply (auto)
sorry
(* proof (induction t arbitrary: d c rule: Term.induct)
  case LTrue thus ?case by auto
  case LFalse thus ?case by auto
  case LIf thus ?case by auto
  case Var thus ?case sorry
  case Abs thus ?case sorry
  case App thus ?case by auto
qed *)

lemma subst_erasure: "erase (subst j s t) = substU j (erase s) (erase t)"
  apply (rule Term.induct)
  apply (auto)
sorry
(* proof (induction t rule: Term.induct)
  print_cases
  case LTrue thus ?case by auto
  case LFalse thus ?case by auto
  case LIf thus ?case by auto
  case Var thus ?case sorry
  case Abs thus ?case sorry
  case App thus ?case by auto
qed *)

lemma is_value_erasure: "is_value t \<Longrightarrow> is_valueU (erase t)"
  by (auto  intro: is_valueU.intros elim!: is_value.cases)

theorem "eval_once t t' \<Longrightarrow> eval_onceU (erase t) (erase t')"
by (induction t t' rule: eval_once.induct)
  (auto intro: eval_onceU.intros simp: shift_erasure subst_erasure is_value_erasure)

end
