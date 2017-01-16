theory Normalization
imports 
  Main
  "~~/src/HOL/IMP/Star"
begin

datatype ltype=
  A | Fun ltype ltype ("_\<rightarrow>_" [100,100] 225)

datatype lterm=
  LVar nat | LApp lterm lterm | LAbs ltype lterm | ValA

fun shift_L :: "int \<Rightarrow> nat \<Rightarrow> lterm \<Rightarrow> lterm" where
 "shift_L d c ValA = ValA" |
 "shift_L d c (LVar k)    = LVar (if k < c then k else nat (int k + d))" |
 "shift_L d c (LApp t t1) = LApp (shift_L d c t) (shift_L d c t1)" |
 "shift_L d c (LAbs T t)  = LAbs T (shift_L d (Suc c) t)" 

fun subst_L :: "nat \<Rightarrow> lterm \<Rightarrow> lterm \<Rightarrow> lterm" where
  "subst_L j s ValA = ValA" |
  "subst_L j s (LApp t1 t2) = LApp (subst_L j s t1) (subst_L j s t2)" |
  "subst_L j s (LVar k) = (if k = j then s else LVar k)" |
  "subst_L j s (LAbs T t) = LAbs T (subst_L (Suc j) (shift_L 1 0 s) t)"

fun FV ::"lterm \<Rightarrow> nat set" where
  "FV (LVar k) = {k}"|
  "FV (LApp t1 t2) = FV t1 \<union> FV t2"|
  "FV (LAbs T t) =  image (\<lambda>x. x - 1) (FV t - {0})" |
  "FV ValA = {}"

inductive is_value_L:: "lterm \<Rightarrow> bool" where
  "is_value_L ValA" 
| "is_value_L (LAbs T t)"

inductive eval1_L :: "lterm \<Rightarrow> lterm \<Rightarrow> bool" where
   -- "Rules relating to the evaluation of function application"
  eval1_LApp1:
    "eval1_L t1 t1' \<Longrightarrow> eval1_L (LApp t1 t2) (LApp t1' t2)" |
  eval1_LApp2:
    "is_value_L v1 \<Longrightarrow> eval1_L t2 t2' \<Longrightarrow> eval1_L (LApp v1 t2) (LApp v1 t2')" |
  eval1_LApp_LAbs:
    "is_value_L v2 \<Longrightarrow> eval1_L (LApp (LAbs T' t12) v2)
      (shift_L (-1) 0 (subst_L 0 (shift_L 1 0 v2) t12))" 

type_synonym lcontext = "ltype list"


notation Nil ("\<emptyset>")
abbreviation cons :: "lcontext \<Rightarrow> ltype \<Rightarrow> lcontext" (infixl "|,|" 200) where
  "cons \<Gamma> T' \<equiv> T' # \<Gamma>"
abbreviation elem' :: "(nat \<times> ltype) \<Rightarrow> lcontext \<Rightarrow> bool" (infix "|\<in>|" 200) where
  "elem' p \<Gamma> \<equiv> fst p < length \<Gamma> \<and> snd p = nth \<Gamma> (fst p)"


text{*  For the typing rule of letbinder, we require to replace the type 
        of the variable by the expected type 
    *}


inductive has_type_L :: "lcontext \<Rightarrow> lterm \<Rightarrow> ltype \<Rightarrow> bool" ("((_)/ \<turnstile> (_)/ |:| (_))" [150,150, 150] 150) where
  -- "Rules relating to the type of A"
  has_type_LValA:
    "\<Gamma> \<turnstile> ValA |:| A"|
  -- \<open>Rules relating to the type of the constructs of the $\lambda$-calculus\<close>
  has_type_LVar:
    "(x, T') |\<in>| \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> LVar x |:| (T')" |
  has_type_LAbs:
    "(\<Gamma> |,| T1) \<turnstile> t2 |:| T2 \<Longrightarrow> \<Gamma> \<turnstile> LAbs T1 t2 |:| (T1 \<rightarrow> T2)" |
  has_type_LApp:
    "\<Gamma> \<turnstile> t1 |:| (T11 \<rightarrow> T12) \<Longrightarrow> \<Gamma> \<turnstile> t2 |:| T11 \<Longrightarrow> \<Gamma> \<turnstile> LApp t1 t2 |:| T12"

abbreviation closed ::"lterm \<Rightarrow> bool" where
  "closed t \<equiv> FV t={}"

abbreviation halts :: "lterm \<Rightarrow> bool" where
  "halts t \<equiv> (\<exists>t'. star eval1_L t t' \<and> (\<forall>t1. \<not> eval1_L t' t1)) \<or> (\<forall>t1. \<not> eval1_L t t1)"

locale rel_reasoning =
  fixes R::"lterm \<Rightarrow> ltype \<Rightarrow> bool" ("(_)\<in>\<^sub>R(_)" [150,150] 200)
  assumes R\<^sub>A: " halts t = t \<in>\<^sub>R A" and 
          R_fun: " (halts t \<and>
            (\<forall>s. s \<in>\<^sub>R T1 \<longrightarrow> (LApp t s) \<in>\<^sub>R T2)) = t \<in>\<^sub>R (T1\<rightarrow>T2)" and
          R_def: "t\<in>\<^sub>RT \<Longrightarrow> closed t \<and> \<emptyset> \<turnstile> t |:| T"

lemma (in rel_reasoning) R_halts:
  "t \<in>\<^sub>R T \<Longrightarrow> halts t"
by (induction T, insert R\<^sub>A[of t] R_fun[of t], auto)

lemma[simp]: "nat (int x + 1) = Suc x" by simp
lemma[simp]: "nat (1 + int x) = Suc x" by simp
lemma[simp]: "nat (int x - 1) = x - 1" by simp

lemma gr_Suc_conv: "Suc x \<le> n \<longleftrightarrow> (\<exists>m. n = Suc m \<and> x \<le> m)"
  by (cases n) auto

lemma FV_shift:
  "FV (shift_L (int d) c t) = image (\<lambda>x. if x \<ge> c then x + d else x) (FV t)"
proof (induction t arbitrary: c rule: lterm.induct)
  case (LAbs T t)
  thus ?case  by (auto simp: gr_Suc_conv image_iff) force+
qed auto

lemma FV_subst:
  "FV (subst_L n t u) = (if n \<in> FV u then (FV u - {n}) \<union> FV t else FV u)"
proof (induction u arbitrary: n t rule: lterm.induct)
  case (LAbs T u)
  thus ?case 
    by (auto simp: gr0_conv_Suc image_iff FV_shift[of 1, unfolded int_1],
        (metis DiffI One_nat_def UnCI diff_Suc_1 empty_iff imageI insert_iff nat.distinct(1))+)
qed (auto simp: gr0_conv_Suc image_iff FV_shift[of 1, unfolded int_1])

lemma eval_det:
  "eval1_L t t1 \<Longrightarrow> eval1_L t t2 \<Longrightarrow> t1=t2" sorry

lemma preservation:
  "\<Gamma>\<turnstile> t|:| T \<Longrightarrow> eval1_L t t' \<Longrightarrow> \<Gamma> \<turnstile> t'|:| T" sorry


lemma halting_evalL:
  "eval1_L t t1 \<Longrightarrow> halts t \<Longrightarrow> halts t1"
proof (induction rule: eval1_L.induct)
  case (eval1_LApp1 t1 t1' t2)
    thus ?case 
      using star.simps[of "eval1_L" "LApp t1 t2"]
            eval1_L.intros(1) 
            eval_det
      by metis
next
  case (eval1_LApp2 v t2 t2')
    then show ?case 
      using star.simps[of "eval1_L" "LApp v t2"] eval1_L.intros(2) eval_det
      by metis
next
  case (eval1_LApp_LAbs v T t)
    thus ?case
      using star.simps[of "eval1_L" "LApp (LAbs T t) v"] 
            eval1_L.intros(3) eval_det 
      by metis
qed

lemma halting_evalR:
  "eval1_L t t1 \<Longrightarrow> halts t1 \<Longrightarrow> halts t"
by (induction rule: eval1_L.induct) (metis eval1_L.intros star_trans star_step1)+

theorem halting_eval:
  "eval1_L t t1 \<Longrightarrow> halts t = halts t1"
using halting_evalL halting_evalR by blast


lemma (in rel_reasoning) eval_preserves_R:
  "\<Gamma> \<turnstile> t|:|T \<Longrightarrow> eval1_L t t' \<Longrightarrow> t \<in>\<^sub>R T \<Longrightarrow> t'\<in>\<^sub>R T"
proof (induction T arbitrary: \<Gamma> t t')
  case (A)
    then show ?case 
      using A(3)[unfolded R\<^sub>A[symmetric] halting_eval[OF A(2)]]
            preservation[of \<emptyset> t A t'] A(2)
            R\<^sub>A[of t']
      by auto
next
  case (Fun T1 T2)
    note hyps=this
    have "(\<forall>s. s\<in>\<^sub>RT1 \<longrightarrow> LApp t' s\<in>\<^sub>RT2)" 
      using hyps(2)[of \<emptyset>, OF _ eval1_LApp1[OF hyps(4)]]
            hyps(5)[unfolded R_fun[symmetric], THEN conjunct2]
            R_def[of "LApp t _" T2]
      by blast
    then show ?case
      using R_fun[of t' T1 T2]
            hyps(5)[unfolded R_fun[symmetric] halting_eval[OF hyps(4)]]
      by auto
qed

abbreviation subst_all:: "lterm list \<Rightarrow> lterm \<Rightarrow> lterm" where
"subst_all V \<equiv> rec_nat id (\<lambda>i r. r \<circ> (subst_L i (V!i))) (length V)"

lemma (in rel_reasoning) subst_R:
  "\<Gamma> \<turnstile> t |:| T \<Longrightarrow> length V = length \<Gamma> \<Longrightarrow> (\<And>i. i<length V \<Longrightarrow> (V!i) \<in>\<^sub>R (\<Gamma>!i)) \<Longrightarrow> 
    subst_all V t \<in>\<^sub>R T"
sorry

theorem (in rel_reasoning) Normalization:
  "\<emptyset>\<turnstile> t |:| T \<Longrightarrow> halts t"
using subst_R[of \<emptyset> t T \<emptyset>] R_halts[of t T]
by auto  

end