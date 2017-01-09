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
  "subst_L j s (LAbs T t) = LAbs T (subst_L (Suc j) s t)"

fun FV ::"lterm \<Rightarrow> nat set" where
  "FV (LVar k) = {k}"|
  "FV (LApp t1 t2) = FV t1 \<union> FV t2"|
  "FV (LAbs T t) =  image (\<lambda>x. x - 1) (FV t - {0})" |
  "FV ValA = {}"

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

inductive is_value_L:: "lterm \<Rightarrow> bool" where
  "is_value_L ValA" 
| "is_value_L (LAbs T t)"

abbreviation R:: " lterm \<Rightarrow> ltype \<Rightarrow> bool" ("(_) \<in>\<^sub>R (_)" [100,100] 200) where
  "t \<in>\<^sub>R T \<equiv> (\<emptyset> \<turnstile> t |:| T \<and> FV t = {})"

abbreviation halts :: "lterm \<Rightarrow> bool" where
  "halts t \<equiv> \<exists>t'. star eval1_L t t' \<and> (\<forall>t1. \<not> eval1_L t' t1)"

lemma R_def:
  "t \<in>\<^sub>R A = (halts t)"
  "s \<in>\<^sub>R (T1\<rightarrow>T2) = (\<forall>t. t \<in>\<^sub>R (T1) \<longrightarrow> (LApp s t) \<in>\<^sub>R T2)"
proof -
  have lr:"t \<in>\<^sub>R A \<Longrightarrow> halts t"
    proof -
      assume H:"t \<in>\<^sub>R A"
      obtain \<Gamma> where G:"\<Gamma> = \<emptyset>" "\<Gamma> \<turnstile> t |:| A"
        using H
        by metis
      show "halts t"
        using G(2,1)
              H[THEN conjunct2] 
        proof (induction rule:has_type_L.induct)
          case (has_type_LApp \<Gamma> t1 T1 T2 t2)
            note hyps=this and FVt1=this(6)[simplified, THEN conjunct1] and
                 FVt2 = this(6)[simplified, THEN conjunct2]
            obtain t1' t2' where Ht1:"star eval1_L t1 t1'" "(\<forall>t1. \<not> eval1_L t1' t1)"
                             and Ht2: " star eval1_L t2 t2' \<and> (\<forall>t1. \<not> eval1_L t2' t1)"
              using hyps(3)[OF hyps(5) FVt1]
                    hyps(4)[OF hyps(5) FVt2]
              by blast
            show ?case
              
              sorry
        qed (auto simp: eval1_L.simps[of ValA] eval1_L.simps[of "LAbs _ _"])
  have "halts t \<Longrightarrow> t \<in>\<^sub>R A"
  sorry

  with lr show "t \<in>\<^sub>R A = (halts t)" by blast
next
  have lr:" s \<in>\<^sub>R (T1\<rightarrow>T2) \<Longrightarrow> (\<forall>t. t \<in>\<^sub>R (T1) \<longrightarrow> (LApp s t) \<in>\<^sub>R T2)" sorry
  have "(\<forall>t. t \<in>\<^sub>R (T1) \<longrightarrow> (LApp s t) \<in>\<^sub>R T2) \<Longrightarrow> s \<in>\<^sub>R (T1\<rightarrow>T2)" sorry

  with lr show "s \<in>\<^sub>R (T1\<rightarrow>T2) = (\<forall>t. t \<in>\<^sub>R (T1) \<longrightarrow> (LApp s t) \<in>\<^sub>R T2)" by satx
qed      


end