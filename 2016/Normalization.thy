theory Normalization
imports 
  Main
  "~~/src/HOL/IMP/Star"
  "$AFP/List-Index/List_Index"
begin

datatype ltype=
  A | Fun ltype ltype (infixr "\<rightarrow>"  225)

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

inductive_cases eval1_LAppE: "eval1_L (LApp t1 t2) t'"

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
    "\<Gamma> \<turnstile> t1 |:| T11 \<rightarrow> T12 \<Longrightarrow> \<Gamma> \<turnstile> t2 |:| T11 \<Longrightarrow> \<Gamma> \<turnstile> LApp t1 t2 |:| T12"

lemma canonical_forms:
  "is_value_L v \<Longrightarrow> \<Gamma> \<turnstile> v |:| A \<Longrightarrow> v = ValA"
  "is_value_L v \<Longrightarrow> \<Gamma> \<turnstile> v |:| T1 \<rightarrow> T2 \<Longrightarrow> \<exists>t. v = LAbs T1 t"
by (auto elim: has_type_L.cases is_value_L.cases)

abbreviation closed ::"lterm \<Rightarrow> bool" where
  "closed t \<equiv> FV t={}"

abbreviation halts :: "lterm \<Rightarrow> bool" where
  "halts t \<equiv> (\<exists>t'. star eval1_L t t' \<and> (\<forall>t1. \<not> eval1_L t' t1)) \<or> (\<forall>t1. \<not> eval1_L t t1)"


lemma value_characterisation:
  "\<Gamma> \<turnstile> t |:| T \<Longrightarrow> \<Gamma> = \<emptyset> \<Longrightarrow> \<forall>t1. \<not> eval1_L t t1 \<Longrightarrow> is_value_L t"
proof (induction rule:"has_type_L.induct")
  case (has_type_LApp \<Gamma> t1 T1 T2 t2)
    have "\<exists>t. eval1_L (LApp t1 t2) t"
      proof (cases "\<exists>t1'. eval1_L t1 t1'")
        case (True)
          thus ?thesis
            by (auto intro: eval1_LApp1)
      next
        case (False)
          thus ?thesis
            using has_type_LApp(3)[OF has_type_LApp(5)]
                  has_type_LApp(4)[OF has_type_LApp(5)]
                  canonical_forms(2)[OF _ has_type_LApp(1)]
            by (cases "\<exists>t2'. eval1_L t2 t2'", auto intro: eval1_L.intros) 
      qed
    with has_type_LApp(6) show ?case by blast
qed (auto intro: "is_value_L.intros")

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

theorem eval_det:
  "eval1_L t t1 \<Longrightarrow> eval1_L t t2 \<Longrightarrow> t1=t2"
proof (induction t t1 arbitrary: t2 rule: eval1_L.induct)
  case (eval1_LApp1 t1 t1' t2)
    from eval1_LApp1.hyps eval1_LApp1.prems show ?case
      by (auto elim: eval1_L.cases is_value_L.cases intro: eval1_LApp1.IH)
next
  case (eval1_LApp2 t1 t2 t2')
    from eval1_LApp2.hyps eval1_LApp2.prems show ?case
      by (auto elim: eval1_L.cases is_value_L.cases intro: eval1_LApp2.IH)
next
  case (eval1_LApp_LAbs v2 t12)
    thus ?case by (auto elim: eval1_L.cases simp: is_value_L.simps)
qed

lemma weakening:
  "\<Gamma> \<turnstile> t |:| T \<Longrightarrow> n \<le> length \<Gamma> \<Longrightarrow> insert_nth n S \<Gamma> \<turnstile> shift_L 1 n t |:| T"
proof (induction \<Gamma> t T arbitrary: n rule: has_type_L.induct)
  case (has_type_LAbs \<Gamma> T1 t2 T2)
    from has_type_LAbs.prems has_type_LAbs.hyps
      has_type_LAbs.IH[where n="Suc n"] 
    show ?case
      by (auto intro: has_type_L.intros)
qed (auto simp: nth_append min_def intro: has_type_L.intros)

lemma substitution:
  "\<Gamma> \<turnstile> t |:| T \<Longrightarrow>  \<Gamma> \<turnstile> LVar n |:| S \<Longrightarrow> \<Gamma> \<turnstile> s |:| S \<Longrightarrow> \<Gamma> \<turnstile> subst_L n s t |:| T"
proof (induction \<Gamma> t T arbitrary: s n rule: has_type_L.induct)
  case (has_type_LAbs \<Gamma> T1 t T2)
  thus ?case by (fastforce
    intro: has_type_L.intros weakening[where n=0, unfolded insert_nth_def nat.rec]
    simp: has_type_L.simps[of _ "LVar n" _, simplified])
qed (auto intro!: has_type_L.intros 
          simp: has_type_L.simps[of _ "LVar _" _, simplified])

lemma shift_down:
  "insert_nth n U \<Gamma> \<turnstile> t |:| T \<Longrightarrow> n \<le> length \<Gamma> \<Longrightarrow>
   (\<And>x. x \<in> FV t \<Longrightarrow> x \<noteq> n) \<Longrightarrow> \<Gamma> \<turnstile> shift_L (- 1) n t |:| T"
proof (induction "insert_nth n U \<Gamma>" t T arbitrary: \<Gamma> n rule: has_type_L.induct)
  case (has_type_LAbs V t T)
  from this(1,3,4) show ?case
    by (fastforce intro: has_type_L.intros has_type_LAbs.hyps(2)[where n="Suc n"])+
qed (fastforce intro: has_type_L.intros simp: nth_append min_def)+


theorem preservation:
  "\<Gamma>\<turnstile> t|:| T \<Longrightarrow> eval1_L t t' \<Longrightarrow> \<Gamma> \<turnstile> t'|:| T" 
proof (induction \<Gamma> t T arbitrary: t' rule: has_type_L.induct)
  case (has_type_LApp \<Gamma> t1 T11 T12 t2)
    note hyps = this and has_T_Abs= has_type_L.simps[of _ "LAbs _ _", simplified]
         
    from hyps show ?case  by (auto
      intro!: has_type_L.intros substitution shift_down
      dest: weakening[where n=0, unfolded insert_nth_def nat.rec]
      elim!: eval1_LAppE
      split: lterm.splits if_splits
      simp: FV_subst FV_shift[of 1, unfolded int_1] has_T_Abs) 
        (metis neq0_conv)
qed (auto elim: eval1_L.cases)


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

lemma shift_shift_invert: "a>0 \<Longrightarrow> shift_L (-a) b (shift_L a b t) = t"
by (induction t arbitrary: a b, auto)

lemma halting_evalR:
  "eval1_L t t1 \<Longrightarrow> halts t1 \<Longrightarrow> halts t"
by (induction rule: eval1_L.induct) (metis eval1_L.intros star_trans star_step1)+

theorem halting_eval:
  "eval1_L t t1 \<Longrightarrow> halts t = halts t1"
using halting_evalL halting_evalR by blast

lemma preservation_step:
  "star eval1_L t t' \<Longrightarrow> \<Gamma> \<turnstile> t |:| T \<Longrightarrow> \<Gamma> \<turnstile> t' |:| T"
by (induction rule: star.induct, auto intro: preservation)

lemma closed_shift:
  "closed t \<Longrightarrow> shift_L d c t = t" 
proof (induction t arbitrary: d c)
  case (LAbs T t)
    show ?case 
      using LAbs(2)[simplified] sorry
qed auto

lemma closedness_preservation1:
  "eval1_L t t' \<Longrightarrow> closed t = closed t'"
proof (induction rule: eval1_L.induct)
  case (eval1_LApp_LAbs v T t)
    note hyps=this
    show ?case
      apply (simp add: FV_subst[of 0 "shift_L 1 0 v" t] FV_shift[of 1 0 v, simplified])
      apply rule
      using subset_singletonD[of "FV t" 0]
      apply simp
      apply (rule disjE[of " closed t" " FV t = {0}"])
      apply simp
      using  closed_shift[of "subst_L 0 (shift_L 1 0 v) t" "-1" 0] 
             FV_subst[of 0 "shift_L 1 0 v" t] FV_shift[of 1 0 v, simplified]
      apply force
      using  closed_shift[of "subst_L 0 (shift_L 1 0 v) t" "-1" 0] 
             FV_subst[of 0 "shift_L 1 0 v" t] FV_shift[of 1 0 v, simplified]
      apply force
      sorry       
qed auto

lemma closedness_preservation:
 "star eval1_L t t' \<Longrightarrow> closed t = closed t'"
proof (induction rule: star.induct)
  case (step x y z)
    show ?case 
      using closedness_preservation1[OF step(1)] step(3)
      by auto
qed auto

locale rel_reasoning =
  fixes R::"lterm \<Rightarrow> ltype \<Rightarrow> bool" ("(_)\<in>\<^sub>R(_)" [150,150] 200)
  assumes R\<^sub>A: " halts t = t \<in>\<^sub>R A" and 
          R_fun: " (halts t \<and>
            (\<forall>s. s \<in>\<^sub>R T1 \<longrightarrow> (LApp t s) \<in>\<^sub>R T2)) = t \<in>\<^sub>R T1\<rightarrow>T2" and
          R_def: "t\<in>\<^sub>RT \<Longrightarrow> closed t \<and> \<emptyset> \<turnstile> t |:| T"

abbreviation C::"ltype \<Rightarrow> lterm set" where
"C T \<equiv> {t. closed t \<and> \<emptyset> \<turnstile> t |:| T}"

fun R::"lterm \<Rightarrow> ltype \<Rightarrow> bool" ("(_)\<in>\<^sub>R(_)" [150,150] 200) where
  "R t A = (t \<in> C A \<and> halts t)"|
  "R t (T1\<rightarrow>T2) = ( t \<in> C (T1\<rightarrow>T2) \<and> halts t \<and> (\<forall>s. R s T1 \<longrightarrow> R (LApp t s) T2))"  

theorem type_unique:
  "\<Gamma> \<turnstile> t |:| T  \<Longrightarrow> \<Gamma> \<turnstile> t |:| B \<Longrightarrow> T=B" sorry

lemma R\<^sub>A: "t \<in>\<^sub>R A \<Longrightarrow> halts t " by auto

lemma R_halts:
  "t \<in>\<^sub>R T \<Longrightarrow> halts t"
by (induction T, auto)

lemma R_def: "t\<in>\<^sub>RT \<Longrightarrow> closed t \<and> \<emptyset> \<turnstile> t |:| T" by (auto elim: R.elims)

lemma halt_val:
  "t \<in>\<^sub>R T \<Longrightarrow>\<exists>v. is_value_L v \<and> star eval1_L t v"
proof -
  assume Rt: "t \<in>\<^sub>R T"
 
  have 1: "\<And>t'. star eval1_L t t' \<Longrightarrow> \<forall>t1. \<not> eval1_L t' t1 \<Longrightarrow> \<exists>v. is_value_L v \<and> star eval1_L t v"
    using value_characterisation[of \<emptyset> _ T]
          preservation_step[OF _ R_def[OF Rt, THEN conjunct2]]
    by auto      
  have "\<forall>t1.\<not> eval1_L t t1 \<Longrightarrow> \<exists>v. is_value_L v \<and> star eval1_L t v"
    using value_characterisation[OF R_def[OF Rt, THEN conjunct2]]
          star.refl[of "eval1_L"]
    by auto

  with 1 show "\<exists>v. is_value_L v \<and> star eval1_L t v" using R_halts[OF Rt] by auto
qed  

lemma eval_preserves_R:
  "\<Gamma> \<turnstile> t|:|T \<Longrightarrow> eval1_L t t' \<Longrightarrow> t \<in>\<^sub>R T \<Longrightarrow> t'\<in>\<^sub>R T"
proof (induction T arbitrary: \<Gamma> t t')
  case (A)
    then show ?case 
      using R\<^sub>A[OF A(3), unfolded halting_eval[OF A(2)]]
            preservation[of \<emptyset> t A t']
            closedness_preservation
      by auto
next
  case (Fun T1 T2)
    note hyps=this
    have "(\<forall>s. s\<in>\<^sub>RT1 \<longrightarrow> LApp t' s\<in>\<^sub>RT2)" 
      using hyps(2)[of \<emptyset>, OF _ eval1_LApp1[OF hyps(4)]]
            hyps(5)[simplified]
            R_def[of "LApp t _" T2]
      by blast
    then show ?case
      using hyps(5)[simplified, unfolded halting_eval[OF hyps(4)]]
            preservation[OF _ hyps(4)] closedness_preservation1[OF hyps(4)]
      by auto
qed

(*
lemma  eval_preserves_R2:
  "\<Gamma> \<turnstile> t|:|T \<Longrightarrow> eval1_L t t' \<Longrightarrow> t' \<in>\<^sub>R T \<Longrightarrow> t\<in>\<^sub>R T"
proof (induction T arbitrary: \<Gamma> t t')
  case (A)
    have 1:"\<And>B. \<emptyset> \<turnstile> t |:| B \<Longrightarrow> B=A"
      using preservation[of \<emptyset>,OF _ A(2)]
            A(3)[simplified, THEN conjunct2, THEN conjunct1]
            type_unique[of \<emptyset> t' A]
      by fast
    show ?case 
      using A(3)[simplified, unfolded halting_eval[OF A(2), symmetric]]
            closedness_preservation1[OF A(2), symmetric] A(2)
      apply auto
      
next
  case (Fun T1 T2)
    note hyps=this
    have "(\<forall>s. s\<in>\<^sub>RT1 \<longrightarrow> LApp t s\<in>\<^sub>RT2)" 
      using hyps(2)[of \<emptyset>, OF _ eval1_LApp1[OF hyps(4)]]
            hyps(5)[unfolded R_fun[symmetric], THEN conjunct2]
            R_def[of "LApp t' _" T2] 
      sorry
    then show ?case
      using R_fun[of t T1 T2]
            hyps(5)[unfolded R_fun[symmetric] halting_eval[OF hyps(4),symmetric]]
      by auto
qed*)

fun subst_all :: "nat \<Rightarrow> lterm list \<Rightarrow> lterm \<Rightarrow> lterm" where
  "subst_all n V ValA = ValA" |
  "subst_all n V (LApp s t) = LApp (subst_all n V s) (subst_all n V t)"|
  "subst_all n V (LAbs T t) = LAbs T (subst_all (Suc n) (map (shift_L 1 0) V) t)"|
  "subst_all n V (LVar k) = (if (k\<ge>n \<and> (k-n)<length V) then (V!(k-n)) else LVar k)"

lemma subst_all_empty[simp]:
  "subst_all n [] t = t"
by (induction t arbitrary: n, auto)

lemma subst_free_var_only: "x\<notin>FV t \<Longrightarrow> subst_L x t1 t = t"
by (induction t arbitrary:t1 x, force+)

lemma subst_all_shift:
  "shift_L d c (subst_all n V t) = subst_all n (map (shift_L d c) V) t"
sorry

lemma subst_comp_subst_all:
  "subst_L n v (subst_all (Suc n) (map (shift_L ((int n) + 1) 0) V) t) = subst_all n (v#map (shift_L ((int n) + 1) 0) V) t"
proof (induction t arbitrary: n v)
  case (LVar k)
    have H:"\<And>s. n \<notin> FV (shift_L ((int n) + 1) 0 s)" 
      proof (rule)
        fix s
       
        assume H:"n \<in> FV (shift_L ((int n) + 1) 0 s)"
        have H1:"1+int n = int n +1" by auto

        show "False"
          using FV_shift[of "n+1" 0 s, simplified]
                image_iff[of n "\<lambda>x. Suc (x + n)" "FV s"]
                H[unfolded H1[symmetric]]
          by force
      qed    
          
    from LVar show ?case
      using subst_free_var_only[OF H]
      by auto
next
  case (LAbs T t)
    have H:"\<And>k. shift_L 1 k \<circ> shift_L (int n + 1) k= shift_L (int (Suc n) + 1) k"
      proof 
        fix k s 
        show "(shift_L 1 k \<circ> shift_L (int n + 1) k) s= shift_L (int (Suc n) + 1) k s"
          by (induction s arbitrary:k, auto)
      qed
    then show ?case using LAbs[of "Suc n"] by simp
qed auto

lemma substitution_all:
  "\<Gamma> \<turnstile> t |:| T \<Longrightarrow>  (\<And>i. i<length V \<Longrightarrow> \<Gamma> \<turnstile> LVar (i+k) |:| (\<Gamma>!i) \<and> \<Gamma> \<turnstile> (V!i) |:| (\<Gamma>!i)) \<Longrightarrow> 
    \<Gamma> \<turnstile> subst_all k V t |:| T"
proof (induction \<Gamma> t T arbitrary: s n k V rule: has_type_L.induct)
  case (has_type_LAbs \<Gamma> T1 t T2)
    note H=this
    show ?case
      apply simp
      apply rule
      using H(2)[of "map (shift_L 1 0) V" "Suc k", simplified]
            H(3)
      sorry
next
  case (has_type_LVar) thus ?case sorry
  (*by (fastforce
    intro: has_type_L.intros weakening[where n=0, unfolded insert_nth_def nat.rec]
    simp: has_type_L.simps[of _ "LVar n" _, simplified])*)
qed (auto intro!: has_type_L.intros 
          simp: has_type_L.simps[of _ "LVar _" _, simplified])

lemma  subst_R:
  "\<Gamma> \<turnstile> t |:| T \<Longrightarrow> length V = length \<Gamma> \<Longrightarrow> (\<And>i. i<length V \<Longrightarrow>is_value_L (V!i) \<and> (V!i) \<in>\<^sub>R (\<Gamma>!i)) \<Longrightarrow> 
    subst_all 0 V t \<in>\<^sub>R T"
proof (induction arbitrary: V rule:has_type_L.induct)
  case (has_type_LVar x T \<Gamma>)
    have "V\<noteq>\<emptyset> \<Longrightarrow> \<exists>v V'. V= v#V'"
      by (meson list.exhaust)
    with has_type_LVar show ?case
      by(cases "V=\<emptyset>", auto)      
next
  case (has_type_LApp \<Gamma> t1 T1 T2 t2)
    note hyps=this
    show ?case
      using hyps(3)[OF hyps(5,6), simplified,
                    THEN conjunct2]
            hyps(4)[OF hyps(5,6),simplified]
      by auto
next
  case (has_type_LAbs \<Gamma> T1 t T2)
    note hyps=this
    have B:"\<emptyset> |,| T1 \<turnstile> subst_all (Suc 0) (map (shift_L 1 0) V) t |:| T2" sorry
    have C: "closed (subst_all (Suc 0) (map (shift_L 1 0) V) t)" sorry
    have "\<And>s. s\<in>\<^sub>RT1 \<Longrightarrow> LApp (LAbs T1 (subst_all (Suc 0) (map (shift_L 1 0) V) t)) s\<in>\<^sub>RT2"
      proof -
        fix s
        assume Rs: "s \<in>\<^sub>R T1"
        obtain v where v_prop:"is_value_L v" "star eval1_L s v"
          using halt_val[OF Rs]
          by auto
        from this(2) have Rv:"v \<in>\<^sub>R T1"
          using Rs
          proof (induction rule:star.induct)
            case (step x y z)
              thus ?case using eval_preserves_R R_def
                by force
          qed force
        have "shift_L (-1) 0 \<circ> shift_L 1 0 = id"
          proof
            fix x
            show "(shift_L (-1) 0 \<circ> shift_L 1 0) x = id x"
              using shift_shift_invert[of 1, simplified]
              by auto
          qed
        hence ev1:"star eval1_L (LApp (LAbs T1 (subst_all (Suc 0) (map (shift_L 1 0) V) t)) v) 
                             (subst_all 0 (v # V) t)"
          using eval1_LApp_LAbs[OF v_prop(1),of T1 "subst_all (Suc 0) (map (shift_L 1 0) V) t"]
                subst_comp_subst_all[of 0 "shift_L 1 0 v" V t, simplified]
                subst_all_shift[of "-1" 0 0 _ t]
                shift_shift_invert[of 1, simplified]
          by force
        have "star eval1_L (LApp (LAbs T1 (subst_all (Suc 0) (map (shift_L 1 0) V) t)) s)
                (LApp (LAbs T1 (subst_all (Suc 0) (map (shift_L 1 0) V) t)) v)"
          using v_prop(2,1)
          proof (induction rule: star.induct)
            case (step x y z)
              show ?case
                using star.intros(2)[OF _ step(3)[OF step(4)]]
                      "is_value_L.intros"(2) eval1_LApp2[OF _ step(1)] 
                by blast                      
          qed auto
        with ev1 have eval:"star eval1_L (LApp (LAbs T1 (subst_all (Suc 0) (map (shift_L 1 0) V) t)) s)
                            (subst_all 0 (v # V) t)"
          using star_trans[of "eval1_L"]
          by meson
        have type: "\<emptyset> \<turnstile> LApp (LAbs T1 (subst_all (Suc 0) (map (shift_L 1 0) V) t)) v |:| T2"
          using R_def[of "subst_all 0 (v # V) t" T2,THEN conjunct2]
                substitution[OF hyps(1), of _ "(\<Gamma>|,|T1)!_" "shift_L 1 0 (V!_)"]
                hyps(4)
                weakening[of \<emptyset> "V!_" "\<Gamma>!_" 0 T1, simplified]
                R_def[OF Rv, THEN conjunct2]
                has_type_L.intros(3,4)
                has_type_L.simps[of "\<Gamma> |,| T1" "LVar _", simplified]
          sorry
        thm hyps(2)[of "v#V",simplified]
        show "LApp (LAbs T1 (subst_all (Suc 0) (map (shift_L 1 0) V) t)) s\<in>\<^sub>RT2"
          using v_prop(1) 
                R_def[OF Rs, THEN conjunct2] value_characterisation
                hyps(2)[of "v# V", simplified]
                
                eval
                
                
                
          sorry
      qed
    
    then show ?case
      using eval1_L.simps[of "LAbs T1 _", simplified] 
            has_type_L.intros(3)[OF B] C
      by auto     
qed (insert R\<^sub>A, auto intro!: has_type_L.intros eval1_L.simps[of ValA, simplified])

theorem Normalization:
  "\<emptyset>\<turnstile> t |:| T \<Longrightarrow> halts t"
using subst_R[of \<emptyset> t T \<emptyset>] R_halts[of t T]
by auto  




end