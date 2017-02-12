theory Normalization
imports 
  Main
  "~~/src/HOL/IMP/Star"
  "$AFP/List-Index/List_Index"
  "~~/src/HOL/Eisbach/Eisbach"
  "~~/src/HOL/Eisbach/Eisbach_Tools"
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
  "\<emptyset> \<turnstile> t |:| T \<Longrightarrow> \<forall>t1. \<not> eval1_L t t1 \<Longrightarrow> is_value_L t"
proof (induction "\<emptyset>::ltype list" t T rule:"has_type_L.induct")
  case (has_type_LApp t1 T1 T2 t2)
    have "\<exists>t. eval1_L (LApp t1 t2) t"
      proof (cases "\<exists>t1'. eval1_L t1 t1'")
        case (True)
          thus ?thesis
            by (auto intro: eval1_LApp1)
      next
        case (False)
          thus ?thesis
            using has_type_LApp(2-4)                  
                  canonical_forms(2)[OF _ has_type_LApp(1)]
            by (cases "\<exists>t2'. eval1_L t2 t2'", auto intro: eval1_L.intros) 
      qed
    with has_type_LApp(5) show ?case by blast
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

lemma shift_only_FV:
  "(\<forall>x\<in>FV t. x < c) \<Longrightarrow> shift_L d c t = t" 
proof (induction t arbitrary: d c)
  case (LAbs T t)
    show ?case 
      using LAbs(2)[simplified]
            LAbs(1)[of "Suc c" d]
      by force
qed auto

lemma FV_ctx:
  "\<Gamma> \<turnstile> t |:| B \<Longrightarrow> FV t \<subseteq> {k. k<length \<Gamma>}"
by (induction rule: "has_type_L.induct") auto

method invert_type = (match premises in H:"\<emptyset> \<turnstile> Te |:| B" for Te::lterm and B::ltype\<Rightarrow>
                      \<open> insert has_type_L.simps[of \<emptyset> Te B, simplified]\<close>)


lemma closedness_preservation1:
  "eval1_L t t' \<Longrightarrow> \<emptyset> \<turnstile> t |:| B \<Longrightarrow> closed t = closed t'"
using FV_ctx[of \<emptyset> _ B, simplified] preservation
by blast

lemma closedness_preservation:
 "star eval1_L t t'\<Longrightarrow> \<emptyset> \<turnstile> t |:| B  \<Longrightarrow> closed t = closed t'"
proof (induction rule: star.induct)
  case (step x y z)
    show ?case 
      using closedness_preservation1[OF step(1)] step(3,4)
            preservation[OF step(4,1)]
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
    using value_characterisation[of _ T]
          preservation_step[OF _ R_def[OF Rt, THEN conjunct2]]
    by auto      
  have "\<forall>t1.\<not> eval1_L t t1 \<Longrightarrow> \<exists>v. is_value_L v \<and> star eval1_L t v"
    using value_characterisation[OF R_def[OF Rt, THEN conjunct2]]
          star.refl[of "eval1_L"]
    by auto

  with 1 show "\<exists>v. is_value_L v \<and> star eval1_L t v" using R_halts[OF Rt] by auto
qed  

lemma eval_preserves_R:
  "\<emptyset> \<turnstile> t|:|T \<Longrightarrow> eval1_L t t' \<Longrightarrow> t \<in>\<^sub>R T = t'\<in>\<^sub>R T"
proof (induction T arbitrary: t t')
  case (A)
    then show ?case 
      using halting_eval[OF A(2)]
            preservation[OF A]
            closedness_preservation[OF star_step1[of "eval1_L",OF A(2)]]
      by auto
next
  case (Fun T1 T2)
    note hyps=this
    have "\<forall>s. s\<in>\<^sub>RT1 \<longrightarrow> ( LApp t' s\<in>\<^sub>RT2 = LApp t s\<in>\<^sub>RT2)" 
      proof (rule, rule)
        fix s
        assume Rs: "s\<in>\<^sub>RT1"
        have "LApp t' s\<in>\<^sub>RT2 \<Longrightarrow> LApp t s\<in>\<^sub>RT2"
          using hyps(2)[OF _ eval1_LApp1[OF hyps(4)],of s]
                has_type_L.simps[of \<emptyset> "LApp t s"] hyps(3) R_def[OF Rs]
          by auto
        then show "LApp t' s\<in>\<^sub>RT2 = LApp t s\<in>\<^sub>RT2"
          using hyps(2)[OF _ eval1_LApp1[OF hyps(4)],of s]
                R_def[of "LApp t s" T2]
          by fast
      qed
    then show ?case
      using halting_eval[OF hyps(4)]
            preservation[OF hyps(3,4)] 
            hyps(3)
            closedness_preservation1[OF hyps(4)]
      by auto
qed

lemma star_eval_preserves_R:
  "star eval1_L t t' \<Longrightarrow> \<emptyset> \<turnstile> t|:|T \<Longrightarrow> t \<in>\<^sub>R T = t'\<in>\<^sub>R T"
proof (induction rule: star.induct)
  case (step x y z)
    show ?case
      using eval_preserves_R[OF step(4,1)]
            step(3) preservation[OF step(4,1)]
      by auto
qed auto

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

lemma weakening_closed:
  "\<emptyset> \<turnstile> t |:| T \<Longrightarrow> \<Gamma> \<turnstile> t |:| T"
proof (induction \<Gamma>)
  case (Cons B \<Gamma>')
    thus ?case
      using weakening[of \<Gamma>' t T 0 B] 
            shift_only_FV[of t 0 1]
            FV_ctx[of \<emptyset> t T, simplified]
      by force
qed auto 

lemma substitution_all:
  "\<Gamma> \<turnstile> t |:| T \<Longrightarrow> k+length V = length \<Gamma> \<Longrightarrow> (\<And>i. i<length V \<Longrightarrow> \<emptyset> \<turnstile> (V!i) |:| (\<Gamma>!(i+k))) \<Longrightarrow> 
    (take k \<Gamma> @ drop (k + length V) \<Gamma>) \<turnstile> subst_all k V t |:| T"
proof (induction \<Gamma> t T arbitrary: k V rule: has_type_L.induct)
  case (has_type_LAbs \<Gamma> T1 t T2)
    note H=this
    have "\<And>i. i < length V \<Longrightarrow>
           \<emptyset>  \<turnstile> shift_L 1 0 (V ! i) |:| (\<Gamma> ! (i + k))"
      proof -
        fix i
        assume inf_len: "i < length V"
        show "\<emptyset>  \<turnstile> shift_L 1 0 (V ! i) |:| (\<Gamma> ! (i + k))"
          using  H(4)[OF inf_len] 
                 FV_ctx[of \<emptyset> "V!i"] shift_only_FV[of "V!i" 0 1]                 
          by force
      qed
    then show ?case
      using H(2)[of "Suc k" "map (shift_L 1 0) V", simplified] H(3)
      by (auto intro:"has_type_L.has_type_LAbs")      
next
  case (has_type_LVar k1 A \<Gamma>) 
    note H=this
    show ?case
      using H(1,2)
            H(3)[of "k1-k"]
            weakening_closed[of "V!(k1-k)" A]
      by (auto intro: has_type_L.has_type_LVar less_diff_conv2)
      
qed (auto intro!: has_type_L.intros simp: has_type_L.simps[of _ "LVar _" _, simplified])


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
    have B:"\<emptyset> |,| T1 \<turnstile> subst_all (Suc 0) (map (shift_L 1 0) V) t |:| T2"
      using substitution_all[OF hyps(1),of "Suc 0" "map (shift_L 1 0) V", 
            simplified] FV_ctx[of \<emptyset>, simplified] shift_only_FV[of "V!_" 0 1] 
            R_def[OF hyps(4)[THEN conjunct2], THEN conjunct2]
            hyps(3)
      by force
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

        have R_sub:"subst_all 0 (v # V) t\<in>\<^sub>RT2"
          using v_prop(1) Rv hyps(4)[unfolded hyps(3)]
                hyps(2)[of "v#V", simplified, OF hyps(3)] 
                less_Suc_eq_0_disj nth_Cons_0 nth_Cons_Suc 
          by force

        have V_no_shift: "map (shift_L 1 0) V = V"
          using shift_only_FV[of _ 0 1, simplified]
                R_def[OF hyps(4)[THEN conjunct2], THEN conjunct1]
          by (simp add: nth_equalityI)
        have ev1:"star eval1_L (LApp (LAbs T1 (subst_all (Suc 0) (map (shift_L 1 0) V) t)) v) 
                             (subst_all 0 (v # V) t)"
          using eval1_LApp_LAbs[OF v_prop(1),of T1 "subst_all (Suc 0) (map (shift_L 1 0) V) t", unfolded
                subst_comp_subst_all[of 0 "shift_L 1 0 v" V t, simplified]]
                shift_only_FV[of "subst_all 0 (v # V) t" 0 "-1",
                               simplified]
                R_def[OF R_sub, THEN conjunct1]
                shift_only_FV[of _ 0 1, simplified, OF R_def[OF Rv, THEN conjunct1]]
                V_no_shift
          by simp    
            
        have ev0:"star eval1_L (LApp (LAbs T1 (subst_all (Suc 0) (map (shift_L 1 0) V) t)) s)
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
        have type: "\<emptyset> \<turnstile> LApp (LAbs T1 (subst_all (Suc 0) (map (shift_L 1 0) V) t)) s |:| T2"
          using B R_def[OF Rs, simplified]
          by (auto intro: "has_type_L.intros")
        
        show "LApp (LAbs T1 (subst_all (Suc 0) (map (shift_L 1 0) V) t)) s\<in>\<^sub>RT2"
          using star_eval_preserves_R[OF star_trans[OF ev0 ev1] type] R_sub
          by metis
      qed
    
    then show ?case
      using eval1_L.simps[of "LAbs T1 _", simplified] 
            has_type_L.intros(3)[OF B] 
            FV_ctx[of \<emptyset> "LAbs T1 (subst_all (Suc 0) (map (shift_L 1 0) V) t)"]
      by auto       
qed (insert R\<^sub>A, auto intro!: has_type_L.intros eval1_L.simps[of ValA, simplified])

theorem Normalization:
  "\<emptyset>\<turnstile> t |:| T \<Longrightarrow> halts t"
using subst_R[of \<emptyset> t T \<emptyset>] R_halts[of t T]
by auto  

end