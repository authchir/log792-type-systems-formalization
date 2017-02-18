theory Exceptions
imports Main "$AFP/List-Index/List_Index" List_extra

begin



datatype ltype=
Unit | Fun ltype ltype (infixr "\<rightarrow>"  225) | VariantType "string list" "ltype list"("<(_):=(_)>" [201,200]225) |
Ty string  

datatype lterm=
  LVar nat 
| LApp lterm lterm 
| LAbs ltype lterm 
| unit
| error


fun shift_L :: "int \<Rightarrow> nat \<Rightarrow> lterm \<Rightarrow> lterm" where
 "shift_L d c (LVar k)    = LVar (if k < c then k else nat (int k + d))" |
 "shift_L d c (LApp t t1) = LApp (shift_L d c t) (shift_L d c t1)" |
 "shift_L d c (LAbs T t)  = LAbs T (shift_L d (Suc c) t)" |
 "shift_L d c error = error" |
 "shift_L d c unit = unit" 


fun subst_L :: "nat \<Rightarrow> lterm \<Rightarrow> lterm \<Rightarrow> lterm" where
 "subst_L j s (LApp t1 t2) = LApp (subst_L j s t1) (subst_L j s t2)" |
 "subst_L j s (LVar k) = (if k = j then s else LVar k)" |
 "subst_L j s (LAbs T t) = LAbs T (subst_L (Suc j) (shift_L 1 0 s) t)"|
 "subst_L j s unit = unit" |
 "subst_L j s (error) = error"

inductive is_value_L :: "lterm \<Rightarrow> bool" where
  "is_value_L unit"|
  "is_value_L (LAbs T t)"


inductive eval1_L :: "lterm \<Rightarrow> lterm \<Rightarrow> bool" where
  -- "Rules relating to the evaluation of function application"
  eval1_LApp1:
    "eval1_L t1 t1' \<Longrightarrow> eval1_L (LApp t1 t2) (LApp t1' t2)" |
  eval1_LApp2:
    "is_value_L v1 \<Longrightarrow> eval1_L t2 t2' \<Longrightarrow> eval1_L (LApp v1 t2) (LApp v1 t2')" |
  eval1_LApp_LAbs:
    "is_value_L v2 \<Longrightarrow> eval1_L (LApp (LAbs T t12) v2)
      (shift_L (-1) 0 (subst_L 0 (shift_L 1 0 v2) t12))" |
  eval1_LErrApp1:
    "eval1_L (LApp error t) error"|
  eval1_LErrApp2:
    "is_value_L v \<Longrightarrow> eval1_L (LApp v error) error" 
 
  

type_synonym lcontext = "ltype list"


notation Nil ("\<emptyset>")
abbreviation cons :: "lcontext \<Rightarrow> ltype \<Rightarrow> lcontext" (infixl "|,|" 200) where
  "cons \<Gamma> T \<equiv> T # \<Gamma>"
abbreviation elem' :: "(nat \<times> ltype) \<Rightarrow> lcontext \<Rightarrow> bool" (infix "|\<in>|" 200) where
  "elem' p \<Gamma> \<equiv> fst p < length \<Gamma> \<and> snd p = nth \<Gamma> (fst p)"


inductive  has_type_L :: "lcontext \<Rightarrow> lterm \<Rightarrow> ltype \<Rightarrow> bool" ("((_)/ \<turnstile> (_)/ |:| (_))" [150, 150, 150] 150) where
  has_type_Lunit:
    "\<Gamma> \<turnstile> unit |:| Unit" |
  has_type_LVar:
    "(x, T) |\<in>| \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> (LVar x) |:| T" |
  has_type_LAbs:
    "(\<Gamma> |,| T1) \<turnstile> t2 |:| T2 \<Longrightarrow> \<Gamma> \<turnstile> (LAbs T1 t2) |:| (T1 \<rightarrow> T2)" |
  has_type_LApp:
    "\<Gamma> \<turnstile> t1 |:| (T11 \<rightarrow> T12) \<Longrightarrow> \<Gamma> \<turnstile> t2 |:| T11 \<Longrightarrow> \<Gamma> \<turnstile> (LApp t1 t2) |:| T12" |
  has_type_error:
    "\<Gamma> \<turnstile> error |:| T"
  
lemma canonical_forms:
  "is_value_L v \<Longrightarrow> \<Gamma> \<turnstile> v |:| Unit \<Longrightarrow> v = unit"
  "is_value_L v \<Longrightarrow> \<Gamma> \<turnstile> v |:| T1 \<rightarrow> T2 \<Longrightarrow> \<exists>t. v = LAbs T1 t"
by (auto elim: has_type_L.cases is_value_L.cases)

primrec FV :: "lterm \<Rightarrow> nat set" where
 "FV unit = {}" |
 "FV error = {}" |
 "FV (LVar x) = {x}" |
 "FV (LAbs T t) = image (\<lambda>x. x - 1) (FV t - {0})" |
 "FV (LApp t1 t2) = FV t1 \<union> FV t2" 

definition is_closed :: "lterm \<Rightarrow> bool" where
  "is_closed t \<equiv> FV t = {}"

(* 14.1.2 with try and raise structure*)
theorem progress:
   "\<emptyset> \<turnstile> t |:| T \<Longrightarrow> is_closed t \<Longrightarrow> (\<forall>t'.\<not> eval1_L t t') \<Longrightarrow> is_value_L t \<or> t=error"
proof (induction t T rule: has_type_L.induct)
  case (has_type_LApp \<Gamma> t1 T11 T12 t2)
    thus ?case 
      by (cases "is_value_L t1", cases "is_value_L t2")
          (auto intro: eval1_L.intros dest: canonical_forms simp: is_closed_def)
qed (simp_all add: is_value_L.intros is_closed_def)


datatype lterm1=
  LVar1 nat 
| LApp1 lterm1 lterm1 
| LAbs1 ltype "string list" "ltype list" lterm1 ("LAbs1/ (_)/ <(_):=(_)>/ (_)" [200,201,200,200] 220)
| unit1
| trapp lterm1 lterm1 ("try/ (_)/ with/ (_)" [181,180]220)
| raise lterm1
| N nat
| S string
| Variant string lterm1 ltype ("<(_)::=(_)>/ as/ (_)" [201,200] 220)

inductive Err_incl::"ltype\<Rightarrow>ltype\<Rightarrow> bool" (infixl "\<sqsubseteq>" 225) where 
 "set(zip L TL) \<subseteq> set (zip L' TL') \<Longrightarrow> length L = length TL \<Longrightarrow> length L' = length TL' \<Longrightarrow> (<L:=TL>)\<sqsubseteq>(<L':=TL'>)"

lemma Err_incl_reflcase:
  "length L = length TL \<Longrightarrow> (<L:=TL>) \<sqsubseteq> (<L:=TL>)"
unfolding Err_incl.simps
by blast

lemma Err_incl_trans:
  "T1 \<sqsubseteq> T2 \<Longrightarrow> T2 \<sqsubseteq> T3 \<Longrightarrow> T1 \<sqsubseteq> T3"
unfolding Err_incl.simps by blast

inductive agrees:: "lterm1 \<Rightarrow> ltype \<Rightarrow> bool" where
  agrees_LAbs:"(<L:=TL>) \<sqsubseteq> (<L':=TL'>) \<Longrightarrow> 
                agrees t (<L:=TL>) \<Longrightarrow> agrees (LAbs1 T1 <L:=TL> t) (<L':=TL'>)"
| agrees_LApp: "agrees t1 (<L:=TL>) \<Longrightarrow> agrees t2 (<L:=TL>) \<Longrightarrow> agrees (LApp1 t1 t2) (<L:=TL>)"
| agrees_trapp: "agrees t1 (<L:=TL>) \<Longrightarrow> agrees t2 (<L:=TL>) \<Longrightarrow> agrees (try t1 with t2) (<L:=TL>)"
| agrees_raise: "agrees t (<L:=TL>) \<Longrightarrow> agrees (raise t) (<L:=TL>)"
| agrees_Vaiant: "agrees t (<L:=TL>) \<Longrightarrow> agrees (<s::=t> as A) (<L:=TL>)"
| agrees_N: "agrees (N n) (<L:=TL>)"
| agrees_S: "agrees (S n) (<L:=TL>)"
| agrees_U: "agrees (unit1) (<L:=TL>)"
| agrees_V: "agrees (LVar1 x) (<L:=TL>)"

fun shift_L1 :: "int \<Rightarrow> nat \<Rightarrow> lterm1 \<Rightarrow> lterm1" where
 "shift_L1 d c (LVar1 k)    = LVar1 (if k < c then k else nat (int k + d))" |
 "shift_L1 d c (LApp1 t t1) = LApp1 (shift_L1 d c t) (shift_L1 d c t1)" |
 "shift_L1 d c (LAbs1 T <L:=TL> t)  = LAbs1 T <L:=TL> (shift_L1 d (Suc c) t)" |
 "shift_L1 d c unit1 = unit1" |
 "shift_L1 d c (try t with t1) = try (shift_L1 d c t) with (shift_L1 d c t1)"|
 "shift_L1 d c (raise t) = raise (shift_L1 d c t)"|
 "shift_L1 d c (<s::=t> as A) = <s::=(shift_L1 d c t)> as A"|
 "shift_L1 d c t = t"

abbreviation join :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'b list \<Rightarrow> ('a\<times>'b)  list" where
  "join L L' TL TL' \<equiv> 
    filter (\<lambda>p. fst p \<notin> set L \<inter> set L' \<or> p \<in> set(zip L TL) \<inter> set (zip L' TL'))
             (zip (L@L') (TL@TL'))"

fun subst_L1 :: "nat \<Rightarrow> lterm1 \<Rightarrow> lterm1 \<Rightarrow> lterm1" where
 "subst_L1 j s (LApp1 t1 t2) = LApp1 (subst_L1 j s t1) (subst_L1 j s t2)" |
 "subst_L1 j s (LVar1 k) = (if k = j then s else LVar1 k)" |
 "subst_L1 j s (LAbs1 T <L:=TL> t) =  LAbs1 T <L:=TL> (subst_L1 (Suc j) (shift_L1 1 0 s) t)"|
 "subst_L1 j s unit1 = unit1" |
 "subst_L1 j s (try t with t1) = try (subst_L1 j s t) with (subst_L1 j s t1)"|
 "subst_L1 j s (raise t) = raise (subst_L1 j s t)"|
 "subst_L1 j s (<s1::=t> as A) = <s1::=(subst_L1 j s t)> as A"|
 "subst_L1 j s t = t"

primrec FV1 :: "lterm1 \<Rightarrow> nat set" where
 "FV1 unit1 = {}" |
 "FV1 (LVar1 x) = {x}" |
 "FV1 (LAbs1 T <L:=TL> t) = image (\<lambda>x. x - 1) (FV1 t - {0})" |
 "FV1 (LApp1 t1 t2) = FV1 t1 \<union> FV1 t2"|
 "FV1 (try t with t1) = FV1 t \<union> FV1 t1"|
 "FV1 (raise t) = FV1 t"|
 "FV1 (<s::=t> as A) = FV1 t"|
 "FV1 (N _) = {}"|
 "FV1 (S _) = {}"

inductive is_value_L1 :: "lterm1 \<Rightarrow> bool" where
  "is_value_L1 unit1"|"is_value_L1 (N _)"|"is_value_L1 (S _)"|
  "is_value_L1 (LAbs1 T <L:=TL> t)" 
  |"is_value_L1 v \<Longrightarrow> is_value_L1 (<s::=v> as A)"


inductive eval1_L1 :: "lterm1 \<Rightarrow> lterm1 \<Rightarrow> bool" where
  -- "Rules relating to the evaluation of function application"
  eval1_L1App1:
    "eval1_L1 t1 t1' \<Longrightarrow> eval1_L1 (LApp1 t1 t2) (LApp1 t1' t2)" |
  eval1_L1App2:
    "is_value_L1 v1 \<Longrightarrow> eval1_L1 t2 t2' \<Longrightarrow> eval1_L1 (LApp1 v1 t2) (LApp1 v1 t2')" |
  eval1_L1App_LAbs:
    "is_value_L1 v2 \<Longrightarrow> eval1_L1 (LApp1 (LAbs1 T <L:=TL> t12) v2)
      (shift_L1 (-1) 0 (subst_L1 0 (shift_L1 1 0 v2) t12))" |
  eval1_VE:
    "eval1_L1 t t' \<Longrightarrow> eval1_L1 (<s::=t> as A) (<s::=t'> as A)"|
  eval1_L1TryV:
    "is_value_L1 v \<Longrightarrow> eval1_L1 (try v with t) v" |
  eval1_L1TryE:
    "eval1_L1 t1 t2 \<Longrightarrow> eval1_L1 (try t1 with t) (try t2 with t)"|
  eval1_L1AppRaise1:
    "is_value_L1 v \<Longrightarrow> eval1_L1 (LApp1 (raise v) t) (raise v)"|
  eval1_L1AppRaise2:
    "is_value_L1 v \<Longrightarrow> is_value_L1 v1 \<Longrightarrow> eval1_L1 (LApp1 v (raise v1)) (raise v1)"|
  eval1_RaiseE:
    "eval1_L1 t t1 \<Longrightarrow> eval1_L1 (raise t) (raise t1)"|
  eval1_RaiseRaise:
    "is_value_L1 v \<Longrightarrow> eval1_L1 (raise (raise v)) (raise v)"|
  eval1_TryRaise:
    "is_value_L1 v \<Longrightarrow> eval1_L1 (try (raise v) with t2) (LApp1 t2 v)"

type_synonym err_ctx = "((string list)\<times>(ltype list)) list"

inductive  has_type1_L :: "err_ctx \<Rightarrow> lcontext \<Rightarrow> lterm1 \<Rightarrow> ltype \<Rightarrow> bool" ("((_)|*|(_)/ \<turnstile>\<^sub>1 (_)/ |:| (_))" [150, 150, 150] 150) where
  has_type1_Lunit:
    "T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 unit1 |:| Unit" |
  has_type1_LNat:
    "T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 (N n) |:| Ty ''nat''"|
  has_type1_LString:
    "T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 (S s) |:| Ty ''str''"|
  has_type1_LVar:
    "(x, T) |\<in>| \<Gamma> \<Longrightarrow> T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 (LVar1 x) |:| T" |
  has_type1_LAbs_empty:
    "distinct L \<Longrightarrow> length L = length TL \<Longrightarrow> agrees t2 (<L:=TL>) \<Longrightarrow> [(L,TL)]|*|(\<Gamma> |,| T1) \<turnstile>\<^sub>1 t2 |:| T2 \<Longrightarrow> 
      \<emptyset>|*|\<Gamma> \<turnstile>\<^sub>1 (LAbs1 T1 <L:=TL> t2) |:| (T1 \<rightarrow> T2)" |
  has_type1_LAbs_sub:
    " distinct L \<Longrightarrow> length L = length TL \<Longrightarrow>(<L:=TL>) \<sqsubseteq> (<L1:=TL1>) \<Longrightarrow> ((L,TL)#T\<alpha>1)|*|(\<Gamma> |,| T1) \<turnstile>\<^sub>1 t2 |:| T2 \<Longrightarrow> 
      ((L1,TL1)#T\<alpha>1)|*|\<Gamma> \<turnstile>\<^sub>1 (LAbs1 T1 <L:=TL> t2) |:| (T1 \<rightarrow> T2)" |
  has_type1_LApp:
    "T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 t1 |:| (T11 \<rightarrow> T12) \<Longrightarrow> T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 t2 |:| T11 \<Longrightarrow> T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 (LApp1 t1 t2) |:| T12" |
  has_type1_Variant:
    "i<length L \<Longrightarrow> length L = length TL \<Longrightarrow> T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 t |:| (TL!i) \<Longrightarrow>T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 <(L!i)::=t> as (<L:=TL>) |:| <L:=TL>" |
  has_type1_try:
    "(<L1:=TL1>) \<sqsubseteq> (<L:=TL>) \<Longrightarrow> ((L,TL)#T\<alpha>)|*|\<Gamma> \<turnstile>\<^sub>1 t1 |:| T \<Longrightarrow> ((L,TL)#T\<alpha>)|*|\<Gamma> \<turnstile>\<^sub>1 t2 |:| (<L1:=TL1>)\<rightarrow>T \<Longrightarrow> ((L,TL)#T\<alpha>)|*|\<Gamma> \<turnstile>\<^sub>1 try t1 with t2 |:| T" |
  has_type1_raise:
    "T\<alpha>1 \<sqsubseteq> (<L:=TL>) \<Longrightarrow> ((L,TL)#T\<alpha>)|*|\<Gamma> \<turnstile>\<^sub>1 t |:| T\<alpha>1 \<Longrightarrow> ((L,TL)#T\<alpha>)|*|\<Gamma> \<turnstile>\<^sub>1 raise t |:| T"

lemma canonical_forms1:
  "is_value_L1 v \<Longrightarrow> T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 v |:| Unit \<Longrightarrow> v = unit1"
  "is_value_L1 v \<Longrightarrow> T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 v |:| T1 \<rightarrow> T2 \<Longrightarrow> \<exists>t L TL. v = LAbs1 T1 <L:=TL> t"
  "is_value_L1 v \<Longrightarrow> T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 v |:| <L:=TL> \<Longrightarrow> \<exists>s t. v = <s::=t> as (<L:=TL>)"
by (auto elim: "is_value_L1.cases" has_type1_L.cases)

lemma progress1:
  "\<emptyset>|*|\<emptyset> \<turnstile>\<^sub>1 t |:| T \<Longrightarrow> is_value_L1 t \<or> (\<exists>t'. eval1_L1 t t')"
proof (induction "\<emptyset>::err_ctx" "\<emptyset>::lcontext" t T rule: has_type1_L.induct)
  case (has_type1_LApp t1 T1 T2 t2)
    note hyps=this
    show ?case 
      using hyps(2,4) eval1_L1.intros(1-3)
            canonical_forms1(2)[OF _ hyps(1)]
      by metis
next
  case (has_type1_Variant i L TL t)
    note hyps=this
    show ?case 
      using hyps(4) "is_value_L1.intros"(5)[of t "L!i"]
            eval1_VE[of t _ "L!i"]
      by auto
qed (simp_all add: is_value_L1.intros)

lemma[simp]: "nat (int x + 1) = Suc x" by simp
lemma[simp]: "nat (1 + int x) = Suc x" by simp
lemma[simp]: "nat (int x - 1) = x - 1" by simp

lemma gr_Suc_conv: "Suc x \<le> n \<longleftrightarrow> (\<exists>m. n = Suc m \<and> x \<le> m)"
  by (cases n) auto

lemma FV1_shift:
  "FV1 (shift_L1 (int d) c t) = image (\<lambda>x. if x \<ge> c then x + d else x) (FV1 t)"
proof (induction t arbitrary: c rule: lterm1.induct)
  case (LAbs1 T E t)
  thus ?case  by (auto simp: gr_Suc_conv image_iff) force+
qed auto

lemma FV1_subst:
  "FV1 (subst_L1 n t u) = (if n \<in> FV1 u then (FV1 u - {n}) \<union> FV1 t else FV1 u)"
proof (induction u arbitrary: n t rule: lterm1.induct)
  case (LAbs1 T L TL u)
    have A: "Suc n \<in> FV1 u \<Longrightarrow> \<exists>x\<in>FV1 u - {0}. n = x - Suc 0 \<Longrightarrow>
              {y. \<exists>x\<in>FV1 u - {Suc n} \<union> {y. \<exists>x\<in>FV1 t. y = Suc x} - {0}. y = x - Suc 0} =
              {y. \<exists>x\<in>FV1 u - {0}. y = x - Suc 0} - {n} \<union> FV1 t"
      by (rule, force) 
          (rule, simp, metis (mono_tags, lifting) Diff_iff Un_iff diff_Suc_Suc 
                              diff_zero mem_Collect_eq nat.simps(3) singletonD)      
    have " Suc n \<in> FV1 u \<Longrightarrow>
          \<forall>x\<in>FV1 u - {0}. n \<noteq> x - Suc 0 \<Longrightarrow>
          {y. \<exists>x\<in>FV1 u - {Suc n} \<union> {y. \<exists>x\<in>FV1 t. y = Suc x} - {0}. y = x - Suc 0} =
          {y. \<exists>x\<in>FV1 u - {0}. y = x - Suc 0}"
      by (rule, rule ,simp , metis (mono_tags, lifting) Diff_iff diff_Suc_Suc diff_zero nat.simps(3) singletonD)+
    
    with A LAbs1 show ?case
      by (auto simp:gr0_conv_Suc image_iff image_def FV1_shift[of 1, unfolded int_1])      
   
qed (auto simp: gr0_conv_Suc image_iff FV1_shift[of 1, unfolded int_1])

method invert_agrees = (match premises in H:"agrees Te A" for Te A \<Rightarrow>
                      \<open> insert H[unfolded agrees.simps[of Te, simplified]]\<close>)

lemma agrees_shift: 
  "agrees t (<L:=TL>) \<Longrightarrow> agrees (shift_L1 d c t) (<L:=TL>)"
proof (induction t arbitrary: d c L TL)
  case (LAbs1 T L' TL' t)
    have "<L':=TL'> \<sqsubseteq> (<L:=TL>) \<and> agrees t (<L':=TL'>) "
      using LAbs1(2)[unfolded "agrees.simps"[of "LAbs1 T <L':=TL'> t" "<L:=TL>"], simplified]
      by blast
    then show ?case
      using agrees_LAbs LAbs1(1)[of L' TL' d "Suc c"]
      by auto     
qed (invert_agrees, force intro: agrees.intros)+

lemma agrees_upper:"agrees s (<L':=TL'>) \<Longrightarrow> <L':=TL'> \<sqsubseteq> (<L:=TL>) \<Longrightarrow> agrees s (<L:=TL>)"
proof(induction arbitrary: L TL rule: agrees.induct)
  case (agrees_LAbs La TLa L' TL' t T)
    note hyps=this
    show ?case
      using Err_incl_trans[OF hyps(1,4)]
            hyps(3)[OF Err_incl_reflcase] "Err_incl.simps"
      by (force intro: agrees.intros)
qed (auto intro: agrees.intros Err_incl.intros) 

lemma agrees_subst: 
  "agrees t (<L:=TL>) \<Longrightarrow> length L = length TL \<Longrightarrow>  agrees s (<\<emptyset>:=\<emptyset>>) \<Longrightarrow> agrees (subst_L1 j s t) (<L:=TL>)"
proof (induction arbitrary: j s L TL rule: agrees.induct)
  case (agrees_LAbs L1 TL1 L' TL' t T)
    note hyps=this
    show ?case
      apply simp
      apply rule
      defer
      using hyps(3)[of _ _ _ "Suc j"] hyps(1)[unfolded "Err_incl.simps"]
            hyps(5,1) agrees_shift
      apply (force intro: agrees.intros)
      apply rule
      using hyps
next
  case (agrees_V k L TL)
    show ?case
      using agrees_upper[OF agrees_V(2), unfolded Err_incl.simps, simplified]
            agrees_V(1)
      by (force intro: agrees.intros)
qed (auto intro: agrees.intros)
(*proof (induction t arbitrary: j s L TL)
  case (LAbs1 T L' TL' t)
    have A:"set (zip L' TL') \<subseteq> set (zip L TL)" "agrees t (<L':=TL'>)" "length L' = length TL'"
            "length L = length TL"
      using LAbs1(3)[unfolded "agrees.simps"[of "LAbs1 T <L':=TL'> t" "<L:=TL>"] "Err_incl.simps"]
      by blast+

    have "\<not> agrees s (<L':=TL'>) \<Longrightarrow> ?case "
      proof -
        assume H: "\<not> agrees s (<L':=TL'>)"
        note H1= H[unfolded "agrees.simps"[of s "<L':=TL'>", simplified], simplified]
        
        then obtain L1 Ta TL1 t1 where s_unfold:"s = LAbs1 Ta <L1:=TL1> t1"
          sorry
        have H2:"set (zip L1 TL1) \<subseteq> set (zip L TL)" "agrees t1 (<L1:=TL1>)"
             "length L1=length TL1"
          using LAbs1(2)[unfolded s_unfold agrees.simps[of "LAbs1 Ta <L1:=TL1> t1", simplified]
                          "Err_incl.simps"]
          by blast+
        have B:"set (zip (map fst (join L' L1 TL' TL1)) (map snd (join L' L1 TL' TL1))) \<subseteq> set (zip L TL)"
          using Collect_restrict set_zip_subset_app[OF A(3) H2(3) A(1) H2(1)]
          by (force simp:fst_map[symmetric] zip_comp[of "join L' L1 TL' TL1",simplified,symmetric]
                         snd_map[symmetric])
        have C:"agrees (LAbs1 Ta <L1:=TL1> shift_L1 1 (Suc 0) t1) (<L1:=TL1>)"
          using H2(1,3) A(4) agrees_shift[OF H2(2)] 
          by (force intro: agrees_LAbs "Err_incl.intros")
        from H show ?case
          using A(4) B
                LAbs1(1)[OF C _,of "Suc j"] 
          by (auto intro!: agrees.intros(1) simp: s_unfold)
      qed
    then show ?case
      using agrees_LAbs[OF A(3,4,1)] 
            LAbs1(1)[OF agrees_shift[OF LAbs1(2),of 1 0] A(2),of "Suc j"]   
      by force
qed 
*)

lemma weakening1:
  "T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 t |:| T \<Longrightarrow> n \<le> length \<Gamma> \<Longrightarrow> T\<alpha>|*|insert_nth n U \<Gamma> \<turnstile>\<^sub>1 shift_L1 1 n t |:| T"
proof (induction T\<alpha> \<Gamma> t T arbitrary: n rule: has_type1_L.induct)
  case (has_type1_LAbs_empty L TL \<Gamma> t T1 T2)
    from has_type1_LAbs_empty.prems has_type1_LAbs_empty.hyps(1-)
      has_type1_LAbs_empty.IH[where n="Suc n"] 
    show ?case      
      by (auto intro: has_type1_L.intros simp: agrees_shift)
next
  case (has_type1_LAbs_sub L t Ta TL \<Gamma> T1 T2)
    from has_type1_LAbs_sub.prems has_type1_LAbs_sub.hyps(1-)
      has_type1_LAbs_sub.IH[where n="Suc n"] 
    show ?case      
      by (auto intro: has_type1_L.intros)
qed (auto simp: nth_append min_def intro: has_type1_L.intros)



method invert_eval1 = (match premises in H:"eval1_L1 Te Te1" (multi) for Te Te1::lterm1 \<Rightarrow>
                      \<open> insert eval1_L1.simps[of Te Te1, simplified]\<close>)

method raise_solve = (match conclusion in "Ta|*|\<Gamma>' \<turnstile>\<^sub>1 raise t |:| A"for Ta \<Gamma>' t A \<Rightarrow>
                        \<open> match premises in H:"Ta|*|\<Gamma>' \<turnstile>\<^sub>1 raise t |:| B" for B \<Rightarrow>
                           \<open>insert has_type1_L.simps[of Ta \<Gamma>' "raise t" B, simplified]
                             \<close>\<close>, meson has_type1_L.intros)

abbreviation sub_ctx :: "err_ctx \<Rightarrow> err_ctx \<Rightarrow> bool" (infixl "\<subseteq>\<^sub>e\<^sub>r\<^sub>r" 225) where
  "Ta \<subseteq>\<^sub>e\<^sub>r\<^sub>r Ta1 \<equiv> (\<forall> i<length Ta. (<fst (Ta!i):=snd (Ta!i)>) \<sqsubseteq> (<fst (Ta1!i):=snd (Ta1!i)>)) \<and> length Ta \<le> length Ta1"

lemma sub_ctx_inv:
  "Ta \<subseteq>\<^sub>e\<^sub>r\<^sub>r Ta1 \<Longrightarrow> (\<forall>i<length Ta. length (fst (Ta!i)) = length (snd (Ta!i)) \<and> 
                                  length (fst (Ta1!i)) = length (snd (Ta1!i)))"
using "Err_incl.simps"
by blast


lemma sub_ctx_refl:
  "(\<forall>i<length Ta. length (fst (Ta ! i)) = length (snd (Ta!i))) \<Longrightarrow> Ta \<subseteq>\<^sub>e\<^sub>r\<^sub>r Ta"
using Err_incl_reflcase
by blast

lemma sub_ctx_trans:
  "T \<subseteq>\<^sub>e\<^sub>r\<^sub>r T1 \<Longrightarrow> T1 \<subseteq>\<^sub>e\<^sub>r\<^sub>r T2 \<Longrightarrow> T \<subseteq>\<^sub>e\<^sub>r\<^sub>r T2"
proof (clarify)
  assume Err_inc:"\<forall>i<length T. <fst (T ! i):=snd (T ! i)> \<sqsubseteq> (<fst (T1 ! i):=snd (T1 ! i)>)"
                  "\<forall>i<length T1. <fst (T1 ! i):=snd (T1 ! i)> \<sqsubseteq> (<fst (T2 ! i):=snd (T2 ! i)>)" 
         and len_assms: "length T \<le> length T1" "length T1 \<le> length T2"
            
  from len_assms have "length T \<le> length T2" using order_trans by blast
  then show ?thesis
    using Err_incl_trans less_le_trans Err_inc len_assms(1)
    by blast
qed

lemma Err_replace_sub:
  "n<length T\<alpha>1 \<Longrightarrow> (<L:=TL>)\<sqsubseteq>(<fst (T\<alpha>!n):=snd(T\<alpha>!n)>) \<Longrightarrow> T\<alpha>1 \<subseteq>\<^sub>e\<^sub>r\<^sub>r T\<alpha>\<Longrightarrow>replace n (L,TL) T\<alpha>1 \<subseteq>\<^sub>e\<^sub>r\<^sub>r T\<alpha>"
proof (cases n)
  case 0
    note H=this
    assume hyps:"n<length T\<alpha>1" "(<L:=TL>)\<sqsubseteq>(<fst (T\<alpha>!n):=snd(T\<alpha>!n)>)"  "T\<alpha>1 \<subseteq>\<^sub>e\<^sub>r\<^sub>r T\<alpha>"
    have "\<And>Ta' T\<alpha>1'. T\<alpha>1 = Ta' # T\<alpha>1' \<Longrightarrow> ((L,TL)#T\<alpha>1') \<subseteq>\<^sub>e\<^sub>r\<^sub>r T\<alpha>"
      proof -
        fix Ta' T\<alpha>1'
        assume h:"T\<alpha>1 = Ta' # T\<alpha>1'"
        have "\<And>i. i<length ((L, TL) # T\<alpha>1') \<Longrightarrow> <fst (((L, TL) # T\<alpha>1') ! i):=snd (((L, TL) # T\<alpha>1') ! i)> \<sqsubseteq>
                (<fst (T\<alpha> ! i):=snd (T\<alpha> ! i)>)"
          proof -
            fix i
            show "i<length ((L, TL) # T\<alpha>1') \<Longrightarrow> <fst (((L, TL) # T\<alpha>1') ! i):=snd (((L, TL) # T\<alpha>1') ! i)> \<sqsubseteq>
                (<fst (T\<alpha> ! i):=snd (T\<alpha> ! i)>)"
              using hyps(2,3)[unfolded h H, simplified]
                    fst_conv snd_conv nth_Cons'[of _ _i]
              by (cases i) fastforce+
          qed
        then show "((L,TL)#T\<alpha>1') \<subseteq>\<^sub>e\<^sub>r\<^sub>r T\<alpha>"
          using hyps(3)[unfolded h, simplified]
          by fastforce
      qed
  with H show "replace n (L,TL) T\<alpha>1 \<subseteq>\<^sub>e\<^sub>r\<^sub>r T\<alpha>"
    by (cases T\<alpha>1) force+
next
  case (Suc k)
    note H= this
    assume hyps:"n<length T\<alpha>1" "(<L:=TL>)\<sqsubseteq>(<fst (T\<alpha>!n):=snd(T\<alpha>!n)>)"  "T\<alpha>1 \<subseteq>\<^sub>e\<^sub>r\<^sub>r T\<alpha>"
    have "length T\<alpha>1 > Suc k" using hyps(1)[unfolded H] by simp
    with H show "replace n (L,TL) T\<alpha>1 \<subseteq>\<^sub>e\<^sub>r\<^sub>r T\<alpha>"
      apply (simp add: min_def)
      apply rule
      defer
      using hyps(3)[THEN conjunct2]
      apply (simp_all add: Suc_diff_Suc Suc_pred numeral_2_eq_2 min_def nat.simps(3) less_Suc_eq)
      using hyps(3)[THEN conjunct1] hyps(2)[unfolded H]
             fst_conv id_take_nth_drop length_take less_Suc0 
             less_Suc_eq less_le_trans not_less nth_Cons' nth_append snd_conv
      
    
      sorry
qed

lemma Err_weak:
  "Ta|*|\<Gamma> \<turnstile>\<^sub>1 t |:| T \<Longrightarrow> Ta \<subseteq>\<^sub>e\<^sub>r\<^sub>r Ta1 \<Longrightarrow> Ta1|*|\<Gamma> \<turnstile>\<^sub>1 t |:| T"
proof (induction arbitrary: Ta1 rule:has_type1_L.induct)
  case (has_type1_LAbs_sub L TL L1 TL1 Ta \<Gamma> T1 t T2)
    note hyps=this and 
        samelen= this(3)[unfolded Err_incl.simps, simplified, THEN conjunct2, THEN conjunct1]

    obtain La TAL TA where Ta1_def:"Ta1 = (La,TAL)#TA"
      using length_Suc_conv hyps(6)[THEN conjunct2, simplified]
      by (metis surj_pair Suc_le_D)

   

    have "\<And>i. i<length ((L, TL) # Ta) \<Longrightarrow> <fst (((L, TL) # Ta) ! i):=snd (((L, TL) # Ta) ! i)> \<sqsubseteq>
                                          (<fst (((L, TL) # TA) ! i):=snd (((L, TL) # TA) ! i)>)"
      proof -
        fix i
        show "i<length ((L, TL) # Ta) \<Longrightarrow> <fst (((L, TL) # Ta) ! i):=snd (((L, TL) # Ta) ! i)> \<sqsubseteq>
                                          (<fst (((L, TL) # TA) ! i):=snd (((L, TL) # TA) ! i)>)"
          using Err_incl_reflcase[OF samelen]
                hyps(6)[unfolded Ta1_def, THEN conjunct1, simplified]
          by (cases i) fastforce+
      qed
      
    
    hence "((L, TL) # Ta) \<subseteq>\<^sub>e\<^sub>r\<^sub>r ((L, TL) # TA)"
      using hyps(6)[unfolded Ta1_def, THEN conjunct2, simplified]
      by simp   
    
    then show ?case
      using hyps(1,2) 
             hyps(6)[unfolded Ta1_def, THEN conjunct1] Err_incl_trans[OF hyps(3)] hyps(5)
      by (force intro!: has_type1_L.intros simp: Ta1_def)   
next
  case (has_type1_LAbs_empty L TL t \<Gamma> T1 T2)
    note hyps=this
    
    have "\<And>Ta Tal. Ta1 = Ta # Tal \<Longrightarrow> Ta1|*|\<Gamma> \<turnstile>\<^sub>1 LAbs1 T1 <L:=TL> t |:| T1 \<rightarrow> T2"
      proof -
        fix Ta TA
        assume h:"Ta1 = Ta # TA"
        
        then obtain La Tal where ta_def:"Ta1 = (La,Tal)#TA"
          by (metis surj_pair)
       
        with ta_def show "Ta1|*|\<Gamma> \<turnstile>\<^sub>1 LAbs1 T1 <L:=TL> t |:| T1 \<rightarrow> T2"
          using hyps(1,2,3) hyps(5)[of "(L, TL) # TA", simplified]
                sorry
      qed
    with hyps show ?case 
      by (cases "Ta1") (force intro!: has_type1_L.intros)+  
next
  case (has_type1_try L1 TL1 L TL Ta \<Gamma> t1 T t2)     
    note hyps=this
    obtain La TaL TA where ta_def:"Ta1 = (La,TaL)#TA" 
      using hyps(6)[THEN conjunct2] length_Suc_conv
      by (metis surj_pair Suc_le_D) 
    then show ?case
      using hyps(6)[unfolded ta_def, THEN conjunct1]
            Err_incl_trans[OF hyps(1), of "<La:=TaL>"]
            hyps(4,5)[OF hyps(6), unfolded ta_def]
      by (force intro!: has_type1_L.intros) 
next
  case (has_type1_raise T\<alpha> L TL Ta \<Gamma> t T)    
    note hyps=this
    obtain La TaL TA where ta_def:"Ta1 = (La,TaL)#TA" 
      using hyps(4)[THEN conjunct2] length_Suc_conv
      by (metis surj_pair Suc_le_D)
    then show ?case
      using hyps(4)[unfolded ta_def, THEN conjunct1]
            Err_incl_trans[OF hyps(1), of "<La:=TaL>"]
            hyps(3)[OF hyps(4), unfolded ta_def]
      by (force intro!: has_type1_L.intros) 
qed (auto intro: has_type1_L.intros)
                                                   
lemma substitution:
  "T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 t |:| T \<Longrightarrow> T\<alpha>1 \<subseteq>\<^sub>e\<^sub>r\<^sub>r T\<alpha> \<Longrightarrow> T\<alpha>1|*|\<Gamma> \<turnstile>\<^sub>1 LVar1 n |:| U \<Longrightarrow> T\<alpha>1|*|\<Gamma> \<turnstile>\<^sub>1 s |:| U \<Longrightarrow> 
    T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 subst_L1 n s t |:| T"  
proof (induction T\<alpha> \<Gamma> t T arbitrary: s n T\<alpha>1 rule: has_type1_L.induct)
  case (has_type1_LAbs_empty L TL t \<Gamma> T1 T2)
    note hyps=this
    have "agrees (subst_L1 (Suc n) (shift_L1 1 0 s) t) (<L:=TL>)" 
      using agrees_subst agrees_shift[of s L TL 1 0]
            hyps(1-8)
      sorry
    then show ?case
      using hyps(1,2,6-) 
            weakening1[where n=0, simplified]
            hyps(5)[of T\<alpha>1 "Suc n" "shift_L1 1 0 s"]            
      by (fastforce intro: "has_type1_L.has_type1_LAbs_empty")
next
  case (has_type1_LAbs_sub L TL L1 TL1 T\<alpha> \<Gamma> T1 t T2)
    note hyps=this 
    have "\<And>Ta' T\<alpha>1'. T\<alpha>1 = Ta' # T\<alpha>1' \<Longrightarrow> ((L,TL)#T\<alpha>1') \<subseteq>\<^sub>e\<^sub>r\<^sub>r ((L,TL)#T\<alpha>)"
      proof -
        fix Ta' T\<alpha>1'
        assume h:"T\<alpha>1 = Ta' # T\<alpha>1'"
        have "\<And>i. i<length ((L, TL) # T\<alpha>1') \<Longrightarrow> <fst (((L, TL) # T\<alpha>1') ! i):=snd (((L, TL) # T\<alpha>1') ! i)> \<sqsubseteq>
                (<fst (((L, TL) # T\<alpha>) ! i):=snd (((L, TL) # T\<alpha>) ! i)>)"
          proof -
            fix i
            show "i<length ((L, TL) # T\<alpha>1') \<Longrightarrow> <fst (((L, TL) # T\<alpha>1') ! i):=snd (((L, TL) # T\<alpha>1') ! i)> \<sqsubseteq>
                (<fst (((L, TL) # T\<alpha>) ! i):=snd (((L, TL) # T\<alpha>) ! i)>)"
              using hyps(6)[unfolded h] hyps(3)[unfolded Err_incl.simps, simplified] Err_incl_reflcase[of L TL]
                    fst_conv snd_conv nth_Cons'[of _ _i]
              by (cases i) fastforce+
          qed
        then show "((L,TL)#T\<alpha>1') \<subseteq>\<^sub>e\<^sub>r\<^sub>r ((L,TL)#T\<alpha>)"
          using hyps(6)[unfolded h, THEN conjunct2]
          by fastforce
      qed
                
    hence A:"replace 0 (L,TL) T\<alpha>1 \<subseteq>\<^sub>e\<^sub>r\<^sub>r ((L, TL) # T\<alpha>)"
      by (cases T\<alpha>1) force+     
      
    show ?case
      apply simp
      apply rule
      using hyps(1-3)
      apply force+ 
      using hyps(7-) 
            weakening1[where n=0, simplified]
            hyps(5)[OF A, of "Suc n" "shift_L1 1 0 s"]
            
      (*by (fastforce intro: "has_type1_L.has_type1_LAbs_sub")*) sorry
next
  case (has_type1_LVar k A \<Gamma> Ta)
    note hyps=this 
    show ?case
      using hyps(1) Err_weak
            hyps(3)[unfolded has_type1_L.simps[of _ _ "LVar1 _" _, simplified]]
      by (force intro: "has_type1_L.intros")
      
qed (auto intro!: has_type1_L.intros simp: has_type1_L.simps[of _ _ "LVar1 _" _, simplified])


lemma shift_down:
  "T\<alpha>|*|(insert_nth n U \<Gamma>) \<turnstile>\<^sub>1 t |:| T \<Longrightarrow> n \<le> length \<Gamma> \<Longrightarrow>
   (\<And>x. x \<in> FV1 t \<Longrightarrow> x \<noteq> n) \<Longrightarrow> T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 shift_L1 (- 1) n t |:| T"
proof (induction T\<alpha> "insert_nth n U \<Gamma>" t T arbitrary: \<Gamma> n rule: has_type1_L.induct)
  case (has_type1_LAbs L t TL V T T\<alpha>)
    note hyps=this
    have "agrees (shift_L1 (- 1) (Suc n) t) (<L:=TL>)"
      using hyps(2) agrees_shift
      by auto
    
    with hyps(1,5-) show ?case
      by (fastforce intro: has_type1_L.intros hyps(4)[of "Suc n" "\<Gamma>|,|V"])     
qed (fastforce intro: has_type1_L.intros simp: nth_append min_def)+




lemma preservation:
  " T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 t |:| T\<Longrightarrow> eval1_L1 t t' \<Longrightarrow> T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 t' |:| T"
proof (induction arbitrary: t' rule: has_type1_L.induct)
  case (has_type1_try T\<alpha> \<Gamma> t1 T1 t2)
    note H=this and inv_eval= this(5)[unfolded eval1_L1.simps[of "try t1 with t2", simplified]]
    thus ?case  
      by (meson has_type1_L.intros 
                has_type1_L.simps[of T\<alpha> \<Gamma> "raise _" T1, simplified])
next
  case (has_type1_LApp T\<alpha> \<Gamma> t1 T1 T2 t2)
    note hyps=this
    have "\<And>L TL T t12. t1 = LAbs1 T <L:=TL> t12 \<Longrightarrow> t'=shift_L1 (-1) 0 (subst_L1 0 (shift_L1 1 0 t2) t12) \<Longrightarrow> ?case"
      proof -
        fix L TL T t12
        assume t'_def:"t' = shift_L1 (- 1) 0 (subst_L1 0 (shift_L1 1 0 t2) t12)"
               and Abs_t1: "t1 = LAbs1 T <L:=TL> t12"
        have t12_type:"<L:=TL>|*|\<Gamma> |,| T1 \<turnstile>\<^sub>1 t12 |:| T2"
          using hyps(1)[unfolded Abs_t1, simplified]
                has_type1_L.simps[of T\<alpha> \<Gamma> "LAbs1 T <L:=TL> t12" "T1\<rightarrow>T2", simplified]
          by blast
        have not_free0:"\<And>x. x \<in> FV1 (subst_L1 0 (shift_L1 1 0 t2) t12) \<Longrightarrow> x \<noteq> 0"
          using FV1_subst[of 0 "shift_L1 1 0 t2" t12] 
                FV1_shift[of 1 0 t2, unfolded int_1]
          by (cases "0\<in>FV1 t12") force+
        from t'_def show ?case
          using substitution[OF t12_type, of 0 T1 "shift_L1 1 0 t2"] 
            shift_down[of _ 0 T1 \<Gamma> _ T2, simplified, unfolded neq0_conv[symmetric]]
            weakening1[OF hyps(2),of 0 T1, simplified]
            not_free0
            "has_type1_L.simps"[of T\<alpha> "\<Gamma>|,|T1" "LVar1 0" T1, simplified]
          (*by blast  *) sorry
      qed
    with has_type1_LApp show ?case
      by simp (invert_eval1, (meson has_type1_L.intros;(raise_solve|blast)))
qed (raise_solve|(invert_eval1, meson has_type1_L.intros), (raise_solve?))+


end