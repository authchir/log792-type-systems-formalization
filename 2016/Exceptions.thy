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


fun shift_L1 :: "int \<Rightarrow> nat \<Rightarrow> lterm1 \<Rightarrow> lterm1" where
 "shift_L1 d c (LVar1 k)    = LVar1 (if k < c then k else nat (int k + d))" |
 "shift_L1 d c (LApp1 t t1) = LApp1 (shift_L1 d c t) (shift_L1 d c t1)" |
 "shift_L1 d c (LAbs1 T <L:=TL> t)  = LAbs1 T <L:=TL> (shift_L1 d (Suc c) t)" |
 "shift_L1 d c unit1 = unit1" |
 "shift_L1 d c (try t with t1) = try (shift_L1 d c t) with (shift_L1 d c t1)"|
 "shift_L1 d c (raise t) = raise (shift_L1 d c t)"|
 "shift_L1 d c (<s::=t> as A) = <s::=(shift_L1 d c t)> as A"|
 "shift_L1 d c t = t"

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

fun Errors:: "lterm1 \<Rightarrow> lterm1 set" where
 "Errors (LAbs1 T <L:=TL> t) = Errors t" |
 "Errors (LApp1 t1 t2) = Errors t1 \<union> Errors t2"|
 "Errors (try t with t1) = Errors t1"|
 "Errors (raise t) = {t}"|
 "Errors (<s::=t> as A) = Errors t"|
 "Errors _ = {}"
 

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


inductive  has_type1_L :: "ltype \<Rightarrow> lcontext \<Rightarrow> lterm1 \<Rightarrow> ltype \<Rightarrow> bool" ("((_)|*|(_)/ \<turnstile>\<^sub>1 (_)/ |:| (_))" [150, 150, 150] 150) where
  has_type1_Lunit:
    "T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 unit1 |:| Unit" |
  has_type1_LNat:
    "T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 (N n) |:| Ty ''nat''"|
  has_type1_LString:
    "T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 (S s) |:| Ty ''str''"|
  has_type1_LVar:
    "(x, T) |\<in>| \<Gamma> \<Longrightarrow> T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 (LVar1 x) |:| T" |
  has_type1_LAbs_empty:
    "length L>0 \<Longrightarrow>distinct L \<Longrightarrow> length L = length TL \<Longrightarrow> <L:=TL>|*|(\<Gamma> |,| T1) \<turnstile>\<^sub>1 t2 |:| T2 \<Longrightarrow> 
      <\<emptyset>:=\<emptyset>>|*|\<Gamma> \<turnstile>\<^sub>1 (LAbs1 T1 <L:=TL> t2) |:| (T1 \<rightarrow> T2)" |
  has_type1_LAbs_sub:
    " distinct L \<Longrightarrow> length L = length TL \<Longrightarrow> <L:=TL>|*|(\<Gamma> |,| T1) \<turnstile>\<^sub>1 t2 |:| T2 \<Longrightarrow> 
      <L:=TL>|*|\<Gamma> \<turnstile>\<^sub>1 (LAbs1 T1 <L:=TL> t2) |:| (T1 \<rightarrow> T2)" |
  has_type1_LApp:
    "T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 t1 |:| (T11 \<rightarrow> T12) \<Longrightarrow> T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 t2 |:| T11 \<Longrightarrow> T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 (LApp1 t1 t2) |:| T12" |
  has_type1_Variant:
    "i<length L \<Longrightarrow> length L = length TL \<Longrightarrow> T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 t |:| (TL!i) \<Longrightarrow>T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 <(L!i)::=t> as (<L:=TL>) |:| <L:=TL>" |
  has_type1_try:
    "length L = length TL \<Longrightarrow> <L:=TL>|*|\<Gamma> \<turnstile>\<^sub>1 t1 |:| T \<Longrightarrow> <L:=TL>|*|\<Gamma> \<turnstile>\<^sub>1 t2 |:| (<L:=TL>)\<rightarrow>T \<Longrightarrow> <L:=TL>|*|\<Gamma> \<turnstile>\<^sub>1 try t1 with t2 |:| T" |
  has_type1_raise:
    "length L > 0 \<Longrightarrow> length L = length TL \<Longrightarrow> <L:=TL>|*|\<Gamma> \<turnstile>\<^sub>1 t |:| (<L:=TL>) \<Longrightarrow> <L:=TL>|*|\<Gamma> \<turnstile>\<^sub>1 raise t |:| T"

method invert_type = (match premises in H:"Ta|*|\<Gamma> \<turnstile>\<^sub>1 Te |:| A" for Ta \<Gamma> Te A \<Rightarrow>
                        \<open> insert has_type1_L.simps[of Ta \<Gamma> Te A, simplified]\<close>)

lemma canonical_forms1:
  "is_value_L1 v \<Longrightarrow> T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 v |:| Unit \<Longrightarrow> v = unit1"
  "is_value_L1 v \<Longrightarrow> T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 v |:| T1 \<rightarrow> T2 \<Longrightarrow> \<exists>t L TL. v = LAbs1 T1 <L:=TL> t"
  "is_value_L1 v \<Longrightarrow> T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 v |:| <L:=TL> \<Longrightarrow> \<exists>i t. v = (<(L!i)::= t> as (<L:=TL>)) \<and> T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 t |:| (TL!i)"
proof -
  assume val:"is_value_L1 v" and type:"T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 v |:| <L:=TL>"
  then show "\<exists>i t. v = (<(L!i)::= t> as (<L:=TL>)) \<and> T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 t |:| (TL!i)"
    by (induction rule: is_value_L1.induct) (invert_type, blast)+
qed (blast elim: "is_value_L1.cases" has_type1_L.cases)+

lemma progress1:
  "<\<emptyset>:=\<emptyset>>|*|\<emptyset> \<turnstile>\<^sub>1 t |:| T \<Longrightarrow> is_value_L1 t \<or> (\<exists>t'. eval1_L1 t t') \<or> (\<exists>t1. t=raise t1 \<and> is_value_L1 t1) "
proof (induction "<\<emptyset>:=\<emptyset>>::ltype" "\<emptyset>::lcontext" t T rule: has_type1_L.induct)
  case (has_type1_LApp t1 T1 T2 t2)
    note hyps=this
    show ?case 
      using hyps(2,4) eval1_L1.intros(1-3,7-8)
            canonical_forms1(2)[OF _ hyps(1)]
      by metis
next
  case (has_type1_Variant i L TL t)
    note hyps=this
    show ?case 
      using hyps(3,4) "is_value_L1.intros"(5)[of t "L!i"]
            eval1_VE[of t _ "L!i"] has_type1_L.simps[of "<\<emptyset>:=\<emptyset>>" \<emptyset> "raise _", simplified]
      by meson
next
  case (has_type1_try t T t2)
    note hyps=this
    show ?case
      using hyps(3) eval1_L1TryV eval1_L1TryE eval1_TryRaise
      by blast
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

lemma weakening1:
  "T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 t |:| T \<Longrightarrow> n \<le> length \<Gamma> \<Longrightarrow> T\<alpha>|*|insert_nth n U \<Gamma> \<turnstile>\<^sub>1 shift_L1 1 n t |:| T"
proof (induction T\<alpha> \<Gamma> t T arbitrary: n rule: has_type1_L.induct)
  case (has_type1_LAbs_empty L TL \<Gamma> t T1 T2)
    from has_type1_LAbs_empty.prems has_type1_LAbs_empty.hyps(1-)
      has_type1_LAbs_empty.IH[where n="Suc n"] 
    show ?case      
      by (auto intro: has_type1_L.intros)
next
  case (has_type1_LAbs_sub L TL \<Gamma> T1 t T2)
    from has_type1_LAbs_sub.prems has_type1_LAbs_sub.hyps
      has_type1_LAbs_sub.IH[where n="Suc n"] 
    show ?case      
      by (auto intro: has_type1_L.intros)
qed (auto simp: nth_append min_def intro: has_type1_L.intros)



lemma "<\<emptyset>:=\<emptyset>>|*|\<Gamma> \<turnstile>\<^sub>1 t |:| A \<Longrightarrow> Errors t ={}"
proof (induction "<\<emptyset>:=\<emptyset>>::ltype" \<Gamma> t A rule: has_type1_L.induct)
  case (has_type1_LAbs_empty L TL \<Gamma> T1 t T2)
    thus ?case
      sorry
qed simp_all

lemma substitution:
  "T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 t |:| T \<Longrightarrow> T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 LVar1 n |:| U \<Longrightarrow> T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 s |:| U \<Longrightarrow> 
    T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 subst_L1 n s t |:| T"  
proof (induction T\<alpha> \<Gamma> t T arbitrary: s n rule: has_type1_L.induct)
  case (has_type1_LAbs_empty L TL \<Gamma> T1 t T2)
    note hyps=this
    show ?case
      apply simp
      apply rule
      using hyps(1-3)
      apply force+
      using hyps(4,5-) weakening1[where n=0 and U=T1]
            has_type1_L.simps[of _ _ "LVar1 _", simplified] has_type1_LVar
      sorry      
next
  case (has_type1_LAbs_sub L TL T\<alpha> \<Gamma> T1 t T2)
    note hyps=this 
   
    show ?case
      using hyps(1,2,4-)  has_type1_L.simps[of _ _ "LVar1 _", simplified]
            weakening1[where n=0, simplified]
      by (force intro!: "has_type1_L.has_type1_LAbs_sub") 
qed (auto intro!: has_type1_L.intros simp: has_type1_L.simps[of _ _ "LVar1 _" _, simplified])


lemma shift_down:
  "T\<alpha>|*|(insert_nth n U \<Gamma>) \<turnstile>\<^sub>1 t |:| T \<Longrightarrow> n \<le> length \<Gamma> \<Longrightarrow>
   (\<And>x. x \<in> FV1 t \<Longrightarrow> x \<noteq> n) \<Longrightarrow> T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 shift_L1 (- 1) n t |:| T"
proof (induction T\<alpha> "insert_nth n U \<Gamma>" t T arbitrary: \<Gamma> n rule: has_type1_L.induct)
  case (has_type1_LAbs_empty L TL V t T \<Gamma>)
    note hyps=this
    show ?case
      using hyps(1-3,6-) hyps(5)[of "Suc n" "\<Gamma>|,|V"]
      by (fastforce intro: has_type1_L.intros )
next
  case (has_type1_LAbs_sub L TL V t T \<Gamma>)
    note hyps=this
    show ?case
      using hyps(1,2,5-) hyps(4)[of "Suc n" "\<Gamma>|,|V"]
      by (fastforce intro: has_type1_L.intros )     
qed (fastforce intro: has_type1_L.intros simp: nth_append min_def)+


method invert_eval1 = (match premises in H:"eval1_L1 Te Te1" (multi) for Te Te1::lterm1 \<Rightarrow>
                        \<open> insert eval1_L1.simps[of Te Te1, simplified]\<close>)

method raise_solve = (match conclusion in "Ta|*|\<Gamma> \<turnstile>\<^sub>1 raise t |:| A"for Ta \<Gamma> t A \<Rightarrow>
                        \<open> match premises in H:"Ta|*|\<Gamma> \<turnstile>\<^sub>1 raise t |:| B" for B \<Rightarrow>
                           \<open>insert has_type1_L.simps[of Ta \<Gamma> "raise t" B, simplified]
                             \<close>\<close>, (fastforce intro:has_type1_L.intros))


lemma preservation:
  " T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 t |:| T\<Longrightarrow> eval1_L1 t t' \<Longrightarrow> T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 t' |:| T"
proof (induction arbitrary: t' rule: has_type1_L.induct)
  case (has_type1_try L TL \<Gamma> t1 T1 t2)
    note H=this(1-5) and inv_eval= this(6)[unfolded eval1_L1.simps[of "try t1 with t2", simplified]]
    thus ?case  
      by (meson has_type1_L.intros 
                has_type1_L.simps[of "<L:=TL>" \<Gamma> "raise _" T1, simplified])
next
  case (has_type1_LApp T\<alpha> \<Gamma> t1 T1 T2 t2)
    note hyps=this
    have "\<And>L TL T t12. t1 = LAbs1 T <L:=TL> t12 \<Longrightarrow> t'=shift_L1 (-1) 0 (subst_L1 0 (shift_L1 1 0 t2) t12) \<Longrightarrow> ?case"
      proof -
        fix L TL T t12
        assume t'_def:"t' = shift_L1 (- 1) 0 (subst_L1 0 (shift_L1 1 0 t2) t12)"
               and Abs_t1: "t1 = LAbs1 T <L:=TL> t12"
        have t12_type:"<L:=TL>|*|\<Gamma> |,| T1 \<turnstile>\<^sub>1 t12 |:| T2" and 
              T\<alpha>_def : "T\<alpha> = <\<emptyset>:=\<emptyset>> \<or> T\<alpha> = <L:=TL>"
          using hyps(1)[unfolded Abs_t1, simplified]
                has_type1_L.simps[of T\<alpha> \<Gamma> "LAbs1 T <L:=TL> t12" "T1\<rightarrow>T2", simplified]
          by blast+
        have not_free0:"\<And>x. x \<in> FV1 (subst_L1 0 (shift_L1 1 0 t2) t12) \<Longrightarrow> x \<noteq> 0"
          using FV1_subst[of 0 "shift_L1 1 0 t2" t12] 
                FV1_shift[of 1 0 t2, unfolded int_1]
          by (cases "0\<in>FV1 t12") force+
        from t'_def show ?case
          using T\<alpha>_def
          apply auto
          defer
          using substitution[OF t12_type, of 0 T1 "shift_L1 1 0 t2"] 
                shift_down[of _ 0 T1 \<Gamma> _ T2, simplified, unfolded neq0_conv[symmetric]]
                weakening1[OF hyps(2),of 0 T1, simplified]
                not_free0
                "has_type1_L.simps"[of "<L:=TL>" "\<Gamma>|,|T1" "LVar1 0" T1,simplified]
          apply blast
          
          (*by blast  *) sorry
      qed
    with has_type1_LApp show ?case
      by simp (invert_eval1, (meson has_type1_L.intros;(raise_solve|blast)))
qed (raise_solve|(invert_eval1, meson has_type1_L.intros), (raise_solve?))+


end