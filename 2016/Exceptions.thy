theory Exceptions
imports Main "$AFP/List-Index/List_Index"

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
| Variant string lterm1 ("<(_)::=(_)>" [201,200] 220)

fun shift_L1 :: "int \<Rightarrow> nat \<Rightarrow> lterm1 \<Rightarrow> lterm1" where
 "shift_L1 d c (LVar1 k)    = LVar1 (if k < c then k else nat (int k + d))" |
 "shift_L1 d c (LApp1 t t1) = LApp1 (shift_L1 d c t) (shift_L1 d c t1)" |
 "shift_L1 d c (LAbs1 T <L:=TL> t)  = LAbs1 T <L:=TL> (shift_L1 d (Suc c) t)" |
 "shift_L1 d c unit1 = unit1" |
 "shift_L1 d c (try t with t1) = try (shift_L1 d c t) with (shift_L1 d c t1)"|
 "shift_L1 d c (raise t) = raise (shift_L1 d c t)"|
 "shift_L1 d c (<s::=t>) = <s::=(shift_L1 d c t)>"|
 "shift_L1 d c t = t"

fun subst_L1 :: "nat \<Rightarrow> lterm1 \<Rightarrow> lterm1 \<Rightarrow> lterm1" where
 "subst_L1 j s (LApp1 t1 t2) = LApp1 (subst_L1 j s t1) (subst_L1 j s t2)" |
 "subst_L1 j s (LVar1 k) = (if k = j then s else LVar1 k)" |
 "subst_L1 j s (LAbs1 T <L:=TL> t) = LAbs1 T <L:=TL> (subst_L1 (Suc j) (shift_L1 1 0 s) t)"|
 "subst_L1 j s unit1 = unit1" |
 "subst_L1 j s (try t with t1) = try (subst_L1 j s t) with (subst_L1 j s t1)"|
 "subst_L1 j s (raise t) = raise (subst_L1 j s t)"|
 "subst_L1 j s (<s1::=t>) = <s1::=(subst_L1 j s t)>"|
 "subst_L1 j s t = t"

primrec FV1 :: "lterm1 \<Rightarrow> nat set" where
 "FV1 unit1 = {}" |
 "FV1 (LVar1 x) = {x}" |
 "FV1 (LAbs1 T <L:=TL> t) = image (\<lambda>x. x - 1) (FV1 t - {0})" |
 "FV1 (LApp1 t1 t2) = FV1 t1 \<union> FV1 t2"|
 "FV1 (try t with t1) = FV1 t \<union> FV1 t1"|
 "FV1 (raise t) = FV1 t"|
 "FV1 (<s::=t>) = FV1 t"|
 "FV1 (N _) = {}"|
 "FV1 (S _) = {}"

inductive is_value_L1 :: "lterm1 \<Rightarrow> bool" where
  "is_value_L1 unit1"|"is_value_L1 (N _)"|"is_value_L1 (S _)"|
  "is_value_L1 (LAbs1 T <L:=TL> t)" 
  |"is_value_L1 v \<Longrightarrow> is_value_L1 (<s::=v>)"


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
    "eval1_L1 t t' \<Longrightarrow> eval1_L1 (<s::=t>) (<s::=t'>)"|
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

abbreviation agrees:: "lterm1 \<Rightarrow> ltype \<Rightarrow> bool" where
 "agrees t T \<equiv> (case t of LAbs1 Ta <L:=TL> t' \<Rightarrow> (<L:=TL>)=T | _\<Rightarrow> True)"

inductive  has_type1_L :: "ltype \<Rightarrow> lcontext \<Rightarrow> lterm1 \<Rightarrow> ltype \<Rightarrow> bool" ("((_)|*|(_)/ \<turnstile>\<^sub>1 (_)/ |:| (_))" [150, 150, 150] 150) where
  has_type1_Lunit:
    "T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 unit1 |:| Unit" |
  has_type1_LNat:
    "T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 (N n) |:| Ty ''nat''"|
  has_type1_LString:
    "T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 (S s) |:| Ty ''str''"|
  has_type1_LVar:
    "(x, T) |\<in>| \<Gamma> \<Longrightarrow> T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 (LVar1 x) |:| T" |
  has_type1_LAbs:
    "distinct L \<Longrightarrow> agrees t2 (<L:=TL>) \<Longrightarrow> <L:=TL>|*|(\<Gamma> |,| T1) \<turnstile>\<^sub>1 t2 |:| T2 \<Longrightarrow> T\<alpha>1|*|\<Gamma> \<turnstile>\<^sub>1 (LAbs1 T1 <L:=TL> t2) |:| (T1 \<rightarrow> T2)" |
  has_type1_LApp:
    "T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 t1 |:| (T11 \<rightarrow> T12) \<Longrightarrow> T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 t2 |:| T11 \<Longrightarrow> T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 (LApp1 t1 t2) |:| T12" |
  has_type1_Variant:
    "L!i = s \<Longrightarrow> TL!i= A \<Longrightarrow> T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 t |:| A \<Longrightarrow>T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 <s::=t> |:| <L:=TL>" |
  has_type1_try:
    "T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 t1 |:| T \<Longrightarrow> T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 t2 |:| T\<alpha>\<rightarrow>T \<Longrightarrow> T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 try t1 with t2 |:| T" |
  has_type1_raise:
    "T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 t |:| T\<alpha> \<Longrightarrow> T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 raise t |:| T"

lemma canonical_forms1:
  "is_value_L1 v \<Longrightarrow> T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 v |:| Unit \<Longrightarrow> v = unit1"
  "is_value_L1 v \<Longrightarrow> T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 v |:| T1 \<rightarrow> T2 \<Longrightarrow> \<exists>t L TL. v = LAbs1 T1 <L:=TL> t"
by (auto elim: "is_value_L1.cases" has_type1_L.cases)

lemma progress1:
  "<\<emptyset>:=\<emptyset>>|*|\<emptyset> \<turnstile>\<^sub>1 t |:| T \<Longrightarrow> is_value_L1 t \<or> (\<exists>t'. eval1_L1 t t')"
sorry


lemma preservation:
  "T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 t |:| T \<Longrightarrow> eval1_L1 t t' \<Longrightarrow> T\<alpha>|*|\<Gamma> \<turnstile>\<^sub>1 t' |:| T"
sorry

end