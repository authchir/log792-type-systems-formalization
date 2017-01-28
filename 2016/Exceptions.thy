theory Exceptions
imports Main "$AFP/List-Index/List_Index"

begin

datatype ltype=
Unit | Fun ltype ltype (infixr "\<rightarrow>"  225)

datatype lterm=
  LVar nat 
| LApp lterm lterm 
| LAbs ltype lterm 
| unit
| error
| trapp lterm lterm ("try/ (_)/ with/ (_)" [181,180]220)
| raise lterm

fun shift_L :: "int \<Rightarrow> nat \<Rightarrow> lterm \<Rightarrow> lterm" where
 "shift_L d c (LVar k)    = LVar (if k < c then k else nat (int k + d))" |
 "shift_L d c (LApp t t1) = LApp (shift_L d c t) (shift_L d c t1)" |
 "shift_L d c (LAbs T t)  = LAbs T (shift_L d (Suc c) t)" |
 "shift_L d c error = error" |
 "shift_L d c unit = unit" |
 "shift_L d c (try t with t1) = try (shift_L d c t) with (shift_L d c t1)"|
 "shift_L d c (raise t) = raise (shift_L d c t)"

fun subst_L :: "nat \<Rightarrow> lterm \<Rightarrow> lterm \<Rightarrow> lterm" where
 "subst_L j s (LApp t1 t2) = LApp (subst_L j s t1) (subst_L j s t2)" |
 "subst_L j s (LVar k) = (if k = j then s else LVar k)" |
 "subst_L j s (LAbs T t) = LAbs T (subst_L (Suc j) (shift_L 1 0 s) t)"|
 "subst_L j s unit = unit" |
 "subst_L j s (error) = error"|
 "subst_L j s (try t with t1) = try (subst_L j s t) with (subst_L j s t1)"|
 "subst_L j s (raise t) = raise (subst_L j s t)"
 
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
    "is_value_L v \<Longrightarrow> eval1_L (LApp v error) error" |
  eval1_LTryV:
    "is_value_L v \<Longrightarrow> eval1_L (try v with t) v" |
  eval1_LTryE:
    "eval1_L t1 t2 \<Longrightarrow> eval1_L (try t1 with t) (try t2 with t)"|
  eval1_LTryErr:
    "eval1_L (try error with t) t"|
  eval1_LAppRaise1:
    "is_value_L v \<Longrightarrow> eval1_L (LApp (raise v) t) (raise v)"|
  eval1_LAppRaise2:
    "is_value_L v \<Longrightarrow> is_value_L v1 \<Longrightarrow> eval1_L (LApp v (raise v1)) (raise v1)"|
  eval1_RaiseE:
    "eval1_L t t1 \<Longrightarrow> eval1_L (raise t) (raise t1)"|
  eval1_RaiseRaise:
    "is_value_L v \<Longrightarrow> eval1_L (raise (raise v)) (raise v)"|
  eval1_TryRaise:
    "is_value_L v \<Longrightarrow> eval1_L (try (raise v) with t2) (LApp t2 v)"
  
  

type_synonym lcontext = "ltype list"


notation Nil ("\<emptyset>")
abbreviation cons :: "lcontext \<Rightarrow> ltype \<Rightarrow> lcontext" (infixl "|,|" 200) where
  "cons \<Gamma> T \<equiv> T # \<Gamma>"
abbreviation elem' :: "(nat \<times> ltype) \<Rightarrow> lcontext \<Rightarrow> bool" (infix "|\<in>|" 200) where
  "elem' p \<Gamma> \<equiv> fst p < length \<Gamma> \<and> snd p = nth \<Gamma> (fst p)"


inductive has_type_L :: "lcontext \<Rightarrow> lterm \<Rightarrow> ltype \<Rightarrow> bool" ("((_)/ \<turnstile> (_)/ |:| (_))" [150, 150, 150] 150) where
  has_type_Lunit:
    "\<Gamma> \<turnstile> unit |:| Unit" |
  has_type_LVar:
    "(x, T) |\<in>| \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> (LVar x) |:| T" |
  has_type_LAbs:
    "(\<Gamma> |,| T1) \<turnstile> t2 |:| T2 \<Longrightarrow> \<Gamma> \<turnstile> (LAbs T1 t2) |:| (T1 \<rightarrow> T2)" |
  has_type_LApp:
    "\<Gamma> \<turnstile> t1 |:| (T11 \<rightarrow> T12) \<Longrightarrow> \<Gamma> \<turnstile> t2 |:| T11 \<Longrightarrow> \<Gamma> \<turnstile> (LApp t1 t2) |:| T12" |
  has_type_error:
    "\<Gamma> \<turnstile> error |:| T"|
  has_type_try:
    "\<Gamma> \<turnstile> t1 |:| T \<Longrightarrow> \<Gamma> \<turnstile> t2 |:| T \<Longrightarrow> \<Gamma> \<turnstile> try t1 with t2 |:| T"

lemma canonical_forms:
  "is_value_L v \<Longrightarrow> \<Gamma> \<turnstile> v |:| Unit \<Longrightarrow> v = unit"
  "is_value_L v \<Longrightarrow> \<Gamma> \<turnstile> v |:| T1 \<rightarrow> T2 \<Longrightarrow> \<exists>t. v = LAbs T1 t"
by (auto elim: has_type_L.cases is_value_L.cases)

primrec FV :: "lterm \<Rightarrow> nat set" where
 "FV unit = {}" |
 "FV error = {}" |
 "FV (LVar x) = {x}" |
 "FV (LAbs T t) = image (\<lambda>x. x - 1) (FV t - {0})" |
 "FV (LApp t1 t2) = FV t1 \<union> FV t2"|
 "FV (try t with t1) = FV t \<union> FV t1"|
 "FV (raise t) = FV t"

definition is_closed :: "lterm \<Rightarrow> bool" where
  "is_closed t \<equiv> FV t = {}"

(* 14.1.2 with try and raise structure*)
theorem progress:
   "\<emptyset> \<turnstile> t |:| T \<Longrightarrow> is_closed t \<Longrightarrow> (\<forall>t'.\<not> eval1_L t t') \<Longrightarrow> is_value_L t \<or> t=error \<or> 
                                      (\<exists>t1 t2. t=try t1 with t2)"
proof (induction t T rule: has_type_L.induct)
  case (has_type_LApp \<Gamma> t1 T11 T12 t2)
    thus ?case sorry
    (*by (cases "is_value_L t1", cases "is_value_L t2")
      (auto intro: eval1_L.intros dest: canonical_forms simp: is_closed_def)*)
qed (simp_all add: is_value_L.intros is_closed_def)

end