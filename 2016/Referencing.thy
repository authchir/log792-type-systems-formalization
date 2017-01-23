theory Referencing
imports Main  "$AFP/List-Index/List_Index"
begin
  
datatype ltype=
  Unit | Fun ltype ltype (infixr "\<rightarrow>"  225) | Ref ltype

datatype lterm=
  LVar nat 
| LApp lterm lterm 
| LAbs ltype lterm 
| unit
| ref lterm
| deref lterm ("!(_)" 200)
| assign lterm lterm ("(_)::=(_)" [100,195] 220)
| L nat

fun shift_L :: "int \<Rightarrow> nat \<Rightarrow> lterm \<Rightarrow> lterm" where
 "shift_L d c (ref t) = ref (shift_L d c t)"|
 "shift_L d c (t1::=t2) = t1::=(shift_L d c t2)"|
 "shift_L d c (LVar k)    = LVar (if k < c then k else nat (int k + d))" |
 "shift_L d c (LApp t t1) = LApp (shift_L d c t) (shift_L d c t1)" |
 "shift_L d c (LAbs T t)  = LAbs T (shift_L d (Suc c) t)" |
 "shift_L d c t = t" 

fun subst_L :: "nat \<Rightarrow> lterm \<Rightarrow> lterm \<Rightarrow> lterm" where
  "subst_L j s (ref t) = ref (subst_L j s t)"|
  "subst_L j s (t1::=t2) = t1::=(subst_L j s t2)"|
  "subst_L j s (LApp t1 t2) = LApp (subst_L j s t1) (subst_L j s t2)" |
  "subst_L j s (LVar k) = (if k = j then s else LVar k)" |
  "subst_L j s (LAbs T t) = LAbs T (subst_L (Suc j) (shift_L 1 0 s) t)"|
  "subst_L j s t = t"

fun FV ::"lterm \<Rightarrow> nat set" where
  "FV (LVar k) = {k}"|
  "FV (LApp t1 t2) = FV t1 \<union> FV t2"|
  "FV (LAbs T t) =  image (\<lambda>x. x - 1) (FV t - {0})" |
  "FV (t1::=t2) = FV t2"|
  "FV _ = {}"

inductive is_value_L:: "lterm \<Rightarrow> bool" where
  "is_value_L unit"
| "is_value_L (L n)" 
| "is_value_L (LAbs T t)"

type_synonym lstore   = "lterm list"

abbreviation consS :: "lstore \<Rightarrow> lterm \<Rightarrow> lstore" (infixl "|\<leftarrow>|" 200) where
  "\<mu>|\<leftarrow>|v \<equiv> \<mu>@[v]"

inductive eval1_L :: "lterm \<Rightarrow> lstore \<Rightarrow> lterm \<Rightarrow> lstore \<Rightarrow> bool" where
   -- "Rules relating to the evaluation of function application"
  eval1_LApp1:
    "eval1_L t1 \<mu> t1' \<mu>' \<Longrightarrow> eval1_L (LApp t1 t2) \<mu> (LApp t1' t2) \<mu>'" |
  eval1_LApp2:
    "is_value_L v1 \<Longrightarrow> eval1_L t2 \<mu> t2' \<mu>'\<Longrightarrow> eval1_L (LApp v1 t2) \<mu> (LApp v1 t2') \<mu>'" |
  eval1_LApp_LAbs:
    "is_value_L v2 \<Longrightarrow> eval1_L (LApp (LAbs T' t12) v2) \<mu>
      (shift_L (-1) 0 (subst_L 0 (shift_L 1 0 v2) t12)) \<mu>" | 
  eval1_LRefV:
    "is_value_L v \<Longrightarrow> eval1_L (ref v) \<mu> (Loc (length \<mu>)) (\<mu>|\<leftarrow>|v)" |
  eval1_LRef:
    "eval1_L t1 \<mu> t1' \<mu>' \<Longrightarrow> eval1_L (ref t1) \<mu> (ref t1') \<mu>'" |
  eval1_LDerefLoc:
    "n<length \<mu> \<Longrightarrow> is_value_L (\<mu>!n) \<Longrightarrow> eval1_L (!(Loc n)) \<mu> (\<mu>!n) \<mu>" |
  eval1_LDeref:
    "eval1_L t1 \<mu> t1' \<mu>' \<Longrightarrow> eval1_L (!t1) \<mu> (!t1') \<mu>'" |
  eval1_LAssignLoc:
    "is_value_L v \<Longrightarrow> eval1_L (Loc n::=v) \<mu> unit (\<mu>[n:=v])"|
  eval1_LAssign1:
    "eval1_L t1 \<mu> t1' \<mu>' \<Longrightarrow> eval1_L (t1::=t2) \<mu> (t1'::=t2) \<mu>'" |
  eval1_LAssign2:
    "is_value_L v1 \<Longrightarrow> eval1_L t2 \<mu> t2' \<mu>'\<Longrightarrow> eval1_L (v1::=t2) \<mu> (v1::=t2') \<mu>'"


inductive_cases eval1_LAppE: "eval1_L (LApp t1 t2) \<mu> t' \<mu>'"

type_synonym lcontext = "ltype list"
type_synonym loc_ctx   = "ltype list"

notation Nil ("\<emptyset>")
abbreviation cons :: "lcontext \<Rightarrow> ltype \<Rightarrow> lcontext" (infixl "|,|" 200) where
  "cons \<Gamma> T' \<equiv> T' # \<Gamma>"
abbreviation elem' :: "(nat \<times> ltype) \<Rightarrow> lcontext \<Rightarrow> bool" (infix "|\<in>|" 200) where
  "elem' p \<Gamma> \<equiv> fst p < length \<Gamma> \<and> snd p = nth \<Gamma> (fst p)"

abbreviation consLoc :: "loc_ctx \<Rightarrow> ltype \<Rightarrow> loc_ctx" (infixl "|,|\<^sub>l" 200) where
  "\<Sigma> |,|\<^sub>l T' \<equiv> \<Sigma>@[T']"
abbreviation elemLoc :: "(nat \<times> ltype) \<Rightarrow> loc_ctx \<Rightarrow> bool" (infix "|\<in>\<^sub>l|" 200) where
  "elemLoc p \<Sigma> \<equiv> fst p < length \<Sigma> \<and> snd p = nth \<Sigma> (fst p)"


text{*  For the typing rule of letbinder, we require to replace the type 
        of the variable by the expected type 
    *}


inductive has_type_L :: "lcontext \<Rightarrow> loc_ctx \<Rightarrow> lterm \<Rightarrow> ltype \<Rightarrow> bool" ("((_)|;|(_)/ \<turnstile> (_)/ |:| (_))" [150,150, 150] 150) where
  -- "Rules relating to the type of Unit"
  has_type_Lunit:
    "\<Gamma>|;|\<Sigma> \<turnstile> unit |:| Unit"|
  -- \<open>Rules relating to the type of the constructs of the $\lambda$-calculus\<close>
  has_type_LVar:
    "(x, T') |\<in>| \<Gamma> \<Longrightarrow> \<Gamma>|;|\<Sigma> \<turnstile> LVar x |:| (T')" |
  has_type_LAbs:
    "(\<Gamma> |,| T1)|;|\<Sigma> \<turnstile> t2 |:| T2 \<Longrightarrow> \<Gamma>|;|\<Sigma> \<turnstile> LAbs T1 t2 |:| (T1 \<rightarrow> T2)" |
  has_type_LApp:
    "\<Gamma>|;|\<Sigma> \<turnstile> t1 |:| T11 \<rightarrow> T12 \<Longrightarrow> \<Gamma>|;|\<Sigma> \<turnstile> t2 |:| T11 \<Longrightarrow> \<Gamma>|;|\<Sigma> \<turnstile> LApp t1 t2 |:| T12" |
  has_type_Loc:
    "(n,T1) |\<in>\<^sub>l| \<Sigma> \<Longrightarrow> \<Gamma>|;|\<Sigma> \<turnstile> L n |:| Ref T1" |
  has_type_Ref:
    "\<Gamma>|;|\<Sigma> \<turnstile> t |:| T1 \<Longrightarrow> \<Gamma>|;|\<Sigma> \<turnstile> ref t |:| Ref T1"|
  has_type_Deref:
    "\<Gamma>|;|\<Sigma> \<turnstile> t |:| Ref T1 \<Longrightarrow> \<Gamma>|;|\<Sigma> \<turnstile> !t |:| T1"|
  has_type_Assign:
    "\<Gamma>|;|\<Sigma> \<turnstile> t1 |:| Ref T1 \<Longrightarrow> \<Gamma>|;|\<Sigma> \<turnstile> t2 |:| T1 \<Longrightarrow> \<Gamma>|;|\<Sigma> \<turnstile> (t1::=t2) |:| Unit"

lemma canonical_forms:
  "is_value_L v \<Longrightarrow> \<Gamma>|;|\<Sigma> \<turnstile> v |:| Unit \<Longrightarrow> v = unit"
  "is_value_L v \<Longrightarrow> \<Gamma>|;|\<Sigma> \<turnstile> v |:| T1 \<rightarrow> T2 \<Longrightarrow> \<exists>t. v = LAbs T1 t"
  "is_value_L v \<Longrightarrow> \<Gamma>|;|\<Sigma> \<turnstile> v |:| Ref T1 \<Longrightarrow>\<exists>n. n<length \<Sigma> \<and> v = L n \<and> \<Sigma>!n=T1"  
by (auto elim: has_type_L.cases is_value_L.cases)

abbreviation well_typed_store::"lcontext \<Rightarrow> loc_ctx \<Rightarrow> lstore \<Rightarrow> bool" ("(_)|;|(_) \<Turnstile> (_)" [150,150,190] 200) where
"\<Gamma>|;|\<Sigma> \<Turnstile> \<mu> \<equiv> (length \<Sigma> = length \<mu>) \<and> (\<forall>i<length \<Sigma>. \<Gamma>|;|\<Sigma> \<turnstile> (\<mu>!i) |:| (\<Sigma>!i))"

lemma substitution:
  "\<Gamma> |;|\<Sigma> \<turnstile> t |:| T \<Longrightarrow>  \<Gamma>|;|\<Sigma> \<turnstile> LVar n |:| S \<Longrightarrow> \<Gamma>|;|\<Sigma> \<turnstile> s |:| S \<Longrightarrow> \<Gamma>|;|\<Sigma> \<turnstile> subst_L n s t |:| T"  
sorry

lemma storing_updt:
  "\<Gamma> |;|\<Sigma> \<Turnstile> \<mu> \<Longrightarrow> i<length \<Sigma> \<Longrightarrow> \<Sigma>!i = T \<Longrightarrow> \<Gamma> |;|\<Sigma> \<turnstile> v |:| T \<Longrightarrow> \<Gamma> |;|\<Sigma> \<Turnstile> (\<mu>[i:=v])"
sorry

lemma store_weakening:
  "\<Gamma> |;|\<Sigma> \<turnstile> t |:| T \<Longrightarrow> \<Gamma>|;|(\<Sigma>@\<Sigma>1) \<turnstile> t |:| T" 
sorry

lemma progress:
  "\<emptyset>|;|\<Sigma> \<turnstile> t |:| T \<Longrightarrow> is_value_L t \<or> (\<forall>\<mu>. \<emptyset>|;|\<Sigma> \<Turnstile> \<mu> \<longrightarrow> (\<exists>t' \<mu>'. eval1_L t \<mu> t' \<mu>'))"
sorry

lemma preservation:
  "\<Gamma> |;|\<Sigma> \<turnstile> t |:| T \<Longrightarrow> \<Gamma> |;|\<Sigma> \<Turnstile> \<mu> \<Longrightarrow> eval1_L t \<mu> t' \<mu>' \<Longrightarrow> 
    \<exists>\<Sigma>1. \<Gamma> |;| (\<Sigma>@\<Sigma>1) \<Turnstile> \<mu>' \<and> \<Gamma> |;|(\<Sigma>@\<Sigma>1) \<turnstile> t' |:| T"
sorry

end