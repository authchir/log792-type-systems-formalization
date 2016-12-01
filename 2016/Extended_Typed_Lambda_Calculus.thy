(*<*)
theory Extended_Typed_Lambda_Calculus
imports
  Main
  "~~/src/HOL/Eisbach/Eisbach"
  "~~/src/HOL/Eisbach/Eisbach_Tools"
  "$AFP/List-Index/List_Index" 
begin
(*>*)

section {* Derived form*}

text{*    
    This part will cover the classical lambda calculus extended with booleans , unit type, 
    type variables and sequence in two different ways. The goal is to show that 
    both implementations are  equivalent up to some isomorphism (e) 
    with respect to evaluation and typing.
*}


subsection {* Definitions *}

(* Redefinition of the typed lambda calculus
   and properties with extended types

   We add base types T(1) T(2) .... and Unit 
 *)

datatype ltype =
  Bool |
  T (num:nat) |
  Unit |
  Fun (domain: ltype) (codomain: ltype) (infixr "\<rightarrow>" 225)

(* internal language definition with Unit only*)
datatype ltermI =
  LTrue |
  LFalse |
  LIf (bool_expr: ltermI) (then_expr: ltermI) (else_expr: ltermI) |
  LVar nat |
  LAbs (arg_type: ltype) (body: ltermI) |
  LApp ltermI ltermI |
  unit

primrec shift_L :: "int \<Rightarrow> nat \<Rightarrow> ltermI \<Rightarrow> ltermI" where
  "shift_L d c LTrue = LTrue" |
  "shift_L d c LFalse = LFalse" |
  "shift_L d c (LIf t1 t2 t3) = LIf (shift_L d c t1) (shift_L d c t2) (shift_L d c t3)" |
  "shift_L d c (LVar k) = LVar (if k < c then k else nat (int k + d))" |
  "shift_L d c (LAbs A t) = LAbs A (shift_L d (Suc c) t)" |
  "shift_L d c (LApp t1 t2) = LApp (shift_L d c t1) (shift_L d c t2)" |
  "shift_L d c unit = unit"

primrec subst_L :: "nat \<Rightarrow> ltermI \<Rightarrow> ltermI \<Rightarrow> ltermI" where
  "subst_L j s LTrue = LTrue" |
  "subst_L j s LFalse = LFalse" |
  "subst_L j s (LIf t1 t2 t3) = LIf (subst_L j s t1) (subst_L j s t2) (subst_L j s t3)" |
  "subst_L j s (LVar k) = (if k = j then s else LVar k)" |
  "subst_L j s (LAbs T' t) = LAbs T' (subst_L (Suc j) (shift_L 1 0 s) t)" |
  "subst_L j s (LApp t1 t2) = LApp (subst_L j s t1) (subst_L j s t2)" |
  "subst_L j s unit = unit"

(* unit is a value*)
inductive is_value_L :: "ltermI \<Rightarrow> bool" where
  "is_value_L LTrue" |
  "is_value_L LFalse" |
  "is_value_L (LAbs T' t)" |
  "is_value_L unit"

(* 
  a sequence is only valid if FV t2 doesn't contain 0
  so we will only consider shifted term t2 (always a valid term)
*)

abbreviation sequence :: "ltermI\<Rightarrow>ltermI\<Rightarrow>ltermI" (infix ";;" 200) where
(* "sequence t1 t2 \<equiv> (LApp (LAbs Unit  (shift_L 1 0 t2)) t1)"*)
"sequence t1 t2 \<equiv> (LApp (LAbs Unit t2) t1)"
primrec FV :: "ltermI \<Rightarrow> nat set" where
  "FV LTrue = {}" |
  "FV LFalse = {}" |
  "FV (LIf t1 t2 t3) = FV t1 \<union> FV t2 \<union> FV t3" |
  "FV (LVar x) = {x}" |
  "FV (LAbs T1 t) = image (\<lambda>x. x - 1) (FV t - {0})" |
  "FV (LApp t1 t2) = FV t1 \<union> FV t2" |
  "FV unit = {}"


inductive eval1_L :: "ltermI \<Rightarrow> ltermI \<Rightarrow> bool" where
  -- "Rules relating to the evaluation of Booleans"
  eval1_LIf_LTrue:
    "eval1_L (LIf LTrue t2 t3) t2" |
  eval1_LIf_LFalse:
    "eval1_L (LIf LFalse t2 t3) t3" |
  eval1_LIf:
    "eval1_L t1 t1' \<Longrightarrow> eval1_L (LIf t1 t2 t3) (LIf t1' t2 t3)" |

  -- "Rules relating to the evaluation of function application"
  eval1_LApp1:
    "eval1_L t1 t1' \<Longrightarrow> eval1_L (LApp t1 t2) (LApp t1' t2)" |
  eval1_LApp2:
    "is_value_L v1 \<Longrightarrow> eval1_L t2 t2' \<Longrightarrow> eval1_L (LApp v1 t2) (LApp v1 t2')" |
  eval1_LApp_LAbs:
    "is_value_L v2 \<Longrightarrow> eval1_L (LApp (LAbs T' t12) v2)
      (shift_L (-1) 0 (subst_L 0 (shift_L 1 0 v2) t12))" 


inductive_cases eval1_LIf_E: "eval1_L (LIf t t1 t2) t'"
inductive_cases eval1_LApp_E: "eval1_L (LApp t1 t2) t'"

type_synonym lcontext = "ltype list"


notation Nil ("\<emptyset>")
abbreviation cons :: "lcontext \<Rightarrow> ltype \<Rightarrow> lcontext" (infixl "|,|" 200) where
  "cons \<Gamma> T' \<equiv> T' # \<Gamma>"
abbreviation elem' :: "(nat \<times> ltype) \<Rightarrow> lcontext \<Rightarrow> bool" (infix "|\<in>|" 200) where
  "elem' p \<Gamma> \<equiv> fst p < length \<Gamma> \<and> snd p = nth \<Gamma> (fst p)"

(* had new typing rule for unit and sequence*)
inductive has_type_L :: "lcontext \<Rightarrow> ltermI \<Rightarrow> ltype \<Rightarrow> bool" ("((_)/ \<turnstile> (_)/ |:| (_))" [150, 150, 150] 150) where
  -- "Rules relating to the type of Booleans"
  has_type_LTrue:
    "\<Gamma> \<turnstile> LTrue |:| Bool" |
  has_type_LFalse:
    "\<Gamma> \<turnstile> LFalse |:| Bool" |
  has_type_LIf:
    "\<Gamma> \<turnstile> t1 |:| Bool \<Longrightarrow> \<Gamma> \<turnstile> t2 |:| T' \<Longrightarrow> \<Gamma> \<turnstile> t3 |:| T' \<Longrightarrow> \<Gamma> \<turnstile> (LIf t1 t2 t3) |:| T'" |

  -- \<open>Rules relating to the type of the constructs of the $\lambda$-calculus\<close>
  has_type_LVar:
    "(x, T') |\<in>| \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> (LVar x) |:| (T')" |
  has_type_LAbs:
    "(\<Gamma> |,| T1) \<turnstile> t2 |:| T2 \<Longrightarrow> \<Gamma> \<turnstile> (LAbs T1 t2) |:| (T1 \<rightarrow> T2)" |
  has_type_LApp:
    "\<Gamma> \<turnstile> t1 |:| (T11 \<rightarrow> T12) \<Longrightarrow> \<Gamma> \<turnstile> t2 |:| T11 \<Longrightarrow> \<Gamma> \<turnstile> (LApp t1 t2) |:| T12" |
  has_type_LUnit:
    "\<Gamma> \<turnstile> unit |:| Unit"

lemma[simp]: "nat (int x + 1) = Suc x" by simp
lemma[simp]: "nat (1 + int x) = Suc x" by simp
lemma[simp]: "nat (int x - 1) = x - 1" by simp

lemma gr_Suc_conv: "Suc x \<le> n \<longleftrightarrow> (\<exists>m. n = Suc m \<and> x \<le> m)"
  by (cases n) auto

lemma FV_shift:
  "FV (shift_L d c t) = image (\<lambda>x. if x \<ge> c then nat (int x + d) else x) (FV t)"
proof (induction t arbitrary: c rule: ltermI.induct)
  case (LAbs T t)
    show ?case sorry
qed auto

lemma FV_subst:
  "FV (subst_L n t u) = (if n \<in> FV u then (FV u - {n}) \<union> FV t else FV u)"
proof (induction u arbitrary: n t rule: ltermI.induct)
  case (LAbs T u)
  thus ?case 
    by (auto simp: gr0_conv_Suc image_iff FV_shift[of 1, unfolded int_1],
        (metis DiffI One_nat_def UnCI diff_Suc_1 empty_iff imageI insert_iff nat.distinct(1))+)
qed (auto simp: gr0_conv_Suc image_iff FV_shift[of 1, unfolded int_1])



(* inversion, uniqueness and canonical form updated with unit*)
lemma inversion:
  "\<Gamma> \<turnstile> LTrue |:| R \<Longrightarrow> R = Bool"
  "\<Gamma> \<turnstile> LFalse |:| R \<Longrightarrow> R = Bool"
  "\<Gamma> \<turnstile> LIf t1 t2 t3 |:| R \<Longrightarrow> \<Gamma> \<turnstile> t1 |:| Bool \<and> \<Gamma> \<turnstile> t2 |:| R \<and> \<Gamma> \<turnstile> t3 |:| R"
  "\<Gamma> \<turnstile> LVar x |:| R \<Longrightarrow> (x, R) |\<in>| \<Gamma>"
  "\<Gamma> \<turnstile> LAbs T1 t2 |:| R \<Longrightarrow> \<exists>R2. R = T1 \<rightarrow> R2 \<and> \<Gamma> |,| T1 \<turnstile> t2 |:| R2"
  "\<Gamma> \<turnstile> LApp t1 t2 |:| R \<Longrightarrow> \<exists>T11. \<Gamma> \<turnstile> t1 |:| T11 \<rightarrow> R \<and> \<Gamma> \<turnstile> t2 |:| T11"
  "\<Gamma> \<turnstile>  unit |:| R \<Longrightarrow> R = Unit"
  by (auto elim: has_type_L.cases)
  

theorem uniqueness_of_types:
  "\<Gamma> \<turnstile> t |:| T1 \<Longrightarrow> \<Gamma> \<turnstile> t |:| T2 \<Longrightarrow> T1 = T2"
by (induction \<Gamma> t T1 arbitrary: T2 rule: has_type_L.induct)
  (metis prod.sel ltype.sel inversion)+

lemma canonical_forms:
  "is_value_L v \<Longrightarrow> \<Gamma> \<turnstile> v |:| Bool \<Longrightarrow> v = LTrue \<or> v = LFalse"
  "is_value_L v \<Longrightarrow> \<Gamma> \<turnstile> v |:| T1 \<rightarrow> T2 \<Longrightarrow> \<exists>t. v = LAbs T1 t"
  "is_value_L v \<Longrightarrow> \<Gamma> \<turnstile> v |:| Unit \<Longrightarrow> v = unit"
by (auto elim: has_type_L.cases is_value_L.cases)

lemma shift_down:
  "insert_nth n U \<Gamma> \<turnstile> t |:| A \<Longrightarrow> n \<le> length \<Gamma> \<Longrightarrow>
   (\<And>x. x \<in> FV t \<Longrightarrow> x \<noteq> n) \<Longrightarrow> \<Gamma> \<turnstile> shift_L (-1) n t |:| A"
proof (induction "insert_nth n U \<Gamma>" t A arbitrary: \<Gamma> n rule: has_type_L.induct)
  case (has_type_LAbs V t A)
  from this(1,3,4) show ?case
    by (fastforce intro: has_type_L.intros has_type_LAbs.hyps(2)[where n="Suc n"])+
qed (fastforce intro: has_type_L.intros simp: nth_append min_def)+

lemma weakening:
  "\<Gamma> \<turnstile> t |:| A \<Longrightarrow> n \<le> length \<Gamma> \<Longrightarrow> insert_nth n S \<Gamma> \<turnstile> shift_L 1 n t |:| A"
proof (induction \<Gamma> t A arbitrary: n rule: has_type_L.induct)
  case (has_type_LAbs \<Gamma> T1 t2 T2)
    show ?case
      using has_type_LAbs(1,3) has_type_LAbs.IH[where n="Suc n"] 
      by (auto intro: has_type_L.intros)
qed (auto simp: nth_append min_def intro: has_type_L.intros)


(* sequence specific lemmas 
    evaluation
    typing
*)

theorem eval1_Lseq: 
  "eval1_L t1 t1' \<Longrightarrow> eval1_L (t1;;t2) (t1';;t2)"
  by (auto intro: eval1_L.intros is_value_L.intros)

lemma subst_free_var_only: "x\<notin>FV t \<Longrightarrow> subst_L x t1 t = t"
by (induction t arbitrary:t1 x, force+)

lemma shift_shift_invert: "a>0 \<Longrightarrow> shift_L (-a) b (shift_L a b t) = t"
by (induction t arbitrary: a b, auto)
   
  
theorem eval1_Lseq_next:
  "0\<notin>FV t2 \<Longrightarrow> eval1_L (unit ;; t2) (shift_L (-1) 0 t2)"
proof - 
  assume nozero: "0\<notin>FV t2"
  have A:"eval1_L (unit ;; t2) (shift_L (-1) 0 (subst_L 0 (shift_L 1 0 unit) t2))"
    using eval1_LApp_LAbs
          "is_value_L.simps"
     by presburger

  have B:" subst_L 0 (shift_L 1 0 unit) t2 = t2"
    using subst_free_var_only[of 0 t2 unit]  
          nozero
    by auto
  show ?thesis 
    using A[unfolded B] shift_shift_invert
    by force        
qed    

lemma eval1_LSeq_E:
  fixes t1 t2 t':: ltermI
  assumes H:"eval1_L (t1;;t2) t'" and nozero:"0\<notin>FV t2" and
          step1: "\<And>t1'. eval1_L t1 t1' \<Longrightarrow> t' = (t1';;t2) \<Longrightarrow> P" and
          step2: "t1 = unit \<Longrightarrow> t' = shift_L (-1) 0 t2 \<Longrightarrow> P" and
          step3: "is_value_L t1 \<Longrightarrow> t' = shift_L (-1) 0 t2 \<Longrightarrow> P"  
  shows "P"
using assms
proof (induction "(t1;;t2)" t' rule:eval1_L.induct)
  case (eval1_LApp_LAbs)
    have "shift_L (-1) 0 (subst_L 0 (shift_L 1 0 t1) t2) = shift_L (-1) 0 t2"
      using subst_free_var_only[of 0 t2  "shift_L 1 0 t1" ]  eval1_LApp_LAbs(2)
      by force
    with "eval1_LApp_LAbs.hyps" "eval1_LApp_LAbs.prems"(4)
      show ?case
        by auto
qed (auto elim: eval1_L.cases)

lemma r1: "0\<notin>FV t2 \<Longrightarrow> \<Gamma> \<turnstile> shift_L (-1) 0 t2 |:| A \<Longrightarrow> \<Gamma>|,|B \<turnstile> t2 |:| A" sorry

theorem has_type_LSeq: 
  "0\<notin>FV t2 \<Longrightarrow> \<Gamma> \<turnstile> t1 |:| Unit \<Longrightarrow> \<Gamma> \<turnstile> shift_L (-1) 0 t2 |:| A \<Longrightarrow> \<Gamma> \<turnstile> (t1 ;; t2) |:| A"
using has_type_LAbs has_type_LApp r1      
by fastforce
  
(* external language definition with sequence as a term*)
datatype ltermE =
  LETrue |
  LEFalse |
  LEIf (bool_expr: ltermE) (then_expr: ltermE) (else_expr: ltermE) |
  LEVar nat |
  LEAbs (arg_type: ltype) (body: ltermE) |
  LEApp ltermE ltermE |
  unitE |
  SeqE (fp: ltermE) (sp: ltermE)

primrec shift_LE :: "int \<Rightarrow> nat \<Rightarrow> ltermE \<Rightarrow> ltermE" where
  "shift_LE d c LETrue = LETrue" |
  "shift_LE d c LEFalse = LEFalse" |
  "shift_LE d c (LEIf t1 t2 t3) = LEIf (shift_LE d c t1) (shift_LE d c t2) (shift_LE d c t3)" |
  "shift_LE d c (LEVar k) = LEVar (if k < c then k else nat (int k + d))" |
  "shift_LE d c (LEAbs A t) = LEAbs A (shift_LE d (Suc c) t)" |
  "shift_LE d c (LEApp t1 t2) = LEApp (shift_LE d c t1) (shift_LE d c t2)" |
  "shift_LE d c unitE = unitE"|
"shift_LE d c (SeqE t1 t2) = 
SeqE (shift_LE d c t1) (shift_LE d (Suc c) t2)"

primrec subst_LE :: "nat \<Rightarrow> ltermE \<Rightarrow> ltermE \<Rightarrow> ltermE" where
  "subst_LE j s LETrue = LETrue" |
  "subst_LE j s LEFalse = LEFalse" |
  "subst_LE j s (LEIf t1 t2 t3) = LEIf (subst_LE j s t1) (subst_LE j s t2) (subst_LE j s t3)" |
  "subst_LE j s (LEVar k) = (if k = j then s else LEVar k)" |
  "subst_LE j s (LEAbs T' t) = LEAbs T' (subst_LE (Suc j) (shift_LE 1 0 s) t)" |
  "subst_LE j s (LEApp t1 t2) = LEApp (subst_LE j s t1) (subst_LE j s t2)" |
  "subst_LE j s unitE = unitE" |
  "subst_LE j s (SeqE t1 t2) = SeqE (subst_LE j s t1) (subst_LE j s t2)"
  
(* unit is a value*)
inductive is_value_LE :: "ltermE \<Rightarrow> bool" where
  "is_value_LE LETrue" |
  "is_value_LE LEFalse" |
  "is_value_LE (LEAbs T' t)" |
  "is_value_LE unitE"

primrec FVE :: "ltermE \<Rightarrow> nat set" where
  "FVE LETrue = {}" |
  "FVE LEFalse = {}" |
  "FVE (LEIf t1 t2 t3) = FVE t1 \<union> FVE t2 \<union> FVE t3" |
  "FVE (LEVar x) = {x}" |
  "FVE (LEAbs T1 t) = image (\<lambda>x. x - 1) (FVE t - {0})" |
  "FVE (LEApp t1 t2) = FVE t1 \<union> FVE t2" |
  "FVE unitE = {}" |
  "FVE (SeqE t1 t2) = FVE t1 \<union> FVE t2"

inductive eval1_LE :: "ltermE \<Rightarrow> ltermE \<Rightarrow> bool" where
  -- "Rules relating to the evaluation of Booleans"
  eval1_LEIf_LTrue:
    "eval1_LE (LEIf LETrue t2 t3) t2" |
  eval1_LEIf_LFalse:
    "eval1_LE (LEIf LEFalse t2 t3) t3" |
  eval1_LEIf:
    "eval1_LE t1 t1' \<Longrightarrow> eval1_LE (LEIf t1 t2 t3) (LEIf t1' t2 t3)" |

  -- "Rules relating to the evaluation of function application"
  eval1_LEApp1:
    "eval1_LE t1 t1' \<Longrightarrow> eval1_LE (LEApp t1 t2) (LEApp t1' t2)" |
  eval1_LEApp2:
    "is_value_LE v1 \<Longrightarrow> eval1_LE t2 t2' \<Longrightarrow> eval1_LE (LEApp v1 t2) (LEApp v1 t2')" |
  eval1_LEApp_LEAbs:
    "is_value_LE v2 \<Longrightarrow> eval1_LE (LEApp (LEAbs T' t12) v2)
      (shift_LE (-1) 0 (subst_LE 0 (shift_LE 1 0 v2) t12))" |
  
  -- "Rules relating to evaluation of sequence"
  
  eval1_LE_E_Seq:
    "eval1_LE t1 t1' \<Longrightarrow> eval1_LE (SeqE t1 t2) (SeqE t1' t2)" |
  eval1_LE_E_Seq_Next:
    "eval1_LE (SeqE unitE t2) t2"


inductive_cases eval1_LEIf_E: "eval1_LE (LEIf t t1 t2) t'"
inductive_cases eval1_LEApp_E: "eval1_LE (LEApp t1 t2) t'"
inductive_cases eval1_LESeq_E: "eval1_LE (SeqE t1 t2) t'"

(* had new typing rule for unit and sequence*)
inductive has_type_LE :: "lcontext \<Rightarrow> ltermE \<Rightarrow> ltype \<Rightarrow> bool" ("((_)/ \<turnstile>\<^sup>E (_)/ |:| (_))" [150, 150, 150] 150) where
  -- "Rules relating to the type of Booleans"
  has_type_LETrue:
    "\<Gamma> \<turnstile>\<^sup>E LETrue |:| Bool" |
  has_type_LEFalse:
    "\<Gamma> \<turnstile>\<^sup>E LEFalse |:| Bool" |
  has_type_LEIf:
    "\<Gamma> \<turnstile>\<^sup>E t1 |:| Bool \<Longrightarrow> \<Gamma> \<turnstile>\<^sup>E t2 |:| T' \<Longrightarrow> \<Gamma> \<turnstile>\<^sup>E t3 |:| T' \<Longrightarrow> \<Gamma> \<turnstile>\<^sup>E (LEIf t1 t2 t3) |:| T'" |

  -- \<open>Rules relating to the type of the constructs of the $\lambda$-calculus\<close>
  has_type_LEVar:
    "(x, T') |\<in>| \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile>\<^sup>E (LEVar x) |:| (T')" |
  has_type_LEAbs:
    "(\<Gamma> |,| T1) \<turnstile>\<^sup>E t2 |:| T2 \<Longrightarrow> \<Gamma> \<turnstile>\<^sup>E (LEAbs T1 t2) |:| (T1 \<rightarrow> T2)" |
  has_type_LEApp:
    "\<Gamma> \<turnstile>\<^sup>E t1 |:| (T11 \<rightarrow> T12) \<Longrightarrow> \<Gamma> \<turnstile>\<^sup>E t2 |:| T11 \<Longrightarrow> \<Gamma> \<turnstile>\<^sup>E (LEApp t1 t2) |:| T12" |
  
  has_type_LEUnit:
    "\<Gamma> \<turnstile>\<^sup>E unitE |:| Unit " |  
  -- "Rule relating to sequence"
  has_type_LESeqE:
    "0\<notin>FVE t2 \<Longrightarrow> \<Gamma> \<turnstile>\<^sup>E t1 |:| Unit \<Longrightarrow> \<Gamma> \<turnstile>\<^sup>E t2 |:| A \<Longrightarrow> \<Gamma> \<turnstile>\<^sup>E (SeqE t1 t2) |:| A"

lemma inversionE:
  "\<Gamma> \<turnstile>\<^sup>E LETrue |:| R \<Longrightarrow> R = Bool"
  "\<Gamma> \<turnstile>\<^sup>E LEFalse |:| R \<Longrightarrow> R = Bool"
  "\<Gamma> \<turnstile>\<^sup>E LEIf t1 t2 t3 |:| R \<Longrightarrow> \<Gamma> \<turnstile>\<^sup>E t1 |:| Bool \<and> \<Gamma> \<turnstile>\<^sup>E t2 |:| R \<and> \<Gamma> \<turnstile>\<^sup>E t3 |:| R"
  "\<Gamma> \<turnstile>\<^sup>E LEVar x |:| R \<Longrightarrow> (x, R) |\<in>| \<Gamma>"
  "\<Gamma> \<turnstile>\<^sup>E LEAbs T1 t2 |:| R \<Longrightarrow> \<exists>R2. R = T1 \<rightarrow> R2 \<and> \<Gamma> |,| T1 \<turnstile>\<^sup>E t2 |:| R2"
  "\<Gamma> \<turnstile>\<^sup>E LEApp t1 t2 |:| R \<Longrightarrow> \<exists>T11. \<Gamma> \<turnstile>\<^sup>E t1 |:| T11 \<rightarrow> R \<and> \<Gamma> \<turnstile>\<^sup>E t2 |:| T11"
  "\<Gamma> \<turnstile>\<^sup>E unitE |:| R \<Longrightarrow> R = Unit"
  "\<Gamma> \<turnstile>\<^sup>E SeqE t1 t2 |:| R \<Longrightarrow> \<exists>A. R = A \<and> \<Gamma> \<turnstile>\<^sup>E t2 |:| A \<and> \<Gamma> \<turnstile>\<^sup>E t1 |:| Unit \<and> 0\<notin>FVE t2"
  by (auto elim: has_type_LE.cases)

lemma canonical_formsE:
  "is_value_LE v \<Longrightarrow> \<Gamma> \<turnstile>\<^sup>E v |:| Bool \<Longrightarrow> v = LETrue \<or> v = LEFalse"
  "is_value_LE v \<Longrightarrow> \<Gamma> \<turnstile>\<^sup>E v |:| T1 \<rightarrow> T2 \<Longrightarrow> \<exists>t. v = LEAbs T1 t"
  "is_value_LE v \<Longrightarrow> \<Gamma> \<turnstile>\<^sup>E v |:| Unit \<Longrightarrow> v = unitE"
by (auto elim: has_type_LE.cases is_value_LE.cases)
  

lemma FVE_shift:
  "FVE (shift_LE (int d) c t) = image (\<lambda>x. if x \<ge> c then x + d else x) (FVE t)"
proof (induction t arbitrary: c rule: ltermE.induct)
  case (LEAbs T t)
    thus ?case 
      by (auto simp: gr_Suc_conv image_iff) force+
qed auto

lemma weakeningE:
  "\<Gamma> \<turnstile>\<^sup>E t |:| A \<Longrightarrow> n \<le> length \<Gamma> \<Longrightarrow> insert_nth n S \<Gamma> \<turnstile>\<^sup>E shift_LE 1 n t |:| A"
proof (induction \<Gamma> t A arbitrary: n rule: has_type_LE.induct)
  case (has_type_LEAbs \<Gamma> T1 t2 T2)
    show ?case
      using has_type_LEAbs(1,3) has_type_LEAbs.IH[where n="Suc n"] 
      by (auto intro: has_type_LE.intros)
next
  case (has_type_LESeqE t2 \<Gamma> t1 A)
    show ?case
      using has_type_LESeqE(1)
            FVE_shift[of 1 n]
            has_type_LESeqE(4,5,6)
      by (auto intro: has_type_LE.intros)
qed (auto simp: nth_append min_def intro: has_type_LE.intros)
 
(* Theorem 11.3.1 Sequence is a derived form*)

(*e is a translation function from external to internal language*)


fun e::"ltermE \<Rightarrow> ltermI" where
  "e LETrue = LTrue" |
  "e LEFalse = LFalse" |
  "e (LEIf t1 t2 t3) = LIf (e t1) (e t2) (e t3)" |
  "e (LEVar x) = LVar x" |
  "e (LEAbs A t1) = LAbs A (e t1)" |
  "e (LEApp t1 t2) = LApp (e t1) (e t2)" |
  "e unitE = unit" |
  "e (SeqE t1 t2) = (e t1 ;; e t2)"

(* 
  This theorem shows that both implementation of sequence are
   equivalent in term of typing and evaluation
*)

method e_elim uses rule1 = (auto intro: e.elims[OF rule1] is_value_LE.intros) 
method sym_then_elim = match premises in I: "A = B" for A and B \<Rightarrow>
            \<open>e_elim rule1: I[symmetric]\<close>

lemma value_equiv: "is_value_LE v1 \<longleftrightarrow> is_value_L (e v1)" (is "?P \<longleftrightarrow> ?Q")
proof
  show "?P \<Longrightarrow> ?Q"
    by (induction rule: is_value_LE.induct, auto intro:"is_value_L.intros")    
next
  show "?Q \<Longrightarrow> ?P" 
    by (induction "e v1" rule: is_value_L.induct, sym_then_elim+)
qed

lemma e_inv:
  "e t = LTrue \<Longrightarrow> t = LETrue"
  "e t = LFalse \<Longrightarrow> t = LEFalse" 
  "e t = LIf c t1 t2 \<Longrightarrow> \<exists>c' t1' t2'. e c'= c \<and>  e t1' = t1 \<and> t = LEIf c' t1' t2' \<and>  e t2' = t2"
  "e t = LAbs A t1 \<Longrightarrow> \<exists>t1'. t = LEAbs A t1' \<and> e t1' = t1"
  "e t = LVar x \<Longrightarrow> t = LEVar x"
  "e t = unit \<Longrightarrow> t = unitE"
  "e t = LApp t1 t2 \<Longrightarrow> \<exists>t1' t2'. e t1' = t1 \<and> e t2' = t2 \<and> t = LEApp t1' t2' 
                        \<or> 
       (\<exists>t3 t3'. t1 = LAbs Unit t3 \<and> e t3' = t3 \<and> t = SeqE t2' t3')"  
by (auto elim: e.elims)

lemma e_shift:
  "e (shift_LE d c t) = shift_L d c (e t)"
by (induction t arbitrary: c, auto)

lemma e_subst:
  "e (subst_LE j s t) = subst_L j (e s) (e t)"
sorry

theorem e_surjective:
  fixes t::ltermI
  shows "\<exists>u. e u = t"
by (induction t)(blast intro:e.simps)+
      
theorem equiv_type:
  "\<Gamma> \<turnstile>\<^sup>E t |:| A \<longleftrightarrow> \<Gamma> \<turnstile> (e t) |:| A" (is "?P \<longleftrightarrow> ?Q")
proof 
  show "?P \<Longrightarrow> ?Q" sorry
next
  show "?Q \<Longrightarrow> ?P" sorry
qed



theorem Progress:
  "\<Gamma> \<turnstile> t |:| A \<Longrightarrow> is_value_L t \<or> (\<exists>t'. eval1_L t t')"
sorry

theorem ProgressE:
  "\<Gamma> \<turnstile>\<^sup>E t |:| A \<Longrightarrow> is_value_LE t \<or> (\<exists>t'. eval1_LE t t')"
sorry

theorem eval1_L_det:
  "eval1_L t t1 \<Longrightarrow> eval1_L t t2 \<Longrightarrow> t1 = t2"
sorry

theorem eval1_L_to_eval1_LE :
  fixes   t t'::ltermE and \<Gamma>::lcontext
  assumes "\<Gamma> \<turnstile>\<^sup>E t |:| A" and "(eval1_LE t t')"
  shows   "(eval1_L (e t) (e t'))" 
using assms(2,1)
proof (induction t t' arbitrary: A rule: eval1_LE.induct)
  case (eval1_LEApp_LEAbs)
    thus ?case sorry
next
  case (eval1_LE_E_Seq)
    thus ?case sorry
next
  case (eval1_LE_E_Seq_Next)
    thus ?case sorry
qed (auto intro: eval1_L.intros elim: has_type_LE.cases simp: value_equiv)

fun subterms:: "ltermE \<Rightarrow> ltermE list" where
"subterms (LEIf c t1 t2) = [c,t1, t2]"|
"subterms (LEApp t1 t2) = [t1,t2]"|
"subterms (LEAbs A t)   = [t]"|
"subterms (SeqE t1 t2)  = [t1, t2]" |
"subterms t = []"

abbreviation term_equiv:: "ltermE\<Rightarrow>ltermE\<Rightarrow>bool" ("(_)/ \<cong>/ (_)" [200,202] 200) where
"t \<cong> t1 \<equiv> (\<forall>\<Gamma> A t2. \<Gamma> \<turnstile>\<^sup>E t |:| A = \<Gamma> \<turnstile>\<^sup>E t1 |:| A \<and> eval1_LE t t2 = eval1_LE t1 t2)"

lemma equiv_subterms_comp:
  "(\<And>i. i<length (subterms t) \<Longrightarrow> length (subterms t) = length (subterms t') \<Longrightarrow> (subterms t ! i) \<cong> (subterms t' ! i))
    \<Longrightarrow> t \<cong> t'"
sorry

theorem sym_equiv[sym]:
  "(t \<cong> t') \<Longrightarrow> (t' \<cong> t)"
by blast

print_attributes

lemma e_equiv:
  "e t1 = e t2 \<Longrightarrow> t1 \<cong> t2" sorry

lemma eval1_LE_to_sim_eval1_L:
  fixes   t t'::ltermE
  shows   "(eval1_L (e t) (e t')) \<Longrightarrow>\<exists>t1. (eval1_LE t t1) \<and> (t' \<cong> t1)" 
proof (induction "e t" "e t'" arbitrary: t t' rule: eval1_L.induct)
  case (eval1_LApp1)
    thus ?case sorry
next
  case (eval1_LApp2)
    thus ?case sorry
next
  case (eval1_LApp_LAbs)
    thus ?case sorry
next
  case (eval1_LIf c c1 t1 t2)
    note H=this
    obtain c' t1' t2' where invs_t: "c =e c'" "e t1' = t1" "t = LEIf c' t1' t2'" "e t2' = t2"
      using e_inv(3)[OF H(3)[symmetric]]
      by blast
    obtain c1' t1'' t2'' where invs_t': "c1 = e c1'" "t1 = e t1''" "t' = LEIf c1' t1'' t2''" "t2 = e t2''"
      using e_inv(3)[OF H(4)[symmetric]]
      by blast

    note invs_t = invs_t[unfolded invs_t']

    obtain c2 where cdt_equi:"eval1_LE c' c2" "c1' \<cong> c2"
      using H(2)[OF invs_t(1) invs_t'(1)]
      by blast
    have equi:"\<And>i. i < length (subterms t') \<Longrightarrow> length (subterms t') = length [c2, t1', t2'] \<Longrightarrow> (subterms t' ! i) \<cong> ([c2, t1', t2'] ! i)"
      proof -
        fix i
        assume  inf_len:"i<length (subterms t')" and same_len:"length (subterms t') = length [c2, t1', t2']"
        hence "i=0 \<or> i=1 \<or> i=2" by auto
        thus "(subterms t' ! i) \<cong> ([c2, t1', t2'] ! i)"
          using invs_t'(3) e_equiv[OF invs_t(2), symmetric] e_equiv[OF invs_t(4), symmetric]
                cdt_equi(2)
          by force
      qed
    show ?case
      using eval1_LE.intros(3)[OF cdt_equi(1),of t1' t2'] invs_t(3)
             equiv_subterms_comp[of t' "LEIf c2 t1' t2'", unfolded "subterms.simps"]
            equi
      by blast            
qed (match premises in I: "A = B" for A and B \<Rightarrow> \<open> insert I[symmetric] e_equiv eval1_LE.intros
            e_inv(1-3), metis \<close>)+

