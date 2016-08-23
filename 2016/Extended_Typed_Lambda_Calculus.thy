(*<*)
theory Extended_Typed_Lambda_Calculus
imports
  Main
  "~~/src/HOL/Eisbach/Eisbach"
  "~~/src/HOL/Eisbach/Eisbach_Tools"
  "$AFP/List-Index/List_Index" 
begin
(*>*)

section {* Extended Typed Lambda Calculi*}

text{*    
    This part will cover different lambda calculi containing some basic type extension
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
  "shift_L d c (LAbs T' t) = LAbs T' (shift_L d (Suc c) t)" |
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

abbreviation sequence :: "ltermI\<Rightarrow>ltermI\<Rightarrow>ltermI" (infix ";" 200) where
 "sequence t1 t2 \<equiv> (LApp (LAbs Unit  (shift_L 1 0 t2)) t1)"

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
  "FV (shift_L (int d) c t) = image (\<lambda>x. if x \<ge> c then x + d else x) (FV t)"
proof (induction t arbitrary: c rule: ltermI.induct)
  case (LAbs T t)
  thus ?case by (auto simp: gr_Suc_conv image_iff) force+
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
   (\<And>x. x \<in> FV t \<Longrightarrow> x \<noteq> n) \<Longrightarrow> \<Gamma> \<turnstile> shift_L (- 1) n t |:| A"
proof (induction "insert_nth n U \<Gamma>" t A arbitrary: \<Gamma> n rule: has_type_L.induct)
  case (has_type_LAbs V t A)
  from this(1,3,4) show ?case
    by (fastforce intro: has_type_L.intros has_type_LAbs.hyps(2)[where n="Suc n"])+
qed (fastforce intro: has_type_L.intros simp: nth_append min_def)+

lemma weakening:
  "\<Gamma> \<turnstile> t |:| A \<Longrightarrow> n \<le> length \<Gamma> \<Longrightarrow> insert_nth n S \<Gamma> \<turnstile> shift_L 1 n t |:| A"
proof (induction \<Gamma> t A arbitrary: n rule: has_type_L.induct)
  case (has_type_LAbs \<Gamma> T1 t2 T2)
  from has_type_LAbs.prems has_type_LAbs.hyps
    has_type_LAbs.IH[where n="Suc n"] show ?case
    by (auto intro: has_type_L.intros)
qed (auto simp: nth_append min_def intro: has_type_L.intros)


(* sequence specific lemmas 
    evaluation
    typing
*)

theorem eval1_Lseq: 
  "eval1_L t1 t1' \<Longrightarrow> eval1_L (t1;t2) (t1';t2)"
  by (auto intro: eval1_L.intros is_value_L.intros)

lemma subst_free_var_only: "x\<notin>FV t \<Longrightarrow> subst_L x t1 t = t"
by (induction t arbitrary:t1 x, force+)

lemma shift_shift_invert: "a>0 \<Longrightarrow> shift_L (-a) b (shift_L a b t) = t"
by(induction t arbitrary: a b, auto)

theorem eval1_Lseq_next:
  " eval1_L (unit ; t2) t2"
proof -  
  have A:"eval1_L (unit ; t2) (shift_L (-1) 0 (subst_L 0 (shift_L 1 0 unit) (shift_L 1 0 t2)))"
    using eval1_LApp_LAbs
          "is_value_L.simps"
     by presburger

  have " subst_L 0 (shift_L 1 0 unit) (shift_L 1 0 t2) = (shift_L 1 0 t2)"
      using subst_free_var_only[of 0 "shift_L (int 1) 0 t2" "unit"]  
            FV_shift[of 1 0 t2]
            image_iff
      by auto
  with A show ?thesis 
    using shift_shift_invert
    by force        
qed    

lemma eval1_LSeq_E:
  fixes t1 t2 t':: ltermI
  assumes H:"eval1_L (t1;t2) t'" and 
          step1: "\<And>t1'. eval1_L t1 t1' \<Longrightarrow> t' = (t1';t2) \<Longrightarrow> P" and
          step2: "t1 = unit \<Longrightarrow> t' = t2 \<Longrightarrow> P" and
          step3: "is_value_L t1 \<Longrightarrow> t' = t2 \<Longrightarrow> P"  
  shows "P"
using assms
proof (induction "(t1;t2)" t' rule:eval1_L.induct)
  case (eval1_LApp_LAbs)
    have "shift_L (- 1) 0 (subst_L 0 (shift_L 1 0 t1) (shift_L 1 0 t2)) = t2"
      using subst_free_var_only[of 0 "shift_L 1 0 t2"  "shift_L 1 0 t1" ]
            FV_shift[of 1 0 t2]
            image_iff
            shift_shift_invert
      by force
    with "eval1_LApp_LAbs.hyps" "eval1_LApp_LAbs.prems"(3)
      show ?case
        by auto
qed (auto elim: eval1_L.cases)
 

theorem has_type_LSeq: 
  "\<Gamma> \<turnstile> t1 |:| Unit \<Longrightarrow> \<Gamma> \<turnstile> t2 |:| A \<Longrightarrow> \<Gamma> \<turnstile> (t1 ; t2) |:| A"
    by (metis insert_nth.simps(1) less_eq_nat.simps(1) has_type_LAbs has_type_LApp
        weakening)

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
  "shift_LE d c (LEAbs T' t) = LEAbs T' (shift_LE d (Suc c) t)" |
  "shift_LE d c (LEApp t1 t2) = LEApp (shift_LE d c t1) (shift_LE d c t2)" |
  "shift_LE d c unitE = unitE" |
  "shift_LE d c (SeqE t1 t2) = SeqE (shift_LE d c t1) (shift_LE d (Suc c) t2)"

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
    "\<Gamma> \<turnstile>\<^sup>E t1 |:| Unit \<Longrightarrow> \<Gamma> \<turnstile>\<^sup>E t2 |:| A \<Longrightarrow> \<Gamma> \<turnstile>\<^sup>E (SeqE t1 t2) |:| A"

lemma inversionE:
  "\<Gamma> \<turnstile>\<^sup>E LETrue |:| R \<Longrightarrow> R = Bool"
  "\<Gamma> \<turnstile>\<^sup>E LEFalse |:| R \<Longrightarrow> R = Bool"
  "\<Gamma> \<turnstile>\<^sup>E LEIf t1 t2 t3 |:| R \<Longrightarrow> \<Gamma> \<turnstile>\<^sup>E t1 |:| Bool \<and> \<Gamma> \<turnstile>\<^sup>E t2 |:| R \<and> \<Gamma> \<turnstile>\<^sup>E t3 |:| R"
  "\<Gamma> \<turnstile>\<^sup>E LEVar x |:| R \<Longrightarrow> (x, R) |\<in>| \<Gamma>"
  "\<Gamma> \<turnstile>\<^sup>E LEAbs T1 t2 |:| R \<Longrightarrow> \<exists>R2. R = T1 \<rightarrow> R2 \<and> \<Gamma> |,| T1 \<turnstile>\<^sup>E t2 |:| R2"
  "\<Gamma> \<turnstile>\<^sup>E LEApp t1 t2 |:| R \<Longrightarrow> \<exists>T11. \<Gamma> \<turnstile>\<^sup>E t1 |:| T11 \<rightarrow> R \<and> \<Gamma> \<turnstile>\<^sup>E t2 |:| T11"
  "\<Gamma> \<turnstile>\<^sup>E unitE |:| R \<Longrightarrow> R = Unit"
  "\<Gamma> \<turnstile>\<^sup>E SeqE t1 t2 |:| R \<Longrightarrow> \<exists>A. R = A \<and> \<Gamma> \<turnstile>\<^sup>E t2 |:| A \<and> \<Gamma> \<turnstile>\<^sup>E t1 |:| Unit"
  by (auto elim: has_type_LE.cases)

lemma canonical_formsE:
  "is_value_LE v \<Longrightarrow> \<Gamma> \<turnstile>\<^sup>E v |:| Bool \<Longrightarrow> v = LETrue \<or> v = LEFalse"
  "is_value_LE v \<Longrightarrow> \<Gamma> \<turnstile>\<^sup>E v |:| T1 \<rightarrow> T2 \<Longrightarrow> \<exists>t. v = LEAbs T1 t"
  "is_value_LE v \<Longrightarrow> \<Gamma> \<turnstile>\<^sup>E v |:| Unit \<Longrightarrow> v = unitE"
by (auto elim: has_type_LE.cases is_value_LE.cases)
  

lemma weakeningE:
  "\<Gamma> \<turnstile>\<^sup>E t |:| A \<Longrightarrow> n \<le> length \<Gamma> \<Longrightarrow> insert_nth n S \<Gamma> \<turnstile>\<^sup>E shift_LE 1 n t |:| A"
proof (induction \<Gamma> t A arbitrary: n rule: has_type_LE.induct)
  case (has_type_LEAbs \<Gamma> T1 t2 T2)
    from has_type_LEAbs.prems has_type_LEAbs.hyps
      has_type_LEAbs.IH[where n="Suc n"] show ?case
      by (auto intro: has_type_LE.intros)
next
  case (has_type_LESeqE)
    thus ?case sorry
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
  "e (SeqE t1 t2) = (e t1 ; e t2)"

(* 
  This theorem shows that both implementation of sequence are
   equivalent in term of typing and evaluation
*)


lemma shift_L_com: 
  fixes     a d::int and b c::nat and t::ltermI
  assumes   no_zero:"a \<ge> 0"  
  shows "d \<ge> 0 \<Longrightarrow> b > c \<Longrightarrow> shift_L d c (shift_L a b t) = shift_L a b (shift_L d c t)"
        "d < 0 \<Longrightarrow> b < c \<Longrightarrow> c + (nat d) \<ge> b \<Longrightarrow> shift_L d c (shift_L a b t) = shift_L a b (shift_L d c t)"
sorry

lemma e_comp_shift: "e (shift_LE d c t) = shift_L d c (e t)"
proof (induction arbitrary: d c rule: e.induct)
  case (8 t2 t1)
    thus ?case
      using shift_L_com[of d 1 0 "Suc c"]
        sorry
qed auto

lemma ssj: "shift_L 1 0 (subst_L d t1 t2) = subst_L (Suc d) (shift_L 1 0 t1) (shift 1 0 t2)"
sorry

lemma e_comp_subst: "d \<ge> 0 \<Longrightarrow> e (subst_LE d c t) = subst_L d (e c) (e t)"
by(induction arbitrary: d c rule: e.induct)
    (auto simp:e_comp_shift, force intro: ssj)

  
method e_elim uses rule1 = (auto intro: e.elims[OF rule1] is_value_LE.intros) 
method sym_then_elim = match premises in I: "A = B" for A and B \<Rightarrow>
            \<open>e_elim rule1: HOL.sym[OF I]\<close>

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
by (auto elim: e.elims)
  
lemma e_iso:
  "e t = e t' \<Longrightarrow> t = t'"
proof (induction arbitrary: t rule: ltermE.induct)
  case (LEAbs A t1)
    thus ?case 
      using e_inv(4)
      by force
next
  case (LEIf t0 t1 t2)
    thus ?case
      using e_inv(3)[of t "e t0" "e t1" "e t2"] 
            "e.simps"(3)[of t0 t1 t2]
      by auto
next
  case (LEApp t1 t2)
    thus ?case
      sorry
next
  case (SeqE t1 t2)
    thus ?case sorry      
qed (auto intro: e_inv)

theorem e_complete:
  fixes t::ltermI
  shows "\<exists>u. e u = t"
by (induction t)(blast intro:e.simps)+
      

(*
    proof (induction rule:eval1_LE.induct)
      case (eval1_LEApp2 v1 t2 t2')
        thus ?case by (metis e.simps(6) value_equiv eval1_L.intros(5))
    next
      case (eval1_LEApp_LEAbs v1 A t)
        thus ?case
          by (simp add:e_comp_shift e_comp_subst eval1_LApp_LAbs value_equiv)
    qed (auto intro: eval1_L.intros eval1_Lseq eval1_Lseq_next)
*)

theorem equiv_type:
  "\<Gamma> \<turnstile>\<^sup>E t |:| A \<longleftrightarrow> \<Gamma> \<turnstile> (e t) |:| A" (is "?P \<longleftrightarrow> ?Q")
proof 
  show "?P \<Longrightarrow> ?Q" sorry
next
  show "?Q \<Longrightarrow> ?P" sorry
qed

theorem equiv_eval :
 "(\<Gamma> \<turnstile>\<^sup>E t |:| A \<and>  eval1_LE t t') \<longleftrightarrow> (\<Gamma> \<turnstile> (e t) |:| A \<and> eval1_L (e t) (e t'))" (is "?P \<longleftrightarrow> ?Q")
proof 
  show "?P \<Longrightarrow> ?Q"
    proof(induction t arbitrary: t' A)
      case (LEIf t1 t2 t3) 
        note H=this(4) 
        show ?case
          proof -
            obtain ll :: ltermE where
              f1: "t1 = LETrue \<and> t2 = t' \<or> t1 = LEFalse \<and> t3 = t' \<or> t' = LEIf ll t2 t3 \<and> eval1_LE t1 ll"
              by (metis H eval1_LEIf_E)       
            have "t' = LEIf ll t2 t3 \<and> eval1_LE t1 ll \<longrightarrow> eval1_L (LIf (e t1) (e t2) (e t3)) (LIf (e ll) (e t2) (e t3))"
              using LEIf.IH(1)[of Bool] eval1_LIf H has_type_LE.cases
                by blast
            with f1 show ?thesis
              using equiv_type H "eval1_L.intros"(1,2)
              by auto            
          qed
    next       
      case (LEApp t1 t2 t' B)
        note H=this(3)
        show ?case
          proof -
            obtain ll :: ltermE  and A::ltype where
              f1: "t' = LEApp ll t2 \<and> eval1_LE t1 ll
                    \<or>  t' = LEApp t1 ll \<and> is_value_LE t1 \<and> eval1_LE t2 ll \<or> 
                        t' = shift_LE (- 1) 0 (subst_LE 0 (shift_LE 1 0 t2) ll) \<and> is_value_LE t2 \<and> t1 = LEAbs A ll"
              by (metis eval1_LEApp_E H)
            let ?substll="shift_LE (- 1) 0 (subst_LE 0 (shift_LE 1 0 t2) ll)"
           
            have L:"t' = ?substll \<and> is_value_LE t2 \<and> t1 = LEAbs A ll
                    \<longrightarrow> eval1_L (LApp (e t1) (e t2)) (e ?substll)"
              using value_equiv
                    e_comp_shift
                    e_comp_subst
                    "LEApp.IH"
                    eval1_LApp_LAbs
              by simp
            show ?thesis
              proof (rule conjI, metis H equiv_type, rule disjE[OF f1], auto)
                from L 
                  show "t' = shift_LE (- 1) 0 (subst_LE 0 (shift_LE 1 0 t2) ll) \<Longrightarrow> is_value_LE t2 \<Longrightarrow> 
                              t1 = LEAbs A ll \<Longrightarrow> 
                             eval1_L (LApp (LAbs A (e ll)) (e t2)) (e (shift_LE (- 1) 0 (subst_LE 0 (shift_LE 1 0 t2) ll)))"
                  by auto     
              qed (metis "LEApp.IH" H inversionE(6) eval1_L.intros(4,5) value_equiv)+
          qed
    next
      case (SeqE t1 t2)
        note H=this(3)
        show ?case
          proof -
            obtain ll :: ltermE where
              f1: "t' = SeqE ll t2 \<and> eval1_LE t1 ll \<or> t2 = t' \<and> t1 = unitE"
              by (metis eval1_LESeq_E H)
             show ?thesis
              by (rule conjI, metis H equiv_type, rule disjE[OF f1])
                 (metis "SeqE.IH" eval1_Lseq eval1_Lseq_next H inversionE(8) e.simps)+
          qed
    qed (auto elim: eval1_LE.cases)
next
  show "?Q \<Longrightarrow> ?P"
    proof(induction t arbitrary:t' A)
      case LETrue
        thus ?case
          using e.simps(1) eval1_L.cases ltermI.distinct(3) ltermI.distinct(9) by fastforce
    next
      case LEFalse
        thus ?case
          using e.simps(1) eval1_L.cases ltermI.distinct(3) ltermI.distinct(9) by fastforce
    next
      case (LEVar x)
        thus ?case
          using e.simps(1) eval1_L.cases ltermI.distinct(3) ltermI.distinct(9) by fastforce
    next
      case (unitE)
        thus ?case
          using e.simps(1) eval1_L.cases ltermI.distinct(3) ltermI.distinct(9) by fastforce
    next
      case (LEAbs A t1)
        from this(2) show ?case
          using e.simps(1) eval1_L.cases ltermI.distinct(3) ltermI.distinct(9) by fastforce
    next    
      case (LEIf c t1 t2)           
        note H=this(4) 
        show ?case
          proof -
            obtain ll :: ltermI and u::ltermE where
              f1: "e c = LTrue \<and> e t1 = e t' \<or> e c= LFalse \<and> e t2 = e t' \<or> e t' = LIf ll (e t1) (e t2) \<and> eval1_L (e c) ll \<and> e u = ll"
              using eval1_LIf_E[of "e c" "e t1" "e t2" "e t'"] H e_complete
              by fastforce
            have H1:
              "e t' = LIf ll (e t1) (e t2) \<and> eval1_L (e c) ll \<and> e u = ll \<longrightarrow> eval1_LE (LEIf c t1 t2) (LEIf u t1 t2) \<and>
                 e u = ll \<and> t' = LEIf u t1 t2 "
              by (metis e_iso "LEIf.IH"(1) eval1_LEIf H inversion(3) "e.simps"(3))                            
            show ?thesis
              by(rule conjI, metis H equiv_type, rule disjE[OF f1], auto)
                (metis H1 eval1_LE.intros(1,2) e_inv(1,2,3) e_iso)+               
          qed          
    next     
      case (SeqE t1 t2)
        note H=this(3)
        from H have A:"eval1_L (e t1;e t2) (e t')" by simp
        show ?case
          proof -
            obtain ll :: ltermI and u::ltermE where
              f1: "e u = ll \<and> eval1_L (e t1) ll \<and> e t' = (ll;e t2)  \<or> e t1 = unit \<and> e t' = e t2 \<or>
                    is_value_L (e t1) \<and> e t' = e t2"
              by (metis eval1_LSeq_E[OF A] e_complete)
              from SeqE.IH H
                have 1:"is_value_L (e t1) \<and> e t' = e t2 \<Longrightarrow> eval1_LE (SeqE t1 t2) t'"
                  by (metis canonical_forms(3) e_inv(6) e_iso equiv_type inversionE(8) 
                              eval1_LE_E_Seq_Next)
              show ?case
                by (rule conjI, metis H equiv_type, rule disjE[OF f1], auto)
                    (metis SeqE.IH(1) H e.simps(7,8) e_iso eval1_LE_E_Seq 
                           inversion(6) eval1_LE_E_Seq_Next 1)+                  
          qed
    next
      case (LEApp t1 t2 t' B)
        hence H: "eval1_L (LApp (e t1) (e t2)) (e t')"
          by simp
        show ?case 
          proof -
            obtain ll :: ltermI and u::ltermE and C::ltype where
              f1: "e u = ll \<and> eval1_L (e t1) ll \<and> e t' = LApp ll (e t2)  \<or> 
                    e u = ll \<and> is_value_L (e t1) \<and> eval1_L (e t2) ll \<and> e t' = LApp (e t1) ll \<or>
                    is_value_L (e t2) \<and> e u = ll  \<and> e t1 = LAbs C ll \<and> e t' = shift_L (- 1) 0 (subst_L 0 (shift_L 1 0 (e t2)) ll)"
              by (metis eval1_LApp_E[OF H] e_complete)
            let ?substll = "shift_L (- 1) 0 (subst_L 0 (shift_L 1 0 (e t2)) (e u))"
                and ?substll1 = "shift_LE (- 1) 0 (subst_LE 0 (shift_LE 1 0 t2) u)"
            have L:"is_value_L (e t2) \<and> e u = ll \<and> e t1 = LAbs C ll \<and> e t' = ?substll 
                    \<Longrightarrow> eval1_LE (LEApp t1 t2) ?substll1"
              using e_inv(4)[of t1 C "e u"] e_comp_subst[of 0 "shift_LE 1 0 t2" u]
                    value_equiv[of t2]
                    e_comp_shift e_iso  
                    eval1_LEApp_LEAbs
              by fast
            show ?case
               proof  (rule conjI, metis LEApp.prems equiv_type, rule disjE[OF f1], auto)
                  show " is_value_L (e t2) \<Longrightarrow> ll = e u \<Longrightarrow> e t1 = LAbs C (e u) \<Longrightarrow> 
                        e t' = shift_L (- 1) 0 (subst_L 0 (shift_L 1 0 (e t2)) (e u)) \<Longrightarrow> eval1_LE (LEApp t1 t2) t'"
                  using e_comp_shift L
                        e_comp_subst[of 0 "shift_LE 1 0 t2" "u"]
                        e_iso[of "t'" "?substll1"]
                  by auto                 
               qed (metis LEApp.IH eval1_LE.intros(4,5) e.simps(6) LEApp.prems inversion(6) e_iso value_equiv)+
          qed 
    qed
qed    

