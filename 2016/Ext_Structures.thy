(*<*)
theory Ext_Structures
imports
   Main Pure
   List_extra
   Lambda_calculus
  "~~/src/HOL/List"
  "~~/src/HOL/Eisbach/Eisbach"
  "~~/src/HOL/Eisbach/Eisbach_Tools"
  "$AFP/List-Index/List_Index" 
begin
(*>*)

section{*Pair, Tuples and Records*}

text{* In this section,we extend our current lambda calculus with extended structures (pairs, tuples, records)*}




inductive Lmatch ::"Lpattern \<Rightarrow> lterm \<Rightarrow> (lterm \<Rightarrow>lterm) \<Rightarrow> bool" where
  M_Var:
    "is_value_L v \<Longrightarrow> Lmatch (V n as A) v (fill [n \<mapsto> v])" |
  M_RCD:
    "distinct L \<Longrightarrow> length L = length LT \<Longrightarrow> length F = length PL \<Longrightarrow> length PL = length LT 
    \<Longrightarrow> is_value_L (Record L LT) \<Longrightarrow> (\<And>i. i<length PL \<Longrightarrow> Lmatch (PL!i) (LT!i) (F!i))
    \<Longrightarrow> Lmatch (RCD L PL) (Record L LT) (\<Odot> F)"

inductive Lmatch_Type ::"Lpattern \<Rightarrow> (nat \<rightharpoonup> ltype) \<Rightarrow> bool" where
  M_Var:
    "Lmatch_Type (V n as A) [n \<mapsto> A]" |
  M_RCD:
    "distinct L \<Longrightarrow> length Tx = length PL \<Longrightarrow> length L = length PL \<Longrightarrow> 
      (\<And>i. i<length PL \<Longrightarrow> Lmatch_Type (PL!i) (Tx!i))
    \<Longrightarrow> Lmatch_Type (RCD L PL) (\<Odot>\<^sub>T Tx)"

inductive coherent ::"Lpattern \<Rightarrow> ltype \<Rightarrow> bool" where
 "coherent (V n as A) A" |
 "distinct(Pvars (RCD L PL)) \<Longrightarrow> length L = length PL \<Longrightarrow> length PL = length TL \<Longrightarrow>
  (\<And>i. i<length TL \<Longrightarrow> coherent (PL!i) (TL!i)) \<Longrightarrow> coherent (RCD L PL) (\<lparr>L|:|TL\<rparr>)"
  

inductive eval1_L :: "lterm \<Rightarrow> lterm \<Rightarrow> bool" where
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
      (shift_L (-1) 0 (subst_L 0 (shift_L 1 0 v2) t12))" |
  
  eval1_L_Seq:
    "eval1_L t1 t1' \<Longrightarrow> eval1_L (Seq t1 t2) (Seq t1' t2)" |
  eval1_L_Seq_Next:
    "eval1_L (Seq unit t2) t2" |
  
 -- "Rules relating to evaluation of ascription"
  eval1_L_Ascribe:
    "is_value_L v \<Longrightarrow> eval1_L (v as A) v" |
  eval1_L_Ascribe1:
    "eval1_L t1 t1' \<Longrightarrow> eval1_L (t1 as A) (t1' as A)" |
 -- "Rules relating to evaluation of letbinder"
  eval1_L_LetV:
    "is_value_L v1 \<Longrightarrow> eval1_L (Let var x := v1 in t2) (shift_L (-1) x (subst_L x (shift_L 1 x v1) t2))" |
  eval1_L_Let:
    "eval1_L t1 t1' \<Longrightarrow> eval1_L (Let var x := t1 in t2) (Let var x := t1' in t2)" |
 -- "Rules relating to evaluation of pairs"
  eval1_L_PairBeta1:
    "is_value_L v1 \<Longrightarrow> is_value_L v2 \<Longrightarrow> eval1_L (\<pi>1 \<lbrace>v1,v2\<rbrace>) v1" | 
  eval1_L_PairBeta2:
    "is_value_L v1 \<Longrightarrow> is_value_L v2 \<Longrightarrow> eval1_L (\<pi>2 \<lbrace>v1,v2\<rbrace>) v2" |
  eval1_L_Proj1:
    "eval1_L t1 t1' \<Longrightarrow> eval1_L (\<pi>1 t1) (\<pi>1 t1')" |
  eval1_L_Proj2:
    "eval1_L t2 t2' \<Longrightarrow> eval1_L (\<pi>2 t2) (\<pi>2 t2')" |
  eval1_L_Pair1:
    "eval1_L t1 t1' \<Longrightarrow> eval1_L (\<lbrace>t1,t2\<rbrace>) (\<lbrace>t1',t2\<rbrace>)" |
  eval1_L_Pair2:
    "is_value_L v1 \<Longrightarrow> eval1_L t2 t2' \<Longrightarrow> eval1_L (\<lbrace>v1,t2\<rbrace>) (\<lbrace>v1,t2'\<rbrace>)" |
 -- "Rules relating to evaluation of tuples"
  eval1_L_ProjTuple:
    "1\<le>i \<Longrightarrow> i\<le>length L \<Longrightarrow> is_value_L (Tuple L) \<Longrightarrow> eval1_L (\<Pi> i (Tuple L)) (L ! (i-1))" |
  eval1_L_Proj:
    "eval1_L t1 t1' \<Longrightarrow> eval1_L (\<Pi> i t1) (\<Pi> i t1')" |
  eval1_L_Tuple:
    " 1\<le>j\<Longrightarrow> j\<le>length L \<Longrightarrow> is_value_L (Tuple (take (j-1) L)) \<Longrightarrow> 
      eval1_L (L ! (j-1)) (t') \<Longrightarrow> eval1_L (Tuple L) (Tuple (replace (j-1) t' L))" |
 -- "Rules relating to evaluation of records"
  eval1_L_ProjRCD:
    "l \<in> set L \<Longrightarrow> is_value_L (Record L LT) \<Longrightarrow> eval1_L (ProjR l (Record L LT)) (LT ! (index L l))" |
  eval1_L_ProjR:
    "eval1_L t1 t1' \<Longrightarrow> eval1_L (ProjR i t1) (ProjR i t1')" |
  eval1_L_RCD:
    " m<length LT \<Longrightarrow> is_value_L (Record (take m L) (take m LT)) \<Longrightarrow> 
      eval1_L (LT ! m) (t') \<Longrightarrow> eval1_L (Record L LT) (Record L (replace m t' LT))" |   
 -- "Rules relating to evaluation of pattern matching"
  eval1_L_LetPV:
    "is_value_L v1 \<Longrightarrow> Lmatch p v1 \<sigma> \<Longrightarrow> eval1_L (Let pattern p := v1 in t2) (\<sigma> t2)" |
  eval1_L_LetP:
    "eval1_L t1 t1' \<Longrightarrow> eval1_L (Let pattern p := t1 in t2) (Let pattern p := t1' in t2)" |
 -- "Rules relating to evaluation of Sums"
  eval1_L_CaseInl:
    "is_value_L v \<Longrightarrow> eval1_L (Case (inl v as A) of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2) (shift_L (-1) x (subst_L x (shift_L 1 x v) t1))" |
  eval1_L_CaseInr:
    "is_value_L v \<Longrightarrow> eval1_L (Case (inr v as A) of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2) (shift_L (-1) y (subst_L y (shift_L 1 y v) t2))" |
  eval1_L_CaseS:
    "eval1_L t t' \<Longrightarrow> eval1_L (Case t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2) (Case t' of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2)" |
  eval1_L_Inl:
    "eval1_L t t' \<Longrightarrow> eval1_L (inl t as A) (inl t' as A)" |
  eval1_L_Inr:
    "eval1_L t t' \<Longrightarrow> eval1_L (inr t as A) (inr t' as A)" |
  eval1_L_CaseVar:
    "is_value_L v \<Longrightarrow> i<length L \<Longrightarrow> eval1_L (Case (<L!i:=v> as A) of L \<Rightarrow> B) (shift_L (-1) (fst(B!i)) (subst_L (fst (B!i)) (shift_L 1 (fst (B!i)) v) (snd(B!i))))" |
  eval1_L_CaseV:
    "eval1_L t t' \<Longrightarrow> eval1_L (Case t of L \<Rightarrow> B) (Case t' of L \<Rightarrow> B)" |
  eval1_L_Variant:
    "eval1_L t t' \<Longrightarrow> eval1_L (<l:=t> as A) (<l:=t'> as A)" |
  eval1_L_FixBeta:
    "eval1_L (fix (LAbs A t)) (shift_L (-1) 0 (subst_L 0 (shift_L 1 0 (fix LAbs A t)) t))"|
  eval1_LFix_step:
    "eval1_L t t' \<Longrightarrow> eval1_L (fix t) (fix t')" 
  

type_synonym lcontext = "ltype list"
type_synonym pcontext = "(nat \<rightharpoonup> ltype)"

notation Nil ("\<emptyset>")
abbreviation cons :: "lcontext \<Rightarrow> ltype \<Rightarrow> lcontext" (infixl "|,|" 200) where
  "cons \<Gamma> T' \<equiv> T' # \<Gamma>"
abbreviation elem' :: "(nat \<times> ltype) \<Rightarrow> lcontext \<Rightarrow> bool" (infix "|\<in>|" 200) where
  "elem' p \<Gamma> \<equiv> fst p < length \<Gamma> \<and> snd p = nth \<Gamma> (fst p)"


text{*  For the typing rule of letbinder, we require to replace the type 
        of the variable by the expected type 
    *}


inductive has_type_L :: "lcontext \<Rightarrow> lterm \<Rightarrow> pcontext \<Rightarrow> ltype \<Rightarrow> bool" ("((_)/ \<turnstile> \<lparr>(_)|;|(_)\<rparr>/ |:| (_))" [150, 150, 150,150] 150) where
  -- "Rules relating to the type of Booleans"
  has_type_LTrue:
    "\<Gamma> \<turnstile> \<lparr>LTrue|;| \<sigma>\<rparr> |:| Bool" |
  has_type_LFalse:
    "\<Gamma> \<turnstile> \<lparr>LFalse|;| \<sigma>\<rparr> |:| Bool" |
  has_type_LIf:
    "\<Gamma> \<turnstile> \<lparr>t1|;| \<sigma>\<rparr> |:| Bool \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t2|;| \<sigma>\<rparr> |:| T' \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t3|;| \<sigma>\<rparr> |:| T' \<Longrightarrow> 
      \<Gamma> \<turnstile> \<lparr>LIf t1 t2 t3|;| \<sigma>\<rparr> |:| T'" |

  -- \<open>Rules relating to the type of the constructs of the $\lambda$-calculus\<close>
  has_type_LVar:
    "(x, T') |\<in>| \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>LVar x|;| \<sigma>\<rparr> |:| (T')" |
  has_type_LAbs:
    "(\<Gamma> |,| T1) \<turnstile> \<lparr>t2|;| \<sigma>\<rparr> |:| T2 \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>LAbs T1 t2|;| \<sigma>\<rparr> |:| (T1 \<rightarrow> T2)" |
  has_type_LApp:
    "\<Gamma> \<turnstile> \<lparr>t1|;| \<sigma>\<rparr> |:| (T11 \<rightarrow> T12) \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t2|;| \<sigma>\<rparr> |:| T11 \<Longrightarrow> 
      \<Gamma> \<turnstile> \<lparr>LApp t1 t2|;| \<sigma>\<rparr> |:| T12" |  
  has_type_LUnit:
    "\<Gamma> \<turnstile> \<lparr>unit|;| \<sigma>\<rparr> |:| Unit " |  
  has_type_LSeq:
    "\<Gamma> \<turnstile> \<lparr>t1|;| \<sigma>\<rparr> |:| Unit \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t2|;| \<sigma>\<rparr> |:| A \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Seq t1 t2|;| \<sigma>\<rparr> |:| A" |
  has_type_LAscribe:
    "\<Gamma> \<turnstile> \<lparr>t1|;| \<sigma>\<rparr> |:| A \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t1 as A|;| \<sigma>\<rparr> |:| A" |
  has_type_Let:
    "x\<le>length \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t1|;| \<sigma>\<rparr> |:| A \<Longrightarrow> (insert_nth x A \<Gamma>) \<turnstile> \<lparr> t2|;| \<sigma>\<rparr> |:| B \<Longrightarrow> 
      \<Gamma> \<turnstile> \<lparr>Let var x := t1 in t2|;| \<sigma>\<rparr> |:| B" |
  has_type_Pair:
    "\<Gamma> \<turnstile> \<lparr>t1|;| \<sigma>\<rparr> |:| A \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t2|;| \<sigma>\<rparr> |:| B \<Longrightarrow> 
      \<Gamma> \<turnstile> \<lparr>\<lbrace>t1,t2\<rbrace>|;| \<sigma>\<rparr> |:| A |\<times>| B" |
  has_type_Proj1:
    "\<Gamma> \<turnstile> \<lparr>t1|;| \<sigma>\<rparr> |:| A |\<times>| B \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>\<pi>1 t1|;| \<sigma>\<rparr> |:| A" |
  has_type_Proj2:
    "\<Gamma> \<turnstile> \<lparr>t1|;| \<sigma>\<rparr> |:| A |\<times>| B \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>\<pi>2 t1|;| \<sigma>\<rparr> |:| B" |
  has_type_Tuple:
    "L\<noteq>[] \<Longrightarrow> length L = length TL \<Longrightarrow> 
      (\<And>i. 0\<le>i \<Longrightarrow> i< length L \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>(L ! i)|;| \<sigma>\<rparr> |:| (TL ! i))
      \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Tuple L|;| \<sigma>\<rparr> |:| \<lparr>TL\<rparr>" |
  has_type_ProjT:
    "1\<le>i \<Longrightarrow> i\<le> length TL \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t|;| \<sigma>\<rparr> |:| \<lparr>TL\<rparr> \<Longrightarrow> 
      \<Gamma> \<turnstile> \<lparr>\<Pi> i t|;| \<sigma>\<rparr> |:| (TL ! (i-1))" |
  has_type_RCD:
    "L\<noteq>[] \<Longrightarrow> distinct L \<Longrightarrow> length LT = length TL \<Longrightarrow> length L = length LT \<Longrightarrow>
      (\<And>i. i< length LT \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>(LT ! i)|;| \<sigma>\<rparr> |:| (TL ! i))
      \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Record L LT|;| \<sigma>\<rparr> |:| \<lparr>L|:|TL\<rparr>" |
  has_type_ProjR:
    "distinct L1 \<Longrightarrow> l\<in> set L1  \<Longrightarrow> length L1 = length TL \<Longrightarrow> 
      \<Gamma> \<turnstile> \<lparr>t|;| \<sigma>\<rparr> |:| \<lparr>L1|:|TL\<rparr> \<Longrightarrow> 
      \<Gamma> \<turnstile> \<lparr>ProjR l t|;| \<sigma>\<rparr> |:| (TL ! index L1 l)" |
  has_type_PatternVar:
    "\<sigma> k = Some A \<Longrightarrow> \<Gamma> \<turnstile> \<lparr><|V k as A|>|;| \<sigma>\<rparr> |:| A" |
  has_type_LetPattern:
    "coherent p B\<Longrightarrow> Lmatch_Type p \<sigma> \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t1|;| \<sigma>1\<rparr> |:| B \<Longrightarrow>
     \<Gamma> \<turnstile> \<lparr>t2|;|(\<sigma>1 ++ \<sigma>)\<rparr> |:| A \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Let pattern p := t1 in t2|;| \<sigma>1\<rparr> |:| A" |
  has_type_Inl:
    "\<Gamma> \<turnstile> \<lparr>t1|;| \<sigma>1\<rparr> |:| A \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>inl t1 as A|+|B |;|\<sigma>1\<rparr> |:| A|+|B" |
  has_type_Inr:
    "\<Gamma> \<turnstile> \<lparr>t1|;| \<sigma>1\<rparr> |:| B \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>inr t1 as A|+|B |;| \<sigma>1\<rparr> |:| A|+|B" |
  has_type_Case:
    "x\<le>length \<Gamma> \<Longrightarrow> y\<le>length \<Gamma> \<Longrightarrow>\<Gamma> \<turnstile> \<lparr> t|;| \<sigma>1 \<rparr> |:| A|+|B \<Longrightarrow> insert_nth x A \<Gamma> \<turnstile> \<lparr>t1|;| \<sigma>1\<rparr> |:| C \<Longrightarrow>
     insert_nth y B \<Gamma> \<turnstile> \<lparr>t2|;| \<sigma>1\<rparr> |:| C \<Longrightarrow> 
     \<Gamma> \<turnstile> \<lparr>Case t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2 |;| \<sigma>1\<rparr> |:| C" |
  has_type_Variant:
    "i<length L \<Longrightarrow>distinct L \<Longrightarrow> length L=length TL \<Longrightarrow> \<Gamma> \<turnstile> \<lparr> t |;| \<sigma> \<rparr> |:| (TL!i) \<Longrightarrow> 
      \<Gamma> \<turnstile> \<lparr> <(L!i):=t> as <L|,|TL> |;|\<sigma> \<rparr> |:| <L|,|TL>" |
  has_type_CaseV:
    " L\<noteq>\<emptyset> \<Longrightarrow> distinct L \<Longrightarrow> length L = length TL \<Longrightarrow> 
      length L = length B \<Longrightarrow> 
      \<Gamma> \<turnstile> \<lparr> t |;| \<sigma> \<rparr> |:| <L|,|TL> \<Longrightarrow> 
      (\<forall>i<length L. insert_nth (fst(B!i)) (TL!i) \<Gamma> \<turnstile> \<lparr>(snd (B!i))|;| \<sigma>\<rparr> |:| A \<and> fst (B!i)\<le>length \<Gamma>) \<Longrightarrow>
      \<Gamma> \<turnstile> \<lparr> Case t of L \<Rightarrow> B |;| \<sigma>\<rparr> |:| A" |
  has_type_Fix:
    "\<Gamma> \<turnstile> \<lparr> t |;| \<sigma>\<rparr> |:| A\<rightarrow>A \<Longrightarrow> \<Gamma> \<turnstile> \<lparr> fix t |;| \<sigma>\<rparr> |:| A"

inductive_cases has_type_LetE : "\<Gamma> \<turnstile> \<lparr> Let var x := t1 in t2|;|\<sigma>\<rparr>  |:| B"
inductive_cases has_type_ProjTE: "\<Gamma> \<turnstile> \<lparr> \<Pi> i t|;|\<sigma>1\<rparr> |:| R"
inductive_cases has_type_ProjRE: "\<Gamma> \<turnstile> \<lparr> ProjR l t|;|\<sigma>1\<rparr> |:| R"
inductive_cases has_type_LetPE: "\<Gamma> \<turnstile> \<lparr>Let pattern p := t1 in t2|;|\<sigma>1\<rparr> |:| A"
inductive_cases has_type_CaseSE: "\<Gamma> \<turnstile> \<lparr>Case t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2|;|\<sigma>1\<rparr> |:| R"
inductive_cases has_type_CaseVE: "\<Gamma> \<turnstile> \<lparr>Case t of L \<Rightarrow> B |;|\<sigma>1\<rparr> |:| R"
inductive_cases has_type_LAbsE: "\<Gamma> \<turnstile> \<lparr>LAbs T1 t2|;|\<sigma>1\<rparr> |:| R"
inductive_cases has_type_VariantE: "\<Gamma> \<turnstile> \<lparr><l:=t> as R1 |;|\<sigma>1\<rparr> |:| R"

lemma record_patterns_characterisation:
  "set (patterns (<|RCD L PL|>)) \<subseteq> S \<Longrightarrow> x \<in> set PL \<Longrightarrow> set(patterns (<|x|>)) \<subseteq> S"
by (induction PL arbitrary: S x, auto) 

lemma inversion:
  "\<Gamma> \<turnstile> \<lparr> LTrue |;| \<sigma>\<rparr> |:| R \<Longrightarrow> R = Bool"
  "\<Gamma> \<turnstile> \<lparr> LFalse |;| \<sigma>\<rparr> |:| R \<Longrightarrow> R = Bool"
  "\<Gamma> \<turnstile> \<lparr> LIf t1 t2 t3 |;| \<sigma>\<rparr> |:| R \<Longrightarrow>  \<Gamma> \<turnstile> \<lparr>t1|;| \<sigma>\<rparr> |:| Bool \<and> \<Gamma> \<turnstile> \<lparr>t2|;| \<sigma>\<rparr> |:| R \<and> \<Gamma> \<turnstile> \<lparr>t3|;| \<sigma>\<rparr> |:| R"
  "\<Gamma> \<turnstile> \<lparr> LVar x|;| \<sigma>\<rparr> |:| R \<Longrightarrow> (x, R) |\<in>| \<Gamma>"
  "\<Gamma> \<turnstile> \<lparr> LAbs T1 t2 |;| \<sigma>\<rparr> |:| R \<Longrightarrow> \<exists>R2. R = T1 \<rightarrow> R2 \<and>  \<Gamma> |,| T1 \<turnstile> \<lparr>t2|;| \<sigma>\<rparr> |:| R2 "
  "\<Gamma> \<turnstile> \<lparr> LApp t1 t2 |;| \<sigma>\<rparr> |:| R \<Longrightarrow> \<exists>T11. \<Gamma> \<turnstile> \<lparr>t1|;|\<sigma>\<rparr> |:| T11 \<rightarrow> R \<and> \<Gamma> \<turnstile> \<lparr>t2|;| \<sigma>\<rparr> |:| T11"
  "\<Gamma> \<turnstile> \<lparr> unit|;| \<sigma>\<rparr> |:| R \<Longrightarrow> R = Unit"
  "\<Gamma> \<turnstile> \<lparr> Seq t1 t2 |;| \<sigma>\<rparr> |:| R \<Longrightarrow> \<exists>A. R = A \<and> \<Gamma> \<turnstile> \<lparr>t2|;| \<sigma>\<rparr> |:| A \<and> \<Gamma> \<turnstile> \<lparr>t1|;| \<sigma>\<rparr> |:| Unit"
  "\<Gamma> \<turnstile> \<lparr> t as A |;| \<sigma>\<rparr> |:| R \<Longrightarrow> R = A \<and> \<Gamma> \<turnstile> \<lparr> t |;| \<sigma>\<rparr> |:| A"
  "\<Gamma> \<turnstile> \<lparr> Let var x := t in t1 |;| \<sigma>\<rparr> |:| R \<Longrightarrow> \<exists>A B. R = B \<and> \<Gamma> \<turnstile> \<lparr> t|;| \<sigma>\<rparr> |:| A \<and> x\<le>length \<Gamma> \<and> (insert_nth x A \<Gamma>) \<turnstile> \<lparr>t1|;| \<sigma>\<rparr> |:| B"
  "\<Gamma> \<turnstile> \<lparr> \<lbrace>t1,t2\<rbrace>|;| \<sigma>\<rparr> |:| R \<Longrightarrow> \<exists>A B. \<Gamma> \<turnstile> \<lparr> t1|;| \<sigma>\<rparr> |:| A \<and> \<Gamma> \<turnstile> \<lparr> t2|;| \<sigma>\<rparr> |:| B \<and> R = A |\<times>| B"
  "\<Gamma> \<turnstile> \<lparr> \<pi>1 t|;| \<sigma>\<rparr> |:| R \<Longrightarrow> \<exists>A B f. \<Gamma> \<turnstile> \<lparr> t|;| \<sigma>\<rparr> |:| A |\<times>| B \<and> R = A"
  "\<Gamma> \<turnstile> \<lparr> \<pi>2 t|;| \<sigma>\<rparr> |:| R \<Longrightarrow> \<exists>A B. \<Gamma> \<turnstile> \<lparr> t|;| \<sigma>\<rparr> |:| A |\<times>| B \<and> R = B"
  "\<Gamma> \<turnstile> \<lparr> Tuple L|;| \<sigma>\<rparr> |:| R \<Longrightarrow> \<exists>TL. length L = length TL \<and> (\<forall>i. 0\<le>i \<longrightarrow> i< length L \<longrightarrow> \<Gamma> \<turnstile> \<lparr>(L ! i)|;| \<sigma>\<rparr> |:| (TL ! i)) \<and> R = \<lparr>TL\<rparr>"
  "\<Gamma> \<turnstile> \<lparr> (\<Pi> i t)|;| \<sigma>\<rparr> |:| R \<Longrightarrow> \<exists>TL. R = (TL ! (i-1)) \<and> \<Gamma> \<turnstile> \<lparr>t|;| \<sigma>\<rparr> |:| \<lparr>TL\<rparr> \<and> 1\<le>i \<and> i\<le> length TL"
  "\<Gamma> \<turnstile> \<lparr> (Record L1 LT)|;| \<sigma>\<rparr> |:| R \<Longrightarrow> \<exists>TL. R = \<lparr>L1|:|TL\<rparr> \<and> length TL = length LT \<and> length L1 = length LT \<and> distinct L1 \<and> 
                                    (\<forall>i. 0\<le>i \<longrightarrow> i< length LT \<longrightarrow> \<Gamma> \<turnstile> \<lparr> (LT ! i)|;| \<sigma>\<rparr> |:| (TL ! i)) " 
  "\<Gamma> \<turnstile> \<lparr> (ProjR l t)|;| \<sigma>\<rparr> |:| R \<Longrightarrow>\<exists>m L TL. \<Gamma> \<turnstile> \<lparr>t |;| \<sigma>\<rparr> |:| \<lparr>L|:|TL\<rparr> \<and> index L l = m \<and> TL ! m = R \<and> distinct L \<and> length L = length TL
                              \<and> l \<in> set L"
  "\<Gamma> \<turnstile> \<lparr><|V k as A|>|;|\<sigma>\<rparr> |:| R \<Longrightarrow>R=A \<and> \<sigma> k = Some A"
  "\<Gamma> \<turnstile> \<lparr>Let pattern p := t1 in t2|;|\<sigma>1\<rparr> |:| R \<Longrightarrow>\<exists>\<sigma> B. coherent p B\<and> Lmatch_Type p \<sigma>  \<and> \<Gamma> \<turnstile> \<lparr>t1|;|\<sigma>1\<rparr> |:| B \<and>
                                                  \<Gamma> \<turnstile> \<lparr>t2|;|(\<sigma>1 ++  \<sigma>)\<rparr> |:| R" 
  "\<Gamma> \<turnstile> \<lparr>inl t as R1|;|\<sigma>1\<rparr> |:| R \<Longrightarrow>R1 = R \<and> (\<exists>A B. R = A|+|B \<and> \<Gamma> \<turnstile> \<lparr>t|;|\<sigma>1\<rparr> |:| A)"
  "\<Gamma> \<turnstile> \<lparr>inr t as R1|;|\<sigma>1\<rparr> |:| R \<Longrightarrow>R1 = R \<and> (\<exists>A B. R = A|+|B \<and> \<Gamma> \<turnstile> \<lparr>t|;|\<sigma>1\<rparr> |:| B)"
  "\<Gamma> \<turnstile> \<lparr>Case t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2|;|\<sigma>1\<rparr> |:| R \<Longrightarrow>\<exists>A B C. R = C \<and> \<Gamma> \<turnstile> \<lparr>t|;|\<sigma>1\<rparr> |:| A|+|B \<and> x\<le>length \<Gamma> \<and> y\<le>length \<Gamma> \<and>
                                                          insert_nth x A \<Gamma> \<turnstile> \<lparr>t1|;|\<sigma>1\<rparr> |:| C \<and> insert_nth y B \<Gamma> \<turnstile> \<lparr>t2|;|\<sigma>1\<rparr> |:| C"
   "\<Gamma> \<turnstile> \<lparr> <l:=t> as R1 |;| \<sigma>1 \<rparr> |:| R \<Longrightarrow>R=R1 \<and> (\<exists>L TL i. R=<L|,|TL> \<and> \<Gamma> \<turnstile> \<lparr> t |;| \<sigma>1 \<rparr> |:| (TL!i) \<and> l = L!i \<and> i<length L \<and> length L = length TL \<and> distinct L)" 
    " \<Gamma> \<turnstile> \<lparr> Case t of L1 \<Rightarrow> B |;| \<sigma>1\<rparr> |:| A \<Longrightarrow>\<exists>TL. L1\<noteq>\<emptyset> \<and> length B = length L1 \<and> length L1 = length TL \<and> distinct L1 \<and>
      \<Gamma> \<turnstile> \<lparr> t |;| \<sigma>1 \<rparr> |:| <L1|,|TL> \<and> (\<forall>i<length L1. insert_nth (fst(B!i)) (TL!i) \<Gamma> \<turnstile> \<lparr>(snd(B!i))|;| \<sigma>1\<rparr> |:| A \<and> fst(B!i)\<le>length \<Gamma>)"
   "\<Gamma> \<turnstile> \<lparr> fix t |;| \<sigma>\<rparr> |:| A \<Longrightarrow> \<Gamma> \<turnstile> \<lparr> t |;| \<sigma>\<rparr> |:| A\<rightarrow>A"
proof -
  assume H:"\<Gamma> \<turnstile> \<lparr> Let var x := t in t1|;|\<sigma>\<rparr> |:| R"
  show " \<exists>A B. R = B \<and> \<Gamma> \<turnstile> \<lparr> t|;| \<sigma>\<rparr> |:| A \<and>x\<le>length \<Gamma>\<and> (insert_nth x A \<Gamma>) \<turnstile> \<lparr>t1|;| \<sigma>\<rparr> |:| B"
    using has_type_LetE[OF H] 
    by fastforce 
next
  assume H1: "\<Gamma> \<turnstile> \<lparr>Let pattern p := t1 in t2|;|\<sigma>1\<rparr> |:| R"
  show "\<exists>\<sigma> B. coherent p B \<and> Lmatch_Type p \<sigma>  \<and>  \<Gamma> \<turnstile> \<lparr>t1|;|\<sigma>1\<rparr> |:| B \<and>  \<Gamma> \<turnstile> \<lparr>t2|;|(\<sigma>1 ++ \<sigma>)\<rparr> |:| R"
    using has_type_LetPE[OF H1]
    by metis
next
  assume H2: "\<Gamma> \<turnstile> \<lparr>Case t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2|;|\<sigma>1\<rparr> |:| R"
  show "\<exists>A B C. R = C \<and> \<Gamma> \<turnstile> \<lparr>t|;|\<sigma>1\<rparr> |:| A |+| B \<and> x\<le>length \<Gamma> \<and> y\<le>length \<Gamma> \<and> insert_nth x A \<Gamma> \<turnstile> \<lparr>t1|;|\<sigma>1\<rparr> |:| C \<and> insert_nth y B \<Gamma> \<turnstile> \<lparr>t2|;|\<sigma>1\<rparr> |:| C"
    using has_type_CaseSE[OF H2]
    by fastforce
next
  assume H4: "\<Gamma> \<turnstile> \<lparr><l:=t> as R1|;|\<sigma>1\<rparr> |:| R"
  show  "R=R1 \<and> (\<exists>L TL i. R = <L|,|TL> \<and> \<Gamma> \<turnstile> \<lparr>t|;|\<sigma>1\<rparr> |:| (TL ! i) \<and> l = L ! i \<and> i<length L \<and> length L = length TL \<and> distinct L)"
    using has_type_VariantE[OF H4]
    by metis    
next
  assume H5: "\<Gamma> \<turnstile> \<lparr>Case t of L1 \<Rightarrow> B|;|\<sigma>1\<rparr> |:| A"
  show "\<exists>TL. L1\<noteq>\<emptyset> \<and> length B = length L1 \<and> length L1 = length TL  \<and> distinct L1 \<and>
      \<Gamma> \<turnstile> \<lparr> t |;| \<sigma>1 \<rparr> |:| <L1|,|TL> \<and> (\<forall>i<length L1. insert_nth (fst(B!i)) (TL!i) \<Gamma> \<turnstile> \<lparr>(snd(B!i))|;| \<sigma>1\<rparr> |:| A \<and> fst(B!i)\<le>length \<Gamma>)"
    using has_type_CaseVE[OF H5] insert_nth_take_drop append_Cons append_Nil 
    by metis
next
  assume H: "\<Gamma> \<turnstile> \<lparr> (ProjR l t)|;| \<sigma>\<rparr> |:| R"
  show "\<exists>m L TL. \<Gamma> \<turnstile> \<lparr>t |;| \<sigma>\<rparr> |:| \<lparr>L|:|TL\<rparr> \<and> index L l = m \<and> TL ! m = R \<and> distinct L \<and> length L = length TL
                              \<and> l \<in> set L"
    using has_type_ProjRE[OF H]
    by metis
qed (auto elim: has_type_L.cases has_type_ProjTE)

lemma simpl1: "nat (int x + 1) = Suc x" by simp
lemma simpl2: "nat (1 + int x) = Suc x" by simp

lemma simpl3: "nat (int x - 1) = x - 1" by simp 


lemma gr_Suc_conv: "Suc x \<le> n \<longleftrightarrow> (\<exists>m. n = Suc m \<and> x \<le> m)"
  by (cases n) auto


lemma fill_fill_comp:
  "(fill \<sigma> \<circ> fill \<sigma>1) t = fill (\<lambda>x. case \<sigma>1 x of None \<Rightarrow> \<sigma> x | Some t \<Rightarrow> Some (fill \<sigma> t)) t"
proof (induction t arbitrary:)
  case (Pattern p)
    show ?case
      proof (induction p)
        case (V n A)
          show ?case  by (cases "n\<notin>dom \<sigma>1") (simp add: domIff, force)+
      next 
      qed simp 
qed (auto intro: snds.intros)  

lemma Binder_FV_shift:
  fixes c x d::nat and t1 t2::lterm
  assumes  "(\<And>c1. FV (shift_L (int d) c1 t1) = (\<lambda>x. if c1 \<le> x then x + d else x) ` FV t1)"
              "(\<And>c1. FV (shift_L (int d) c1 t2) = (\<lambda>x. if c1 \<le> x then x + d else x) ` FV t2)"
  shows "(if c < x then FV (shift_L (int d) c t1) \<union> 
        (\<lambda>y. if nat (int x + int d) < y then y - 1 else y) `(FV(shift_L (int d) c t2)- {nat (int x + int d)})
        else FV(shift_L (int d) c t1) \<union> ((\<lambda>y. if x < y then y - 1 else y) ` (FV(shift_L (int d) (Suc c) t2)-{x}))) =
        (\<lambda>x. if c \<le> x then x + d else x) ` ((\<lambda>y. if x < y then y - 1 else y) ` (FV t2 - {x}) \<union> FV t1)"
using assms
proof -
  
  let ?S3= "\<lambda>c x t1 t2. (if c < x then FV (shift_L (int d) c t1) \<union> 
            (\<lambda>y. if nat (int x + int d) < y then y - 1 else y) `(FV(shift_L (int d) c t2)- {nat (int x + int d)})
            else FV(shift_L (int d) c t1) \<union> ((\<lambda>y. if x < y then y - 1 else y) ` (FV(shift_L (int d) (Suc c) t2)-{x})))"
      and  ?S4 ="\<lambda>c x t1 t2. (\<lambda>x. if c \<le> x then x + d else x) ` ((\<lambda>y. if x < y then y - 1 else y) ` (FV t2 - {x}) \<union> FV t1)"
  
   have simp_nat: "\<And>x. nat (int x + int d) = x + d" by auto
    have C1:"\<And>c x t1 t2. c < x \<Longrightarrow> (\<And>c1. FV (shift_L (int d) c1 t1) = (\<lambda>x. if c1 \<le> x then x + d else x) ` FV t1)
            \<Longrightarrow> (\<And>c1. FV (shift_L (int d) c1 t2) = (\<lambda>x. if c1 \<le> x then x + d else x) ` FV t2) \<Longrightarrow>?S3 c x t1 t2 \<subseteq> ?S4 c x t1 t2"
      proof -
        fix c::nat and x t1 t2
        assume supc:"c<x" and
               FV_s:"\<And>c. FV (shift_L (int d) c t1) = (\<lambda>x. if c \<le> x then x + d else x) ` FV t1"
                    "\<And>c. FV (shift_L (int d) c t2) = (\<lambda>x. if c \<le> x then x + d else x) ` FV t2"
        have " {y. \<exists>xa. ((\<exists>x. x \<in> FV t2 \<and> c \<le> x \<and> xa = x + d) \<or> xa \<in> FV t2 \<and> \<not> c \<le> xa) \<and>
                  xa \<noteq> nat (int x + int d) \<and> nat (int x + int d) < xa \<and> y = xa - Suc 0} \<subseteq> 
                  {y. \<exists>xa. ((\<exists>xb. xb \<in> FV t2 \<and> xb \<noteq> x \<and> x < xb \<and> xa = xb - Suc 0) \<or>
                 xa \<in> FV t2 \<and> xa \<noteq> x \<and> \<not> x < xa \<or> xa \<in> FV t1) \<and> c \<le> xa \<and> y = xa + d} \<union>
                 ({y. \<exists>xa. xa \<in> FV t2 \<and> xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0} \<union> (FV t2 - {x}) \<inter>
                  {y. \<not> x < y} \<union> FV t1) \<inter>  {x. \<not> c \<le> x}"
          proof (rule, simp)
            fix x1
            assume " \<exists>xaa. ((\<exists>x. x \<in> FV t2 \<and> c \<le> x \<and> xaa = x + d) \<or> xaa \<in> FV t2 \<and> \<not> c \<le> xaa) \<and>
               xaa \<noteq> nat (int x + int d) \<and> nat (int x + int d) < xaa \<and> x1 = xaa - Suc 0"
            then obtain xaa where H1:"((\<exists>x. x \<in> FV t2 \<and> c \<le> x \<and> xaa = x + d) \<or> xaa \<in> FV t2 \<and> \<not> c \<le> xaa)"
               "xaa \<noteq> nat (int x + int d)" "nat (int x + int d) < xaa" "x1 = xaa - Suc 0"
              by blast
            
            let ?goal= "(\<exists>xaa. ((\<exists>xb. xb \<in> FV t2 \<and> xb \<noteq> x \<and> x < xb \<and> xaa = xb - Suc 0) \<or>
                 xaa \<in> FV t2 \<and> xaa \<noteq> x \<and> \<not> x < xaa \<or> xaa \<in> FV t1) \<and> c \<le> xaa \<and> x1 = xaa + d) \<or>
                 ((\<exists>xaa. xaa \<in> FV t2 \<and> xaa \<noteq> x \<and> x < xaa \<and> x1 = xaa - Suc 0) \<or> x1 \<in> FV t2 \<and> x1 \<noteq> x \<and>
                 \<not> x < x1 \<or> x1 \<in> FV t1) \<and> \<not> c \<le> x1"

            have "(\<exists>x. x \<in> FV t2 \<and> c \<le> x \<and> xaa = x + d) \<Longrightarrow> ?goal"
              proof -
                assume "\<exists>x. x \<in> FV t2 \<and> c \<le> x \<and> xaa = x + d"
                then obtain xa where "xa \<in> FV t2" "c \<le> xa" "xaa = xa + d"
                  by blast
                hence "xa \<in> FV t2 \<and> xa \<noteq> x \<and> x < xa \<and> xa - Suc 0 = xa - Suc 0 \<and>
                        c \<le> xa - Suc 0 \<and> x1 = xa - Suc 0 + d"
                  using H1(2-)[unfolded simp_nat] supc
                  by force
                thus ?goal by metis
              qed      
            moreover have "xaa \<in> FV t2 \<and> \<not> c \<le> xaa \<Longrightarrow> ?goal"
              using H1(2-)[unfolded simp_nat] supc
              by simp
            ultimately show ?goal using H1(1) by satx
          qed       
  
        moreover have "({y. \<exists>x. x \<in> FV t2 \<and> c \<le> x \<and> y = x + d} \<union> FV t2 \<inter> {x. \<not> c \<le> x} - {nat (int x + int d)}) \<inter>
                {y. \<not> nat (int x + int d) < y} \<subseteq> {y. \<exists>xa. ((\<exists>xb. xb \<in> FV t2 \<and> xb \<noteq> x \<and> x < xb \<and> xa = xb - Suc 0) \<or>
                 xa \<in> FV t2 \<and> xa \<noteq> x \<and> \<not> x < xa \<or> xa \<in> FV t1) \<and> c \<le> xa \<and> y = xa + d} \<union>
                ({y. \<exists>xa. xa \<in> FV t2 \<and> xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0} \<union> (FV t2 - {x}) \<inter>
                {y. \<not> x < y} \<union> FV t1) \<inter> {x. \<not> c \<le> x}"
          using supc  by force
        
        moreover have " {y. \<exists>x. x \<in> FV t1 \<and> c \<le> x \<and> y = x + d} \<subseteq> {y. \<exists>xa. ((\<exists>xb. xb \<in> FV t2 \<and> xb \<noteq> x \<and> x < xb \<and> xa = xb - Suc 0) \<or>
                         xa \<in> FV t2 \<and> xa \<noteq> x \<and> \<not> x < xa \<or> xa \<in> FV t1) \<and> c \<le> xa \<and> y = xa + d} \<union>
                           ({y. \<exists>xa. xa \<in> FV t2 \<and> xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0} \<union> (FV t2 - {x}) \<inter> {y. \<not> x < y} \<union> FV t1) \<inter>
                           {x. \<not> c \<le> x}"
          using supc by force

        moreover have "FV t1 \<inter> {x. \<not> c \<le> x} \<subseteq> {y. \<exists>xa. ((\<exists>xb. xb \<in> FV t2 \<and> xb \<noteq> x \<and> x < xb \<and> xa = xb - Suc 0) \<or>
                        xa \<in> FV t2 \<and> xa \<noteq> x \<and> \<not> x < xa \<or> xa \<in> FV t1) \<and> c \<le> xa \<and> y = xa + d} \<union>
                          ({y. \<exists>xa. xa \<in> FV t2 \<and> xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0} \<union> (FV t2 - {x}) \<inter> 
                          {y. \<not> x < y} \<union> FV t1) \<inter> {x. \<not> c \<le> x}"
          by force

        ultimately show "?S3 c x t1 t2 \<subseteq> ?S4 c x t1 t2" 
          using supc 
          by (simp add: image_def FV_s Int_Collect Bex_def)
      qed
    have C2:"\<And>c x t1 t2. c < x \<Longrightarrow> (\<And>c. FV (shift_L (int d) c t1) = (\<lambda>x. if c \<le> x then x + d else x) ` FV t1)
            \<Longrightarrow> (\<And>c. FV (shift_L (int d) c t2) = (\<lambda>x. if c \<le> x then x + d else x) ` FV t2) \<Longrightarrow>?S4 c x t1 t2 \<subseteq> ?S3 c x t1 t2"
      proof -
        fix c::nat and x t1 t2
        assume supc:"c<x" and
               FV_s:"\<And>c. FV (shift_L (int d) c t1) = (\<lambda>x. if c \<le> x then x + d else x) ` FV t1"
                    "\<And>c. FV (shift_L (int d) c t2) = (\<lambda>x. if c \<le> x then x + d else x) ` FV t2"
        have "c<x \<Longrightarrow> ({y. \<exists>xa. xa \<in> FV t2 \<and> xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0} \<union> (FV t2 - {x}) \<inter> {y. \<not> x < y} \<union> FV t1) \<inter>
                {x. \<not> c \<le> x} \<subseteq> {y. \<exists>xa. ((\<exists>x. x \<in> FV t2 \<and> c \<le> x \<and> xa = x + d) \<or> xa \<in> FV t2 \<and> \<not> c \<le> xa) \<and>
                xa \<noteq> nat (int x + int d) \<and> nat (int x + int d) < xa \<and> y = xa - Suc 0} \<union>
               ({y. \<exists>x. x \<in> FV t2 \<and> c \<le> x \<and> y = x + d} \<union> FV t2 \<inter> {x. \<not> c \<le> x} - {nat (int x + int d)}) \<inter>
               {y. \<not> nat (int x + int d) < y} \<union> ({y. \<exists>x. x \<in> FV t1 \<and> c \<le> x \<and> y = x + d} \<union> FV t1
               \<inter> {x. \<not> c \<le> x})"
           by force  
        moreover have " c < x \<Longrightarrow> {y. \<exists>xa. ((\<exists>xb. xb \<in> FV t2 \<and> xb \<noteq> x \<and> x < xb \<and> xa = xb - Suc 0) \<or>
                        xa \<in> FV t2 \<and> xa \<noteq> x \<and> \<not> x < xa \<or> xa \<in> FV t1) \<and>  c \<le> xa \<and> y = xa + d}
                        \<subseteq> {y. \<exists>xa. ((\<exists>x. x \<in> FV t2 \<and> c \<le> x \<and> xa = x + d) \<or> xa \<in> FV t2 \<and> \<not> c \<le> xa) \<and>
                        xa \<noteq> nat (int x + int d) \<and> nat (int x + int d) < xa \<and> y = xa - Suc 0} \<union>
                        ({y. \<exists>x. x \<in> FV t2 \<and> c \<le> x \<and> y = x + d} \<union> FV t2 \<inter> {x. \<not> c \<le> x} - {nat (int x + int d)}) \<inter>
                        {y. \<not> nat (int x + int d) < y} \<union> ({y. \<exists>x. x \<in> FV t1 \<and> c \<le> x \<and> y = x + d} \<union> FV t1 \<inter> {x. \<not> c \<le> x})"
          proof (rule, simp)
            fix x1
            assume grc:"c<x"  and "\<exists>xaa. ((\<exists>xb. xb \<in> FV t2 \<and> xb \<noteq> x \<and> x < xb \<and> xaa = xb - Suc 0) \<or>
                                    xaa \<in> FV t2 \<and> xaa \<noteq> x \<and> \<not> x < xaa \<or> xaa \<in> FV t1) \<and> c \<le> xaa \<and> x1 = xaa + d"
            then obtain xaa where H1:"(\<exists>xb. xb \<in> FV t2 \<and> xb \<noteq> x \<and> x < xb \<and> xaa = xb - Suc 0) \<or>
                                    xaa \<in> FV t2 \<and> xaa \<noteq> x \<and> \<not> x < xaa \<or> xaa \<in> FV t1" "c \<le> xaa" "x1 = xaa + d"
              by blast
            let ?goal = "(\<exists>xaa. ((\<exists>x. x \<in> FV t2 \<and> c \<le> x \<and> xaa = x + d) \<or> xaa \<in> FV t2 \<and> \<not> c \<le> xaa) \<and>
                          xaa \<noteq> nat (int x + int d) \<and> nat (int x + int d) < xaa \<and> x1 = xaa - Suc 0) \<or>
                         ((\<exists>xa. xa \<in> FV t2 \<and> c \<le> xa \<and> x1 = xa + d) \<or> x1 \<in> FV t2 \<and> \<not> c \<le> x1) \<and>
                         x1 \<noteq> nat (int x + int d) \<and> \<not> nat (int x + int d) < x1 \<or>
                         (\<exists>xa. xa \<in> FV t1 \<and> c \<le> xa \<and> x1 = xa + d) \<or> x1 \<in> FV t1 \<and> \<not> c \<le> x1"
            have "\<exists>xb. xb \<in> FV t2 \<and> xb \<noteq> x \<and> x < xb \<and> xaa = xb - Suc 0 \<Longrightarrow> ?goal"
              proof -
                assume "\<exists>xb. xb \<in> FV t2 \<and> xb \<noteq> x \<and> x < xb \<and> xaa = xb - Suc 0"
                then obtain xb where "xb \<in> FV t2" "xb \<noteq> x" "x < xb" "xaa = xb - Suc 0"
                  by blast
                hence "xb \<in> FV t2 \<and> c \<le> xb \<and> xb+d \<noteq> nat (int x + int d) \<and> 
                        nat (int x + int d) < xb+d \<and> x1 = xb + d - Suc 0"
                  using H1(2-)[unfolded simp_nat] grc
                  by force
                thus ?goal by blast
              qed
            moreover have "xaa \<in> FV t2 \<and> xaa \<noteq> x \<and> \<not> x < xaa \<Longrightarrow> ?goal"
              using H1(2-)[unfolded simp_nat] grc
              by auto
            ultimately show ?goal using H1[unfolded simp_nat] grc by blast
          qed        
        ultimately show "?S4 c x t1 t2 \<subseteq> ?S3 c x t1 t2" 
          using supc 
          by (simp add: image_def FV_s Int_Collect Bex_def)
              (meson, auto simp add: inf_sup_aci(5))
      qed

     have C4:"\<And>c x t1 t2. \<not>c<x \<Longrightarrow> (\<And>c. FV (shift_L (int d) c t1) = (\<lambda>x. if c \<le> x then x + d else x) ` FV t1)
            \<Longrightarrow> (\<And>c. FV (shift_L (int d) c t2) = (\<lambda>x. if c \<le> x then x + d else x) ` FV t2) \<Longrightarrow> ?S3 c x t1 t2 \<subseteq> ?S4 c x t1 t2"
      proof -
        fix c::nat and x t1 t2
        assume infc: "\<not>c<x" and
               FV_s: "(\<And>c. FV (shift_L (int d) c t1) = (\<lambda>x. if c \<le> x then x + d else x) ` FV t1)"
                     " (\<And>c. FV (shift_L (int d) c t2) = (\<lambda>x. if c \<le> x then x + d else x) ` FV t2)"
        have " {y. \<exists>xa. ((\<exists>x. x \<in> FV t2 \<and> Suc c \<le> x \<and> xa = x + d) \<or> xa \<in> FV t2 \<and> \<not> Suc c \<le> xa) \<and>
                xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0} \<subseteq> {y. \<exists>xa. ((\<exists>xb. xb \<in> FV t2 \<and> xb \<noteq> x \<and> x < xb \<and>
                xa = xb - Suc 0) \<or> xa \<in> FV t2 \<and> xa \<noteq> x \<and> \<not> x < xa \<or> xa \<in> FV t1) \<and>
                c \<le> xa \<and> y = xa + d} \<union> ({y. \<exists>xa. xa \<in> FV t2 \<and> xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0} \<union>
                (FV t2 - {x}) \<inter> {y. \<not> x < y} \<union> FV t1) \<inter> {x. \<not> c \<le> x}"
        proof (rule, simp)
          (*generated with sledgehammer*)
          fix xa :: nat
          assume a1: "\<exists>xaa. ((\<exists>x. x \<in> FV t2 \<and> Suc c \<le> x \<and> xaa = x + d) \<or> xaa \<in> FV t2 \<and> \<not> Suc c \<le> xaa) \<and> xaa \<noteq> x \<and> x < xaa \<and> xa = xaa - Suc 0"
          obtain nna :: nat where
            f2: "(\<exists>v0. ((\<exists>v1. v1 \<in> FV t2 \<and> Suc c \<le> v1 \<and> v0 = v1 + d) \<or> v0 \<in> FV t2 \<and> \<not> Suc c \<le> v0) \<and> v0 \<noteq> x \<and> x < v0 \<and> xa = v0 - Suc 0) = (((\<exists>v1. v1 \<in> FV t2 \<and> Suc c \<le> v1 \<and> nna = v1 + d) \<or> nna \<in> FV t2 \<and> \<not> Suc c \<le> nna) \<and> nna \<noteq> x \<and> x < nna \<and> xa = nna - Suc 0)"
            by moura
          obtain nn :: nat where
             "(\<exists>v1. v1 \<in> FV t2 \<and> Suc c \<le> v1 \<and> nna = v1 + d) = (nn \<in> FV t2 \<and> Suc c \<le> nn \<and> nna = nn + d)"
            by moura
          then have f3: "(nn \<in> FV t2 \<and> Suc c \<le> nn \<and> nna = nn + d \<or> nna \<in> FV t2 \<and> \<not> Suc c \<le> nna) \<and> nna \<noteq> x \<and> x < nna \<and> xa = nna - Suc 0"
            using f2 a1 by presburger
          then have f4: "nna \<in> FV t2 \<and> \<not> Suc c \<le> nna \<longrightarrow> \<not> c \<le> xa"
            by (simp add: gr_Suc_conv)
          obtain nnb :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
            f5: "(\<not> Suc c \<le> nn \<or> nn = Suc (nnb nn c) \<and> c \<le> nnb nn c) \<and> (Suc c \<le> nn \<or> (\<forall>n. nn \<noteq> Suc n \<or> \<not> c \<le> n))"
            by (metis gr_Suc_conv)
          have "nn - Suc c + Suc c = nn \<and> Suc 0 \<le> nn \<and> nnb nn c = nn - Suc 0 \<and> nn = x \<longrightarrow> nn \<noteq> Suc (nnb nn c) \<or> \<not> c \<le> nnb nn c"
            by (metis (no_types) infc not_less_eq ordered_cancel_comm_monoid_diff_class.add_diff_inverse trans_less_add2)
          moreover
          { assume "nn \<noteq> x"
            { assume "nn \<noteq> x \<and> x < nn"
              moreover
              { assume "(\<exists>n. n \<in> FV t2 \<and> n \<noteq> x \<and> x < n \<and> nnb nn c = n - Suc 0) \<or> nnb nn c \<in> FV t2 \<and> nnb nn c \<noteq> x \<and> \<not> x < nnb nn c \<or> nnb nn c \<in> FV t1"
                moreover
                { assume "xa \<noteq> nnb nn c + d"
                  then have "Suc 0 \<le> nn \<and> nnb nn c = nn - Suc 0 \<longrightarrow> nn \<notin> FV t2 \<or> \<not> Suc c \<le> nn \<or> nna \<noteq> nn + d"
                    using f3 by (metis (no_types) Nat.add_diff_assoc2) }
                ultimately have "Suc 0 \<le> nn \<and> nnb nn c = nn - Suc 0 \<longrightarrow> (nn \<notin> FV t2 \<or> \<not> Suc c \<le> nn \<or> nna \<noteq> nn + d) \<or> (nn \<noteq> Suc (nnb nn c) \<or> \<not> c \<le> nnb nn c) \<or> (\<exists>n. ((\<exists>na. na \<in> FV t2 \<and> na \<noteq> x \<and> x < na \<and> n = na - Suc 0) \<or> n \<in> FV t2 \<and> n \<noteq> x \<and> \<not> x < n \<or> n \<in> FV t1) \<and> c \<le> n \<and> xa = n + d) \<or> ((\<exists>n. n \<in> FV t2 \<and> n \<noteq> x \<and> x < n \<and> xa = n - Suc 0) \<or> xa \<in> FV t2 \<and> xa \<noteq> x \<and> \<not> x < xa \<or> xa \<in> FV t1) \<and> \<not> c \<le> xa"
                  by blast }
              ultimately have "Suc 0 \<le> nn \<and> nnb nn c = nn - Suc 0 \<longrightarrow> (nn \<notin> FV t2 \<or> \<not> Suc c \<le> nn \<or> nna \<noteq> nn + d) \<or> (nn \<noteq> Suc (nnb nn c) \<or> \<not> c \<le> nnb nn c) \<or> (\<exists>n. ((\<exists>na. na \<in> FV t2 \<and> na \<noteq> x \<and> x < na \<and> n = na - Suc 0) \<or> n \<in> FV t2 \<and> n \<noteq> x \<and> \<not> x < n \<or> n \<in> FV t1) \<and> c \<le> n \<and> xa = n + d) \<or> ((\<exists>n. n \<in> FV t2 \<and> n \<noteq> x \<and> x < n \<and> xa = n - Suc 0) \<or> xa \<in> FV t2 \<and> xa \<noteq> x \<and> \<not> x < xa \<or> xa \<in> FV t1) \<and> \<not> c \<le> xa"
                by blast }
            moreover
            { assume "\<not> x < nn"
              then have "nn - Suc c + Suc c \<noteq> nn"
                by (metis (no_types) infc not_less_eq trans_less_add2) }
            ultimately have "nn - Suc c + Suc c = nn \<and> Suc 0 \<le> nn \<and> nnb nn c = nn - Suc 0 \<longrightarrow> (nn \<notin> FV t2 \<or> \<not> Suc c \<le> nn \<or> nna \<noteq> nn + d) \<or> (nn \<noteq> Suc (nnb nn c) \<or> \<not> c \<le> nnb nn c) \<or> (\<exists>n. ((\<exists>na. na \<in> FV t2 \<and> na \<noteq> x \<and> x < na \<and> n = na - Suc 0) \<or> n \<in> FV t2 \<and> n \<noteq> x \<and> \<not> x < n \<or> n \<in> FV t1) \<and> c \<le> n \<and> xa = n + d) \<or> ((\<exists>n. n \<in> FV t2 \<and> n \<noteq> x \<and> x < n \<and> xa = n - Suc 0) \<or> xa \<in> FV t2 \<and> xa \<noteq> x \<and> \<not> x < xa \<or> xa \<in> FV t1) \<and> \<not> c \<le> xa"
              by fastforce }
          moreover
          { assume "nn - Suc c + Suc c \<noteq> nn"
            then have "nn \<notin> FV t2 \<or> \<not> Suc c \<le> nn \<or> nna \<noteq> nn + d"
              using le_add_diff_inverse2 by blast }
          moreover
          { assume "nn \<noteq> Suc (nnb nn c) \<or> \<not> c \<le> nnb nn c"
            then have "nn \<notin> FV t2 \<or> \<not> Suc c \<le> nn \<or> nna \<noteq> nn + d"
              using f5 by fastforce }
          moreover
          { assume "\<not> Suc 0 \<le> nn"
            then have "nn \<noteq> Suc (nnb nn c) \<or> \<not> c \<le> nnb nn c"
              by simp }
          moreover
          { assume "nnb nn c \<noteq> nn - Suc 0"
            then have "nn \<noteq> Suc (nnb nn c) \<or> \<not> c \<le> nnb nn c"
              by (metis (no_types) One_nat_def diff_Suc_1) }
          moreover
          { assume "nn \<notin> FV t2 \<or> \<not> Suc c \<le> nn \<or> nna \<noteq> nn + d"
            then have "(nna \<in> FV t2 \<and> \<not> Suc c \<le> nna) \<and> ((\<exists>n. n \<in> FV t2 \<and> n \<noteq> x \<and> x < n \<and> xa = n - Suc 0) \<or> xa \<in> FV t2 \<and> xa \<noteq> x \<and> \<not> x < xa \<or> xa \<in> FV t1)"
              using f3 by blast
            then have "(\<exists>n. ((\<exists>na. na \<in> FV t2 \<and> na \<noteq> x \<and> x < na \<and> n = na - Suc 0) \<or> n \<in> FV t2 \<and> n \<noteq> x \<and> \<not> x < n \<or> n \<in> FV t1) \<and> c \<le> n \<and> xa = n + d) \<or> ((\<exists>n. n \<in> FV t2 \<and> n \<noteq> x \<and> x < n \<and> xa = n - Suc 0) \<or> xa \<in> FV t2 \<and> xa \<noteq> x \<and> \<not> x < xa \<or> xa \<in> FV t1) \<and> \<not> c \<le> xa"
              using f4 by force }
          ultimately show "(\<exists>n. ((\<exists>na. na \<in> FV t2 \<and> na \<noteq> x \<and> x < na \<and> n = na - Suc 0) \<or> n \<in> FV t2 \<and> n \<noteq> x \<and> \<not> x < n \<or> n \<in> FV t1) \<and> c \<le> n \<and> xa = n + d) \<or> ((\<exists>n. n \<in> FV t2 \<and> n \<noteq> x \<and> x < n \<and> xa = n - Suc 0) \<or> xa \<in> FV t2 \<and> xa \<noteq> x \<and> \<not> x < xa \<or> xa \<in> FV t1) \<and> \<not> c \<le> xa"
            by satx
        qed
      
        then show "?S3 c x t1 t2 \<subseteq> ?S4 c x t1 t2"
           using infc
           by (simp add: image_def FV_s Int_Collect Bex_def) force
      qed
     
    have "\<And>c x t1 t2. \<not>c<x \<Longrightarrow>(\<And>c. FV (shift_L (int d) c t1) = (\<lambda>x. if c \<le> x then x + d else x) ` FV t1)
            \<Longrightarrow> (\<And>c. FV (shift_L (int d) c t2) = (\<lambda>x. if c \<le> x then x + d else x) ` FV t2) 
            \<Longrightarrow>?S4 c x t1 t2 \<subseteq> ?S3 c x t1 t2"
     proof -
       fix c::nat and x t1 t2
       assume infc:"\<not>c<x" and
              FV_s: "(\<And>c. FV (shift_L (int d) c t1) = (\<lambda>x. if c \<le> x then x + d else x) ` FV t1)"
                    "(\<And>c. FV (shift_L (int d) c t2) = (\<lambda>x. if c \<le> x then x + d else x) ` FV t2)"
       have "\<not> c < x \<Longrightarrow>
        {y. \<exists>xa. ((\<exists>xb. xb \<in> FV t2 \<and> xb \<noteq> x \<and> x < xb \<and> xa = xb - Suc 0) \<or> xa \<in> FV t2 \<and> xa \<noteq> x \<and> \<not> x < xa \<or> xa \<in> FV t1) \<and>
         c \<le> xa \<and> y = xa + d} \<subseteq> {y. \<exists>x. x \<in> FV t1 \<and> c \<le> x \<and> y = x + d} \<union> FV t1 \<inter> {x. \<not> c \<le> x} \<union>
         ({y. \<exists>xa. ((\<exists>x. x \<in> FV t2 \<and> Suc c \<le> x \<and> xa = x + d) \<or> xa \<in> FV t2 \<and> \<not> Suc c \<le> xa) \<and>
         xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0} \<union> ({y. \<exists>x. x \<in> FV t2 \<and> Suc c \<le> x \<and> y = x + d} \<union> 
         FV t2 \<inter> {x. \<not> Suc c \<le> x} - {x}) \<inter> {y. \<not> x < y})"
         proof (rule, simp)
            (*generated with sledgehammer*)
            fix xa :: nat
            assume a1: "\<exists>xb. ((\<exists>xa. xa \<in> FV t2 \<and> xa \<noteq> x \<and> x < xa \<and> xb = xa - Suc 0) \<or> xb \<in> FV t2 \<and> xb \<noteq> x \<and> \<not> x < xb \<or> xb \<in> FV t1) \<and> c \<le> xb \<and> xa = xb + d"
            assume a2: "\<not> c < x"
            obtain nna :: nat where
              f3:"(\<exists>v0. ((\<exists>v1. v1 \<in> FV t2 \<and> v1 \<noteq> x \<and> x < v1 \<and> v0 = v1 - Suc 0) \<or> v0 \<in> FV t2 \<and> v0 \<noteq> x \<and> \<not> x < v0 \<or> v0 \<in> FV t1) \<and> c \<le> v0 \<and> xa = v0 + d) = (((\<exists>v1. v1 \<in> FV t2 \<and> v1 \<noteq> x \<and> x < v1 \<and> nna = v1 - Suc 0) \<or> nna \<in> FV t2 \<and> nna \<noteq> x \<and> \<not> x < nna \<or> nna \<in> FV t1) \<and> c \<le> nna \<and> xa = nna + d)"
              by moura
            obtain nn :: nat where
              "(\<exists>v1. v1 \<in> FV t2 \<and> v1 \<noteq> x \<and> x < v1 \<and> nna = v1 - Suc 0) = (nn \<in> FV t2 \<and> nn \<noteq> x \<and> x < nn \<and> nna = nn - Suc 0)"
              by moura
            then have f4: "(nn \<in> FV t2 \<and> nn \<noteq> x \<and> x < nn \<and> nna = nn - Suc 0 \<or> nna \<in> FV t2 \<and> nna \<noteq> x \<and> \<not> x < nna \<or> nna \<in> FV t1) \<and> c \<le> nna \<and> xa = nna + d"
              using f3 a1 by presburger
            have f5: "\<forall>n na. \<not> n \<le> na \<or> n < Suc na"
              using le_imp_less_Suc by satx
            have f6: "\<forall>n na. \<not> n < na \<or> Suc n \<le> na"
              by simp
            obtain nnb :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
              "\<forall>x0 x1. (\<exists>v2>0. x1 + v2 = x0) = (0 < nnb x0 x1 \<and> x1 + nnb x0 x1 = x0)"
              by moura
            then have f7: "\<forall>n na. \<not> n < na \<or> 0 < nnb na n \<and> n + nnb na n = na"
              using less_imp_add_positive by presburger
            have f8: "\<forall>n na. \<not> (n::nat) \<le> na \<or> n + (na - n) = na"
              by fastforce
            have f9: "0 < Suc nna"
              by force
            have f10: "nna \<notin> FV t2 \<or> nna = x \<or> x < nna"
              using f8 f4 a2 by (metis le_neq_implies_less linorder_neqE_nat trans_less_add1)
            have "nn = Suc nna \<longrightarrow> (nn \<notin> FV t2 \<or> nn = x \<or> \<not> x < nn \<or> nna \<noteq> nn - Suc 0) \<or> (\<exists>n. n \<in> FV t1 \<and> c \<le> n \<and> xa = n + d) \<or> xa \<in> FV t1 \<and> \<not> c \<le> xa \<or> (\<exists>n. ((\<exists>na. na \<in> FV t2 \<and> Suc c \<le> na \<and> n = na + d) \<or> n \<in> FV t2 \<and> \<not> Suc c \<le> n) \<and> n \<noteq> x \<and> x < n \<and> xa = n - Suc 0) \<or> ((\<exists>n. n \<in> FV t2 \<and> Suc c \<le> n \<and> xa = n + d) \<or> xa \<in> FV t2 \<and> \<not> Suc c \<le> xa) \<and> xa \<noteq> x \<and> \<not> x < xa"
              using f9 f6 f5 f4 a2 by (metis (no_types) Nat.add_diff_assoc2 trans_less_add1)
            moreover
            { assume "nn \<noteq> Suc nna"
              then have "nn \<notin> FV t2 \<or> nn = x \<or> \<not> x < nn \<or> nna \<noteq> nn - Suc 0"
                using f9 f8 f7 f6 by (metis (no_types) One_nat_def add_gr_0 diff_Suc_1) }
            ultimately have "((\<exists>n. n \<in> FV t1 \<and> c \<le> n \<and> xa = n + d) \<or> xa \<in> FV t1 \<and> \<not> c \<le> xa \<or> (\<exists>n. ((\<exists>na. na \<in> FV t2 \<and> Suc c \<le> na \<and> n = na + d) \<or> n \<in> FV t2 \<and> \<not> Suc c \<le> n) \<and> n \<noteq> x \<and> x < n \<and> xa = n - Suc 0) \<or> ((\<exists>n. n \<in> FV t2 \<and> Suc c \<le> n \<and> xa = n + d) \<or> xa \<in> FV t2 \<and> \<not> Suc c \<le> xa) \<and> xa \<noteq> x \<and> \<not> x < xa) \<or> nn \<notin> FV t2 \<or> nn = x \<or> \<not> x < nn \<or> nna \<noteq> nn - Suc 0"
              by fastforce
            then show "(\<exists>n. n \<in> FV t1 \<and> c \<le> n \<and> xa = n + d) \<or> xa \<in> FV t1 \<and> \<not> c \<le> xa \<or> (\<exists>n. ((\<exists>na. na \<in> FV t2 \<and> Suc c \<le> na \<and> n = na + d) \<or> n \<in> FV t2 \<and> \<not> Suc c \<le> n) \<and> n \<noteq> x \<and> x < n \<and> xa = n - Suc 0) \<or> ((\<exists>n. n \<in> FV t2 \<and> Suc c \<le> n \<and> xa = n + d) \<or> xa \<in> FV t2 \<and> \<not> Suc c \<le> xa) \<and> xa \<noteq> x \<and> \<not> x < xa"
              using f10 f4 by auto
         qed
         
        
       then show "?S4 c x t1 t2 \<subseteq> ?S3 c x t1 t2"
         using infc
         by (simp add: image_def FV_s Int_Collect Bex_def) fastforce
     qed   

    note H= C1 C2  C4 this

    show "?S3 c x t1 t2 = ?S4 c x t1 t2"
      using H[of c x t1 t2] assms
      by (cases "c<x") fast+      
qed


lemma FV_shift:
  "FV (shift_L (int d) c t) = image (\<lambda>x. if x \<ge> c then x + d else x) (FV t)"
proof (induction t arbitrary: c rule: lterm.induct)
  case (LAbs T t)      
    thus ?case        
      by (auto simp: gr_Suc_conv image_iff) force+
next
  case (Tuple L)
    have "\<And>xa c. xa \<in> set L \<Longrightarrow> FV (shift_L (int d) c xa) = (\<lambda>x. if c \<le> x then x + d else x) ` FV xa"
      proof -
        fix xa c
        assume H:"xa \<in> set L" 
        show "FV (shift_L (int d) c xa) = (\<lambda>x. if c \<le> x then x + d else x) ` FV xa"
          using H[unfolded in_set_conv_nth] Tuple(1)[OF H]
          by blast
      qed          
    thus ?case by auto 
next
  case (Record L LT)
    have "\<And>xa c. xa \<in> set LT \<Longrightarrow> FV (shift_L (int d) c xa) = (\<lambda>x. if c \<le> x then x + d else x) ` FV xa"
      proof -
        fix xa c
        assume H:"xa \<in> set LT" 
        show "FV (shift_L (int d) c xa) = (\<lambda>x. if c \<le> x then x + d else x) ` FV xa"
          using H[unfolded in_set_conv_nth] Record(1)[OF H]
          by blast
      qed          
    thus ?case by auto        
next
    case (LetBinder x t1 t2)
    note hyps=this
    let ?S3= "\<lambda>x t1 t2. (if c < x then FV (shift_L (int d) c t1) \<union> 
                  (\<lambda>y. if nat (int x + int d) < y then y - 1 else y) `(FV(shift_L (int d) c t2)- {nat (int x + int d)})
        else FV(shift_L (int d) c t1) \<union> ((\<lambda>y. if x < y then y - 1 else y) ` (FV(shift_L (int d) (Suc c) t2)-{x})))"
   
    have A:" FV (if c < x then Let var nat (int x + int d) := shift_L (int d) c t1 in shift_L (int d) c t2
              else Let var x := shift_L (int d) c t1 in shift_L (int d) (Suc c) t2) = ?S3 x t1 t2"
      by auto

    show ?case
      using Binder_FV_shift[of d t1 t2 c x,OF hyps]
      by (simp only: shift_L.simps FV.simps A)
      
next
  case (CaseSum t x t1 y t2)
    note hyps = this(1-3) 
    have simp_nat: "nat (int x + int d) = x+d" 
                   "nat (int y + int d) = y+d"
      by force+
   
    let ?P1 = "(\<lambda>y. if (if c < x then nat (int x + int d) else x) < y then y - 1 else y) `
              (FV (shift_L (int d) (if x \<le> c then Suc c else c) t1) - {if c < x then nat (int x + int d) else x}) \<union>
              (\<lambda>z. if (if c < y then nat (int y + int d) else y) < z then z - 1 else z) `
              (FV (shift_L (int d) (if y \<le> c then Suc c else c) t2) - {if c < y then nat (int y + int d) else y}) \<union>
              FV (shift_L (int d) c t)" and
        ?P2 = "(if c < x then FV (shift_L (int d) c t) \<union> (\<lambda>y. if nat (int x + int d) < y then y - 1 else y) `
                (FV (shift_L (int d) c t1) - {nat (int x + int d)}) else FV (shift_L (int d) c t) \<union>
                (\<lambda>y. if x < y then y - 1 else y) ` (FV (shift_L (int d) (Suc c) t1) - {x})) \<union> 
               (if c < y then FV (shift_L (int d) c t) \<union> (\<lambda>ya. if nat (int y + int d) < ya then ya - 1 else ya) `
               (FV (shift_L (int d) c t2) - {nat (int y + int d)})  else FV (shift_L (int d) c t) \<union>
               (\<lambda>ya. if y < ya then ya - 1 else ya) ` (FV (shift_L (int d) (Suc c) t2) - {y}))" 

    have "?P1 = ?P2"
      by force     
 
    thus "?case"
      using Binder_FV_shift[of d t t1 c x,OF hyps(1,2)] 
            Binder_FV_shift[of d t t2 c y, OF hyps(1,3)]
      by (force simp only: shift_L.simps FV.simps if_True if_False)

next
  case (CaseVar t L B)
    note hyps=this  
    have simp_nat: "\<And>x. nat (int x + int d) = x+d" by force
    let ?f= "\<lambda>p. (if c < fst p then nat (int (fst p) + int d) else fst p,
                           shift_L (int d) (if fst p \<le> c then Suc c else c) (snd p))"
        and ?fv="(\<lambda>p. (\<lambda>y. if fst p < y then y - 1 else y) ` (FV (snd p) - {fst p}))"
        and ?S = "\<lambda>i. (if c < fst (B ! i) then
                  (\<lambda>y. if nat (int (fst (B ! i)) + int d) < y then y - 1 else y) `
                  (FV (shift_L (int d) c (snd (B ! i))) - {nat (int (fst (B ! i)) + int d)})
                  else (\<lambda>y. if fst (B ! i) < y then y - 1 else y) `
                  (FV (shift_L (int d) (Suc c) (snd (B ! i))) - {fst (B ! i)}))"
    have shift_simp: "\<And>i c1. i<length B \<Longrightarrow> FV (shift_L (int d) c1 (snd (B ! i))) =
                      (\<lambda>x. if c1 \<le> x then x + d else x) ` FV (snd (B ! i))"
      using hyps(2)[of "B!_" "snd(B!_)"] in_set_conv_nth[of _ B]
            snds.intros[of "B!_"]
      by blast

    have B2:"(\<Union>l\<in>(\<lambda>p. (\<lambda>y. if fst p < y then y - 1 else y) ` (FV (snd p) - {fst p})) ` set B. l) = 
             (\<Union>i<length B. (\<lambda>p. (\<lambda>y. if fst p < y then y - 1 else y) ` (FV (snd p) - {fst p})) (B!i))"
      by (simp only: in_set_conv_nth[of _ B] image_def[of _ "set B", unfolded Bex_def]
                     Collect_ex_eq) blast

    have B1:"(\<Union>l\<in>?fv ` ?f ` set B. l)= (\<Union>i<length B. (?fv \<circ>?f) (B!i))"
      by (simp only: in_set_conv_nth[of _ B] image_def[of "?fv \<circ> ?f" "set B", unfolded Bex_def]
                        image_comp[of ?fv ?f] Collect_ex_eq) blast
   
    have A:"FV (shift_L (int d) c t) \<union> ... = (\<Union>i<length B. ?S i) \<union>  FV (shift_L (int d) c t)"
      by (simp only: Un_commute Fun.comp_apply fst_conv simp_nat) fastforce
    

    have A2: "\<And>i. (if c < fst (B ! i)
             then FV (shift_L (int d) c t) \<union>
                  (\<lambda>y. if nat (int (fst (B ! i)) + int d) < y then y - 1 else y) `
                  (FV (shift_L (int d) c (snd (B ! i))) - {nat (int (fst (B ! i)) + int d)})
             else FV (shift_L (int d) c t) \<union>
                  (\<lambda>y. if fst (B ! i) < y then y - 1 else y) `
                  (FV (shift_L (int d) (Suc c) (snd (B ! i))) - {fst (B ! i)})) = ?S i \<union> FV (shift_L (int d) c t) "
      by force

    have H1:"\<And>i. i<length B \<Longrightarrow> (if c < fst (B ! i)
        then (\<lambda>y. if nat (int (fst (B ! i)) + int d) < y then y - 1 else y) `
             (FV (shift_L (int d) c (snd (B ! i))) - {nat (int (fst (B ! i)) + int d)})
        else (\<lambda>y. if fst (B ! i) < y then y - 1 else y) `
             (FV (shift_L (int d) (Suc c) (snd (B ! i))) - {fst (B ! i)})) =
          (\<lambda>x. if c \<le> x then x + d else x) `
        (\<lambda>y. if fst (B ! i) < y then y - 1 else y) ` (FV (snd (B ! i)) - {fst (B ! i)})"
      proof -
        fix i
        assume Ha:"i<length B"
        have s_nat: "\<And>x. nat(int x + int d) = x + d" by force
        have A:" c < fst (B ! i) \<Longrightarrow>
                {y. \<exists>x. ((\<exists>xa. xa \<in> FV (snd (B ! i)) \<and> c \<le> xa \<and> x = xa + d) \<or> x \<in> FV (snd (B ! i)) \<and> \<not> c \<le> x) \<and>
                        x \<noteq> nat (int (fst (B ! i)) + int d) \<and> nat (int (fst (B ! i)) + int d) < x \<and> y = x - Suc 0} \<union>
                ({y. \<exists>x. x \<in> FV (snd (B ! i)) \<and> c \<le> x \<and> y = x + d} \<union> FV (snd (B ! i)) \<inter> {x. \<not> c \<le> x} -
                 {nat (int (fst (B ! i)) + int d)}) \<inter>
                {y. \<not> nat (int (fst (B ! i)) + int d) < y} =
                {y. \<exists>x. ((\<exists>xa. xa \<in> FV (snd (B ! i)) \<and> xa \<noteq> fst (B ! i) \<and> fst (B ! i) < xa \<and> x = xa - Suc 0) \<or>
                         x \<in> FV (snd (B ! i)) \<and> x \<noteq> fst (B ! i) \<and> \<not> fst (B ! i) < x) \<and>
                        c \<le> x \<and> y = x + d} \<union>
                ({y. \<exists>x. x \<in> FV (snd (B ! i)) \<and> x \<noteq> fst (B ! i) \<and> fst (B ! i) < x \<and> y = x - Suc 0} \<union>
                 (FV (snd (B ! i)) - {fst (B ! i)}) \<inter> {y. \<not> fst (B ! i) < y}) \<inter>
                {x. \<not> c \<le> x}"
        proof -
          assume AH:"c<fst(B!i)"
          have 1: " \<And>x. c < fst (B ! i) \<Longrightarrow>
           (\<exists>xa. ((\<exists>x. x \<in> FV (snd (B ! i)) \<and> c \<le> x \<and> xa = x + d) \<or> xa \<in> FV (snd (B ! i)) \<and> \<not> c \<le> xa) \<and>
                 xa \<noteq> nat (int (fst (B ! i)) + int d) \<and>
                 nat (int (fst (B ! i)) + int d) < xa \<and> x = xa - Suc 0) \<or>
           ((\<exists>xa. xa \<in> FV (snd (B ! i)) \<and> c \<le> xa \<and> x = xa + d) \<or> x \<in> FV (snd (B ! i)) \<and> \<not> c \<le> x) \<and>
           x \<noteq> nat (int (fst (B ! i)) + int d) \<and> \<not> nat (int (fst (B ! i)) + int d) < x \<Longrightarrow>
           (\<exists>xa. ((\<exists>x. x \<in> FV (snd (B ! i)) \<and> x \<noteq> fst (B ! i) \<and> fst (B ! i) < x \<and> xa = x - Suc 0) \<or>
                  xa \<in> FV (snd (B ! i)) \<and> xa \<noteq> fst (B ! i) \<and> \<not> fst (B ! i) < xa) \<and>
                 c \<le> xa \<and> x = xa + d) \<or>
           ((\<exists>xa. xa \<in> FV (snd (B ! i)) \<and> xa \<noteq> fst (B ! i) \<and> fst (B ! i) < xa \<and> x = xa - Suc 0) \<or>
            x \<in> FV (snd (B ! i)) \<and> x \<noteq> fst (B ! i) \<and> \<not> fst (B ! i) < x) \<and>
           \<not> c \<le> x"
            proof (meson, simp_all)
              fix xb
              show "c < fst (B ! i) \<Longrightarrow> nat (int (fst (B ! i)) + int d) < xb + d \<Longrightarrow> xb \<in> FV (snd (B ! i))
                    \<Longrightarrow> c \<le> xb \<Longrightarrow> \<forall>xa\<ge>c. (\<forall>x>fst (B ! i). x \<in> FV (snd (B ! i)) \<longrightarrow> xa \<noteq> x - Suc 0) \<and>
                    (xa \<in> FV (snd (B ! i)) \<longrightarrow> xa = fst (B ! i) \<or> fst (B ! i) < xa) \<or> xb + d - Suc 0 \<noteq> xa + d \<Longrightarrow>
                    \<forall>xa>fst (B ! i). xa \<in> FV (snd (B ! i)) \<longrightarrow> xb + d - Suc 0 \<noteq> xa - Suc 0 \<Longrightarrow>
                    xb + d - Suc 0 \<in> FV (snd (B ! i))"                         
              proof (simp add: s_nat)
                assume a1: "c < fst (B ! i)"
                assume a2: "fst (B ! i) < xb"
                assume a3: "xb \<in> FV (snd (B ! i))"
                assume a4: "\<forall>xa\<ge>c. (\<forall>x>fst (B ! i). x \<in> FV (snd (B ! i)) \<longrightarrow> xa \<noteq> x - Suc 0) \<and> (xa \<in> FV (snd (B ! i)) \<longrightarrow> xa = fst (B ! i) \<or> fst (B ! i) < xa) \<or> xb + d - Suc 0 \<noteq> xa + d"
                have f5: "Suc c \<le> xb"
                  using a2 a1 by (meson Suc_leI less_SucI less_le_trans)
                have "\<forall>n na. \<exists>nb. \<not> na < n \<or> Suc (na + nb) = n"
                  using less_imp_Suc_add by blast
                then show ?thesis
                  using f5 a4 a3 a2 by (metis (no_types) Nat.add_diff_assoc2 One_nat_def Suc_leI Suc_le_mono add_gr_0 diff_Suc_1 less_imp_add_positive)
              qed              
            next
              fix xb
              show " c < fst (B ! i) \<Longrightarrow> nat (int (fst (B ! i)) + int d) < xb + d \<Longrightarrow> xb \<in> FV (snd (B ! i)) \<Longrightarrow>
                    c \<le> xb \<Longrightarrow> \<forall>xa\<ge>c. (\<forall>x>fst (B ! i). x \<in> FV (snd (B ! i)) \<longrightarrow> xa \<noteq> x - Suc 0) \<and>
                    (xa \<in> FV (snd (B ! i)) \<longrightarrow> xa = fst (B ! i) \<or> fst (B ! i) < xa) \<or> fst (B ! i) \<noteq> xa + d
                    \<Longrightarrow> \<forall>xa>fst (B ! i). xa \<in> FV (snd (B ! i)) \<longrightarrow> fst (B ! i) \<noteq> xa - Suc 0 \<Longrightarrow>
                    xb + d - Suc 0 = fst (B ! i) \<Longrightarrow> False"
                by (force simp add: s_nat)
            next
              fix xb
              show "c < fst (B ! i) \<Longrightarrow> nat (int (fst (B ! i)) + int d) < xb + d \<Longrightarrow> xb \<in> FV (snd (B ! i))
                    \<Longrightarrow> c \<le> xb \<Longrightarrow> \<forall>xa\<ge>c. (\<forall>x>fst (B ! i). x \<in> FV (snd (B ! i)) \<longrightarrow> xa \<noteq> x - Suc 0) \<and>
                    (xa \<in> FV (snd (B ! i)) \<longrightarrow> xa = fst (B ! i) \<or> fst (B ! i) < xa) \<or>
                    xb + d - Suc 0 \<noteq> xa + d \<Longrightarrow> \<forall>xa>fst (B ! i). xa \<in> FV (snd (B ! i)) \<longrightarrow> xb + d - Suc 0 \<noteq> xa - Suc 0 \<Longrightarrow>
                    fst (B ! i) < xb + d - Suc 0 \<Longrightarrow> False"
                proof (simp add: s_nat)
                  assume a1: "c < fst (B ! i)"
                  assume a2: "fst (B ! i) < xb"
                  assume a3: "xb \<in> FV (snd (B ! i))"
                  assume "\<forall>xa\<ge>c. (\<forall>x>fst (B ! i). x \<in> FV (snd (B ! i)) \<longrightarrow> xa \<noteq> x - Suc 0) \<and> (xa \<in> FV (snd (B ! i)) \<longrightarrow> xa = fst (B ! i) \<or> fst (B ! i) < xa) \<or> xb + d - Suc 0 \<noteq> xa + d"
                  then have "\<not> c \<le> xb - Suc 0"
                    using a3 a2 by (metis (no_types) Nat.add_diff_assoc2 Suc_leI add_gr_0 less_imp_add_positive)
                  then show ?thesis
                    using a2 a1 by linarith
                qed             
            next
              fix xb
              show "c < fst (B ! i) \<Longrightarrow> nat (int (fst (B ! i)) + int d) < xb + d \<Longrightarrow> xb \<in> FV (snd (B ! i)) \<Longrightarrow>
                    c \<le> xb \<Longrightarrow> \<forall>xa\<ge>c. (\<forall>x>fst (B ! i). x \<in> FV (snd (B ! i)) \<longrightarrow> xa \<noteq> x - Suc 0) \<and>
                    (xa \<in> FV (snd (B ! i)) \<longrightarrow> xa = fst (B ! i) \<or> fst (B ! i) < xa) \<or> xb + d - Suc 0 \<noteq> xa + d \<Longrightarrow>
                    c \<le> xb + d - Suc 0 \<Longrightarrow> False"       
                proof (simp add: s_nat)
                  assume a1: "c < fst (B ! i)"
                  assume a2: "fst (B ! i) < xb"
                  assume a3: "xb \<in> FV (snd (B ! i))"
                  assume a4: "\<forall>xa\<ge>c. (\<forall>x>fst (B ! i). x \<in> FV (snd (B ! i)) \<longrightarrow> xa \<noteq> x - Suc 0) \<and> (xa \<in> FV (snd (B ! i)) \<longrightarrow> xa = fst (B ! i) \<or> fst (B ! i) < xa) \<or> xb + d - Suc 0 \<noteq> xa + d"
                  have f5: "Suc c \<le> xb"
                    using a2 a1 by auto
                  have "\<forall>n na. \<exists>nb. \<not> na < n \<or> Suc (na + nb) = n"
                    using less_imp_Suc_add by blast
                  then show ?thesis
                    using f5 a4 a3 a2 by (metis (no_types) Nat.add_diff_assoc2 One_nat_def Suc_leI Suc_le_mono add_gr_0 diff_Suc_1 less_imp_add_positive)
                qed          
                
            qed (linarith, fastforce, linarith+)
          have 2:"\<And>x. c < fst (B ! i) \<Longrightarrow> (\<exists>xa. ((\<exists>x. x \<in> FV (snd (B ! i)) \<and> x \<noteq> fst (B ! i) \<and> fst (B ! i) < x \<and> xa = x - Suc 0) \<or>
                  xa \<in> FV (snd (B ! i)) \<and> xa \<noteq> fst (B ! i) \<and> \<not> fst (B ! i) < xa) \<and>
                 c \<le> xa \<and> x = xa + d) \<or> ((\<exists>xa. xa \<in> FV (snd (B ! i)) \<and> xa \<noteq> fst (B ! i) \<and> fst (B ! i) < xa \<and> x = xa - Suc 0) \<or>
                 x \<in> FV (snd (B ! i)) \<and> x \<noteq> fst (B ! i) \<and> \<not> fst (B ! i) < x) \<and>
                 \<not> c \<le> x \<Longrightarrow> (\<exists>xa. ((\<exists>x. x \<in> FV (snd (B ! i)) \<and> c \<le> x \<and> xa = x + d) \<or> xa \<in> FV (snd (B ! i)) \<and> \<not> c \<le> xa) \<and>
                 xa \<noteq> nat (int (fst (B ! i)) + int d) \<and> nat (int (fst (B ! i)) + int d) < xa \<and> x = xa - Suc 0) \<or>
                 ((\<exists>xa. xa \<in> FV (snd (B ! i)) \<and> c \<le> xa \<and> x = xa + d) \<or> x \<in> FV (snd (B ! i)) \<and> \<not> c \<le> x) \<and>
                 x \<noteq> nat (int (fst (B ! i)) + int d) \<and> \<not> nat (int (fst (B ! i)) + int d) < x"
            by (meson, simp_all add: s_nat, (metis Suc_pred add_gr_0 add_less_cancel_right le_SucI less_imp_add_positive)+)
          
          show ?thesis by (rule;rule) (simp_all add: AH 1 2)
        qed
        have B: "\<not> c < fst (B ! i) \<Longrightarrow>
                {y. \<exists>x. ((\<exists>xa. xa \<in> FV (snd (B ! i)) \<and> Suc c \<le> xa \<and> x = xa + d) \<or> x \<in> FV (snd (B ! i)) \<and> \<not> Suc c \<le> x) \<and>
                        x \<noteq> fst (B ! i) \<and> fst (B ! i) < x \<and> y = x - Suc 0} \<union>
                ({y. \<exists>x. x \<in> FV (snd (B ! i)) \<and> Suc c \<le> x \<and> y = x + d} \<union> FV (snd (B ! i)) \<inter> {x. \<not> Suc c \<le> x} -
                 {fst (B ! i)}) \<inter>
                {y. \<not> fst (B ! i) < y} =
                {y. \<exists>x. ((\<exists>xa. xa \<in> FV (snd (B ! i)) \<and> xa \<noteq> fst (B ! i) \<and> fst (B ! i) < xa \<and> x = xa - Suc 0) \<or>
                         x \<in> FV (snd (B ! i)) \<and> x \<noteq> fst (B ! i) \<and> \<not> fst (B ! i) < x) \<and>
                        c \<le> x \<and> y = x + d} \<union>
                ({y. \<exists>x. x \<in> FV (snd (B ! i)) \<and> x \<noteq> fst (B ! i) \<and> fst (B ! i) < x \<and> y = x - Suc 0} \<union>
                 (FV (snd (B ! i)) - {fst (B ! i)}) \<inter> {y. \<not> fst (B ! i) < y}) \<inter>
                {x. \<not> c \<le> x}"
          proof -
            assume BH:"\<not> c < fst (B ! i)"
            have 1: "\<And>x. \<not> c < fst (B ! i) \<Longrightarrow>(\<exists>xa. ((\<exists>x. x \<in> FV (snd (B ! i)) \<and> Suc c \<le> x \<and> xa = x + d) \<or>
                xa \<in> FV (snd (B ! i)) \<and> \<not> Suc c \<le> xa) \<and> xa \<noteq> fst (B ! i) \<and> fst (B ! i) < xa \<and> x = xa - Suc 0) \<or>
                ((\<exists>xa. xa \<in> FV (snd (B ! i)) \<and> Suc c \<le> xa \<and> x = xa + d) \<or> x \<in> FV (snd (B ! i)) \<and> \<not> Suc c \<le> x) \<and>
                x \<noteq> fst (B ! i) \<and> \<not> fst (B ! i) < x \<Longrightarrow>(\<exists>xa. ((\<exists>x. x \<in> FV (snd (B ! i)) \<and> x \<noteq> fst (B ! i) \<and> fst (B ! i) < x \<and> xa = x - Suc 0) \<or>
                xa \<in> FV (snd (B ! i)) \<and> xa \<noteq> fst (B ! i) \<and> \<not> fst (B ! i) < xa) \<and> c \<le> xa \<and> x = xa + d) \<or>
                ((\<exists>xa. xa \<in> FV (snd (B ! i)) \<and> xa \<noteq> fst (B ! i) \<and> fst (B ! i) < xa \<and> x = xa - Suc 0) \<or>
                x \<in> FV (snd (B ! i)) \<and> x \<noteq> fst (B ! i) \<and> \<not> fst (B ! i) < x) \<and> \<not> c \<le> x"
              proof (meson,simp_all)
                fix xb
                show "\<not> c < fst (B ! i) \<Longrightarrow> xb \<in> FV (snd (B ! i)) \<Longrightarrow> Suc c \<le> xb \<Longrightarrow>
                      \<forall>xa\<ge>c. (\<forall>x>fst (B ! i). x \<in> FV (snd (B ! i)) \<longrightarrow> xa \<noteq> x - Suc 0) \<and>
                      (xa \<in> FV (snd (B ! i)) \<longrightarrow> xa = fst (B ! i) \<or> fst (B ! i) < xa) \<or>
                      xb + d - Suc 0 \<noteq> xa + d \<Longrightarrow> \<forall>xa>fst (B ! i). xa \<in> FV (snd (B ! i)) \<longrightarrow> xb + d - Suc 0 \<noteq> xa - Suc 0 \<Longrightarrow>
                      xb + d - Suc 0 \<in> FV (snd (B ! i))"                 
                  proof -
                    assume a1: "Suc c \<le> xb"
                    assume a2: "\<not> c < fst (B ! i)"
                    assume a3: "xb \<in> FV (snd (B ! i))"
                    assume "\<forall>xa\<ge>c. (\<forall>x>fst (B ! i). x \<in> FV (snd (B ! i)) \<longrightarrow> xa \<noteq> x - Suc 0) \<and> (xa \<in> FV (snd (B ! i)) \<longrightarrow> xa = fst (B ! i) \<or> fst (B ! i) < xa) \<or> xb + d - Suc 0 \<noteq> xa + d"
                    then have "\<not> fst (B ! i) < xb"
                      using a3 a1 by (metis (no_types) Nat.add_diff_assoc2 One_nat_def Suc_leI diff_Suc_1 gr_Suc_conv zero_less_Suc)
                    then show ?thesis
                      using a2 a1 by linarith
                  qed
              next
                fix xb
                show "\<not> c < fst (B ! i) \<Longrightarrow> xb \<in> FV (snd (B ! i)) \<Longrightarrow> Suc c \<le> xb \<Longrightarrow>
                      \<forall>xa\<ge>c. (\<forall>x>fst (B ! i). x \<in> FV (snd (B ! i)) \<longrightarrow> xa \<noteq> x - Suc 0) \<and>
                        (xa \<in> FV (snd (B ! i)) \<longrightarrow> xa = fst (B ! i) \<or> fst (B ! i) < xa) \<or>
                       fst (B ! i) \<noteq> xa + d \<Longrightarrow> \<forall>xa>fst (B ! i). xa \<in> FV (snd (B ! i)) \<longrightarrow> fst (B ! i) \<noteq> xa - Suc 0 \<Longrightarrow>
                        xb + d - Suc 0 = fst (B ! i) \<Longrightarrow> False"
                  proof -
                    assume a1: "\<not> c < fst (B ! i)"
                    assume a2: "Suc c \<le> xb"
                    assume a3: "\<forall>xa\<ge>c. (\<forall>x>fst (B ! i). x \<in> FV (snd (B ! i)) \<longrightarrow> xa \<noteq> x - Suc 0) \<and> (xa \<in> FV (snd (B ! i)) \<longrightarrow> xa = fst (B ! i) \<or> fst (B ! i) < xa) \<or> fst (B ! i) \<noteq> xa + d"
                    assume a4: "xb + d - Suc 0 = fst (B ! i)"
                    assume a5: "xb \<in> FV (snd (B ! i))"
                    obtain nn :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
                      "\<forall>x0 x1. (\<exists>v2. x0 = Suc v2 \<and> x1 \<le> v2) = (x0 = Suc (nn x0 x1) \<and> x1 \<le> nn x0 x1)"
                      by moura
                    then have f6: "\<forall>n na. (\<not> Suc n \<le> na \<or> na = Suc (nn na n) \<and> n \<le> nn na n) \<and> (Suc n \<le> na \<or> (\<forall>nb. na \<noteq> Suc nb \<or> \<not> n \<le> nb))"
                      using gr_Suc_conv by fastforce
                    then have f7: "xb = Suc (nn xb c) \<and> c \<le> nn xb c"
                      using a2 by presburger
                    have f8: "\<forall>n. \<not> c \<le> n \<or> (\<forall>na. (\<not> fst (B ! i) < na \<or> na \<notin> FV (snd (B ! i))) \<or> n \<noteq> na - Suc 0) \<and> (n \<notin> FV (snd (B ! i)) \<or> n = fst (B ! i) \<or> fst (B ! i) < n) \<or> fst (B ! i) \<noteq> n + d"
                      using a3 by presburger
                    have f9: "fst (B ! i) = nn xb c + d"
                      using f7 a4 by (metis (no_types) Nat.add_diff_assoc2 One_nat_def Suc_leI diff_Suc_1 zero_less_Suc)
                    have f10: "Suc (nn xb c) \<in> FV (snd (B ! i))"
                      using f7 a5 by presburger
                    have "nn xb c = Suc (nn xb c) - Suc 0"
                      by presburger
                    then have "Suc (nn xb c) < fst (B ! i)"
                      using f10 f9 f8 f7 f6 a1 by (meson Suc_le_lessD linorder_neqE_nat)
                    then show ?thesis
                      using f7 a1 by linarith
                  qed
              next
                fix xb
                show "\<not> c < fst (B ! i) \<Longrightarrow> xb \<in> FV (snd (B ! i)) \<Longrightarrow> Suc c \<le> xb \<Longrightarrow>
                      \<forall>xa\<ge>c. (\<forall>x>fst (B ! i). x \<in> FV (snd (B ! i)) \<longrightarrow> xa \<noteq> x - Suc 0) \<and>
                      (xa \<in> FV (snd (B ! i)) \<longrightarrow> xa = fst (B ! i) \<or> fst (B ! i) < xa) \<or>
                      xb + d - Suc 0 \<noteq> xa + d \<Longrightarrow> \<forall>xa>fst (B ! i). xa \<in> FV (snd (B ! i)) \<longrightarrow> xb + d - Suc 0 \<noteq> xa - Suc 0 \<Longrightarrow>
                      fst (B ! i) < xb + d - Suc 0 \<Longrightarrow> False"
                 proof -
                  assume a1: "Suc c \<le> xb"
                  assume a2: "\<not> c < fst (B ! i)"
                  assume a3: "xb \<in> FV (snd (B ! i))"
                  assume "\<forall>xa\<ge>c. (\<forall>x>fst (B ! i). x \<in> FV (snd (B ! i)) \<longrightarrow> xa \<noteq> x - Suc 0) \<and> (xa \<in> FV (snd (B ! i)) \<longrightarrow> xa = fst (B ! i) \<or> fst (B ! i) < xa) \<or> xb + d - Suc 0 \<noteq> xa + d"
                  then have "\<not> fst (B ! i) < xb"
                    using a3 a1 by (metis (no_types) Nat.add_diff_assoc2 One_nat_def Suc_leI diff_Suc_1 gr_Suc_conv zero_less_Suc)
                  then show ?thesis
                    using a2 a1 by linarith
                qed
              next
                fix xb
                show "\<not> c < fst (B ! i) \<Longrightarrow> xb \<in> FV (snd (B ! i)) \<Longrightarrow> Suc c \<le> xb \<Longrightarrow>
                      \<forall>xa\<ge>c. (\<forall>x>fst (B ! i). x \<in> FV (snd (B ! i)) \<longrightarrow> xa \<noteq> x - Suc 0) \<and>
                      (xa \<in> FV (snd (B ! i)) \<longrightarrow> xa = fst (B ! i) \<or> fst (B ! i) < xa) \<or>
                      xb + d - Suc 0 \<noteq> xa + d \<Longrightarrow> c \<le> xb + d - Suc 0 \<Longrightarrow> False"
                  proof -
                    assume a1: "Suc c \<le> xb"
                    assume a2: "\<not> c < fst (B ! i)"
                    assume a3: "xb \<in> FV (snd (B ! i))"
                    assume "\<forall>xa\<ge>c. (\<forall>x>fst (B ! i). x \<in> FV (snd (B ! i)) \<longrightarrow> xa \<noteq> x - Suc 0) \<and> (xa \<in> FV (snd (B ! i)) \<longrightarrow> xa = fst (B ! i) \<or> fst (B ! i) < xa) \<or> xb + d - Suc 0 \<noteq> xa + d"
                    then have "\<not> fst (B ! i) < xb"
                      using a3 a1 by (metis (no_types) Nat.add_diff_assoc2 One_nat_def Suc_leI diff_Suc_1 gr_Suc_conv zero_less_Suc)
                    then show ?thesis
                      using a2 a1 by (metis (no_types) Suc_leD Suc_le_lessD less_le_trans linorder_neqE_nat)
                  qed                
              qed (force+)
            
            have 2:"\<And>x. \<not> c < fst (B ! i) \<Longrightarrow> (\<exists>xa. ((\<exists>x. x \<in> FV (snd (B ! i)) \<and> x \<noteq> fst (B ! i) \<and> fst (B ! i) < x \<and> xa = x - Suc 0) \<or>
                  xa \<in> FV (snd (B ! i)) \<and> xa \<noteq> fst (B ! i) \<and> \<not> fst (B ! i) < xa) \<and> c \<le> xa \<and> x = xa + d) \<or>
                  ((\<exists>xa. xa \<in> FV (snd (B ! i)) \<and> xa \<noteq> fst (B ! i) \<and> fst (B ! i) < xa \<and> x = xa - Suc 0) \<or>
                  x \<in> FV (snd (B ! i)) \<and> x \<noteq> fst (B ! i) \<and> \<not> fst (B ! i) < x) \<and> \<not> c \<le> x \<Longrightarrow>
                  (\<exists>xa. ((\<exists>x. x \<in> FV (snd (B ! i)) \<and> Suc c \<le> x \<and> xa = x + d) \<or> xa \<in> FV (snd (B ! i)) \<and> \<not> Suc c \<le> xa) \<and>
                  xa \<noteq> fst (B ! i) \<and> fst (B ! i) < xa \<and> x = xa - Suc 0) \<or> ((\<exists>xa. xa \<in> FV (snd (B ! i)) \<and> Suc c \<le> xa \<and> x = xa + d) \<or> x \<in> FV (snd (B ! i)) \<and> \<not> Suc c \<le> x) \<and>
                  x \<noteq> fst (B ! i) \<and> \<not> fst (B ! i) < x"
              proof (meson, simp_all)
                fix xb
                show "\<not> c < fst (B ! i) \<Longrightarrow> c \<le> xb - Suc 0 \<Longrightarrow> xb \<in> FV (snd (B ! i)) \<Longrightarrow> fst (B ! i) < xb \<Longrightarrow>
                      \<forall>xa>fst (B ! i). (\<forall>x\<ge>Suc c. x \<in> FV (snd (B ! i)) \<longrightarrow> xa \<noteq> x + d) \<and> (xa \<in> FV (snd (B ! i)) \<longrightarrow> Suc c \<le> xa) \<or>
                      xb + d - Suc 0 \<noteq> xa - Suc 0 \<Longrightarrow> \<forall>xa\<ge>Suc c. xa \<in> FV (snd (B ! i)) \<longrightarrow> xb + d - Suc 0 \<noteq> xa + d \<Longrightarrow>
                      xb + d - Suc 0 \<in> FV (snd (B ! i))"
                  by (metis (mono_tags, lifting) Suc_leI Suc_pred le_add1 le_imp_less_Suc less_le_trans less_nat_zero_code linorder_neqE_nat)
              next
                fix xb
                show "\<not> c < fst (B ! i) \<Longrightarrow> c \<le> xb - Suc 0 \<Longrightarrow> xb \<in> FV (snd (B ! i)) \<Longrightarrow> fst (B ! i) < xb \<Longrightarrow>
                      \<forall>xa>fst (B ! i). (\<forall>x\<ge>Suc c. x \<in> FV (snd (B ! i)) \<longrightarrow> xa \<noteq> x + d) \<and> (xa \<in> FV (snd (B ! i)) \<longrightarrow> Suc c \<le> xa) \<or>
                      xb + d - Suc 0 \<noteq> xa - Suc 0 \<Longrightarrow> \<forall>xa\<ge>Suc c. xa \<in> FV (snd (B ! i)) \<longrightarrow> xb + d - Suc 0
                      \<noteq> xa + d \<Longrightarrow> Suc c \<le> xb + d - Suc 0 \<Longrightarrow> False"
                  proof -
                    assume a1: "c \<le> xb - Suc 0"
                    assume a2: "fst (B ! i) < xb"
                    assume a3: "xb \<in> FV (snd (B ! i))"
                    assume "\<forall>xa>fst (B ! i). (\<forall>x\<ge>Suc c. x \<in> FV (snd (B ! i)) \<longrightarrow> xa \<noteq> x + d) \<and> (xa \<in> FV (snd (B ! i)) \<longrightarrow> Suc c \<le> xa) \<or> xb + d - Suc 0 \<noteq> xa - Suc 0"
                    then have "\<not> Suc c \<le> xb"
                      using a3 a2 by (metis add.commute trans_less_add2)
                    then show ?thesis
                      using a2 a1 by linarith
                  qed
              next
                fix xb
                show " \<not> c < fst (B ! i) \<Longrightarrow> c \<le> xb - Suc 0 \<Longrightarrow>xb \<in> FV (snd (B ! i)) \<Longrightarrow> fst (B ! i) < xb \<Longrightarrow>
                      \<forall>xa>fst (B ! i). (\<forall>x\<ge>Suc c. x \<in> FV (snd (B ! i)) \<longrightarrow> xa \<noteq> x + d) \<and> (xa \<in> FV (snd (B ! i)) \<longrightarrow> Suc c \<le> xa) \<or>
                      xb + d - Suc 0 \<noteq> xa - Suc 0 \<Longrightarrow> fst (B ! i) < xb + d - Suc 0 \<Longrightarrow> False"
                  by (metis Suc_leI Suc_pred add_gr_0 le_imp_less_Suc less_SucI less_imp_Suc_add zero_less_Suc)
              qed fastforce+

            show ?thesis by (rule;rule, simp_all add: BH 1 2)
          qed

        show "(if c < fst (B ! i)
              then (\<lambda>y. if nat (int (fst (B ! i)) + int d) < y then y - 1 else y) `
             (FV (shift_L (int d) c (snd (B ! i))) - {nat (int (fst (B ! i)) + int d)})
             else (\<lambda>y. if fst (B ! i) < y then y - 1 else y) `
             (FV (shift_L (int d) (Suc c) (snd (B ! i))) - {fst (B ! i)})) =
             (\<lambda>x. if c \<le> x then x + d else x) ` (\<lambda>y. if fst (B ! i) < y then y - 1 else y) `
             (FV (snd (B ! i)) - {fst (B ! i)})"
          by (cases "c <fst (B!i)")
             (simp_all add: Ha hyps(1) shift_simp Bex_def image_def A B)
      qed
  

    from H1 show ?case
      by (simp only: shift_L.simps FV.simps if_True if_False set_foldl_union set_map B2 B1 A
              image_Un image_UN Un_empty_right,subst hyps(1)[of c], fast) 
qed (force)+

lemma Binder_FV_subst:
  fixes n x::nat and t t1 t2::lterm
  assumes "\<And>n t. FV (subst_L n t t1) = (if n \<in> FV t1 then FV t1 - {n} \<union> FV t else FV t1)"
          "\<And>n t. FV (subst_L n t t2) = (if n \<in> FV t2 then FV t2 - {n} \<union> FV t else FV t2)"
  shows "(\<lambda>y. if x < y then y - 1 else y) ` (FV (subst_L (if x \<le> n then Suc n else n) (shift_L 1 x t) t2) - {x}) \<union>
              FV (subst_L n t t1) = (if n \<in> (\<lambda>y. if x < y then y - 1 else y) ` (FV t2 - {x}) \<union> FV t1
                then (\<lambda>y. if x < y then y - 1 else y) ` (FV t2 - {x}) \<union> FV t1 - {n} \<union> FV t
                else (\<lambda>y. if x < y then y - 1 else y) ` (FV t2 - {x}) \<union> FV t1)"
proof -
  let ?S3="\<lambda>n t x t1 t2. (\<lambda>y. if x < y then y - 1 else y) ` (FV (subst_L (if x \<le> n then Suc n else n) (shift_L 1 x t) t2) - {x}) \<union>
              FV (subst_L n t t1)" and
        ?S4 ="\<lambda>n t x t1 t2. (if n \<in> (\<lambda>y. if x < y then y - 1 else y) ` (FV t2 - {x}) \<union> FV t1
                then (\<lambda>y. if x < y then y - 1 else y) ` (FV t2 - {x}) \<union> FV t1 - {n} \<union> FV t
                else (\<lambda>y. if x < y then y - 1 else y) ` (FV t2 - {x}) \<union> FV t1)"
        
    have C1:"\<And>n t x t1 t2. (\<And>n1 ta. FV (subst_L n1 ta t1) = (if n1 \<in> FV t1 then FV t1 - {n1} \<union> FV ta else 
                          FV t1)) \<Longrightarrow>
                         (\<And>n1 ta. FV (subst_L n1 ta t2) = (if n1 \<in> FV t2 then FV t2 - {n1} \<union> FV ta else 
                          FV t2)) \<Longrightarrow> x \<le> n \<Longrightarrow> ?S3 n t x t1 t2 \<subseteq> ?S4 n t x t1 t2"
      proof -
        fix n::nat and t x t1 t2
        assume le_n:"x\<le>n" and
                FV_s:"\<And>n1 ta. FV (subst_L n1 ta t1) = (if n1 \<in> FV t1 then FV t1 - {n1} \<union> FV ta else FV t1)"
                     "\<And>n1 ta. FV (subst_L n1 ta t2) = (if n1 \<in> FV t2 then FV t2 - {n1} \<union> FV ta else FV t2)"
        note FV_s= FV_s[of n t] FV_s[of "Suc n" "shift_L 1 x t"]
        have "Suc n \<in> FV t2 \<Longrightarrow> n\<in> FV t1 \<Longrightarrow> ?S3 n t x t1 t2 \<subseteq> ?S4 n t x t1 t2" 
          using le_n
          by (simp add: image_def FV_s Int_Collect Bex_def FV_shift[of 1, unfolded int_1]) force

        moreover have "Suc n \<in> FV t2 \<Longrightarrow> n \<notin> FV t1 \<Longrightarrow> ?S3 n t x t1 t2 \<subseteq> ?S4 n t x t1 t2" 
          using le_n
          by (simp add: image_def FV_s Int_Collect Bex_def FV_shift[of 1, unfolded int_1])
             (meson, (force+)[3], ((metis One_nat_def diff_Suc_1 le_imp_less_Suc)+)[2],
                 (force+)[2], (metis One_nat_def diff_Suc_1 le_imp_less_Suc)+)
          
        moreover have "Suc n \<notin> FV t2 \<Longrightarrow>?S3 n t x t1 t2 \<subseteq> ?S4 n t x t1 t2"
          using le_n
          by (simp add: image_def FV_s Int_Collect Bex_def FV_shift[of 1, unfolded int_1])
             (cases "n\<in> FV t1", auto)

        ultimately show "?S3 n t x t1 t2 \<subseteq> ?S4 n t x t1 t2" by linarith
      qed
    have C2:"\<And>n t x t1 t2. (\<And>n1 ta. FV (subst_L n1 ta t1) = (if n1 \<in> FV t1 then FV t1 - {n1} \<union> FV ta else 
                          FV t1)) \<Longrightarrow>
                         (\<And>n1 ta. FV (subst_L n1 ta t2) = (if n1 \<in> FV t2 then FV t2 - {n1} \<union> FV ta else 
                          FV t2)) \<Longrightarrow> x \<le> n \<Longrightarrow> ?S4 n t x t1 t2 \<subseteq> ?S3 n t x t1 t2" 
      proof -
        fix n::nat and t x t1 t2
        assume le_n:"x\<le>n" and
                FV_s:"\<And>n1 ta. FV (subst_L n1 ta t1) = (if n1 \<in> FV t1 then FV t1 - {n1} \<union> FV ta else FV t1)"
                     "\<And>n1 ta. FV (subst_L n1 ta t2) = (if n1 \<in> FV t2 then FV t2 - {n1} \<union> FV ta else FV t2)"
        note FV_s= FV_s[of n t] FV_s[of "Suc n" "shift_L 1 x t"]
        have "Suc n \<in> FV t2 \<Longrightarrow> n\<in> FV t1 \<Longrightarrow> ?S4 n t x t1 t2 \<subseteq> ?S3 n t x t1 t2" 
          using le_n
          by (simp add: image_def FV_s Int_Collect Bex_def FV_shift[of 1, unfolded int_1]) force

        moreover have "Suc n \<in> FV t2 \<Longrightarrow> n \<notin> FV t1 \<Longrightarrow> ?S4 n t x t1 t2 \<subseteq> ?S3 n t x t1 t2" 
          using le_n
          proof (simp add: image_def FV_s Int_Collect Bex_def FV_shift[of 1, unfolded int_1], meson)
            fix x1
            show "Suc (x1 - Suc 0) \<in> FV t2 \<Longrightarrow> x1 - Suc 0 \<notin> FV t1 \<Longrightarrow> x \<le> x1 - Suc 0 \<Longrightarrow> x1 \<in> FV t2 \<Longrightarrow>
                  x1 \<noteq> x \<Longrightarrow> x < x1 \<Longrightarrow> n = x1 - Suc 0 \<Longrightarrow> {y. \<exists>xa. xa \<in> FV t2 \<and> xa \<noteq> x \<and> x < xa \<and> 
                  y = xa - Suc 0} \<union> (FV t2 - {x}) \<inter> {y. \<not> x < y} \<union> FV t1 - {x1 - Suc 0}
                  \<subseteq> {y. \<exists>xb. (xb \<in> FV t2 \<and> xb \<noteq> Suc (x1 - Suc 0) \<or> (\<exists>xa. xa \<in> FV t \<and> x \<le> xa \<and> xb = Suc xa) \<or> xb \<in> FV t \<and> \<not> x \<le> xb) \<and>
                  xb \<noteq> x \<and> x < xb \<and> y = xb - Suc 0} \<union> (FV t2 - {Suc (x1 - Suc 0)} \<union> ({y. \<exists>xa. xa \<in> FV t \<and>
                  x \<le> xa \<and> y = Suc xa} \<union> FV t \<inter> {y. \<not> x \<le> y}) - {x}) \<inter> {y. \<not> x < y} \<union> FV t1"
              by auto
          next
            fix x1
            show "Suc (x1 - Suc 0) \<in> FV t2 \<Longrightarrow> x1 - Suc 0 \<notin> FV t1 \<Longrightarrow>  x \<le> x1 - Suc 0 \<Longrightarrow> x1 \<in> FV t2 \<Longrightarrow>
                  x1 \<noteq> x \<Longrightarrow> x < x1 \<Longrightarrow> n = x1 - Suc 0 \<Longrightarrow> FV t \<subseteq> {y. \<exists>xb. (xb \<in> FV t2 \<and>
                  xb \<noteq> Suc (x1 - Suc 0) \<or> (\<exists>xa. xa \<in> FV t \<and> x \<le> xa \<and> xb = Suc xa) \<or> xb \<in> FV t \<and> \<not> x \<le> xb) \<and>
                  xb \<noteq> x \<and> x < xb \<and> y = xb - Suc 0} \<union> (FV t2 - {Suc (x1 - Suc 0)} \<union> ({y. \<exists>xa. xa \<in> FV t \<and>
                  x \<le> xa \<and> y = Suc xa} \<union> FV t \<inter> {y. \<not> x \<le> y}) - {x}) \<inter> {y. \<not> x < y} \<union> FV t1"
              by (rule, simp, metis One_nat_def diff_Suc_1 le_eq_less_or_eq le_imp_less_Suc nat_neq_iff)
          qed fastforce+

        moreover have "Suc n \<notin> FV t2 \<Longrightarrow>?S4 n t x t1 t2 \<subseteq> ?S3 n t x t1 t2"
          using le_n
          by (simp add: image_def FV_s Int_Collect Bex_def FV_shift[of 1, unfolded int_1])
             (cases "n\<in> FV t1", auto)

        ultimately show "?S4 n t x t1 t2 \<subseteq> ?S3 n t x t1 t2" by linarith
      qed

    have C3:"\<And>n t x t1 t2. (\<And>n1 ta. FV (subst_L n1 ta t1) = (if n1 \<in> FV t1 then FV t1 - {n1} \<union> FV ta else 
                          FV t1)) \<Longrightarrow>
                         (\<And>n1 ta. FV (subst_L n1 ta t2) = (if n1 \<in> FV t2 then FV t2 - {n1} \<union> FV ta else 
                          FV t2)) \<Longrightarrow>\<not>x\<le>n \<Longrightarrow>?S3 n t x t1 t2 \<subseteq> ?S4 n t x t1 t2"
      proof -
        fix n::nat and t x t1 t2
        assume gr_n:"\<not>x\<le>n" and
                FV_s:"\<And>n1 ta. FV (subst_L n1 ta t1) = (if n1 \<in> FV t1 then FV t1 - {n1} \<union> FV ta else FV t1)"
                     "\<And>n1 ta. FV (subst_L n1 ta t2) = (if n1 \<in> FV t2 then FV t2 - {n1} \<union> FV ta else FV t2)"
        note FV_s= FV_s[of n t] FV_s[of "Suc n" "shift_L 1 x t"] FV_s[of n "shift_L 1 x t"]
        from gr_n have "n\<in>FV t2 \<Longrightarrow> n\<in>FV t1 \<Longrightarrow> ?S3 n t x t1 t2 \<subseteq> ?S4 n t x t1 t2"
          by (simp add: image_def FV_s Int_Collect Bex_def FV_shift[of 1, unfolded int_1]) force
        moreover from gr_n have "n\<notin>FV t2 \<Longrightarrow> ?S3 n t x t1 t2 \<subseteq> ?S4 n t x t1 t2"
          by (force simp add: image_def FV_s Int_Collect Bex_def FV_shift[of 1, unfolded int_1])

        moreover from gr_n have "n\<in>FV t2 \<Longrightarrow> n\<notin>FV t1 \<Longrightarrow> ?S3 n t x t1 t2 \<subseteq> ?S4 n t x t1 t2"
          by (simp add: image_def FV_s Int_Collect Bex_def FV_shift[of 1, unfolded int_1]) force
         
        ultimately  show "?S3 n t x t1 t2 \<subseteq> ?S4 n t x t1 t2"
          by (cases "n\<in>FV t2", cases "n\<in>FV t1", blast+)
      qed    
    have "\<And>n t x t1 t2. (\<And>n1 ta. FV (subst_L n1 ta t1) = (if n1 \<in> FV t1 then FV t1 - {n1} \<union> FV ta else 
                          FV t1)) \<Longrightarrow>
                         (\<And>n1 ta. FV (subst_L n1 ta t2) = (if n1 \<in> FV t2 then FV t2 - {n1} \<union> FV ta else 
                          FV t2)) \<Longrightarrow>\<not>x\<le>n \<Longrightarrow>?S4 n t x t1 t2 \<subseteq> ?S3 n t x t1 t2"
      proof -
        fix n::nat and t x t1 t2
        assume gr_n:"\<not>x\<le>n" and
                FV_s:"\<And>n1 ta. FV (subst_L n1 ta t1) = (if n1 \<in> FV t1 then FV t1 - {n1} \<union> FV ta else FV t1)"
                     "\<And>n1 ta. FV (subst_L n1 ta t2) = (if n1 \<in> FV t2 then FV t2 - {n1} \<union> FV ta else FV t2)"
        note FV_s= FV_s[of n t] FV_s[of "Suc n" "shift_L 1 x t"] FV_s[of n "shift_L 1 x t"]
        from gr_n have "n\<in>FV t2 \<Longrightarrow> n\<in>FV t1 \<Longrightarrow> ?S4 n t x t1 t2 \<subseteq> ?S3 n t x t1 t2"
          by (simp add: image_def FV_s Int_Collect Bex_def FV_shift[of 1, unfolded int_1]) force
        moreover from gr_n have "n\<notin>FV t2 \<Longrightarrow> ?S4 n t x t1 t2 \<subseteq> ?S3 n t x t1 t2"
          by (simp add: image_def FV_s Int_Collect Bex_def FV_shift[of 1, unfolded int_1]) fastforce

        moreover from gr_n have "n\<in>FV t2 \<Longrightarrow> n\<notin>FV t1 \<Longrightarrow> ?S4 n t x t1 t2 \<subseteq> ?S3 n t x t1 t2"
          proof (simp add: image_def FV_s Int_Collect Bex_def FV_shift[of 1, unfolded int_1], meson)
            show "n \<in> FV t2 \<Longrightarrow> n \<notin> FV t1 \<Longrightarrow> \<not> x \<le> n \<Longrightarrow> FV t \<subseteq> {y. \<exists>xa. (xa \<in> FV t2 \<and> xa \<noteq> n \<or> 
                  (\<exists>xb. xb \<in> FV t \<and> x \<le> xb \<and> xa = Suc xb) \<or> xa \<in> FV t \<and> \<not> x \<le> xa) \<and> xa \<noteq> x \<and> x < xa \<and>
                  y = xa - Suc 0} \<union> (FV t2 - {n} \<union> ({y. \<exists>xa. xa \<in> FV t \<and> x \<le> xa \<and> y = Suc xa} \<union> FV t \<inter>
                  {y. \<not> x \<le> y}) - {x}) \<inter> {y. \<not> x < y} \<union> FV t1"
              by (rule, simp, metis One_nat_def diff_Suc_1 le_eq_less_or_eq le_imp_less_Suc nat_neq_iff)
          qed fastforce      
         
        ultimately  show "?S4 n t x t1 t2 \<subseteq> ?S3 n t x t1 t2"
          by (cases "n\<in>FV t2", cases "n\<in>FV t1", blast+)
      qed
    note H = this C1 C2 C3
   
    from H[OF assms,of x n] show "?S3 n t x t1 t2 = ?S4 n t x t1 t2" by blast
qed


lemma FV_subst:
  " FV (subst_L n t u) = (if n \<in> FV u then (FV u - {n}) \<union> FV t else FV u)"
proof (induction u arbitrary: n t rule: lterm.induct)
  case (LAbs T u)
    thus ?case 
    by (auto simp: gr0_conv_Suc image_iff FV_shift[of 1, unfolded int_1],
        (metis DiffI One_nat_def UnCI diff_Suc_1 empty_iff imageI insert_iff nat.distinct(1))+)
next
  case (Record L LT)
    note hyps=this(1) this(1)[of _ _ "shift_L 1 0 _"]
    have "(\<exists>x\<in>set LT. n \<in> FV x) \<longrightarrow> (\<Union>x\<in>set LT. FV (subst_L n t x)) = UNION (set LT) FV - {n} \<union> FV t"
      proof (rule)
        assume "\<exists>x\<in>set LT. n \<in> FV x"
        then obtain x where H:"x\<in>set LT" "n\<in>FV x" by blast

        note H1= hyps[OF H(1), of n, simplified H(2) if_True]
        
        have "(\<Union>x\<in>set LT. FV (subst_L n t x)) \<subseteq> UNION (set LT) FV - {n} \<union> FV t"
          proof (rule,simp)
            fix y
            assume "\<exists>xa\<in>set LT. y \<in> FV (subst_L n t xa)"
            then obtain x1 where A:"x1\<in>set LT" "y \<in> FV (subst_L n t x1)" by blast
            note H2=A(2)[unfolded hyps[OF A(1), of n]]
            show "(\<exists>xa\<in>set LT. y \<in> FV xa) \<and> y \<noteq> n \<or> y \<in> FV t"
                using H2 A(1)
                by (cases "n\<in>FV x1") force+
          qed
        moreover have "UNION (set LT) FV - {n} \<union> FV t \<subseteq> (\<Union>x\<in>set LT. FV (subst_L n t x))"
          using hyps[of _ n] H1 H
          by auto
        
        ultimately show "(\<Union>x\<in>set LT. FV (subst_L n t x)) = UNION (set LT) FV - {n} \<union> FV t"
          by blast
      qed
    moreover have "(\<forall>x\<in>set LT. n \<notin> FV x) \<longrightarrow> (\<Union>x\<in>set LT. FV (subst_L n t x)) = UNION (set LT) FV"
      using hyps
      by simp
    ultimately show ?case by simp      
next
  case (Tuple LT)
    note hyps= this(1) this(1)[of _ _ "shift_L 1 0 _"]
    have "(\<exists>x\<in>set LT. n \<in> FV x) \<longrightarrow> (\<Union>x\<in>set LT. FV (subst_L n t x)) = UNION (set LT) FV - {n} \<union> FV t"
      proof (rule)
        assume "\<exists>x\<in>set LT. n \<in> FV x"
        then obtain x where H:"x\<in>set LT" "n\<in>FV x" by blast

        note H1= hyps[OF H(1), of n, simplified H(2) if_True]
        
        have "(\<Union>x\<in>set LT. FV (subst_L n t x)) \<subseteq> UNION (set LT) FV - {n} \<union> FV t"
          proof (rule,simp)
            fix y
            assume "\<exists>xa\<in>set LT. y \<in> FV (subst_L n t xa)"
            then obtain x1 where A:"x1\<in>set LT" "y \<in> FV (subst_L n t x1)" by blast
            note H2=A(2)[unfolded hyps[OF A(1), of n]]
            show "(\<exists>xa\<in>set LT. y \<in> FV xa) \<and> y \<noteq> n \<or> y \<in> FV t"
                using H2 A(1)
                by (cases "n\<in>FV x1") force+
          qed
        moreover have "UNION (set LT) FV - {n} \<union> FV t \<subseteq> (\<Union>x\<in>set LT. FV (subst_L n t x))"
          using hyps[of _ n] H1 H
          by auto
        
        ultimately show "(\<Union>x\<in>set LT. FV (subst_L n t x)) = UNION (set LT) FV - {n} \<union> FV t"
          by blast
      qed
    moreover have "(\<forall>x\<in>set LT. n \<notin> FV x) \<longrightarrow> (\<Union>x\<in>set LT. FV (subst_L n t x)) = UNION (set LT) FV"
      using hyps
      by simp
    ultimately show ?case by simp
next
  case (LetBinder x t1 t2)
    note hyps=this         
      
    show ?case using Binder_FV_subst[OF hyps] by force
     
next
  case (CaseSum t1 x t2 y t3)
    note hyps=this
    
    have   A:" (\<lambda>y. if x < y then y - 1 else y) ` (FV (subst_L (if x \<le> n then Suc n else n) (shift_L 1 x t) t2) - {x}) \<union>
            (\<lambda>z. if y < z then z - 1 else z) ` (FV (subst_L (if y \<le> n then Suc n else n) (shift_L 1 y t) t3) - {y}) \<union>
            FV (subst_L n t t1) = (\<lambda>y. if x < y then y - 1 else y) ` (FV (subst_L (if x \<le> n then Suc n else n) (shift_L 1 x t) t2) - {x}) \<union>
            FV (subst_L n t t1) \<union> (\<lambda>ya. if y < ya then ya - 1 else ya) ` (FV (subst_L (if y \<le> n then Suc n else n) (shift_L 1 y t) t3) - {y}) \<union>
            FV (subst_L n t t1)"
      by blast
        
    have B: "(if n \<in> (\<lambda>y. if x < y then y - 1 else y) ` (FV t2 - {x}) \<union>
             (\<lambda>z. if y < z then z - 1 else z) ` (FV t3 - {y}) \<union> FV t1
             then (\<lambda>y. if x < y then y - 1 else y) ` (FV t2 - {x}) \<union>
             (\<lambda>z. if y < z then z - 1 else z) ` (FV t3 - {y}) \<union> FV t1 - {n} \<union> FV t
             else (\<lambda>y. if x < y then y - 1 else y) ` (FV t2 - {x}) \<union>
             (\<lambda>z. if y < z then z - 1 else z) ` (FV t3 - {y}) \<union> FV t1) =
             (if n \<in> (\<lambda>y. if x < y then y - 1 else y) ` (FV t2 - {x}) \<union> FV t1
             then (\<lambda>y. if x < y then y - 1 else y) ` (FV t2 - {x}) \<union> FV t1 - {n} \<union> FV t
             else (\<lambda>y. if x < y then y - 1 else y) ` (FV t2 - {x}) \<union> FV t1) \<union>
             (if n \<in> (\<lambda>ya. if y < ya then ya - 1 else ya) ` (FV t3 - {y}) \<union> FV t1
             then (\<lambda>ya. if y < ya then ya - 1 else ya) ` (FV t3 - {y}) \<union> FV t1 - {n} \<union> FV t
             else (\<lambda>ya. if y < ya then ya - 1 else ya) ` (FV t3 - {y}) \<union> FV t1)"
       by (cases "n \<in> (\<lambda>y. if x < y then y - 1 else y) ` (FV t2 - {x}) \<union>
             (\<lambda>z. if y < z then z - 1 else z) ` (FV t3 - {y}) \<union> FV t1")
          (simp_all, blast+)
       
    show ?case
      using Binder_FV_subst[OF hyps(1,2), of x n t]
            Binder_FV_subst[OF hyps(1,3), of y n t]
      by (simp only: subst_L.simps FV.simps A B) blast
next
  case (CaseVar t1 L B)
    note hyps=this
        let ?fv= "\<lambda>p. (\<lambda>y. if fst p < y then y - 1 else y) ` (FV (snd p) - {fst p})"
        and ?f="\<lambda>p. (fst p, subst_L (if fst p \<le> n then Suc n else n) (shift_L 1 (fst p) t) (snd p))"
        and ?S = "\<lambda>i. (\<lambda>y. if fst (B ! i) < y then y - 1 else y) `
                  (FV (subst_L (if fst (B ! i) \<le> n then Suc n else n) (shift_L 1 (fst (B ! i)) t) (snd (B ! i))) -
                   {fst (B ! i)})"

    from hyps have shift_simp:"\<And>i n t. i<length B \<Longrightarrow> FV (subst_L n t (snd (B!i))) = 
              (if n \<in> FV (snd (B!i)) then FV (snd (B!i)) - {n} \<union> FV t else FV (snd (B!i)))"
      using in_set_conv_nth snds.intros
      by metis
    
    have B2:"(\<Union>l\<in>(\<lambda>p. (\<lambda>y. if fst p < y then y - 1 else y) ` (FV (snd p) - {fst p})) ` set B. l) = 
           (\<Union>i<length B. (\<lambda>p. (\<lambda>y. if fst p < y then y - 1 else y) ` (FV (snd p) - {fst p})) (B!i))"
      by (simp only: in_set_conv_nth[of _ B] image_def[of _ "set B", unfolded Bex_def]
                     Collect_ex_eq) blast
    have B1:"(\<Union>l\<in>?fv ` ?f ` set B. l)= (\<Union>i<length B. (?fv \<circ>?f) (B!i))"
      by (simp only: in_set_conv_nth[of _ B] image_def[of "?fv \<circ> ?f" "set B", unfolded Bex_def]
                        image_comp[of ?fv ?f] Collect_ex_eq) blast

    have A:"FV (subst_L n t t1) \<union> ... = (\<Union>i<length B. ?S i) \<union>  FV (subst_L n t t1)"
      by (simp only: Un_commute Fun.comp_apply fst_conv) fastforce
    
    have C1:"\<And>x xa. n \<in> FV t1 \<Longrightarrow> fst (B ! xa) \<le> n \<Longrightarrow> (Suc n \<in> FV (snd (B ! xa)) \<longrightarrow> xa < length B \<and>
             ((\<exists>xb>fst (B ! xa). (xb \<in> FV (snd (B ! xa)) \<and> xb \<noteq> Suc n \<or> (\<exists>x\<ge>fst (B ! xa). x \<in> FV t \<and> xb = Suc x)) \<and>
                  x = xb - Suc 0) \<or>
              (x \<in> FV (snd (B ! xa)) \<and> x \<noteq> Suc n \<or> (\<exists>xb\<ge>fst (B ! xa). xb \<in> FV t \<and> x = Suc xb) \<or> x \<in> FV t \<and> \<not> fst (B ! xa) \<le> x) \<and>
              x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> (Suc n \<in> FV (snd (B ! xa)) \<or>xa < length B \<and>
             ((\<exists>xb>fst (B ! xa). xb \<in> FV (snd (B ! xa)) \<and> x = xb - Suc 0) \<or>
              x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<Longrightarrow>
            (x \<in> FV t1 \<and> x \<noteq> n \<or> (\<exists>xa<length B.
                 (\<exists>xb. xb \<in> FV (snd (B ! xa)) \<and> xb \<noteq> fst (B ! xa) \<and> fst (B ! xa) < xb \<and> x = xb - Suc 0) \<or>
                 x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x) \<and> x \<noteq> n \<or> x \<in> FV t) \<and> ((\<exists>x<length B.
                 (\<exists>xa. xa \<in> FV (snd (B ! x)) \<and> xa \<noteq> fst (B ! x) \<and> fst (B ! x) < xa \<and> n = xa - Suc 0) \<or>
                 n \<in> FV (snd (B ! x)) \<and> n \<noteq> fst (B ! x) \<and> \<not> fst (B ! x) < n) \<longrightarrow>
             x \<in> FV t1 \<and> x \<noteq> n \<or>
             (\<exists>xa<length B. (\<exists>xb. xb \<in> FV (snd (B ! xa)) \<and> xb \<noteq> fst (B ! xa) \<and> fst (B ! xa) < xb \<and> x = xb - Suc 0) \<or>
                 x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x) \<and> x \<noteq> n \<or> x \<in> FV t)"
         
        proof -

          fix x :: nat and xa :: nat
          assume a1: "fst (B ! xa) \<le> n"
          assume a2: "(Suc n \<in> FV (snd (B ! xa)) \<longrightarrow> xa < length B \<and> ((\<exists>xb>fst (B ! xa). (xb \<in> FV (snd (B ! xa)) \<and> xb \<noteq> Suc n \<or> (\<exists>x\<ge>fst (B ! xa). x \<in> FV t \<and> xb = Suc x)) \<and> x = xb - Suc 0) \<or> (x \<in> FV (snd (B ! xa)) \<and> x \<noteq> Suc n \<or> (\<exists>xb\<ge>fst (B ! xa). xb \<in> FV t \<and> x = Suc xb) \<or> x \<in> FV t \<and> \<not> fst (B ! xa) \<le> x) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> (Suc n \<in> FV (snd (B ! xa)) \<or> xa < length B \<and> ((\<exists>xb>fst (B ! xa). xb \<in> FV (snd (B ! xa)) \<and> x = xb - Suc 0) \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x))"
          have f3: "\<forall>n. \<not> (n::nat) < n"
            by force
          obtain nn :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
            "\<forall>x0 x1. (\<exists>v2. x0 = Suc (x1 + v2)) = (x0 = Suc (x1 + nn x0 x1))"
            by moura
          then have f4: "\<forall>n na. \<not> n < na \<or> na = Suc (n + nn na n)"
            using less_imp_Suc_add by presburger
          have f5: "\<forall>n. \<not> 0 < n \<or> Suc (n - Suc 0) = n"
            by presburger
          have f6: "fst (B ! xa) = n \<or> fst (B ! xa) < n"
            using a1 by (meson leD linorder_neqE_nat)
          have "(Suc n \<in> FV (snd (B ! xa)) \<longrightarrow> xa < length B \<and> ((\<exists>v0>fst (B ! xa). (v0 \<in> FV (snd (B ! xa)) \<and> v0 \<noteq> Suc n \<or> (\<exists>v1\<ge>fst (B ! xa). v1 \<in> FV t \<and> v0 = Suc v1)) \<and> x = v0 - Suc 0) \<or> (x \<in> FV (snd (B ! xa)) \<and> x \<noteq> Suc n \<or> (\<exists>v0\<ge>fst (B ! xa). v0 \<in> FV t \<and> x = Suc v0) \<or> x \<in> FV t \<and> \<not> fst (B ! xa) \<le> x) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) = (Suc n \<notin> FV (snd (B ! xa)) \<or> xa < length B \<and> ((\<exists>v0>fst (B ! xa). (v0 \<in> FV (snd (B ! xa)) \<and> v0 \<noteq> Suc n \<or> (\<exists>v1\<ge>fst (B ! xa). v1 \<in> FV t \<and> v0 = Suc v1)) \<and> x = v0 - Suc 0) \<or> (x \<in> FV (snd (B ! xa)) \<and> x \<noteq> Suc n \<or> (\<exists>v0\<ge>fst (B ! xa). v0 \<in> FV t \<and> x = Suc v0) \<or> x \<in> FV t \<and> \<not> fst (B ! xa) \<le> x) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x))"
            by fastforce
          then have f7: "(Suc n \<notin> FV (snd (B ! xa)) \<or> xa < length B \<and> ((\<exists>n>fst (B ! xa). (n \<in> FV (snd (B ! xa)) \<and> n \<noteq> Suc n \<or> (\<exists>na\<ge>fst (B ! xa). na \<in> FV t \<and> n = Suc na)) \<and> x = n - Suc 0) \<or> (x \<in> FV (snd (B ! xa)) \<and> x \<noteq> Suc n \<or> (\<exists>n\<ge>fst (B ! xa). n \<in> FV t \<and> x = Suc n) \<or> x \<in> FV t \<and> \<not> fst (B ! xa) \<le> x) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> (Suc n \<in> FV (snd (B ! xa)) \<or> xa < length B \<and> ((\<exists>n>fst (B ! xa). n \<in> FV (snd (B ! xa)) \<and> x = n - Suc 0) \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x))"
            using a2 by auto
          obtain nnb :: nat where
            f9: "(\<exists>v0>fst (B ! xa). (v0 \<in> FV (snd (B ! xa)) \<and> v0 \<noteq> Suc n \<or> (\<exists>v1\<ge>fst (B ! xa). v1 \<in> FV t \<and> v0 = Suc v1)) \<and> x = v0 - Suc 0) = (fst (B ! xa) < nnb \<and> (nnb \<in> FV (snd (B ! xa)) \<and> nnb \<noteq> Suc n \<or> (\<exists>v1\<ge>fst (B ! xa). v1 \<in> FV t \<and> nnb = Suc v1)) \<and> x = nnb - Suc 0)"
            by moura
          obtain nna :: nat where
            f8: "(\<exists>v1\<ge>fst (B ! xa). v1 \<in> FV t \<and> nnb = Suc v1) = (fst (B ! xa) \<le> nna \<and> nna \<in> FV t \<and> nnb = Suc nna)"
            by moura
          obtain nnc :: nat where
            "(\<exists>v0\<ge>fst (B ! xa). v0 \<in> FV t \<and> x = Suc v0) = (fst (B ! xa) \<le> nnc \<and> nnc \<in> FV t \<and> x = Suc nnc)"
            by moura
          then have f10: "Suc n \<notin> FV (snd (B ! xa)) \<or> xa < length B \<and> (fst (B ! xa) < nnb \<and> (nnb \<in> FV (snd (B ! xa)) \<and> nnb \<noteq> Suc n \<or> fst (B ! xa) \<le> nna \<and> nna \<in> FV t \<and> nnb = Suc nna) \<and> x = nnb - Suc 0 \<or> (x \<in> FV (snd (B ! xa)) \<and> x \<noteq> Suc n \<or> fst (B ! xa) \<le> nnc \<and> nnc \<in> FV t \<and> x = Suc nnc \<or> x \<in> FV t \<and> \<not> fst (B ! xa) \<le> x) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)"
            using f9 f8 f7 a2 by auto
          obtain nnd :: nat where
            f11: "Suc n \<in> FV (snd (B ! xa)) \<or> xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)"
            using a2 by moura
          have f12: "x = nnd - Suc 0 \<and> nnd = Suc (fst (B ! xa) + nn nnd (fst (B ! xa))) \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = n \<longrightarrow> xa < length B \<and> (fst (B ! xa) < nnb \<and> (nnb \<in> FV (snd (B ! xa)) \<and> nnb \<noteq> Suc n \<or> fst (B ! xa) \<le> nna \<and> nna \<in> FV t \<and> nnb = Suc nna) \<and> x = nnb - Suc 0 \<or> (x \<in> FV (snd (B ! xa)) \<and> x \<noteq> Suc n \<or> fst (B ! xa) \<le> nnc \<and> nnc \<in> FV t \<and> x = Suc nnc \<or> x \<in> FV t \<and> \<not> fst (B ! xa) \<le> x) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)"
            using f10 by force
          then have f13: "((x \<notin> FV (snd (B ! xa)) \<or> x = Suc n) \<and> (\<not> fst (B ! xa) \<le> nnc \<or> nnc \<notin> FV t \<or> x \<noteq> Suc nnc) \<and> (x \<notin> FV t \<or> fst (B ! xa) \<le> x) \<or> x = fst (B ! xa) \<or> fst (B ! xa) < x) \<and> x = nnd - Suc 0 \<and> nnd = Suc (fst (B ! xa) + nn nnd (fst (B ! xa))) \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = n \<and> \<not> fst (B ! xa) < x \<longrightarrow> fst (B ! xa) \<le> nna \<and> nna \<in> FV t \<and> nnb = Suc nna"
            using f5 f4 by (metis (no_types) zero_less_Suc)
          have f14: "((x \<notin> FV (snd (B ! xa)) \<or> x = Suc n) \<and> (\<not> fst (B ! xa) \<le> nnc \<or> nnc \<notin> FV t \<or> x \<noteq> Suc nnc) \<and> (x \<notin> FV t \<or> fst (B ! xa) \<le> x) \<or> x = fst (B ! xa) \<or> fst (B ! xa) < x) \<and> x = nnd - Suc 0 \<and> nnd = Suc (fst (B ! xa) + nn nnd (fst (B ! xa))) \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = n \<and> \<not> fst (B ! xa) < x \<longrightarrow> nna = n"
            using f12 f6 f5 f4 by (metis (no_types) diff_Suc_1 zero_less_Suc)
          { assume "(\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n"
            moreover
            { assume "(\<not> fst (B ! xa) < x \<and> (x \<in> FV (snd (B ! xa)) \<and> x \<noteq> Suc n \<or> fst (B ! xa) \<le> nnc \<and> nnc \<in> FV t \<and> x = Suc nnc \<or> x \<in> FV t \<and> \<not> fst (B ! xa) \<le> x) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x) \<and> (x \<notin> FV (snd (B ! xa)) \<or> x = Suc n)"
              then have "x \<in> FV t"
                using le_imp_less_Suc by blast }
            moreover
            { assume "((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n) \<and> ((x \<notin> FV (snd (B ! xa)) \<or> x = Suc n) \<and> (\<not> fst (B ! xa) \<le> nnc \<or> nnc \<notin> FV t \<or> x \<noteq> Suc nnc) \<and> (x \<notin> FV t \<or> fst (B ! xa) \<le> x) \<or> x = fst (B ! xa) \<or> fst (B ! xa) < x)"
              moreover
              { assume "((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n) \<and> fst (B ! xa) < nnb \<and> (nnb \<in> FV (snd (B ! xa)) \<and> nnb \<noteq> Suc n \<or> fst (B ! xa) \<le> nna \<and> nna \<in> FV t \<and> nnb = Suc nna) \<and> x = nnb - Suc 0"
                then have "((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n) \<and> (\<exists>n. n \<in> FV (snd (B ! xa)) \<and> n \<noteq> fst (B ! xa) \<and> fst (B ! xa) < n \<and> x = n - Suc 0) \<or> (\<forall>n. n \<notin> FV (snd (B ! xa)) \<or> n = fst (B ! xa) \<or> \<not> fst (B ! xa) < n \<or> x \<noteq> n - Suc 0) \<and> fst (B ! xa) < nnb \<and> (nnb \<in> FV (snd (B ! xa)) \<and> nnb \<noteq> Suc n \<or> fst (B ! xa) \<le> nna \<and> nna \<in> FV t \<and> nnb = Suc nna) \<and> x = nnb - Suc 0"
                  by meson
                moreover
                { assume "(\<forall>n. n \<notin> FV (snd (B ! xa)) \<or> n = fst (B ! xa) \<or> \<not> fst (B ! xa) < n \<or> x \<noteq> n - Suc 0) \<and> fst (B ! xa) < nnb \<and> (nnb \<in> FV (snd (B ! xa)) \<and> nnb \<noteq> Suc n \<or> fst (B ! xa) \<le> nna \<and> nna \<in> FV t \<and> nnb = Suc nna) \<and> x = nnb - Suc 0"
                  then have "x \<in> FV t"
                    using f5 f3 by (metis diff_Suc_1 zero_less_Suc) }
                moreover
                { assume "((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n) \<and> (\<exists>n. n \<in> FV (snd (B ! xa)) \<and> n \<noteq> fst (B ! xa) \<and> fst (B ! xa) < n \<and> x = n - Suc 0)"
                  moreover
                  { assume "((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n) \<and> x = n"
                    moreover
                    { assume "((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n) \<and> (\<not> xa < length B \<or> (\<not> fst (B ! xa) < nnb \<or> (nnb \<notin> FV (snd (B ! xa)) \<or> nnb = Suc n) \<and> (\<not> fst (B ! xa) \<le> nna \<or> nna \<notin> FV t \<or> nnb \<noteq> Suc nna) \<or> x \<noteq> nnb - Suc 0) \<and> ((x \<notin> FV (snd (B ! xa)) \<or> x = Suc n) \<and> (\<not> fst (B ! xa) \<le> nnc \<or> nnc \<notin> FV t \<or> x \<noteq> Suc nnc) \<and> (x \<notin> FV t \<or> fst (B ! xa) \<le> x) \<or> x = fst (B ! xa) \<or> fst (B ! xa) < x))"
                      then have "((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n) \<and> Suc n \<notin> FV (snd (B ! xa))"
                        using f10 by force }
                    ultimately have "((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n) \<and> Suc n \<notin> FV (snd (B ! xa)) \<or> x \<in> FV t"
                      using f6 f5 f4 by (metis diff_Suc_1 zero_less_Suc) }
                  ultimately have "((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n) \<and> (\<not> xa < length B \<or> (\<not> fst (B ! xa) < nnb \<or> (nnb \<notin> FV (snd (B ! xa)) \<or> nnb = Suc n) \<and> (\<not> fst (B ! xa) \<le> nna \<or> nna \<notin> FV t \<or> nnb \<noteq> Suc nna) \<or> x \<noteq> nnb - Suc 0) \<and> ((x \<notin> FV (snd (B ! xa)) \<or> x = Suc n) \<and> (\<not> fst (B ! xa) \<le> nnc \<or> nnc \<notin> FV t \<or> x \<noteq> Suc nnc) \<and> (x \<notin> FV t \<or> fst (B ! xa) \<le> x) \<or> x = fst (B ! xa) \<or> fst (B ! xa) < x)) \<or> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n) \<and> Suc n \<notin> FV (snd (B ! xa)) \<or> x \<in> FV t"
                    by (metis (no_types)) }
                ultimately have "((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n) \<and> (\<not> xa < length B \<or> (\<not> fst (B ! xa) < nnb \<or> (nnb \<notin> FV (snd (B ! xa)) \<or> nnb = Suc n) \<and> (\<not> fst (B ! xa) \<le> nna \<or> nna \<notin> FV t \<or> nnb \<noteq> Suc nna) \<or> x \<noteq> nnb - Suc 0) \<and> ((x \<notin> FV (snd (B ! xa)) \<or> x = Suc n) \<and> (\<not> fst (B ! xa) \<le> nnc \<or> nnc \<notin> FV t \<or> x \<noteq> Suc nnc) \<and> (x \<notin> FV t \<or> fst (B ! xa) \<le> x) \<or> x = fst (B ! xa) \<or> fst (B ! xa) < x)) \<or> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n) \<and> Suc n \<notin> FV (snd (B ! xa)) \<or> x \<in> FV t"
                  by fastforce }
              ultimately have "((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n) \<and> (\<not> xa < length B \<or> (\<not> fst (B ! xa) < nnb \<or> (nnb \<notin> FV (snd (B ! xa)) \<or> nnb = Suc n) \<and> (\<not> fst (B ! xa) \<le> nna \<or> nna \<notin> FV t \<or> nnb \<noteq> Suc nna) \<or> x \<noteq> nnb - Suc 0) \<and> ((x \<notin> FV (snd (B ! xa)) \<or> x = Suc n) \<and> (\<not> fst (B ! xa) \<le> nnc \<or> nnc \<notin> FV t \<or> x \<noteq> Suc nnc) \<and> (x \<notin> FV t \<or> fst (B ! xa) \<le> x) \<or> x = fst (B ! xa) \<or> fst (B ! xa) < x)) \<or> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n) \<and> Suc n \<notin> FV (snd (B ! xa)) \<or> x \<in> FV t"
                by satx }
            moreover
            { assume "(xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)"
              moreover
              { assume "((xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)) \<and> nna \<in> FV t"
                then have "((xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)) \<and> nna \<noteq> x \<or> x \<in> FV t"
                  by fastforce
                moreover
                { assume "((xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)) \<and> nna \<noteq> x"
                  then have "((xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)) \<and> nna \<noteq> n \<or> ((xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)) \<and> (\<forall>n. n \<notin> FV (snd (B ! xa)) \<or> n = fst (B ! xa) \<or> \<not> fst (B ! xa) < n \<or> x \<noteq> n - Suc 0)"
                    by meson
                  moreover
                  { assume "((xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)) \<and> nna \<noteq> n"
                    moreover
                    { assume "((xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)) \<and> Suc nna \<noteq> Suc (nnb - Suc 0)"
                      then have "((xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)) \<and> (\<not> fst (B ! xa) \<le> nna \<or> nna \<notin> FV t \<or> nnb \<noteq> Suc nna) \<or> ((xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)) \<and> \<not> 0 < nnb"
                        using f5 by (metis (no_types)) }
                    ultimately have "((xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)) \<and> (\<not> fst (B ! xa) \<le> nna \<or> nna \<notin> FV t \<or> nnb \<noteq> Suc nna) \<or> ((xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)) \<and> nnb - Suc 0 \<noteq> n \<or> ((xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)) \<and> \<not> 0 < nnb"
                      by auto }
                  ultimately have "((xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)) \<and> (\<not> fst (B ! xa) \<le> nna \<or> nna \<notin> FV t \<or> nnb \<noteq> Suc nna) \<or> ((xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)) \<and> nnb - Suc 0 \<noteq> n \<or> ((xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)) \<and> \<not> 0 < nnb \<or> ((xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)) \<and> (\<forall>n. n \<notin> FV (snd (B ! xa)) \<or> n = fst (B ! xa) \<or> \<not> fst (B ! xa) < n \<or> x \<noteq> n - Suc 0)"
                    by fastforce }
                ultimately have "((xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)) \<and> (\<not> fst (B ! xa) \<le> nna \<or> nna \<notin> FV t \<or> nnb \<noteq> Suc nna) \<or> ((xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)) \<and> nnb - Suc 0 \<noteq> n \<or> ((xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)) \<and> \<not> 0 < nnb \<or> ((xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)) \<and> (\<forall>n. n \<notin> FV (snd (B ! xa)) \<or> n = fst (B ! xa) \<or> \<not> fst (B ! xa) < n \<or> x \<noteq> n - Suc 0) \<or> x \<in> FV t"
                  by fastforce }
              moreover
              { assume "((xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)) \<and> (\<not> fst (B ! xa) \<le> nna \<or> nna \<notin> FV t \<or> nnb \<noteq> Suc nna)"
                moreover
                { assume "((xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)) \<and> nnb \<noteq> Suc n"
                  moreover
                  { assume "((xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)) \<and> Suc (nnb - Suc 0) \<noteq> nnb"
                    then have "((xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)) \<and> \<not> 0 < nnb"
                      using f5 by meson }
                  ultimately have "((xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)) \<and> nnb - Suc 0 \<noteq> n \<or> ((xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)) \<and> \<not> 0 < nnb"
                    by simp }
                ultimately have "((xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)) \<and> nnb - Suc 0 \<noteq> n \<or> ((xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)) \<and> \<not> 0 < nnb \<or> ((xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)) \<and> (\<not> fst (B ! xa) < nnb \<or> (nnb \<notin> FV (snd (B ! xa)) \<or> nnb = Suc n) \<and> (\<not> fst (B ! xa) \<le> nna \<or> nna \<notin> FV t \<or> nnb \<noteq> Suc nna) \<or> x \<noteq> nnb - Suc 0)"
                  by satx }
              moreover
              { assume "((xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)) \<and> \<not> 0 < nnb"
                then have "((xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)) \<and> (\<not> fst (B ! xa) < nnb \<or> (nnb \<notin> FV (snd (B ! xa)) \<or> nnb = Suc n) \<and> (\<not> fst (B ! xa) \<le> nna \<or> nna \<notin> FV t \<or> nnb \<noteq> Suc nna) \<or> x \<noteq> nnb - Suc 0)"
                  by fastforce }
              moreover
              { assume "((xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)) \<and> nnb - Suc 0 \<noteq> n"
                then have "((xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)) \<and> (\<not> fst (B ! xa) < nnb \<or> (nnb \<notin> FV (snd (B ! xa)) \<or> nnb = Suc n) \<and> (\<not> fst (B ! xa) \<le> nna \<or> nna \<notin> FV t \<or> nnb \<noteq> Suc nna) \<or> x \<noteq> nnb - Suc 0) \<or> ((xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)) \<and> (\<forall>n. n \<notin> FV (snd (B ! xa)) \<or> n = fst (B ! xa) \<or> \<not> fst (B ! xa) < n \<or> x \<noteq> n - Suc 0)"
                  by auto }
              moreover
              { assume "((xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)) \<and> (\<not> fst (B ! xa) < nnb \<or> (nnb \<notin> FV (snd (B ! xa)) \<or> nnb = Suc n) \<and> (\<not> fst (B ! xa) \<le> nna \<or> nna \<notin> FV t \<or> nnb \<noteq> Suc nna) \<or> x \<noteq> nnb - Suc 0)"
                moreover
                { assume "((xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)) \<and> (\<not> xa < length B \<or> (\<not> fst (B ! xa) < nnb \<or> (nnb \<notin> FV (snd (B ! xa)) \<or> nnb = Suc n) \<and> (\<not> fst (B ! xa) \<le> nna \<or> nna \<notin> FV t \<or> nnb \<noteq> Suc nna) \<or> x \<noteq> nnb - Suc 0) \<and> ((x \<notin> FV (snd (B ! xa)) \<or> x = Suc n) \<and> (\<not> fst (B ! xa) \<le> nnc \<or> nnc \<notin> FV t \<or> x \<noteq> Suc nnc) \<and> (x \<notin> FV t \<or> fst (B ! xa) \<le> x) \<or> x = fst (B ! xa) \<or> fst (B ! xa) < x))"
                  then have "((xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)) \<and> Suc n \<notin> FV (snd (B ! xa))"
                    using f10 by satx
                  moreover
                  { assume "((xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)) \<and> nnd \<noteq> Suc n"
                    then have "((xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)) \<and> fst (B ! xa) + nn nnd (fst (B ! xa)) \<noteq> n \<or> ((xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)) \<and> nnd \<noteq> Suc (fst (B ! xa) + nn nnd (fst (B ! xa)))"
                      by presburger
                    moreover
                    { assume "((xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)) \<and> nnd \<noteq> Suc (fst (B ! xa) + nn nnd (fst (B ! xa)))"
                      then have "(fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n) \<and> xa < length B \<and> \<not> fst (B ! xa) < x"
                        using f4 by metis }
                    moreover
                    { assume "((xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)) \<and> fst (B ! xa) + nn nnd (fst (B ! xa)) \<noteq> n"
                      moreover
                      { assume "((xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)) \<and> fst (B ! xa) + nn nnd (fst (B ! xa)) \<noteq> x"
                        moreover
                        { assume "((xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)) \<and> fst (B ! xa) + nn nnd (fst (B ! xa)) \<noteq> nnd - Suc 0"
                          then have "((xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)) \<and> Suc (nnd - Suc 0) \<noteq> nnd \<or> ((xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)) \<and> nnd \<noteq> Suc (fst (B ! xa) + nn nnd (fst (B ! xa)))"
                            by auto
                          then have "(fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n) \<and> xa < length B \<and> \<not> fst (B ! xa) < x"
                            using f5 f4 by (metis (no_types) zero_less_Suc) }
                        ultimately have "(fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n) \<and> xa < length B \<and> \<not> fst (B ! xa) < x"
                          by fastforce }
                      ultimately have "((xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)) \<and> (\<forall>n. n \<notin> FV (snd (B ! xa)) \<or> n = fst (B ! xa) \<or> \<not> fst (B ! xa) < n \<or> x \<noteq> n - Suc 0) \<or> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n) \<and> xa < length B \<and> \<not> fst (B ! xa) < x"
                        by meson }
                    ultimately have "((xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)) \<and> (\<forall>n. n \<notin> FV (snd (B ! xa)) \<or> n = fst (B ! xa) \<or> \<not> fst (B ! xa) < n \<or> x \<noteq> n - Suc 0) \<or> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n) \<and> xa < length B \<and> \<not> fst (B ! xa) < x"
                      by fastforce }
                  ultimately have "((xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)) \<and> (\<forall>n. n \<notin> FV (snd (B ! xa)) \<or> n = fst (B ! xa) \<or> \<not> fst (B ! xa) < n \<or> x \<noteq> n - Suc 0) \<or> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n) \<and> xa < length B \<and> \<not> fst (B ! xa) < x"
                    by auto }
                ultimately have "((xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)) \<and> (\<forall>n. n \<notin> FV (snd (B ! xa)) \<or> n = fst (B ! xa) \<or> \<not> fst (B ! xa) < n \<or> x \<noteq> n - Suc 0) \<or> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n) \<and> xa < length B \<and> \<not> fst (B ! xa) < x"
                  by satx }
              ultimately have "((xa < length B \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n)) \<and> (\<forall>n. n \<notin> FV (snd (B ! xa)) \<or> n = fst (B ! xa) \<or> \<not> fst (B ! xa) < n \<or> x \<noteq> n - Suc 0) \<or> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n) \<and> xa < length B \<and> \<not> fst (B ! xa) < x \<or> x \<in> FV t"
                by satx
              moreover
              { assume "(fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0 \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x) \<and> ((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n) \<and> xa < length B \<and> \<not> fst (B ! xa) < x"
                moreover
                { assume "(((\<forall>n. \<not> n < length B \<or> (\<forall>na. na \<notin> FV (snd (B ! n)) \<or> na = fst (B ! n) \<or> \<not> fst (B ! n) < na \<or> x \<noteq> na - Suc 0) \<and> (x \<notin> FV (snd (B ! n)) \<or> x = fst (B ! n) \<or> fst (B ! n) < x)) \<or> x = n) \<and> (fst (B ! xa) < nnd \<and> nnd \<in> FV (snd (B ! xa)) \<and> x = nnd - Suc 0) \<and> xa < length B \<and> \<not> fst (B ! xa) < x) \<and> (x \<in> FV (snd (B ! xa)) \<and> x \<noteq> Suc n \<or> fst (B ! xa) \<le> nnc \<and> nnc \<in> FV t \<and> x = Suc nnc \<or> x \<in> FV t \<and> \<not> fst (B ! xa) \<le> x) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x"
                  then have "x \<in> FV t"
                    using a1 by (metis (no_types) leD le_imp_less_Suc linorder_neqE_nat) }
                ultimately have "x \<in> FV t"
                  using f14 f13 f6 f4 f3 by (metis (no_types)) }
              ultimately have "x \<in> FV t"
                by blast }
            ultimately have "(x \<in> FV t1 \<and> x \<noteq> n \<or> (\<exists>n<length B. (\<exists>na. na \<in> FV (snd (B ! n)) \<and> na \<noteq> fst (B ! n) \<and> fst (B ! n) < na \<and> x = na - Suc 0) \<or> x \<in> FV (snd (B ! n)) \<and> x \<noteq> fst (B ! n) \<and> \<not> fst (B ! n) < x) \<and> x \<noteq> n \<or> x \<in> FV t) \<and> (\<not> nna < length B \<or> (nnd \<notin> FV (snd (B ! nna)) \<or> nnd = fst (B ! nna) \<or> \<not> fst (B ! nna) < nnd \<or> n \<noteq> nnd - Suc 0) \<and> (n \<notin> FV (snd (B ! nna)) \<or> n = fst (B ! nna) \<or> fst (B ! nna) < n) \<or> x \<in> FV t1 \<and> x \<noteq> n \<or> (\<exists>n<length B. (\<exists>na. na \<in> FV (snd (B ! n)) \<and> na \<noteq> fst (B ! n) \<and> fst (B ! n) < na \<and> x = na - Suc 0) \<or> x \<in> FV (snd (B ! n)) \<and> x \<noteq> fst (B ! n) \<and> \<not> fst (B ! n) < x) \<and> x \<noteq> n \<or> x \<in> FV t)"
              using f11 f10 by satx }
          then have "(x \<in> FV t1 \<and> x \<noteq> n \<or> (\<exists>n<length B. (\<exists>na. na \<in> FV (snd (B ! n)) \<and> na \<noteq> fst (B ! n) \<and> fst (B ! n) < na \<and> x = na - Suc 0) \<or> x \<in> FV (snd (B ! n)) \<and> x \<noteq> fst (B ! n) \<and> \<not> fst (B ! n) < x) \<and> x \<noteq> n \<or> x \<in> FV t) \<and> (\<not> nna < length B \<or> (nnd \<notin> FV (snd (B ! nna)) \<or> nnd = fst (B ! nna) \<or> \<not> fst (B ! nna) < nnd \<or> n \<noteq> nnd - Suc 0) \<and> (n \<notin> FV (snd (B ! nna)) \<or> n = fst (B ! nna) \<or> fst (B ! nna) < n) \<or> x \<in> FV t1 \<and> x \<noteq> n \<or> (\<exists>n<length B. (\<exists>na. na \<in> FV (snd (B ! n)) \<and> na \<noteq> fst (B ! n) \<and> fst (B ! n) < na \<and> x = na - Suc 0) \<or> x \<in> FV (snd (B ! n)) \<and> x \<noteq> fst (B ! n) \<and> \<not> fst (B ! n) < x) \<and> x \<noteq> n \<or> x \<in> FV t)"
            by blast
          then show "n \<in> FV t1 \<Longrightarrow> fst (B ! xa) \<le> n \<Longrightarrow> (Suc n \<in> FV (snd (B ! xa)) \<longrightarrow> xa < length B \<and>
             ((\<exists>xb>fst (B ! xa). (xb \<in> FV (snd (B ! xa)) \<and> xb \<noteq> Suc n \<or> (\<exists>x\<ge>fst (B ! xa). x \<in> FV t \<and> xb = Suc x)) \<and>
                  x = xb - Suc 0) \<or> (x \<in> FV (snd (B ! xa)) \<and> x \<noteq> Suc n \<or> (\<exists>xb\<ge>fst (B ! xa). xb \<in> FV t \<and> x = Suc xb) \<or> x \<in> FV t \<and> \<not> fst (B ! xa) \<le> x) \<and>
              x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> (Suc n \<in> FV (snd (B ! xa)) \<or>xa < length B \<and>
             ((\<exists>xb>fst (B ! xa). xb \<in> FV (snd (B ! xa)) \<and> x = xb - Suc 0) \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<Longrightarrow>
            (x \<in> FV t1 \<and> x \<noteq> n \<or> (\<exists>xa<length B. (\<exists>xb. xb \<in> FV (snd (B ! xa)) \<and> xb \<noteq> fst (B ! xa) \<and> fst (B ! xa) < xb \<and> x = xb - Suc 0) \<or>
                 x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x) \<and> x \<noteq> n \<or> x \<in> FV t) \<and> ((\<exists>x<length B.
                 (\<exists>xa. xa \<in> FV (snd (B ! x)) \<and> xa \<noteq> fst (B ! x) \<and> fst (B ! x) < xa \<and> n = xa - Suc 0) \<or>
                 n \<in> FV (snd (B ! x)) \<and> n \<noteq> fst (B ! x) \<and> \<not> fst (B ! x) < n) \<longrightarrow> x \<in> FV t1 \<and> x \<noteq> n \<or>
             (\<exists>xa<length B. (\<exists>xb. xb \<in> FV (snd (B ! xa)) \<and> xb \<noteq> fst (B ! xa) \<and> fst (B ! xa) < xb \<and> x = xb - Suc 0) \<or>
                 x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x) \<and> x \<noteq> n \<or> x \<in> FV t)"
            by force
        qed
            
    have C3: "\<And>x xa. n \<notin> FV t1 \<Longrightarrow>fst (B ! xa) \<le> n \<Longrightarrow> (Suc n \<in> FV (snd (B ! xa)) \<longrightarrow> xa < length B \<and>
             ((\<exists>xb>fst (B ! xa).(xb \<in> FV (snd (B ! xa)) \<and> xb \<noteq> Suc n \<or> (\<exists>x\<ge>fst (B ! xa). x \<in> FV t \<and> xb = Suc x)) \<and>
                  x = xb - Suc 0) \<or>
              (x \<in> FV (snd (B ! xa)) \<and> x \<noteq> Suc n \<or> (\<exists>xb\<ge>fst (B ! xa). xb \<in> FV t \<and> x = Suc xb) \<or> x \<in> FV t \<and> \<not> fst (B ! xa) \<le> x) \<and>
              x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> (Suc n \<in> FV (snd (B ! xa)) \<or>xa < length B \<and>
             ((\<exists>xb>fst (B ! xa). xb \<in> FV (snd (B ! xa)) \<and> x = xb - Suc 0) \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<Longrightarrow>
            ((\<exists>x<length B.(\<exists>xa. xa \<in> FV (snd (B ! x)) \<and> xa \<noteq> fst (B ! x) \<and> fst (B ! x) < xa \<and> n = xa - Suc 0) \<or>
                 n \<in> FV (snd (B ! x)) \<and> n \<noteq> fst (B ! x) \<and> \<not> fst (B ! x) < n) \<longrightarrow>x \<in> FV t1 \<and> x \<noteq> n \<or>
             (\<exists>xa<length B.(\<exists>xb. xb \<in> FV (snd (B ! xa)) \<and> xb \<noteq> fst (B ! xa) \<and> fst (B ! xa) < xb \<and> x = xb - Suc 0) \<or>
                 x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x) \<and>x \<noteq> n \<or> x \<in> FV t) \<and>
            ((\<forall>x<length B. (\<forall>xa>fst (B ! x). xa \<in> FV (snd (B ! x)) \<longrightarrow> n \<noteq> xa - Suc 0) \<and>
                 (n \<in> FV (snd (B ! x)) \<longrightarrow> n = fst (B ! x) \<or> fst (B ! x) < n)) \<longrightarrow>
             x \<in> FV t1 \<or> (\<exists>xa<length B. (\<exists>xb. xb \<in> FV (snd (B ! xa)) \<and> xb \<noteq> fst (B ! xa) \<and> fst (B ! xa) < xb \<and> x = xb - Suc 0) \<or>
                 x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x))"
      by (meson, simp_all, (blast+)[3])
          (((metis One_nat_def diff_Suc_1 le_imp_less_Suc)+)[2] , blast,
            ((metis Suc_pred less_nat_zero_code neq0_conv)+)[2], blast+)

    have C2: "\<And>x xa. n \<in> FV t1 \<Longrightarrow>\<not> fst (B ! xa) \<le> n \<Longrightarrow>(n \<in> FV (snd (B ! xa)) \<longrightarrow>xa < length B \<and>
             ((\<exists>xb>fst (B ! xa).(xb \<in> FV (snd (B ! xa)) \<and> xb \<noteq> n \<or> (\<exists>x\<ge>fst (B ! xa). x \<in> FV t \<and> xb = Suc x)) \<and>
                  x = xb - Suc 0) \<or>(x \<in> FV (snd (B ! xa)) \<and> x \<noteq> n \<or>(\<exists>xb\<ge>fst (B ! xa). xb \<in> FV t \<and> x = Suc xb) \<or> x \<in> FV t \<and> \<not> fst (B ! xa) \<le> x) \<and>
              x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> (n \<in> FV (snd (B ! xa)) \<or> xa < length B \<and>
             ((\<exists>xb>fst (B ! xa). xb \<in> FV (snd (B ! xa)) \<and> x = xb - Suc 0) \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<Longrightarrow>
            (x \<in> FV t1 \<and> x \<noteq> n \<or>(\<exists>xa<length B.
            (\<exists>xb. xb \<in> FV (snd (B ! xa)) \<and> xb \<noteq> fst (B ! xa) \<and> fst (B ! xa) < xb \<and> x = xb - Suc 0) \<or>
            x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x) \<and>x \<noteq> n \<or>x \<in> FV t) \<and>
            ((\<exists>x<length B. (\<exists>xa. xa \<in> FV (snd (B ! x)) \<and> xa \<noteq> fst (B ! x) \<and> fst (B ! x) < xa \<and> n = xa - Suc 0) \<or>
             n \<in> FV (snd (B ! x)) \<and> n \<noteq> fst (B ! x) \<and> \<not> fst (B ! x) < n) \<longrightarrow> x \<in> FV t1 \<and> x \<noteq> n \<or>
             (\<exists>xa<length B. (\<exists>xb. xb \<in> FV (snd (B ! xa)) \<and> xb \<noteq> fst (B ! xa) \<and> fst (B ! xa) < xb \<and> x = xb - Suc 0) \<or>
              x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x) \<and> x \<noteq> n \<or> x \<in> FV t)"
       by (meson, simp_all, blast+)
    have C4: "\<And>x xa. n \<notin> FV t1 \<Longrightarrow> \<not> fst (B ! xa) \<le> n \<Longrightarrow> (n \<in> FV (snd (B ! xa)) \<longrightarrow> xa < length B \<and>
             ((\<exists>xb>fst (B ! xa).(xb \<in> FV (snd (B ! xa)) \<and> xb \<noteq> n \<or> (\<exists>x\<ge>fst (B ! xa). x \<in> FV t \<and> xb = Suc x)) \<and>
                  x = xb - Suc 0) \<or>
              (x \<in> FV (snd (B ! xa)) \<and> x \<noteq> n \<or>
               (\<exists>xb\<ge>fst (B ! xa). xb \<in> FV t \<and> x = Suc xb) \<or> x \<in> FV t \<and> \<not> fst (B ! xa) \<le> x) \<and>
              x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and>
            (n \<in> FV (snd (B ! xa)) \<or>xa < length B \<and>
             ((\<exists>xb>fst (B ! xa). xb \<in> FV (snd (B ! xa)) \<and> x = xb - Suc 0) \<or>x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<Longrightarrow>
            ((\<exists>x<length B.(\<exists>xa. xa \<in> FV (snd (B ! x)) \<and> xa \<noteq> fst (B ! x) \<and> fst (B ! x) < xa \<and> n = xa - Suc 0) \<or>
                 n \<in> FV (snd (B ! x)) \<and> n \<noteq> fst (B ! x) \<and> \<not> fst (B ! x) < n) \<longrightarrow>x \<in> FV t1 \<and> x \<noteq> n \<or>
             (\<exists>xa<length B.(\<exists>xb. xb \<in> FV (snd (B ! xa)) \<and> xb \<noteq> fst (B ! xa) \<and> fst (B ! xa) < xb \<and> x = xb - Suc 0) \<or>
                 x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x) \<and>x \<noteq> n \<or> x \<in> FV t) \<and>
            ((\<forall>x<length B.(\<forall>xa>fst (B ! x). xa \<in> FV (snd (B ! x)) \<longrightarrow> n \<noteq> xa - Suc 0) \<and>
             (n \<in> FV (snd (B ! x)) \<longrightarrow> n = fst (B ! x) \<or> fst (B ! x) < n)) \<longrightarrow> x \<in> FV t1 \<or>
             (\<exists>xa<length B. (\<exists>xb. xb \<in> FV (snd (B ! xa)) \<and> xb \<noteq> fst (B ! xa) \<and> fst (B ! xa) < xb \<and> x = xb - Suc 0) \<or>
                 x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x))"
      by (meson, simp_all, (fastforce+)[5], blast+)
    have C6:"\<And>x. n \<in> FV t1 \<or>   (\<exists>x<length B. (\<exists>xa. xa \<in> FV (snd (B ! x)) \<and> xa \<noteq> fst (B ! x) \<and> fst (B ! x) < xa \<and> n = xa - Suc 0) \<or>
             n \<in> FV (snd (B ! x)) \<and> n \<noteq> fst (B ! x) \<and> \<not> fst (B ! x) < n) \<Longrightarrow>x \<in> FV t1 \<and> x \<noteq> n \<or>
         (\<exists>xa<length B.(\<exists>xb. xb \<in> FV (snd (B ! xa)) \<and> xb \<noteq> fst (B ! xa) \<and> fst (B ! xa) < xb \<and> x = xb - Suc 0) \<or>
             x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x) \<and> x \<noteq> n \<or> x \<in> FV t \<Longrightarrow>
         (n \<in> FV t1 \<longrightarrow> (\<exists>xa. (fst (B ! xa) \<le> n \<longrightarrow> (Suc n \<in> FV (snd (B ! xa)) \<longrightarrow> xa < length B \<and>
          ((\<exists>xb. (xb \<in> FV (snd (B ! xa)) \<and> xb \<noteq> Suc n \<or> (\<exists>x. x \<in> FV t \<and> fst (B ! xa) \<le> x \<and> xb = Suc x) \<or>
           xb \<in> FV t \<and> \<not> fst (B ! xa) \<le> xb) \<and> xb \<noteq> fst (B ! xa) \<and> fst (B ! xa) < xb \<and> x = xb - Suc 0) \<or>
            (x \<in> FV (snd (B ! xa)) \<and> x \<noteq> Suc n \<or> (\<exists>xb. xb \<in> FV t \<and> fst (B ! xa) \<le> xb \<and> x = Suc xb) \<or> x \<in> FV t \<and> \<not> fst (B ! xa) \<le> x) \<and>
             x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> (Suc n \<notin> FV (snd (B ! xa)) \<longrightarrow> xa < length B \<and>
             ((\<exists>xb. xb \<in> FV (snd (B ! xa)) \<and> xb \<noteq> fst (B ! xa) \<and> fst (B ! xa) < xb \<and> x = xb - Suc 0) \<or>
             x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x))) \<and>(\<not> fst (B ! xa) \<le> n \<longrightarrow>
             (n \<in> FV (snd (B ! xa)) \<longrightarrow> xa < length B \<and> ((\<exists>xb. (xb \<in> FV (snd (B ! xa)) \<and> xb \<noteq> n \<or>
             (\<exists>x. x \<in> FV t \<and> fst (B ! xa) \<le> x \<and> xb = Suc x) \<or> xb \<in> FV t \<and> \<not> fst (B ! xa) \<le> xb) \<and>
              xb \<noteq> fst (B ! xa) \<and> fst (B ! xa) < xb \<and> x = xb - Suc 0) \<or> (x \<in> FV (snd (B ! xa)) \<and> x \<noteq> n \<or>
             (\<exists>xb. xb \<in> FV t \<and> fst (B ! xa) \<le> xb \<and> x = Suc xb) \<or> x \<in> FV t \<and> \<not> fst (B ! xa) \<le> x) \<and>
              x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and>(n \<notin> FV (snd (B ! xa)) \<longrightarrow> xa < length B \<and>
             ((\<exists>xb. xb \<in> FV (snd (B ! xa)) \<and> xb \<noteq> fst (B ! xa) \<and> fst (B ! xa) < xb \<and> x = xb - Suc 0) \<or>
            x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)))) \<or> x \<in> FV t1 \<and> x \<noteq> n \<or> x \<in> FV t) \<and>
         (n \<notin> FV t1 \<longrightarrow> (\<exists>xa. (fst (B ! xa) \<le> n \<longrightarrow> (Suc n \<in> FV (snd (B ! xa)) \<longrightarrow> xa < length B \<and>
         ((\<exists>xb. (xb \<in> FV (snd (B ! xa)) \<and> xb \<noteq> Suc n \<or> (\<exists>x. x \<in> FV t \<and> fst (B ! xa) \<le> x \<and> xb = Suc x) \<or>
          xb \<in> FV t \<and> \<not> fst (B ! xa) \<le> xb) \<and> xb \<noteq> fst (B ! xa) \<and> fst (B ! xa) < xb \<and> x = xb - Suc 0) \<or>
         (x \<in> FV (snd (B ! xa)) \<and> x \<noteq> Suc n \<or>(\<exists>xb. xb \<in> FV t \<and> fst (B ! xa) \<le> xb \<and> x = Suc xb) \<or> x \<in> FV t \<and> \<not> fst (B ! xa) \<le> x) \<and>
          x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and>(Suc n \<notin> FV (snd (B ! xa)) \<longrightarrow> xa < length B \<and>
          ((\<exists>xb. xb \<in> FV (snd (B ! xa)) \<and> xb \<noteq> fst (B ! xa) \<and> fst (B ! xa) < xb \<and> x = xb - Suc 0) \<or>
          x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x))) \<and> (\<not> fst (B ! xa) \<le> n \<longrightarrow>
          (n \<in> FV (snd (B ! xa)) \<longrightarrow> xa < length B \<and> ((\<exists>xb. (xb \<in> FV (snd (B ! xa)) \<and> xb \<noteq> n \<or>
          (\<exists>x. x \<in> FV t \<and> fst (B ! xa) \<le> x \<and> xb = Suc x) \<or> xb \<in> FV t \<and> \<not> fst (B ! xa) \<le> xb) \<and>
           xb \<noteq> fst (B ! xa) \<and> fst (B ! xa) < xb \<and> x = xb - Suc 0) \<or> (x \<in> FV (snd (B ! xa)) \<and> x \<noteq> n \<or>
           (\<exists>xb. xb \<in> FV t \<and> fst (B ! xa) \<le> xb \<and> x = Suc xb) \<or> x \<in> FV t \<and> \<not> fst (B ! xa) \<le> x) \<and>
          x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> (n \<notin> FV (snd (B ! xa)) \<longrightarrow> xa < length B \<and>
          ((\<exists>xb. xb \<in> FV (snd (B ! xa)) \<and> xb \<noteq> fst (B ! xa) \<and> fst (B ! xa) < xb \<and> x = xb - Suc 0) \<or>
          x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)))) \<or> x \<in> FV t1)"
      apply meson
      apply simp_all
      apply (fastforce+)[2]
      apply ((metis less_or_eq_imp_le nat_neq_iff One_nat_def diff_Suc_1 
                    le_imp_less_Suc less_imp_Suc_add)+)[4]
      apply rule+
      apply force
      apply (metis One_nat_def diff_Suc_1 le_eq_less_or_eq le_imp_less_Suc not_less_eq_eq)
      
(*      apply ((metis One_nat_def diff_Suc_1 less_or_eq_imp_le nat_neq_iff le_SucI less_le
            diff_Suc_Suc  lessI  less_Suc_eq_le less_irrefl_nat minus_nat.diff_0)+)[5]*)
      sorry
    show ?case
      apply (simp only: FV.simps subst_L.simps if_True if_False set_foldl_union set_map 
                        B1 B2 A Un_empty_right Un_Diff)
      apply (rule;rule)
      apply (simp_all add: image_def hyps(1) shift_simp Bex_def FV_shift[of 1 "fst(B!_)" t, simplified] split: if_splits)
      apply (simp add: C1 C2 C3 C4 C6)+
      apply blast
      (* apply (smt One_nat_def diff_Suc_1 leD le_imp_less_Suc le_neq_implies_less less_imp_Suc_add less_or_eq_imp_le not_less_eq_eq)*)
      defer
      apply meson
      apply simp_all
      apply (metis One_nat_def diff_Suc_1 less_or_eq_imp_le nat_neq_iff)  
proof -
  fix x :: nat and xa :: nat
  assume a1: "xa < length B"
  assume a2: "x \<in> FV (snd (B ! xa))"
  assume a3: "x \<noteq> fst (B ! xa)"
  assume a4: "\<not> fst (B ! xa) < x"
  assume "\<forall>x<length B. (\<forall>xa>fst (B ! x). xa \<in> FV (snd (B ! x)) \<longrightarrow> n \<noteq> xa - Suc 0) \<and> (n \<in> FV (snd (B ! x)) \<longrightarrow> n = fst (B ! x) \<or> fst (B ! x) < n)"
  then have "x \<noteq> n"
    using a4 a3 a2 a1 by blast
  moreover
  { assume "\<exists>n1\<le>n. x \<noteq> n \<and> \<not> n < x"
    then have "x \<noteq> n \<and> \<not> n < x"
      using le_less_trans
      by meson
    then have "\<exists>xa. (fst (B ! xa) \<le> n \<longrightarrow> (Suc n \<in> FV (snd (B ! xa)) \<longrightarrow> xa < length B \<and> ((\<exists>nb. (nb \<in> FV (snd (B ! xa)) \<and> nb \<noteq> Suc n \<or> (\<exists>na. na \<in> FV t \<and> fst (B ! xa) \<le> na \<and> nb = Suc na) \<or> nb \<in> FV t \<and> \<not> fst (B ! xa) \<le> nb) \<and> nb \<noteq> fst (B ! xa) \<and> fst (B ! xa) < nb \<and> x = nb - Suc 0) \<or> (x \<in> FV (snd (B ! xa)) \<and> x \<noteq> Suc n \<or> (\<exists>na. na \<in> FV t \<and> fst (B ! xa) \<le> na \<and> x = Suc na) \<or> x \<in> FV t \<and> \<not> fst (B ! xa) \<le> x) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> (Suc n \<notin> FV (snd (B ! xa)) \<longrightarrow> xa <length B \<and> ((\<exists>na. na \<in> FV (snd (B ! xa)) \<and> na \<noteq> fst (B ! xa) \<and> fst (B ! xa) < na \<and> x = na - Suc 0) \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x))) \<and> (\<not> fst (B ! xa) \<le> n \<longrightarrow> (n \<in> FV (snd (B ! xa)) \<longrightarrow> xa <length B \<and> ((\<exists>nb. (nb \<in> FV (snd (B ! xa)) \<and> nb \<noteq> n \<or> (\<exists>na. na \<in> FV t \<and> fst (B ! xa) \<le> na \<and> nb = Suc na) \<or> nb \<in> FV t \<and> \<not> fst (B ! xa) \<le> nb) \<and> nb \<noteq> fst (B ! xa) \<and> fst (B ! xa) < nb \<and> x = nb - Suc 0) \<or> (x \<in> FV (snd (B ! xa)) \<and> x \<noteq> n \<or> (\<exists>na. na \<in> FV t \<and> fst (B ! xa) \<le> na \<and> x = Suc na) \<or> x \<in> FV t \<and> \<not> fst (B ! xa) \<le> x) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and> (n \<notin> FV (snd (B ! xa)) \<longrightarrow> xa <length B \<and> ((\<exists>na. na \<in> FV (snd (B ! xa)) \<and> na \<noteq> fst (B ! xa) \<and> fst (B ! xa) < na \<and> x = na - Suc 0) \<or> x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)))"
      using a4 a3 a2 a1 by blast }
  ultimately show "\<exists>xa. (fst (B ! xa) \<le> n \<longrightarrow> (Suc n \<in> FV (snd (B ! xa)) \<longrightarrow> xa < length B \<and>
                   ((\<exists>xb. (xb \<in> FV (snd (B ! xa)) \<and> xb \<noteq> Suc n \<or> (\<exists>x. x \<in> FV t \<and> fst (B ! xa) \<le> x \<and> xb = Suc x) \<or>
                           xb \<in> FV t \<and> \<not> fst (B ! xa) \<le> xb) \<and>xb \<noteq> fst (B ! xa) \<and> fst (B ! xa) < xb \<and> x = xb - Suc 0) \<or>
                    (x \<in> FV (snd (B ! xa)) \<and> x \<noteq> Suc n \<or>(\<exists>xb. xb \<in> FV t \<and> fst (B ! xa) \<le> xb \<and> x = Suc xb) \<or> x \<in> FV t \<and> \<not> fst (B ! xa) \<le> x) \<and>
                    x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and>(Suc n \<notin> FV (snd (B ! xa)) \<longrightarrow>
                   xa < length B \<and>((\<exists>xb. xb \<in> FV (snd (B ! xa)) \<and> xb \<noteq> fst (B ! xa) \<and> fst (B ! xa) < xb \<and> x = xb - Suc 0) \<or>
                    x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x))) \<and>
                 (\<not> fst (B ! xa) \<le> n \<longrightarrow> (n \<in> FV (snd (B ! xa)) \<longrightarrow> xa < length B \<and>
                   ((\<exists>xb. (xb \<in> FV (snd (B ! xa)) \<and> xb \<noteq> n \<or> (\<exists>x. x \<in> FV t \<and> fst (B ! xa) \<le> x \<and> xb = Suc x) \<or>
                           xb \<in> FV t \<and> \<not> fst (B ! xa) \<le> xb) \<and> xb \<noteq> fst (B ! xa) \<and> fst (B ! xa) < xb \<and> x = xb - Suc 0) \<or>
                    (x \<in> FV (snd (B ! xa)) \<and> x \<noteq> n \<or>(\<exists>xb. xb \<in> FV t \<and> fst (B ! xa) \<le> xb \<and> x = Suc xb) \<or> x \<in> FV t \<and> \<not> fst (B ! xa) \<le> x) \<and>
                    x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and>(n \<notin> FV (snd (B ! xa)) \<longrightarrow>xa < length B \<and>
                   ((\<exists>xb. xb \<in> FV (snd (B ! xa)) \<and> xb \<noteq> fst (B ! xa) \<and> fst (B ! xa) < xb \<and> x = xb - Suc 0) \<or>
                    x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)))"
    using a4 a3 a2 a1 by fastforce
next
  fix x
  show "n \<in> FV t1 \<or>
         (\<exists>x<length B.
             (\<exists>xa. xa \<in> FV (snd (B ! x)) \<and> xa \<noteq> fst (B ! x) \<and> fst (B ! x) < xa \<and> n = xa - Suc 0) \<or>
             n \<in> FV (snd (B ! x)) \<and> n \<noteq> fst (B ! x) \<and> \<not> fst (B ! x) < n) \<Longrightarrow>
         x \<in> FV t1 \<and> x \<noteq> n \<or>
         (\<exists>xa<length B.
             (\<exists>xb. xb \<in> FV (snd (B ! xa)) \<and> xb \<noteq> fst (B ! xa) \<and> fst (B ! xa) < xb \<and> x = xb - Suc 0) \<or>
             x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x) \<and>
         x \<noteq> n \<or>
         x \<in> FV t \<Longrightarrow>
         (n \<in> FV t1 \<longrightarrow>
          (\<exists>xa. (fst (B ! xa) \<le> n \<longrightarrow>
                 (Suc n \<in> FV (snd (B ! xa)) \<longrightarrow>
                  xa < length B \<and>
                  ((\<exists>xb. (xb \<in> FV (snd (B ! xa)) \<and> xb \<noteq> Suc n \<or>
                          (\<exists>x. x \<in> FV t \<and> fst (B ! xa) \<le> x \<and> xb = Suc x) \<or>
                          xb \<in> FV t \<and> \<not> fst (B ! xa) \<le> xb) \<and>
                         xb \<noteq> fst (B ! xa) \<and> fst (B ! xa) < xb \<and> x = xb - Suc 0) \<or>
                   (x \<in> FV (snd (B ! xa)) \<and> x \<noteq> Suc n \<or>
                    (\<exists>xb. xb \<in> FV t \<and> fst (B ! xa) \<le> xb \<and> x = Suc xb) \<or> x \<in> FV t \<and> \<not> fst (B ! xa) \<le> x) \<and>
                   x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and>
                 (Suc n \<notin> FV (snd (B ! xa)) \<longrightarrow>
                  xa < length B \<and>
                  ((\<exists>xb. xb \<in> FV (snd (B ! xa)) \<and> xb \<noteq> fst (B ! xa) \<and> fst (B ! xa) < xb \<and> x = xb - Suc 0) \<or>
                   x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x))) \<and>
                (\<not> fst (B ! xa) \<le> n \<longrightarrow>
                 (n \<in> FV (snd (B ! xa)) \<longrightarrow>
                  xa < length B \<and>
                  ((\<exists>xb. (xb \<in> FV (snd (B ! xa)) \<and> xb \<noteq> n \<or>
                          (\<exists>x. x \<in> FV t \<and> fst (B ! xa) \<le> x \<and> xb = Suc x) \<or>
                          xb \<in> FV t \<and> \<not> fst (B ! xa) \<le> xb) \<and>
                         xb \<noteq> fst (B ! xa) \<and> fst (B ! xa) < xb \<and> x = xb - Suc 0) \<or>
                   (x \<in> FV (snd (B ! xa)) \<and> x \<noteq> n \<or>
                    (\<exists>xb. xb \<in> FV t \<and> fst (B ! xa) \<le> xb \<and> x = Suc xb) \<or> x \<in> FV t \<and> \<not> fst (B ! xa) \<le> x) \<and>
                   x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and>
                 (n \<notin> FV (snd (B ! xa)) \<longrightarrow>
                  xa < length B \<and>
                  ((\<exists>xb. xb \<in> FV (snd (B ! xa)) \<and> xb \<noteq> fst (B ! xa) \<and> fst (B ! xa) < xb \<and> x = xb - Suc 0) \<or>
                   x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)))) \<or>
          x \<in> FV t1 \<and> x \<noteq> n \<or> x \<in> FV t) \<and>
         (n \<notin> FV t1 \<longrightarrow>
          (\<exists>xa. (fst (B ! xa) \<le> n \<longrightarrow>
                 (Suc n \<in> FV (snd (B ! xa)) \<longrightarrow>
                  xa < length B \<and>
                  ((\<exists>xb. (xb \<in> FV (snd (B ! xa)) \<and> xb \<noteq> Suc n \<or>
                          (\<exists>x. x \<in> FV t \<and> fst (B ! xa) \<le> x \<and> xb = Suc x) \<or>
                          xb \<in> FV t \<and> \<not> fst (B ! xa) \<le> xb) \<and>
                         xb \<noteq> fst (B ! xa) \<and> fst (B ! xa) < xb \<and> x = xb - Suc 0) \<or>
                   (x \<in> FV (snd (B ! xa)) \<and> x \<noteq> Suc n \<or>
                    (\<exists>xb. xb \<in> FV t \<and> fst (B ! xa) \<le> xb \<and> x = Suc xb) \<or> x \<in> FV t \<and> \<not> fst (B ! xa) \<le> x) \<and>
                   x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and>
                 (Suc n \<notin> FV (snd (B ! xa)) \<longrightarrow>
                  xa < length B \<and>
                  ((\<exists>xb. xb \<in> FV (snd (B ! xa)) \<and> xb \<noteq> fst (B ! xa) \<and> fst (B ! xa) < xb \<and> x = xb - Suc 0) \<or>
                   x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x))) \<and>
                (\<not> fst (B ! xa) \<le> n \<longrightarrow>
                 (n \<in> FV (snd (B ! xa)) \<longrightarrow>
                  xa < length B \<and>
                  ((\<exists>xb. (xb \<in> FV (snd (B ! xa)) \<and> xb \<noteq> n \<or>
                          (\<exists>x. x \<in> FV t \<and> fst (B ! xa) \<le> x \<and> xb = Suc x) \<or>
                          xb \<in> FV t \<and> \<not> fst (B ! xa) \<le> xb) \<and>
                         xb \<noteq> fst (B ! xa) \<and> fst (B ! xa) < xb \<and> x = xb - Suc 0) \<or>
                   (x \<in> FV (snd (B ! xa)) \<and> x \<noteq> n \<or>
                    (\<exists>xb. xb \<in> FV t \<and> fst (B ! xa) \<le> xb \<and> x = Suc xb) \<or> x \<in> FV t \<and> \<not> fst (B ! xa) \<le> x) \<and>
                   x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)) \<and>
                 (n \<notin> FV (snd (B ! xa)) \<longrightarrow>
                  xa < length B \<and>
                  ((\<exists>xb. xb \<in> FV (snd (B ! xa)) \<and> xb \<noteq> fst (B ! xa) \<and> fst (B ! xa) < xb \<and> x = xb - Suc 0) \<or>
                   x \<in> FV (snd (B ! xa)) \<and> x \<noteq> fst (B ! xa) \<and> \<not> fst (B ! xa) < x)))) \<or>
          x \<in> FV t1)"
      apply meson
      apply simp_all         
      apply fastforce
      apply fastforce
      apply ((metis less_or_eq_imp_le less_or_eq_imp_le nat_neq_iff
                    One_nat_def diff_Suc_1 le_imp_less_Suc less_imp_Suc_add)+)[3]
      apply force
      apply rule+
      apply fastforce
      apply (metis One_nat_def diff_Suc_1 le_imp_less_Suc less_or_eq_imp_le nat_neq_iff)
      defer
      defer
      apply ((metis One_nat_def diff_Suc_1 less_or_eq_imp_le nat_neq_iff)+)[2]
      apply (force+)[2]
      apply (metis Suc_n_not_le_n diff_Suc_Suc le_imp_less_Suc le_neq_implies_less less_or_eq_imp_le minus_nat.diff_0)
      apply rule
      apply meson
      apply force
      
      
qed
      (*apply (smt Suc_pred diff_Suc_1 le_imp_less_Suc le_neq_implies_less less_imp_Suc_add less_irrefl_nat zero_less_Suc)
      apply (smt Suc_pred diff_Suc_1 leD le_imp_less_Suc less_imp_Suc_add less_or_eq_imp_le not_less_eq_eq zero_less_Suc)
      apply blast
      defer
      apply (smt One_nat_def diff_Suc_1 le_imp_less_Suc less_or_eq_imp_le)*)
      
      sorry
qed (auto simp: gr0_conv_Suc image_iff FV_shift[of 1, unfolded int_1])

lemma weakening :
  fixes \<Gamma>::lcontext  and t::lterm and A S::ltype and \<sigma> ::"nat\<rightharpoonup>ltype" and n::nat
  assumes well_typed: "\<Gamma> \<turnstile> \<lparr>t|;| \<sigma>\<rparr> |:| A" and
          weaker_ctx: " n \<le> length \<Gamma>" 
  shows "insert_nth n S \<Gamma> \<turnstile> \<lparr>shift_L 1 n t|;| \<sigma>\<rparr> |:| A"
using assms 
proof(induction \<Gamma> t \<sigma> A arbitrary: n rule:has_type_L.induct)
  case (has_type_LAbs \<Gamma>1 T1 t2 \<sigma>1 T2)
    
    have "Suc n\<le>length(\<Gamma>1|,|T1)" using has_type_LAbs(3) by auto

    hence "insert_nth (Suc n) S (\<Gamma>1 |,| T1) \<turnstile> \<lparr>shift_L 1 (Suc n) t2|;| \<sigma>1\<rparr> |:| T2"
      using has_type_LAbs(2)[where n="Suc n"]
      by auto
    then show ?case
      by (auto intro: has_type_L.has_type_LAbs)              
next 
  case(has_type_Tuple L TL \<Gamma>1 \<sigma>1)
    show ?case    
      using has_type_Tuple(1,2) nth_map[of _ L "shift_L 1 n"] 
            has_type_Tuple(4)[OF _ _ has_type_Tuple(5)]
      by (force intro!: has_type_L.intros(14))
next
  case (has_type_ProjT i TL \<Gamma>1 t \<sigma>1)
    show ?case
      using has_type_ProjT(4)[OF has_type_ProjT(5)]
            "has_type_L.intros"(15)[OF has_type_ProjT(1,2)]
      by fastforce
next
  case (has_type_RCD L LT TL \<Gamma> \<sigma>1)
    show ?case
      using has_type_RCD(1-4) nth_map[of _ LT "shift_L 1 n"]
            has_type_RCD(6)[OF _ has_type_RCD(7)]           
      by (force intro!: "has_type_L.intros"(16))+
next
  case (has_type_Let x \<Gamma> t1 \<sigma>1 A t2 B)
    
    have "n \<le> x \<Longrightarrow> (take n \<Gamma> @ drop n \<Gamma> |,| S) \<turnstile> \<lparr>Let var Suc x := shift_L 1 n t1 in shift_L 1 n t2|;| \<sigma>1\<rparr> |:| B"
      using has_type_Let(1,4,6)
            has_type_Let(5)[unfolded length_insert_nth, of n] 
            insert_nth_comp(1)[of n \<Gamma> x]
      by (auto intro!: has_type_L.intros(10))

    then show ?case
      using has_type_Let(4)[OF has_type_Let(6)] 
            has_type_Let(5)[unfolded length_insert_nth, of "Suc n" ] 
            has_type_Let(6)
            insert_nth_comp(2)[OF has_type_Let(6),of x S A]  
      by (auto intro!: has_type_L.intros(10) simp: simpl1) 
next
  case (has_type_LetPattern p B t1 \<sigma>1 \<Gamma> \<sigma>2 t2 A)
    note hyps=this
    show ?case
      using hyps(1,2,3) hyps(5,6)[OF hyps(7)]
      by (auto intro: has_type_L.intros(19))
next
  case (has_type_Case x \<Gamma>1 y t \<sigma>1 A B t1 C t2)

    have Sum_type: "insert_nth n S \<Gamma>1 \<turnstile> \<lparr>shift_L 1 n t|;| \<sigma>1\<rparr> |:| A |+| B"
      using has_type_Case(6)[OF has_type_Case(9)] 
      by auto

    have B1:"n < x \<Longrightarrow> n < y \<Longrightarrow> insert_nth (Suc x) A (insert_nth n S \<Gamma>1) \<turnstile> \<lparr>shift_L 1 n t1|;|\<sigma>1\<rparr> |:| C \<and>
                                  insert_nth (Suc y) B (insert_nth n S \<Gamma>1) \<turnstile> \<lparr>shift_L 1 n t2|;|\<sigma>1\<rparr> |:| C"
      using  has_type_Case(7)[of n] has_type_Case(9)
             has_type_Case(8)[of n]
             insert_nth_comp(1)[of n \<Gamma>1 _ S _] length_insert_nth
      by force

    have B2: " n < x \<Longrightarrow> \<not> n < y \<Longrightarrow> insert_nth (Suc x) A (insert_nth n S \<Gamma>1) \<turnstile> \<lparr>shift_L 1 n t1|;|\<sigma>1\<rparr> |:| C \<and> 
                                      insert_nth y B (insert_nth n S \<Gamma>1) \<turnstile> \<lparr>shift_L 1 (Suc n) t2|;|\<sigma>1\<rparr> |:| C"
      using  has_type_Case(7)[of n, unfolded length_insert_nth]
             has_type_Case(8)[of "Suc n", unfolded length_insert_nth]  
             has_type_Case(9) insert_nth_comp[of n \<Gamma>1 _ S _] 
      by simp

    have B3: "\<not> n < x \<Longrightarrow>  n < y \<Longrightarrow> insert_nth x A (insert_nth n S \<Gamma>1) \<turnstile> \<lparr>shift_L 1 (Suc n) t1|;|\<sigma>1\<rparr> |:| C \<and>
                                      insert_nth (Suc y) B (insert_nth n S \<Gamma>1) \<turnstile> \<lparr>shift_L 1 n t2|;|\<sigma>1\<rparr> |:| C"
      using  has_type_Case(7)[of "Suc n", unfolded length_insert_nth]
             has_type_Case(8)[of n, unfolded length_insert_nth]  
             has_type_Case(9) insert_nth_comp[of n \<Gamma>1 _ S _] 
      by force

    have B4: "\<not> n < x \<Longrightarrow> \<not> n < y \<Longrightarrow> insert_nth x A (insert_nth n S \<Gamma>1) \<turnstile> \<lparr>shift_L 1 (Suc n) t1|;|\<sigma>1\<rparr> |:| C \<and>
                                      insert_nth y B (insert_nth n S \<Gamma>1) \<turnstile> \<lparr>shift_L 1 (Suc n) t2|;|\<sigma>1\<rparr> |:| C"
       using has_type_Case(7)[of "Suc n", unfolded length_insert_nth]
             has_type_Case(8)[of "Suc n", unfolded length_insert_nth]  
             has_type_Case(9) insert_nth_comp(2)[of n \<Gamma>1 _ S _] 
      by (metis Suc_le_mono not_le)+

    show ?case
      using has_type_Case(6)[OF has_type_Case(9)] has_type_Case(1,2)
            has_type_L.intros(22) B1 B2 B3 B4 
      by (force simp add: simpl1 simpl2 simpl3)      
next
  case (has_type_CaseV L TL B \<Gamma> t \<sigma>1  A)
    have branches_wtyped:"\<forall>i<length L. insert_nth (fst (map 
          (\<lambda>p. (if n < fst p then nat (int (fst p) + 1) else fst p,
           shift_L 1 (if fst p \<le> n then Suc n else n) (snd p))) B ! i))
           (TL ! i) (take n \<Gamma> @ drop n \<Gamma> |,| S)
       \<turnstile> \<lparr>snd (map (\<lambda>p. (if n < fst p then nat (int (fst p) + 1) else fst p,
          shift_L 1 (if fst p \<le> n then Suc n else n) (snd p))) B ! i)|;|\<sigma>1\<rparr> |:| A\<and>
       fst (map (\<lambda>p. (if n < fst p then nat (int (fst p) + 1) else fst p,
       shift_L 1 (if fst p \<le> n then Suc n else n) (snd p))) B ! i) \<le> 
       length (take n \<Gamma> @ drop n \<Gamma> |,| S)"
      proof (rule+)
        fix i
        let ?goal =" insert_nth (fst (map 
          (\<lambda>p. (if n < fst p then nat (int (fst p) + 1) else fst p,
           shift_L 1 (if fst p \<le> n then Suc n else n) (snd p))) B ! i))
           (TL ! i) (take n \<Gamma> @ drop n \<Gamma> |,| S)
       \<turnstile> \<lparr>snd (map (\<lambda>p. (if n < fst p then nat (int (fst p) + 1) else fst p,
          shift_L 1 (if fst p \<le> n then Suc n else n) (snd p))) B ! i)|;|\<sigma>1\<rparr> |:| A"
        assume H:"i<length L"
        have P:"\<And>k. k\<le>length (insert_nth (fst (B ! i)) (TL ! i) \<Gamma>) \<Longrightarrow>
                     insert_nth k S (insert_nth (fst (B ! i)) (TL ! i) \<Gamma>) \<turnstile> \<lparr>shift_L 1 k (snd (B ! i))|;|\<sigma>1\<rparr>|:| A"
          using has_type_CaseV(7) H 
          by auto

        then have branches_type_n:"insert_nth n S (insert_nth (fst (B ! i)) (TL ! i) \<Gamma>) \<turnstile> \<lparr>shift_L 1 n (snd (B ! i))|;| \<sigma>1\<rparr> |:| A"
          using  has_type_CaseV(8)    
                 length_insert_nth[of "fst(B!i)" "TL!i" \<Gamma>]
          by (metis le_SucI)

        have branches_type_Sucn:"insert_nth (Suc n) S (insert_nth (fst (B ! i)) (TL ! i) \<Gamma>) \<turnstile> \<lparr>shift_L 1 (Suc n) (snd (B ! i))|;|\<sigma>1\<rparr> |:| A"
          using  has_type_CaseV(8)
                 length_insert_nth[of "fst(B!i)" "TL!i" \<Gamma>] P[of "Suc n"]
          by (metis Suc_le_mono)

        have 1:"n< fst(B!i) \<Longrightarrow> ?goal"
          using has_type_CaseV(1,3,8) H        
          proof -
            
            assume hyps:"n < fst(B!i)" "L \<noteq> \<emptyset>" "length L = length TL" "n \<le> length \<Gamma>" "i < length L"
            have simp_ind:"fst (map (\<lambda>p. (if n < fst p then nat (int (fst p) + 1) else fst p,
                     shift_L 1 (if fst p \<le> n then Suc n else n) (snd p))) B ! i) = 
                     Suc (fst (B!i))"
                     "snd (map (\<lambda>p. (if n < fst p then nat (int (fst p) + 1) else fst p,
                      shift_L 1 (if fst p \<le> n then Suc n else n) (snd p))) B ! i) =
                      shift_L 1 n (snd (B!i))"
              using hyps(1,5)[unfolded  has_type_CaseV(4)] has_type_CaseV(3)
              by force+
              
            from branches_type_n
              have "insert_nth (Suc (fst(B ! i))) (TL ! i) (take n \<Gamma> @ drop n \<Gamma> |,| S) \<turnstile> \<lparr>shift_L 1 n (snd(B ! i))|;|\<sigma>1\<rparr> |:| A"
                using insert_nth_comp(1)[OF hyps(4)] H has_type_CaseV(3) hyps(1)
                by force
            
            with simp_ind show ?thesis using hyps by force
            
          qed

        have  "\<not> n< fst(B!i) \<Longrightarrow> ?goal"
          using has_type_CaseV(1,3,8) H        
          proof -            
            assume hyps:"\<not>n< fst(B!i)" "L \<noteq> \<emptyset>" "length L = length TL" "n \<le> length \<Gamma>" "i < length L"
            
            have simp_ind:"fst (map (\<lambda>p. (if n < fst p then nat (int (fst p) + 1) else fst p,
                           shift_L 1 (if fst p \<le> n then Suc n else n) (snd p))) B ! i) = 
                           fst (B!i)"
                           "snd (map (\<lambda>p. (if n < fst p then nat (int (fst p) + 1) else fst p,
                            shift_L 1 (if fst p \<le> n then Suc n else n) (snd p))) B ! i) =
                            shift_L 1 (Suc n) (snd (B!i))"
              using hyps(1,5)[unfolded has_type_CaseV(4)]
              by force+

            from branches_type_Sucn
              have  "insert_nth (fst(B ! i)) (TL ! i) (take n \<Gamma> @ drop n \<Gamma> |,| S) \<turnstile> \<lparr>shift_L 1 (Suc n) (snd (B ! i))|;|\<sigma>1\<rparr> |:| A"
                using insert_nth_comp(2)[OF hyps(4), of "fst(B!i)"] hyps(1)
                by fastforce

            with simp_ind show ?thesis using hyps by force
              
          qed

        with 1 show ?goal
          by blast
      next
        fix i
        assume H:"i<length L"

        note inf_ctx=has_type_CaseV(7)[rule_format,OF H,THEN conjunct2]

        show "fst (map (\<lambda>p. (if n < fst p then nat (int (fst p) + 1) else fst p,
              shift_L 1 (if fst p \<le> n then Suc n else n) (snd p))) B ! i) \<le> 
              length (take n \<Gamma> @ drop n \<Gamma> |,| S)"
          using inf_ctx Suc_le_mono nth_map fst_conv has_type_CaseV(4) H
          by (cases "n < fst(B!i)") force+          
      qed 

    show ?case
      using has_type_CaseV(1-4)
            has_type_CaseV(6)[OF has_type_CaseV(8)]
            branches_wtyped            
      by ((force intro!: has_type_L.intros(24))+)
      
qed (auto intro!: has_type_L.intros simp: nth_append min_def simpl1 simpl2 simpl3)

lemma fill_keep_value:
  "is_value_L v \<Longrightarrow> is_value_L (fill \<sigma> v)"
by(induction v rule: is_value_L.induct, auto intro: "is_value_L.intros" )

lemma Lmatch_Type_det:
  "Lmatch_Type p \<sigma> \<Longrightarrow> Lmatch_Type p \<sigma>1 \<Longrightarrow> \<sigma> = \<sigma>1"
by (induction arbitrary: \<sigma>1 rule: Lmatch_Type.induct)
   (force simp: "Lmatch_Type.simps"[of "V _ as _", simplified],
     metis (no_types, hide_lams) nth_equalityI 
            "Lmatch_Type.simps"[of "RCD _ _", simplified])

lemma fill_id:
  "fill empty t= t"
proof (induction t)
  case (Tuple L)
    thus ?case by (induction L, simp+)
next
  case (Record L LT)
    thus ?case by (induction LT, simp+)
next
  case (Pattern p)
    show ?case by (induction p, simp+)
next
  case (CaseVar t L B)
    note hyps= this
    then show ?case 
      proof (induction B arbitrary: t)
        case (Cons b B)
          have "map (\<lambda>p. (fst p, fill Map.empty (snd p))) B = B"
            using Cons(1)[OF Cons(2)] Cons(3)
            by force      
          then show ?case
            by (simp add: Cons 
                Cons(3)[of "b" "snd b",OF _ snds.intros[of b], simplified])                  
      qed (simp add: hyps) 
qed (simp+)

lemma lmatch_is_fill:
  "Lmatch p t \<sigma> \<Longrightarrow> \<exists>\<sigma>1. fill \<sigma>1 = \<sigma>"
proof(induction rule:Lmatch.induct)
  case (M_RCD L LT F PL)
    thus ?case
      proof (induction F arbitrary: L LT PL)
        case (Nil)
          show ?case using fill_id by auto
      next
        case (Cons f F')
          obtain p PL' l L' t' LT' where l_prop:"PL = p#PL'" "length F' = length PL'"
                                        "L = l#L'" "length L' = length LT'" "distinct L'"
                                        "LT = t'#LT'" "length PL' = length LT'"
            using Cons(2,5) length_Suc_conv[of _ "length F'"]
                  Cons(3,4)[symmetric]
            by (metis distinct.simps(2))
            
          obtain \<Sigma> where "fill \<Sigma> = \<Odot> F'"
            using Cons(1)[OF l_prop(5,4,2,7) is_value_L.intros(7)[of LT' L']] 
                  Cons(6)[unfolded is_value_L.simps[of "Record _ _", simplified] l_prop]                  
                  Cons(7,8)[of "Suc _",unfolded l_prop, simplified]
            by fastforce
          then show ?case
            using Cons(8)[of 0,unfolded l_prop, simplified]
                  fill_fill_comp[of _ \<Sigma>]
            by fastforce   
      qed
qed blast

method inv_type = (match premises in H:"\<Gamma> \<turnstile> \<lparr> t|;| \<sigma>\<rparr> |:| A" for \<Gamma> t \<sigma> A \<Rightarrow>
                   \<open>insert "has_type_L.simps"[of \<Gamma> t \<sigma> A, simplified]\<close>)  
    
theorem uniqueness_of_types:
  "\<Gamma> \<turnstile> \<lparr>t|;|\<sigma>\<rparr> |:| A \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t|;|\<sigma>\<rparr> |:| B \<Longrightarrow> A=B"
proof (induction \<Gamma> t \<sigma> A arbitrary:B rule: has_type_L.induct)
  case (has_type_Tuple L TL \<Gamma> \<sigma> f)
    note hyps=this
    show ?case 
      using inversion(14)[OF hyps(5)]
            hyps(2,4) List.nth_equalityI[of TL ]
      by force
next
  case (has_type_RCD L LT TL)
    note hyps=this
    show ?case 
      using inversion(16)[OF hyps(7)]
            hyps(3,4,6)
            List.nth_equalityI[of TL]
      by force
next
  case (has_type_LetPattern p B1 \<sigma>)
    note hyps=this
    show ?case 
      using inversion(19)[OF hyps(7)]
            hyps(6) Lmatch_Type_det[OF hyps(2)]
      by force
next
  case (has_type_Case)
    thus ?case using inversion(22) by blast
next
  case (has_type_CaseV)
    thus ?case using inversion(24) by blast
next
  case (has_type_Fix)
    thus ?case using inversion(25) by blast
qed (((metis prod.sel ltype.sel inversion(1-13))+)[13],
     (metis prod.sel ltype.sel inversion(15,17,18,20,21,23))+)


lemma canonical_forms:
  "is_value_L v \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>v|;|\<sigma>\<rparr> |:| Bool \<Longrightarrow> v = LTrue \<or> v = LFalse"
  "is_value_L v \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>v|;|\<sigma>\<rparr> |:| T1 \<rightarrow> T2 \<Longrightarrow> \<exists>t n. v = LAbs T1 t"
  "is_value_L v \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>v|;|\<sigma>\<rparr> |:| Unit \<Longrightarrow> v = unit"
  "is_value_L v \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>v|;|\<sigma>\<rparr> |:| A |\<times>| B \<Longrightarrow> (\<exists>v1 v2. is_value_L v1 \<and> is_value_L v2 \<and> v= \<lbrace>v1,v2\<rbrace>)"
  "is_value_L v \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>v|;|\<sigma>\<rparr> |:| \<lparr>TL\<rparr> \<Longrightarrow> (\<exists>L. is_value_L (Tuple L) \<and> v = Tuple L \<and> length TL = length L)"
  "is_value_L v \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>v|;|\<sigma>\<rparr> |:| \<lparr>L|:|TL\<rparr> \<Longrightarrow> (\<exists>LT. is_value_L (Record L LT) \<and> v = (Record L LT))" 
  "is_value_L v \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>v|;|\<sigma>\<rparr> |:| <L|,|TL> \<Longrightarrow> (\<exists>i v1. i<length L \<and> is_value_L v1 \<and> v = <(L!i):=v1> as <L|,|TL>)"
  "is_value_L v \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>v|;|\<sigma>\<rparr> |:| A|+|B \<Longrightarrow> (\<exists>v1. is_value_L v1 \<and> v = inl v1 as A|+|B) \<or> (\<exists>v1. v = inr v1 as A|+|B \<and> is_value_L v1)"
proof -
  assume  val: "is_value_L v" and 
          typed: "\<Gamma> \<turnstile> \<lparr>v|;|\<sigma>\<rparr> |:| A|+|B"
  show "(\<exists>v1. is_value_L v1 \<and> v = inl v1 as A|+|B) \<or> (\<exists>v1. v = inr v1 as A|+|B \<and> is_value_L v1)"
    using val typed
    by (induction rule: is_value_L.induct, auto elim: "has_type_L.cases")           
next
   assume  val: "is_value_L v" and 
          typed: "\<Gamma> \<turnstile> \<lparr>v|;|\<sigma>\<rparr> |:| <L|,|TL>"
  show "\<exists>i v1. i<length L \<and> is_value_L v1 \<and> v = <(L!i):=v1> as <L|,|TL>"
    using val typed
    by (induction rule: is_value_L.induct, auto elim: "has_type_L.cases")
qed (auto elim: "is_value_L.cases" "has_type_L.cases")  

lemma coherent_val_imp_Lmatch:
  "coherent p A \<Longrightarrow> \<Gamma>\<turnstile> \<lparr>t|;|\<sigma>\<rparr> |:| A \<Longrightarrow> is_value_L t \<Longrightarrow>\<exists>\<sigma>. Lmatch p t \<sigma>"
proof (induction arbitrary:t \<Gamma> \<sigma> rule:coherent.induct)
  case (2 L PL TL)
    note hyps=this
    obtain LT where H:"is_value_L (Record L LT)" "t = Record L LT"
      using canonical_forms(6)[OF hyps(7,6)]
      by blast
         
    note lenTL_LT = hyps(6)[unfolded H(2) has_type_L.simps[of _ "Record L LT" _  "\<lparr>L|:|TL\<rparr>", simplified],
                        THEN conjunct2, THEN conjunct2, THEN conjunct1]
         and TL_types = hyps(6)[unfolded H(2) has_type_L.simps[of _ "Record L LT" _  "\<lparr>L|:|TL\<rparr>", simplified],
                        THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2]
      
    have "\<exists>F. (\<forall>i<length PL. Lmatch (PL ! i) (LT ! i) (F!i)) \<and> length F = length PL"
      using lenTL_LT TL_types H(1)[unfolded is_value_L.simps[of "Record L LT", simplified]]
            hyps(3)[symmetric] hyps(5)[of _ \<Gamma> "LT!_" \<sigma> ]
      proof (induction PL arbitrary: TL LT)
        case (Cons p PL')
          obtain l LT' Ta TL' where l_decomp:"TL = Ta # TL'" "LT= l#LT'" "length TL'= length PL'"
                                             "length LT' = length PL'"
            using Cons(2,5) length_Suc_conv by metis

          note len'= l_decomp(4)[unfolded l_decomp(3)[symmetric]]
          obtain F where Fprop:"(\<forall>i<length PL'. Lmatch (PL' ! i) (LT' ! i) (F ! i)) \<and> length F = length PL'"
            using Cons(1)[OF len' _ _ l_decomp(3)] 
                  Cons(6)[of "Suc _" "Suc _", unfolded l_decomp(1,2), simplified]
                  Cons(3,4)[unfolded l_decomp(1,2)]
            by (metis (no_types, lifting) Suc_leI le_imp_less_Suc length_Cons nth_Cons_Suc)
          obtain a where p_match:"Lmatch p l a"
            using Cons(6)[of 0 0, unfolded l_decomp(1,2), simplified] 
                   Cons(3,4)[rule_format,of 0, unfolded l_decomp(1,2),simplified]
            by auto
          have "(\<forall>i<length (p#PL'). Lmatch ((p#PL') ! i) ((l#LT') ! i) ((a#F) ! i)) \<and> 
                length (a#F) = length (p#PL')"
            proof (rule+)
              fix i
              assume inf_len:"i<length (p#PL')"
              show "Lmatch ((p#PL') ! i) ((l#LT') ! i) ((a#F) ! i)"
                using Fprop[THEN conjunct1, rule_format]
                      p_match inf_len
                by (cases i, force+)
            next
              show "length (a#F) = length (p#PL')"
                using Fprop[THEN conjunct2] 
                by force
            qed
          then show ?case using l_decomp(2) by blast
      qed simp
    then obtain F where exF:"\<forall>i<length PL. Lmatch (PL ! i) (LT ! i) (F!i)"
                            "length F = length PL"
      by blast
    have "\<And>i. i < length PL \<Longrightarrow> Lmatch (PL ! i) (LT ! i) (F ! i)"
      proof -
        fix i 
        assume inf_len: "i<length PL"
        obtain \<sigma> where "Lmatch (PL ! i) (LT ! i) \<sigma>"
          using exF(2) H(1)[unfolded is_value_L.simps[of "Record L LT", simplified]]
                hyps(6)[unfolded H(2) has_type_L.simps[of _ "Record L LT" _ "\<lparr>L|:|TL\<rparr>", simplified],
                        THEN conjunct2, THEN conjunct2]
                hyps(3)[symmetric] hyps(5)[of i \<Gamma> "LT!i" \<sigma> ] inf_len
          by presburger
        then show "Lmatch (PL ! i) (LT ! i) (F ! i)"
          using exF(1) inf_len 
          by presburger
      qed          
       
    then show ?case
      using "Lmatch.intros"(2)[OF _ _ exF(2) _ H(1)]
            hyps(6)[unfolded H(2) has_type_L.simps[of _ "Record L LT" _ "\<lparr>L|:|TL\<rparr>", simplified]]
            hyps(3) H(2)
      by force
qed (auto intro: Lmatch.intros) 

theorem progress:
  "\<emptyset> \<turnstile> \<lparr>t|;|empty\<rparr> |:| A \<Longrightarrow> is_value_L t \<or> (\<exists>t1. eval1_L t t1)"
proof (induction "\<emptyset>::ltype list" t "empty::nat\<rightharpoonup>ltype" A rule: has_type_L.induct)
  case (has_type_LIf t1 t2 A t3)
    thus ?case by (metis eval1_L.intros canonical_forms)
next
  case (has_type_Tuple L TL)
    note hyps=this
    have "(\<exists>j<length L. (\<forall>i<j. is_value_L (L ! i)) \<and> (\<exists>t1. eval1_L (L ! j) t1))\<or>
          is_value_L (Tuple L)"
      using hyps(4)
      proof (induction L)
        case Nil
          show ?case 
            using "is_value_L.intros"(6)[of \<emptyset>, simplified]
            by blast
      next
        case (Cons a L')
          have "is_value_L a\<Longrightarrow> ?case"
            using Cons(1)[OF Cons(2)[of "Suc _", simplified], simplified] "is_value_L.intros"(6)[of "a#L'"]
                  "is_value_L.simps"[of "Tuple _", simplified]
            by meson (metis Suc_less_eq nth_Cons_0 nth_Cons_Suc old.nat.exhaust length_Cons,
                   metis One_nat_def Suc_pred le_imp_less_Suc length_Cons less_SucE not_less_eq nth_Cons')
          then show ?case
            using Cons(2)[of 0, simplified]
            by fastforce
      qed 
    then show ?case
      using eval1_L_Tuple[of "Suc _" L, simplified] "is_value_L.intros"(6)[of "take _ L", simplified]
      by force
next
  case (has_type_RCD L LT TL)
    note hyps=this
    have "(\<exists>j<length LT. (\<forall>i<j. is_value_L (LT ! i)) \<and> (\<exists>t1. eval1_L (LT ! j) t1))\<or>
          is_value_L (Record L LT)"
      using hyps(2-4,6)
      proof (induction LT arbitrary: L TL)
        case Nil
          show ?case 
            using "is_value_L.intros"(7)[of \<emptyset>, simplified] 
            by blast
      next
        case (Cons a LT')
          obtain l L' t TL' where l_prop:"L = l#L'" "length L' = length LT'"
                                  "TL = t#TL'" "length LT' = length TL'"
            using length_Suc_conv Cons(3,4)
            by metis

          note dist_L' = Cons(2)[unfolded l_prop(1) distinct.simps(2)[of l L'], THEN conjunct2]

          have "is_value_L a\<Longrightarrow> ?case"
            using Cons(1)[OF dist_L' l_prop(4,2) Cons(5)[of "Suc _", simplified], simplified]
            by meson (metis Suc_less_eq nth_Cons_0 nth_Cons_Suc old.nat.exhaust length_Cons,
                      fastforce simp: "is_value_L.simps"[of "Record L (a#LT')", simplified] 
                                      less_Suc_eq_0_disj Cons(4)[simplified]
                                      "is_value_L.simps"[of "Record L' LT'", simplified])
          then show ?case
            using Cons(5)[of 0, simplified]
            by fastforce
      qed 
    then show ?case
      using eval1_L_RCD[of _ LT L] "is_value_L.intros"(7)[of "take _ LT" "take _ L", simplified]
            hyps(4)
      by force
next
  case (has_type_ProjT i TL t)
   thus ?case 
     by (metis eval1_L.intros canonical_forms)     
next
  case (has_type_CaseV L B LT t  A)
    note hyps=this
    show ?case
      using eval1_L.intros(32,33) hyps(6) canonical_forms(7)[OF _ hyps(5)]
      by metis
next
  case (has_type_Case t A B x t1 C y t2)
    note hyps=this
    show ?case
      using canonical_forms(8)[OF _ hyps(3)] hyps(4) eval1_L.intros(27-29)
      by blast
next
  case (has_type_LetPattern p B \<sigma> t1 t2 A)
    note hyps=this
    show ?case 
      using hyps(4) coherent_val_imp_Lmatch[OF hyps(1,3)] eval1_L.intros(25,26) 
      by blast
qed (force intro!: is_value_L.intros eval1_L.intros dest: canonical_forms)+


lemma shift_down:
  "insert_nth n U \<Gamma> \<turnstile> \<lparr>t|;|\<sigma>\<rparr> |:| A \<Longrightarrow> n \<le> length \<Gamma> \<Longrightarrow>
   (\<And>x. x \<in> FV t \<Longrightarrow> x \<noteq> n) \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>shift_L (- 1) n t|;|\<sigma>\<rparr> |:| A"
proof (induction "insert_nth n U \<Gamma>" t \<sigma> A arbitrary: \<Gamma> n U rule: has_type_L.induct)
  case (has_type_LAbs V t T)
  from this(1,3,4) show ?case
    by (fastforce intro: has_type_L.intros has_type_LAbs.hyps(2)[where n="Suc n"])+
next
  case (has_type_Tuple L TL)
    note hyps=this
    have "\<And>i x. i < length L \<Longrightarrow> x \<in> FV (L ! i) \<Longrightarrow> x \<noteq> n"
      using hyps(6)[simplified, unfolded Bex_def in_set_conv_nth]
      by blast
    then show ?case 
      using has_type_L.intros(14)[of "map (shift_L (-1) n) L", simplified]
            hyps(1,2) hyps(4)[OF _ _ _ hyps(5), simplified] 
      by force  
next
  case (has_type_ProjT)
    show ?case
      using has_type_ProjT(4)[OF _ has_type_ProjT(5)] has_type_ProjT(6)
            "has_type_L.intros"(15)[OF has_type_ProjT(1,2)]
      by fastforce     
next
  case (has_type_RCD L LT TL \<sigma>)
    show ?case
      using has_type_RCD(1-4,8)
            has_type_RCD(6)[OF _ _ has_type_RCD(7), simplified]           
      by (force intro!: "has_type_L.intros"(16))+
next
   case (has_type_Let x t \<sigma> A t1 B)
    note hyps=this
    have H1:"\<And>x. x \<in> FV t \<Longrightarrow> x \<noteq> n" "\<And>y.\<exists>xa. xa \<in> FV t1 \<and> xa \<noteq> x \<and> y = (if x < xa then xa - 1 else xa)\<Longrightarrow> y\<noteq>n"
            
      using hyps(7)[unfolded FV.simps Bex_def image_def, simplified]
      by auto
    
    hence H2: "n < x \<Longrightarrow> (\<And>y. y\<in> FV t1 \<Longrightarrow> y\<noteq> n)"
      using hyps H1
      by (metis leD nat_less_le)
      
    have "n<x \<Longrightarrow> Suc (nat (int x - 1)) = x"
      using H1
      by fastforce
    hence K:"n<x \<Longrightarrow>  insert_nth x A (insert_nth n U \<Gamma>) =
            insert_nth n U (insert_nth (nat (int x - 1)) A \<Gamma>)"
      using insert_nth_comp(2)[of "(nat (int x - 1))" \<Gamma> n A U]
            hyps(1)
      by force
      
    have K2:"\<And>y. \<not> n < x \<Longrightarrow> y\<in>FV t1 \<Longrightarrow> y\<noteq>Suc n"
      using H1(2)
      by force
    have "n < x \<Longrightarrow> insert_nth (nat (int x - 1)) A \<Gamma> \<turnstile> \<lparr>shift_L (- 1) n t1|;|\<sigma>\<rparr> |:| B"
      by (metis hyps(5) K H2 hyps(6) le_SucI length_insert_nth)
    
    hence C1:"n < x \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Let var nat (int x - 1) := shift_L (- 1) n t in shift_L (- 1) n t1|;|\<sigma>\<rparr> |:| B"
      using hyps(1) hyps(3)[OF _ hyps(6) _, simplified] H1(1)
      by (force intro: "has_type_L.intros")
      
    have "\<not> n < x \<Longrightarrow> insert_nth x A \<Gamma> \<turnstile> \<lparr>shift_L (- 1) (Suc n) t1|;|\<sigma>\<rparr> |:| B"
      using insert_nth_comp(2)[of "(nat (int x - 1))" \<Gamma> n A U]
            hyps(1) H1(2) hyps(5)[of "Suc n" ] K2
      by (metis Suc_leI hyps(5) hyps(6) insert_nth_comp(2) le_imp_less_Suc length_insert_nth not_le)
    
    hence "\<not> n < x \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Let var x := shift_L (- 1) n t in shift_L (- 1) (Suc n) t1|;|\<sigma>\<rparr> |:| B"
      using hyps(6) hyps(3)[OF _ hyps(6) _ , simplified] H1(1)
      by (force intro: "has_type_L.intros")      

    with C1 show ?case by simp
      
next
  case (has_type_ProjR L l TL t)
    note hyps=this
    show ?case
      using hyps(7)[simplified] hyps(1-3)
            hyps(5)[OF _ hyps(6), simplified]
      by (force intro!: has_type_L.intros(17))
next
  case (has_type_Case x y t \<sigma>1 A B t1 C t2)
    note hyps=this  
    have FV_t: "\<And>z. z\<in>FV t \<Longrightarrow> z\<noteq>n" "\<And>z. z \<in> FV t2 \<and> z \<noteq> y \<and> \<not> y < z \<Longrightarrow> z\<noteq>n"
               "\<And>z. (\<exists>x. x \<in> FV t2 \<and> x \<noteq> y \<and> y < x \<and> z = x - Suc 0) \<Longrightarrow> z\<noteq>n"
               "\<And>z. z \<in> FV t1 \<and> z \<noteq> x \<and> \<not> x < z \<Longrightarrow> z\<noteq>n"
               "\<And>z. (\<exists>y. y \<in> FV t1 \<and> y \<noteq> x \<and> x < y \<and> z = y - Suc 0) \<Longrightarrow> z\<noteq>n"
      using hyps(10)[simplified, unfolded image_iff Bex_def, simplified]
      by blast+

    have Sum_type: "\<Gamma> \<turnstile> \<lparr>shift_L (-1) n t|;| \<sigma>1\<rparr> |:| A |+| B"
      using hyps(4)[OF _ hyps(9), simplified] FV_t
      by auto
    
    have le_x:"n < x \<Longrightarrow> insert_nth x A (insert_nth n U \<Gamma>) = insert_nth n U (insert_nth (x - Suc 0) A \<Gamma>)"
      using One_nat_def diff_Suc_1 insert_nth_comp(1)[of n \<Gamma> "x-Suc 0" U A,OF hyps(9)]
      by fastforce

    have le_y:"n < y \<Longrightarrow> insert_nth y B (insert_nth n U \<Gamma>) = insert_nth n U (insert_nth (y - Suc 0) B \<Gamma>)"
      using One_nat_def diff_Suc_1 insert_nth_comp(1)[of n \<Gamma> "y-Suc 0" U B,OF hyps(9)]
            FV_t(2)
      by fastforce
    
    have ge_x:"\<not> n < x \<Longrightarrow>  insert_nth x A (insert_nth n U \<Gamma>) = insert_nth (Suc n) U (insert_nth x A \<Gamma>)"
      using not_le insert_nth_comp(2)[OF hyps(9),of x U A]
      by metis

    have ge_y:"\<not> n < y \<Longrightarrow> insert_nth y B (insert_nth n U \<Gamma>) = insert_nth (Suc n) U (insert_nth y B \<Gamma>)" 
      using not_le insert_nth_comp(2)[OF hyps(9),of y U B] 
      by metis

    have FV_inf:"n < x \<Longrightarrow> (\<And>z. z\<in>FV t1 \<Longrightarrow> z\<noteq>n)"
                "n < y \<Longrightarrow> (\<And>z. z\<in>FV t2 \<Longrightarrow> z\<noteq>n)"
      using FV_t(3,5)[of "_-Suc 0", simplified] FV_t(2,4) hyps leD nat_less_le
      by metis+

    have FV_sup:"\<And>z. \<not> n < x \<Longrightarrow> z\<in>FV t1 \<Longrightarrow> z\<noteq>Suc n"
                "\<And>z. \<not> n < y \<Longrightarrow> z\<in>FV t2 \<Longrightarrow> z\<noteq>Suc n"
      using FV_t(3,5)[of "_-Suc 0", simplified]
      by fastforce+

    have B1:"n < x \<Longrightarrow> n < y \<Longrightarrow> insert_nth (x-Suc 0) A \<Gamma> \<turnstile> \<lparr>shift_L (-1) n t1|;|\<sigma>1\<rparr> |:| C \<and>
                                  insert_nth (y-Suc 0) B \<Gamma> \<turnstile> \<lparr>shift_L (-1) n t2|;|\<sigma>1\<rparr> |:| C"
      using  hyps(6)[OF le_x] hyps(9) FV_inf hyps(8)[OF le_y] 
      by force           

    have B2: " n < x \<Longrightarrow> \<not> n < y \<Longrightarrow> insert_nth (x-Suc 0) A \<Gamma> \<turnstile> \<lparr>shift_L (-1) n t1|;|\<sigma>1\<rparr> |:| C \<and> 
                                      insert_nth y B \<Gamma> \<turnstile> \<lparr>shift_L (-1) (Suc n) t2|;|\<sigma>1\<rparr> |:| C"
      using  hyps(6)[OF le_x] hyps(8)[OF ge_y] hyps(9) FV_inf(1) FV_sup(2)
      by force

    have B3: "\<not> n < x \<Longrightarrow>  n < y \<Longrightarrow> insert_nth x A \<Gamma> \<turnstile> \<lparr>shift_L (-1) (Suc n) t1|;|\<sigma>1\<rparr> |:| C \<and>
                                      insert_nth (y-Suc 0) B \<Gamma> \<turnstile> \<lparr>shift_L (-1) n t2|;|\<sigma>1\<rparr> |:| C"
      using hyps(6)[OF ge_x] hyps(8)[OF le_y] hyps(9) FV_inf(2) FV_sup(1)
      by force

    have B4: "\<not> n < x \<Longrightarrow> \<not> n < y \<Longrightarrow> insert_nth x A \<Gamma> \<turnstile> \<lparr>shift_L (-1) (Suc n) t1|;|\<sigma>1\<rparr> |:| C \<and>
                                      insert_nth y B \<Gamma> \<turnstile> \<lparr>shift_L (-1) (Suc n) t2|;|\<sigma>1\<rparr> |:| C"
       using hyps(6)[OF ge_x] hyps(8)[OF ge_y] hyps(9) FV_sup
       by force

    show ?case
      using Sum_type hyps(1,2,9)
            has_type_L.intros(22) B1 B2 B3 B4
      by (force simp add: simpl1 simpl2 simpl3)
next
  case (has_type_CaseV L TL B t \<sigma>  A)
    note hyps_t=this
    let ?f = " (\<lambda>k t. (\<lambda>y. y - Suc 0) ` ((FV t - {fst(B!k)}) \<inter> Collect (op < (fst(B!k)))) \<union> (FV t - {fst(B!k)}) \<inter> 
                {y. \<not> fst(B!k) < y})"

      
    have FV_t: "\<And>z. z\<in>FV t \<Longrightarrow> z\<noteq>n" 
                "\<And>z i. i<length B \<Longrightarrow> z \<in> FV (snd(B!i)) \<and> z \<noteq> (fst(B!i)) \<and> \<not> (fst(B!i)) < z \<Longrightarrow> z\<noteq>n"
                "\<And>z i. i<length B \<Longrightarrow>(\<exists>y. y \<in> FV (snd(B!i)) \<and> y \<noteq> (fst(B!i)) \<and> (fst(B!i)) < y \<and> z = y - Suc 0) \<Longrightarrow> z\<noteq>n"
      using hyps_t(9)[simplified, unfolded Bex_def set_conv_nth image_def, simplified]
            fst_conv snd_conv
      by (fast,(metis prod.collapse)+)

    have branches_wtyped:" \<forall>i<length L.
       insert_nth (fst (map (\<lambda>p. (if n < fst p then nat (int (fst p) + - 1) else fst p,
       shift_L (- 1) (if fst p \<le> n then Suc n else n) (snd p))) B ! i)) (TL ! i) \<Gamma>
       \<turnstile> \<lparr>snd (map (\<lambda>p. (if n < fst p then nat (int (fst p) + - 1) else fst p,
          shift_L (- 1) (if fst p \<le> n then Suc n else n) (snd p))) B ! i)|;|\<sigma>\<rparr> |:| A \<and>
       fst (map (\<lambda>p. (if n < fst p then nat (int (fst p) + - 1) else fst p,
           shift_L (- 1) (if fst p \<le> n then Suc n else n) (snd p))) B ! i) \<le> length \<Gamma>"
      proof (rule+)
        fix i
        let ?goal = " insert_nth (fst (map (\<lambda>p. (if n < fst p then nat (int (fst p) + - 1) else fst p,
                     shift_L (- 1) (if fst p \<le> n then Suc n else n) (snd p))) B ! i)) (TL ! i) \<Gamma>
                     \<turnstile> \<lparr>snd (map (\<lambda>p. (if n < fst p then nat (int (fst p) + - 1) else fst p,
                     shift_L (- 1) (if fst p \<le> n then Suc n else n) (snd p))) B ! i)|;|\<sigma>\<rparr> |:| A"
        assume H:"i<length L"
        note i_lenB=H[unfolded hyps_t(4)]
        have P:"\<And>k \<Gamma>' U'. insert_nth (fst(B!i)) (TL ! i) (insert_nth n U \<Gamma>) = insert_nth k U' \<Gamma>' \<Longrightarrow> 
                        k\<le>length \<Gamma>' \<Longrightarrow> (\<forall>x. x \<in> FV (snd(B ! i)) \<longrightarrow> x \<noteq> k) \<Longrightarrow>
                        \<Gamma>' \<turnstile> \<lparr>shift_L (-1) k (snd(B ! i))|;|\<sigma>\<rparr>|:| A"
          using hyps_t(7) H 
          by blast
          
        have 1:"n< fst(B!i) \<Longrightarrow> ?goal"
          using hyps_t(1,3,8) H        
          proof -
            
            assume hyps:"n < (fst(B!i))" "L \<noteq> \<emptyset>" "length L = length TL" "n \<le> length \<Gamma>" "i < length L"
            have simp_ind:"fst (map (\<lambda>p. (if n < fst p then nat (int (fst p) + -1) else fst p,
                           shift_L (-1) (if fst p \<le> n then Suc n else n) (snd p))) B ! i) = 
                           fst (B!i) - Suc 0"
                           "snd (map (\<lambda>p. (if n < fst p then nat (int (fst p) + -1) else fst p,
                            shift_L (-1) (if fst p \<le> n then Suc n else n) (snd p))) B ! i) =
                            shift_L (-1) n (snd (B!i))"
              using hyps(1,5)[unfolded hyps_t(5)] has_type_CaseV(4)
              by force+
            
            have ins_eq:"insert_nth (fst(B!i)) (TL ! i) (insert_nth n U \<Gamma>) =
                    insert_nth n U (insert_nth (fst(B!i) - Suc 0) (TL ! i) \<Gamma>)"
             proof -
               from hyps(1) have "n\<le> fst(B!i) - Suc 0" "Suc (fst(B!i)-Suc 0) = fst(B!i)"
                 by linarith+
               thus ?thesis
                 using insert_nth_comp(1)[OF hyps(4),of "fst(B!i)-Suc 0", symmetric]
                 by presburger
             qed
            
            from hyps(1) have "\<And>x. x \<in> FV (snd(B ! i)) \<Longrightarrow> x \<noteq> n"
              using  FV_t(2)[OF i_lenB]
              by fastforce              
              
            with ins_eq have "insert_nth (fst(B!i) - Suc 0) (TL ! i) \<Gamma> \<turnstile> \<lparr>shift_L (- 1) n (snd(B ! i))|;|\<sigma>\<rparr> |:| A"
              using P[of n U "insert_nth (fst(B!i) - Suc 0) (TL ! i) \<Gamma>"] le_SucI[OF hyps(4)]
               by (metis length_insert_nth)
       
            with simp_ind show ?goal
              by (simp add: hyps min_def del: insert_nth_take_drop)
              
          qed

        have  "\<not> n < fst(B!i) \<Longrightarrow> ?goal"
          using hyps_t(1,3,8) H        
          proof -            
            assume hyps:"\<not>n < (fst(B!i))" "L \<noteq> \<emptyset>" "length L = length TL" "n \<le> length \<Gamma>" "i < length L"
            
            have simp_ind:"fst (map (\<lambda>p. (if n < fst p then nat (int (fst p) + -1) else fst p,
                           shift_L (-1) (if fst p \<le> n then Suc n else n) (snd p))) B ! i) = 
                           fst (B!i)"
                           "snd (map (\<lambda>p. (if n < fst p then nat (int (fst p) + -1) else fst p,
                            shift_L (-1) (if fst p \<le> n then Suc n else n) (snd p))) B ! i) =
                            shift_L (-1) (Suc n) (snd (B!i))"
              using hyps(1,5)[unfolded hyps_t(5)] has_type_CaseV(4)
              by force+

              from hyps(1) have "\<And>x. x \<in> FV (snd (B!i)) \<Longrightarrow> x \<noteq> Suc n"
                using FV_t(3)[of i "_-Suc 0",simplified] i_lenB
                by fastforce              

              hence  "insert_nth (fst(B!i)) (TL ! i) \<Gamma> \<turnstile> \<lparr>shift_L (-1) (Suc n) (snd (B!i))|;|\<sigma>\<rparr> |:| A"
                using insert_nth_comp(2)[OF hyps(4), of "fst(B!i)"] hyps(4)[unfolded Suc_le_mono[of n,symmetric]]
                      P[of "Suc n"] hyps(1)[unfolded not_le]
                by fastforce

            with simp_ind show ?goal using hyps by simp
              
          qed

        with 1 show ?goal
          by fast
      next
        fix i
        assume H:"i<length L"
        show "fst (map (\<lambda>p. (if n < fst p then nat (int (fst p) + - 1) else fst p,
           shift_L (- 1) (if fst p \<le> n then Suc n else n) (snd p))) B ! i) \<le> length \<Gamma>"
          using hyps_t(4,8) H hyps_t(7)[rule_format, OF H, THEN conjunct2]
          by (cases "n<fst(B!i)")  simp+
         
      qed 
    show ?case
      using hyps_t(1-5) 
            hyps_t(6)[OF _ hyps_t(8), simplified]
            FV_t branches_wtyped
      by (force intro!: has_type_L.intros(24))
qed (fastforce intro: has_type_L.intros simp: nth_append min_def simpl1 simpl2 simpl3)+


abbreviation incl_map::"pcontext \<Rightarrow> pcontext\<Rightarrow> bool" (infix "\<subseteq>\<^sub>f" 75) where
"\<sigma> \<subseteq>\<^sub>f \<sigma>1 \<equiv> (\<forall>x\<in>dom \<sigma>. \<sigma> x = \<sigma>1 x)"


lemma weakening_pattern:
  "\<Gamma> \<turnstile> \<lparr>t|;|\<sigma>\<rparr> |:| A \<Longrightarrow> \<sigma> \<subseteq>\<^sub>f \<sigma>1  \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t|;|\<sigma>1\<rparr> |:| A"
proof (induction \<Gamma> t \<sigma> A arbitrary: \<sigma>1 rule: has_type_L.induct)
  case (has_type_Tuple L TL \<Gamma> \<sigma>)
    note hyps=this 
    show ?case 
      using hyps(1,2) hyps(4)[of _ \<sigma>1] has_type_L.intros(14) hyps(5)
      by metis
next
  case (has_type_ProjT i TL \<Gamma> t \<sigma>)
    note hyps=this
    show ?case 
      using hyps(1,2,5) hyps(4)[of \<sigma>1] has_type_L.intros(15)
      by force
next
  case (has_type_RCD L TL LT \<Gamma> \<sigma>)
    note hyps=this
    show ?case 
      using hyps(1-4,7) hyps(6)[of _ \<sigma>1]
      by (force intro!: has_type_L.intros(16))
next
  case (has_type_LetPattern p  B \<sigma> \<Gamma> t1 \<sigma>2 t2 A)
    note hyps=this
    have "\<sigma>2 ++ \<sigma> \<subseteq>\<^sub>f \<sigma>1 ++ \<sigma>"
      proof (rule, simp)
        fix x1
        assume x_dom:"x1\<in> dom \<sigma> \<or> x1\<in> dom \<sigma>2"
        have "x1 \<in> dom \<sigma> \<Longrightarrow> (\<sigma>2 ++ \<sigma>) x1 = (\<sigma>1 ++ \<sigma>) x1" by force
        moreover have "x1\<in> dom \<sigma>2 \<Longrightarrow> (\<sigma>2 ++ \<sigma>) x1 = (\<sigma>1 ++ \<sigma>) x1" 
          using hyps(7)
          by (metis map_add_def)
        ultimately show "(\<sigma>2 ++ \<sigma>) x1 = (\<sigma>1 ++ \<sigma>) x1" using x_dom by blast
      qed

    then show ?case 
      using hyps(1,2) hyps(5)[OF hyps(7)] hyps(6)[of "\<sigma>1++\<sigma>"]
      by (force intro: has_type_L.intros)
next
  case (has_type_Case)
    note hyps=this(1-9)
    show ?case 
      using hyps(1,2,9) hyps(6-8)[of \<sigma>1]
      by (force intro: has_type_L.intros)
next
  case (has_type_CaseV L TL B \<Gamma> t \<sigma> A)
    note hyps=this
    have "\<forall>i<length L. insert_nth (fst(B!i)) (TL ! i) \<Gamma> \<turnstile> \<lparr>snd (B ! i)|;|\<sigma>1\<rparr> |:| A \<and> fst(B!i) \<le> length \<Gamma>"
      using hyps(7,8)
      by meson

    then show ?case 
      using hyps(1-5) hyps(6)[OF hyps(8)] 
      by (force intro!: has_type_L.intros)
qed (force intro: has_type_L.intros simp: nth_append min_def)+


lemma substitution:
  "\<Gamma> \<turnstile> \<lparr>t|;|\<sigma>\<rparr> |:| A \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>LVar n|;|\<sigma>1\<rparr> |:| S \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>s|;|\<sigma>1\<rparr> |:| S \<Longrightarrow> 
  \<sigma>1 \<subseteq>\<^sub>f \<sigma>\<Longrightarrow> \<Gamma> \<turnstile> \<lparr>subst_L n s t|;|\<sigma>\<rparr> |:| A"
proof (induction \<Gamma> t \<sigma> A arbitrary: s n \<sigma>1 rule: has_type_L.induct)
  case (has_type_LAbs \<Gamma> T1 t \<sigma> T2)
    note hyps=this
    show ?case 
      using weakening[where n=0, unfolded insert_nth_def nat.rec]
            inversion(4) hyps(2)[of "Suc n" \<sigma>1 "shift_L 1 0 s"]
            hyps(3,4,5) 
      by (fastforce intro!: has_type_L.intros)
next
  case (has_type_ProjT i TL \<Gamma> t \<sigma>)
    note hyps=this 
    show ?case
      using has_type_L.intros(15)[OF hyps(1,2)] hyps(4-) 
      by force
next
  case (has_type_Let x \<Gamma> t1 \<sigma> A t2 B)
    note hyps=this 
         
    have "x \<le> n\<Longrightarrow> (Suc n, S) |\<in>| insert_nth x A \<Gamma>"
      proof -
        assume H: "x \<le> n"
        have 1:"Suc n < length (insert_nth x A \<Gamma>)"
          using inversion(4)[OF hyps(6), simplified] hyps(1)
          by force
        from H have "(insert_nth x A \<Gamma>) ! (Suc n) = S"
          using nth_append[of "take x \<Gamma>" "drop x \<Gamma> |,| A" "Suc n", unfolded length_take,  simplified]
                nth_Cons[of A "drop x \<Gamma>" "Suc n-x", simplified] inversion(4)[OF hyps(6), simplified]
                hyps(1) nth_drop[of x "n-x" \<Gamma>]
          by (metis Suc_diff_le Suc_lessD append_Cons append_Nil2 append_eq_append_conv_if 
                    insert_nth_take_drop le_add_diff_inverse le_neq_implies_less less_imp_le_nat 
                    min_def not_add_less1 nth_Cons_Suc)
        with 1 show ?thesis by simp
      qed
    hence A: "x \<le> n \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Let var x := subst_L n s t1 in subst_L (Suc n) (shift_L 1 x s) t2|;|\<sigma>\<rparr> |:| B"
      using hyps(4)[of n \<sigma>1 s,OF _ _ hyps(8)] hyps(5)[of "Suc n",OF _ _ hyps(8)] hyps(1,6,7)
            weakening[where n=x,OF hyps(7,1)] 
            inversion(4)[OF hyps(6)]        
      by (force intro!: has_type_L.intros(4,10))
     
    have "\<not> x \<le> n \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Let var x := subst_L n s t1 in subst_L n (shift_L 1 x s) t2|;|\<sigma>\<rparr> |:| B"
      using hyps(4)[of n _ s,OF _ _ hyps(8)] hyps(1,6-8) weakening[where n=x,OF _ hyps(1)]
            inversion(4)[OF hyps(6)] hyps(5)[of _ _ "shift_L 1 x s",OF _ _ hyps(8)] 
            not_le[of x n] nth_take[of n x \<Gamma>] nth_append[of "take x \<Gamma>" _ n, simplified]            
      by (force intro!: has_type_L.intros(4,10))

    with A show ?case by simp
      
next
  case (has_type_LetPattern p B \<sigma> \<Gamma> t1 \<sigma>2 t2 A)
    note hyps=this 
    have A:"\<sigma>1 \<subseteq>\<^sub>f \<sigma>2 ++ \<sigma>"
      using hyps(9) hyps(1,2,3)
       sorry
    show ?case
      using hyps(5)[of n \<sigma>1 s] hyps(1,2,7-) hyps(6)[of n \<sigma>1 s, OF _ _ A]
      by (force intro!: has_type_L.intros)
next
  case (has_type_Case x \<Gamma> y t \<sigma>2 A B t1 C t2)
    note hyps=this
         
     have V_shifty:"y \<le> n\<Longrightarrow> (Suc n, S) |\<in>| insert_nth y B \<Gamma>"
       proof -
         assume H: "y\<le>n"
         have 1:"Suc n < length (insert_nth x A \<Gamma>)"
           using inversion(4)[OF hyps(9), simplified] hyps(1)
           by force
         from H have "(insert_nth y B \<Gamma>) ! (Suc n) = S"
           using nth_append[of "take y \<Gamma>" "drop y \<Gamma> |,| B" "Suc n", unfolded length_take,  simplified]
                 nth_Cons[of B "drop y \<Gamma>" "Suc n-y", simplified] inversion(4)[OF hyps(9), simplified]
                 hyps(1,2) nth_drop[of y "n-y" \<Gamma>]
           by (metis Suc_diff_le Suc_lessD append_Cons append_Nil2 append_eq_append_conv_if 
                     insert_nth_take_drop le_add_diff_inverse le_neq_implies_less less_imp_le_nat 
                     min_def not_add_less1 nth_Cons_Suc)
         with 1 show ?thesis by simp
       qed
     
     have V_shiftx:"x \<le> n\<Longrightarrow> (Suc n, S) |\<in>| insert_nth x A \<Gamma>"
       proof -
         assume H: "x \<le> n"
         have 1:"Suc n < length (insert_nth x A \<Gamma>)"
           using inversion(4)[OF hyps(9), simplified] hyps(1)
           by force
         from H have "(insert_nth x A \<Gamma>) ! (Suc n) = S"
           using nth_append[of "take x \<Gamma>" "drop x \<Gamma> |,| A" "Suc n", unfolded length_take,  simplified]
                 nth_Cons[of A "drop x \<Gamma>" "Suc n-x", simplified] inversion(4)[OF hyps(9), simplified]
                 hyps(1) nth_drop[of x "n-x" \<Gamma>]
           by (metis Suc_diff_le Suc_lessD append_Cons append_Nil2 append_eq_append_conv_if 
                     insert_nth_take_drop le_add_diff_inverse le_neq_implies_less less_imp_le_nat 
                     min_def not_add_less1 nth_Cons_Suc)
         with 1 show ?thesis by simp
       qed

     have Vx:"\<not>x \<le> n\<Longrightarrow> (n, S) |\<in>| insert_nth x A \<Gamma>"
       using not_less[of x n] nth_take[of n x \<Gamma>] nth_append[of "take x \<Gamma>" _ n, simplified]
             inversion(4)[OF hyps(9), simplified] hyps(1)
       by auto

     have Vy:"\<not>y \<le> n\<Longrightarrow> (n, S) |\<in>| insert_nth y B \<Gamma>"
       using not_less[of y n] nth_take[of n y \<Gamma>] nth_append[of "take y \<Gamma>" _ n, simplified]
             inversion(4)[OF hyps(9), simplified] hyps(1)
       by auto

     have B1:" x \<le> n \<Longrightarrow> y \<le> n \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Case subst_L n s t of Inl x \<Rightarrow> subst_L (Suc n) (shift_L 1 x s) t1 | Inr y \<Rightarrow>
                 subst_L (Suc n) (shift_L 1 y s) t2|;|\<sigma>2\<rparr> |:| C"
       using hyps(1-5)  hyps(6)[of n \<sigma>1 s] hyps(9-) V_shiftx
             hyps(7)[of "Suc n" \<sigma>1 "shift_L 1 x s", OF _ _ hyps(11)] 
             weakening[OF hyps(10) hyps(1)] has_type_LVar
             hyps(8)[of "Suc n" \<sigma>1 "shift_L 1 y s",OF _ _ hyps(11)] V_shifty
             weakening[OF hyps(10) hyps(2)] has_type_L.intros(4)
       by (blast intro!: has_type_L.intros(22))+
    
     have B2:" \<not>x \<le> n \<Longrightarrow> y \<le> n \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Case subst_L n s t of Inl x \<Rightarrow> subst_L  n (shift_L 1 x s) t1 | Inr y \<Rightarrow>
                 subst_L (Suc n) (shift_L 1 y s) t2|;|\<sigma>2\<rparr> |:| C"
       using hyps(1-5)  hyps(6)[of n \<sigma>1 s] hyps(9-) Vx
             hyps(7)[of "n" \<sigma>1 "shift_L 1 x s", OF _ _  hyps(11)] 
             weakening[OF hyps(10,1)] has_type_LVar
             hyps(8)[of "Suc n" \<sigma>1 "shift_L 1 y s",OF _ _ hyps(11)] V_shifty
            weakening[OF hyps(10,2)] has_type_L.intros(4)
       by (blast intro!: has_type_L.intros(22))+    
    
     have B3:" x \<le> n \<Longrightarrow> \<not>y \<le> n \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Case subst_L n s t of Inl x \<Rightarrow> subst_L (Suc n) (shift_L 1 x s) t1 | Inr y \<Rightarrow>
                 subst_L n (shift_L 1 y s) t2|;|\<sigma>2\<rparr> |:| C"
       using hyps(1-5)  hyps(6)[of n \<sigma>1 s] hyps(9-) V_shiftx
             hyps(7)[of "Suc n" \<sigma>1 "shift_L 1 x s", OF _ _ hyps(11)] 
             weakening[OF hyps(10,1)] has_type_LVar
             hyps(8)[of "n" \<sigma>1 "shift_L 1 y s",OF _ _ hyps(11)] Vy
             weakening[OF hyps(10,2)] has_type_L.intros(4)
       by (blast intro!: has_type_L.intros(22))+
     
     have " \<not>x \<le> n \<Longrightarrow> \<not>y \<le> n \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Case subst_L n s t of Inl x \<Rightarrow> subst_L  n (shift_L 1 x s) t1 | Inr y \<Rightarrow>
                 subst_L n (shift_L 1 y s) t2|;|\<sigma>2\<rparr> |:| C"
       using hyps(1-5)  hyps(6)[of n \<sigma>1 s] hyps(9-) Vx
             hyps(7)[of n \<sigma>1 "shift_L 1 x s", OF _ _ hyps(11)] 
             weakening[OF hyps(10,1)] has_type_LVar
             hyps(8)[of n \<sigma>1 "shift_L 1 y s",OF _ _ hyps(11)] Vy
             weakening[OF hyps(10,2)] has_type_L.intros(4)
       by (blast intro!: has_type_L.intros(22))+
    
     with B1 B2 B3 show ?case by simp
      
next
  case (has_type_CaseV L TL B \<Gamma> t \<sigma> A)
    note hyps=this

    have " \<forall>i<length L. insert_nth (fst (map (\<lambda>p. (fst p, subst_L (if fst p \<le> n then Suc n else n) 
           (shift_L 1 (fst p) s) (snd p))) B ! i)) (TL ! i) \<Gamma>
       \<turnstile> \<lparr>snd (map (\<lambda>p. (fst p, subst_L (if fst p \<le> n then Suc n else n) (shift_L 1 (fst p) s) (snd p)))
          B ! i)|;|\<sigma>\<rparr> |:| A"
      proof (rule+)
        fix i
        let ?goal = "insert_nth (fst (map (\<lambda>p. (fst p, subst_L (if fst p \<le> n then Suc n else n) 
           (shift_L 1 (fst p) s) (snd p))) B ! i)) (TL ! i) \<Gamma>
       \<turnstile> \<lparr>snd (map (\<lambda>p. (fst p, subst_L (if fst p \<le> n then Suc n else n) (shift_L 1 (fst p) s) (snd p)))
          B ! i)|;|\<sigma>\<rparr> |:| A"
        assume H1: "i<length L"
        have P:"\<And>n s \<sigma>1 fa. insert_nth (fst(B!i)) (TL ! i) \<Gamma> \<turnstile> \<lparr>LVar n|;|\<sigma>1\<rparr> |:| S \<Longrightarrow>
               insert_nth (fst(B!i)) (TL ! i) \<Gamma> \<turnstile> \<lparr>s|;|\<sigma>1\<rparr> |:| S \<Longrightarrow>  \<sigma>1 \<subseteq>\<^sub>f \<sigma> \<Longrightarrow>
               insert_nth (fst(B!i)) (TL ! i) \<Gamma> \<turnstile> \<lparr>subst_L n s (snd(B ! i))|;|\<sigma>\<rparr> |:| A"
               "fst(B!i) \<le> length \<Gamma>"
          using hyps(7) H1
          by blast+
        
         have "\<not>fst(B!i) \<le> n\<Longrightarrow> (n, S) |\<in>| insert_nth (fst(B!i)) (TL!i) \<Gamma>"
          proof -
            assume H: "\<not>fst(B!i) \<le> n"
            have 1:"n < length (insert_nth (fst(B!i)) (TL!i) \<Gamma>)"
              using inversion(4)[OF hyps(8), simplified] P(2)
              by force
            have "(insert_nth (fst(B!i)) (TL!i) \<Gamma>) ! n = S"
              proof -
                have "(insert_nth (fst(B!i)) (TL!i) \<Gamma>) !  n =  take (fst(B!i)) \<Gamma> ! n"
                  using nth_append[of "take (fst(B!i)) \<Gamma>" "drop (fst(B!i)) \<Gamma> |,| (TL!i)" n, unfolded length_take,  simplified]
                        not_less[of n "fst(B!i)"] P(2) H[unfolded not_le]
                  by (simp add: min.commute min_def)
                then show ?thesis
                  using inversion(4)[OF hyps(8), simplified]
                        H
                  by force
              qed
            with 1 show ?thesis by simp
          qed

        hence "\<not> n \<ge> fst(B!i) \<Longrightarrow> insert_nth (fst(B!i)) (TL ! i) \<Gamma> \<turnstile> \<lparr>subst_L n (shift_L 1 (fst(B!i)) s) (snd (B ! i))|;|\<sigma>\<rparr> |:| A" 
          using P(1)[of n \<sigma>1 , OF _ _ hyps(10)] inversion(4)[OF hyps(8), simplified] P(2)
                 weakening[OF hyps(9) P(2),of "TL!i"] has_type_LVar
          by blast

        moreover have "n\<ge>fst(B!i) \<Longrightarrow> insert_nth (fst(B!i)) (TL ! i) \<Gamma> \<turnstile> \<lparr>subst_L (Suc n) (shift_L 1 (fst(B!i)) s) (snd (B ! i))|;|\<sigma>\<rparr> |:| A"
          proof -
            assume H:"n \<ge> fst(B!i)"
            have V_shift:"fst(B!i) \<le> n\<Longrightarrow> (Suc n, S) |\<in>| insert_nth (fst(B!i)) (TL!i) \<Gamma>"
              proof -
                assume H: "fst(B!i) \<le> n"
                have 1:"Suc n < length (insert_nth (fst(B!i)) (TL!i) \<Gamma>)"
                  using inversion(4)[OF hyps(8), simplified] P(2)
                  by force
                have "(insert_nth (fst(B!i)) (TL!i) \<Gamma>) ! (Suc n) = S"
                  proof -
                    have "(insert_nth (fst(B!i)) (TL!i) \<Gamma>) ! (Suc n) =  (drop (fst(B!i)) \<Gamma> |,| (TL!i)) ! (Suc n - fst(B!i))"
                      using nth_append[of "take (fst(B!i)) \<Gamma>" "drop (fst(B!i)) \<Gamma> |,| (TL!i)" "Suc n", unfolded length_take,  simplified]
                            not_less[of "Suc n" "fst(B!i)"] P(2) H Suc_le_mono
                      by (simp add: min.commute min_def) 
                    moreover have "... = drop (fst(B!i)) \<Gamma> ! (n - fst(B!i))"
                      using nth_Cons[of "TL!i" "drop (fst(B!i)) \<Gamma>" "Suc n-(fst(B!i))", simplified] 
                            H Suc_le_mono
                      by force
                    ultimately show ?thesis
                      using nth_drop[of "fst(B!i)" "n-fst(B!i)" \<Gamma>] inversion(4)[OF hyps(8), simplified]
                            H
                      by force
                  qed
                with 1 show ?thesis by simp
              qed
         
            then show "insert_nth (fst(B!i)) (TL ! i) \<Gamma> \<turnstile> \<lparr>subst_L  (Suc n) (shift_L 1 (fst (B ! i)) s) (snd (B ! i))|;|\<sigma>\<rparr> |:| A"
              using P(1)[of "Suc n" \<sigma>1, OF _ _ hyps(10)]  weakening[OF hyps(9) P(2),of "TL!i"]
                    has_type_LVar H
              by blast
          qed

        ultimately show ?goal using hyps(4) H1 by force
      qed

    then show ?case using hyps by (force intro!: has_type_L.intros(24))      

next
  case (has_type_LVar x A \<Gamma> \<sigma> f)
    note hyps=this
    show ?case
      using hyps(1,2) inversion(4) weakening_pattern[OF hyps(3,4)]           
      by (force intro!: has_type_L.intros)
qed (auto intro!: has_type_L.intros dest: inversion(4))

method inv_eval = (match premises in H:"eval1_L t t1" for t and t1 \<Rightarrow>
                    \<open>insert eval1_L.simps[of t t1, simplified]\<close>)


(*lemma lmatch_coherent_char:
  "Lmatch_Type p \<sigma>1 \<Longrightarrow> coherent p B \<Longrightarrow> Lmatch p t1 (fill \<sigma>) \<Longrightarrow> is_value_L t1\<Longrightarrow>
    \<Gamma> \<turnstile> \<lparr>t1|;|\<sigma>2\<rparr> |:| B \<Longrightarrow>\<forall>x\<in>dom \<sigma>1. \<exists>B t' f1. \<sigma>1 x = Some B \<and> \<sigma> x = Some t' \<and> \<emptyset> \<turnstile> \<lparr>t'|;|\<sigma>21\<rparr> |:| B"
sorry*)

theorem Preservation:
  "\<Gamma> \<turnstile> \<lparr>t|;|\<sigma>\<rparr> |:| A \<Longrightarrow> eval1_L t t1 \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t1|;|\<sigma>\<rparr> |:| A"
proof (induction \<Gamma> t \<sigma> A arbitrary: t1 rule: has_type_L.induct)
  case (has_type_LApp \<Gamma> ta \<sigma> T11 T12 tb)
    note hyps=this(1-4) and inv=this(5)[unfolded eval1_L.simps[of "LApp _ _", simplified]]
    have " (\<exists>t1'. t1 = LApp t1' tb \<and> eval1_L ta t1') \<or> (\<exists>t2'. t1 = LApp ta t2' \<and> is_value_L ta \<and> eval1_L tb t2')
            \<Longrightarrow> ?case"
      using hyps
      by (force intro!:has_type_L.intros)

    moreover have "(\<exists>T' t12. ta = LAbs T' t12 \<and> t1 = shift_L (- 1) 0 (subst_L 0 (shift_L 1 0 tb) t12) \<and> is_value_L tb)
                   \<Longrightarrow> ?case"
      proof -
        assume "\<exists>T' t12. ta = LAbs T' t12 \<and> t1 = shift_L (- 1) 0 (subst_L 0 (shift_L 1 0 tb) t12) \<and> is_value_L tb"
        then obtain T' t12 where H:"ta = LAbs T' t12" "t1 = shift_L (- 1) 0 (subst_L 0 (shift_L 1 0 tb) t12)"
          by blast
        have "\<Gamma> |,| T11 \<turnstile> \<lparr>subst_L 0 (shift_L 1 0 tb) t12|;|\<sigma>\<rparr> |:| T12"
          using substitution[of "\<Gamma>|,|T11" _ \<sigma> T12 0 \<sigma> T11 "shift_L 1 0 tb", simplified]
                hyps(1)[unfolded H(1) has_type_L.simps[of _ "LAbs _ _", simplified]]
                has_type_L.intros(4)[of 0 T11 "\<Gamma>|,|T11", simplified]
                weakening[OF hyps(2),of 0 T11, simplified]
          by blast
        moreover have "\<And>x. x \<in> (if 0 \<in> FV t12 then FV t12 - {0} \<union> Suc ` FV tb else FV t12) \<Longrightarrow> 0 < x"
          by (cases "0\<in>FV t12") (fastforce, metis not_gr0) 
        ultimately show ?case
          using shift_down[of 0 T11 \<Gamma> "subst_L 0 (shift_L 1 0 tb) t12" \<sigma> T12, simplified] H(2)
                FV_subst FV_shift[of 1 0,simplified]
          by presburger
      qed

    ultimately show ?case using inv by blast

next
  case (has_type_Let x \<Gamma> ta \<sigma> A tb B)
    note hyps=this(1-5) and inv=this(6)[unfolded eval1_L.simps[of "LetBinder _ _ _", simplified]]
    have 1:"(x, A) |\<in>| insert_nth x A \<Gamma>"
      using nth_append[of "take x \<Gamma>" "drop x \<Gamma>|,|A" x, simplified] 
            hyps(1)
      by simp
    
      
    have "(\<And>xa. xa \<in> FV (subst_L x (shift_L 1 x ta) tb) \<Longrightarrow> xa \<noteq> x)"
      proof 
        fix x1
        assume H:"x1 \<in> FV (subst_L x (shift_L 1 x ta) tb)" "x1 = x"
        have "x1\<in>FV (shift_L (int 1) x ta) \<Longrightarrow> False"
          using FV_shift[of 1 x, unfolded image_def Bex_def]
          proof (simp)
            assume "\<exists>xa. xa \<in> FV ta \<and> x1 = (if x \<le> xa then xa + 1 else xa)"
            then obtain x2 where "x2 \<in> FV ta \<and> x1 = (if x \<le> x2 then x2 + 1 else x2)"
              by blast
            with H show False
              by (cases "x\<le>x2")fastforce+
          qed    
              
        then show False 
          using H(1) FV_subst[of x "shift_L 1 x ta" tb] image_def
          by (cases "x\<in>FV tb") (simp add: H(2))+
      qed

    hence "t1 =shift_L (- 1) x (subst_L x (shift_L 1 x ta) tb) \<and> is_value_L ta \<Longrightarrow> ?case"
      using substitution[OF hyps(3) has_type_LVar[OF 1] weakening[OF hyps(2,1), of A], simplified]  
            shift_down[of x A \<Gamma> "(subst_L x (shift_L 1 x ta) tb)" \<sigma> B, OF _ hyps(1)]
      by force      
     
    with inv show ?case using hyps(1,3,4) has_type_L.intros(10) by fast
next
  case (has_type_Tuple L TL \<Gamma> \<sigma>)
    note hyps=this(1-4) and inv= this(5)[unfolded eval1_L.simps[of "Tuple _",simplified]]
    from inv obtain j t' where H: "t1 = Tuple (replace (j-1) t' L)"
                                  "Suc 0 \<le> j" "j \<le> length L" "is_value_L (Tuple (take (j - Suc 0) L))" 
                                  "eval1_L (L ! (j - Suc 0)) t'"
      by auto
    have "\<And>i. \<not> length L \<le> j - Suc 0 \<Longrightarrow>
         0 \<le> i \<Longrightarrow>
         i < length (take (j - Suc 0) L @ t' # drop (Suc (j - Suc 0)) L) \<Longrightarrow>
         \<Gamma> \<turnstile> \<lparr>((take (j - Suc 0) L @ t' # drop (Suc (j - Suc 0)) L) ! i)|;|\<sigma>\<rparr> |:| (TL ! i)"
      proof -
        fix i
        assume Hi:"\<not> length L \<le> j - Suc 0" "0 \<le> i" "i < length (take (j - Suc 0) L @ t' # drop (Suc (j - Suc 0)) L)"
        show "\<Gamma> \<turnstile> \<lparr>((take (j - Suc 0) L @ t' # drop (Suc (j - Suc 0)) L) ! i)|;|\<sigma>\<rparr> |:| (TL ! i)"
          using hyps(4)[of "j-Suc 0", simplified] H(5) Hi(1)[unfolded not_le]
                nth_replace[of i L "j-Suc 0" t', simplified] Hi(1) hyps(3)[of i] Hi(2-3)
          by simp
      qed

    then show ?case
      using hyps(1-3) H(1)
      by (force intro!: has_type_L.intros)
      
next
  case (has_type_ProjT i TL \<Gamma> t \<sigma> f)
    note hyps=this and inv=this(5)[unfolded eval1_L.simps[of "\<Pi> _ _" _,simplified]] 
    show ?case
      using hyps inv 
      by (force intro!:has_type_L.intros(15)[of i, simplified] dest: inversion(14))
next
  next
  case (has_type_RCD L LT TL \<Gamma> \<sigma>)
    note hyps=this(1-6) and inv=this(7)[unfolded eval1_L.simps[of "Record _ _", simplified]]
    obtain m t' where H:"t1 = Record L (take m LT @ [t'] @ drop (Suc m) LT)"
                        "m < length LT" "eval1_L (LT ! m) t'"
      using inv
      by fastforce
    
    show ?case
      using hyps(1-4) H(1,2)
             hyps(5) nth_replace[of _  LT m t'] H(2)
            hyps(6)[OF H(2,3)]
      by (auto intro: has_type_L.intros)
next
  case (has_type_LetPattern p B \<sigma>1 \<Gamma> ta \<sigma>2 tb A)
    note hyps=this(1-6) and inv=this(7)[unfolded eval1_L.simps[of "Let pattern _ := _ in _", simplified]]
    have "\<forall>x\<in>dom \<sigma>1. \<exists>B. \<sigma>1 x = Some B" by blast
      
    have "(\<exists>\<sigma>. t1 = \<sigma> tb \<and> is_value_L ta \<and> Lmatch p ta \<sigma>) \<Longrightarrow>?case"
      using lmatch_is_fill[of p ta _]
           (* lmatch_coherent_char[OF hyps(2,1) _ _ hyps(3)]*)
      sorry (* need some lemma to describe substitution with patterns*)
   
    then show ?case using inv has_type_L.intros(19)[OF hyps(1,2,5,4)] by fast
next
  case (has_type_Case x \<Gamma> y t \<sigma>1 A B ta C tb)
    note hyps=this and inv = this(9)[unfolded eval1_L.simps[of "CaseSum _ _ _ _ _" ,simplified]]
    have "\<exists>v. (\<exists>A. t = inl v as A) \<and> t1 = shift_L (- 1) x (subst_L x (shift_L 1 x v) ta) \<and> is_value_L v \<Longrightarrow>
          ?case"
      proof -
        assume "\<exists>v. (\<exists>A. t = inl v as A) \<and> t1 = shift_L (- 1) x (subst_L x (shift_L 1 x v) ta) \<and> is_value_L v"
        then obtain v A1 where H:"t = inl v as A1" "t1 = shift_L (- 1) x (subst_L x (shift_L 1 x v) ta)"
          by blast

        have "\<And>xa. xa \<in> FV (subst_L x (shift_L 1 x v) ta) \<Longrightarrow> xa \<noteq> x"        
          proof 
            fix x1
            assume H1:"x1 \<in> FV (subst_L x (shift_L 1 x v) ta)" "x1 = x"
                        
            have "x1\<in>FV (shift_L (int 1) x v) \<Longrightarrow> False"
              using FV_shift[of 1 x v, unfolded image_def Bex_def]
              proof (simp)
                assume "\<exists>xa. xa \<in> FV v \<and> x1 = (if x \<le> xa then xa + 1 else xa)"
                then obtain x2 where "x2 \<in> FV v \<and> x1 = (if x \<le> x2 then x2 + 1 else x2)"
                  by blast
                with H1 show False
                  by (cases "x\<le>x2")fastforce+
              qed    
                  
            then show False 
              using H1(1) image_iff FV_subst[of x "shift_L 1 x v" ta]
              by (cases "x\<in>FV ta") (simp add: H1(2))+
          qed

        with H show ?case 
          using hyps(1) has_type_LVar[of x A "insert_nth x A \<Gamma>"] 
                nth_append[of "take x \<Gamma>" "drop x \<Gamma>|,|A" x, simplified]
                weakening[of \<Gamma> v \<sigma>1  A _ A,OF _ hyps(1)] 
                hyps(3)[unfolded H has_type_L.simps[of _ "inl _ as _", simplified]]
                substitution[OF hyps(4), of x \<sigma>1 , simplified] 
                shift_down[of x A \<Gamma> "(subst_L x (shift_L 1 x v) ta)", OF _ hyps(1)]
          by fastforce
      qed

    moreover have "\<exists>v. (\<exists>A. t = inr v as A) \<and> t1 = shift_L (- 1) y (subst_L y (shift_L 1 y v) tb) \<and> is_value_L v \<Longrightarrow>
          ?case"
      proof -
        assume "\<exists>v. (\<exists>A. t = inr v as A) \<and> t1 = shift_L (- 1) y (subst_L y (shift_L 1 y v) tb) \<and> is_value_L v"
        then obtain v A1 where H:"t = inr v as A1" "t1 = shift_L (- 1) y (subst_L y (shift_L 1 y v) tb)"
          by blast
        have "\<And>xa. xa \<in> FV (subst_L y (shift_L 1 y v) tb) \<Longrightarrow> xa \<noteq> y"        
          proof 
            fix x1
            assume H1:"x1 \<in> FV (subst_L y (shift_L 1 y v) tb)" "x1 = y"
             
            have "x1\<in>FV (shift_L (int 1) y v) \<Longrightarrow> False"
              using FV_shift[of 1 y v, unfolded image_def Bex_def]
              proof (simp)
                assume "\<exists>xa. xa \<in> FV v \<and> x1 = (if y \<le> xa then xa + 1 else xa)"
                then obtain x2 where "x2 \<in> FV v \<and> x1 = (if y \<le> x2 then x2 + 1 else x2)"
                  by blast
                with H1 show False
                  by (cases "y\<le>x2")fastforce+
              qed    
                  
            then show False 
              using H1(1) FV_subst[of y "shift_L 1 y v" tb] image_iff
              by (cases "y\<in>FV tb") (simp add: H1(2))+
          qed
        with H show ?case 
          using hyps(2) has_type_LVar[of y B "insert_nth y B \<Gamma>"] 
                nth_append[of "take y \<Gamma>" "drop y \<Gamma>|,|B" y, simplified]
                weakening[of \<Gamma> v \<sigma>1 B _ B,OF _ hyps(2)] 
                hyps(3)[unfolded H has_type_L.simps[of _ "inr _ as _", simplified]]
                substitution[OF hyps(5), of y \<sigma>1, simplified] 
                shift_down[of y B \<Gamma> "(subst_L y (shift_L 1 y v) tb)", OF _ hyps(2)]
          by fastforce
      qed

    ultimately show ?case using inv has_type_L.intros(22)[OF hyps(1,2,6,4,5)] by fast
      
next
  case (has_type_CaseV L TL B \<Gamma> t \<sigma> A)
    note hyps=this and inv=this(8)[unfolded eval1_L.simps[of "CaseVar _ _ _ ", simplified]]
    have P:" \<forall>i<length L. fst(B!i) \<le> length \<Gamma> \<and> insert_nth (fst(B!i)) (TL ! i) \<Gamma> \<turnstile> \<lparr>snd (B ! i)|;|\<sigma>\<rparr> |:| A" 
      using hyps(7)
      by blast
    have "\<exists>v i. (\<exists>A. t = <L ! i:=v> as A) \<and>
           t1 = shift_L (- 1) (fst(B!i))
                 (subst_L (fst(B!i)) (shift_L 1 (fst(B!i)) v) (snd(B!i))) \<and> i < length L
          \<Longrightarrow> ?case"
      proof -
        assume "\<exists>v i. (\<exists>A. t = <L ! i:=v> as A) \<and> t1 = shift_L (- 1) (fst(B!i))
                 (subst_L (fst(B!i)) (shift_L 1 (fst(B!i)) v) (snd(B!i))) \<and> i < length L"
        then obtain v i A1 where H:"i<length L" "t = <L!i:=v> as A1"
                                    "t1 = shift_L (- 1) (fst(B!i)) (subst_L (fst(B!i)) 
                                          (shift_L 1 (fst(B!i)) v) (snd(B!i)))"
          by blast
        have "\<And>xa. xa \<in> FV (subst_L (fst(B!i)) (shift_L 1 (fst(B!i)) v) (snd(B!i))) \<Longrightarrow> xa \<noteq> (fst(B!i))"        
          proof 
            fix x1
            assume H1:"x1 \<in> FV (subst_L (fst(B!i)) (shift_L 1 (fst(B!i)) v) (snd(B!i)))" "x1 = fst(B!i)"
 
            have "x1\<in>FV (shift_L (int 1) (fst(B!i)) v) \<Longrightarrow> False"
              using FV_shift[of 1 "fst(B!i)" v, unfolded image_def Bex_def]
              proof (simp)
                assume "\<exists>xa. xa \<in> FV v \<and> x1 = (if fst(B!i) \<le> xa then xa + 1 else xa)"
                then obtain x2 where "x2 \<in> FV v \<and> x1 = (if fst(B!i) \<le> x2 then x2 + 1 else x2)"
                  by blast
                with H1 show False
                  by (cases "fst(B!i)\<le>x2")fastforce+
              qed    
                  
            then show False 
              using H1(1) FV_subst[of "fst(B!i)" "shift_L 1 (fst(B!i)) v" "snd(B!i)"] image_iff
              by (cases "(fst(B!i))\<in>FV (snd(B!i))") (simp add: H1(2))+
          qed
        moreover have "\<Gamma> \<turnstile> \<lparr>v|;|\<sigma>\<rparr> |:| (TL ! i)"
          using hyps(5)[unfolded H has_type_L.simps[of _ "<_:= _> as _", simplified]]
                hyps(2) distinct_conv_nth
                H(1) ltype.inject(7)
          by blast
        ultimately show ?case 
          using P has_type_LVar[of "fst(B!i)" "TL!i" "insert_nth (fst(B!i)) (TL!i) \<Gamma>"] H
                nth_append[of "take (fst(B!i)) \<Gamma>" "drop (fst(B!i)) \<Gamma>|,|(TL!i)" "fst(B!i)", simplified]
                weakening[of \<Gamma> v \<sigma> "TL!i" "fst(B!i)" "TL!i"] 
                substitution[of "insert_nth (fst(B!i)) (TL!i) \<Gamma>" "snd(B!i)" \<sigma>] 
                shift_down[of "fst(B!i)" "TL!i" \<Gamma> "(subst_L (fst(B!i)) (shift_L 1 (fst(B!i)) v) (snd(B!i)))"]
          by fastforce
      qed
    with inv show ?case using has_type_L.intros(24)[OF hyps(1-4,6)] hyps(7) by blast
next
  case (has_type_Fix \<Gamma> t \<sigma> A t1)
    note hyps=this(1,2) and inv=this(3)[unfolded eval1_L.simps[of "fix t" t1, simplified]]
    have 1:"\<And>x t. \<Gamma>|,|A \<turnstile> \<lparr>t|;|\<sigma>\<rparr> |:| A \<Longrightarrow> x \<in> FV (subst_L 0 (fix LAbs A (shift_L 1 (Suc 0) t)) t) \<Longrightarrow> x \<noteq> 0"
      proof 
        fix x t1'
        assume A:"x \<in> FV (subst_L 0 (fix LAbs A (shift_L 1 (Suc 0) t1')) t1')" "x=0" "\<Gamma>|,|A \<turnstile> \<lparr>t1'|;|\<sigma>\<rparr> |:| A"
        show "False"           
          using A(1)[unfolded A(2)] FV_subst[of 0 "fix LAbs A (shift_L 1 (Suc 0) t1')" t1',unfolded FV.simps(25)] 
                FV.simps(5)[of A "shift_L 1 (Suc 0) t1'"] image_def FV_shift[of "Suc 0" 1 t1', simplified]
          by (cases "0\<in>FV t1'") fastforce+
      qed
    
    have "\<exists>A t'. t = LAbs A t' \<and> t1 = shift_L (- 1) 0 (subst_L 0 (fix LAbs A (shift_L 1 (Suc 0) t')) t')
          \<Longrightarrow> ?case"
      proof -
        assume "\<exists>A t'. t = LAbs A t' \<and> t1 = shift_L (- 1) 0 (subst_L 0 (fix LAbs A (shift_L 1 (Suc 0) t')) t')"
      
        then obtain A' t' where H:"t = LAbs A' t' \<and> t1 = shift_L (- 1) 0 (subst_L 0 (fix LAbs A' (shift_L 1 (Suc 0) t')) t')"
          by blast
        have 2:"\<Gamma> |,| A \<turnstile> \<lparr>fix LAbs A (shift_L 1 (Suc 0) t')|;|\<sigma>\<rparr> |:| A"
          using has_type_L.intros(25)[of "\<Gamma>|,|A" "LAbs A (shift_L 1 (Suc 0) t')" \<sigma> A]
                has_type_L.intros(5)[OF weakening[of "\<Gamma>|,|A" t' \<sigma> A "Suc 0" A, simplified]]
                inversion(5) hyps(1)[unfolded H[THEN conjunct1]] 
          by blast
     

        have "insert_nth 0 A \<Gamma> \<turnstile> \<lparr>subst_L 0 (fix LAbs A (shift_L 1 (Suc 0) t')) t'|;|\<sigma>\<rparr> |:| A"
          using inversion(5)[OF hyps(1)[unfolded H[THEN conjunct1]], simplified]
                substitution[OF _ _ 2,of t' \<sigma> A 0,simplified]
                has_type_LVar[of 0 A "\<Gamma>|,|A" \<sigma> , simplified]
          by fastforce
        
        with 1 show ?case
          using shift_down[of 0 A \<Gamma> "subst_L 0 (fix LAbs A (shift_L 1 (Suc 0) t')) t'" \<sigma> A]
                H[THEN conjunct2] inversion(5)[OF hyps(1)[unfolded H[THEN conjunct1]], simplified]
          by fast
      qed
    then show ?case using inv hyps(2) has_type_L.intros(25) by blast      
qed (inv_eval, force intro!: "has_type_L.intros" dest: inversion(11,12,14,16))+

end
