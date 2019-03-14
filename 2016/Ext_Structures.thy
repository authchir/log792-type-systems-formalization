(*<*)
theory Ext_Structures
imports
   Main
   List_extra
   Lambda_calculus
  "HOL.List"
  "HOL-Eisbach.Eisbach"
  "HOL-Eisbach.Eisbach_Tools"
  "List-Index.List_Index"
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
  \<comment> \<open>Rules relating to the evaluation of Booleans\<close>
  eval1_LIf_LTrue:
    "eval1_L (LIf LTrue t2 t3) t2" |
  eval1_LIf_LFalse:
    "eval1_L (LIf LFalse t2 t3) t3" |
  eval1_LIf:
    "eval1_L t1 t1' \<Longrightarrow> eval1_L (LIf t1 t2 t3) (LIf t1' t2 t3)" |

  \<comment> \<open>Rules relating to the evaluation of function application\<close>
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
  
  \<comment> \<open>Rules relating to evaluation of ascription\<close>
  eval1_L_Ascribe:
    "is_value_L v \<Longrightarrow> eval1_L (v as A) v" |
  eval1_L_Ascribe1:
    "eval1_L t1 t1' \<Longrightarrow> eval1_L (t1 as A) (t1' as A)" |

  \<comment> \<open>Rules relating to evaluation of letbinder\<close>
  eval1_L_LetV:
    "is_value_L v1 \<Longrightarrow> eval1_L (Let v1 in t2) (shift_L (-1) 0 (subst_L 0 (shift_L 1 0 v1) t2))" |
  eval1_L_Let:
    "eval1_L t1 t1' \<Longrightarrow> eval1_L (Let t1 in t2) (Let t1' in t2)" |

  \<comment> \<open>Rules relating to evaluation of pairs\<close>
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

  \<comment> \<open>Rules relating to evaluation of tuples\<close>
  eval1_L_ProjTuple:
    "1\<le>i \<Longrightarrow> i\<le>length L \<Longrightarrow> is_value_L (Tuple L) \<Longrightarrow> eval1_L (\<Pi> i (Tuple L)) (L ! (i-1))" |
  eval1_L_Proj:
    "eval1_L t1 t1' \<Longrightarrow> eval1_L (\<Pi> i t1) (\<Pi> i t1')" |
  eval1_L_Tuple:
    " 1\<le>j\<Longrightarrow> j\<le>length L \<Longrightarrow> is_value_L (Tuple (take (j-1) L)) \<Longrightarrow> 
      eval1_L (L ! (j-1)) (t') \<Longrightarrow> eval1_L (Tuple L) (Tuple (replace (j-1) t' L))" |

  \<comment> \<open>Rules relating to evaluation of records\<close>
  eval1_L_ProjRCD:
    "l \<in> set L \<Longrightarrow> is_value_L (Record L LT) \<Longrightarrow> eval1_L (ProjR l (Record L LT)) (LT ! (index L l))" |
  eval1_L_ProjR:
    "eval1_L t1 t1' \<Longrightarrow> eval1_L (ProjR i t1) (ProjR i t1')" |
  eval1_L_RCD:
    " m<length LT \<Longrightarrow> is_value_L (Record (take m L) (take m LT)) \<Longrightarrow> 
      eval1_L (LT ! m) (t') \<Longrightarrow> eval1_L (Record L LT) (Record L (replace m t' LT))" |   

  \<comment> \<open>Rules relating to evaluation of pattern matching\<close>
  eval1_L_LetPV:
    "is_value_L v1 \<Longrightarrow> Lmatch p v1 \<sigma> \<Longrightarrow> eval1_L (Let pattern p := v1 in t2) (\<sigma> t2)" |
  eval1_L_LetP:
    "eval1_L t1 t1' \<Longrightarrow> eval1_L (Let pattern p := t1 in t2) (Let pattern p := t1' in t2)" |

  \<comment> \<open>Rules relating to evaluation of Sums\<close>
  eval1_L_CaseInl:
    "is_value_L v \<Longrightarrow> eval1_L (CaseSum (inl v as A) t1 t2) (shift_L (-1) 0 (subst_L 0 (shift_L 1 0 v) t1))" |
  eval1_L_CaseInr:
    "is_value_L v \<Longrightarrow> eval1_L (CaseSum (inr v as A) t1 t2) (shift_L (-1) 0 (subst_L 0 (shift_L 1 0 v) t2))" |
  eval1_L_CaseS:
    "eval1_L t t' \<Longrightarrow> eval1_L (CaseSum t t1 t2) (CaseSum t' t1 t2)" |
  eval1_L_Inl:
    "eval1_L t t' \<Longrightarrow> eval1_L (inl t as A) (inl t' as A)" |
  eval1_L_Inr:
    "eval1_L t t' \<Longrightarrow> eval1_L (inr t as A) (inr t' as A)" |
  eval1_L_CaseVar:
    "is_value_L v \<Longrightarrow> i<length L \<Longrightarrow> eval1_L (CaseVar (<L!i:=v> as A) L B) (shift_L (-1) 0 (subst_L 0 (shift_L 1 0 v) (B!i)))" |
  eval1_L_CaseV:
    "eval1_L t t' \<Longrightarrow> eval1_L (CaseVar t L B) (CaseVar t' L B)" |
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
  \<comment> \<open>Rules relating to the type of Booleans\<close>
  has_type_LTrue:
    "\<Gamma> \<turnstile> \<lparr>LTrue|;| \<sigma>\<rparr> |:| Bool" |
  has_type_LFalse:
    "\<Gamma> \<turnstile> \<lparr>LFalse|;| \<sigma>\<rparr> |:| Bool" |
  has_type_LIf:
    "\<Gamma> \<turnstile> \<lparr>t1|;| \<sigma>\<rparr> |:| Bool \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t2|;| \<sigma>\<rparr> |:| T' \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t3|;| \<sigma>\<rparr> |:| T' \<Longrightarrow> 
      \<Gamma> \<turnstile> \<lparr>LIf t1 t2 t3|;| \<sigma>\<rparr> |:| T'" |

  \<comment> \<open>Rules relating to the type of the constructs of the $\lambda$-calculus\<close>
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
    " \<Gamma> \<turnstile> \<lparr>t1|;| \<sigma>\<rparr> |:| A \<Longrightarrow> (\<Gamma>|,|A) \<turnstile> \<lparr> t2|;| \<sigma>\<rparr> |:| B \<Longrightarrow> 
      \<Gamma> \<turnstile> \<lparr>Let t1 in t2|;| \<sigma>\<rparr> |:| B" |
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
    "\<Gamma> \<turnstile> \<lparr> t|;| \<sigma>1 \<rparr> |:| A|+|B \<Longrightarrow> (\<Gamma>|,|A) \<turnstile> \<lparr>t1|;| \<sigma>1\<rparr> |:| C \<Longrightarrow>
     (\<Gamma>|,|B) \<turnstile> \<lparr>t2|;| \<sigma>1\<rparr> |:| C \<Longrightarrow> 
     \<Gamma> \<turnstile> \<lparr>CaseSum t t1 t2 |;| \<sigma>1\<rparr> |:| C" |
  has_type_Variant:
    "i<length L \<Longrightarrow>distinct L \<Longrightarrow> length L=length TL \<Longrightarrow> \<Gamma> \<turnstile> \<lparr> t |;| \<sigma> \<rparr> |:| (TL!i) \<Longrightarrow> 
      \<Gamma> \<turnstile> \<lparr> <(L!i):=t> as <L|,|TL> |;|\<sigma> \<rparr> |:| <L|,|TL>" |
  has_type_CaseV:
    " L\<noteq>\<emptyset> \<Longrightarrow> distinct L \<Longrightarrow> length L = length TL \<Longrightarrow> 
      length L = length B \<Longrightarrow> 
      \<Gamma> \<turnstile> \<lparr> t |;| \<sigma> \<rparr> |:| <L|,|TL> \<Longrightarrow> 
      (\<forall>i<length L. (\<Gamma>|,| (TL!i)) \<turnstile> \<lparr>(B!i)|;| \<sigma>\<rparr> |:| A) \<Longrightarrow>
      \<Gamma> \<turnstile> \<lparr> CaseVar t L B |;| \<sigma>\<rparr> |:| A" |
  has_type_Fix:
    "\<Gamma> \<turnstile> \<lparr> t |;| \<sigma>\<rparr> |:| A\<rightarrow>A \<Longrightarrow> \<Gamma> \<turnstile> \<lparr> fix t |;| \<sigma>\<rparr> |:| A"

inductive_cases has_type_LetE : "\<Gamma> \<turnstile> \<lparr> Let t1 in t2|;|\<sigma>\<rparr>  |:| B"
inductive_cases has_type_ProjTE: "\<Gamma> \<turnstile> \<lparr> \<Pi> i t|;|\<sigma>1\<rparr> |:| R"
inductive_cases has_type_ProjRE: "\<Gamma> \<turnstile> \<lparr> ProjR l t|;|\<sigma>1\<rparr> |:| R"
inductive_cases has_type_LetPE: "\<Gamma> \<turnstile> \<lparr>Let pattern p := t1 in t2|;|\<sigma>1\<rparr> |:| A"
inductive_cases has_type_CaseSE: "\<Gamma> \<turnstile> \<lparr>CaseSum t t1 t2|;|\<sigma>1\<rparr> |:| R"
inductive_cases has_type_CaseVE: "\<Gamma> \<turnstile> \<lparr>CaseVar t L B |;|\<sigma>1\<rparr> |:| R"
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
  "\<Gamma> \<turnstile> \<lparr> Let t in t1 |;| \<sigma>\<rparr> |:| R \<Longrightarrow> \<exists>A B. R = B \<and> \<Gamma> \<turnstile> \<lparr> t|;| \<sigma>\<rparr> |:| A \<and> (\<Gamma>|,|A) \<turnstile> \<lparr>t1|;| \<sigma>\<rparr> |:| B"
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
  "\<Gamma> \<turnstile> \<lparr>CaseSum t t1 t2|;|\<sigma>1\<rparr> |:| R \<Longrightarrow>\<exists>A B C. R = C \<and> \<Gamma> \<turnstile> \<lparr>t|;|\<sigma>1\<rparr> |:| A|+|B \<and> (\<Gamma>|,|A) \<turnstile> \<lparr>t1|;|\<sigma>1\<rparr> |:| C \<and>
                                        (\<Gamma>|,|B) \<turnstile> \<lparr>t2|;|\<sigma>1\<rparr> |:| C"
   "\<Gamma> \<turnstile> \<lparr> <l:=t> as R1 |;| \<sigma>1 \<rparr> |:| R \<Longrightarrow>R=R1 \<and> (\<exists>L TL i. R=<L|,|TL> \<and> \<Gamma> \<turnstile> \<lparr> t |;| \<sigma>1 \<rparr> |:| (TL!i) \<and> l = L!i \<and> i<length L \<and> length L = length TL \<and> distinct L)" 
    " \<Gamma> \<turnstile> \<lparr> CaseVar t L1 B |;| \<sigma>1\<rparr> |:| A \<Longrightarrow>\<exists>TL. L1\<noteq>\<emptyset> \<and> length B = length L1 \<and> length L1 = length TL \<and> 
                                        distinct L1 \<and> \<Gamma> \<turnstile> \<lparr> t |;| \<sigma>1 \<rparr> |:| <L1|,|TL> \<and> 
                                        (\<forall>i<length L1. (\<Gamma>|,|(TL!i)) \<turnstile> \<lparr>(B!i)|;| \<sigma>1\<rparr> |:| A)"
   "\<Gamma> \<turnstile> \<lparr> fix t |;| \<sigma>\<rparr> |:| A \<Longrightarrow> \<Gamma> \<turnstile> \<lparr> t |;| \<sigma>\<rparr> |:| A\<rightarrow>A"
proof -
  assume H:"\<Gamma> \<turnstile> \<lparr> Let t in t1|;|\<sigma>\<rparr> |:| R"
  show " \<exists>A B. R = B \<and> \<Gamma> \<turnstile> \<lparr> t|;| \<sigma>\<rparr> |:| A \<and> (\<Gamma>|,|A) \<turnstile> \<lparr>t1|;| \<sigma>\<rparr> |:| B"
    using has_type_LetE[OF H] 
    by fastforce 
next
  assume H1: "\<Gamma> \<turnstile> \<lparr>Let pattern p := t1 in t2|;|\<sigma>1\<rparr> |:| R"
  show "\<exists>\<sigma> B. coherent p B \<and> Lmatch_Type p \<sigma>  \<and>  \<Gamma> \<turnstile> \<lparr>t1|;|\<sigma>1\<rparr> |:| B \<and>  \<Gamma> \<turnstile> \<lparr>t2|;|(\<sigma>1 ++ \<sigma>)\<rparr> |:| R"
    using has_type_LetPE[OF H1]
    by metis
next
  assume H2: "\<Gamma> \<turnstile> \<lparr>CaseSum t t1 t2|;|\<sigma>1\<rparr> |:| R"
  show "\<exists>A B C. R = C \<and> \<Gamma> \<turnstile> \<lparr>t|;|\<sigma>1\<rparr> |:| A |+| B \<and> (\<Gamma>|,|A) \<turnstile> \<lparr>t1|;|\<sigma>1\<rparr> |:| C \<and> (\<Gamma>|,|B) \<turnstile> \<lparr>t2|;|\<sigma>1\<rparr> |:| C"
    using has_type_CaseSE[OF H2]
    by fastforce
next
  assume H4: "\<Gamma> \<turnstile> \<lparr><l:=t> as R1|;|\<sigma>1\<rparr> |:| R"
  show  "R=R1 \<and> (\<exists>L TL i. R = <L|,|TL> \<and> \<Gamma> \<turnstile> \<lparr>t|;|\<sigma>1\<rparr> |:| (TL ! i) \<and> l = L ! i \<and> i<length L \<and> length L = length TL \<and> distinct L)"
    using has_type_VariantE[OF H4]
    by metis    
next
  assume H5: "\<Gamma> \<turnstile> \<lparr>CaseVar t L1 B|;|\<sigma>1\<rparr> |:| A"
  show "\<exists>TL. L1\<noteq>\<emptyset> \<and> length B = length L1 \<and> length L1 = length TL  \<and> distinct L1 \<and>
      \<Gamma> \<turnstile> \<lparr> t |;| \<sigma>1 \<rparr> |:| <L1|,|TL> \<and> (\<forall>i<length L1. (\<Gamma>|,| (TL!i)) \<turnstile> \<lparr>(B!i)|;| \<sigma>1\<rparr> |:| A)"
    using has_type_CaseVE[OF H5]  
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
        case (RCD x1 x2)
        then show ?case by simp
      qed
qed (auto intro: snds.intros)

lemma Binder_FV_shift:
  fixes c d::nat and t1 t2::lterm
  assumes  "(\<And>c1. FV (shift_L (int d) c1 t1) = (\<lambda>x. if c1 \<le> x then x + d else x) ` FV t1)"
              "(\<And>c1. FV (shift_L (int d) c1 t2) = (\<lambda>x. if c1 \<le> x then x + d else x) ` FV t2)"
  shows "(\<lambda>y. y - Suc 0) ` (FV (shift_L (int d) (Suc c) t2) - {0}) \<union> FV (shift_L (int d) c t1) =
          (\<lambda>x. x + d) ` (((\<lambda>y. y - Suc 0) ` (FV t2 - {0}) \<union> FV t1) \<inter> {x. c \<le> x}) \<union>
          ((\<lambda>y. y - Suc 0) ` (FV t2 - {0}) \<union> FV t1) \<inter> {x. \<not> c \<le> x}"
by (force simp add: assms image_iff)

lemma UN_Suc:
  "(\<Union>x<Suc n. P x) = (\<Union>x<n. P (Suc x)) \<union> P 0"
proof (rule;rule)
  fix x
  assume "x\<in> (\<Union>x<Suc n. P x)"
  then obtain xa where "xa\<in>{..<Suc n}" "x \<in> P xa"
    by blast
  then show "x\<in> (\<Union>x<n. P (Suc x)) \<union> P 0"
    using lessThan_Suc_eq_insert_0
    by (cases "xa=0") auto
qed blast

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
    case (LetBinder t1 t2)
    note hyps=this

    from Binder_FV_shift[OF hyps] show ?case by simp

next
  case (CaseSum t t1 t2)
    note hyps = this(1-3) 

    let ?P1 ="(\<lambda>x. x + d) ` (((\<lambda>y. y - Suc 0) ` (FV t1 - {0}) \<union> (\<lambda>z. z - Suc 0) ` (FV t2 - {0}) \<union> FV t) \<inter> {x. c \<le> x}) \<union>
              ((\<lambda>y. y - Suc 0) ` (FV t1 - {0}) \<union> (\<lambda>z. z - Suc 0) ` (FV t2 - {0}) \<union> FV t) \<inter> {x. \<not> c \<le> x}" and
        ?P2 = "((\<lambda>x. x + d) ` (((\<lambda>y. y - Suc 0) ` (FV t1 - {0}) \<union> FV t) \<inter> {x. c \<le> x}) \<union>
                ((\<lambda>y. y - Suc 0) ` (FV t1 - {0}) \<union> FV t) \<inter> {x. \<not> c \<le> x}) \<union> 
               ((\<lambda>x. x + d) ` (((\<lambda>y. y - Suc 0) ` (FV t2 - {0}) \<union> FV t) \<inter> {x. c \<le> x}) \<union>
                ((\<lambda>y. y - Suc 0) ` (FV t2 - {0}) \<union> FV t) \<inter> {x. \<not> c \<le> x})" 

    have A:"?P1 = ?P2" by blast
    
    have f3: "(\<lambda>n. n - Suc 0) ` (FV (shift_L (int d) (Suc c) t1) - {0}) \<union> (\<lambda>n. n - Suc 0) ` (FV (shift_L (int d) (Suc c) t2) - {0}) \<union> FV (shift_L (int d) c t) = (\<lambda>n. n - Suc 0) ` (FV (shift_L (int d) (Suc c) t2) - {0}) \<union> ((\<lambda>n. n - Suc 0) ` (FV (shift_L (int d) (Suc c) t1) - {0}) \<union> FV (shift_L (int d) c t))"
          by blast
    have "(\<lambda>n. n - Suc 0) ` (FV (shift_L (int d) (Suc c) t1) - {0}) \<union> FV (shift_L (int d) c t) = (\<lambda>n. n + d) ` (((\<lambda>n. n - Suc 0) ` (FV t1 - {0}) \<union> FV t) \<inter> Collect ((\<le>) c)) \<union> ((\<lambda>n. n - Suc 0) ` (FV t1 - {0}) \<union> FV t) \<inter> {n. \<not> c \<le> n} \<union> FV (shift_L (int d) c t)"
      using Binder_FV_shift[OF hyps(1,2), of c]  by auto
    then have "(\<lambda>n. n - Suc 0) ` (FV (shift_L (int d) (Suc c) t1) - {0}) \<union> (\<lambda>n. n - Suc 0) ` (FV (shift_L (int d) (Suc c) t2) - {0}) \<union> FV (shift_L (int d) c t) = (\<lambda>n. n + d) ` (((\<lambda>n. n - Suc 0) ` (FV t1 - {0}) \<union> FV t) \<inter> Collect ((\<le>) c)) \<union> ((\<lambda>n. n - Suc 0) ` (FV t1 - {0}) \<union> FV t) \<inter> {n. \<not> c \<le> n} \<union> ((\<lambda>n. n - Suc 0) ` (FV (shift_L (int d) (Suc c) t2) - {0}) \<union> FV (shift_L (int d) c t))"
      using f3 by auto

    then show "?case" using Binder_FV_shift[OF hyps(1,3),of c] A by simp

next
  case (CaseVar t L B)
    note hyps=this 
    have H: "\<And>i c. i<length B \<Longrightarrow> (\<lambda>y. y - Suc 0) ` (FV (shift_L (int d) (Suc c) (B!i)) - {0}) \<union> FV (shift_L (int d) c t) =
            (\<lambda>x. x + d) ` (((\<lambda>y. y - Suc 0) ` (FV (B!i) - {0}) \<union> FV t) \<inter> {x. c \<le> x}) \<union> 
            ((\<lambda>y. y - Suc 0) ` (FV (B!i) - {0}) \<union> FV t) \<inter> {x. \<not> c \<le> x}"
      using Binder_FV_shift[OF hyps, of "B!_"] in_set_conv_nth[of "B!_" B]
      proof -
        fix i :: nat and cb :: nat
        assume "i < length B"
        then show "(\<lambda>n. n - Suc 0) ` (FV (shift_L (int d) (Suc cb) (B ! i)) - {0}) \<union> FV (shift_L (int d) cb t) = (\<lambda>n. n + d) ` (((\<lambda>n. n - Suc 0) ` (FV (B ! i) - {0}) \<union> FV t) \<inter> {n. cb \<le> n}) \<union> ((\<lambda>n. n - Suc 0) ` (FV (B ! i) - {0}) \<union> FV t) \<inter> {n. \<not> cb \<le> n}"
          by (simp add: \<open>\<And>uu c. (\<And>c1. B ! uu \<in> set B) \<Longrightarrow> (\<lambda>y. y - Suc 0) ` (FV (shift_L (int d) (Suc c) (B ! uu)) - {0}) \<union> FV (shift_L (int d) c t) = (\<lambda>x. x + d) ` (((\<lambda>y. y - Suc 0) ` (FV (B ! uu) - {0}) \<union> FV t) \<inter> {x. c \<le> x}) \<union> ((\<lambda>y. y - Suc 0) ` (FV (B ! uu) - {0}) \<union> FV t) \<inter> {x. \<not> c \<le> x}\<close>)
      qed
      show ?case
      using H[of _ c]
      proof (simp,induction "length B" arbitrary: B)
        case 0
        then show ?case using hyps by simp
      next
        case (Suc n B1)
          then obtain a B' where H2:"B1=a#B'" "B1!0=a" "n = length B'"
            using Suc_length_conv  nth_Cons_0
            by metis
          have H3:"((\<lambda>x. x + d) ` ((FV t \<union> (\<Union>x<length B'. (\<lambda>y. y - Suc 0) ` (FV (B' ! x) - {0}))) \<inter> Collect ((\<le>) c)) \<union>
              (FV t \<union> (\<Union>x<length B'. (\<lambda>y. y - Suc 0) ` (FV (B' ! x) - {0}))) \<inter> {x. \<not> c \<le> x}) \<union>
              ((\<lambda>x. x + d) ` (((\<lambda>y. y - Suc 0) ` (FV a - {0}) \<union> FV t) \<inter> Collect ((\<le>) c)) \<union>
              ((\<lambda>y. y - Suc 0) ` (FV a - {0}) \<union> FV t) \<inter> {x. \<not> c \<le> x}) = 
               (\<lambda>x. x + d) ` ((FV t \<union> ((\<Union>x<length B'. (\<lambda>y. y - Suc 0) ` (FV (B' ! x) - {0})) \<union> 
               (\<lambda>y. y - Suc 0) ` (FV a - {0}))) \<inter> Collect ((\<le>) c)) \<union>
               (FV t \<union> ((\<Union>x<length B'. (\<lambda>y. y - Suc 0) ` (FV (B' ! x) - {0})) \<union>
               (\<lambda>y. y - Suc 0) ` (FV a - {0}))) \<inter> {x. \<not> c \<le> x}"
           by fast

         note simp1 =  UN_Suc[where n=n and P="(\<lambda>x. (\<lambda>y. y - Suc 0) ` FV (shift_L (int d) (Suc c) (B1 ! x)) - {0})",
                          unfolded H2 nth_Cons_0 nth_Cons'[of a B' "Suc _", simplified if_False nat.distinct diff_Suc_1]]
          and simp2=  UN_Suc[where n=n and P="\<lambda>x. (\<lambda>y. y - Suc 0) ` (FV (B1 ! x) - {0})", 
                          unfolded H2 nth_Cons_0 nth_Cons'[of a B' "Suc _", simplified if_False nat.distinct diff_Suc_1]]

          show "FV (shift_L (int d) c t) \<union> (\<Union>x<length B1. (\<lambda>y. y - Suc 0) ` (FV (shift_L (int d) (Suc c) (B1 ! x)) - {0})) =
               (\<lambda>x. x + d) ` ((FV t \<union> (\<Union>x<length B1. (\<lambda>y. y - Suc 0) ` (FV (B1 ! x) - {0}))) \<inter> Collect ((\<le>) c)) \<union>
           (FV t \<union> (\<Union>x<length B1. (\<lambda>y. y - Suc 0) ` (FV (B1 ! x) - {0}))) \<inter> {x. \<not> c \<le> x} " (is ?P)
          proof (simp add: H2(1) simp1 simp2  Un_assoc)
            have f3: "FV (shift_L (int d) c t) \<union> ((\<Union>n<length B'. (\<lambda>n. n - Suc 0) ` (FV (shift_L (int d) (Suc c) (B' ! n)) - {0})) \<union> ((\<lambda>n. n - Suc 0) ` (FV (shift_L (int d) (Suc c) a) - {0}) \<union> FV (shift_L (int d) c t))) = (\<lambda>n. n + d) ` ((FV t \<union> ((\<Union>n<length B'. (\<lambda>n. n - Suc 0) ` (FV (B' ! n) - {0})) \<union> (\<lambda>n. n - Suc 0) ` (FV a - {0}))) \<inter> Collect ((\<le>) c)) \<union> (FV t \<union> ((\<Union>n<length B'. (\<lambda>n. n - Suc 0) ` (FV (B' ! n) - {0})) \<union> (\<lambda>n. n - Suc 0) ` (FV a - {0}))) \<inter> {n. \<not> c \<le> n}"
              using  Suc(3)[unfolded H2, of 0, simplified] H3 Suc(1)[OF H2(3) Suc(3)[unfolded H2, of "Suc _", simplified] 
                                                                      Suc(3)[unfolded H2, of "Suc _", simplified], simplified]
              by (metis (no_types, lifting) sup_assoc)
            have "\<And>N Na Nb. (N::nat set) \<union> (Na \<union> (Nb \<union> N)) = N \<union> (Na \<union> Nb)"
              by fastforce
            then have f4: "FV (shift_L (int d) c t) \<union> ((\<Union>n<length B'. (\<lambda>n. n - Suc 0) ` (FV (shift_L (int d) (Suc c) (B' ! n)) - {0})) \<union> (\<lambda>n. n - Suc 0) ` (FV (shift_L (int d) (Suc c) a) - {0})) = (\<lambda>n. n + d) ` ((FV t \<union> ((\<Union>n<length B'. (\<lambda>n. n - Suc 0) ` (FV (B' ! n) - {0})) \<union> (\<lambda>n. n - Suc 0) ` (FV a - {0}))) \<inter> Collect ((\<le>) c)) \<union> (FV t \<union> ((\<Union>n<length B'. (\<lambda>n. n - Suc 0) ` (FV (B' ! n) - {0})) \<union> (\<lambda>n. n - Suc 0) ` (FV a - {0}))) \<inter> {n. \<not> c \<le> n}"
              using f3 by presburger
            then show "FV (shift_L (int d) c t) \<union>
              (\<Union>x<Suc (length B').
                  (\<lambda>y. y - Suc 0) ` (FV (shift_L (int d) (Suc c) ((a # B') ! x)) - {0})) =
              (\<lambda>x. x + d) `
              ((FV t \<union>
                ((\<Union>x<length B'. (\<lambda>y. y - Suc 0) ` (FV (B' ! x) - {0})) \<union>
                 (\<lambda>y. y - Suc 0) ` (FV a - {0}))) \<inter>
               Collect ((\<le>) c)) \<union>
              (FV t \<union>
               ((\<Union>x<length B'. (\<lambda>y. y - Suc 0) ` (FV (B' ! x) - {0})) \<union>
                (\<lambda>y. y - Suc 0) ` (FV a - {0}))) \<inter>
              {x. \<not> c \<le> x}"
              by (simp add: UN_Suc)
          qed
        qed
qed (force)+

lemma Binder_FV_subst:
  fixes n ::nat and t t1 t2::lterm
  assumes "\<And>n t. FV (subst_L n t t1) = (if n \<in> FV t1 then FV t1 - {n} \<union> FV t else FV t1)"
          "\<And>n t. FV (subst_L n t t2) = (if n \<in> FV t2 then FV t2 - {n} \<union> FV t else FV t2)"
  shows "(\<lambda>y. y - 1) ` (FV (subst_L (Suc n) (shift_L 1 0 t) t2) - {0}) \<union>
              FV (subst_L n t t1) = (if n \<in> (\<lambda>y. y - 1) ` (FV t2 - {0}) \<union> FV t1
                then (\<lambda>y. y - 1) ` (FV t2 - {0}) \<union> FV t1 - {n} \<union> FV t
                else (\<lambda>y. y - 1 ) ` (FV t2 - {0}) \<union> FV t1)"
proof -
  have "Suc n \<in> FV t2 \<Longrightarrow> ?thesis"
      proof (simp add: assms FV_shift[of 1 0, simplified] image_iff, meson)
        assume "Suc n \<in> FV t2" "n \<notin> FV t1" "\<exists>x\<in>FV t2 - {0}. n = x - Suc 0" 
        then show "(\<lambda>y. y - Suc 0) ` (FV t2 - {Suc n} \<union> Suc ` FV t - {0}) \<union> FV t1 =
                    (\<lambda>y. y - Suc 0) ` (FV t2 - {0}) \<union> FV t1 - {n} \<union> FV t"
         by (auto simp add: image_def Bex_def)
      qed force+
    moreover have "Suc n \<notin> FV t2 \<Longrightarrow> ?thesis"
      by (simp add: assms image_def Bex_def) fastforce

    ultimately show ?thesis  by satx
qed

lemmas int_1 = of_nat_1[where 'a=int]

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
  case (LetBinder t1 t2)
    note hyps=this         
    show ?case using Binder_FV_subst[OF hyps] by simp
next
  case (CaseSum t1 t2 t3)
    note hyps=this
    
    have   A:" (\<lambda>y. y - 1 ) ` (FV (subst_L (Suc n) (shift_L 1 0 t) t2) - {0}) \<union>
            (\<lambda>z. z - 1) ` (FV (subst_L (Suc n) (shift_L 1 0 t) t3) - {0}) \<union>
            FV (subst_L n t t1) = (\<lambda>y. y - 1) ` (FV (subst_L (Suc n) (shift_L 1 0 t) t2) - {0}) \<union>
            FV (subst_L n t t1) \<union> (\<lambda>ya. ya - 1) ` (FV (subst_L (Suc n) (shift_L 1 0 t) t3) - {0}) \<union>
            FV (subst_L n t t1)"
      by blast
        
    have B: "(if n \<in> (\<lambda>y. y - 1) ` (FV t2 - {0}) \<union>
             (\<lambda>z. z - 1) ` (FV t3 - {0}) \<union> FV t1
             then (\<lambda>y. y - 1) ` (FV t2 - {0}) \<union>
             (\<lambda>z. z - 1) ` (FV t3 - {0}) \<union> FV t1 - {n} \<union> FV t
             else (\<lambda>y. y - 1) ` (FV t2 - {0}) \<union>
             (\<lambda>z. z - 1) ` (FV t3 - {0}) \<union> FV t1) =
             (if n \<in> (\<lambda>y. y - 1) ` (FV t2 - {0}) \<union> FV t1
             then (\<lambda>y. y - 1) ` (FV t2 - {0}) \<union> FV t1 - {n} \<union> FV t
             else (\<lambda>y. y - 1) ` (FV t2 - {0}) \<union> FV t1) \<union>
             (if n \<in> (\<lambda>ya. ya - 1) ` (FV t3 - {0}) \<union> FV t1
             then (\<lambda>ya. ya - 1) ` (FV t3 - {0}) \<union> FV t1 - {n} \<union> FV t
             else (\<lambda>ya. ya - 1) ` (FV t3 - {0}) \<union> FV t1)"
       by (simp_all, blast+)
       
    show ?case
      using Binder_FV_subst[OF hyps(1,2), of n t]
            Binder_FV_subst[OF hyps(1,3), of n t]
      by (simp only: subst_L.simps FV.simps A B) blast
next
  case (CaseVar t1 L B)
    note hyps=this
    have H: "\<And>n t i. i<length B \<Longrightarrow>
            (\<lambda>y. y - 1) ` (FV (subst_L (Suc n) (shift_L 1 0 t) (B!i)) - {0}) \<union> FV (subst_L n t t1) =
            (if n \<in> (\<lambda>y. y - 1) ` (FV (B!i) - {0}) \<union> FV t1 then (\<lambda>y. y - 1) ` (FV (B!i) - {0}) \<union>
            FV t1 - {n} \<union> FV t else (\<lambda>y. y - 1) ` (FV (B!i) - {0}) \<union> FV t1)"
      using Binder_FV_subst[OF hyps] in_set_conv_nth[of "B!_" B]
      by blast
    have simp1: "(\<Union>i<length B. (\<lambda>y. y - 1) ` (FV (map (subst_L (Suc n) (shift_L 1 0 t)) B ! i)-{0})) =
                  (\<Union>i<length B. (\<lambda>y. y - 1) ` (FV (subst_L (Suc n) (shift_L 1 0 t) (B ! i))-{0}))"
      by simp
    show ?case           
      using H[of _ n t] 
      proof (simp only: "FV.simps" subst_L.simps length_map simp1 ,induction "length B" arbitrary: B)
        case (Suc n1 B1)
          then obtain a B' where H2:"B1=a#B'" "B1!0=a" "n1 = length B'"
            using Suc_length_conv  nth_Cons_0
            by metis
          have s1:"Suc 0 = 1" by simp
            
          note simp2 = UN_Suc[where n = "length B'" and P = "\<lambda>x. (\<lambda>y. y - 1) ` (FV (subst_L (Suc n) (shift_L 1 0 t) ((a # B') ! x)) - {0})",
                         unfolded nth_Cons_0 nth_Cons'[of a B' "Suc _", simplified if_False nat.distinct diff_Suc_1]]
           and simp3 = UN_Suc[where n = "length B'" and P = "\<lambda>x. (\<lambda>y. y - 1) ` (FV ((a # B') ! x) - {0})",
                         unfolded H2 nth_Cons_0 nth_Cons'[of a B' "Suc _", simplified if_False nat.distinct diff_Suc_1]]
             and H4=Suc(3)[of "Suc _", unfolded H2 nth_Cons'[of a B' "Suc _", simplified if_False nat.distinct diff_Suc_1]
                            , simplified this length_Cons]
          have H3: "((if n \<in> (\<lambda>y. y - 1) ` (FV a - {0}) \<union> FV t1
                    then (\<lambda>y. y - 1) ` (FV a - {0}) \<union> FV t1 - {n} \<union> FV t
                     else (\<lambda>y. y - 1) ` (FV a - {0}) \<union> FV t1)) \<union> 
                     (if n \<in> FV t1 \<union> (\<Union>i<length B'. (\<lambda>y. y - 1) ` (FV (B' ! i) - {0}))
                     then FV t1 \<union> (\<Union>i<length B'. (\<lambda>y. y - 1) ` (FV (B' ! i) - {0})) - {n} \<union> FV t
                     else FV t1 \<union> (\<Union>i<length B'. (\<lambda>y. y - 1) ` (FV (B' ! i) - {0})))= 
                    (if n \<in> FV t1 \<union> ((\<Union>i<length B'. (\<lambda>y. y - 1) ` (FV (B' ! i) - {0})) \<union> (\<lambda>y. y - 1) ` (FV a - {0}))
                     then FV t1 \<union> ((\<Union>i<length B'. (\<lambda>y. y - 1) ` (FV (B' ! i) - {0})) \<union> (\<lambda>y. y - 1) ` (FV a - {0})) - {n} \<union>
                          FV t
                     else FV t1 \<union> ((\<Union>i<length B'. (\<lambda>y. y - 1) ` (FV (B' ! i) - {0})) \<union> (\<lambda>y. y - 1) ` (FV a - {0})))"
            by auto
          have H5:"FV (subst_L n t t1) \<union> ((\<lambda>y. y - 1) ` (FV (subst_L (Suc n) (shift_L 1 0 t) a) - {0}) \<union>
                (\<Union>i<length B'. (\<lambda>y. y - 1) ` (FV (subst_L (Suc n) (shift_L 1 0 t) (B' ! i)) - {0}))) = 
                ((\<lambda>y. y - Suc 0) ` (FV (subst_L (Suc n) (shift_L 1 0 t) a) - {0}) \<union> FV (subst_L n t t1)) \<union>
                ( FV (subst_L n t t1) \<union> (\<Union>i<length B'. (\<lambda>y. y - 1) ` (FV (subst_L (Suc n) (shift_L 1 0 t) (B' ! i)) - {0})))"
            by auto
          show "?case"
            proof (simp only: length_Cons H2(1) simp3 simp2 Un_assoc)
              
              have f1: "(if n \<in> (\<lambda>y. y - 1) ` (FV a - {0}) \<union> FV t1 then (\<lambda>y. y - 1) ` (FV a - {0}) \<union> FV t1 - {n} \<union> 
                        FV t else (\<lambda>y. y - 1) ` (FV a - {0}) \<union> FV t1) \<union> (\<Union>i<length B'. (\<lambda>y. y - 1) ` 
                        (FV (subst_L (Suc n) (shift_L 1 0 t) (B' ! i)) - {0})) \<union> FV (subst_L n t t1) = (if n \<in> (\<lambda>y. y - 1) ` 
                        (FV a - {0}) \<union> FV t1 then (\<lambda>y. y - 1) ` (FV a - {0}) \<union> FV t1 - {n} \<union> FV t else (\<lambda>y. y - 1) ` 
                        (FV a - {0}) \<union> FV t1) \<union> (if n \<in> FV t1 \<union> (\<Union>i<length B'. (\<lambda>y. y - 1) ` (FV (B' ! i) - {0}))
                        then FV t1 \<union> (\<Union>i<length B'. (\<lambda>y. y - 1) ` (FV (B' ! i) - {0})) - {n} \<union> FV t else FV t1 \<union> 
                        (\<Union>i<length B'. (\<lambda>y. y - 1) ` (FV (B' ! i) - {0})))"
                using  Suc(3)[of 0,unfolded H2 nth_Cons_0, simplified, unfolded s1] Suc(1)[OF H2(3) H4 H4, unfolded s1]
                by blast
                
              have "FV (subst_L n t t1) \<subseteq> (if n \<in> (\<lambda>n. n - 1) ` (FV a - {0}) \<union> FV t1 then (\<lambda>n. n - 1) ` (FV a - {0}) \<union> FV t1 - {n} \<union> FV t else (\<lambda>n. n - 1) ` (FV a - {0}) \<union> FV t1) \<union> (\<Union>i<length B'. (\<lambda>n. n - 1) ` (FV (subst_L (Suc n) (shift_L 1 0 t) (B' ! i)) - {0})) \<longrightarrow> (if n \<in> (\<lambda>n. n - 1) ` (FV a - {0}) \<union> FV t1 then (\<lambda>n. n - 1) ` (FV a - {0}) \<union> FV t1 - {n} \<union> FV t else (\<lambda>n. n - 1) ` (FV a - {0}) \<union> FV t1) \<union> (\<Union>i<length B'. (\<lambda>n. n - 1) ` (FV (subst_L (Suc n) (shift_L 1 0 t) (B' ! i)) - {0})) \<union> FV (subst_L n t t1) = (if n \<in> (\<lambda>n. n - 1) ` (FV a - {0}) \<union> FV t1 then (\<lambda>n. n - 1) ` (FV a - {0}) \<union> FV t1 - {n} \<union> FV t else (\<lambda>n. n - 1) ` (FV a - {0}) \<union> FV t1) \<union> (\<Union>i<length B'. (\<lambda>n. n - 1) ` (FV (subst_L (Suc n) (shift_L 1 0 t) (B' ! i)) - {0}))"
                by (meson Un_absorb2)
              moreover
              { assume "(if n \<in> (\<lambda>n. n - 1) ` (FV a - {0}) \<union> FV t1 then (\<lambda>n. n - 1) ` (FV a - {0}) \<union> FV t1 - {n} \<union> FV t else (\<lambda>n. n - 1) ` (FV a - {0}) \<union> FV t1) \<union> (\<Union>i<length B'. (\<lambda>n. n - 1) ` (FV (subst_L (Suc n) (shift_L 1 0 t) (B' ! i)) - {0})) \<union> FV (subst_L n t t1) = (if n \<in> (\<lambda>n. n - 1) ` (FV a - {0}) \<union> FV t1 then (\<lambda>n. n - 1) ` (FV a - {0}) \<union> FV t1 - {n} \<union> FV t else (\<lambda>n. n - 1) ` (FV a - {0}) \<union> FV t1) \<union> (\<Union>i<length B'. (\<lambda>n. n - 1) ` (FV (subst_L (Suc n) (shift_L 1 0 t) (B' ! i)) - {0}))"
                then have "((if n \<in> (\<lambda>n. n - 1) ` (FV a - {0}) \<union> FV t1 then (\<lambda>n. n - 1) ` (FV a - {0}) \<union> FV t1 - {n} \<union> FV t else (\<lambda>n. n - 1) ` (FV a - {0}) \<union> FV t1) \<union> (\<Union>i<length B'. (\<lambda>n. n - 1) ` (FV (subst_L (Suc n) (shift_L 1 0 t) (B' ! i)) - {0})) \<union> FV (subst_L n t t1) = (if n \<in> (\<lambda>n. n - 1) ` (FV a - {0}) \<union> FV t1 then (\<lambda>n. n - 1) ` (FV a - {0}) \<union> FV t1 - {n} \<union> FV t else (\<lambda>n. n - 1) ` (FV a - {0}) \<union> FV t1) \<union> (\<Union>i<length B'. (\<lambda>n. n - 1) ` (FV (subst_L (Suc n) (shift_L 1 0 t) (B' ! i)) - {0}))) = ((if n \<in> FV t1 \<union> ((\<Union>i<length B'. (\<lambda>n. n - 1) ` (FV (B' ! i) - {0})) \<union> (\<lambda>n. n - 1) ` (FV a - {0})) then FV t1 \<union> ((\<Union>i<length B'. (\<lambda>n. n - 1) ` (FV (B' ! i) - {0})) \<union> (\<lambda>n. n - 1) ` (FV a - {0})) - {n} \<union> FV t else FV t1 \<union> ((\<Union>i<length B'. (\<lambda>n. n - 1) ` (FV (B' ! i) - {0})) \<union> (\<lambda>n. n - 1) ` (FV a - {0}))) = FV (subst_L n t t1) \<union> ((\<Union>i<length B'. (\<lambda>n. n - 1) ` (FV (subst_L (Suc n) (shift_L 1 0 t) (B' ! i)) - {0})) \<union> (\<lambda>n. n - 1) ` (FV (subst_L (Suc n) (shift_L 1 0 t) a) - {0}))) \<longrightarrow> FV (subst_L n t t1) \<union> ((\<Union>i<length B'. (\<lambda>n. n - 1) ` (FV (subst_L (Suc n) (shift_L 1 0 t) (B' ! i)) - {0})) \<union> (\<lambda>n. n - 1) ` (FV (subst_L (Suc n) (shift_L 1 0 t) a) - {0})) = (if n \<in> FV t1 \<union> ((\<Union>i<length B'. (\<lambda>n. n - 1) ` (FV (B' ! i) - {0})) \<union> (\<lambda>n. n - 1) ` (FV a - {0})) then FV t1 \<union> ((\<Union>i<length B'. (\<lambda>n. n - 1) ` (FV (B' ! i) - {0})) \<union> (\<lambda>n. n - 1) ` (FV a - {0})) - {n} \<union> FV t else FV t1 \<union> ((\<Union>i<length B'. (\<lambda>n. n - 1) ` (FV (B' ! i) - {0})) \<union> (\<lambda>n. n - 1) ` (FV a - {0})))"
                  by presburger
                moreover
                { assume "((if n \<in> (\<lambda>n. n - 1) ` (FV a - {0}) \<union> FV t1 then (\<lambda>n. n - 1) ` (FV a - {0}) \<union> FV t1 - {n} 
                            \<union> FV t else (\<lambda>n. n - 1) ` (FV a - {0}) \<union> FV t1) \<union> (\<Union>i<length B'. (\<lambda>n. n - 1) `
                            (FV (subst_L (Suc n) (shift_L 1 0 t) (B' ! i)) - {0})) \<union> FV (subst_L n t t1) = 
                            (if n \<in> (\<lambda>n. n - 1) ` (FV a - {0}) \<union> FV t1 then (\<lambda>n. n - 1) ` (FV a - {0}) \<union> FV t1 - {n}
                            \<union> FV t else (\<lambda>n. n - 1) ` (FV a - {0}) \<union> FV t1) \<union> (\<Union>i<length B'. (\<lambda>n. n - 1) ` (FV (subst_L (Suc n) (shift_L 1 0 t) (B' ! i)) - {0}))) \<noteq>
                            ((if n \<in> FV t1 \<union> ((\<Union>i<length B'. (\<lambda>n. n - 1) ` (FV (B' ! i) - {0})) \<union> (\<lambda>n. n - 1) `
                            (FV a - {0})) then FV t1 \<union> ((\<Union>i<length B'. (\<lambda>n. n - 1) ` (FV (B' ! i) - {0}))
                            \<union> (\<lambda>n. n - 1) ` (FV a - {0})) - {n} \<union> FV t else FV t1 \<union> 
                            ((\<Union>i<length B'. (\<lambda>n. n - 1) ` (FV (B' ! i) - {0})) \<union> (\<lambda>n. n - 1) ` (FV a - {0})))
                            = FV (subst_L n t t1) \<union> ((\<Union>i<length B'. (\<lambda>n. n - 1) ` (FV (subst_L (Suc n) (shift_L 1 0 t) (B' ! i)) - {0})) \<union> (\<lambda>n. n - 1) ` (FV (subst_L (Suc n) (shift_L 1 0 t) a) - {0})))"
                  then have "(if n \<in> (\<lambda>n. n - 1) ` (FV a - {0}) \<union> FV t1 then (\<lambda>n. n - 1) ` (FV a - {0}) \<union> 
                              FV t1 - {n} \<union> FV t else (\<lambda>n. n - 1) ` (FV a - {0}) \<union> FV t1) \<union> (\<Union>i<length B'.
                              (\<lambda>n. n - 1) ` (FV (subst_L (Suc n) (shift_L 1 0 t) (B' ! i)) - {0})) \<noteq> 
                              FV (subst_L n t t1) \<union> ((\<Union>i<length B'. (\<lambda>n. n - 1) ` (FV (subst_L (Suc n)
                              (shift_L 1 0 t) (B' ! i)) - {0})) \<union> (\<lambda>n. n - 1) ` (FV (subst_L (Suc n) 
                              (shift_L 1 0 t) a) - {0}))"
                    using f1 H3 by force
                  then have "(if n \<in> (\<lambda>n. n - 1) ` (FV a - {0}) \<union> FV t1 then (\<lambda>n. n - 1) ` (FV a - {0}) \<union> FV t1 - {n} \<union> FV t else (\<lambda>n. n - 1) ` (FV a - {0}) \<union> FV t1) \<union> (\<Union>i<length B'. (\<lambda>n. n - 1) ` (FV (subst_L (Suc n) (shift_L 1 0 t) (B' ! i)) - {0})) \<noteq> (\<Union>i<length B'. (\<lambda>n. n - 1) ` (FV (subst_L (Suc n) (shift_L 1 0 t) (B' ! i)) - {0})) \<union> (\<lambda>n. n - 1) ` (FV (subst_L (Suc n) (shift_L 1 0 t) a) - {0}) \<union> FV (subst_L n t t1)"
                    by (simp add: inf_sup_aci(5)) }
                ultimately have "(if n \<in> (\<lambda>n. n - 1) ` (FV a - {0}) \<union> FV t1 then (\<lambda>n. n - 1) ` (FV a - {0}) \<union> FV t1 - {n} \<union> FV t else (\<lambda>n. n - 1) ` (FV a - {0}) \<union> FV t1) \<union> (\<Union>i<length B'. (\<lambda>n. n - 1) ` (FV (subst_L (Suc n) (shift_L 1 0 t) (B' ! i)) - {0})) = (\<Union>i<length B'. (\<lambda>n. n - 1) ` (FV (subst_L (Suc n) (shift_L 1 0 t) (B' ! i)) - {0})) \<union> (\<lambda>n. n - 1) ` (FV (subst_L (Suc n) (shift_L 1 0 t) a) - {0}) \<union> FV (subst_L n t t1) \<longrightarrow> FV (subst_L n t t1) \<union> ((\<Union>i<length B'. (\<lambda>n. n - 1) ` (FV (subst_L (Suc n) (shift_L 1 0 t) (B' ! i)) - {0})) \<union> (\<lambda>n. n - 1) ` (FV (subst_L (Suc n) (shift_L 1 0 t) a) - {0})) = (if n \<in> FV t1 \<union> ((\<Union>i<length B'. (\<lambda>n. n - 1) ` (FV (B' ! i) - {0})) \<union> (\<lambda>n. n - 1) ` (FV a - {0})) then FV t1 \<union> ((\<Union>i<length B'. (\<lambda>n. n - 1) ` (FV (B' ! i) - {0})) \<union> (\<lambda>n. n - 1) ` (FV a - {0})) - {n} \<union> FV t else FV t1 \<union> ((\<Union>i<length B'. (\<lambda>n. n - 1) ` (FV (B' ! i) - {0})) \<union> (\<lambda>n. n - 1) ` (FV a - {0})))"
                  by satx }
              moreover
              { assume "\<not> FV (subst_L n t t1) \<subseteq> (if n \<in> (\<lambda>n. n - 1) ` (FV a - {0}) \<union> FV t1 then (\<lambda>n. n - 1) ` (FV a - {0}) \<union> FV t1 - {n} \<union> FV t else (\<lambda>n. n - 1) ` (FV a - {0}) \<union> FV t1) \<union> (\<Union>i<length B'. (\<lambda>n. n - 1) ` (FV (subst_L (Suc n) (shift_L 1 0 t) (B' ! i)) - {0}))"
                then have "(if n \<in> (\<lambda>n. n - 1) ` (FV a - {0}) \<union> FV t1 then (\<lambda>n. n - 1) ` (FV a - {0}) \<union> FV t1 - {n} \<union> FV t else (\<lambda>n. n - 1) ` (FV a - {0}) \<union> FV t1) \<union> (\<Union>i<length B'. (\<lambda>n. n - 1) ` (FV (subst_L (Suc n) (shift_L 1 0 t) (B' ! i)) - {0})) \<noteq> (\<Union>i<length B'. (\<lambda>n. n - 1) ` (FV (subst_L (Suc n) (shift_L 1 0 t) (B' ! i)) - {0})) \<union> (\<lambda>n. n - 1) ` (FV (subst_L (Suc n) (shift_L 1 0 t) a) - {0}) \<union> FV (subst_L n t t1)"
                  by blast }
              moreover
              { assume "(if n \<in> (\<lambda>n. n - 1) ` (FV a - {0}) \<union> FV t1 then (\<lambda>n. n - 1) ` (FV a - {0}) \<union> FV t1 - {n} \<union> FV t else (\<lambda>n. n - 1) ` (FV a - {0}) \<union> FV t1) \<union> (\<Union>i<length B'. (\<lambda>n. n - 1) ` (FV (subst_L (Suc n) (shift_L 1 0 t) (B' ! i)) - {0})) \<noteq> (\<Union>i<length B'. (\<lambda>n. n - 1) ` (FV (subst_L (Suc n) (shift_L 1 0 t) (B' ! i)) - {0})) \<union> (\<lambda>n. n - 1) ` (FV (subst_L (Suc n) (shift_L 1 0 t) a) - {0}) \<union> FV (subst_L n t t1)"
                then have "(if n \<in> (\<lambda>n. n - 1) ` (FV a - {0}) \<union> FV t1 then (\<lambda>n. n - 1) ` (FV a - {0}) \<union> FV t1 - {n} \<union> FV t else (\<lambda>n. n - 1) ` (FV a - {0}) \<union> FV t1) \<noteq> (\<lambda>n. n - 1) ` (FV (subst_L (Suc n) (shift_L 1 0 t) a) - {0}) \<union> FV (subst_L n t t1)"
                  by blast
                moreover
                { assume "(if n \<in> (\<lambda>n. n - 1) ` (FV a - {0}) \<union> FV t1 then (\<lambda>n. n - 1) ` (FV a - {0}) \<union> FV t1 - {n} \<union> FV t else (\<lambda>n. n - 1) ` (FV a - {0}) \<union> FV t1) \<noteq> (\<lambda>n. n - 1) ` (FV (B1 ! 0) - {0}) \<union> FV t1 - {n} \<union> FV t"
                  then have "n \<notin> (\<lambda>n. n - 1) ` (FV a - {0}) \<union> FV t1"
                    by (metis H2(2)) }
                ultimately have "FV (subst_L n t t1) \<union> ((\<Union>i<length B'. (\<lambda>n. n - 1) ` (FV (subst_L (Suc n) (shift_L 1 0 t) (B' ! i)) - {0})) \<union> (\<lambda>n. n - 1) ` (FV (subst_L (Suc n) (shift_L 1 0 t) a) - {0})) = (if n \<in> FV t1 \<union> ((\<Union>i<length B'. (\<lambda>n. n - 1) ` (FV (B' ! i) - {0})) \<union> (\<lambda>n. n - 1) ` (FV a - {0})) then FV t1 \<union> ((\<Union>i<length B'. (\<lambda>n. n - 1) ` (FV (B' ! i) - {0})) \<union> (\<lambda>n. n - 1) ` (FV a - {0})) - {n} \<union> FV t else FV t1 \<union> ((\<Union>i<length B'. (\<lambda>n. n - 1) ` (FV (B' ! i) - {0})) \<union> (\<lambda>n. n - 1) ` (FV a - {0})))"
                  by (metis H2(2) Suc.hyps(2) Suc.prems(1) zero_less_Suc) }
              ultimately show "FV (subst_L n t t1) \<union> ((\<Union>i<length B'. (\<lambda>n. n - 1) ` (FV (subst_L (Suc n) (shift_L 1 0 t) (B' ! i)) - {0})) \<union> (\<lambda>n. n - 1) ` (FV (subst_L (Suc n) (shift_L 1 0 t) a) - {0})) = (if n \<in> FV t1 \<union> ((\<Union>i<length B'. (\<lambda>n. n - 1) ` (FV (B' ! i) - {0})) \<union> (\<lambda>n. n - 1) ` (FV a - {0})) then FV t1 \<union> ((\<Union>i<length B'. (\<lambda>n. n - 1) ` (FV (B' ! i) - {0})) \<union> (\<lambda>n. n - 1) ` (FV a - {0})) - {n} \<union> FV t else FV t1 \<union> ((\<Union>i<length B'. (\<lambda>n. n - 1) ` (FV (B' ! i) - {0})) \<union> (\<lambda>n. n - 1) ` (FV a - {0})))"
                by linarith
            qed
          qed(simp add: hyps)              

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
  case (has_type_Let \<Gamma> t1 \<sigma>1 A t2 B) 
    show ?case
      using has_type_Let(4)[of "Suc n"] has_type_Let(5)
            has_type_Let(3)[OF has_type_Let(5)]
      by (auto intro!: has_type_L.intros(10) simp: simpl1) 
next
  case (has_type_LetPattern p B t1 \<sigma>1 \<Gamma> \<sigma>2 t2 A)
    note hyps=this
    show ?case
      using hyps(1,2,3) hyps(5,6)[OF hyps(7)]
      by (auto intro: has_type_L.intros(19))
next
  case (has_type_Case \<Gamma>1 t \<sigma>1 A B t1 C t2)

    show ?case
      using has_type_Case(4)[OF has_type_Case(7)]
            has_type_Case(5,6)[of "Suc n"] has_type_Case(7)
            has_type_L.intros(22) 
      by (force simp add: simpl1 simpl2 simpl3)      
next
  case (has_type_CaseV L TL B \<Gamma> t \<sigma>1  A)
    show ?case
      using has_type_CaseV(1-4, 8)
            has_type_CaseV(6)[OF has_type_CaseV(8)]
            has_type_CaseV(7)[rule_format, THEN conjunct2, rule_format, of _ "Suc n"]
            nth_map[of _ B "shift_L 1 (Suc n)"]
      by (force intro: has_type_L.intros(24))
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
  "fill Map.empty t= t"
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
      by (induction B arbitrary: t, force+)       
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
  "\<emptyset> \<turnstile> \<lparr>t |;| Map.empty\<rparr> |:| A \<Longrightarrow> is_value_L t \<or> (\<exists>t1. eval1_L t t1)"
proof (induction "\<emptyset>::ltype list" t "Map.empty::nat\<rightharpoonup>ltype" A rule: has_type_L.induct)
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
  case (has_type_Case t A B t1 C t2)
    note hyps=this
    show ?case
      using canonical_forms(8)[OF _ hyps(1)] hyps(2) eval1_L.intros(27-29)
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
   case (has_type_Let t \<sigma> A t1 B)
    note hyps=this

    have "\<And>x. x\<in>FV t \<Longrightarrow> x\<noteq>n" "\<And>x. x\<in>FV t1 \<Longrightarrow> x\<noteq>Suc n"
      using hyps(6)[simplified]
      by fastforce+

    then show ?case 
      using hyps(2)[OF _ hyps(5)] hyps(4)[of "Suc n"] hyps(5)            
      by (force intro: has_type_L.intros)      
next
  case (has_type_ProjR L l TL t)
    note hyps=this
    show ?case
      using hyps(7)[simplified] hyps(1-3)
            hyps(5)[OF _ hyps(6), simplified]
      by (force intro!: has_type_L.intros(17))
next
  case (has_type_Case t \<sigma>1 A B t1 C t2)
    note hyps=this  
    have FV_t: "\<And>z. z\<in>FV t \<Longrightarrow> z\<noteq>n" "\<And>z. z \<in> FV t2  \<Longrightarrow> z\<noteq>Suc n"
               "\<And>z. z \<in> FV t1  \<Longrightarrow> z\<noteq>Suc n"
      using hyps(8)[simplified]
      by fastforce+

    then show ?case
      using hyps(2)[OF _ hyps(7)]
            hyps(4,6)[of "Suc n"] hyps(7)
            has_type_L.intros(22) 
      by (force simp add: simpl1 simpl2 simpl3)
next
  case (has_type_CaseV L TL B t \<sigma>  A)
    note hyps_t=this
    have "\<And>x. x\<in> FV t \<Longrightarrow> x\<noteq>n"
         "\<And>i x. i<length B \<Longrightarrow> x\<in>FV (B!i) \<Longrightarrow> x \<noteq> Suc n"
     using hyps_t(9)[simplified]
     by fastforce+

    then show ?case
      using hyps_t(1-5) 
            hyps_t(6)[OF _ hyps_t(8), simplified]
            hyps_t(8) hyps_t(7)[rule_format, THEN conjunct2, rule_format, of _ "Suc n"]
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
    note hyps=this(1-)
    show ?case 
      using hyps(1,2,7) hyps(4-6)[of \<sigma>1]
      by (force intro: has_type_L.intros)
next
  case (has_type_CaseV L TL B \<Gamma> t \<sigma> A)
    note hyps=this
    have "\<forall>i<length L. (\<Gamma>|,|(TL ! i)) \<turnstile> \<lparr>(B ! i)|;|\<sigma>1\<rparr> |:| A"
      using hyps(7,8)
      by meson

    then show ?case 
      using hyps(1-5) hyps(6)[OF hyps(8)] 
      by (force intro!: has_type_L.intros)
qed (force intro: has_type_L.intros simp: nth_append min_def)+

(*sorry only concerns patterns missing premise in typing rule or
  required a different premise (instead of \<sigma>1 \<subseteq>\<^sub>f \<sigma>) *)
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
  case (has_type_Let \<Gamma> t1 \<sigma> A t2 B)
    note hyps=this 
    have "\<Gamma> |,| A \<turnstile> \<lparr>subst_L (Suc n) (shift_L 1 0 s) t2|;|\<sigma>\<rparr> |:| B"
      using hyps(5-6) weakening[of \<Gamma> _ \<sigma>1 S 0 A, simplified]
            hyps(4)[OF _ _ hyps(7), of "Suc n"]
      by (metis Suc_mono diff_Suc_1 fst_conv has_type_LVar inversion(4) length_Cons nat.distinct(1)
                nth_Cons' snd_conv)    
    then show ?case 
      using hyps(3)[OF hyps(5-7)] 
      by (force intro: has_type_L.intros(10))
      
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
  case (has_type_Case \<Gamma> t \<sigma>2 A B t1 C t2)
    note hyps=this
     have "\<Gamma> |,| A \<turnstile> \<lparr>subst_L (Suc n) (shift_L 1 0 s) t1|;|\<sigma>2\<rparr> |:| C"    
       using hyps(5,7-9)
             weakening[of \<Gamma> _ \<sigma>1 S 0 A, simplified]
       by (metis Suc_mono diff_Suc_1 fst_conv has_type_LVar inversion(4) length_Cons nat.distinct(1)
                nth_Cons' snd_conv)    
     moreover  have "\<Gamma> |,| B \<turnstile> \<lparr>subst_L (Suc n) (shift_L 1 0 s) t2|;|\<sigma>2\<rparr> |:| C"    
       using hyps(6,7-9)
             weakening[of \<Gamma> _ \<sigma>1 S 0 B, simplified]
       by (metis Suc_mono diff_Suc_1 fst_conv has_type_LVar inversion(4) length_Cons nat.distinct(1)
                nth_Cons' snd_conv)    


     ultimately show ?case 
       using hyps(4)[OF hyps(7-9)]
       by (force intro: has_type_L.intros)
      
next
  case (has_type_CaseV L TL B \<Gamma> t \<sigma> A)
    note hyps=this
    have "\<And>i. i<length L \<Longrightarrow> \<Gamma> |,| (TL ! i) \<turnstile> \<lparr>subst_L (Suc n) (shift_L 1 0 s) (B ! i)|;|\<sigma>\<rparr> |:| A"
      using hyps(7)[rule_format, THEN conjunct2, rule_format]
            weakening[of \<Gamma> _ \<sigma>1 S 0 "TL!_", simplified]
            hyps(8-)
      by (metis Suc_mono diff_Suc_1 fst_conv has_type_LVar inversion(4) length_Cons nat.distinct(1)
                nth_Cons' snd_conv)     
    then show ?case 
      using hyps(1-4,7)
            hyps(6)[OF hyps(8-)]
      by (force intro!: has_type_L.intros(24))      

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
  case (has_type_Let \<Gamma> ta \<sigma> A tb B)
    note hyps=this(1-4) and inv=this(5)[unfolded eval1_L.simps[of "LetBinder _ _", simplified]]
   
      
    have "(\<And>xa. xa \<in> FV (subst_L 0 (shift_L 1 0 ta) tb) \<Longrightarrow> xa \<noteq> 0)"
      proof 
        fix x1
        assume H:"x1 \<in> FV (subst_L 0 (shift_L 1 0 ta) tb)" "x1 = 0"
        have "x1\<in>FV (shift_L (int 1) 0 ta) \<Longrightarrow> False"
          using FV_shift[of 1 0, simplified] H(2)
          by auto
              
        then show False 
          using H(1) FV_subst[of 0 "shift_L 1 0 ta" tb] image_def
          by (cases "0\<in>FV tb") (simp add: H(2))+
      qed

    hence "t1 =shift_L (- 1) 0 (subst_L 0 (shift_L 1 0 ta) tb) \<and> is_value_L ta \<Longrightarrow> ?case"
      using substitution[OF hyps(2) _ weakening[OF hyps(1), of 0 A, simplified], of 0]
            has_type_LVar[of 0 A "\<Gamma>|,|A", simplified]
            shift_down[of 0 A \<Gamma> "(subst_L 0 (shift_L 1 0 ta) tb)" \<sigma> B, simplified]
      by force      
     
    with inv show ?case using hyps(2,3) has_type_L.intros(10) by fast
      
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
  case (has_type_Case \<Gamma> t \<sigma>1 A B ta C tb)
    note hyps=this and inv = this(7)[unfolded eval1_L.simps[of "CaseSum  _ _ _" ,simplified]]
    have "\<exists>v. (\<exists>A. t = inl v as A) \<and> t1 = shift_L (- 1) 0 (subst_L 0 (shift_L 1 0 v) ta) \<and> is_value_L v \<Longrightarrow>
          ?case"
      proof -
        assume "\<exists>v. (\<exists>A. t = inl v as A) \<and> t1 = shift_L (- 1) 0 (subst_L 0 (shift_L 1 0 v) ta) \<and> is_value_L v"
        then obtain v A1 where H:"t = inl v as A1" "t1 = shift_L (- 1) 0 (subst_L 0 (shift_L 1 0 v) ta)"
          by blast

        have "\<And>xa. xa \<in> FV (subst_L 0 (shift_L 1 0 v) ta) \<Longrightarrow> xa \<noteq> 0"        
          proof 
            fix x1
            assume H1:"x1 \<in> FV (subst_L 0 (shift_L 1 0 v) ta)" "x1 = 0"
                        
            have "x1\<in>FV (shift_L (int 1) 0 v) \<Longrightarrow> False"
              using FV_shift[of 1 0 v] H1
              by auto
                  
            then show False 
              using H1(1) image_iff FV_subst[of 0 "shift_L 1 0 v" ta]
              by (cases "0\<in>FV ta") (simp add: H1(2))+
          qed

        with H show ?case 
          using hyps(1) has_type_LVar[of 0 A "\<Gamma>|,|A"]                
                inversion(20) weakening[of \<Gamma> v \<sigma>1 A 0 A, simplified]
                substitution[OF hyps(2)] 
                shift_down[of 0 A \<Gamma> "(subst_L 0 (shift_L 1 0 v) ta)"]
          by fastforce
      qed

    moreover have "\<exists>v. (\<exists>A. t = inr v as A) \<and> t1 = shift_L (- 1) 0 (subst_L 0 (shift_L 1 0 v) tb) \<and> is_value_L v \<Longrightarrow>
          ?case"
      proof -
        assume "\<exists>v. (\<exists>A. t = inr v as A) \<and> t1 = shift_L (- 1) 0 (subst_L 0 (shift_L 1 0 v) tb) \<and> is_value_L v"
        then obtain v A1 where H:"t = inr v as A1" "t1 = shift_L (- 1) 0 (subst_L 0 (shift_L 1 0 v) tb)"
          by blast
        have "\<And>xa. xa \<in> FV (subst_L 0 (shift_L 1 0 v) tb) \<Longrightarrow> xa \<noteq> 0"        
          proof 
            fix x1
            assume H1:"x1 \<in> FV (subst_L 0 (shift_L 1 0 v) tb)" "x1 = 0"
             
            have "x1\<in>FV (shift_L (int 1) 0 v) \<Longrightarrow> False"
              using FV_shift[of 1 0 v] H1
              by auto 
                  
            then show False 
              using H1(1) FV_subst[of 0 "shift_L 1 0 v" tb] image_iff
              by (cases "0\<in>FV tb") (simp add: H1(2))+
          qed
        with H show ?case 
          using hyps(1) has_type_LVar[of 0 B "\<Gamma>|,|B", simplified] 
                inversion(21)
                weakening[of \<Gamma> v \<sigma>1 B 0 B, simplified] 
                substitution[OF hyps(3)] 
                shift_down[of 0 B \<Gamma> "(subst_L 0 (shift_L 1 0 v) tb)"]
          by fastforce
      qed

    ultimately show ?case using inv has_type_L.intros(22)[OF hyps(4,2,3)] by fast
      
next
  case (has_type_CaseV L TL B \<Gamma> t \<sigma> A)
    note hyps=this and inv=this(8)[unfolded eval1_L.simps[of "CaseVar _ _ _ ", simplified]]
    have P:" \<And>i. i<length L \<Longrightarrow> (\<Gamma>|,|(TL ! i)) \<turnstile> \<lparr>(B ! i)|;|\<sigma>\<rparr> |:| A" 
      using hyps(7)
      by blast
    have "\<exists>v i. (\<exists>A. t = <L ! i:=v> as A) \<and>
           t1 = shift_L (- 1) 0
                 (subst_L 0 (shift_L 1 0 v) (B!i)) \<and> i < length L
          \<Longrightarrow> ?case"
      proof -
        assume "\<exists>v i. (\<exists>A. t = <L ! i:=v> as A) \<and> t1 = shift_L (- 1) 0
                 (subst_L 0 (shift_L 1 0 v) (B!i)) \<and> i < length L"
        then obtain v i A1 where H:"i<length L" "t = <L!i:=v> as A1"
                                    "t1 = shift_L (- 1) 0 (subst_L 0 
                                          (shift_L 1 0 v) (B!i))"
          by blast
        have "\<And>xa. xa \<in> FV (subst_L 0 (shift_L 1 0 v) (B!i)) \<Longrightarrow> xa \<noteq> 0"        
          proof 
            fix x1
            assume H1:"x1 \<in> FV (subst_L 0 (shift_L 1 0 v) (B!i))" "x1 = 0"
 
            have "x1\<in>FV (shift_L (int 1) 0 v) \<Longrightarrow> False"
              using FV_shift[of 1 0 v] H1
              by auto
                  
            then show False 
              using H1(1) FV_subst[of 0 "shift_L 1 0 v" "B!i"] image_iff
              by (cases "0\<in>FV (B!i)") (simp add: H1(2))+
          qed
        moreover have "\<Gamma> \<turnstile> \<lparr>v|;|\<sigma>\<rparr> |:| (TL ! i)"
          using hyps(5)[unfolded H has_type_L.simps[of _ "<_:= _> as _", simplified]]
                hyps(2) distinct_conv_nth
                H(1) ltype.inject(7)
          by blast
        ultimately show ?case 
          using P has_type_LVar[of 0 "TL!i" " \<Gamma>|,| (TL!i)"] H               
                weakening[of \<Gamma> v \<sigma> "TL!i" 0 "TL!i", simplified] 
                substitution[of "\<Gamma>|,| (TL!i)" "B!i" \<sigma>] 
                shift_down[of 0 "TL!i" \<Gamma> "(subst_L 0 (shift_L 1 0 v) (B!i))"]
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
