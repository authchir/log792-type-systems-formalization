(*<*)
theory Ext_Structures
imports
   Main
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
    "is_value_L v \<Longrightarrow> Lmatch (V n) v (fill (\<lambda>p. if (p=n) then v else (<|V p|>)))" |
  M_RCD:
    "distinct L \<Longrightarrow> length L = length LT \<Longrightarrow> length F = length PL \<Longrightarrow> length PL = length LT 
    \<Longrightarrow> is_value_L (Record L LT) \<Longrightarrow> (\<And>i. i<length PL \<Longrightarrow> Lmatch (PL!i) (LT!i) (F!i))
    \<Longrightarrow> Lmatch (RCD L PL) (Record L LT) (\<Odot> F)"

abbreviation coherent ::"Lpattern \<Rightarrow> bool" where
"coherent p \<equiv> distinct (Pvars p)"

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

  -- "Rules relating to the evaluation of Plus"
  eval1_LPlus:
    "eval1_L (LPlus (LNat n1) (LNat n2)) (LNat (n1+n2))"|
  eval1_LUMinus:
    "eval1_L (UMinus (LNat n1)) (LNat (-n1))" |
  eval1_LIsZero:
    "eval1_L (IsZero (LNat 0)) LTrue" |
 -- "Rules relating to evaluation of sequence"
  
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
    "is_value_L v1 \<Longrightarrow> eval1_L (Let var x := v1 in t2) (subst_L x v1 t2)" |
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
    " l\<in>set L \<Longrightarrow> index L l = m \<Longrightarrow> is_value_L (Record (take m L) (take m LT)) \<Longrightarrow> 
      eval1_L (LT ! m) (t') \<Longrightarrow> eval1_L (Record L LT) (Record L (replace m t' LT))" |   
 -- "Rules relating to evaluation of pattern matching"
  eval1_L_LetPV:
    "coherent p \<Longrightarrow> is_value_L v1 \<Longrightarrow> Lmatch p v1 \<sigma> \<Longrightarrow> eval1_L (Let pattern p := v1 in t2) (\<sigma> t2)" |
  eval1_L_LetP:
    "eval1_L t1 t1' \<Longrightarrow> eval1_L (Let pattern p := t1 in t2) (Let pattern p := t1' in t2)" |
 -- "Rules relating to evaluation of Sums"
  eval1_L_CaseInl:
    "is_value_L v \<Longrightarrow> eval1_L (Case (inl v as A) of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2) (subst_L x v t1)" |
  eval1_L_CaseInr:
    "is_value_L v \<Longrightarrow> eval1_L (Case (inr v as A) of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2) (subst_L y v t2)" |
  eval1_L_CaseS:
    "eval1_L t t' \<Longrightarrow> eval1_L (Case t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2) (Case t' of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2)" |
  eval1_L_Inl:
    "eval1_L t t' \<Longrightarrow> eval1_L (inl t as A) (inl t' as A)" |
  eval1_L_Inr:
    "eval1_L t t' \<Longrightarrow> eval1_L (inr t as A) (inr t' as A)" |
  eval1_L_CaseVar:
    "l=L!i \<Longrightarrow> eval1_L (Case (<l:=v> as A) of <L:=I> \<Rightarrow> LT) (subst_L (I!i) v (LT!i))" |
  eval1_L_CaseV:
    "eval1_L t t' \<Longrightarrow> eval1_L (Case t of <L:=I> \<Rightarrow> LT) (Case t' of <L:=I> \<Rightarrow> LT)" |
  eval1_L_Variant:
    "eval1_L t t' \<Longrightarrow> eval1_L (<l:=t> as A) (<l:=t'> as A)"

type_synonym lcontext = "ltype list"
type_synonym pcontext = "(lterm \<Rightarrow> lterm)"

notation Nil ("\<emptyset>")
abbreviation cons :: "lcontext \<Rightarrow> ltype \<Rightarrow> lcontext" (infixl "|,|" 200) where
  "cons \<Gamma> T' \<equiv> T' # \<Gamma>"
abbreviation elem' :: "(nat \<times> ltype) \<Rightarrow> lcontext \<Rightarrow> bool" (infix "|\<in>|" 200) where
  "elem' p \<Gamma> \<equiv> fst p < length \<Gamma> \<and> snd p = nth \<Gamma> (fst p)"


text{*  For the typing rule of letbinder, we require to replace the type 
        of the variable by the expected type 
    *}

inductive has_type_L :: "lcontext \<Rightarrow> lterm \<Rightarrow> pcontext \<Rightarrow> ltype \<Rightarrow> bool" ("((_)/ \<turnstile> \<lparr>(_)|;|(_)\<rparr>/ |:| (_))" [150, 150, 150, 150] 150) where
  -- "Rules relating to the type of Booleans"
  has_type_LTrue:
    "\<Gamma> \<turnstile> \<lparr>LTrue|;|fill \<delta>\<rparr> |:| Bool" |
  has_type_LFalse:
    "\<Gamma> \<turnstile> \<lparr>LFalse|;|fill \<delta>\<rparr> |:| Bool" |
  has_type_LIf:
    "\<Gamma> \<turnstile> \<lparr>t1|;|fill \<delta>\<rparr> |:| Bool \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t2|;|fill \<delta>\<rparr> |:| T' \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t3|;|fill \<delta>\<rparr> |:| T' \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>LIf t1 t2 t3|;|fill \<delta>\<rparr> |:| T'" |

  -- \<open>Rules relating to the type of the constructs of the $\lambda$-calculus\<close>
  has_type_LVar:
    "(x, T') |\<in>| \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>LVar x|;|fill \<delta>\<rparr> |:| (T')" |
  has_type_LNat:
    "\<Gamma> \<turnstile> \<lparr>LNat n|;| fill \<delta>\<rparr> |:| Nat"|
  has_type_LPlus:
    "\<Gamma> \<turnstile> \<lparr>t1|;| fill \<delta>\<rparr> |:| Nat \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t2|;| fill \<delta>\<rparr> |:| Nat \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>LPlus t1 t2|;| fill \<delta>\<rparr> |:| Nat" |  
  has_type_UMinus:
    "\<Gamma> \<turnstile> \<lparr>t|;| fill \<delta>\<rparr> |:| Nat \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>UMinus t|;| fill \<delta>\<rparr> |:| Nat" |
  has_type_IsZero:
    "\<Gamma> \<turnstile> \<lparr>t|;| fill \<delta>\<rparr> |:| Nat \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>IsZero t|;| fill \<delta>\<rparr> |:| Bool" |
  has_type_LAbs:
    "(\<Gamma> |,| T1) \<turnstile> \<lparr>t2|;| fill (shift_L 1 (Suc (nbinder t2)) \<circ> \<delta>)\<rparr> |:| T2 \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>LAbs T1 t2|;|fill \<delta>\<rparr> |:| (T1 \<rightarrow> T2)" |
  has_type_LApp:
    "\<Gamma> \<turnstile> \<lparr>t1|;|fill \<delta>\<rparr> |:| (T11 \<rightarrow> T12) \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t2|;|fill \<delta>\<rparr> |:| T11 \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>LApp t1 t2|;|fill \<delta>\<rparr> |:| T12" |  
  has_type_LUnit:
    "\<Gamma> \<turnstile> \<lparr>unit|;|fill \<delta>\<rparr> |:| Unit " |  
  has_type_LSeq:
    "\<Gamma> \<turnstile> \<lparr>t1|;|fill \<delta>\<rparr> |:| Unit \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t2|;|fill \<delta>\<rparr> |:| A \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Seq t1 t2|;|fill \<delta>\<rparr> |:| A" |
  has_type_LAscribe:
    "\<Gamma> \<turnstile> \<lparr>t1|;|fill \<delta>\<rparr> |:| A \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t1 as A|;|fill \<delta>\<rparr> |:| A" |
  has_type_Let:
    "\<Gamma> \<turnstile> \<lparr>t1|;|fill \<delta>\<rparr> |:| A \<Longrightarrow> (replace x A \<Gamma>) \<turnstile> \<lparr>t2|;| fill \<delta>\<rparr> |:| B \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Let var x := t1 in t2|;|fill \<delta>\<rparr> |:| B" |
  has_type_Pair:
    "\<Gamma> \<turnstile> \<lparr>t1|;|fill \<delta>\<rparr> |:| A \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t2|;|fill \<delta>\<rparr> |:| B \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>\<lbrace>t1,t2\<rbrace>|;|fill \<delta>\<rparr> |:| A |\<times>| B" |
  has_type_Proj1:
    "\<Gamma> \<turnstile> \<lparr>t1|;|fill \<delta>\<rparr> |:| A |\<times>| B \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>\<pi>1 t1|;|fill \<delta>\<rparr> |:| A" |
  has_type_Proj2:
    "\<Gamma> \<turnstile> \<lparr>t1|;|fill \<delta>\<rparr> |:| A |\<times>| B \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>\<pi>2 t1|;|fill \<delta>\<rparr> |:| B" |
  has_type_Tuple:
    "L\<noteq>[] \<Longrightarrow> length L = length TL \<Longrightarrow> (\<And>i. 0\<le>i \<Longrightarrow> i< length L \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>(L ! i)|;|fill \<delta>\<rparr> |:| (TL ! i))
      \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Tuple L|;|fill \<delta>\<rparr> |:| \<lparr>TL\<rparr>" |
  has_type_ProjT:
    "1\<le>i \<Longrightarrow> i\<le> length TL \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t|;|fill \<delta>\<rparr> |:| \<lparr>TL\<rparr> \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>\<Pi> i t|;|fill \<delta>\<rparr> |:| (TL ! (i-1))" |
  has_type_RCD:
    "L\<noteq>[] \<Longrightarrow> distinct L \<Longrightarrow> length LT = length TL \<Longrightarrow> length L = length LT \<Longrightarrow> (\<And>i. i< length LT \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>(LT ! i)|;|fill \<delta>\<rparr> |:| (TL ! i))
      \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Record L LT|;|fill \<delta>\<rparr> |:| \<lparr>L|:|TL\<rparr>" |
  has_type_ProjR:
    "distinct L1 \<Longrightarrow> l\<in> set L1  \<Longrightarrow> length L1 = length TL \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t|;|fill \<delta>\<rparr> |:| \<lparr>L1|:|TL\<rparr> \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>ProjR l t|;|fill \<delta>\<rparr> |:| (TL ! index L1 l)" |
  has_type_PatternVar:
    "\<Gamma> \<turnstile> \<lparr> (fill \<delta>^^n) (<|V k|>) |;| id\<rparr> |:| A \<Longrightarrow>  set(patterns ((fill \<delta>^^n) (<|V k|>))) = {}\<Longrightarrow> \<Gamma> \<turnstile> \<lparr><|V k|>|;|fill \<delta>\<rparr> |:| A" |
  has_type_PatternRCD:
    "L\<noteq>[] \<Longrightarrow> distinct L \<Longrightarrow> length PL = length TL \<Longrightarrow> length L = length PL \<Longrightarrow> (\<And>i. i< length PL \<Longrightarrow> \<Gamma> \<turnstile> \<lparr><|PL ! i|>|;|fill \<delta>\<rparr> |:| (TL ! i))
      \<Longrightarrow> \<Gamma> \<turnstile> \<lparr><|RCD L PL|>|;|fill \<delta>\<rparr> |:| \<lparr>L|:|TL\<rparr>" |
  has_type_LetPattern:
    "coherent p \<Longrightarrow> Lmatch p t1 \<delta>  \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t1|;|fill \<delta>1\<rparr> |:| R \<Longrightarrow>
     \<Gamma> \<turnstile> \<lparr>t2|;|((fill \<delta>1) \<circ> \<delta>)\<rparr> |:| A \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Let pattern p := t1 in t2|;|fill \<delta>1\<rparr> |:| A" |
  has_type_Inl:
    "\<Gamma> \<turnstile> \<lparr>t1|;|fill \<delta>1\<rparr> |:| A \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>inl t1 as A|+|B |;|fill \<delta>1\<rparr> |:| A|+|B" |
  has_type_Inr:
    "\<Gamma> \<turnstile> \<lparr>t1|;|fill \<delta>1\<rparr> |:| B \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>inr t1 as A|+|B |;|fill \<delta>1\<rparr> |:| A|+|B" |
  has_type_Case:
    "\<Gamma> \<turnstile> \<lparr> t|;|fill \<delta>1 \<rparr> |:| A|+|B \<Longrightarrow> replace x A \<Gamma> \<turnstile> \<lparr>t1|;|fill \<delta>1\<rparr> |:| C \<Longrightarrow>
     replace y B \<Gamma> \<turnstile> \<lparr>t2|;|fill \<delta>1\<rparr> |:| C \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Case t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2 |;|fill \<delta>1\<rparr> |:| C" |
  has_type_Variant:
    "\<Gamma> \<turnstile> \<lparr> t |;| fill \<delta> \<rparr> |:| (TL!i) \<Longrightarrow> \<Gamma> \<turnstile> \<lparr> <(L!i):=t> as <L|,|TL> |;| fill \<delta> \<rparr> |:| <L|,|TL>" |
  has_type_CaseV:
    " L\<noteq>\<emptyset> \<Longrightarrow> length I = length L \<Longrightarrow> length L = length TL \<Longrightarrow> length L = length LT \<Longrightarrow>
      \<Gamma> \<turnstile> \<lparr> t |;| fill \<delta> \<rparr> |:| <L|,|TL> \<Longrightarrow> (\<forall>i<length L. replace (I!i) (TL!i) \<Gamma> \<turnstile> \<lparr>(LT!i)|;|fill \<delta>\<rparr> |:| A) \<Longrightarrow>
      \<Gamma> \<turnstile> \<lparr> Case t of <L:=I> \<Rightarrow> LT |;|fill \<delta>\<rparr> |:| A"

inductive_cases has_type_LetE : "\<Gamma> \<turnstile> \<lparr> Let var x := t1 in t2|;|\<delta>1\<rparr>  |:| B"
inductive_cases has_type_ProjTE: "\<Gamma> \<turnstile> \<lparr> \<Pi> i t|;|\<delta>1\<rparr> |:| R"
inductive_cases has_type_ProjRE: "\<Gamma> \<turnstile> \<lparr> ProjR l t|;|\<delta>1\<rparr> |:| R"
inductive_cases has_type_LetPE: "\<Gamma> \<turnstile> \<lparr>Let pattern p := t1 in t2|;|\<delta>1\<rparr> |:| A"
inductive_cases has_type_CaseSE: "\<Gamma> \<turnstile> \<lparr>Case t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2|;|\<delta>1\<rparr> |:| R"
inductive_cases has_type_CaseVE: "\<Gamma> \<turnstile> \<lparr>Case t of <L:=I> \<Rightarrow> LT|;|\<delta>1\<rparr> |:| R"
inductive_cases has_type_LAbsE: "\<Gamma> \<turnstile> \<lparr>LAbs T1 t2|;|fill \<delta>'\<rparr> |:| R"
inductive_cases has_type_VariantE: "\<Gamma> \<turnstile> \<lparr><l:=t> as R |;|\<delta>1\<rparr> |:| R"

lemma record_patterns_characterisation:
  "set (patterns (<|RCD L PL|>)) \<subseteq> S \<Longrightarrow> x \<in> set PL \<Longrightarrow> set(patterns (<|x|>)) \<subseteq> S"
by (induction PL arbitrary: S x, auto) 

lemma inversion:
  "\<Gamma> \<turnstile> \<lparr> LTrue |;| \<delta>\<rparr> |:| R \<Longrightarrow> R = Bool"
  "\<Gamma> \<turnstile> \<lparr> LFalse |;| \<delta>\<rparr> |:| R \<Longrightarrow> R = Bool"
  "\<Gamma> \<turnstile> \<lparr> LIf t1 t2 t3 |;| \<delta>\<rparr> |:| R \<Longrightarrow>  \<Gamma> \<turnstile> \<lparr>t1|;| \<delta>\<rparr> |:| Bool \<and> \<Gamma> \<turnstile> \<lparr>t2|;| \<delta>\<rparr> |:| R \<and> \<Gamma> \<turnstile> \<lparr>t3|;| \<delta>\<rparr> |:| R"
  "\<Gamma> \<turnstile> \<lparr> LVar x|;| \<delta>\<rparr> |:| R \<Longrightarrow> (x, R) |\<in>| \<Gamma>"
  "\<Gamma> \<turnstile> \<lparr> LAbs T1 t2 |;| fill \<delta>'\<rparr> |:| R \<Longrightarrow> \<exists>R2 \<Delta>. R = T1 \<rightarrow> R2 \<and>  \<Gamma> |,| T1 \<turnstile> \<lparr>t2|;|fill (shift_L 1 (Suc (nbinder t2)) \<circ> \<Delta>)\<rparr> |:| R2 \<and> fill \<Delta> = fill \<delta>'"
  "\<Gamma> \<turnstile> \<lparr> LApp t1 t2 |;| \<delta>\<rparr> |:| R \<Longrightarrow> \<exists>T11. \<Gamma> \<turnstile> \<lparr>t1|;| \<delta>\<rparr> |:| T11 \<rightarrow> R \<and> \<Gamma> \<turnstile> \<lparr>t2|;| \<delta>\<rparr> |:| T11"
  "\<Gamma> \<turnstile> \<lparr> unit|;| \<delta>\<rparr> |:| R \<Longrightarrow> R = Unit"
  "\<Gamma> \<turnstile> \<lparr> Seq t1 t2 |;| \<delta>\<rparr> |:| R \<Longrightarrow> \<exists>A. R = A \<and> \<Gamma> \<turnstile> \<lparr>t2|;| \<delta>\<rparr> |:| A \<and> \<Gamma> \<turnstile> \<lparr>t1|;| \<delta>\<rparr> |:| Unit"
  "\<Gamma> \<turnstile> \<lparr> t as A |;| \<delta>\<rparr> |:| R \<Longrightarrow> R = A"
  "\<Gamma> \<turnstile> \<lparr> Let var x := t in t1 |;| \<delta>\<rparr> |:| R \<Longrightarrow> \<exists>A B. R = B \<and> \<Gamma> \<turnstile> \<lparr> t|;| \<delta>\<rparr> |:| A \<and> (replace x A \<Gamma>) \<turnstile> \<lparr> t1|;| \<delta>\<rparr> |:| B"
  "\<Gamma> \<turnstile> \<lparr> \<lbrace>t1,t2\<rbrace>|;| \<delta>\<rparr> |:| R \<Longrightarrow> \<exists>A B. \<Gamma> \<turnstile> \<lparr> t1|;| \<delta>\<rparr> |:| A \<and> \<Gamma> \<turnstile> \<lparr> t2|;| \<delta>\<rparr> |:| B \<and> R = A |\<times>| B"
  "\<Gamma> \<turnstile> \<lparr> \<pi>1 t|;| \<delta>\<rparr> |:| R \<Longrightarrow> \<exists>A B. \<Gamma> \<turnstile> \<lparr> t|;| \<delta>\<rparr> |:| A |\<times>| B \<and> R = A"
  "\<Gamma> \<turnstile> \<lparr> \<pi>2 t|;| \<delta>\<rparr> |:| R \<Longrightarrow> \<exists>A B. \<Gamma> \<turnstile> \<lparr> t|;| \<delta>\<rparr> |:| A |\<times>| B \<and> R = B"
  "\<Gamma> \<turnstile> \<lparr> Tuple L|;| \<delta>\<rparr> |:| R \<Longrightarrow> \<exists>TL. length L = length TL \<and> (\<forall>i. 0\<le>i \<longrightarrow> i< length L \<longrightarrow> \<Gamma> \<turnstile> \<lparr>(L ! i)|;| \<delta>\<rparr> |:| (TL ! i)) \<and> R = \<lparr>TL\<rparr>"
  "\<Gamma> \<turnstile> \<lparr> (\<Pi> i t)|;| \<delta>\<rparr> |:| R \<Longrightarrow> \<exists>TL. R = (TL ! (i-1)) \<and> \<Gamma> \<turnstile> \<lparr>t|;| \<delta>\<rparr> |:| \<lparr>TL\<rparr> \<and> 1\<le>i \<and> i\<le> length TL"
  "\<Gamma> \<turnstile> \<lparr> (Record L1 LT)|;| \<delta>\<rparr> |:| R \<Longrightarrow> \<exists>TL. R = \<lparr>L1|:|TL\<rparr> \<and> length TL = length LT \<and> length L1 = length LT \<and> distinct L1 \<and> 
                                    (\<forall>i. 0\<le>i \<longrightarrow> i< length LT \<longrightarrow> \<Gamma> \<turnstile> \<lparr> (LT ! i)|;| \<delta>\<rparr> |:| (TL ! i)) " 
  "\<Gamma> \<turnstile> \<lparr> (ProjR l t)|;| \<delta>\<rparr> |:| R \<Longrightarrow>\<exists>m L TL. \<Gamma> \<turnstile> \<lparr>t |;| \<delta>\<rparr> |:| \<lparr>L|:|TL\<rparr> \<and> index L l = m \<and> TL ! m = R \<and> distinct L \<and> length L = length TL
                              \<and> l \<in> set L"
  "\<Gamma> \<turnstile> \<lparr><|V k|>|;|\<delta>\<rparr> |:| R \<Longrightarrow> \<exists>n. \<Gamma> \<turnstile> \<lparr>(\<delta>^^n) (<|V k|>)|;| id\<rparr> |:| R \<and>  set(patterns ((\<delta>^^n) (<|V k|>))) = {}"
  "\<Gamma> \<turnstile> \<lparr><|RCD L1 PL|>|;|\<delta>\<rparr> |:| R \<Longrightarrow> \<exists>TL. R = \<lparr>L1|:|TL\<rparr> \<and> L1\<noteq>[] \<and> distinct L1 \<and> length PL = length TL \<and> length L1 = length PL \<and>
                                    (\<forall>i< length PL. \<Gamma> \<turnstile> \<lparr><|PL ! i|>|;|\<delta>\<rparr> |:| (TL ! i))"
  "\<Gamma> \<turnstile> \<lparr>Let pattern p := t1 in t2|;|\<delta>1\<rparr> |:| R \<Longrightarrow>\<exists>\<delta> R1. coherent p \<and> Lmatch p t1 \<delta>  \<and> \<Gamma> \<turnstile> \<lparr>t1|;|\<delta>1\<rparr> |:| R1 \<and>
     \<Gamma> \<turnstile> \<lparr>t2|;|(\<delta>1 \<circ> \<delta>)\<rparr> |:| R" 
  "\<Gamma> \<turnstile> \<lparr>inl t as R|;|\<delta>1\<rparr> |:| R \<Longrightarrow>\<exists>A B. R = A|+|B \<and> \<Gamma> \<turnstile> \<lparr>t|;|\<delta>1\<rparr> |:| A"
  "\<Gamma> \<turnstile> \<lparr>inr t as R|;|\<delta>1\<rparr> |:| R \<Longrightarrow>\<exists>A B. R = A|+|B \<and> \<Gamma> \<turnstile> \<lparr>t|;|\<delta>1\<rparr> |:| B"
  "\<Gamma> \<turnstile> \<lparr>Case t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2|;|\<delta>1\<rparr> |:| R \<Longrightarrow>\<exists>A B C. R = C \<and> \<Gamma> \<turnstile> \<lparr>t|;|\<delta>1\<rparr> |:| A|+|B \<and>
                                                          replace x A \<Gamma> \<turnstile> \<lparr>t1|;|\<delta>1\<rparr> |:| C \<and> replace y B \<Gamma> \<turnstile> \<lparr>t2|;|\<delta>1\<rparr> |:| C"
   "\<Gamma> \<turnstile> \<lparr> <l:=t> as R |;| \<delta>1 \<rparr> |:| R \<Longrightarrow>\<exists>L TL i. R=<L|,|TL> \<and> \<Gamma> \<turnstile> \<lparr> t |;| \<delta>1 \<rparr> |:| (TL!i) \<and> l = L!i " 
    " \<Gamma> \<turnstile> \<lparr> Case t of <L1:=I> \<Rightarrow> LT |;| \<delta>1\<rparr> |:| A \<Longrightarrow>\<exists>TL. L1\<noteq>\<emptyset> \<and> length I = length L1 \<and> length L1 = length TL \<and> length L1 = length LT \<and>
      \<Gamma> \<turnstile> \<lparr> t |;| \<delta>1 \<rparr> |:| <L1|,|TL> \<and> (\<forall>i<length L1. replace (I!i) (TL!i) \<Gamma> \<turnstile> \<lparr>(LT!i)|;| \<delta>1\<rparr> |:| A)"
proof -
  assume H:"\<Gamma> \<turnstile> \<lparr> Let var x := t in t1|;|\<delta>\<rparr> |:| R"
  show "\<exists>A B. R = B \<and> \<Gamma> \<turnstile> \<lparr>t|;|\<delta>\<rparr> |:| A \<and> replace x A \<Gamma> \<turnstile> \<lparr>t1|;|\<delta>\<rparr> |:| B"
    using H has_type_LetE
    by (cases "x\<ge> length \<Gamma>", fastforce+)
next
  assume H1: "\<Gamma> \<turnstile> \<lparr>Let pattern p := t1 in t2|;|\<delta>1\<rparr> |:| R"
  show "\<exists>\<delta> R1. coherent p \<and> Lmatch p t1 \<delta> \<and> \<Gamma> \<turnstile> \<lparr>t1|;|\<delta>1\<rparr> |:| R1 \<and> \<Gamma> \<turnstile> \<lparr>t2|;|(\<delta>1 \<circ> \<delta>)\<rparr> |:| R"
    using has_type_LetPE[OF H1]
    by metis
next
  assume H2: "\<Gamma> \<turnstile> \<lparr>Case t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2|;|\<delta>1\<rparr> |:| R"
  show "\<exists>A B C. R = C \<and> \<Gamma> \<turnstile> \<lparr>t|;|\<delta>1\<rparr> |:| A |+| B \<and> replace x A \<Gamma> \<turnstile> \<lparr>t1|;|\<delta>1\<rparr> |:| C \<and> replace y B \<Gamma> \<turnstile> \<lparr>t2|;|\<delta>1\<rparr> |:| C"
    by (cases "length \<Gamma> \<le> x"; cases "length \<Gamma> \<le> y"; insert has_type_CaseSE[OF H2]; metis (full_types) replace.simps)
next
  assume H3:"\<Gamma> \<turnstile> \<lparr>LAbs T1 t2|;|fill \<delta>'\<rparr> |:| R"
  show "\<exists>R2 \<Delta>. R = T1 \<rightarrow> R2 \<and> \<Gamma> |,| T1 \<turnstile> \<lparr>t2|;|fill (shift_L 1 (Suc (nbinder t2)) \<circ> \<Delta>)\<rparr> |:| R2 \<and> fill \<Delta> = fill \<delta>'"
    using has_type_LAbsE[OF H3]
    by metis      
next
  assume H4: "\<Gamma> \<turnstile> \<lparr><l:=t> as R|;|\<delta>1\<rparr> |:| R"
  show  "\<exists>L TL i. R = <L|,|TL> \<and> \<Gamma> \<turnstile> \<lparr>t|;|\<delta>1\<rparr> |:| (TL ! i) \<and> l = L ! i"
    using has_type_VariantE[OF H4]
    by metis    
next
  assume H5: "\<Gamma> \<turnstile> \<lparr>Case t of <L1:=I> \<Rightarrow> LT|;|\<delta>1\<rparr> |:| A"
  have "\<And>TL \<delta>. \<delta>1 = fill \<delta> \<Longrightarrow> length L1 = length TL \<Longrightarrow>\<forall>i<length TL. (if length \<Gamma> \<le> I ! i then \<Gamma> else take (I ! i) \<Gamma> @ \<emptyset> |,| (TL ! i) @ drop (Suc (I ! i)) \<Gamma>) \<turnstile> \<lparr>(LT ! i)|;|fill \<delta>\<rparr> |:| A
         \<Longrightarrow> \<forall>i<length L1. replace (I ! i) (TL ! i) \<Gamma> \<turnstile> \<lparr>(LT ! i)|;|\<delta>1\<rparr> |:| A"
    proof (rule+)
      fix TL \<delta> i
      assume hyps:"\<forall>i<length TL. (if length \<Gamma> \<le> I ! i then \<Gamma> else take (I ! i) \<Gamma> @ \<emptyset> |,| (TL ! i) @ drop (Suc (I ! i)) \<Gamma>) \<turnstile> \<lparr>(LT ! i)|;|fill \<delta>\<rparr> |:| A"
                  "\<delta>1 = fill \<delta>" "i<length L1" "length L1 = length TL"
      then show "replace (I ! i) (TL ! i) \<Gamma> \<turnstile> \<lparr>(LT ! i)|;|\<delta>1\<rparr> |:| A"
        by (cases "length \<Gamma>\<le> I!i", fastforce+)
    qed      
  then show "\<exists>TL. L1 \<noteq> \<emptyset> \<and> length I = length L1 \<and> length L1 = length TL \<and> length L1 = length LT \<and> 
          \<Gamma> \<turnstile> \<lparr>t|;|\<delta>1\<rparr> |:| <L1|,|TL> \<and> (\<forall>i<length L1. replace (I ! i) (TL ! i) \<Gamma> \<turnstile> \<lparr>(LT ! i)|;|\<delta>1\<rparr> |:| A)"
    using has_type_CaseVE[OF H5]
    by metis
qed (auto elim: has_type_L.cases has_type_ProjTE, metis has_type_ProjRE)


lemma[simp]: "nat (int x + 1) = Suc x" by simp
lemma[simp]: "nat (1 + int x) = Suc x" by simp

lemma[simp]: "nat (int x - 1) = x - 1" by simp 


lemma pvars_never_empty:
  "Pvars p \<noteq> \<emptyset>"
sorry


lemma pattern_shift:
  "set(patterns (shift_L d c t)) = set(patterns t)"
by(induction t arbitrary: d c, auto)

lemma pattern_def_fill:
  assumes "same_dom \<delta> S"
  shows "set (patterns (fill \<delta> t)) = set(patterns t) - set S \<union> A" 
sorry


lemma fill_id:
  "id = fill (\<lambda>x. <|V x|>)"
proof 
  fix t
  show "id t = fill (\<lambda>x. <|V x|>) t"
    proof (induction t)
      case (Tuple L)
        thus ?case by (induction L, auto)
    next
      case (Record L TL)
        thus ?case by (induction TL, auto)
    next
      case (Pattern p)
        show ?case
          proof (induction p)
            case (RCD L PL)
              show ?case
                using "same_dom.cases"[of "\<lambda>x. <|V x|>" "list_iter op @ \<emptyset> (map Pvars PL)"]
                by fastforce      
          qed auto
    next
      case (CaseVar t L I LT)
        thus ?case by (induction LT, auto)
    qed auto
qed

lemma fill_fill_comp:
  "fill \<delta> \<circ> fill \<delta>1 = fill (fill \<delta> \<circ> \<delta>1)"
proof (rule)
  fix x
  show "(fill \<delta> \<circ> fill \<delta>1) x= fill (fill \<delta> \<circ> \<delta>1) x"
    proof (induction x arbitrary: \<delta> \<delta>1)
      case (Pattern p)
        show ?case
          proof (induction p)
            case (RCD L PL)
              show ?case
                apply (simp del: "p_instantiate.simps")
                using "p_instantiate.simps"(2) RCD
                sorry
          qed auto
    qed auto
qed

lemma lmatch_gives_fill:
  "Lmatch p t \<delta> \<Longrightarrow> \<exists>\<delta>1. fill \<delta>1 = \<delta>" 
proof (induction rule: Lmatch.induct)
  case (M_RCD L LT F PL)
    show ?case
      using M_RCD(3,7)
      proof (induction F arbitrary:PL)
        case (Nil)
          show ?case 
            using fill_id "BigCirc.simps"(1)
            by metis
      next
        case (Cons f F)
          obtain p PL' where unfold_PL:"PL = p#PL'"
            using Cons(2) length_Suc_conv
            by metis
          then obtain \<Delta> where BigCirc_\<Delta>:"fill \<Delta> = \<Odot> F"
            using Cons(1)[of PL'] Cons(2) Cons(3)[of "_+1"]
            by force
          obtain \<delta>1 where "fill \<delta>1 = f"
            using Cons(3)[of 0] Cons(2)
            by force
          with BigCirc_\<Delta> show ?case
            using fill_fill_comp[of \<delta>1 \<Delta>]
            by fastforce
      qed 
qed auto

lemma pattern_fill_shift:
  "patterns ((fill (shift_L d c \<circ> \<delta>) ^^n) t) = patterns ((fill \<delta> ^^ n) t)"
proof (induction n)
  case (Suc n1)
    show ?case
       sorry
qed auto


lemma weakening :
  fixes \<Gamma>::lcontext  and t::lterm and A R S::ltype and \<delta>::"nat\<Rightarrow>lterm" and x n::nat
  assumes well_typed: "\<Gamma> \<turnstile> \<lparr>t|;|fill \<delta>\<rparr> |:| A" and
          weaker_ctx: " n \<le> length \<Gamma>" 
  shows "insert_nth n S \<Gamma> \<turnstile> \<lparr>shift_L 1 n t|;|fill (shift_L 1 n \<circ> \<delta>)\<rparr> |:| A"
using assms 
proof(induction \<Gamma> t "fill \<delta>" A arbitrary: n \<delta> rule:has_type_L.induct)
  case (has_type_LAbs \<Gamma>1 T1 t2 \<delta>1 T2)
    have A:"shift_L 1 (Suc (nbinder (shift_L 1 (Suc n) t2))) = shift_L 1 (Suc (nbinder t2))" sorry
    have B: "shift_L 1 (Suc (nbinder t2)) \<circ> fill (shift_L 1 (Suc (nbinder t2)) \<circ> \<delta>) = fill (shift_L 2 (Suc (nbinder t2)) \<circ> \<delta>)"
      sorry
    show ?case
      apply simp
      apply rule
      apply (cases "n\<le> Suc (nbinder t2)")
      apply (simp add:A B max_def)
      using has_type_LAbs(2)[where n= "Suc n" and \<delta>= "shift_L 1 (Suc (nbinder t2)) \<circ> \<delta>"]
      
      sorry
      (*using has_type_LAbs has_type_LAbs(3)
      by (auto intro: "has_type_L.intros" simp: nth_append min_def)*)
next 
  case(has_type_Tuple L TL \<Gamma>1 \<delta>1)
    show ?case
      using has_type_Tuple(1,2)
            nth_map[of _ L "shift_L 1 n"] has_type_Tuple(4)[OF _ _ has_type_Tuple(5,6)]
      by (force intro: "has_type_L.intros")+
next
  case (has_type_ProjT i TL \<Gamma>1 t \<delta>1)
    show ?case
      using has_type_ProjT(4)[OF has_type_ProjT(5,6)]
            "has_type_L.intros"(19)[OF has_type_ProjT(1,2)]
      by fastforce
next
  case (has_type_RCD L LT TL \<Gamma> \<delta>1)
    show ?case
      using has_type_RCD(1-4) nth_map[of _ LT "shift_L 1 n"]
            has_type_RCD(6)[OF _ has_type_RCD(7,8)]           
      by (force intro!: "has_type_L.intros"(20))+
next
  case (has_type_Let \<Gamma>1 t1 \<delta>1 A x t2 B)
    have 1:"n\<le>x \<Longrightarrow> ?case"
      proof -
        assume le_x: "n\<le>x"
        show ?case
          using has_type_Let(4-6) le_x
                "has_type_L.intros"(14)[OF has_type_Let(2)[OF has_type_Let(5,6)], of "Suc x"]
          by  (simp add: le_x del: Fun.comp_apply,
                metis insert_nth_take_drop rep_ins replace_inv_length append_Cons append_Nil2 append_eq_append_conv_if)
      qed

    have "n>x \<Longrightarrow> ?case"
      using has_type_Let(4-6) rep_ins2[OF _ has_type_Let(6), of x S A]
            "has_type_L.intros"(14)[OF has_type_Let(2)[OF has_type_Let(5,6)], of x]
      by (simp del: Fun.comp_apply,
            metis append_Cons append_Nil insert_nth_take_drop replace_inv_length)
    with 1 show ?case 
      by auto
next
  case (has_type_PatternVar \<Gamma>1 \<delta>1 m k A)
    have HB: "shift_L 1 n ((fill \<delta>1 ^^ m) (<|V k|>)) = (fill (shift_L 1 n \<circ> \<delta>) ^^ m) (<|V k|>)" sorry
    have HC: "(shift_L 1 n \<circ> (\<lambda>x. <|V x|>)) = (\<lambda>x. <|V x|>)" 
      proof rule
        fix x
        show "(shift_L 1 n \<circ> (\<lambda>x. <|V x|>)) x = (\<lambda>x. <|V x|>) x" 
          using Fun.comp_apply[of "shift_L 1 n" "\<lambda>x. <|V x|>" x]
                "shift_L.simps"(22)
          by (metis (full_types))
      qed
    have 1:"insert_nth n S \<Gamma>1 \<turnstile> \<lparr>(fill (shift_L 1 n \<circ> \<delta>) ^^ m) (<|V k|>)|;|id\<rparr> |:| A" 
      using has_type_PatternVar(2)[OF fill_id has_type_PatternVar(5)]
            HOL.sym[OF fill_id] HB HC
      by simp
    have "set (patterns ((fill (shift_L 1 n \<circ> \<delta>) ^^ m) (<|V k|>))) = {}"
      using has_type_PatternVar(3,4) pattern_fill_shift[of m 1 n \<delta> "<|V k|>"]
      by fastforce  
    with 1 show ?case by (auto intro:"has_type_L.intros"(22)[where \<delta>="(shift_L 1 n \<circ> \<delta>)"])
next
  case (has_type_LetPattern p t1 \<delta>1 \<Gamma>1 \<delta>2 B t2 A)
    have 1:"Lmatch p (shift_L 1 n t1) (shift_L 1 n \<circ> \<delta>1)"
      sorry
    obtain \<delta>' where fill_\<delta>1:"\<delta>1 = fill \<delta>'"
      using lmatch_gives_fill[OF has_type_LetPattern(2)]
      by auto
    have HB:"(fill (shift_L 1 n \<circ> \<delta>) \<circ> (shift_L 1 n \<circ> \<delta>1)) = shift_L 1 n \<circ> (fill \<delta>) \<circ> \<delta>1" sorry
    have HD:"fill \<delta>2 \<circ> \<delta>1 = fill (fill \<delta> \<circ> \<delta>')" 
      using fill_\<delta>1 has_type_LetPattern(7)
      sorry      
    hence 2: "insert_nth n S \<Gamma>1 \<turnstile> \<lparr>shift_L 1 n t2|;|fill (shift_L 1 n \<circ> (fill \<delta> \<circ> \<delta>'))\<rparr> |:| A"
      using has_type_LetPattern(6)[OF _ has_type_LetPattern(8), of "fill \<delta> \<circ> \<delta>'"]      
      by auto
  show ?case
    apply simp
    apply rule
    using has_type_LetPattern(1)
          1 has_type_LetPattern(4)[OF has_type_LetPattern(7,8)]
    apply auto[3]
    using HD has_type_LetPattern(7)
          2
    sorry
    (*take n \<Gamma>1 @ drop n \<Gamma>1 |,| S) \<turnstile> \<lparr>shift_L 1 n t2|;|(shift_L 1 n \<circ> fill (fill \<delta> \<circ> \<delta>'))\<rparr> |:| A*)
next
  case (has_type_Case \<Gamma>1 t \<delta>1 A B x t1 C y t2)
    have A: "(take n \<Gamma>1 @ drop n \<Gamma>1 |,| S) \<turnstile> \<lparr>shift_L 1 n t|;|fill (shift_L 1 n \<circ> \<delta>)\<rparr> |:| A |+| B"
      using has_type_Case(2)[OF has_type_Case(7,8)]
      by auto
    have B1:"n \<le> x \<Longrightarrow> n \<le> y \<Longrightarrow> replace (Suc x) A (insert_nth n S \<Gamma>1) \<turnstile> \<lparr>shift_L 1 n t1|;|fill (shift_L 1 n \<circ> \<delta>)\<rparr> |:| C \<and>
                                  replace (Suc y) B (insert_nth n S \<Gamma>1) \<turnstile> \<lparr>shift_L 1 n t2|;|fill (shift_L 1 n \<circ> \<delta>)\<rparr> |:| C"
      using  has_type_Case(4)[OF has_type_Case(7)] has_type_Case(8)
             has_type_Case(6)[OF has_type_Case(7)]
             rep_ins[of n _ \<Gamma>1 S _] replace_inv_length 
      by metis+
    have B2: " n \<le> x \<Longrightarrow> \<not> n \<le> y \<Longrightarrow> replace (Suc x) A (insert_nth n S \<Gamma>1) \<turnstile> \<lparr>shift_L 1 n t1|;|fill (shift_L 1 n \<circ> \<delta>)\<rparr> |:| C \<and>
                                      replace y B (insert_nth n S \<Gamma>1) \<turnstile> \<lparr>shift_L 1 n t2|;|fill (shift_L 1 n \<circ> \<delta>)\<rparr> |:| C"
      using  has_type_Case(4)[OF has_type_Case(7)] has_type_Case(8)
             has_type_Case(6)[OF has_type_Case(7)] rep_ins2[of y n \<Gamma>1 S B]
             rep_ins[of n x \<Gamma>1 S A] replace_inv_length not_le
      by metis+
    have B3: "\<not> n \<le> x \<Longrightarrow>  n \<le> y \<Longrightarrow> replace x A (insert_nth n S \<Gamma>1) \<turnstile> \<lparr>shift_L 1 n t1|;|fill (shift_L 1 n \<circ> \<delta>)\<rparr> |:| C \<and>
                                      replace (Suc y) B (insert_nth n S \<Gamma>1) \<turnstile> \<lparr>shift_L 1 n t2|;|fill (shift_L 1 n \<circ> \<delta>)\<rparr> |:| C"
      using  has_type_Case(4)[OF has_type_Case(7)] has_type_Case(8)
             has_type_Case(6)[OF has_type_Case(7)] rep_ins2[of x n \<Gamma>1 S A]
             rep_ins[of n y \<Gamma>1 S B] replace_inv_length not_le
      by metis+
    have B4: "\<not> n \<le> x \<Longrightarrow> \<not> n \<le> y \<Longrightarrow> replace x A (insert_nth n S \<Gamma>1) \<turnstile> \<lparr>shift_L 1 n t1|;|fill (shift_L 1 n \<circ> \<delta>)\<rparr> |:| C \<and>
                                      replace y B (insert_nth n S \<Gamma>1) \<turnstile> \<lparr>shift_L 1 n t2|;|fill (shift_L 1 n \<circ> \<delta>)\<rparr> |:| C"
      using  has_type_Case(4)[OF has_type_Case(7)] has_type_Case(8)
             has_type_Case(6)[OF has_type_Case(7)] rep_ins2[of _ n \<Gamma>1 S _]
             replace_inv_length not_le
      by metis+
    show ?case
      by (auto)(insert A B1 B2 B3 B4 "has_type_L.intros"(27), force+)
next
  case (has_type_CaseV L I TL LT \<Gamma> t \<delta>1 A)
    have branches_wtyped:"\<forall>i<length L.
       replace (map (\<lambda>x. if n \<le> x then nat (int x + 1) else x) I ! i) (TL ! i) (take n \<Gamma> @ drop n \<Gamma> |,| S)
       \<turnstile> \<lparr>(map (shift_L 1 n) LT ! i)|;|fill (shift_L 1 n \<circ> \<delta>)\<rparr> |:| A"
      proof (rule+)
        fix i
        assume H:"i<length L"
        have " (\<And>x xa. fill \<delta>1 = fill x \<Longrightarrow> xa\<le>length (replace (I ! i) (TL ! i) \<Gamma>) \<Longrightarrow>
                   insert_nth xa S (replace (I ! i) (TL ! i) \<Gamma>) \<turnstile> \<lparr>shift_L 1 xa (LT ! i)|;|fill (shift_L 1 xa \<circ> x)\<rparr> |:| A)"
          using has_type_CaseV(7) H
          by auto
        then have branches_type:"insert_nth n S (replace (I ! i) (TL ! i) \<Gamma>) \<turnstile> \<lparr>shift_L 1 n (LT ! i)|;|fill (shift_L 1 n \<circ> \<delta>)\<rparr> |:| A"
          using  has_type_CaseV(8,9) 
                 replace_inv_length[of "I!i" "TL!i" \<Gamma>]
          by presburger
        have 1:"n\<le> I!i \<Longrightarrow> replace (map (\<lambda>x. if n \<le> x then nat (int x + 1) else x) I ! i) (TL ! i) (take n \<Gamma> @ drop n \<Gamma> |,| S)
                \<turnstile> \<lparr>(map (shift_L 1 n) LT ! i)|;|fill (shift_L 1 n \<circ> \<delta>)\<rparr> |:| A"
          using has_type_CaseV(1,2,9) H        
          proof -
            
            assume hyps:"n \<le> I ! i" "L \<noteq> \<emptyset>" "length I = length L" "n \<le> length \<Gamma>" "i < length L"
            
            from branches_type
              have "replace (Suc (I ! i)) (TL ! i) (take n \<Gamma> @ drop n \<Gamma> |,| S) \<turnstile> \<lparr>(map (shift_L 1 n) LT ! i)|;|fill (shift_L 1 n \<circ> \<delta>)\<rparr> |:| A"
              using rep_ins[OF hyps(1,4),of S "TL!i"] H has_type_CaseV(4)
              by auto
            
            then show ?thesis by (simp add: hyps)        
          qed
        have  "\<not> n\<le> I!i \<Longrightarrow> replace (map (\<lambda>x. if n \<le> x then nat (int x + 1) else x) I ! i) (TL ! i) (take n \<Gamma> @ drop n \<Gamma> |,| S)
                \<turnstile> \<lparr>(map (shift_L 1 n) LT ! i)|;|fill (shift_L 1 n \<circ> \<delta>)\<rparr> |:| A"
          using has_type_CaseV(1,2,9) H        
          proof -
            
            assume hyps:"\<not>n \<le> I ! i" "L \<noteq> \<emptyset>" "length I = length L" "n \<le> length \<Gamma>" "i < length L"
            
            from branches_type
              have  "replace (I ! i) (TL ! i) (take n \<Gamma> @ drop n \<Gamma> |,| S) \<turnstile> \<lparr>(map (shift_L 1 n) LT ! i)|;|fill (shift_L 1 n \<circ> \<delta>)\<rparr> |:| A"
              using rep_ins2[OF _ hyps(4),of "I!i" S "TL!i"] H has_type_CaseV(4) hyps(1) not_le[of n "I!i"]
              by auto

            then show ?thesis by (simp add: hyps)        
          qed

        with 1 show "replace (map (\<lambda>x. if n \<le> x then nat (int x + 1) else x) I ! i) (TL ! i) (take n \<Gamma> @ drop n \<Gamma> |,| S)
         \<turnstile> \<lparr>(map (shift_L 1 n) LT ! i)|;|fill (shift_L 1 n \<circ> \<delta>)\<rparr> |:| A"
          by blast
      qed 
    show ?case
      using has_type_CaseV(1-4) has_type_CaseV(6)[OF has_type_CaseV(8,9)]
            branches_wtyped
      by (force intro!: "has_type_L.intros"(29))+      
qed (auto intro!: has_type_L.intros simp: nth_append min_def)

lemma fill_keep_value:
  "is_value_L v \<Longrightarrow> is_value_L (fill \<delta> v)"
by(induction v rule: is_value_L.induct, auto intro: "is_value_L.intros" )

lemma canonical_forms:
  "is_value_L v \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>v|;|\<delta>\<rparr> |:| Bool \<Longrightarrow> v = LTrue \<or> v = LFalse"
  "is_value_L v \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>v|;|\<delta>\<rparr> |:| T1 \<rightarrow> T2 \<Longrightarrow> \<exists>t n. v = LAbs T1 t"
  "is_value_L v \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>v|;|\<delta>\<rparr> |:| Unit \<Longrightarrow> v = unit"
  "is_value_L v \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>v|;|\<delta>\<rparr> |:| A |\<times>| B \<Longrightarrow> \<exists>v1 v2. is_value_L v1 \<and> is_value_L v2 \<and> v= \<lbrace>v1,v2\<rbrace>"
  "is_value_L v \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>v|;|\<delta>\<rparr> |:| \<lparr>TL\<rparr> \<Longrightarrow> \<exists>L. is_value_L (Tuple L) \<and> v = Tuple L"
  "is_value_L v \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>v|;|\<delta>\<rparr> |:| \<lparr>L|:|TL\<rparr> \<Longrightarrow> \<exists>L LT. is_value_L (Record L LT) \<and> v = (Record L LT)" 
  "is_value_L v \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>v|;|\<delta>\<rparr> |:| A|+|B \<Longrightarrow> (\<exists>v1. is_value_L v1 \<and> v = inl v1 as A|+|B) \<or> (\<exists>v1. v = inr v1 as A|+|B \<and> is_value_L v1)" 
  "is_value_L v \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>v|;|\<delta>\<rparr> |:| Nat \<Longrightarrow> \<exists>n. v = LNat n"
proof -
  assume  val: "is_value_L v" and 
          typed: "\<Gamma> \<turnstile> \<lparr>v|;|\<delta>\<rparr> |:| A|+|B"
  show "(\<exists>v1. is_value_L v1 \<and> v = inl v1 as A|+|B) \<or> (\<exists>v1. v = inr v1 as A|+|B \<and> is_value_L v1)"
    using val typed
    by (induction rule: is_value_L.induct, auto elim: "has_type_L.cases")
qed (auto elim: "is_value_L.cases" "has_type_L.cases")  

end
