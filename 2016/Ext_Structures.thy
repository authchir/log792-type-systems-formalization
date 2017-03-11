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
    "l\<in>set L \<Longrightarrow> index L l = i \<Longrightarrow> eval1_L (Case (<l:=v> as A) of <L:=I> \<Rightarrow> LT) (shift_L (-1) (I!i) (subst_L (I!i) (shift_L 1 (I!i) v) (LT!i)))" |
  eval1_L_CaseV:
    "eval1_L t t' \<Longrightarrow> eval1_L (Case t of <L:=I> \<Rightarrow> LT) (Case t' of <L:=I> \<Rightarrow> LT)" |
  eval1_L_Variant:
    "eval1_L t t' \<Longrightarrow> eval1_L (<l:=t> as A) (<l:=t'> as A)" |
  eval1_L_FixBeta:
    "eval1_L (fix (LAbs A t)) (shift_L (-1) 0 (subst_L 0 (shift_L 1 0 (fix LAbs A t)) t))"|
  eval1_LFix_step:
    "eval1_L t t' \<Longrightarrow> eval1_L (fix t) (fix t')" |
  eval1_Lcons1:
    "eval1_L t t1 \<Longrightarrow> eval1_L (Lcons A t t') (Lcons A t1 t')"|
  eval1_Lcons2:
    "is_value_L v \<Longrightarrow> eval1_L t' t1 \<Longrightarrow> eval1_L (Lcons A v t') (Lcons A v t1)"|
  eval1_Lisnil_nil:
    "eval1_L (Lisnil A (Lnil A)) LTrue"|
   eval1_Lisnil_cons:
    "is_value_L v1 \<Longrightarrow> is_value_L v2 \<Longrightarrow> eval1_L (Lisnil A (Lcons A v1 v2)) LFalse"|
  eval1_Lisnil_step:
    "eval1_L t t' \<Longrightarrow> eval1_L (Lisnil A t) (Lisnil A t')"|
  eval1_Lhead_cons:
    "is_value_L v1 \<Longrightarrow> is_value_L v2 \<Longrightarrow> eval1_L (Lhead A (Lcons A v1 v2)) v1" | 
  eval1_Lhead_step:
    "eval1_L t t1 \<Longrightarrow> eval1_L (Lhead A t) (Lhead A t1)" |
  eval1_Ltail_cons:
    "is_value_L v1 \<Longrightarrow> is_value_L v2 \<Longrightarrow> eval1_L (Ltail A (Lcons A v1 v2)) v2" | 
  eval1_Ltail_step:
    "eval1_L t t1 \<Longrightarrow> eval1_L (Ltail A t) (Ltail A t1)" 

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


inductive has_type_L :: "lcontext \<Rightarrow> lterm \<Rightarrow> pcontext \<Rightarrow> bool \<Rightarrow> ltype \<Rightarrow> bool" ("((_)/ \<turnstile> \<lparr>(_)|;|(_),(_)\<rparr>/ |:| (_))" [150, 150, 150, 150,150] 150) where
  -- "Rules relating to the type of Booleans"
  has_type_LTrue:
    "\<Gamma> \<turnstile> \<lparr>LTrue|;| \<sigma>, f\<rparr> |:| Bool" |
  has_type_LFalse:
    "\<Gamma> \<turnstile> \<lparr>LFalse|;| \<sigma>, f\<rparr> |:| Bool" |
  has_type_LIf:
    "\<Gamma> \<turnstile> \<lparr>t1|;| \<sigma>,f\<rparr> |:| Bool \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t2|;| \<sigma>,f\<rparr> |:| T' \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t3|;| \<sigma>,f\<rparr> |:| T' \<Longrightarrow> 
      \<Gamma> \<turnstile> \<lparr>LIf t1 t2 t3|;| \<sigma>,f\<rparr> |:| T'" |

  -- \<open>Rules relating to the type of the constructs of the $\lambda$-calculus\<close>
  has_type_LVar:
    "(x, T') |\<in>| \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>LVar x|;| \<sigma>,f\<rparr> |:| (T')" |
  has_type_LAbs:
    "(\<Gamma> |,| T1) \<turnstile> \<lparr>t2|;| \<sigma>,f\<rparr> |:| T2 \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>LAbs T1 t2|;| \<sigma>,f\<rparr> |:| (T1 \<rightarrow> T2)" |
  has_type_LApp:
    "\<Gamma> \<turnstile> \<lparr>t1|;| \<sigma>,f\<rparr> |:| (T11 \<rightarrow> T12) \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t2|;| \<sigma>,f\<rparr> |:| T11 \<Longrightarrow> 
      \<Gamma> \<turnstile> \<lparr>LApp t1 t2|;| \<sigma>,f\<rparr> |:| T12" |  
  has_type_LUnit:
    "\<Gamma> \<turnstile> \<lparr>unit|;| \<sigma>,f\<rparr> |:| Unit " |  
  has_type_LSeq:
    "\<Gamma> \<turnstile> \<lparr>t1|;| \<sigma>,f\<rparr> |:| Unit \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t2|;| \<sigma>,f\<rparr> |:| A \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Seq t1 t2|;| \<sigma>,f\<rparr> |:| A" |
  has_type_LAscribe:
    "\<Gamma> \<turnstile> \<lparr>t1|;| \<sigma>,f\<rparr> |:| A \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t1 as A|;| \<sigma>,f\<rparr> |:| A" |
  has_type_Let:
    "x\<le>length \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t1|;| \<sigma>,f\<rparr> |:| A \<Longrightarrow> (insert_nth x A \<Gamma>) \<turnstile> \<lparr> t2|;| \<sigma>,f\<rparr> |:| B \<Longrightarrow> 
      \<Gamma> \<turnstile> \<lparr>Let var x := t1 in t2|;| \<sigma>,f\<rparr> |:| B" |
  has_type_Pair:
    "\<Gamma> \<turnstile> \<lparr>t1|;| \<sigma>,f\<rparr> |:| A \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t2|;| \<sigma>,f\<rparr> |:| B \<Longrightarrow> 
      \<Gamma> \<turnstile> \<lparr>\<lbrace>t1,t2\<rbrace>|;| \<sigma>,f\<rparr> |:| A |\<times>| B" |
  has_type_Proj1:
    "\<Gamma> \<turnstile> \<lparr>t1|;| \<sigma>,f\<rparr> |:| A |\<times>| B \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>\<pi>1 t1|;| \<sigma>,f\<rparr> |:| A" |
  has_type_Proj2:
    "\<Gamma> \<turnstile> \<lparr>t1|;| \<sigma>,f\<rparr> |:| A |\<times>| B \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>\<pi>2 t1|;| \<sigma>,f\<rparr> |:| B" |
  has_type_Tuple:
    "L\<noteq>[] \<Longrightarrow> length L = length TL \<Longrightarrow> 
      (\<And>i. 0\<le>i \<Longrightarrow> i< length L \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>(L ! i)|;| \<sigma>,f\<rparr> |:| (TL ! i))
      \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Tuple L|;| \<sigma>,f\<rparr> |:| \<lparr>TL\<rparr>" |
  has_type_ProjT:
    "1\<le>i \<Longrightarrow> i\<le> length TL \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t|;| \<sigma>,f\<rparr> |:| \<lparr>TL\<rparr> \<Longrightarrow> 
      \<Gamma> \<turnstile> \<lparr>\<Pi> i t|;| \<sigma>,f\<rparr> |:| (TL ! (i-1))" |
  has_type_RCD:
    "L\<noteq>[] \<Longrightarrow> distinct L \<Longrightarrow> length LT = length TL \<Longrightarrow> length L = length LT \<Longrightarrow>
      (\<And>i. i< length LT \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>(LT ! i)|;| \<sigma>,f\<rparr> |:| (TL ! i))
      \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Record L LT|;| \<sigma>,f\<rparr> |:| \<lparr>L|:|TL\<rparr>" |
  has_type_ProjR:
    "distinct L1 \<Longrightarrow> l\<in> set L1  \<Longrightarrow> length L1 = length TL \<Longrightarrow> 
      \<Gamma> \<turnstile> \<lparr>t|;| \<sigma>,f\<rparr> |:| \<lparr>L1|:|TL\<rparr> \<Longrightarrow> 
      \<Gamma> \<turnstile> \<lparr>ProjR l t|;| \<sigma>,f\<rparr> |:| (TL ! index L1 l)" |
  has_type_PatternVar:
    "\<sigma> k = Some A \<Longrightarrow> \<Gamma> \<turnstile> \<lparr><|V k as A|>|;| \<sigma>,f\<rparr> |:| A" |
  has_type_LetPattern:
    "coherent p B\<Longrightarrow> Lmatch_Type p \<sigma> \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t1|;| \<sigma>1,f\<rparr> |:| B \<Longrightarrow>
     \<Gamma> \<turnstile> \<lparr>t2|;|(\<sigma>1 ++ \<sigma>), f\<rparr> |:| A \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Let pattern p := t1 in t2|;| \<sigma>1, f\<rparr> |:| A" |
  has_type_Inl:
    "\<Gamma> \<turnstile> \<lparr>t1|;| \<sigma>1,f\<rparr> |:| A \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>inl t1 as A|+|B |;|\<sigma>1,f\<rparr> |:| A|+|B" |
  has_type_Inr:
    "\<Gamma> \<turnstile> \<lparr>t1|;| \<sigma>1,f\<rparr> |:| B \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>inr t1 as A|+|B |;| \<sigma>1,f\<rparr> |:| A|+|B" |
  has_type_Case:
    "x\<le>length \<Gamma> \<Longrightarrow> y\<le>length \<Gamma> \<Longrightarrow>\<Gamma> \<turnstile> \<lparr> t|;| \<sigma>1,f \<rparr> |:| A|+|B \<Longrightarrow> insert_nth x A \<Gamma> \<turnstile> \<lparr>t1|;| \<sigma>1,f\<rparr> |:| C \<Longrightarrow>
     insert_nth y B \<Gamma> \<turnstile> \<lparr>t2|;| \<sigma>1,f\<rparr> |:| C \<Longrightarrow> 
     \<Gamma> \<turnstile> \<lparr>Case t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2 |;| \<sigma>1,f\<rparr> |:| C" |
  has_type_Variant:
    "i<length L \<Longrightarrow>distinct L \<Longrightarrow> length L=length TL \<Longrightarrow> \<Gamma> \<turnstile> \<lparr> t |;| \<sigma>,f \<rparr> |:| (TL!i) \<Longrightarrow> 
      \<Gamma> \<turnstile> \<lparr> <(L!i):=t> as <L|,|TL> |;|\<sigma>,f \<rparr> |:| <L|,|TL>" |
  has_type_CaseV:
    " L\<noteq>\<emptyset> \<Longrightarrow> distinct L \<Longrightarrow> length I = length L \<Longrightarrow> length L = length TL \<Longrightarrow> 
      length L = length LT \<Longrightarrow> 
      \<Gamma> \<turnstile> \<lparr> t |;| \<sigma>,f \<rparr> |:| <L|,|TL> \<Longrightarrow> 
      (\<forall>i<length L. insert_nth (I!i) (TL!i) \<Gamma> \<turnstile> \<lparr>(LT!i)|;| \<sigma>,f\<rparr> |:| A \<and> I!i\<le>length \<Gamma>) \<Longrightarrow>
      \<Gamma> \<turnstile> \<lparr> Case t of <L:=I> \<Rightarrow> LT |;| \<sigma>,f\<rparr> |:| A" |
  has_type_Fix:
    "\<Gamma> \<turnstile> \<lparr> t |;| \<sigma>,f\<rparr> |:| A\<rightarrow>A \<Longrightarrow> \<Gamma> \<turnstile> \<lparr> fix t |;| \<sigma>,f\<rparr> |:| A"|
  has_type_Nil:
    "\<Gamma> \<turnstile> \<lparr> Lnil A |;| \<sigma>, False\<rparr> |:| \<lambda>List A"|
  has_type_isNil:
    "\<Gamma> \<turnstile> \<lparr> t|;| \<sigma>,f \<rparr> |:| \<lambda>List A \<Longrightarrow>\<Gamma> \<turnstile> \<lparr> Lisnil A t|;| \<sigma>,f \<rparr> |:| Bool"| 
  has_type_head:
    "\<Gamma> \<turnstile> \<lparr> t|;| \<sigma>,True \<rparr> |:| \<lambda>List A \<Longrightarrow>\<Gamma> \<turnstile> \<lparr> Lhead A t|;| \<sigma>,f \<rparr> |:| A"| 
  has_type_tail:
    "\<Gamma> \<turnstile> \<lparr> t|;| \<sigma>,True \<rparr> |:| \<lambda>List A \<Longrightarrow>\<Gamma> \<turnstile> \<lparr> Ltail A t|;| \<sigma>,f \<rparr> |:| \<lambda>List A"| 
  has_type_cons:
    "\<Gamma> \<turnstile> \<lparr> t|;| \<sigma>,f \<rparr> |:| A \<Longrightarrow> \<Gamma> \<turnstile> \<lparr> t' |;| \<sigma>,f \<rparr> |:| \<lambda>List A \<Longrightarrow>
      \<Gamma> \<turnstile> \<lparr> Lcons A t t'|;| \<sigma>,f \<rparr> |:| \<lambda>List A"  

inductive_cases has_type_LetE : "\<Gamma> \<turnstile> \<lparr> Let var x := t1 in t2|;|\<sigma>,f\<rparr>  |:| B"
inductive_cases has_type_ProjTE: "\<Gamma> \<turnstile> \<lparr> \<Pi> i t|;|\<sigma>1,f\<rparr> |:| R"
inductive_cases has_type_ProjRE: "\<Gamma> \<turnstile> \<lparr> ProjR l t|;|\<sigma>1,f\<rparr> |:| R"
inductive_cases has_type_LetPE: "\<Gamma> \<turnstile> \<lparr>Let pattern p := t1 in t2|;|\<sigma>1,f\<rparr> |:| A"
inductive_cases has_type_CaseSE: "\<Gamma> \<turnstile> \<lparr>Case t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2|;|\<sigma>1,f\<rparr> |:| R"
inductive_cases has_type_CaseVE: "\<Gamma> \<turnstile> \<lparr>Case t of <L:=I> \<Rightarrow> LT|;|\<sigma>1,f\<rparr> |:| R"
inductive_cases has_type_LAbsE: "\<Gamma> \<turnstile> \<lparr>LAbs T1 t2|;|\<sigma>1,f\<rparr> |:| R"
inductive_cases has_type_VariantE: "\<Gamma> \<turnstile> \<lparr><l:=t> as R1 |;|\<sigma>1,f\<rparr> |:| R"

lemma record_patterns_characterisation:
  "set (patterns (<|RCD L PL|>)) \<subseteq> S \<Longrightarrow> x \<in> set PL \<Longrightarrow> set(patterns (<|x|>)) \<subseteq> S"
by (induction PL arbitrary: S x, auto) 

lemma inversion:
  "\<Gamma> \<turnstile> \<lparr> LTrue |;| \<sigma>,f\<rparr> |:| R \<Longrightarrow> R = Bool"
  "\<Gamma> \<turnstile> \<lparr> LFalse |;| \<sigma>,f\<rparr> |:| R \<Longrightarrow> R = Bool"
  "\<Gamma> \<turnstile> \<lparr> LIf t1 t2 t3 |;| \<sigma>,f\<rparr> |:| R \<Longrightarrow>  \<Gamma> \<turnstile> \<lparr>t1|;| \<sigma>,f\<rparr> |:| Bool \<and> \<Gamma> \<turnstile> \<lparr>t2|;| \<sigma>,f\<rparr> |:| R \<and> \<Gamma> \<turnstile> \<lparr>t3|;| \<sigma>,f\<rparr> |:| R"
  "\<Gamma> \<turnstile> \<lparr> LVar x|;| \<sigma>,f\<rparr> |:| R \<Longrightarrow> (x, R) |\<in>| \<Gamma>"
  "\<Gamma> \<turnstile> \<lparr> LAbs T1 t2 |;| \<sigma>,f\<rparr> |:| R \<Longrightarrow> \<exists>R2. R = T1 \<rightarrow> R2 \<and>  \<Gamma> |,| T1 \<turnstile> \<lparr>t2|;| \<sigma>,f\<rparr> |:| R2 "
  "\<Gamma> \<turnstile> \<lparr> LApp t1 t2 |;| \<sigma>,f\<rparr> |:| R \<Longrightarrow> \<exists>T11. \<Gamma> \<turnstile> \<lparr>t1|;|\<sigma>,f\<rparr> |:| T11 \<rightarrow> R \<and> \<Gamma> \<turnstile> \<lparr>t2|;| \<sigma>,f\<rparr> |:| T11"
  "\<Gamma> \<turnstile> \<lparr> unit|;| \<sigma>,f\<rparr> |:| R \<Longrightarrow> R = Unit"
  "\<Gamma> \<turnstile> \<lparr> Seq t1 t2 |;| \<sigma>,f\<rparr> |:| R \<Longrightarrow> \<exists>A. R = A \<and> \<Gamma> \<turnstile> \<lparr>t2|;| \<sigma>,f\<rparr> |:| A \<and> \<Gamma> \<turnstile> \<lparr>t1|;| \<sigma>,f\<rparr> |:| Unit"
  "\<Gamma> \<turnstile> \<lparr> t as A |;| \<sigma>,f\<rparr> |:| R \<Longrightarrow> R = A \<and> \<Gamma> \<turnstile> \<lparr> t |;| \<sigma>,f\<rparr> |:| A"
  "\<Gamma> \<turnstile> \<lparr> Let var x := t in t1 |;| \<sigma>,f\<rparr> |:| R \<Longrightarrow> \<exists>A B. R = B \<and> \<Gamma> \<turnstile> \<lparr> t|;| \<sigma>,f\<rparr> |:| A \<and> x\<le>length \<Gamma> \<and> (insert_nth x A \<Gamma>) \<turnstile> \<lparr>t1|;| \<sigma>,f\<rparr> |:| B"
  "\<Gamma> \<turnstile> \<lparr> \<lbrace>t1,t2\<rbrace>|;| \<sigma>,f\<rparr> |:| R \<Longrightarrow> \<exists>A B. \<Gamma> \<turnstile> \<lparr> t1|;| \<sigma>,f\<rparr> |:| A \<and> \<Gamma> \<turnstile> \<lparr> t2|;| \<sigma>,f\<rparr> |:| B \<and> R = A |\<times>| B"
  "\<Gamma> \<turnstile> \<lparr> \<pi>1 t|;| \<sigma>,f1\<rparr> |:| R \<Longrightarrow> \<exists>A B f. f=f1 \<and> \<Gamma> \<turnstile> \<lparr> t|;| \<sigma>,f\<rparr> |:| A |\<times>| B \<and> R = A"
  "\<Gamma> \<turnstile> \<lparr> \<pi>2 t|;| \<sigma>,f\<rparr> |:| R \<Longrightarrow> \<exists>A B. \<Gamma> \<turnstile> \<lparr> t|;| \<sigma>,f\<rparr> |:| A |\<times>| B \<and> R = B"
  "\<Gamma> \<turnstile> \<lparr> Tuple L|;| \<sigma>,f\<rparr> |:| R \<Longrightarrow> \<exists>TL. length L = length TL \<and> (\<forall>i. 0\<le>i \<longrightarrow> i< length L \<longrightarrow> \<Gamma> \<turnstile> \<lparr>(L ! i)|;| \<sigma>,f\<rparr> |:| (TL ! i)) \<and> R = \<lparr>TL\<rparr>"
  "\<Gamma> \<turnstile> \<lparr> (\<Pi> i t)|;| \<sigma>,f\<rparr> |:| R \<Longrightarrow> \<exists>TL. R = (TL ! (i-1)) \<and> \<Gamma> \<turnstile> \<lparr>t|;| \<sigma>,f\<rparr> |:| \<lparr>TL\<rparr> \<and> 1\<le>i \<and> i\<le> length TL"
  "\<Gamma> \<turnstile> \<lparr> (Record L1 LT)|;| \<sigma>,f\<rparr> |:| R \<Longrightarrow> \<exists>TL. R = \<lparr>L1|:|TL\<rparr> \<and> length TL = length LT \<and> length L1 = length LT \<and> distinct L1 \<and> 
                                    (\<forall>i. 0\<le>i \<longrightarrow> i< length LT \<longrightarrow> \<Gamma> \<turnstile> \<lparr> (LT ! i)|;| \<sigma>,f\<rparr> |:| (TL ! i)) " 
  "\<Gamma> \<turnstile> \<lparr> (ProjR l t)|;| \<sigma>,f\<rparr> |:| R \<Longrightarrow>\<exists>m L TL. \<Gamma> \<turnstile> \<lparr>t |;| \<sigma>,f\<rparr> |:| \<lparr>L|:|TL\<rparr> \<and> index L l = m \<and> TL ! m = R \<and> distinct L \<and> length L = length TL
                              \<and> l \<in> set L"
  "\<Gamma> \<turnstile> \<lparr><|V k as A|>|;|\<sigma>,f\<rparr> |:| R \<Longrightarrow>R=A \<and> \<sigma> k = Some A"
  "\<Gamma> \<turnstile> \<lparr>Let pattern p := t1 in t2|;|\<sigma>1,f\<rparr> |:| R \<Longrightarrow>\<exists>\<sigma> B. coherent p B\<and> Lmatch_Type p \<sigma>  \<and> \<Gamma> \<turnstile> \<lparr>t1|;|\<sigma>1,f\<rparr> |:| B \<and>
                                                  \<Gamma> \<turnstile> \<lparr>t2|;|(\<sigma>1 ++  \<sigma>), f\<rparr> |:| R" 
  "\<Gamma> \<turnstile> \<lparr>inl t as R1|;|\<sigma>1,f\<rparr> |:| R \<Longrightarrow>R1 = R \<and> (\<exists>A B. R = A|+|B \<and> \<Gamma> \<turnstile> \<lparr>t|;|\<sigma>1,f\<rparr> |:| A)"
  "\<Gamma> \<turnstile> \<lparr>inr t as R1|;|\<sigma>1,f\<rparr> |:| R \<Longrightarrow>R1 = R \<and> (\<exists>A B. R = A|+|B \<and> \<Gamma> \<turnstile> \<lparr>t|;|\<sigma>1,f\<rparr> |:| B)"
  "\<Gamma> \<turnstile> \<lparr>Case t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2|;|\<sigma>1,f\<rparr> |:| R \<Longrightarrow>\<exists>A B C. R = C \<and> \<Gamma> \<turnstile> \<lparr>t|;|\<sigma>1,f\<rparr> |:| A|+|B \<and> x\<le>length \<Gamma> \<and> y\<le>length \<Gamma> \<and>
                                                          insert_nth x A \<Gamma> \<turnstile> \<lparr>t1|;|\<sigma>1,f\<rparr> |:| C \<and> insert_nth y B \<Gamma> \<turnstile> \<lparr>t2|;|\<sigma>1,f\<rparr> |:| C"
   "\<Gamma> \<turnstile> \<lparr> <l:=t> as R1 |;| \<sigma>1,f \<rparr> |:| R \<Longrightarrow>R=R1 \<and> (\<exists>L TL i. R=<L|,|TL> \<and> \<Gamma> \<turnstile> \<lparr> t |;| \<sigma>1,f \<rparr> |:| (TL!i) \<and> l = L!i \<and> i<length L \<and> length L = length TL \<and> distinct L)" 
    " \<Gamma> \<turnstile> \<lparr> Case t of <L1:=I> \<Rightarrow> LT |;| \<sigma>1,f\<rparr> |:| A \<Longrightarrow>\<exists>TL. L1\<noteq>\<emptyset> \<and> length I = length L1 \<and> length L1 = length TL \<and> length L1 = length LT \<and> distinct L1 \<and>
      \<Gamma> \<turnstile> \<lparr> t |;| \<sigma>1,f \<rparr> |:| <L1|,|TL> \<and> (\<forall>i<length L1. insert_nth (I!i) (TL!i) \<Gamma> \<turnstile> \<lparr>(LT!i)|;| \<sigma>1,f\<rparr> |:| A \<and> I!i\<le>length \<Gamma>)"
   "\<Gamma> \<turnstile> \<lparr> fix t |;| \<sigma>,f\<rparr> |:| A \<Longrightarrow> \<Gamma> \<turnstile> \<lparr> t |;| \<sigma>,f\<rparr> |:| A\<rightarrow>A"
   "\<Gamma> \<turnstile> \<lparr> Lnil A |;| \<sigma>,f\<rparr> |:| R \<Longrightarrow> R = (\<lambda>List A) \<and> f=False"
   "\<Gamma> \<turnstile> \<lparr> Lhead A t |;| \<sigma>,f\<rparr> |:| R \<Longrightarrow> R = A \<and> \<Gamma> \<turnstile> \<lparr> t |;| \<sigma>, True\<rparr> |:| \<lambda>List A"
   "\<Gamma> \<turnstile> \<lparr> Lisnil A t |;| \<sigma>,f\<rparr> |:| R \<Longrightarrow> R = Bool \<and> \<Gamma> \<turnstile> \<lparr> t |;| \<sigma>,f\<rparr> |:| \<lambda>List A"
   "\<Gamma> \<turnstile> \<lparr> Ltail A t |;| \<sigma>,f\<rparr> |:| R \<Longrightarrow> R = (\<lambda>List A) \<and> \<Gamma> \<turnstile> \<lparr> t |;| \<sigma>, True\<rparr> |:| \<lambda>List A"
   "\<Gamma> \<turnstile> \<lparr> Lcons A t t'|;| \<sigma>,f\<rparr> |:| R \<Longrightarrow> R = (\<lambda>List A) \<and> \<Gamma> \<turnstile> \<lparr> t' |;| \<sigma>,f\<rparr> |:| (\<lambda>List A) \<and> 
                                        \<Gamma> \<turnstile> \<lparr> t |;| \<sigma>,f\<rparr> |:| A"
proof -
  assume H:"\<Gamma> \<turnstile> \<lparr> Let var x := t in t1|;|\<sigma>,f\<rparr> |:| R"
  show " \<exists>A B. R = B \<and> \<Gamma> \<turnstile> \<lparr> t|;| \<sigma>,f\<rparr> |:| A \<and>x\<le>length \<Gamma>\<and> (insert_nth x A \<Gamma>) \<turnstile> \<lparr>t1|;| \<sigma>,f\<rparr> |:| B"
    using has_type_LetE[OF H] 
    by fastforce 
next
  assume H1: "\<Gamma> \<turnstile> \<lparr>Let pattern p := t1 in t2|;|\<sigma>1,f\<rparr> |:| R"
  show "\<exists>\<sigma> B. coherent p B \<and> Lmatch_Type p \<sigma>  \<and>  \<Gamma> \<turnstile> \<lparr>t1|;|\<sigma>1,f\<rparr> |:| B \<and>  \<Gamma> \<turnstile> \<lparr>t2|;|(\<sigma>1 ++ \<sigma>),f\<rparr> |:| R"
    using has_type_LetPE[OF H1]
    by metis
next
  assume H2: "\<Gamma> \<turnstile> \<lparr>Case t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2|;|\<sigma>1,f\<rparr> |:| R"
  show "\<exists>A B C. R = C \<and> \<Gamma> \<turnstile> \<lparr>t|;|\<sigma>1,f\<rparr> |:| A |+| B \<and> x\<le>length \<Gamma> \<and> y\<le>length \<Gamma> \<and> insert_nth x A \<Gamma> \<turnstile> \<lparr>t1|;|\<sigma>1,f\<rparr> |:| C \<and> insert_nth y B \<Gamma> \<turnstile> \<lparr>t2|;|\<sigma>1,f\<rparr> |:| C"
    using has_type_CaseSE[OF H2]
    by fastforce
next
  assume H4: "\<Gamma> \<turnstile> \<lparr><l:=t> as R1|;|\<sigma>1,f\<rparr> |:| R"
  show  "R=R1 \<and> (\<exists>L TL i. R = <L|,|TL> \<and> \<Gamma> \<turnstile> \<lparr>t|;|\<sigma>1,f\<rparr> |:| (TL ! i) \<and> l = L ! i \<and> i<length L \<and> length L = length TL \<and> distinct L)"
    using has_type_VariantE[OF H4]
    by metis    
next
  assume H5: "\<Gamma> \<turnstile> \<lparr>Case t of <L1:=I> \<Rightarrow> LT|;|\<sigma>1,f\<rparr> |:| A"
  show "\<exists>TL. L1\<noteq>\<emptyset> \<and> length I = length L1 \<and> length L1 = length TL \<and> length L1 = length LT \<and> distinct L1 \<and>
      \<Gamma> \<turnstile> \<lparr> t |;| \<sigma>1,f \<rparr> |:| <L1|,|TL> \<and> (\<forall>i<length L1. insert_nth (I!i) (TL!i) \<Gamma> \<turnstile> \<lparr>(LT!i)|;| \<sigma>1,f\<rparr> |:| A \<and> I!i\<le>length \<Gamma>)"
    using has_type_CaseVE[OF H5] insert_nth_take_drop append_Cons append_Nil 
    by metis
next
  assume H: "\<Gamma> \<turnstile> \<lparr> (ProjR l t)|;| \<sigma>,f\<rparr> |:| R"
  show "\<exists>m L TL. \<Gamma> \<turnstile> \<lparr>t |;| \<sigma>,f\<rparr> |:| \<lparr>L|:|TL\<rparr> \<and> index L l = m \<and> TL ! m = R \<and> distinct L \<and> length L = length TL
                              \<and> l \<in> set L"
    using has_type_ProjRE[OF H]
    by metis
qed (auto elim: has_type_L.cases has_type_ProjTE)

lemma[simp]: "nat (int x + 1) = Suc x" by simp
lemma[simp]: "nat (1 + int x) = Suc x" by simp

lemma[simp]: "nat (int x - 1) = x - 1" by simp 


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
      qed simp      
qed auto  

abbreviation same_Len:: "lterm \<Rightarrow> bool" where 
"same_Len t \<equiv> (case t of CaseVar _ _ I LT \<Rightarrow> length I = length LT | _\<Rightarrow>True)"

inductive RCons::"lterm \<Rightarrow> bool" where
"subterms t = Comp t1 L \<Longrightarrow> same_Len t \<Longrightarrow> RCons t1 \<Longrightarrow> (\<And>i. i<length L \<Longrightarrow> RCons (L!i))\<Longrightarrow> RCons t"
|"subterms t = UList L \<Longrightarrow> (\<And>i. i<length L \<Longrightarrow> RCons (L!i))\<Longrightarrow> RCons t"
|"subterms t = Ter t1 t2 t3 \<Longrightarrow> RCons t1 \<Longrightarrow>RCons t2 \<Longrightarrow>RCons t3 \<Longrightarrow> RCons t"
|"subterms t = Bi t1 t2 \<Longrightarrow> RCons t1 \<Longrightarrow>RCons t2  \<Longrightarrow> RCons t"
|"subterms t = Unary t1 \<Longrightarrow> RCons t1 \<Longrightarrow> RCons t"
|"subterms t = Void \<Longrightarrow> RCons t"

method RCons_inv = (match premises in H:"RCons t" for t \<Rightarrow> \<open>insert H[unfolded RCons.simps[of t, simplified]]\<close>)

lemma FV_shift:
  "RCons t \<Longrightarrow> FV (shift_L (int d) c t) = image (\<lambda>x. if x \<ge> c then x + d else x) (FV t)"
proof (induction t arbitrary: c rule: lterm.induct)
  case (LAbs T t)      
    show ?case 
      using LAbs(1)[OF LAbs(2)[unfolded RCons.simps[of "LAbs T t", simplified]]]       
      by (auto simp: gr_Suc_conv image_iff) force+
next
  case (Tuple L)
    have "\<And>xa c. xa \<in> set L \<Longrightarrow> FV (shift_L (int d) c xa) = (\<lambda>x. if c \<le> x then x + d else x) ` FV xa"
      proof -
        fix xa c
        assume H:"xa \<in> set L" 
        show "FV (shift_L (int d) c xa) = (\<lambda>x. if c \<le> x then x + d else x) ` FV xa"
          using Tuple(2)[unfolded RCons.simps[of "Tuple L", simplified], rule_format]
                H[unfolded in_set_conv_nth] Tuple(1)[OF H]
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
          using Record(2)[unfolded RCons.simps[of "Record L LT", simplified], rule_format]
                H[unfolded in_set_conv_nth] Record(1)[OF H]
          by blast
      qed          
    thus ?case by auto        
next
  case (LetBinder x t1 t2)
    note this(1-2) and inv = this(3)[unfolded RCons.simps[of "LetBinder x t1 t2", simplified]]
    note hyps=this(1)[OF inv[THEN conjunct1]] this(2)[OF inv[THEN conjunct2]]
    have simp_nat:"nat (int x + int d) = x + d" by force
    let ?S= "{y. \<exists>xa. (xa = x \<or> ((\<exists>xb. xb \<in> FV t2 \<and> xb \<noteq> x \<and> x < xb \<and> xa = xb - Suc 0) \<or>
               xa \<in> FV t2 \<and> xa \<noteq> x \<and> \<not> x < xa \<or> xa \<in> FV t1) \<and> c \<le> xa) \<and> y = xa + d} \<union>
             ({y. \<exists>xa. xa \<in> FV t2 \<and> xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0} \<union> (FV t2 - {x}) \<inter> {y. \<not> x < y} \<union> FV t1) \<inter>
             {x. \<not> c \<le> x}"
        and ?S1 ="insert (x + d)({y. \<exists>xa. ((\<exists>x. x \<in> FV t2 \<and> c \<le> x \<and> xa = x + d) \<or> xa \<in> FV t2 \<and> \<not> c \<le> xa) \<and>
                  xa \<noteq> x + d \<and> x + d < xa \<and> y = xa - Suc 0} \<union> ({y. \<exists>x. x \<in> FV t2 \<and> c \<le> x \<and> y = x + d} \<union> 
                  FV t2 \<inter> {x. \<not> c \<le> x} - {x + d}) \<inter> {y. \<not> x + d < y} \<union>
                  ({y. \<exists>x. x \<in> FV t1 \<and> c \<le> x \<and> y = x + d} \<union> FV t1 \<inter> {x. \<not> c \<le> x}))"
    have 1:"x\<ge>c \<Longrightarrow> ?S1 \<subseteq> ?S"
      proof (rule)
        fix y
        assume "y \<in> ?S1" and H2:"x\<ge>c"
        note this(1)[simplified,unfolded not_less]
        then have H:" y = x + d \<or> (\<exists>xa x1. x1 \<in> FV t2 \<and> c \<le> x1 \<and> xa = x1 + d \<and> xa \<noteq> x + d \<and> x + d < xa 
                        \<and> y = xa - Suc 0) \<or> 
                   (\<exists>xa. xa \<in> FV t2 \<and> \<not> c \<le> xa \<and> xa \<noteq> x + d \<and> x + d < xa \<and> y = xa - Suc 0)
               \<or> (\<exists>x. x \<in> FV t2 \<and> c \<le> x \<and> y = x + d) \<and> y \<noteq> x + d \<and> y \<le> x + d \<or>
               y \<in> FV t2 \<and> \<not> c \<le> y \<and> y \<noteq> x + d \<and> y \<le> x + d \<or> (\<exists>x. x \<in> FV t1 \<and> c \<le> x \<and> y = x + d) \<or> y \<in> FV t1 \<and> \<not> c \<le> y"
          by blast
        have "y=x+d \<Longrightarrow> y\<in> ?S" by blast
        moreover have "\<exists>xa x1. x1 \<in> FV t2 \<and> c \<le> x1 \<and> xa = x1 + d \<and> xa \<noteq> x + d \<and> x + d < xa 
                        \<and> y = xa - Suc 0 \<Longrightarrow>
                        y\<in>?S"
          using H2 le_neq_implies_less[of y "x+d"]
          proof (simp)
            assume "\<exists>x1. x1 \<in> FV t2 \<and> c \<le> x1 \<and> x1 \<noteq> x \<and> x < x1 \<and> y = x1 + d - Suc 0" and 
                    H':"c\<le> x"
            then obtain x1 where "x1 \<in> FV t2 \<and> c \<le> x1 \<and> x1 \<noteq> x \<and> x < x1 \<and> y = x1 + d - Suc 0"
              by blast
            hence "x1 \<in> FV t2 \<and> x1 \<noteq> x \<and> x < x1 \<and> x1 - Suc 0 = x1 - Suc 0 \<and> c \<le> x1 - Suc 0 \<and> 
                    y = x1 - Suc 0 + d"
              using Orderings.order_class.dual_order.strict_trans2[OF _ H', of x1]
              by auto
            then show "(\<exists>xa. (xa = x \<or> ((\<exists>xb. xb \<in> FV t2 \<and> xb \<noteq> x \<and> x < xb \<and> xa = xb - Suc 0) \<or> xa \<in> FV t2 
                        \<and> xa \<noteq> x \<and> \<not> x < xa \<or> xa \<in> FV t1) \<and> c \<le> xa) \<and> y = xa + d) \<or> ((\<exists>xa. xa \<in> FV t2 \<and>
                        xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0) \<or> y \<in> FV t2 \<and> y \<noteq> x \<and> \<not> x < y \<or> y \<in> FV t1) \<and>
                        \<not> c \<le> y"
              by blast
          qed

        moreover have "\<exists>xa. xa \<in> FV t2 \<and> \<not> c \<le> xa \<and> xa \<noteq> x + d \<and> x + d < xa \<and> y = xa - Suc 0 \<Longrightarrow>
                        y\<in>?S"
          using H2
          by force
        moreover have "(\<exists>x. x \<in> FV t2 \<and> c \<le> x \<and> y = x + d) \<and> y \<noteq> x + d \<and> y \<le> x + d \<Longrightarrow> y\<in>?S"
          using H2 le_neq_implies_less[of y "x+d"]
          by force
        moreover have "y \<in> FV t2 \<and> \<not> c \<le> y \<and> y \<noteq> x + d \<and> y \<le> x + d \<Longrightarrow> y\<in>?S"
          using H2 le_neq_implies_less[of y "x+d"] not_less not_le
          by simp
        moreover have "(\<exists>x. x \<in> FV t1 \<and> c \<le> x \<and> y = x + d) \<or> y \<in> FV t1 \<and> \<not> c \<le> y \<Longrightarrow> y\<in>?S"   
          using H2 not_le not_less
          by blast
        ultimately show "y\<in>?S" using H by satx   
          
      qed    

    have "x\<ge>c \<Longrightarrow> ?S \<subseteq> ?S1"
      proof (rule)
        fix y
        assume "y \<in> ?S" and H':"x\<ge>c"
        note this(1)[simplified,unfolded not_less not_le] 
        then have H:"y=x+d \<or> (\<exists>xa xb. xb \<in> FV t2 \<and> xb \<noteq> x \<and> x < xb \<and> xa = xb - Suc 0 \<and> c \<le> xa \<and> y = xa + d) \<or>
              (\<exists>xa. xa \<in> FV t2 \<and> xa \<noteq> x \<and> xa \<le> x \<and> c \<le> xa \<and> y = xa + d) \<or> 
              (\<exists>xa. xa \<in> FV t2 \<and> xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0) \<and> y < c \<or>
              (y \<in> FV t2 \<and> y \<noteq> x \<and> y \<le> x \<and> y < c) \<or> (\<exists>xa. xa \<in> FV t1 \<and> c \<le> xa \<and> y = xa + d) \<or> y \<in> FV t1 \<and> y < c"
          by blast
        have "y=x+d \<Longrightarrow> y\<in> ?S1" by blast
        moreover have "\<exists>xa xb. xb \<in> FV t2 \<and> xb \<noteq> x \<and> x < xb \<and> xa = xb - Suc 0 \<and> c \<le> xa \<and> y = xa + d
                        \<Longrightarrow> y\<in>?S1"
          using H'
          proof(simp)
            assume "\<exists>xb. xb \<in> FV t2 \<and> xb \<noteq> x \<and> x < xb \<and> c \<le> xb - Suc 0 \<and> y = xb - Suc 0 + d"
            then obtain xb where  "xb \<in> FV t2 \<and> xb \<noteq> x \<and> x < xb \<and> c \<le> xb - Suc 0 \<and> y = xb - Suc 0 + d"
              by blast
            hence "xb\<in>FV t2 \<and> c\<le>xb \<and> xb+d=xb+d \<and> xb+d\<noteq>x+d \<and> x+d < xb+d \<and> y = xb +d - Suc 0"
              by force
            then show "y = x + d \<or>(\<exists>xa. ((\<exists>x. x \<in> FV t2 \<and> c \<le> x \<and> xa = x + d) \<or> xa \<in> FV t2 \<and> \<not> c \<le> xa) \<and>
                      xa \<noteq> x + d \<and> x + d < xa \<and> y = xa - Suc 0) \<or> ((\<exists>x. x \<in> FV t2 \<and> c \<le> x \<and> y = x + d) \<or> y \<in> FV t2 \<and> \<not> c \<le> y) \<and> y \<noteq> x + d \<and> \<not> x + d < y \<or>
                      (\<exists>x. x \<in> FV t1 \<and> c \<le> x \<and> y = x + d) \<or> y \<in> FV t1 \<and> \<not> c \<le> y "
              by blast
          qed
        moreover have "\<exists>xa. xa \<in> FV t2 \<and> xa \<noteq> x \<and> xa \<le> x \<and> c \<le> xa \<and> y = xa + d \<Longrightarrow>
                        y\<in>?S1"
          using H' le_neq_implies_less[of _ x] not_less not_le
          by force

        moreover have "(\<exists>xa. xa \<in> FV t2 \<and> xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0) \<and> y < c \<Longrightarrow>
                        y\<in>?S1"
          using H' by auto              
          
        moreover have "y \<in> FV t2 \<and> y \<noteq> x \<and> y \<le> x \<and> y < c \<Longrightarrow> y\<in> ?S1"
          using H' by auto

        moreover have "\<exists>xa. xa \<in> FV t1 \<and> c \<le> xa \<and> y = xa + d \<Longrightarrow> y\<in>?S1"
          using H' by force
        moreover have " y \<in> FV t1 \<and> y < c \<Longrightarrow> y\<in>?S1" by auto
        ultimately show "y\<in>?S1" using H by satx
      qed

    with 1 have P1:"x\<ge>c \<Longrightarrow> ?S = ?S1" by fast

    let ?S2 =" insert x ({y. \<exists>xa. ((\<exists>x. x \<in> FV t2 \<and> Suc c \<le> x \<and> xa = x + d) \<or> xa \<in> FV t2 \<and> \<not> Suc c \<le> xa) \<and>
               xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0} \<union> ({y. \<exists>x. x \<in> FV t2 \<and> Suc c \<le> x \<and> y = x + d} \<union> FV t2 \<inter> {x. \<not> Suc c \<le> x} - {x}) \<inter> {y. \<not> x < y} \<union>
               ({y. \<exists>x. x \<in> FV t1 \<and> c \<le> x \<and> y = x + d} \<union> FV t1 \<inter> {x. \<not> c \<le> x}))"
        and ?S4 ="insert x
     ({y. \<exists>xa. ((\<exists>xb. xb \<in> FV t2 \<and> xb \<noteq> x \<and> x < xb \<and> xa = xb - Suc 0) \<or>
                xa \<in> FV t2 \<and> xa \<noteq> x \<and> \<not> x < xa \<or> xa \<in> FV t1) \<and>
               c \<le> xa \<and> y = xa + d} \<union>
      ({y. \<exists>xa. xa \<in> FV t2 \<and> xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0} \<union> (FV t2 - {x}) \<inter> {y. \<not> x < y} \<union> FV t1) \<inter>
      {x. \<not> c \<le> x})"
    have 3:"x<c \<Longrightarrow> ?S4 \<subseteq> ?S2"
      proof (rule)
        fix y
        assume "y \<in> ?S4" and H2:"x<c"
        note this(1)[simplified,unfolded not_less not_le] 
        then have H:"y=x \<or> (\<exists>xa x1. x1 \<in> FV t2 \<and> x1 \<noteq> x \<and> x < x1 \<and> xa = x1 - Suc 0 \<and>  c \<le> xa \<and> y = xa + d)\<or>
                    (\<exists>xa.  xa \<in> FV t2 \<and> xa \<noteq> x \<and> xa \<le> x \<and> c \<le> xa \<and> y = xa + d) \<or>
                    (\<exists>xa. xa \<in> FV t2 \<and> xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0) \<and> y < c \<or>
                    y \<in> FV t2 \<and> y \<noteq> x \<and> y \<le> x \<and> y < c \<or> (\<exists>xa.  xa \<in> FV t1 \<and> c \<le> xa \<and> y = xa + d) \<or> y \<in> FV t1 \<and> y < c "
          by blast
        have "y=x \<Longrightarrow> y\<in> ?S2" by blast
        moreover have "\<exists>xa x1. x1 \<in> FV t2 \<and> x1 \<noteq> x \<and> x < x1 \<and> xa = x1 - Suc 0 \<and>  c \<le> xa \<and> y = xa + d \<Longrightarrow>
                        y\<in>?S2"
          using H2 
          proof (simp add: not_le not_less)
            assume "\<exists>x1. x1 \<in> FV t2 \<and> x1 \<noteq> x \<and> x < x1 \<and> c \<le> x1 - Suc 0 \<and> y = x1 - Suc 0 + d" and 
                    H':"c> x"
            then obtain x1 where "x1 \<in> FV t2 \<and> x1 \<noteq> x \<and> x < x1 \<and> c \<le> x1 - Suc 0 \<and> y = x1 - Suc 0 + d"
              by blast
            hence "x1 \<in> FV t2 \<and> Suc c \<le> x1 \<and> x1+d = x1 + d \<and>  x1+d \<noteq> x \<and> x < x1+d \<and> y = x1 + d - Suc 0"
              using Suc_le_mono[symmetric]
              by force
            then show " y = x \<or> (\<exists>xa. ((\<exists>x. x \<in> FV t2 \<and> Suc c \<le> x \<and> xa = x + d) \<or> xa \<in> FV t2 \<and> xa < Suc c) \<and>
                        xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0) \<or> ((\<exists>x. x \<in> FV t2 \<and> Suc c \<le> x \<and> y = x + d) 
                        \<or> y \<in> FV t2 \<and> y < Suc c) \<and> y \<noteq> x \<and> y \<le> x \<or> (\<exists>x. x \<in> FV t1 \<and> c \<le> x \<and> y = x + d)
                        \<or> y \<in> FV t1 \<and> y < c"
              by auto
          qed

        moreover have "\<exists>xa.  xa \<in> FV t2 \<and> xa \<noteq> x \<and> xa \<le> x \<and> c \<le> xa \<and> y = xa + d \<Longrightarrow>
                        y\<in>?S2"
          using H2 not_le not_less
          by force

        moreover have "(\<exists>xa. xa \<in> FV t2 \<and> xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0) \<and> y < c \<Longrightarrow> y\<in>?S2"
          using H2 by force
         
        moreover have "y \<in> FV t2 \<and> y \<noteq> x \<and> y \<le> x \<and> y < c \<Longrightarrow> y\<in>?S2"
          using H2 
          by (simp add: not_le not_less)
          
        moreover have "(\<exists>xa.  xa \<in> FV t1 \<and> c \<le> xa \<and> y = xa + d) \<or> y \<in> FV t1 \<and> y < c \<Longrightarrow> y\<in>?S2"   
          using H2 
          by (simp add: not_le not_less)
          
        ultimately show "y\<in>?S2" using H by satx        
          
      qed    

    have "x<c \<Longrightarrow> ?S2 \<subseteq> ?S4"
      proof (rule)
        fix y
        assume "y \<in> ?S2" and H':"x<c"
        note this(1)[simplified,unfolded not_less not_le] 
        then have H:"y=x \<or> (\<exists>xa xb. xb \<in> FV t2 \<and> Suc c \<le> xb \<and> xa = xb + d \<and> xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0)\<or>
                   (\<exists>xa. xa \<in> FV t2 \<and> xa < Suc c \<and> xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0) \<or> 
                   (\<exists>x. x \<in> FV t2 \<and> Suc c \<le> x \<and> y = x + d) \<and> y \<noteq> x \<and> y \<le> x \<or>
                   y \<in> FV t2 \<and> y < Suc c \<and> y \<noteq> x \<and> y \<le> x \<or>(\<exists>x. x \<in> FV t1 \<and> c \<le> x \<and> y = x + d) \<or> 
                   y \<in> FV t1 \<and> y < c"
          by blast
        have "y=x \<Longrightarrow> y\<in> ?S4" by blast
        moreover have "\<exists>xa xb. xb \<in> FV t2 \<and> Suc c \<le> xb \<and> xa = xb + d \<and> xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0
                        \<Longrightarrow> y\<in>?S4"
          using H'
          proof (simp add: not_le not_less)
            assume "\<exists>x1. x1 \<in> FV t2 \<and> Suc c \<le> x1 \<and> x1 + d \<noteq> x \<and> x < x1 + d \<and> y = x1 + d - Suc 0" and 
                    H':"c> x"
            then obtain x1 where "x1 \<in> FV t2 \<and> Suc c \<le> x1 \<and> x1 + d \<noteq> x \<and> x < x1 + d \<and> y = x1 + d - Suc 0"
              by blast
            hence "x1 \<in> FV t2 \<and> c \<le> x1-Suc 0 \<and> x1-Suc 0 = x1-Suc 0 \<and>  x1 \<noteq> x \<and> x < x1 \<and> y = x1 - Suc 0 + d"
              using Suc_le_mono[symmetric] H'
              by force
            then show "y = x \<or> (\<exists>xa. ((\<exists>xb. xb \<in> FV t2 \<and> xb \<noteq> x \<and> x < xb \<and> xa = xb - Suc 0) \<or>
                      xa \<in> FV t2 \<and> xa \<noteq> x \<and> xa \<le> x \<or> xa \<in> FV t1) \<and> c \<le> xa \<and> y = xa + d) \<or>
                      ((\<exists>xa. xa \<in> FV t2 \<and> xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0) \<or> y \<in> FV t2 \<and> y \<noteq> x \<and> y \<le> x \<or> y \<in> FV t1) \<and> y < c"
              by blast
          qed

        moreover have "\<exists>xa. xa \<in> FV t2 \<and> xa < Suc c \<and> xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0 \<Longrightarrow>
                        y\<in>?S4"
          using H' 
          by (auto simp: not_le not_less)

        moreover have "(\<exists>x. x \<in> FV t2 \<and> Suc c \<le> x \<and> y = x + d) \<and> y \<noteq> x \<and> y \<le> x \<Longrightarrow>
                        y\<in>?S4"
          using H' by linarith       
          
        moreover have "y \<in> FV t2 \<and> y < Suc c \<and> y \<noteq> x \<and> y \<le> x \<Longrightarrow> y\<in> ?S4"
          using H' by auto

        moreover have "(\<exists>x. x \<in> FV t1 \<and> c \<le> x \<and> y = x + d) \<or> y \<in> FV t1 \<and> y < c \<Longrightarrow> y\<in>?S4"
          using H' by force
        
        ultimately show "y\<in>?S4" using H by satx
      qed
  
    with 3 have P2:"x<c \<Longrightarrow> ?S2 = ?S4" by fast

    show ?case 
      using P1 P2 not_le
      by (cases "x\<ge>c")(force simp: hyps image_def Bex_def Int_Collect simp_nat)+
next
  case (CaseSum t x t1 y t2)
    note this(1-3) and inv = this(4)[unfolded RCons.simps[of "CaseSum t x t1 y t2", simplified]]
    note hyps=this(1)[OF inv[THEN conjunct1]] this(2)[OF inv[THEN conjunct2, THEN conjunct1]]
              this(3)[OF inv[THEN conjunct2, THEN conjunct2]]
    have simp_nat: "nat (int x + int d) = x+d" 
                   "nat (int y + int d) = y+d"
      by force+
   
    let ?S= "\<lambda>x t1 t2. {y. \<exists>xa. (xa = x \<or> ((\<exists>xb. xb \<in> FV t2 \<and> xb \<noteq> x \<and> x < xb \<and> xa = xb - Suc 0) \<or>
               xa \<in> FV t2 \<and> xa \<noteq> x \<and> \<not> x < xa \<or> xa \<in> FV t1) \<and> c \<le> xa) \<and> y = xa + d} \<union>
             ({y. \<exists>xa. xa \<in> FV t2 \<and> xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0} \<union> (FV t2 - {x}) \<inter> {y. \<not> x < y} \<union> FV t1) \<inter>
             {x. \<not> c \<le> x}"
        and ?S1 ="\<lambda>x t1 t2. insert (x + d)({y. \<exists>xa. ((\<exists>x. x \<in> FV t2 \<and> c \<le> x \<and> xa = x + d) \<or> xa \<in> FV t2 \<and> \<not> c \<le> xa) \<and>
                  xa \<noteq> x + d \<and> x + d < xa \<and> y = xa - Suc 0} \<union> ({y. \<exists>x. x \<in> FV t2 \<and> c \<le> x \<and> y = x + d} \<union> 
                  FV t2 \<inter> {x. \<not> c \<le> x} - {x + d}) \<inter> {y. \<not> x + d < y} \<union>
                  ({y. \<exists>x. x \<in> FV t1 \<and> c \<le> x \<and> y = x + d} \<union> FV t1 \<inter> {x. \<not> c \<le> x}))"
    
    have 1:"\<And>x t1 t2. x\<ge>c \<Longrightarrow> ?S1 x t1 t2 \<subseteq> ?S x t1 t2"
      proof (rule)
        fix u ta tb y
        assume "y \<in> ?S1 u ta tb" and H2:"u\<ge>c"
        note this(1)[simplified,unfolded not_less]
        then have H:"(\<lambda>x t1 t2. y = x + d \<or> (\<exists>xa x1. x1 \<in> FV t2 \<and> c \<le> x1 \<and> xa = x1 + d \<and> xa \<noteq> x + d \<and> x + d < xa 
                        \<and> y = xa - Suc 0) \<or> 
                   (\<exists>xa. xa \<in> FV t2 \<and> \<not> c \<le> xa \<and> xa \<noteq> x + d \<and> x + d < xa \<and> y = xa - Suc 0)
               \<or> (\<exists>x. x \<in> FV t2 \<and> c \<le> x \<and> y = x + d) \<and> y \<noteq> x + d \<and> y \<le> x + d \<or>
               y \<in> FV t2 \<and> \<not> c \<le> y \<and> y \<noteq> x + d \<and> y \<le> x + d \<or> (\<exists>x. x \<in> FV t1 \<and> c \<le> x \<and> y = x + d) \<or> y \<in> FV t1 \<and> \<not> c \<le> y)
               u ta tb"
          by blast
        have "(\<lambda>x. y=x+d) u \<Longrightarrow> y\<in> ?S u ta tb" by blast
        moreover have "(\<lambda>x t1 t2. \<exists>xa x1. x1 \<in> FV t2 \<and> c \<le> x1 \<and> xa = x1 + d \<and> xa \<noteq> x + d \<and> x + d < xa 
                        \<and> y = xa - Suc 0) u ta tb\<Longrightarrow>
                        y\<in>?S u ta tb"
          using H2 le_neq_implies_less[of y "u+d"]
          proof (simp)
            assume "(\<lambda>x t1 t2. \<exists>x1. x1 \<in> FV t2 \<and> c \<le> x1 \<and> x1 \<noteq> x \<and> x < x1 \<and> y = x1 + d - Suc 0) u ta tb" and 
                    H':"c\<le> u"
            then obtain x1 where "(\<lambda>x t1 t2. x1 \<in> FV t2 \<and> c \<le> x1 \<and> x1 \<noteq> x \<and> x < x1 \<and> y = x1 + d - Suc 0) u ta tb"
              by blast
            hence "(\<lambda>x t1 t2. x1 \<in> FV t2 \<and> x1 \<noteq> x \<and> x < x1 \<and> x1 - Suc 0 = x1 - Suc 0 \<and> c \<le> x1 - Suc 0 \<and> 
                    y = x1 - Suc 0 + d) u ta tb"
              using Orderings.order_class.dual_order.strict_trans2[OF _ H', of x1]
              by auto
            then show "(\<lambda>x t1 t2.(\<exists>xa. (xa = x \<or> ((\<exists>xb. xb \<in> FV t2 \<and> xb \<noteq> x \<and> x < xb \<and> xa = xb - Suc 0) \<or> xa \<in> FV t2 
                        \<and> xa \<noteq> x \<and> \<not> x < xa \<or> xa \<in> FV t1) \<and> c \<le> xa) \<and> y = xa + d) \<or> ((\<exists>xa. xa \<in> FV t2 \<and>
                        xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0) \<or> y \<in> FV t2 \<and> y \<noteq> x \<and> \<not> x < y \<or> y \<in> FV t1) \<and>
                        \<not> c \<le> y) u ta tb"
              by blast
          qed

        moreover have "(\<lambda>x t1 t2. \<exists>xa. xa \<in> FV t2 \<and> \<not> c \<le> xa \<and> xa \<noteq> x + d \<and> x + d < xa \<and> y = xa - Suc 0) u ta tb\<Longrightarrow>
                        y\<in>?S u ta tb"
          using H2
          by force
        moreover have "(\<lambda>x t1 t2. (\<exists>x. x \<in> FV t2 \<and> c \<le> x \<and> y = x + d) \<and> y \<noteq> x + d \<and> y \<le> x + d) u ta tb\<Longrightarrow> y\<in>?S u ta tb"
          using H2 le_neq_implies_less[of y "x+d"]
          by force
        moreover have "(\<lambda>x t1 t2. y \<in> FV t2 \<and> \<not> c \<le> y \<and> y \<noteq> x + d \<and> y \<le> x + d) u ta tb\<Longrightarrow> y\<in>?S u ta tb"
          using H2 le_neq_implies_less[of y "x+d"] not_less not_le
          by simp
        moreover have "(\<lambda>x t1 t2. (\<exists>x. x \<in> FV t1 \<and> c \<le> x \<and> y = x + d) \<or> y \<in> FV t1 \<and> \<not> c \<le> y) u ta tb\<Longrightarrow> y\<in>?S u ta tb"   
          using H2 not_le not_less
          by blast
        ultimately show "y\<in>?S u ta tb" using H by satx   
          
      qed    

    have 2:"\<And>x t1 t2. x\<ge>c \<Longrightarrow> ?S x t1 t2 \<subseteq> ?S1 x t1 t2"
      proof (rule)
        fix u t1 t2 y
        assume "y \<in> ?S u t1 t2" and H':"u\<ge>c"
        note this(1)[simplified,unfolded not_less not_le] 
        then have H:"(\<lambda>x. y=x+d \<or> (\<exists>xa xb. xb \<in> FV t2 \<and> xb \<noteq> x \<and> x < xb \<and> xa = xb - Suc 0 \<and> c \<le> xa \<and> y = xa + d) \<or>
              (\<exists>xa. xa \<in> FV t2 \<and> xa \<noteq> x \<and> xa \<le> x \<and> c \<le> xa \<and> y = xa + d) \<or> 
              (\<exists>xa. xa \<in> FV t2 \<and> xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0) \<and> y < c \<or>
              (y \<in> FV t2 \<and> y \<noteq> x \<and> y \<le> x \<and> y < c) \<or> (\<exists>xa. xa \<in> FV t1 \<and> c \<le> xa \<and> y = xa + d) \<or> y \<in> FV t1 \<and> y < c) u"
          by blast
        have "(\<lambda>x. y=x+d) u \<Longrightarrow> y\<in> ?S1 u t1 t2" by blast
        moreover have "(\<lambda>x. \<exists>xa xb. xb \<in> FV t2 \<and> xb \<noteq> x \<and> x < xb \<and> xa = xb - Suc 0 \<and> c \<le> xa \<and> y = xa + d) u
                        \<Longrightarrow> y\<in>?S1 u t1 t2"
          using H'
          proof(simp)
            assume "(\<lambda>x. \<exists>xb. xb \<in> FV t2 \<and> xb \<noteq> x \<and> x < xb \<and> c \<le> xb - Suc 0 \<and> y = xb - Suc 0 + d) u"
            then obtain xb where  "(\<lambda>x. xb \<in> FV t2 \<and> xb \<noteq> x \<and> x < xb \<and> c \<le> xb - Suc 0 \<and> y = xb - Suc 0 + d) u"
              by blast
            hence "(\<lambda>x. xb\<in>FV t2 \<and> c\<le>xb \<and> xb+d=xb+d \<and> xb+d\<noteq>x+d \<and> x+d < xb+d \<and> y = xb +d - Suc 0) u"
              by force
            then show "(\<lambda>x. y = x + d \<or>(\<exists>xa. ((\<exists>x. x \<in> FV t2 \<and> c \<le> x \<and> xa = x + d) \<or> xa \<in> FV t2 \<and> \<not> c \<le> xa) \<and>
                      xa \<noteq> x + d \<and> x + d < xa \<and> y = xa - Suc 0) \<or> ((\<exists>x. x \<in> FV t2 \<and> c \<le> x \<and> y = x + d) \<or> y \<in> FV t2 \<and> \<not> c \<le> y) \<and> y \<noteq> x + d \<and> \<not> x + d < y \<or>
                      (\<exists>x. x \<in> FV t1 \<and> c \<le> x \<and> y = x + d) \<or> y \<in> FV t1 \<and> \<not> c \<le> y) u"
              by blast
          qed
        moreover have "(\<lambda>x. \<exists>xa. xa \<in> FV t2 \<and> xa \<noteq> x \<and> xa \<le> x \<and> c \<le> xa \<and> y = xa + d) u \<Longrightarrow>
                        y\<in>?S1 u t1 t2"
          using H' le_neq_implies_less[of _ x] not_less not_le
          by force

        moreover have "(\<lambda>x. (\<exists>xa. xa \<in> FV t2 \<and> xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0) \<and> y < c) u \<Longrightarrow>
                        y\<in>?S1 u t1 t2"
          using H' by auto              
          
        moreover have "(\<lambda>x. y \<in> FV t2 \<and> y \<noteq> x \<and> y \<le> x \<and> y < c) u \<Longrightarrow> y\<in> ?S1 u t1 t2"
          using H' by auto

        moreover have "(\<lambda>x. \<exists>xa. xa \<in> FV t1 \<and> c \<le> xa \<and> y = xa + d) u \<Longrightarrow> y\<in>?S1 u t1 t2"
          using H' by force
        moreover have "(\<lambda>x.  y \<in> FV t1 \<and> y < c) u \<Longrightarrow> y\<in>?S1 u t1 t2" by auto
        ultimately show "y\<in>?S1 u t1 t2" using H by satx
      qed

    have P1:"\<And>x t1 t2. x\<ge>c \<Longrightarrow> ?S x t1 t2= ?S1 x t1 t2"
      proof -
        fix x ta tb
        assume H:"x\<ge>c"
        show "?S x ta tb= ?S1 x ta tb" 
          using 1[OF H,of tb ta] 2[OF H,of tb ta]
          by fast
      qed  
     
    let ?SS1= "insert (x + d)
     (insert (y + d)
       ({y. \<exists>xa. ((\<exists>x. x \<in> FV t1 \<and> c \<le> x \<and> xa = x + d) \<or> xa \<in> FV t1 \<and> \<not> c \<le> xa) \<and>
                 xa \<noteq> x + d \<and> x + d < xa \<and> y = xa - Suc 0} \<union>
        ({y. \<exists>x. x \<in> FV t1 \<and> c \<le> x \<and> y = x + d} \<union> FV t1 \<inter> {x. \<not> c \<le> x} - {x + d}) \<inter> {y. \<not> x + d < y} \<union>
        ({ya. \<exists>x. ((\<exists>xa. xa \<in> FV t2 \<and> c \<le> xa \<and> x = xa + d) \<or> x \<in> FV t2 \<and> \<not> c \<le> x) \<and>
                  x \<noteq> y + d \<and> y + d < x \<and> ya = x - Suc 0} \<union>
         ({y. \<exists>x. x \<in> FV t2 \<and> c \<le> x \<and> y = x + d} \<union> FV t2 \<inter> {x. \<not> c \<le> x} - {y + d}) \<inter> {z. \<not> y + d < z}) \<union>
        ({y. \<exists>x. x \<in> FV t \<and> c \<le> x \<and> y = x + d} \<union> FV t \<inter> {x. \<not> c \<le> x})))" and
        ?SS2 = "
    {ya. \<exists>xa. (xa = x \<or>
               xa = y \<or>
               ((\<exists>xb. xb \<in> FV t1 \<and> xb \<noteq> x \<and> x < xb \<and> xa = xb - Suc 0) \<or>
                xa \<in> FV t1 \<and> xa \<noteq> x \<and> \<not> x < xa \<or>
                (\<exists>x. x \<in> FV t2 \<and> x \<noteq> y \<and> y < x \<and> xa = x - Suc 0) \<or>
                xa \<in> FV t2 \<and> xa \<noteq> y \<and> \<not> y < xa \<or> xa \<in> FV t) \<and>
               c \<le> xa) \<and>
              ya = xa + d} \<union>
    ({y. \<exists>xa. xa \<in> FV t1 \<and> xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0} \<union> (FV t1 - {x}) \<inter> {y. \<not> x < y} \<union>
     ({ya. \<exists>x. x \<in> FV t2 \<and> x \<noteq> y \<and> y < x \<and> ya = x - Suc 0} \<union> (FV t2 - {y}) \<inter> {z. \<not> y < z}) \<union>
     FV t) \<inter>
    {x. \<not> c \<le> x}"
    have S1:"?SS1 = ?S1 x t t1 \<union> ?S1 y t t2"
     by fast
    have S2:"?SS2 = ?S x t t1 \<union> ?S y t t2"
     proof (rule; rule)
       fix a
       assume "a\<in>{ya. \<exists>xa. (xa = x \<or>
                          xa = y \<or>
                          ((\<exists>xb. xb \<in> FV t1 \<and> xb \<noteq> x \<and> x < xb \<and> xa = xb - Suc 0) \<or>
                           xa \<in> FV t1 \<and> xa \<noteq> x \<and> \<not> x < xa \<or>
                           (\<exists>x. x \<in> FV t2 \<and> x \<noteq> y \<and> y < x \<and> xa = x - Suc 0) \<or>
                           xa \<in> FV t2 \<and> xa \<noteq> y \<and> \<not> y < xa \<or> xa \<in> FV t) \<and>
                          c \<le> xa) \<and>
                         ya = xa + d} \<union>
               ({y. \<exists>xa. xa \<in> FV t1 \<and> xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0} \<union>
                (FV t1 - {x}) \<inter> {y. \<not> x < y} \<union>
                ({ya. \<exists>x. x \<in> FV t2 \<and> x \<noteq> y \<and> y < x \<and> ya = x - Suc 0} \<union>
                 (FV t2 - {y}) \<inter> {z. \<not> y < z}) \<union>
                FV t) \<inter>
               {x. \<not> c \<le> x}"
       note this[unfolded Un_iff Int_iff]
      then show "a \<in> {y. \<exists>xa. (xa = x \<or>
                   ((\<exists>xb. xb \<in> FV t1 \<and> xb \<noteq> x \<and> x < xb \<and> xa = xb - Suc 0) \<or>
                    xa \<in> FV t1 \<and> xa \<noteq> x \<and> \<not> x < xa \<or> xa \<in> FV t) \<and> c \<le> xa) \<and> y = xa + d} \<union>
                ({y. \<exists>xa. xa \<in> FV t1 \<and> xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0} \<union>
                 (FV t1 - {x}) \<inter> {y. \<not> x < y} \<union> FV t) \<inter> {x. \<not> c \<le> x} \<union>
                ({ya. \<exists>xa. (xa = y \<or> ((\<exists>xb. xb \<in> FV t2 \<and> xb \<noteq> y \<and> y < xb \<and> xa = xb - Suc 0) \<or>
                  xa \<in> FV t2 \<and> xa \<noteq> y \<and> \<not> y < xa \<or> xa \<in> FV t) \<and> c \<le> xa) \<and> ya = xa + d} \<union>
                 ({ya. \<exists>xa. xa \<in> FV t2 \<and> xa \<noteq> y \<and> y < xa \<and> ya = xa - Suc 0} \<union>
                  (FV t2 - {y}) \<inter> {ya. \<not> y < ya} \<union> FV t) \<inter> {x. \<not> c \<le> x})" 
         by (simp, blast)
     next
       fix a
       assume  "a \<in> {y. \<exists>xa. (xa = x \<or>
                   ((\<exists>xb. xb \<in> FV t1 \<and> xb \<noteq> x \<and> x < xb \<and> xa = xb - Suc 0) \<or>
                    xa \<in> FV t1 \<and> xa \<noteq> x \<and> \<not> x < xa \<or> xa \<in> FV t) \<and> c \<le> xa) \<and> y = xa + d} \<union>
                ({y. \<exists>xa. xa \<in> FV t1 \<and> xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0} \<union>
                 (FV t1 - {x}) \<inter> {y. \<not> x < y} \<union> FV t) \<inter> {x. \<not> c \<le> x} \<union>
                ({ya. \<exists>xa. (xa = y \<or> ((\<exists>xb. xb \<in> FV t2 \<and> xb \<noteq> y \<and> y < xb \<and> xa = xb - Suc 0) \<or>
                  xa \<in> FV t2 \<and> xa \<noteq> y \<and> \<not> y < xa \<or> xa \<in> FV t) \<and> c \<le> xa) \<and> ya = xa + d} \<union>
                 ({ya. \<exists>xa. xa \<in> FV t2 \<and> xa \<noteq> y \<and> y < xa \<and> ya = xa - Suc 0} \<union>
                  (FV t2 - {y}) \<inter> {ya. \<not> y < ya} \<union> FV t) \<inter> {x. \<not> c \<le> x})" 
       note this[unfolded Un_iff Int_iff]
       then show "a\<in>{ya. \<exists>xa. (xa = x \<or>
                          xa = y \<or>
                          ((\<exists>xb. xb \<in> FV t1 \<and> xb \<noteq> x \<and> x < xb \<and> xa = xb - Suc 0) \<or>
                           xa \<in> FV t1 \<and> xa \<noteq> x \<and> \<not> x < xa \<or>
                           (\<exists>x. x \<in> FV t2 \<and> x \<noteq> y \<and> y < x \<and> xa = x - Suc 0) \<or>
                           xa \<in> FV t2 \<and> xa \<noteq> y \<and> \<not> y < xa \<or> xa \<in> FV t) \<and>
                          c \<le> xa) \<and>
                         ya = xa + d} \<union>
               ({y. \<exists>xa. xa \<in> FV t1 \<and> xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0} \<union>
                (FV t1 - {x}) \<inter> {y. \<not> x < y} \<union>
                ({ya. \<exists>x. x \<in> FV t2 \<and> x \<noteq> y \<and> y < x \<and> ya = x - Suc 0} \<union>
                 (FV t2 - {y}) \<inter> {z. \<not> y < z}) \<union>
                FV t) \<inter>
               {x. \<not> c \<le> x}"
         by (simp, blast)
     qed
    have "c \<le> y \<Longrightarrow> c \<le> x \<Longrightarrow> ?SS1 = ?SS2"
      proof (simp only: S1 S2)
        assume hyps:"c \<le> y" "c\<le>x"
        show "?S1 x t t1 \<union> ?S1 y t t2 = ?S x t t1 \<union> ?S y t t2"
          using P1[OF hyps(2), of t1 t, symmetric] P1[OF hyps(1),of t2 t, symmetric]
          by presburger
      qed
    hence C1: "c \<le> y \<Longrightarrow> c \<le> x \<Longrightarrow> ?case"
      by (simp add: hyps image_def Bex_def Int_Collect simp_nat)        
    
    let ?S2 ="\<lambda>x t1 t2. insert x ({y. \<exists>xa. ((\<exists>x. x \<in> FV t2 \<and> Suc c \<le> x \<and> xa = x + d) \<or> xa \<in> FV t2 \<and> \<not> Suc c \<le> xa) \<and>
               xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0} \<union> ({y. \<exists>x. x \<in> FV t2 \<and> Suc c \<le> x \<and> y = x + d} \<union> FV t2 \<inter> {x. \<not> Suc c \<le> x} - {x}) \<inter> {y. \<not> x < y} \<union>
               ({y. \<exists>x. x \<in> FV t1 \<and> c \<le> x \<and> y = x + d} \<union> FV t1 \<inter> {x. \<not> c \<le> x}))"
        and ?S4 ="\<lambda>x t1 t2. insert x
     ({y. \<exists>xa. ((\<exists>xb. xb \<in> FV t2 \<and> xb \<noteq> x \<and> x < xb \<and> xa = xb - Suc 0) \<or>
                xa \<in> FV t2 \<and> xa \<noteq> x \<and> \<not> x < xa \<or> xa \<in> FV t1) \<and>
               c \<le> xa \<and> y = xa + d} \<union>
      ({y. \<exists>xa. xa \<in> FV t2 \<and> xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0} \<union> (FV t2 - {x}) \<inter> {y. \<not> x < y} \<union> FV t1) \<inter>
      {x. \<not> c \<le> x})" and
      ?SS3 ="insert x (insert (y + d) ({y. \<exists>xa. ((\<exists>x. x \<in> FV t1 \<and> Suc c \<le> x \<and> xa = x + d) \<or>
             xa \<in> FV t1 \<and> \<not> Suc c \<le> xa) \<and> xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0} \<union> ({y. \<exists>x. x \<in> FV t1 \<and> Suc c \<le> x \<and> y = x + d} \<union> FV t1 \<inter> {x. \<not> Suc c \<le> x} -
         {x}) \<inter> {y. \<not> x < y} \<union> ({ya. \<exists>x. ((\<exists>xa. xa \<in> FV t2 \<and> c \<le> xa \<and> x = xa + d) \<or> x \<in> FV t2 \<and> \<not> c \<le> x) \<and>
                  x \<noteq> y + d \<and> y + d < x \<and> ya = x - Suc 0} \<union> ({y. \<exists>x. x \<in> FV t2 \<and> c \<le> x \<and> y = x + d} \<union> FV t2 \<inter> {x. \<not> c \<le> x} - {y + d}) \<inter>
         {z. \<not> y + d < z}) \<union> ({y. \<exists>x. x \<in> FV t \<and> c \<le> x \<and> y = x + d} \<union> FV t \<inter> {x. \<not> c \<le> x})))"
       and ?SS4 = "insert x ({ya. \<exists>xa. (xa = y \<or> ((\<exists>xb. xb \<in> FV t1 \<and> xb \<noteq> x \<and> x < xb \<and> xa = xb - Suc 0) \<or>
                  xa \<in> FV t1 \<and> xa \<noteq> x \<and> \<not> x < xa \<or> (\<exists>x. x \<in> FV t2 \<and> x \<noteq> y \<and> y < x \<and> xa = x - Suc 0) \<or>
                  xa \<in> FV t2 \<and> xa \<noteq> y \<and> \<not> y < xa \<or> xa \<in> FV t) \<and> c \<le> xa) \<and> ya = xa + d} \<union>
                  ({y. \<exists>xa. xa \<in> FV t1 \<and> xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0} \<union> (FV t1 - {x}) \<inter> {y. \<not> x < y} \<union>
                  ({ya. \<exists>x. x \<in> FV t2 \<and> x \<noteq> y \<and> y < x \<and> ya = x - Suc 0} \<union> (FV t2 - {y}) \<inter> {z. \<not> y < z}) \<union>
                    FV t) \<inter> {x. \<not> c \<le> x})"
    
    have 3:"\<And>x t1 t2. x<c \<Longrightarrow> ?S4 x t1 t2 \<subseteq> ?S2 x t1 t2"
      proof (rule)
        fix x t1 t2 y
        assume "y \<in> ?S4 x t1 t2" and H2:"x<c"
        note this(1)[simplified,unfolded not_less not_le] 
        then have H:"y=x \<or> (\<exists>xa x1. x1 \<in> FV t2 \<and> x1 \<noteq> x \<and> x < x1 \<and> xa = x1 - Suc 0 \<and>  c \<le> xa \<and> y = xa + d)\<or>
                    (\<exists>xa.  xa \<in> FV t2 \<and> xa \<noteq> x \<and> xa \<le> x \<and> c \<le> xa \<and> y = xa + d) \<or>
                    (\<exists>xa. xa \<in> FV t2 \<and> xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0) \<and> y < c \<or>
                    y \<in> FV t2 \<and> y \<noteq> x \<and> y \<le> x \<and> y < c \<or> (\<exists>xa.  xa \<in> FV t1 \<and> c \<le> xa \<and> y = xa + d) \<or> y \<in> FV t1 \<and> y < c "
          by blast
        have "y=x \<Longrightarrow> y\<in> ?S2 x t1 t2" by blast
        moreover have "\<exists>xa x1. x1 \<in> FV t2 \<and> x1 \<noteq> x \<and> x < x1 \<and> xa = x1 - Suc 0 \<and>  c \<le> xa \<and> y = xa + d \<Longrightarrow>
                        y\<in>?S2 x t1 t2"
          using H2 
          proof (simp add: not_le not_less)
            assume "\<exists>x1. x1 \<in> FV t2 \<and> x1 \<noteq> x \<and> x < x1 \<and> c \<le> x1 - Suc 0 \<and> y = x1 - Suc 0 + d" and 
                    H':"c> x"
            then obtain x1 where "x1 \<in> FV t2 \<and> x1 \<noteq> x \<and> x < x1 \<and> c \<le> x1 - Suc 0 \<and> y = x1 - Suc 0 + d"
              by blast
            hence "x1 \<in> FV t2 \<and> Suc c \<le> x1 \<and> x1+d = x1 + d \<and>  x1+d \<noteq> x \<and> x < x1+d \<and> y = x1 + d - Suc 0"
              using Suc_le_mono[symmetric]
              by force
            then show " y = x \<or> (\<exists>xa. ((\<exists>x. x \<in> FV t2 \<and> Suc c \<le> x \<and> xa = x + d) \<or> xa \<in> FV t2 \<and> xa < Suc c) \<and>
                        xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0) \<or> ((\<exists>x. x \<in> FV t2 \<and> Suc c \<le> x \<and> y = x + d) 
                        \<or> y \<in> FV t2 \<and> y < Suc c) \<and> y \<noteq> x \<and> y \<le> x \<or> (\<exists>x. x \<in> FV t1 \<and> c \<le> x \<and> y = x + d)
                        \<or> y \<in> FV t1 \<and> y < c"
              by auto
          qed

        moreover have "\<exists>xa.  xa \<in> FV t2 \<and> xa \<noteq> x \<and> xa \<le> x \<and> c \<le> xa \<and> y = xa + d \<Longrightarrow>
                        y\<in>?S2 x t1 t2"
          using H2 not_le not_less
          by force

        moreover have "(\<exists>xa. xa \<in> FV t2 \<and> xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0) \<and> y < c \<Longrightarrow> y\<in>?S2 x t1 t2"
          using H2 by force
         
        moreover have "y \<in> FV t2 \<and> y \<noteq> x \<and> y \<le> x \<and> y < c \<Longrightarrow> y\<in>?S2 x t1 t2"
          using H2 
          by (simp add: not_le not_less)
          
        moreover have "(\<exists>xa.  xa \<in> FV t1 \<and> c \<le> xa \<and> y = xa + d) \<or> y \<in> FV t1 \<and> y < c \<Longrightarrow> y\<in>?S2 x t1 t2"   
          using H2 
          by (simp add: not_le not_less)
          
        ultimately show "y\<in>?S2 x t1 t2" using H by satx        
          
      qed    

    have 4:"\<And>x t1 t2. x<c \<Longrightarrow> ?S2 x t1 t2 \<subseteq> ?S4 x t1 t2"
      proof (rule)
        fix x t1 t2 y
        assume "y \<in> ?S2 x t1 t2" and H':"x<c"
        note this(1)[simplified,unfolded not_less not_le] 
        then have H:"y=x \<or> (\<exists>xa xb. xb \<in> FV t2 \<and> Suc c \<le> xb \<and> xa = xb + d \<and> xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0)\<or>
                   (\<exists>xa. xa \<in> FV t2 \<and> xa < Suc c \<and> xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0) \<or> 
                   (\<exists>x. x \<in> FV t2 \<and> Suc c \<le> x \<and> y = x + d) \<and> y \<noteq> x \<and> y \<le> x \<or>
                   y \<in> FV t2 \<and> y < Suc c \<and> y \<noteq> x \<and> y \<le> x \<or>(\<exists>x. x \<in> FV t1 \<and> c \<le> x \<and> y = x + d) \<or> 
                   y \<in> FV t1 \<and> y < c"
          by blast
        have "y=x \<Longrightarrow> y\<in> ?S4 x t1 t2" by blast
        moreover have "\<exists>xa xb. xb \<in> FV t2 \<and> Suc c \<le> xb \<and> xa = xb + d \<and> xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0
                        \<Longrightarrow> y\<in>?S4 x t1 t2"
          using H'
          proof (simp add: not_le not_less)
            assume "\<exists>x1. x1 \<in> FV t2 \<and> Suc c \<le> x1 \<and> x1 + d \<noteq> x \<and> x < x1 + d \<and> y = x1 + d - Suc 0" and 
                    H':"c> x"
            then obtain x1 where "x1 \<in> FV t2 \<and> Suc c \<le> x1 \<and> x1 + d \<noteq> x \<and> x < x1 + d \<and> y = x1 + d - Suc 0"
              by blast
            hence "x1 \<in> FV t2 \<and> c \<le> x1-Suc 0 \<and> x1-Suc 0 = x1-Suc 0 \<and>  x1 \<noteq> x \<and> x < x1 \<and> y = x1 - Suc 0 + d"
              using Suc_le_mono[symmetric] H'
              by force
            then show "y = x \<or> (\<exists>xa. ((\<exists>xb. xb \<in> FV t2 \<and> xb \<noteq> x \<and> x < xb \<and> xa = xb - Suc 0) \<or>
                      xa \<in> FV t2 \<and> xa \<noteq> x \<and> xa \<le> x \<or> xa \<in> FV t1) \<and> c \<le> xa \<and> y = xa + d) \<or>
                      ((\<exists>xa. xa \<in> FV t2 \<and> xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0) \<or> y \<in> FV t2 \<and> y \<noteq> x \<and> y \<le> x \<or> y \<in> FV t1) \<and> y < c"
              by blast
          qed

        moreover have "\<exists>xa. xa \<in> FV t2 \<and> xa < Suc c \<and> xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0 \<Longrightarrow>
                        y\<in>?S4 x t1 t2"
          using H' 
          by (auto simp: not_le not_less)

        moreover have "(\<exists>x. x \<in> FV t2 \<and> Suc c \<le> x \<and> y = x + d) \<and> y \<noteq> x \<and> y \<le> x \<Longrightarrow>
                        y\<in>?S4 x t1 t2"
          using H' by linarith       
          
        moreover have "y \<in> FV t2 \<and> y < Suc c \<and> y \<noteq> x \<and> y \<le> x \<Longrightarrow> y\<in> ?S4 x t1 t2"
          using H' by auto

        moreover have "(\<exists>x. x \<in> FV t1 \<and> c \<le> x \<and> y = x + d) \<or> y \<in> FV t1 \<and> y < c \<Longrightarrow> y\<in>?S4 x t1 t2"
          using H' by force
        
        ultimately show "y\<in>?S4 x t1 t2" using H by satx
      qed
  
    have P2:"\<And>x t1 t2. x<c \<Longrightarrow> ?S2 x t1 t2 = ?S4 x t1 t2" 
      proof -
        fix x ta tb
        assume H:"x<c"
        show "?S2 x ta tb= ?S4 x ta tb" 
          using 3[OF H,of tb ta] 4[OF H,of tb ta]
          by fast
      qed  

    have S3:"?SS3 = ?S2 x t t1 \<union> ?S1 y t t2"
      by fastforce
    have S4:"?SS4= ?S4 x t t1 \<union> ?S y t t2" by blast
    have "c \<le> y \<Longrightarrow>\<not> c \<le> x \<Longrightarrow> ?SS3 = ?SS4"
      proof (simp only: S3 S4)
        assume hyps:"c \<le> y" "\<not>c\<le>x"
        show "?S2 x t t1 \<union> ?S1 y t t2 = ?S4 x t t1 \<union> ?S y t t2"
          using P2[OF hyps(2)[unfolded not_le], of t1 t, symmetric] P1[OF hyps(1),of t2 t, symmetric]
          by presburger
      qed
    then have C2: "c \<le> y \<Longrightarrow> \<not>c \<le> x \<Longrightarrow> ?case"
      by (simp add: hyps image_def Bex_def Int_Collect simp_nat)

    let ?SS5="insert (x + d) (insert y ({y. \<exists>xa. ((\<exists>x. x \<in> FV t1 \<and> c \<le> x \<and> xa = x + d) \<or> xa \<in> FV t1 \<and> \<not> c \<le> xa) \<and>
                 xa \<noteq> x + d \<and> x + d < xa \<and> y = xa - Suc 0} \<union>
        ({y. \<exists>x. x \<in> FV t1 \<and> c \<le> x \<and> y = x + d} \<union> FV t1 \<inter> {x. \<not> c \<le> x} - {x + d}) \<inter> {y. \<not> x + d < y} \<union>
        ({ya. \<exists>x. ((\<exists>xa. xa \<in> FV t2 \<and> Suc c \<le> xa \<and> x = xa + d) \<or> x \<in> FV t2 \<and> \<not> Suc c \<le> x) \<and>
                  x \<noteq> y \<and> y < x \<and> ya = x - Suc 0} \<union>
         ({y. \<exists>x. x \<in> FV t2 \<and> Suc c \<le> x \<and> y = x + d} \<union> FV t2 \<inter> {x. \<not> Suc c \<le> x} - {y}) \<inter> {z. \<not> y < z}) \<union>
        ({y. \<exists>x. x \<in> FV t \<and> c \<le> x \<and> y = x + d} \<union> FV t \<inter> {x. \<not> c \<le> x})))" and
        ?SS6="insert y ({ya. \<exists>xa. (xa = x \<or> ((\<exists>xb. xb \<in> FV t1 \<and> xb \<noteq> x \<and> x < xb \<and> xa = xb - Suc 0) \<or>
              xa \<in> FV t1 \<and> xa \<noteq> x \<and> \<not> x < xa \<or> (\<exists>x. x \<in> FV t2 \<and> x \<noteq> y \<and> y < x \<and> xa = x - Suc 0) \<or>
              xa \<in> FV t2 \<and> xa \<noteq> y \<and> \<not> y < xa \<or> xa \<in> FV t) \<and> c \<le> xa) \<and> ya = xa + d} \<union>
              ({y. \<exists>xa. xa \<in> FV t1 \<and> xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0} \<union> (FV t1 - {x}) \<inter> {y. \<not> x < y} \<union>
              ({ya. \<exists>x. x \<in> FV t2 \<and> x \<noteq> y \<and> y < x \<and> ya = x - Suc 0} \<union> (FV t2 - {y}) \<inter> {z. \<not> y < z}) \<union>
              FV t) \<inter> {x. \<not> c \<le> x})"
    have S5:"?SS5 = ?S1 x t t1 \<union> ?S2 y t t2"
      by fastforce
    have S6:"?SS6= ?S4 y t t2 \<union> ?S x t t1"
      proof (rule; rule)
        fix a
        assume "a \<in> insert y
                ({ya. \<exists>xa. (xa = x \<or>
                            ((\<exists>xb. xb \<in> FV t1 \<and> xb \<noteq> x \<and> x < xb \<and> xa = xb - Suc 0) \<or>
                             xa \<in> FV t1 \<and> xa \<noteq> x \<and> \<not> x < xa \<or>
                             (\<exists>x. x \<in> FV t2 \<and> x \<noteq> y \<and> y < x \<and> xa = x - Suc 0) \<or>
                             xa \<in> FV t2 \<and> xa \<noteq> y \<and> \<not> y < xa \<or> xa \<in> FV t) \<and>
                            c \<le> xa) \<and>
                           ya = xa + d} \<union>
                 ({y. \<exists>xa. xa \<in> FV t1 \<and> xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0} \<union> (FV t1 - {x}) \<inter> {y. \<not> x < y} \<union>
                  ({ya. \<exists>x. x \<in> FV t2 \<and> x \<noteq> y \<and> y < x \<and> ya = x - Suc 0} \<union> (FV t2 - {y}) \<inter> {z. \<not> y < z}) \<union>
                  FV t) \<inter>
                 {x. \<not> c \<le> x})"
       note this[unfolded Un_iff Int_iff insert_def]
      then show "a \<in> insert y
                 ({ya. \<exists>xa. ((\<exists>xb. xb \<in> FV t2 \<and> xb \<noteq> y \<and> y < xb \<and> xa = xb - Suc 0) \<or>
                             xa \<in> FV t2 \<and> xa \<noteq> y \<and> \<not> y < xa \<or> xa \<in> FV t) \<and>
                            c \<le> xa \<and> ya = xa + d} \<union>
                  ({ya. \<exists>xa. xa \<in> FV t2 \<and> xa \<noteq> y \<and> y < xa \<and> ya = xa - Suc 0} \<union>
                   (FV t2 - {y}) \<inter> {ya. \<not> y < ya} \<union>
                   FV t) \<inter>
                  {x. \<not> c \<le> x}) \<union>
                ({y. \<exists>xa. (xa = x \<or>
                           ((\<exists>xb. xb \<in> FV t1 \<and> xb \<noteq> x \<and> x < xb \<and> xa = xb - Suc 0) \<or>
                            xa \<in> FV t1 \<and> xa \<noteq> x \<and> \<not> x < xa \<or> xa \<in> FV t) \<and>
                           c \<le> xa) \<and>
                          y = xa + d} \<union>
                 ({y. \<exists>xa. xa \<in> FV t1 \<and> xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0} \<union> (FV t1 - {x}) \<inter> {y. \<not> x < y} \<union>
                  FV t) \<inter>
                 {x. \<not> c \<le> x})"
        by (simp add: not_le not_less, blast)
     next
       fix a
       assume "a \<in> insert y
                ({ya. \<exists>xa. ((\<exists>xb. xb \<in> FV t2 \<and> xb \<noteq> y \<and> y < xb \<and> xa = xb - Suc 0) \<or>
                            xa \<in> FV t2 \<and> xa \<noteq> y \<and> \<not> y < xa \<or> xa \<in> FV t) \<and>
                           c \<le> xa \<and> ya = xa + d} \<union>
                 ({ya. \<exists>xa. xa \<in> FV t2 \<and> xa \<noteq> y \<and> y < xa \<and> ya = xa - Suc 0} \<union>
                  (FV t2 - {y}) \<inter> {ya. \<not> y < ya} \<union>
                  FV t) \<inter>
                 {x. \<not> c \<le> x}) \<union>
               ({y. \<exists>xa. (xa = x \<or>
                          ((\<exists>xb. xb \<in> FV t1 \<and> xb \<noteq> x \<and> x < xb \<and> xa = xb - Suc 0) \<or>
                           xa \<in> FV t1 \<and> xa \<noteq> x \<and> \<not> x < xa \<or> xa \<in> FV t) \<and>
                          c \<le> xa) \<and>
                         y = xa + d} \<union>
                ({y. \<exists>xa. xa \<in> FV t1 \<and> xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0} \<union> (FV t1 - {x}) \<inter> {y. \<not> x < y} \<union>
                 FV t) \<inter>
                {x. \<not> c \<le> x})"
              
       note this[unfolded Un_iff Int_iff insert_def not_le not_less, simplified]
     
       then show "a \<in> insert y
                 ({ya. \<exists>xa. (xa = x \<or>
                             ((\<exists>xb. xb \<in> FV t1 \<and> xb \<noteq> x \<and> x < xb \<and> xa = xb - Suc 0) \<or>
                              xa \<in> FV t1 \<and> xa \<noteq> x \<and> \<not> x < xa \<or>
                              (\<exists>x. x \<in> FV t2 \<and> x \<noteq> y \<and> y < x \<and> xa = x - Suc 0) \<or>
                              xa \<in> FV t2 \<and> xa \<noteq> y \<and> \<not> y < xa \<or> xa \<in> FV t) \<and>
                             c \<le> xa) \<and>
                            ya = xa + d} \<union>
                  ({y. \<exists>xa. xa \<in> FV t1 \<and> xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0} \<union> (FV t1 - {x}) \<inter> {y. \<not> x < y} \<union>
                   ({ya. \<exists>x. x \<in> FV t2 \<and> x \<noteq> y \<and> y < x \<and> ya = x - Suc 0} \<union> (FV t2 - {y}) \<inter> {z. \<not> y < z}) \<union>
                   FV t) \<inter>
                  {x. \<not> c \<le> x})"
         by (simp add: not_le not_less) blast         
         
     qed

    have "c \<le> x \<Longrightarrow> \<not>c \<le> y \<Longrightarrow> ?SS5 = ?SS6"
      proof -
        assume hyps:"c \<le> x" "\<not>c\<le>y"
        show "?SS5 = ?SS6"
          using P2[OF hyps(2)[unfolded not_le], of t2 t, symmetric] P1[OF hyps(1),of t1 t, symmetric]
                S5 S6
          by force
      qed    
    then have C3: "c \<le> x \<Longrightarrow> \<not>c \<le> y \<Longrightarrow> ?case"
      by (simp add: hyps image_def Bex_def Int_Collect simp_nat)
    
    let ?SS7= "  insert x (insert y ({y. \<exists>xa. ((\<exists>x. x \<in> FV t1 \<and> Suc c \<le> x \<and> xa = x + d) \<or> xa \<in> FV t1 \<and> \<not> Suc c \<le> xa) \<and>
                 xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0} \<union>
        ({y. \<exists>x. x \<in> FV t1 \<and> Suc c \<le> x \<and> y = x + d} \<union> FV t1 \<inter> {x. \<not> Suc c \<le> x} - {x}) \<inter> {y. \<not> x < y} \<union>
        ({ya. \<exists>x. ((\<exists>xa. xa \<in> FV t2 \<and> Suc c \<le> xa \<and> x = xa + d) \<or> x \<in> FV t2 \<and> \<not> Suc c \<le> x) \<and>
                  x \<noteq> y \<and> y < x \<and> ya = x - Suc 0} \<union>
         ({y. \<exists>x. x \<in> FV t2 \<and> Suc c \<le> x \<and> y = x + d} \<union> FV t2 \<inter> {x. \<not> Suc c \<le> x} - {y}) \<inter> {z. \<not> y < z}) \<union>
        ({y. \<exists>x. x \<in> FV t \<and> c \<le> x \<and> y = x + d} \<union> FV t \<inter> {x. \<not> c \<le> x})))" and
        ?SS8=" insert x (insert y ({ya. \<exists>xa. ((\<exists>xb. xb \<in> FV t1 \<and> xb \<noteq> x \<and> x < xb \<and> xa = xb - Suc 0) \<or>
          xa \<in> FV t1 \<and> xa \<noteq> x \<and> \<not> x < xa \<or> (\<exists>x. x \<in> FV t2 \<and> x \<noteq> y \<and> y < x \<and> xa = x - Suc 0) \<or>
           xa \<in> FV t2 \<and> xa \<noteq> y \<and> \<not> y < xa \<or> xa \<in> FV t) \<and> c \<le> xa \<and> ya = xa + d} \<union>
        ({y. \<exists>xa. xa \<in> FV t1 \<and> xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0} \<union> (FV t1 - {x}) \<inter> {y. \<not> x < y} \<union>
         ({ya. \<exists>x. x \<in> FV t2 \<and> x \<noteq> y \<and> y < x \<and> ya = x - Suc 0} \<union> (FV t2 - {y}) \<inter> {z. \<not> y < z}) \<union>
         FV t) \<inter> {x. \<not> c \<le> x}))"

    have S7:"?SS7 = ?S2 x t t1 \<union> ?S2 y t t2"
      by fastforce
    have S8:"?SS8= ?S4 x t t1 \<union> ?S4 y t t2"
      proof (rule; rule)
        fix a
        assume "a \<in> insert x
                (insert y
                  ({ya. \<exists>xa. ((\<exists>xb. xb \<in> FV t1 \<and> xb \<noteq> x \<and> x < xb \<and> xa = xb - Suc 0) \<or>
                              xa \<in> FV t1 \<and> xa \<noteq> x \<and> \<not> x < xa \<or>
                              (\<exists>x. x \<in> FV t2 \<and> x \<noteq> y \<and> y < x \<and> xa = x - Suc 0) \<or>
                              xa \<in> FV t2 \<and> xa \<noteq> y \<and> \<not> y < xa \<or> xa \<in> FV t) \<and>
                             c \<le> xa \<and> ya = xa + d} \<union>
                   ({y. \<exists>xa. xa \<in> FV t1 \<and> xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0} \<union> (FV t1 - {x}) \<inter> {y. \<not> x < y} \<union>
                    ({ya. \<exists>x. x \<in> FV t2 \<and> x \<noteq> y \<and> y < x \<and> ya = x - Suc 0} \<union> (FV t2 - {y}) \<inter> {z. \<not> y < z}) \<union>
                    FV t) \<inter>
                   {x. \<not> c \<le> x}))"
       note this[unfolded Un_iff Int_iff insert_def not_le not_less]
      then show "a \<in> insert x
                 ({y. \<exists>xa. ((\<exists>xb. xb \<in> FV t1 \<and> xb \<noteq> x \<and> x < xb \<and> xa = xb - Suc 0) \<or>
                            xa \<in> FV t1 \<and> xa \<noteq> x \<and> \<not> x < xa \<or> xa \<in> FV t) \<and>
                           c \<le> xa \<and> y = xa + d} \<union>
                  ({y. \<exists>xa. xa \<in> FV t1 \<and> xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0} \<union> (FV t1 - {x}) \<inter> {y. \<not> x < y} \<union>
                   FV t) \<inter>
                  {x. \<not> c \<le> x}) \<union>
                insert y
                 ({ya. \<exists>xa. ((\<exists>xb. xb \<in> FV t2 \<and> xb \<noteq> y \<and> y < xb \<and> xa = xb - Suc 0) \<or>
                             xa \<in> FV t2 \<and> xa \<noteq> y \<and> \<not> y < xa \<or> xa \<in> FV t) \<and>
                            c \<le> xa \<and> ya = xa + d} \<union>
                  ({ya. \<exists>xa. xa \<in> FV t2 \<and> xa \<noteq> y \<and> y < xa \<and> ya = xa - Suc 0} \<union>
                   (FV t2 - {y}) \<inter> {ya. \<not> y < ya} \<union>
                   FV t) \<inter>
                  {x. \<not> c \<le> x})"
        by (simp add: not_le not_less) blast
        
     next
       fix a
       assume "a \<in> insert x
                ({y. \<exists>xa. ((\<exists>xb. xb \<in> FV t1 \<and> xb \<noteq> x \<and> x < xb \<and> xa = xb - Suc 0) \<or>
                           xa \<in> FV t1 \<and> xa \<noteq> x \<and> \<not> x < xa \<or> xa \<in> FV t) \<and>
                          c \<le> xa \<and> y = xa + d} \<union>
                 ({y. \<exists>xa. xa \<in> FV t1 \<and> xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0} \<union> (FV t1 - {x}) \<inter> {y. \<not> x < y} \<union>
                  FV t) \<inter>
                 {x. \<not> c \<le> x}) \<union>
               insert y
                ({ya. \<exists>xa. ((\<exists>xb. xb \<in> FV t2 \<and> xb \<noteq> y \<and> y < xb \<and> xa = xb - Suc 0) \<or>
                            xa \<in> FV t2 \<and> xa \<noteq> y \<and> \<not> y < xa \<or> xa \<in> FV t) \<and>
                           c \<le> xa \<and> ya = xa + d} \<union>
                 ({ya. \<exists>xa. xa \<in> FV t2 \<and> xa \<noteq> y \<and> y < xa \<and> ya = xa - Suc 0} \<union>
                  (FV t2 - {y}) \<inter> {ya. \<not> y < ya} \<union>
                  FV t) \<inter>
                 {x. \<not> c \<le> x})"
              
       note this[unfolded Un_iff Int_iff insert_def not_le not_less, simplified]
     
       then show "a \<in> insert x
                 (insert y
                   ({ya. \<exists>xa. ((\<exists>xb. xb \<in> FV t1 \<and> xb \<noteq> x \<and> x < xb \<and> xa = xb - Suc 0) \<or>
                               xa \<in> FV t1 \<and> xa \<noteq> x \<and> \<not> x < xa \<or>
                               (\<exists>x. x \<in> FV t2 \<and> x \<noteq> y \<and> y < x \<and> xa = x - Suc 0) \<or>
                               xa \<in> FV t2 \<and> xa \<noteq> y \<and> \<not> y < xa \<or> xa \<in> FV t) \<and>
                              c \<le> xa \<and> ya = xa + d} \<union>
                    ({y. \<exists>xa. xa \<in> FV t1 \<and> xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0} \<union>
                     (FV t1 - {x}) \<inter> {y. \<not> x < y} \<union>
                     ({ya. \<exists>x. x \<in> FV t2 \<and> x \<noteq> y \<and> y < x \<and> ya = x - Suc 0} \<union> (FV t2 - {y}) \<inter> {z. \<not> y < z}) \<union>
                     FV t) \<inter> {x. \<not> c \<le> x}))"
         by (simp add: not_le not_less) blast        
         
     qed

    have "\<not>c \<le> y \<Longrightarrow> \<not>c \<le> x \<Longrightarrow> ?SS7 = ?SS8"
      proof (simp only: S7 S8)
        assume hyps:"\<not>c \<le> x" "\<not>c\<le>y"
        show "?S2 x t t1 \<union> ?S2 y t t2 = ?S4 x t t1 \<union> ?S4 y t t2"
          using P2[OF hyps(2)[unfolded not_le], of t2 t, symmetric] 
                P2[OF hyps(1)[unfolded not_le],of t1 t, symmetric]
          by force
      qed    
    then have "\<not>c \<le> y \<Longrightarrow> \<not>c \<le> x \<Longrightarrow> ?case"
      by (simp add: hyps image_def Bex_def Int_Collect simp_nat)
    
    with C1 C2 C3 show ?case by satx
next
  case (CaseVar t L I LT)
    note this(1,2) and inv = this(3)[unfolded RCons.simps[of "CaseVar _ _ _ _", simplified]]          
    note hyps=this(1)[OF inv[THEN conjunct2,THEN conjunct1]] this(2)[OF _ inv[THEN conjunct2,THEN conjunct2, rule_format]]
         and len_cdt=inv[THEN conjunct1]          
    let ?f = "(\<lambda>p. shift_L (int d) (if I ! fst p < c then Suc c else c) (snd p))"

    have A:"\<And>n a b. ([0..<length LT] ! n = a \<and>
                         map (\<lambda>p. shift_L (int d) (if I ! fst p < c then Suc c else c) (snd p))
                          (zip [0..<length LT] LT) !
                         n =
                         b \<and>
                         n < length LT) = (n=a \<and> n < length LT \<and> b= shift_L (int d) (if I ! n < c then Suc c else c) (LT!n))"
      using nth_upt[of 0 _ "length LT", simplified] nth_map[of _ "zip [0..<length LT] LT" ?f, simplified]
      by force
    have B:"\<And>n a b. ([0..<length LT] ! n = a \<and> LT ! n = b \<and> n < length LT) =
             (n=a \<and> LT ! n = b \<and> n < length LT)"
      using nth_upt[of 0 _ "length LT", simplified]
      by fastforce
       
    have simp_n: "\<And>x.  nat (int x + int d) = x+d" 
      by force
    have "{y. \<exists>x. x \<in> FV t \<and> c \<le> x \<and> y = x + d} \<union> FV t \<inter> {x. \<not> c \<le> x} \<union>
    {x. \<exists>xa. (\<exists>a. (I ! a < c \<longrightarrow>
                   a < length LT \<and>
                   xa = {y. \<exists>x. x \<in> FV (shift_L (int d) (Suc c) (LT ! a)) \<and>
                                x \<noteq> map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a \<and>
                                map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a < x \<and>
                                y = x - Suc 0} \<union>
                        (FV (shift_L (int d) (Suc c) (LT ! a)) -
                         {map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a}) \<inter>
                        {y. \<not> map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a < y}) \<and>
                  (\<not> I ! a < c \<longrightarrow>
                   a < length LT \<and>
                   xa = {y. \<exists>x. x \<in> FV (shift_L (int d) c (LT ! a)) \<and>
                                x \<noteq> map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a \<and>
                                map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a < x \<and>
                                y = x - Suc 0} \<union>
                        (FV (shift_L (int d) c (LT ! a)) -
                         {map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a}) \<inter>
                        {y. \<not> map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a < y})) \<and>
             x \<in> xa} \<union>
    ({y. \<exists>x. x \<in> set I \<and> c \<le> x \<and> y = x + d} \<union> set I \<inter> {x. \<not> c \<le> x}) =
    {y. \<exists>x. (x \<in> FV t \<or>
             (\<exists>xa. (\<exists>a<length LT.
                       xa = {y. \<exists>x. x \<in> FV (LT ! a) \<and> x \<noteq> I ! a \<and> I ! a < x \<and> y = x - Suc 0} \<union>
                            (FV (LT ! a) - {I ! a}) \<inter> {y. \<not> I ! a < y}) \<and>
                   x \<in> xa) \<or>
             x \<in> set I) \<and>
            c \<le> x \<and> y = x + d} \<union>
    (FV t \<union>
     {x. \<exists>xa. (\<exists>a<length LT.
                  xa = {y. \<exists>x. x \<in> FV (LT ! a) \<and> x \<noteq> I ! a \<and> I ! a < x \<and> y = x - Suc 0} \<union>
                       (FV (LT ! a) - {I ! a}) \<inter> {y. \<not> I ! a < y}) \<and>
              x \<in> xa} \<union>
     set I) \<inter>
    {x. \<not> c \<le> x}"
      proof (rule; rule)
        fix x
        let ?TS ="x \<in> {y. \<exists>x. (x \<in> FV t \<or> (\<exists>xa. (\<exists>a<length LT.  xa = {y. \<exists>x. x \<in> FV (LT ! a) \<and> x \<noteq> I ! a \<and> I ! a < x \<and> y = x - Suc 0} \<union>
                   (FV (LT ! a) - {I ! a}) \<inter> {y. \<not> I ! a < y}) \<and> x \<in> xa) \<or> x \<in> set I) \<and> c \<le> x \<and> y = x + d} \<union>
              (FV t \<union> {x. \<exists>xa. (\<exists>a<length LT. xa = {y. \<exists>x. x \<in> FV (LT ! a) \<and> x \<noteq> I ! a \<and> I ! a < x \<and> y = x - Suc 0} \<union>
                (FV (LT ! a) - {I ! a}) \<inter> {y. \<not> I ! a < y}) \<and>  x \<in> xa} \<union> set I) \<inter> {x. \<not> c \<le> x}" 
        assume "x \<in> {y. \<exists>x. x \<in> FV t \<and> c \<le> x \<and> y = x + d} \<union> FV t \<inter> {x. \<not> c \<le> x} \<union>
             {x. \<exists>xa. (\<exists>a. (I ! a < c \<longrightarrow> a < length LT \<and>
                            xa = {y. \<exists>x. x \<in> FV (shift_L (int d) (Suc c) (LT ! a)) \<and>
                                         x \<noteq> map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a \<and>
                                         map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a < x \<and>
                                         y = x - Suc 0} \<union>
                                 (FV (shift_L (int d) (Suc c) (LT ! a)) -
                                  {map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a}) \<inter>
                                 {y. \<not> map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a < y}) \<and>
                           (\<not> I ! a < c \<longrightarrow>a < length LT \<and>
                            xa = {y. \<exists>x. x \<in> FV (shift_L (int d) c (LT ! a)) \<and>
                                         x \<noteq> map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a \<and>
                                         map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a < x \<and>
                                         y = x - Suc 0} \<union>
                                 (FV (shift_L (int d) c (LT ! a)) -
                                  {map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a}) \<inter>
                                 {y. \<not> map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a < y})) \<and>
                      x \<in> xa} \<union>
             ({y. \<exists>x. x \<in> set I \<and> c \<le> x \<and> y = x + d} \<union> set I \<inter> {x. \<not> c \<le> x})"
        note H=this[simplified] 
     
        let ?asm="(\<exists>xa. (\<exists>a. (I ! a < c \<longrightarrow> a < length LT \<and>
              xa = {y. \<exists>x. x \<in> FV (shift_L (int d) (Suc c) (LT ! a)) \<and>
                           x \<noteq> map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a \<and>
                map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a < x \<and> y = x - Suc 0} \<union>
                   (FV (shift_L (int d) (Suc c) (LT ! a)) - {map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a}) \<inter>
                   {y. \<not> map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a < y}) \<and>
             (\<not> I ! a < c \<longrightarrow>  a < length LT \<and> xa = {y. \<exists>x. x \<in> FV (shift_L (int d) c (LT ! a)) \<and>
              x \<noteq> map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a \<and> map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a < x \<and> y = x - Suc 0} \<union>
                   (FV (shift_L (int d) c (LT ! a)) - {map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a}) \<inter>
                   {y. \<not> map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a < y})) \<and> x \<in> xa)"
        have "(\<exists>xa. xa \<in> FV t \<and> c \<le> xa \<and> x = xa + d) \<or> x \<in> FV t \<and> \<not> c \<le> x \<Longrightarrow> ?TS" by fast
        moreover have "(\<exists>xa. xa \<in> set I \<and> c \<le> xa \<and> x = xa + d) \<or> x \<in> set I \<and> \<not> c \<le> x \<Longrightarrow> ?TS" by fast
        
        moreover have "?asm \<Longrightarrow> ?TS" 
          proof -
            assume "?asm"
            then obtain xa a where H1:"I ! a < c \<Longrightarrow> a < length LT \<and>
              xa = {y. \<exists>x. x \<in> FV (shift_L (int d) (Suc c) (LT ! a)) \<and>
                           x \<noteq> map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a \<and>
                map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a < x \<and> y = x - Suc 0} \<union>
                   (FV (shift_L (int d) (Suc c) (LT ! a)) - {map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a}) \<inter>
                   {y. \<not> map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a < y}"
             "\<not> I ! a < c \<Longrightarrow> a < length LT \<and> xa = {y. \<exists>x. x \<in> FV (shift_L (int d) c (LT ! a)) \<and>
              x \<noteq> map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a \<and> map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a < x \<and> y = x - Suc 0} \<union>
                   (FV (shift_L (int d) c (LT ! a)) - {map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a}) \<inter>
                   {y. \<not> map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a < y}" "x \<in> xa"
              by blast+
            have "I!a<c \<Longrightarrow> ?TS"
              proof-
                assume infc: "I!a<c"
                note a_len=H1(1)[OF infc, THEN conjunct1]
                have "FV (shift_L (int d) (Suc c) (LT ! a)) = (\<lambda>x. if Suc c \<le> x then x + d else x) ` FV (LT ! a)"
                  using hyps(2)[unfolded in_set_conv_nth,OF _ a_len, of "Suc c"] a_len
                  by blast
                hence " (\<exists>xa. xa \<in> (\<lambda>x. if Suc c \<le> x then x + d else x) ` FV (LT ! a) \<and>
                        xa \<noteq> (if c \<le> (I ! a) then (I ! a) + d else (I ! a))  \<and>
                        (if c \<le> (I ! a) then (I ! a) + d else (I ! a)) < xa \<and> x = xa - Suc 0) \<or>
                          x \<in> (\<lambda>x. if Suc c \<le> x then x + d else x) ` FV (LT ! a) \<and>
                          x \<noteq> (if c \<le> (I ! a) then (I ! a) + d else (I ! a)) \<and>
                          \<not> (if c \<le> (I ! a) then (I ! a) + d else (I ! a)) < x "
                   using H1(3)[unfolded H1(1)[OF infc, THEN conjunct2], simplified]
                   by  (simp only: nth_map[OF a_len[unfolded len_cdt[symmetric]], 
                                of "\<lambda>x. if c \<le> x then nat (int x + int d) else x", symmetric]
                         simp_n[of "I!a", symmetric])
                note C=this[unfolded image_def Bex_def not_less, simplified]
                moreover have "(\<exists>xa. (\<exists>x. x \<in> FV (LT ! a) \<and> xa = (if Suc c \<le> x then x + d else x)) \<and>
                                xa \<noteq> (if c \<le> I ! a then I ! a + d else I ! a) \<and>
                                (if c \<le> I ! a then I ! a + d else I ! a) < xa \<and> x = xa - Suc 0) \<Longrightarrow> ?TS"
                  proof -
                    assume "(\<exists>xa. (\<exists>x. x \<in> FV (LT ! a) \<and> xa = (if Suc c \<le> x then x + d else x)) \<and>
                                xa \<noteq> (if c \<le> I ! a then I ! a + d else I ! a) \<and>
                                (if c \<le> I ! a then I ! a + d else I ! a) < xa \<and> x = xa - Suc 0)"
                    then obtain xa x1 where H:"x1 \<in> FV (LT ! a) \<and> xa = (if Suc c \<le> x1 then x1 + d else x1)"
                                              "xa \<noteq> (I ! a)"  "(I ! a) < xa \<and> x = xa - Suc 0 "
                      using infc
                      by auto
                    have "x1\<ge> Suc c \<Longrightarrow> ?TS"
                      proof -
                        assume "x1\<ge> Suc c"
                        hence "x1-Suc 0 \<in> {y. \<exists>x. x \<in> FV (LT ! a) \<and> x \<noteq> I ! a \<and> I ! a < x \<and> y = x - Suc 0} \<and>
                                c \<le> x1-Suc 0 \<and> x = x1 - Suc 0 + d"
                          using H infc      
                          by force
                        thus ?TS using a_len by blast
                      qed    
              
                    moreover have "x1<Suc c \<Longrightarrow> ?TS" using H a_len by auto
                    ultimately show ?TS by linarith
               qed

               moreover have " (\<exists>xa. xa \<in> FV (LT ! a) \<and> x = (if Suc c \<le> xa then xa + d else xa)) \<and>
                x \<noteq> (if c \<le> I ! a then I ! a + d else I ! a) \<and> x \<le> (if c \<le> I ! a then I ! a + d else I ! a)
                  \<Longrightarrow> ?TS"
                 proof -
                   assume "(\<exists>xa. xa \<in> FV (LT ! a) \<and> x = (if Suc c \<le> xa then xa + d else xa)) \<and>
                          x \<noteq> (if c \<le> I ! a then I ! a + d else I ! a) \<and> x \<le> (if c \<le> I ! a then I ! a + d else I ! a)"
                   then obtain xa where H:" xa \<in> FV (LT ! a) \<and> x = (if Suc c \<le> xa then xa + d else xa)"
                                          " x \<noteq> (if c \<le> I ! a then I ! a + d else I ! a)"  
                                          " x \<le> (if c \<le> I ! a then I ! a + d else I ! a)"
                     by blast
                   have " Suc c > xa \<Longrightarrow> ?TS"  using H infc not_le not_le a_len by auto
                     
                   with H show ?TS using infc a_len by fastforce
                 qed                     
               ultimately show ?TS by satx
             qed
           moreover have "\<not>I!a<c \<Longrightarrow> ?TS"
             proof-
                assume supc: "\<not>I!a<c"
                note a_len=H1(2)[OF supc, THEN conjunct1]
                have "FV (shift_L (int d) c (LT ! a)) = (\<lambda>x. if c \<le> x then x + d else x) ` FV (LT ! a)"
                  using hyps(2)[unfolded in_set_conv_nth,OF _ a_len, of "c"] a_len
                  by blast
                hence "(\<exists>xa. xa \<in> (\<lambda>x. if c \<le> x then x + d else x) ` FV (LT ! a) \<and>
                        xa \<noteq> ( if c \<le> (I ! a) then (I ! a) + d else (I ! a)) \<and>
                        ( if c \<le> (I ! a) then (I ! a) + d else (I ! a)) < xa \<and> x = xa - Suc 0) \<or>
                        x \<in> (\<lambda>x. if c \<le> x then x + d else x) ` FV (LT ! a) \<and>
                        x \<noteq> ( if c \<le> (I ! a) then (I ! a) + d else (I ! a)) \<and>
                        \<not> ( if c \<le> (I ! a) then (I ! a) + d else (I ! a)) < x"
                  using H1(3)[unfolded H1(2)[OF supc, THEN conjunct2], simplified]
                  by (simp only:nth_map[OF a_len[unfolded len_cdt[symmetric]], 
                                of "\<lambda>x. if c \<le> x then nat (int x + int d) else x", symmetric]
                                simp_n[symmetric])
                note C=this[unfolded image_def Bex_def not_less, simplified]
                moreover have "(\<exists>xa. (\<exists>x. x \<in> FV (LT ! a) \<and> xa = (if c \<le> x then x + d else x)) \<and>
                                xa \<noteq> (if c \<le> I ! a then I ! a + d else I ! a) \<and>
                                (if c \<le> I ! a then I ! a + d else I ! a) < xa \<and> x = xa - Suc 0) \<Longrightarrow> ?TS"
                  proof -
                    assume "(\<exists>xa. (\<exists>x. x \<in> FV (LT ! a) \<and> xa = (if c \<le> x then x + d else x)) \<and>
                                xa \<noteq> (if c \<le> I ! a then I ! a + d else I ! a) \<and>
                                (if c \<le> I ! a then I ! a + d else I ! a) < xa \<and> x = xa - Suc 0)"
                    then obtain xa x1 where H:"x1 \<in> FV (LT ! a) \<and> xa = (if c \<le> x1 then x1 + d else x1)"
                                              "xa \<noteq> (I ! a) + d "  "(I ! a) + d < xa \<and> x = xa - Suc 0 "
                      using supc
                      by auto
                    have "x1\<ge> c \<Longrightarrow> ?TS" 
                      proof -
                        assume A:"x1 \<ge> c"
                        hence "x1 \<in> FV (LT ! a) \<and> x1 \<noteq> I ! a \<and> I ! a < x1 \<and> c \<le> x1 - Suc 0 \<and> x = x1 - Suc 0 + d"
                          using H supc[unfolded not_less]
                          by auto
                        thus ?TS using a_len by blast
                      qed    
              
                    moreover have "x1< c \<Longrightarrow> ?TS" using H a_len supc by simp
                    ultimately show ?TS by linarith
                 qed

               moreover have " (\<exists>xa. xa \<in> FV (LT ! a) \<and> x = (if c \<le> xa then xa + d else xa)) \<and>
                x \<noteq> (if c \<le> I ! a then I ! a + d else I ! a) \<and> x \<le> (if c \<le> I ! a then I ! a + d else I ! a)
                  \<Longrightarrow> ?TS"
                 proof -
                   assume "(\<exists>xa. xa \<in> FV (LT ! a) \<and> x = (if c \<le> xa then xa + d else xa)) \<and>
                          x \<noteq> (if c \<le> I ! a then I ! a + d else I ! a) \<and> x \<le> (if c \<le> I ! a then I ! a + d else I ! a)"
                   then obtain xa where H:" xa \<in> FV (LT ! a) \<and> x = (if c \<le> xa then xa + d else xa)"
                                          " x \<noteq> (if c \<le> I ! a then I ! a + d else I ! a)"  
                                          " x \<le> (if c \<le> I ! a then I ! a + d else I ! a)"
                     by blast
                   have " c \<le> xa \<Longrightarrow> ?TS"  using H supc not_le a_len by auto
                   moreover have " c > xa \<Longrightarrow> ?TS"  using supc a_len
                     proof -
                       assume H1: "c>xa"
                       note H=H(1)[THEN conjunct1] H(1)[THEN conjunct2, simplified H1[unfolded not_le[symmetric]] if_False] 
                              H(2-) and H1
                       have "x\<in>(FV (LT ! a) - {I ! a}) \<inter> {y. \<not> I ! a < y} \<and> c>x"                       
                         using H(1)[unfolded H(2)[symmetric], simplified supc[unfolded not_less] if_True] 
                               supc[unfolded not_less] H1[unfolded H(2)[symmetric]]
                         by simp
                       then show ?TS using a_len not_le by blast
                     qed
  
                   ultimately show ?TS using supc a_len by fastforce
                 qed                     
               ultimately show ?TS by satx
             qed
            ultimately show ?TS by fast
          qed

        ultimately show ?TS using H by satx
     next
        fix x
        let ?asm1 ="x \<in> {y. \<exists>x. (x \<in> FV t \<or> (\<exists>xa. (\<exists>a<length LT.  xa = {y. \<exists>x. x \<in> FV (LT ! a) \<and> x \<noteq> I ! a \<and> I ! a < x \<and> y = x - Suc 0} \<union>
                   (FV (LT ! a) - {I ! a}) \<inter> {y. \<not> I ! a < y}) \<and> x \<in> xa) \<or> x \<in> set I) \<and> c \<le> x \<and> y = x + d} \<union>
              (FV t \<union> {x. \<exists>xa. (\<exists>a<length LT. xa = {y. \<exists>x. x \<in> FV (LT ! a) \<and> x \<noteq> I ! a \<and> I ! a < x \<and> y = x - Suc 0} \<union>
                (FV (LT ! a) - {I ! a}) \<inter> {y. \<not> I ! a < y}) \<and>  x \<in> xa} \<union> set I) \<inter> {x. \<not> c \<le> x}" and
            ?TS= "x \<in> {y. \<exists>x. x \<in> FV t \<and> c \<le> x \<and> y = x + d} \<union> FV t \<inter> {x. \<not> c \<le> x} \<union>
             {x. \<exists>xa. (\<exists>a. (I ! a < c \<longrightarrow> a < length LT \<and>
                            xa = {y. \<exists>x. x \<in> FV (shift_L (int d) (Suc c) (LT ! a)) \<and>
                                         x \<noteq> map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a \<and>
                                         map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a < x \<and>
                                         y = x - Suc 0} \<union>
                                 (FV (shift_L (int d) (Suc c) (LT ! a)) -
                                  {map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a}) \<inter>
                                 {y. \<not> map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a < y}) \<and>
                           (\<not> I ! a < c \<longrightarrow>a < length LT \<and>
                            xa = {y. \<exists>x. x \<in> FV (shift_L (int d) c (LT ! a)) \<and>
                                         x \<noteq> map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a \<and>
                                         map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a < x \<and>
                                         y = x - Suc 0} \<union>
                                 (FV (shift_L (int d) c (LT ! a)) -
                                  {map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a}) \<inter>
                                 {y. \<not> map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a < y})) \<and>
                      x \<in> xa} \<union>
             ({y. \<exists>x. x \<in> set I \<and> c \<le> x \<and> y = x + d} \<union> set I \<inter> {x. \<not> c \<le> x})"
        assume ?asm1
        note this[simplified] 

        then have H:"(\<exists>xa. xa \<in> FV t \<and> c \<le> xa \<and> x = xa + d) \<or>
         (\<exists>xa. (\<exists>xaa. (\<exists>a<length LT. xaa = {y. \<exists>x. x \<in> FV (LT ! a) \<and> x \<noteq> I ! a \<and> I ! a < x \<and> y = x - Suc 0} \<union>
         (FV (LT ! a) - {I ! a}) \<inter> {y. \<not> I ! a < y}) \<and> xa \<in> xaa) \<and> c \<le> xa \<and> x = xa + d) \<or>
         (\<exists>xa. xa \<in> set I \<and> c \<le> xa \<and> x = xa + d) \<or>
         x \<in> FV t \<and> \<not> c \<le> x \<or>
         (\<exists>xa. (\<exists>a<length LT. xa = {y. \<exists>x. x \<in> FV (LT ! a) \<and> x \<noteq> I ! a \<and> I ! a < x \<and> y = x - Suc 0} \<union>
          (FV (LT ! a) - {I ! a}) \<inter> {y. \<not> I ! a < y}) \<and> x \<in> xa \<and> \<not> c \<le> x \<or> x \<in> set I \<and> \<not> c \<le> x)"
          by blast

        have "\<exists>xa. xa \<in> FV t \<and>c \<le> xa \<and> x = xa + d \<Longrightarrow> ?TS" by fast
        moreover have "\<exists>xa. xa \<in> set  I\<and>c \<le> xa \<and> x = xa + d \<Longrightarrow> ?TS" by fast
        moreover have "x \<in> FV t \<and> \<not> c \<le> x \<Longrightarrow> ?TS" by fast

        moreover have "\<exists>xa. ((\<exists>xaa. (\<exists>a<length LT. xaa = {y. \<exists>x. x \<in> FV (LT ! a) \<and> x \<noteq> I ! a \<and> I ! a < x \<and> y = x - Suc 0} \<union>
               (FV (LT ! a) - {I ! a}) \<inter> {y. \<not> I ! a < y}) \<and> xa \<in> xaa)) \<and> c \<le> xa \<and> x = xa + d
               \<Longrightarrow> ?TS"
          proof -
            assume "\<exists>xa. ((\<exists>xaa. (\<exists>a<length LT. xaa = {y. \<exists>x. x \<in> FV (LT ! a) \<and> x \<noteq> I ! a \<and> I ! a < x \<and> y = x - Suc 0} \<union>
               (FV (LT ! a) - {I ! a}) \<inter> {y. \<not> I ! a < y}) \<and> xa \<in> xaa)) \<and> c \<le> xa \<and> x = xa + d"
            then obtain xa a x1 where H:"x1 \<in> FV (LT ! a) \<and> x1 \<noteq> I ! a \<and> I ! a < x1 \<and> xa = x1 - Suc 0 \<or>
                                         xa \<in> FV (LT ! a) \<and> xa\<noteq> I ! a \<and> \<not> I ! a < xa" "c \<le> xa" "x = xa + d"
                                        "a<length LT"
              by blast
            have A:"\<And>c. FV (shift_L (int d) c (LT ! a)) = (\<lambda>x. if c \<le> x then x + d else x) ` FV (LT ! a)"
                  using hyps(2)[OF _ H(4)] set_conv_nth H(4)
                  by auto
            have "xa \<in> FV (LT ! a) \<and> xa \<noteq> I ! a \<and> \<not> I ! a < xa \<Longrightarrow> ?TS" 
              proof -
                assume H1:"xa \<in> FV (LT ! a) \<and> xa \<noteq> I ! a \<and> \<not> I ! a < xa"
                note H1=H1[THEN conjunct1] H1[THEN conjunct2,THEN conjunct1] H1[THEN conjunct2,THEN conjunct2]

                
                have "x\<in>{y. \<exists>x. x \<in> FV (shift_L (int d) c (LT ! a)) \<and>
                                     x \<noteq> map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a \<and>
                                     map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a < x \<and>
                                     y = x - Suc 0} \<union>
                             (FV (shift_L (int d) c (LT ! a)) -
                              {map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a}) \<inter>
                             {y. \<not> map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a < y}"
                  proof -
                    have " c\<le> I!a \<Longrightarrow> (\<exists>xa. ((\<exists>x. x \<in> FV (LT ! a) \<and> c \<le> x \<and> xa = x + d) \<or> xa \<in> FV (LT ! a) \<and> \<not> c \<le> xa) \<and>
                           xa \<noteq> I ! a + d \<and> I ! a + d < xa \<and> x = xa - Suc 0) \<or>
                           ((\<exists>xa. xa \<in> FV (LT ! a) \<and> c \<le> xa \<and> x = xa + d) \<or> x \<in> FV (LT ! a) \<and> \<not> c \<le> x) \<and>
                           x \<noteq> I ! a + d \<and> \<not> I ! a + d < x"
                      using H1 H(2-) by simp

                    moreover have " \<not> c \<le> I ! a \<Longrightarrow> (\<exists>xa. ((\<exists>x. x \<in> FV (LT ! a) \<and> c \<le> x \<and> xa = x + d) \<or> xa \<in> FV (LT ! a) \<and> \<not> c \<le> xa) \<and>
                                    xa \<noteq> I ! a \<and> I ! a < xa \<and> x = xa - Suc 0) \<or> ((\<exists>xa. xa \<in> FV (LT ! a) \<and> 
                                    c \<le> xa \<and> x = xa + d) \<or> x \<in> FV (LT ! a) \<and> \<not> c \<le> x) \<and> x \<noteq> I ! a \<and> \<not> I ! a < x"
                      using H1 H(2-)
                      by linarith
                    ultimately show ?thesis
                      by (simp add: A image_iff Bex_def nth_map[OF H(4)[unfolded len_cdt[symmetric]]] simp_n )
                  qed
                then have "\<exists>xa. (I ! a < c \<longrightarrow> a < length LT \<and>
                        xa = {y. \<exists>x. x \<in> FV (shift_L (int d) (Suc c) (LT ! a)) \<and>
                                     x \<noteq> map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a \<and>
                                     map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a < x \<and>
                                     y = x - Suc 0} \<union>(FV (shift_L (int d) (Suc c) (LT ! a)) -
                              {map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a}) \<inter>
                             {y. \<not> map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a < y}) \<and>
                       (\<not> I ! a < c \<longrightarrow> a < length LT \<and> xa = {y. \<exists>x. x \<in> FV (shift_L (int d) c (LT ! a)) \<and>
                                     x \<noteq> map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a \<and>
                                     map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a < x \<and>
                                     y = x - Suc 0} \<union> (FV (shift_L (int d) c (LT ! a)) -
                              {map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a}) \<inter>
                             {y. \<not> map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a < y}) \<and>
                  x \<in> xa"
                  using H(4) H1(3) H(2) less_le_trans by auto
               thus ?TS by auto
             qed
            moreover have "x1 \<in> FV (LT ! a) \<and> x1 \<noteq> I ! a \<and> I ! a < x1 \<and> xa = x1 - Suc 0 \<Longrightarrow> ?TS"
              proof -
                assume H1:"x1 \<in> FV (LT ! a) \<and> x1 \<noteq> I ! a \<and> I ! a < x1 \<and> xa = x1 - Suc 0"
                note H1=H1[THEN conjunct1] H1[THEN conjunct2,THEN conjunct1] 
                        H1[THEN conjunct2,THEN conjunct2,THEN conjunct1] 
                        H1[THEN conjunct2,THEN conjunct2,THEN conjunct2]
                
                have 1:"c>I!a \<Longrightarrow> x\<in>{y. \<exists>x. x \<in> FV (shift_L (int d) (Suc c) (LT ! a)) \<and>
                                     x \<noteq> map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a \<and>
                                     map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a < x \<and>
                                     y = x - Suc 0} \<union>
                             (FV (shift_L (int d) (Suc c) (LT ! a)) -
                              {map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a}) \<inter>
                             {y. \<not> map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a < y}"
                  proof -
                    assume H2:"c> I!a"
                 
                    have a: "x1 \<in> FV (LT ! a) \<and> Suc c \<le> x1  \<and> x1+d \<noteq> I ! a \<and>
                            I ! a < x1+d \<and> x = x1 +d - Suc 0"
                        using H1 H(2-) by auto
                    hence "(\<exists>xa. ((\<exists>x. x \<in> FV (LT ! a) \<and> Suc c \<le> x \<and> xa = x + d) \<or> xa \<in> FV (LT ! a) \<and> \<not>Suc c \<le> xa) \<and>
                          xa \<noteq> I ! a \<and> I ! a < xa \<and> x = xa - Suc 0) \<or>((\<exists>xa. xa \<in> FV (LT ! a) \<and>
                          Suc c \<le> xa \<and> x = xa + d) \<or> x \<in> FV (LT ! a) \<and> \<not>Suc c \<le> x) \<and> x \<noteq> I ! a \<and> \<not> I ! a < x"      
                      by blast  
                    with H2 show ?thesis
                      by (simp add: A image_iff Bex_def nth_map[OF H(4)[unfolded len_cdt[symmetric]]] simp_n )
                  qed
                have "\<not> c > I ! a \<Longrightarrow> x\<in>{y. \<exists>x. x \<in> FV (shift_L (int d) c (LT ! a)) \<and>
                                     x \<noteq> map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a \<and>
                                     map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a < x \<and>
                                     y = x - Suc 0} \<union> (FV (shift_L (int d) c (LT ! a)) -
                              {map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a}) \<inter>
                             {y. \<not> map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a < y}"
                  proof -
                    assume H2:"\<not> c > I ! a"
                   have a: "x1 \<in> FV (LT ! a) \<and> c \<le> x1  \<and> x1+d \<noteq> I ! a \<and>
                            I ! a < x1+d \<and> x = x1 +d - Suc 0"
                        using H1 H(2-) by auto
                   
                    hence "c = I ! a \<Longrightarrow>(\<exists>xa. ((\<exists>x. x \<in> FV (LT ! a) \<and> I ! a \<le> x \<and> xa = x + d) \<or> xa \<in> FV (LT ! a) \<and> \<not> I ! a \<le> xa) \<and>
                                    xa \<noteq> I ! a + d \<and> I ! a + d < xa \<and> x = xa - Suc 0) \<or> 
                                    ((\<exists>xa. xa \<in> FV (LT ! a) \<and> I ! a \<le> xa \<and> x = xa + d) \<or> 
                                    x \<in> FV (LT ! a) \<and> \<not> I ! a \<le> x) \<and> x \<noteq> I ! a + d \<and> \<not> I ! a + d < x"
                      
                      by (metis H1(2) H1(3) add_less_mono1 nat_add_right_cancel)
                    moreover have "(\<exists>xa. ((\<exists>x. x \<in> FV (LT ! a) \<and> c \<le> x \<and> xa = x + d) \<or> xa \<in> FV (LT ! a) \<and> \<not> c \<le> xa) \<and>
                                 xa \<noteq> I ! a + d \<and> I ! a + d < xa \<and> x = xa - Suc 0) \<or>
                           ((\<exists>xa. xa \<in> FV (LT ! a) \<and> c \<le> xa \<and> x = xa + d) \<or> x \<in> FV (LT ! a) \<and> \<not> c \<le> x) \<and>
                           x \<noteq> I ! a + d \<and> \<not> I ! a + d < x"
                      proof -
                        have "x1 \<in> FV (LT ! a) \<and> c \<le> x1  \<and> x1+d \<noteq> I ! a + d \<and>
                              I ! a + d < x1+d \<and> x = x1 +d - Suc 0"
                          using H1 H(2-) by auto
                        thus ?thesis by blast
                      qed
                    ultimately show ?thesis using H2
                      by (simp add: A image_iff Bex_def nth_map[OF H(4)[unfolded len_cdt[symmetric]]] simp_n )
                  qed
                with 1 have "\<exists>xa. (I ! a < c \<longrightarrow> a < length LT \<and>
                        xa = {y. \<exists>x. x \<in> FV (shift_L (int d) (Suc c) (LT ! a)) \<and>
                                     x \<noteq> map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a \<and>
                                     map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a < x \<and>
                                     y = x - Suc 0} \<union>(FV (shift_L (int d) (Suc c) (LT ! a)) -
                              {map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a}) \<inter>
                             {y. \<not> map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a < y}) \<and>
                       (\<not> I ! a < c \<longrightarrow> a < length LT \<and> xa = {y. \<exists>x. x \<in> FV (shift_L (int d) c (LT ! a)) \<and>
                                     x \<noteq> map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a \<and>
                                     map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a < x \<and>
                                     y = x - Suc 0} \<union> (FV (shift_L (int d) c (LT ! a)) -
                              {map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a}) \<inter>
                             {y. \<not> map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a < y}) \<and>
                  x \<in> xa"
                  using H(4)
                  by (metis (no_types, lifting))                  
               thus ?TS by auto
             qed

            ultimately show ?TS using H(1) by blast
          qed

        moreover have "(\<exists>xa. (\<exists>a<length LT. xa = {y. \<exists>x. x \<in> FV (LT ! a) \<and> x \<noteq> I ! a \<and> I ! a < x \<and> y = x - Suc 0} \<union>
          (FV (LT ! a) - {I ! a}) \<inter> {y. \<not> I ! a < y}) \<and> x \<in> xa \<and> \<not> c \<le> x \<or> x \<in> set I \<and> \<not> c \<le> x) \<Longrightarrow> ?TS" 
          proof -
            assume HH:"(\<exists>xa. (\<exists>a<length LT. xa = {y. \<exists>x. x \<in> FV (LT ! a) \<and> x \<noteq> I ! a \<and> I ! a < x \<and> y = x - Suc 0} \<union>
              (FV (LT ! a) - {I ! a}) \<inter> {y. \<not> I ! a < y}) \<and> x \<in> xa \<and> \<not> c \<le> x \<or> x \<in> set I \<and> \<not> c \<le> x)"
            have "\<exists>xa. (\<exists>a<length LT. xa = {y. \<exists>x. x \<in> FV (LT ! a) \<and> x \<noteq> I ! a \<and> I ! a < x \<and> y = x - Suc 0} \<union>
              (FV (LT ! a) - {I ! a}) \<inter> {y. \<not> I ! a < y}) \<and> x \<in> xa \<and> \<not> c \<le> x \<Longrightarrow> ?TS"
              proof-
                assume "\<exists>xa. (\<exists>a<length LT. xa = {y. \<exists>x. x \<in> FV (LT ! a) \<and> x \<noteq> I ! a \<and> I ! a < x \<and> y = x - Suc 0} \<union>
                        (FV (LT ! a) - {I ! a}) \<inter> {y. \<not> I ! a < y}) \<and> x \<in> xa \<and> \<not> c \<le> x"
                then obtain a where H: "a<length LT" "(\<exists>x1. x1 \<in> FV (LT ! a) \<and> x1 \<noteq> I ! a \<and> I ! a < x1 \<and> x = x1 - Suc 0) \<or>
                                      x\<in>FV (LT ! a) \<and> x\<noteq> I!a \<and> \<not> I ! a < x" "\<not> c \<le> x"
                  by blast
               have A:"\<And>c. FV (shift_L (int d) c (LT ! a)) = (\<lambda>x. if c \<le> x then x + d else x) ` FV (LT ! a)"
                  using hyps(2)[OF _ H(1)] set_conv_nth H(1)
                  by auto
               have "\<exists>x1. x1 \<in> FV (LT ! a) \<and> x1 \<noteq> I ! a \<and> I ! a < x1 \<and> x = x1 - Suc 0 \<Longrightarrow> ?TS"
                 proof -
                   assume "\<exists>x1. x1 \<in> FV (LT ! a) \<and> x1 \<noteq> I ! a \<and> I ! a < x1 \<and> x = x1 - Suc 0"
                   then obtain x1 where H1:"x1 \<in> FV (LT ! a)" "x1 \<noteq> I ! a" "I ! a < x1" 
                                            "x = x1 - Suc 0"
                      by blast
                   hence "x\<in> {y. \<exists>x. x \<in> FV (shift_L (int d) (Suc c) (LT ! a)) \<and>
                            x \<noteq> map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a \<and>
                            map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a < x \<and> y = x - Suc 0} \<union>
                            (FV (shift_L (int d) (Suc c) (LT ! a)) -
                             {map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a}) \<inter>
                            {y. \<not> map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a < y}"
                      using H(1,3)
                      by (auto simp:A image_iff Bex_def simp_n nth_map[OF H(1)[unfolded len_cdt[symmetric]]])
                   hence M:"\<exists>xa. (I ! a < c \<longrightarrow> a < length LT \<and> xa = {y. \<exists>x. x \<in> FV (shift_L (int d) (Suc c) (LT ! a)) \<and>
                          x \<noteq> map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a \<and>
                          map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a < x \<and> y = x - Suc 0} \<union>
                          (FV (shift_L (int d) (Suc c) (LT ! a)) -
                           {map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a}) \<inter>
                          {y. \<not> map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a < y}) \<and>
                        (\<not> I ! a < c \<longrightarrow> a < length LT \<and> xa = {y. \<exists>x. x \<in> FV (shift_L (int d) c (LT ! a)) \<and>
                         x \<noteq> map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a \<and>
                         map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a < x \<and> y = x - Suc 0} \<union>
                         (FV (shift_L (int d) c (LT ! a)) - {map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a}) \<inter>
                          {y. \<not> map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a < y}) \<and>
                         x \<in> xa"
                      using H(1,3) H1(3,4) Suc_pred diff_le_self less_le_trans
                            not_less_eq_eq zero_less_diff 
                      by auto
                   then show ?TS by (auto simp add:image_iff Bex_def) 
                 qed     
               moreover have "x\<in>FV (LT ! a) \<and> x\<noteq> I!a \<and> \<not> I ! a < x \<Longrightarrow> ?TS"
                 proof -
                   assume H1:"x\<in>FV (LT ! a) \<and> x\<noteq> I!a \<and> \<not> I ! a < x"
                   hence "I ! a < c \<Longrightarrow> x\<in> (FV (shift_L (int d) (Suc c) (LT ! a)) -
                     {map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a}) \<inter>
                    {y. \<not> map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a < y}"
                     by (simp add:image_iff Bex_def A nth_map[OF H(1)[unfolded len_cdt[symmetric]]] simp_n)
                   moreover have "\<not> I ! a < c \<Longrightarrow> x\<in>(FV (shift_L (int d) c (LT ! a)) -
                              {map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a}) \<inter>
                             {y. \<not> map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a < y}"
                     using H1 H(3)
                     by (simp add:image_iff Bex_def A nth_map[OF H(1)[unfolded len_cdt[symmetric]]] simp_n)
                   ultimately have "\<exists>xa. (\<exists>a. (I ! a < c \<longrightarrow> a < length LT \<and> xa = {y. \<exists>x. x \<in> FV (shift_L (int d) (Suc c) (LT ! a)) \<and>
                                     x \<noteq> map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a \<and>
                                     map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a < x \<and>
                                     y = x - Suc 0} \<union> (FV (shift_L (int d) (Suc c) (LT ! a)) -
                              {map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a}) \<inter>
                             {y. \<not> map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a < y}) \<and>
                       (\<not> I ! a < c \<longrightarrow> a < length LT \<and> xa = {y. \<exists>x. x \<in> FV (shift_L (int d) c (LT ! a)) \<and>
                                     x \<noteq> map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a \<and>
                                     map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a < x \<and>
                                     y = x - Suc 0} \<union>
                       (FV (shift_L (int d) c (LT ! a)) - {map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a}) \<inter>
                       {y. \<not> map (\<lambda>x. if c \<le> x then nat (int x + int d) else x) I ! a < y})) \<and> x \<in> xa"
                     using H
                     by (cases "I ! a < c", auto)
                   thus ?TS by blast
                 qed  
                     
               ultimately show ?TS using H(2) by blast 
             qed       
                  
           moreover have "x \<in> set I \<and> \<not> c \<le> x \<Longrightarrow> ?TS" by blast
           ultimately show ?TS using HH by presburger
         qed

       ultimately show ?TS using H by satx
     qed
   then show ?case
      by (simp add: hyps indexed_to_map image_def Bex_def Int_Collect)
         (simp add: in_set_zip fst_conv snd_conv Union_eq A B simp_n)
qed (RCons_inv, force)+

method RCons_m = (match conclusion in "RCons t" for t \<Rightarrow> 
                    \<open>insert RCons.intros[of t, simplified], force\<close>)

lemma RCons_shift:
  "RCons t \<Longrightarrow> RCons (shift_L d c t)"
by (induction t arbitrary: c) (RCons_inv, RCons_m)+

lemma FV_subst:
  "RCons t \<Longrightarrow> FV (subst_L n t u) = (if n \<in> FV u then (FV u - {n}) \<union> FV t else FV u)"
proof (induction u arbitrary: n t rule: lterm.induct)
  case (LAbs T u)
  from LAbs(1)[OF RCons_shift[OF LAbs(2)]] 
    show ?case 
    by (auto simp: gr0_conv_Suc image_iff FV_shift[OF LAbs(2), of 1, unfolded int_1],
        (metis DiffI One_nat_def UnCI diff_Suc_1 empty_iff imageI insert_iff nat.distinct(1))+)
next
  case (Record L LT)
    note hyps=this(1)[OF _ this(2)] this(1)[OF _ RCons_shift[OF this(2)]]
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
    note hyps= this(1)[OF _ this(2)] this(1)[OF _ RCons_shift[OF this(2)]]
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
    note hyps=this(1)[OF this(3)] this(1)[OF RCons_shift[OF this(3)]]
              this(2)[OF this(3)] this(2)[OF RCons_shift[OF this(3)]]
    have "x < n \<Longrightarrow> ?case"
      proof (rule; rule)
        fix x1
         assume H:"x<n" "x1 \<in> FV (subst_L n t (Let var x := t1 in t2))"
      
        have "n\<in>FV (Let var x := t1 in t2) \<Longrightarrow> x1 \<in> FV (Let var x := t1 in t2) - {n} \<union> FV t"
          using H[simplified] FV_shift[OF LetBinder(3), of 1 x, simplified]
          by (simp add: image_def Bex_def hyps)
             (cases "n\<in> FV t1", cases "Suc n\<in> FV t2", force+)
        moreover have  "n \<notin> FV (Let var x := t1 in t2) \<Longrightarrow> x1\<in> FV (Let var x := t1 in t2)"
          using H[simplified]
          apply (simp add: image_def Bex_def hyps)
          apply (cases "Suc n\<in> FV t2")
          sorry
        ultimately show "x1 \<in> (if n \<in> FV (Let var x := t1 in t2) then FV (Let var x := t1 in t2) - {n} \<union> FV t
                 else FV (Let var x := t1 in t2))"
          by meson
      next
        fix x1
        show "x1 \<in> FV (subst_L n t (Let var x := t1 in t2))" sorry
      qed
    show ?case sorry
     
next
  case (CaseSum t1 x t2 y t3)
    note hyps=this(1)[OF this(4)] this(1)[OF RCons_shift[OF this(4)]] this(2)[OF this(4)]
              this(2)[OF RCons_shift[OF this(4)]] this(3)[OF this(4)] this(3)[OF RCons_shift[OF this(4)]]
    thus ?case sorry
next
  case (CaseVar)
    note hyps=this(1)[OF this(3)] this(1)[OF RCons_shift[OF this(3)]] this(2)[OF _ this(3)]
              this(2)[OF _ RCons_shift[OF this(3)]]

    thus ?case sorry
qed (auto simp: gr0_conv_Suc image_iff FV_shift[of t 1, unfolded int_1])

lemma weakening :
  fixes \<Gamma>::lcontext  and t::lterm and A S::ltype and \<sigma> ::"nat\<rightharpoonup>ltype" and n::nat
  assumes well_typed: "\<Gamma> \<turnstile> \<lparr>t|;| \<sigma>,f\<rparr> |:| A" and
          weaker_ctx: " n \<le> length \<Gamma>" 
  shows "insert_nth n S \<Gamma> \<turnstile> \<lparr>shift_L 1 n t|;| \<sigma>,f\<rparr> |:| A"
using assms 
proof(induction \<Gamma> t \<sigma> f A arbitrary: n rule:has_type_L.induct)
  case (has_type_LAbs \<Gamma>1 T1 t2 \<sigma>1 f T2)
    
    have "Suc n\<le>length(\<Gamma>1|,|T1)" using has_type_LAbs(3) by auto

    hence "insert_nth (Suc n) S (\<Gamma>1 |,| T1) \<turnstile> \<lparr>shift_L 1 (Suc n) t2|;| \<sigma>1,f\<rparr> |:| T2"
      using has_type_LAbs(2)[where n="Suc n"]
      by auto
    then show ?case
      by (auto intro: has_type_L.has_type_LAbs)              
next 
  case(has_type_Tuple L TL \<Gamma>1 \<sigma>1 f)
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
  case (has_type_Let x \<Gamma> t1 \<sigma>1 f A t2 B)
    
    have "n \<le> x \<Longrightarrow> (take n \<Gamma> @ drop n \<Gamma> |,| S) \<turnstile> \<lparr>Let var Suc x := shift_L 1 n t1 in shift_L 1 n t2|;| \<sigma>1,f\<rparr> |:| B"
      using has_type_Let(1,4,6)
            has_type_Let(5)[unfolded length_insert_nth, of n] 
            insert_nth_comp(1)[of n \<Gamma> x]
      by (auto intro!: has_type_L.intros(10))

    then show ?case
      using has_type_Let(4)[OF has_type_Let(6)] 
            has_type_Let(5)[unfolded length_insert_nth, of "Suc n" ] 
            has_type_Let(6)
            insert_nth_comp(2)[OF has_type_Let(6),of x S A]  
      by (auto intro!: has_type_L.intros(10)) 
next
  case (has_type_LetPattern p B t1 \<sigma>1 \<Gamma> \<sigma>2 t2 A)
    note hyps=this
    show ?case
      using hyps(1,2,3) hyps(5,6)[OF hyps(7)]
      by (auto intro: has_type_L.intros(19))
next
  case (has_type_Case x \<Gamma>1 y t \<sigma>1 f A B t1 C t2)

    have Sum_type: "insert_nth n S \<Gamma>1 \<turnstile> \<lparr>shift_L 1 n t|;| \<sigma>1,f\<rparr> |:| A |+| B"
      using has_type_Case(6)[OF has_type_Case(9)] 
      by auto

    have B1:"n \<le> x \<Longrightarrow> n \<le> y \<Longrightarrow> insert_nth (Suc x) A (insert_nth n S \<Gamma>1) \<turnstile> \<lparr>shift_L 1 n t1|;|\<sigma>1,f\<rparr> |:| C \<and>
                                  insert_nth (Suc y) B (insert_nth n S \<Gamma>1) \<turnstile> \<lparr>shift_L 1 n t2|;|\<sigma>1,f\<rparr> |:| C"
      using  has_type_Case(7)[of n] has_type_Case(9)
             has_type_Case(8)[of n]
             insert_nth_comp(1)[of n \<Gamma>1 _ S _] length_insert_nth
      by (metis le_SucI)+

    have B2: " n \<le> x \<Longrightarrow> \<not> n \<le> y \<Longrightarrow> insert_nth (Suc x) A (insert_nth n S \<Gamma>1) \<turnstile> \<lparr>shift_L 1 n t1|;|\<sigma>1,f\<rparr> |:| C \<and> 
                                      insert_nth y B (insert_nth n S \<Gamma>1) \<turnstile> \<lparr>shift_L 1 (Suc n) t2|;|\<sigma>1,f\<rparr> |:| C"
      using  has_type_Case(7)[of n, unfolded length_insert_nth]
             has_type_Case(8)[of "Suc n", unfolded length_insert_nth]  
             has_type_Case(9) insert_nth_comp[of n \<Gamma>1 _ S _] 
      by (metis Suc_le_mono not_le le_SucI)+

    have B3: "\<not> n \<le> x \<Longrightarrow>  n \<le> y \<Longrightarrow> insert_nth x A (insert_nth n S \<Gamma>1) \<turnstile> \<lparr>shift_L 1 (Suc n) t1|;|\<sigma>1,f\<rparr> |:| C \<and>
                                      insert_nth (Suc y) B (insert_nth n S \<Gamma>1) \<turnstile> \<lparr>shift_L 1 n t2|;|\<sigma>1,f\<rparr> |:| C"
      using  has_type_Case(7)[of "Suc n", unfolded length_insert_nth]
             has_type_Case(8)[of n, unfolded length_insert_nth]  
             has_type_Case(9) insert_nth_comp[of n \<Gamma>1 _ S _] 
      by (metis Suc_le_mono not_le le_SucI)+

    have B4: "\<not> n \<le> x \<Longrightarrow> \<not> n \<le> y \<Longrightarrow> insert_nth x A (insert_nth n S \<Gamma>1) \<turnstile> \<lparr>shift_L 1 (Suc n) t1|;|\<sigma>1,f\<rparr> |:| C \<and>
                                      insert_nth y B (insert_nth n S \<Gamma>1) \<turnstile> \<lparr>shift_L 1 (Suc n) t2|;|\<sigma>1,f\<rparr> |:| C"
       using has_type_Case(7)[of "Suc n", unfolded length_insert_nth]
             has_type_Case(8)[of "Suc n", unfolded length_insert_nth]  
             has_type_Case(9) insert_nth_comp(2)[of n \<Gamma>1 _ S _] 
      by (metis Suc_le_mono not_le)+

    show ?case
      using has_type_Case(6)[OF has_type_Case(9)] has_type_Case(1,2)
            has_type_L.intros(22) B1 B2 B3 B4 
      by force      
next
  case (has_type_CaseV L I TL LT \<Gamma> t \<sigma>1 f A)
    have branches_wtyped:"\<forall>i<length L.
       insert_nth (map (\<lambda>x. if n \<le> x then nat (int x + 1) else x) I ! i) (TL ! i) (take n \<Gamma> @ drop n \<Gamma> |,| S)
       \<turnstile> \<lparr>((indexed_map 0 (\<lambda>k. shift_L 1 (if (I!k)<n then Suc n else n)) LT) ! i)|;| \<sigma>1,f\<rparr> |:| A \<and>  map (\<lambda>x. if n \<le> x then nat (int x + 1) else x) I ! i
       \<le> length (insert_nth n S \<Gamma>)"
      proof (rule+)
        fix i
        assume H:"i<length L"
        have P:"\<And>k. k\<le>length (insert_nth (I ! i) (TL ! i) \<Gamma>) \<Longrightarrow>
                     insert_nth k S (insert_nth (I ! i) (TL ! i) \<Gamma>) \<turnstile> \<lparr>shift_L 1 k (LT ! i)|;|\<sigma>1,f\<rparr>|:| A"
          using has_type_CaseV(8) H 
          by auto

        then have branches_type_n:"insert_nth n S (insert_nth (I ! i) (TL ! i) \<Gamma>) \<turnstile> \<lparr>shift_L 1 n (LT ! i)|;| \<sigma>1,f\<rparr> |:| A"
          using  has_type_CaseV(9)    
                 length_insert_nth[of "I!i" "TL!i" \<Gamma>]
          by (metis le_SucI)

        have branches_type_Sucn:"insert_nth (Suc n) S (insert_nth (I ! i) (TL ! i) \<Gamma>) \<turnstile> \<lparr>shift_L 1 (Suc n) (LT ! i)|;|\<sigma>1,f\<rparr> |:| A"
          using  has_type_CaseV(9)
                 length_insert_nth[of "I!i" "TL!i" \<Gamma>] P[of "Suc n"]
          by (metis Suc_le_mono)

        have 1:"n\<le> I!i \<Longrightarrow> insert_nth (map (\<lambda>x. if n \<le> x then nat (int x + 1) else x) I ! i) (TL ! i) (take n \<Gamma> @ drop n \<Gamma> |,| S)
                \<turnstile> \<lparr>((indexed_map 0 (\<lambda>k. shift_L 1 (if (I!k)<n then Suc n else n)) LT) ! i)|;|\<sigma>1,f\<rparr> |:| A"
          using has_type_CaseV(1,3,9) H        
          proof -
            
            assume hyps:"n \<le> I ! i" "L \<noteq> \<emptyset>" "length I = length L" "n \<le> length \<Gamma>" "i < length L"
            have simp_ind:"indexed_map 0 (\<lambda>k. shift_L 1 (if I ! k < n then Suc n else n)) LT ! i =
                  (shift_L 1 n (LT ! i))"
              using hyps(1,5)[unfolded has_type_CaseV(5)]
              by (simp add: indexed_to_map[of 0 "\<lambda>k. shift_L 1 (if I ! k < n then Suc n else n)" LT, simplified])
            
            from branches_type_n
              have "insert_nth (Suc (I ! i)) (TL ! i) (take n \<Gamma> @ drop n \<Gamma> |,| S) \<turnstile> \<lparr>shift_L 1 n (LT ! i)|;|\<sigma>1,f\<rparr> |:| A"
                using insert_nth_comp(1)[OF hyps(4,1)] H has_type_CaseV(4)
                by force
            
            with simp_ind show ?thesis using hyps by force

          qed

        have  "\<not> n\<le> I!i \<Longrightarrow> insert_nth (map (\<lambda>x. if n \<le> x then nat (int x + 1) else x) I ! i) (TL ! i) (take n \<Gamma> @ drop n \<Gamma> |,| S)
                \<turnstile> \<lparr>((indexed_map 0 (\<lambda>k. shift_L 1 (if (I!k)<n then Suc n else n)) LT) ! i)|;|\<sigma>1,f\<rparr> |:| A"
          using has_type_CaseV(1,3,9) H        
          proof -            
            assume hyps:"\<not>n \<le> I ! i" "L \<noteq> \<emptyset>" "length I = length L" "n \<le> length \<Gamma>" "i < length L"
            
            have simp_ind:"indexed_map 0 (\<lambda>k. shift_L 1 (if I ! k < n then Suc n else n)) LT ! i =
                  (shift_L 1 (Suc n) (LT ! i))"
              using hyps(1,5)[unfolded has_type_CaseV(5)]
              by (simp add: indexed_to_map[of 0 "\<lambda>k. shift_L 1 (if I ! k < n then Suc n else n)" LT, simplified])
            
            from branches_type_Sucn
              have  "insert_nth (I ! i) (TL ! i) (take n \<Gamma> @ drop n \<Gamma> |,| S) \<turnstile> \<lparr>shift_L 1 (Suc n) (LT ! i)|;|\<sigma>1,f\<rparr> |:| A"
                using insert_nth_comp(2)[OF hyps(4), of "I!i"] hyps(1)[unfolded not_le[of n "I!i"]]
                by fastforce

            with simp_ind show ?thesis using hyps by force
              
          qed

        with 1 show "insert_nth (map (\<lambda>x. if n \<le> x then nat (int x + 1) else x) I ! i) (TL ! i) (take n \<Gamma> @ drop n \<Gamma> |,| S)
         \<turnstile> \<lparr>((indexed_map 0 (\<lambda>k. shift_L 1 (if (I!k)<n then Suc n else n)) LT) ! i)|;| \<sigma>1,f\<rparr> |:| A"
          by blast
      next
        fix i
        assume H:"i<length L"
        show " map (\<lambda>x. if n \<le> x then nat (int x + 1) else x) I ! i
         \<le> length (insert_nth n S \<Gamma>)"
         using has_type_CaseV(3,8) H nth_map[of i I "\<lambda>x. if n \<le> x then nat (int x + 1) else x"]
         by force
      qed 

    show ?case
      using has_type_CaseV(1-5) indexed_to_map[of 0 "\<lambda>k. shift_L 1 (if I ! k < n then Suc n else n)" LT]
            has_type_CaseV(7)[OF has_type_CaseV(9)]
            branches_wtyped            
      by ((force intro!: has_type_L.intros(24))+)
      
qed (auto intro!: has_type_L.intros simp: nth_append min_def)

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
  case (CaseVar t L I LT)
    thus ?case by (induction LT, simp+)
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

method inv_type = (match premises in H:"\<Gamma> \<turnstile> \<lparr> t|;| \<sigma>, f\<rparr> |:| A" for \<Gamma> t \<sigma> f A \<Rightarrow>
                   \<open>insert "has_type_L.simps"[of \<Gamma> t \<sigma> f A, simplified]\<close>)  
    
theorem uniqueness_of_types:
  "\<Gamma> \<turnstile> \<lparr>t|;|\<sigma>,f\<rparr> |:| A \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t|;|\<sigma>,f\<rparr> |:| B \<Longrightarrow> A=B"
proof (induction \<Gamma> t \<sigma> f A arbitrary:B rule: has_type_L.induct)
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
     (metis prod.sel ltype.sel inversion(15,17,18,20,21,23,26-30))+)



lemma canonical_forms:
  "is_value_L v \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>v|;|\<sigma>,f\<rparr> |:| Bool \<Longrightarrow> v = LTrue \<or> v = LFalse"
  "is_value_L v \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>v|;|\<sigma>,f\<rparr> |:| T1 \<rightarrow> T2 \<Longrightarrow> \<exists>t n. v = LAbs T1 t"
  "is_value_L v \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>v|;|\<sigma>,f\<rparr> |:| Unit \<Longrightarrow> v = unit"
  "is_value_L v \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>v|;|\<sigma>,f\<rparr> |:| A |\<times>| B \<Longrightarrow> (\<exists>v1 v2. is_value_L v1 \<and> is_value_L v2 \<and> v= \<lbrace>v1,v2\<rbrace>)"
  "is_value_L v \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>v|;|\<sigma>,f\<rparr> |:| \<lparr>TL\<rparr> \<Longrightarrow> (\<exists>L. is_value_L (Tuple L) \<and> v = Tuple L \<and> length TL = length L)"
  "is_value_L v \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>v|;|\<sigma>,f\<rparr> |:| \<lparr>L|:|TL\<rparr> \<Longrightarrow> (\<exists>LT. is_value_L (Record L LT) \<and> v = (Record L LT))" 
  "is_value_L v \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>v|;|\<sigma>,f\<rparr> |:| <L|,|TL> \<Longrightarrow> (\<exists>i v1. i<length L \<and> is_value_L v1 \<and> v = <(L!i):=v1> as <L|,|TL>)"
  "is_value_L v \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>v|;|\<sigma>,f\<rparr> |:| A|+|B \<Longrightarrow> (\<exists>v1. is_value_L v1 \<and> v = inl v1 as A|+|B) \<or> (\<exists>v1. v = inr v1 as A|+|B \<and> is_value_L v1)"
  "is_value_L v \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>v|;|\<sigma>,f\<rparr> |:| \<lambda>List A \<Longrightarrow> (v = Lnil A \<and> f=False) \<or> (\<exists>v1 v2. is_value_L v1 \<and> is_value_L v2 \<and> v = Lcons A v1 v2)"
proof -
  assume  val: "is_value_L v" and 
          typed: "\<Gamma> \<turnstile> \<lparr>v|;|\<sigma>,f\<rparr> |:| A|+|B"
  show "(\<exists>v1. is_value_L v1 \<and> v = inl v1 as A|+|B) \<or> (\<exists>v1. v = inr v1 as A|+|B \<and> is_value_L v1)"
    using val typed
    by (induction rule: is_value_L.induct, auto elim: "has_type_L.cases")           
next
   assume  val: "is_value_L v" and 
          typed: "\<Gamma> \<turnstile> \<lparr>v|;|\<sigma>,f\<rparr> |:| <L|,|TL>"
  show "\<exists>i v1. i<length L \<and> is_value_L v1 \<and> v = <(L!i):=v1> as <L|,|TL>"
    using val typed
    by (induction rule: is_value_L.induct, auto elim: "has_type_L.cases")
qed (auto elim: "is_value_L.cases" "has_type_L.cases")  

lemma coherent_val_imp_Lmatch:
  "coherent p A \<Longrightarrow> \<Gamma>\<turnstile> \<lparr>t|;|\<sigma>,f\<rparr> |:| A \<Longrightarrow> is_value_L t \<Longrightarrow>\<exists>\<sigma>. Lmatch p t \<sigma>"
proof (induction arbitrary:t \<Gamma> \<sigma> f rule:coherent.induct)
  case (2 L PL TL)
    note hyps=this
    obtain LT where H:"is_value_L (Record L LT)" "t = Record L LT"
      using canonical_forms(6)[OF hyps(7,6)]
      by blast
         
    note lenTL_LT = hyps(6)[unfolded H(2) has_type_L.simps[of _ "Record L LT" _ _ "\<lparr>L|:|TL\<rparr>", simplified],
                        THEN conjunct2, THEN conjunct2, THEN conjunct1]
         and TL_types = hyps(6)[unfolded H(2) has_type_L.simps[of _ "Record L LT" _ _ "\<lparr>L|:|TL\<rparr>", simplified],
                        THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2]
      
    have "\<exists>F. (\<forall>i<length PL. Lmatch (PL ! i) (LT ! i) (F!i)) \<and> length F = length PL"
      using lenTL_LT TL_types H(1)[unfolded is_value_L.simps[of "Record L LT", simplified]]
            hyps(3)[symmetric] hyps(5)[of _ \<Gamma> "LT!_" \<sigma> f]
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
                hyps(6)[unfolded H(2) has_type_L.simps[of _ "Record L LT" _ _ "\<lparr>L|:|TL\<rparr>", simplified],
                        THEN conjunct2, THEN conjunct2]
                hyps(3)[symmetric] hyps(5)[of i \<Gamma> "LT!i" \<sigma> f] inf_len
          by presburger
        then show "Lmatch (PL ! i) (LT ! i) (F ! i)"
          using exF(1) inf_len 
          by presburger
      qed          
       
    then show ?case
      using "Lmatch.intros"(2)[OF _ _ exF(2) _ H(1)]
            hyps(6)[unfolded H(2) has_type_L.simps[of _ "Record L LT" _ _ "\<lparr>L|:|TL\<rparr>", simplified]]
            hyps(3) H(2)
      by force
qed (auto intro: Lmatch.intros) 

theorem progress:
  "\<emptyset> \<turnstile> \<lparr>t|;|empty, f\<rparr> |:| A \<Longrightarrow> is_value_L t \<or> (\<exists>t1. eval1_L t t1)"
proof (induction "\<emptyset>::ltype list" t "empty::nat\<rightharpoonup>ltype" f A rule: has_type_L.induct)
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
  case (has_type_CaseV L I TL LT t f A)
    note hyps=this
    show ?case
      using eval1_L.intros(32,33) hyps(7) canonical_forms(7)[OF _ hyps(6)] in_set_conv_nth
      by metis
next
  case (has_type_Case t f A B x t1 C y t2)
    note hyps=this
    show ?case
      using canonical_forms(8)[OF _ hyps(3)] hyps(4) eval1_L.intros(27-29)
      by blast
next
  case (has_type_LetPattern p B \<sigma> t1 f t2 A)
    note hyps=this
    show ?case 
      using hyps(4) coherent_val_imp_Lmatch[OF hyps(1,3)] eval1_L.intros(25,26) 
      by blast
qed (force intro!: is_value_L.intros eval1_L.intros dest: canonical_forms)+


lemma shift_down:
  "insert_nth n U \<Gamma> \<turnstile> \<lparr>t|;|\<sigma>,f\<rparr> |:| A \<Longrightarrow> n \<le> length \<Gamma> \<Longrightarrow>
   (\<And>x. x \<in> FV t \<Longrightarrow> x \<noteq> n) \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>shift_L (- 1) n t|;|\<sigma>,f\<rparr> |:| A"
proof (induction "insert_nth n U \<Gamma>" t \<sigma> f A arbitrary: \<Gamma> n U rule: has_type_L.induct)
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
  case (has_type_RCD L LT TL \<sigma> f)
    show ?case
      using has_type_RCD(1-4,8)
            has_type_RCD(6)[OF _ _ has_type_RCD(7), simplified]           
      by (force intro!: "has_type_L.intros"(16))+
next
  case (has_type_Let x t1 \<sigma>1 f A t2 B)
    note hyps=this
    have 1:"(\<And>x. x \<in> FV t1 \<Longrightarrow> x \<noteq> n)" "(\<And>z. (\<exists>y. y\<in>FV t2\<and> y\<noteq>x \<and> x<y \<and> z=y-Suc 0) \<Longrightarrow> z \<noteq> n)" "x\<noteq>n"
            "\<And>z. z \<in> FV t2 \<and> z \<noteq> x \<and> \<not> x < z \<Longrightarrow> z\<noteq>n"
      using hyps(7)[simplified, unfolded image_iff Bex_def, simplified]
      by blast+
        
    hence ins_eq:"n\<le>x \<Longrightarrow>insert_nth x A (insert_nth n U \<Gamma>) = insert_nth n U (insert_nth (x - Suc 0) A \<Gamma>)"
      using insert_nth_comp(1)[OF hyps(6), of "x-Suc 0" U A, symmetric]
      by force
    have "n\<le>x \<Longrightarrow> (\<And>x. x \<in> FV t2 \<Longrightarrow> x \<noteq> n)"
      using 1(2)[of "_-Suc 0", simplified] 1(3,4)
      by fastforce
      
    with 1(1,3) ins_eq have A:"n\<le>x \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Let var (x-Suc 0) := shift_L (-1) n t1 in shift_L (-1) n t2|;| \<sigma>1,f\<rparr> |:| B"
      using hyps(3)[OF _ hyps(6), simplified] 
            has_type_Let(5)[unfolded length_insert_nth, 
                            of n _ "insert_nth (x - Suc 0) A \<Gamma>"] 
            hyps(1,6) 
      by (force intro!: has_type_L.intros(10))
  
    have "\<not> n \<le> x \<Longrightarrow> (\<And>x. x \<in> FV t2 \<Longrightarrow> x \<noteq> Suc n)"
      using 1(2)[of "_-Suc 0", simplified] 1(3) 
      by fastforce
      
    hence "\<not> n \<le> x \<Longrightarrow>\<Gamma> \<turnstile> \<lparr>Let var x := shift_L (- 1) n t1 in shift_L (- 1) (Suc n) t2|;|\<sigma>1,f\<rparr> |:| B"
      using has_type_Let(5)[unfolded length_insert_nth, 
                            of "Suc n" _ "insert_nth x A \<Gamma>"] hyps(6)[unfolded Suc_le_mono[of n, symmetric]]
            insert_nth_comp(2)[OF hyps(6), of x U A, symmetric]
            not_le[of n x] hyps(3)[OF _ hyps(6),of U, simplified] 1(1)
      by (force intro!: has_type_L.intros(10))

    with A show ?case by fastforce
      
next
  case (has_type_ProjR L l TL t)
    note hyps=this
    show ?case
      using hyps(7)[simplified] hyps(1-3)
            hyps(5)[OF _ hyps(6), simplified]
      by (force intro!: has_type_L.intros(17))
next
  case (has_type_Case x y t \<sigma>1 f A B t1 C t2)
    note hyps=this  
    have FV_t: "x\<noteq>n" "y\<noteq>n" "\<And>z. z\<in>FV t \<Longrightarrow> z\<noteq>n" "\<And>z. z \<in> FV t2 \<and> z \<noteq> y \<and> \<not> y < z \<Longrightarrow> z\<noteq>n"
               "\<And>z. (\<exists>x. x \<in> FV t2 \<and> x \<noteq> y \<and> y < x \<and> z = x - Suc 0) \<Longrightarrow> z\<noteq>n"
               "\<And>z. z \<in> FV t1 \<and> z \<noteq> x \<and> \<not> x < z \<Longrightarrow> z\<noteq>n"
               "\<And>z. (\<exists>y. y \<in> FV t1 \<and> y \<noteq> x \<and> x < y \<and> z = y - Suc 0) \<Longrightarrow> z\<noteq>n"
      using hyps(10)[simplified, unfolded image_iff Bex_def, simplified]
      by blast+

    have Sum_type: "\<Gamma> \<turnstile> \<lparr>shift_L (-1) n t|;| \<sigma>1,f\<rparr> |:| A |+| B"
      using hyps(4)[OF _ hyps(9), simplified] FV_t
      by auto
    
    have le_x:"n \<le> x \<Longrightarrow> insert_nth x A (insert_nth n U \<Gamma>) = insert_nth n U (insert_nth (x - Suc 0) A \<Gamma>)"
      using One_nat_def diff_Suc_1 insert_nth_comp(1)[of n \<Gamma> "x-Suc 0" U A,OF hyps(9)]
            FV_t(1)
      by fastforce
    have le_y:"n \<le> y \<Longrightarrow> insert_nth y B (insert_nth n U \<Gamma>) = insert_nth n U (insert_nth (y - Suc 0) B \<Gamma>)"
      using One_nat_def diff_Suc_1 insert_nth_comp(1)[of n \<Gamma> "y-Suc 0" U B,OF hyps(9)]
            FV_t(2)
      by fastforce
    
    have ge_x:"\<not> n \<le> x \<Longrightarrow>  insert_nth x A (insert_nth n U \<Gamma>) = insert_nth (Suc n) U (insert_nth x A \<Gamma>)"
      using not_le insert_nth_comp(2)[OF hyps(9),of x U A] 
      by metis

    have ge_y:"\<not> n \<le> y \<Longrightarrow> insert_nth y B (insert_nth n U \<Gamma>) = insert_nth (Suc n) U (insert_nth y B \<Gamma>)" 
      using not_le insert_nth_comp(2)[OF hyps(9),of y U B] 
      by metis

    have FV_inf:"n \<le> x \<Longrightarrow> (\<And>z. z\<in>FV t1 \<Longrightarrow> z\<noteq>n)"
                "n \<le> y \<Longrightarrow> (\<And>z. z\<in>FV t2 \<Longrightarrow> z\<noteq>n)"
      using FV_t(5,7)[of "_-Suc 0", simplified] FV_t(1,2,4,6)
      by fastforce+

    have FV_sup:"\<not> n \<le> x \<Longrightarrow> (\<And>z. z\<in>FV t1 \<Longrightarrow> z\<noteq>Suc n)"
                "\<not> n \<le> y \<Longrightarrow> (\<And>z. z\<in>FV t2 \<Longrightarrow> z\<noteq>Suc n)"
      using FV_t(5,7)[of "_-Suc 0", simplified] FV_t(1,2)
      by fastforce+

    have B1:"n \<le> x \<Longrightarrow> n \<le> y \<Longrightarrow> insert_nth (x-Suc 0) A \<Gamma> \<turnstile> \<lparr>shift_L (-1) n t1|;|\<sigma>1,f\<rparr> |:| C \<and>
                                  insert_nth (y-Suc 0) B \<Gamma> \<turnstile> \<lparr>shift_L (-1) n t2|;|\<sigma>1,f\<rparr> |:| C"
      using  hyps(6)[OF le_x] hyps(9) FV_inf hyps(8)[OF le_y] 
      by force           

    have B2: " n \<le> x \<Longrightarrow> \<not> n \<le> y \<Longrightarrow> insert_nth (x-Suc 0) A \<Gamma> \<turnstile> \<lparr>shift_L (-1) n t1|;|\<sigma>1,f\<rparr> |:| C \<and> 
                                      insert_nth y B \<Gamma> \<turnstile> \<lparr>shift_L (-1) (Suc n) t2|;|\<sigma>1,f\<rparr> |:| C"
      using  hyps(6)[OF le_x] hyps(8)[OF ge_y] hyps(9) FV_inf(1) FV_sup(2)
      by force

    have B3: "\<not> n \<le> x \<Longrightarrow>  n \<le> y \<Longrightarrow> insert_nth x A \<Gamma> \<turnstile> \<lparr>shift_L (-1) (Suc n) t1|;|\<sigma>1,f\<rparr> |:| C \<and>
                                      insert_nth (y-Suc 0) B \<Gamma> \<turnstile> \<lparr>shift_L (-1) n t2|;|\<sigma>1,f\<rparr> |:| C"
      using hyps(6)[OF ge_x] hyps(8)[OF le_y] hyps(9) FV_inf(2) FV_sup(1)
      by force

    have B4: "\<not> n \<le> x \<Longrightarrow> \<not> n \<le> y \<Longrightarrow> insert_nth x A \<Gamma> \<turnstile> \<lparr>shift_L (-1) (Suc n) t1|;|\<sigma>1,f\<rparr> |:| C \<and>
                                      insert_nth y B \<Gamma> \<turnstile> \<lparr>shift_L (-1) (Suc n) t2|;|\<sigma>1,f\<rparr> |:| C"
       using hyps(6)[OF ge_x] hyps(8)[OF ge_y] hyps(9) FV_sup
       by force

    show ?case
      using Sum_type hyps(1,2,9)
            has_type_L.intros(22) B1 B2 B3 B4
      by force
next
  case (has_type_CaseV L I TL LT t \<sigma> f A)
    note hyps_t=this
    let ?f = " (\<lambda>k t. (\<lambda>y. y - Suc 0) ` ((FV t - {I ! k}) \<inter> Collect (op < (I ! k))) \<union> (FV t - {I ! k}) \<inter> 
                {y. \<not> I ! k < y})"

    have B:"{indexed_map 0 ?f LT ! i |
              i. i < length (indexed_map 0 (\<lambda>k t. (\<lambda>y. y - Suc 0) ` ((FV t - {I ! k}) \<inter> Collect (op < (I ! k))) \<union>
                                (FV t - {I ! k}) \<inter> {y. \<not> I ! k < y}) LT)} = {?f i (LT!i)|i. i<length LT}"
      using nth_indexed_map_0[of _ LT ?f] indexed_map_0_len[of ?f LT]
      by fastforce
      
    have FV_t: "\<And>z. z\<in>FV t \<Longrightarrow> z\<noteq>n" "\<And>i. i<length I \<Longrightarrow> I!i\<noteq>n"
                "\<And>z i. i<length LT \<Longrightarrow> z \<in> FV (LT!i) \<and> z \<noteq> (I!i) \<and> \<not> (I!i) < z \<Longrightarrow> z\<noteq>n"
                "\<And>z i. i<length LT \<Longrightarrow>(\<exists>y. y \<in> FV (LT!i) \<and> y \<noteq> (I!i) \<and> (I!i) < y \<and> z = y - Suc 0) \<Longrightarrow> z\<noteq>n"
      using hyps_t(10)[simplified, unfolded Bex_def set_conv_nth B, simplified]
            image_iff
      by blast+
      
    have branches_wtyped:"\<forall>i<length L.
       insert_nth (map (\<lambda>x. if n \<le> x then nat (int x + - 1) else x) I ! i) (TL ! i) \<Gamma>
       \<turnstile> \<lparr>(indexed_map 0 (\<lambda>k. shift_L (- 1) (if I ! k < n then Suc n else n)) LT ! i)|;|\<sigma>,f\<rparr> |:| A \<and> map (\<lambda>x. if n \<le> x then nat (int x + - 1) else x) I ! i \<le> length \<Gamma>"
      proof (rule+)
        fix i
        assume H:"i<length L"
        note i_lenLT = H[unfolded hyps_t(5)] and i_lenI=H[unfolded hyps_t(3)[symmetric]]
        have P:"\<And>k \<Gamma>' U'. insert_nth (I ! i) (TL ! i) (insert_nth n U \<Gamma>) = insert_nth k U' \<Gamma>' \<Longrightarrow> 
                        k\<le>length \<Gamma>' \<Longrightarrow> (\<forall>x. x \<in> FV (LT ! i) \<longrightarrow> x \<noteq> k) \<Longrightarrow>
                        \<Gamma>' \<turnstile> \<lparr>shift_L (-1) k (LT ! i)|;|\<sigma>,f\<rparr>|:| A"
          using hyps_t(8) H 
          by blast
          
        have 1:"n\<le> I!i \<Longrightarrow> insert_nth (map (\<lambda>x. if n \<le> x then nat (int x + -1) else x) I ! i) (TL ! i) \<Gamma>
                \<turnstile> \<lparr>((indexed_map 0 (\<lambda>k. shift_L (-1) (if (I!k)<n then Suc n else n)) LT) ! i)|;|\<sigma>,f\<rparr> |:| A"
          using hyps_t(1,3,9) H        
          proof -
            
            assume hyps:"n \<le> I ! i" "L \<noteq> \<emptyset>" "length I = length L" "n \<le> length \<Gamma>" "i < length L"
            have simp_ind:"indexed_map 0 (\<lambda>k. shift_L (-1) (if I ! k < n then Suc n else n)) LT ! i =
                  (shift_L (-1) n (LT ! i))"
              using hyps(1,5)[unfolded hyps_t(5)]
              by (simp add: indexed_to_map[of 0 "\<lambda>k. shift_L (-1) (if I ! k < n then Suc n else n)" LT, simplified])
            
            have ins_eq:"insert_nth (I ! i) (TL ! i) (insert_nth n U \<Gamma>) =
                    insert_nth n U (insert_nth (I ! i - Suc 0) (TL ! i) \<Gamma>)"
             proof -
               have "n< I!i"
                 using hyps(1)  hyps(5)[unfolded hyps(3)[symmetric]]
                       FV_t(2)
                 by force
               then have "n\<le> I!i - Suc 0" "Suc (I!i-Suc 0) = I!i"
                 by linarith+
               thus ?thesis
                 using insert_nth_comp(1)[OF hyps(4),of "I!i-Suc 0", symmetric]
                 by presburger
             qed
            
            from hyps(1) have "\<And>x. x \<in> FV (LT ! i) \<Longrightarrow> x \<noteq> n"
              using  FV_t(2)[OF i_lenI] FV_t(3) FV_t(4)[of i "_-Suc 0",simplified] i_lenLT
              by fastforce              
              
            with ins_eq have "insert_nth (I ! i - Suc 0) (TL ! i) \<Gamma> \<turnstile> \<lparr>shift_L (- 1) n (LT ! i)|;|\<sigma>,f\<rparr> |:| A"
              using P[of n U "insert_nth (I ! i - Suc 0) (TL ! i) \<Gamma>"] le_SucI[OF hyps(4)]
               by (metis H hyps(5) length_insert_nth)
       
            with simp_ind show ?thesis
              by (simp add: hyps min_def del: insert_nth_take_drop)
              
          qed

        have  "\<not> n\<le> I!i \<Longrightarrow> insert_nth (map (\<lambda>x. if n \<le> x then nat (int x + -1) else x) I ! i) (TL ! i) \<Gamma>
                \<turnstile> \<lparr>((indexed_map 0 (\<lambda>k. shift_L (-1) (if (I!k)<n then Suc n else n)) LT) ! i)|;|\<sigma>,f\<rparr> |:| A"
          using hyps_t(1,3,9) H        
          proof -            
            assume hyps:"\<not>n \<le> I ! i" "L \<noteq> \<emptyset>" "length I = length L" "n \<le> length \<Gamma>" "i < length L"
            
            have simp_ind:"indexed_map 0 (\<lambda>k. shift_L (-1) (if I ! k < n then Suc n else n)) LT ! i =
                  (shift_L (-1) (Suc n) (LT ! i))"
              using hyps(1,5)[unfolded hyps_t(5)]
              by (simp add: indexed_to_map[of 0 "\<lambda>k. shift_L (-1) (if I ! k < n then Suc n else n)" LT, simplified])
           
              from hyps(1) have "\<And>x. x \<in> FV (LT ! i) \<Longrightarrow> x \<noteq> Suc n"
                using  FV_t(2)[OF i_lenI] FV_t(4)[of i "_-Suc 0",simplified] i_lenLT

                by fastforce              
              hence  "insert_nth (I ! i) (TL ! i) \<Gamma> \<turnstile> \<lparr>shift_L (-1) (Suc n) (LT ! i)|;|\<sigma>,f\<rparr> |:| A"
                using insert_nth_comp(2)[OF hyps(4), of "I!i"] hyps(4)[unfolded Suc_le_mono[of n,symmetric]]
                      P[of "Suc n"] hyps(1)[unfolded not_le]
                by fastforce

            with simp_ind show ?thesis using hyps by simp
              
          qed

        with 1 show "insert_nth (map (\<lambda>x. if n \<le> x then nat (int x + - 1) else x) I ! i) (TL ! i) \<Gamma>
        \<turnstile> \<lparr>(indexed_map 0 (\<lambda>k. shift_L (- 1) (if I ! k < n then Suc n else n)) LT ! i)|;|\<sigma>,f\<rparr> |:| A"
          by fast
      next
        fix i
        assume H:"i<length L"
        show "map (\<lambda>x. if n \<le> x then nat (int x + - 1) else x) I ! i \<le> length \<Gamma>"
          using hyps_t(3,8,9) H nth_map[of i I "\<lambda>x. if n \<le> x then nat (int x + - 1) else x"]
          by (cases "n\<le>I!i") (force, presburger)
      qed 
    show ?case
      using hyps_t(1-5) indexed_to_map[of 0 "\<lambda>k. shift_L (-1) (if I ! k < n then Suc n else n)" LT]
            hyps_t(7)[OF _ hyps_t(9), simplified]
            FV_t branches_wtyped
      by (force intro!: has_type_L.intros(24))
qed (fastforce intro: has_type_L.intros simp: nth_append min_def)+

abbreviation incl_map::"pcontext \<Rightarrow> pcontext\<Rightarrow> bool" (infix "\<subseteq>\<^sub>f" 75) where
"\<sigma> \<subseteq>\<^sub>f \<sigma>1 \<equiv> (\<forall>x\<in>dom \<sigma>. \<sigma> x = \<sigma>1 x)"

abbreviation af::"lterm \<Rightarrow> bool \<Rightarrow> bool" where
"af t f \<equiv> (case t of Lnil _  \<Rightarrow> \<not>f | _\<Rightarrow>True)"

abbreviation afht::"lterm \<Rightarrow>bool\<Rightarrow> bool \<Rightarrow> bool" where
"afht t f1 f \<equiv> (case t of Lhead _ _  \<Rightarrow> f| Ltail _ _ \<Rightarrow> f | _\<Rightarrow>f1=f)"

lemma afht_shift : "afht s f f1 \<Longrightarrow> afht (shift_L d c s) f f1"
by (induction s, auto)

inductive agrees_flag::"lterm \<Rightarrow> bool \<Rightarrow> bool" where
 A_Unary: "subterms t = Unary t1 \<Longrightarrow> afht t f f1 \<Longrightarrow> agrees_flag t1 f1 \<Longrightarrow> agrees_flag t f"|
 A_Binary: "subterms t = Bi t1 t2 \<Longrightarrow> agrees_flag t1 f \<Longrightarrow> agrees_flag t2 f \<Longrightarrow> agrees_flag t f"|
 A_Ternary: "subterms t = Ter t1 t2 t3\<Longrightarrow> agrees_flag t1 f \<Longrightarrow> agrees_flag t2 f \<Longrightarrow> 
              agrees_flag t3 f  \<Longrightarrow> agrees_flag t f"|
 A_Comp: "subterms t = Comp t1 L\<Longrightarrow> agrees_flag t1 f \<Longrightarrow> (\<forall>i<length L. agrees_flag (L!i) f) \<Longrightarrow>
            agrees_flag t f"|
 A_List: "subterms t = UList L\<Longrightarrow> (\<forall>i<length L. agrees_flag (L!i) f) \<Longrightarrow>
            agrees_flag t f"|
 A_Void: "subterms t = Void \<Longrightarrow> af t f \<Longrightarrow> agrees_flag t f"

method agrees_m = (match conclusion in "agrees_flag t f" for t f \<Rightarrow>
                    \<open>insert agrees_flag.intros[of t, simplified], force\<close>)
method inv_agrees_f= (match premises in H:"agrees_flag t f" for t and f\<Rightarrow>
                      \<open>insert "agrees_flag.simps"[of t f, simplified]\<close>)

lemma welltyped_agreesf:
  "\<Gamma> \<turnstile> \<lparr>t|;|\<sigma>,f\<rparr> |:| A \<Longrightarrow> agrees_flag t f"
by (induction \<Gamma> t \<sigma> f A arbitrary: rule: has_type_L.induct) agrees_m+

lemma weakening_pattern_flag:
  "\<Gamma> \<turnstile> \<lparr>t|;|\<sigma>,f\<rparr> |:| A \<Longrightarrow> \<sigma> \<subseteq>\<^sub>f \<sigma>1 \<Longrightarrow> agrees_flag t f1 \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t|;|\<sigma>1,f1\<rparr> |:| A"
proof (induction \<Gamma> t \<sigma> f A arbitrary: \<sigma>1 f1 rule: has_type_L.induct)
  case (has_type_Tuple L TL \<Gamma> \<sigma> f)
    note hyps=this and ag = this(6)[unfolded agrees_flag.simps[of "Tuple _", simplified]]
    show ?case 
      using hyps(1,2) hyps(4)[of _ \<sigma>1] has_type_L.intros(14) hyps(5) ag
      by metis
next
  case (has_type_ProjT i TL \<Gamma> t \<sigma> f)
    note hyps=this and ag = this(6)[unfolded agrees_flag.simps[of "\<Pi> _ _", simplified]]
    show ?case 
      using hyps(1,2) hyps(4)[of \<sigma>1] has_type_L.intros(15) hyps(5) 
            ag
      by force
next
  case (has_type_RCD L TL LT \<Gamma> \<sigma> f)
    note hyps=this and ag = this(8)[unfolded agrees_flag.simps[of "Record _ _", simplified]]
    show ?case 
      using hyps(1-4,7) hyps(6)[of _ \<sigma>1 f1] ag
      by (force intro!: has_type_L.intros(16))
next
  case (has_type_LetPattern p  B \<sigma> \<Gamma> t1 \<sigma>2 f t2 A)
    note hyps=this and ag = this(8)[unfolded agrees_flag.simps[of "Let pattern _ :=  _ in _", simplified]]
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
      using hyps(1,2) hyps(5)[OF hyps(7)] hyps(6)[of "\<sigma>1++\<sigma>"] ag
      by (force intro: has_type_L.intros)
next
  case (has_type_Case)
    note hyps=this(1-9) and ag = this(10)[unfolded agrees_flag.simps[of "CaseSum _ _ _ _ _", simplified]]
    show ?case 
      using hyps(1,2,9) ag hyps(6-8)[of \<sigma>1 f1]
      by (force intro: has_type_L.intros)
next
  case (has_type_CaseV L I TL LT \<Gamma> t \<sigma> f A)
    note hyps=this and ag = this(10)[unfolded agrees_flag.simps[of "CaseVar  _ _ _ _", simplified]]
    have "\<forall>i<length L. insert_nth (I ! i) (TL ! i) \<Gamma> \<turnstile> \<lparr>(LT ! i)|;|\<sigma>1,f1\<rparr> |:| A \<and> I ! i \<le> length \<Gamma>"
      using hyps(8,9) ag[unfolded hyps(5)[symmetric], THEN conjunct2]
      by meson

    then show ?case 
      using hyps(1-5) hyps(7)[OF hyps(9) ag[THEN conjunct1]] 
      by (force intro!: has_type_L.intros)
qed (inv_agrees_f, force intro: has_type_L.intros simp: nth_append min_def)+

lemma agrees_f_true_imp_all:"agrees_flag t True \<Longrightarrow> agrees_flag t f"
by (induction t) (inv_agrees_f, agrees_m)+

lemma agrees_shift: "agrees_flag s f \<Longrightarrow> agrees_flag (shift_L d c s) f"
proof (induction s arbitrary: d c f)
  case (CaseVar t L I LT)
    note hyps=this and inv = this(3)[unfolded agrees_flag.simps[of "CaseVar _ _ _ _", simplified]]
    let ?f = "(\<lambda>k. shift_L d (if I ! k < c then Suc c else c))"
    let ?L = "indexed_map 0 ?f LT"
    have "length ?L = length LT"
      using indexed_to_map[of 0 ?f LT]
      by force
    hence "\<forall>i<length ?L. agrees_flag (?L ! i) f"
      using hyps(2) indexed_to_map[of 0 ?f LT]
            nth_map[of _ "zip [0..<0 + length LT] LT" "\<lambda>p. ?f (fst p) (snd p)", simplified]
            nth_zip[of _ "[0..<0 + length LT]" LT, simplified] fst_conv snd_conv inv
            in_set_conv_nth[of _ LT]
      by fastforce
      
    then show ?case
      using agrees_flag.intros(4)[of "CaseVar _ _ _ (indexed_map 0 (\<lambda>k. shift_L d (if I ! k < c then Suc c else c)) LT)", simplified]
            hyps(1) inv
      by auto      
qed (inv_agrees_f, agrees_m)+

lemma substitution:
  "\<Gamma> \<turnstile> \<lparr>t|;|\<sigma>,f\<rparr> |:| A \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>LVar n|;|\<sigma>1,f1\<rparr> |:| S \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>s|;|\<sigma>1,f1\<rparr> |:| S \<Longrightarrow>agrees_flag s f \<Longrightarrow> 
  \<sigma>1 \<subseteq>\<^sub>f \<sigma>\<Longrightarrow> \<Gamma> \<turnstile> \<lparr>subst_L n s t|;|\<sigma>,f\<rparr> |:| A"
proof (induction \<Gamma> t \<sigma> f A arbitrary: s n \<sigma>1 f1 rule: has_type_L.induct; inv_agrees_f)
  case (has_type_LAbs \<Gamma> T1 t \<sigma> f T2)
    note hyps=this and s_af= agrees_shift[OF this(5)]
    show ?case 
      using weakening[where n=0, unfolded insert_nth_def nat.rec] s_af
            inversion(4) hyps(2)[of "Suc n" \<sigma>1 f1 "shift_L 1 0 s"] hyps(6) 
            hyps(3,4) 
      by (fastforce intro!: has_type_L.intros)
next
  case (has_type_ProjT i TL \<Gamma> t \<sigma> f)
    note hyps=this 
    show ?case
      using has_type_L.intros(15)[OF hyps(1,2)] hyps(4-) 
      by force
next
  case (has_type_Let x \<Gamma> t1 \<sigma> f A t2 B)
    note hyps=this and ag = agrees_shift[OF this(8),of 1]
         
    have "x \<noteq> n \<Longrightarrow> x < n\<Longrightarrow> (Suc n, S) |\<in>| insert_nth x A \<Gamma>"
      proof -
        assume H: "x \<noteq> n" "x < n"
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
    hence A: " x \<noteq> n \<Longrightarrow> x < n \<longrightarrow> \<Gamma> \<turnstile> \<lparr>Let var x := subst_L n s t1 in subst_L (Suc n) (shift_L 1 x s) t2|;|\<sigma>,f\<rparr> |:| B"
      using hyps(4)[of n \<sigma>1 f1  s,OF _ _ hyps(8,9)] hyps(5)[of "Suc n",OF _ _ ag hyps(9), of f1] hyps(1,6,7)
            weakening[where n=x,OF _ hyps(1)] 
            inversion(4)[OF hyps(6)] hyps(5)[of "Suc n" \<sigma>1 f1 "shift_L 1 x s",OF _ _ ag hyps(9)]           
      by (force intro!: has_type_L.intros(4,10))
     
    have "x \<noteq> n \<Longrightarrow> \<not> x < n \<longrightarrow> \<Gamma> \<turnstile> \<lparr>Let var x := subst_L n s t1 in subst_L n (shift_L 1 x s) t2|;|\<sigma>,f\<rparr> |:| B"
      using hyps(4)[of n _ f1 s,OF _ _ hyps(8,9)] hyps(5)[of "Suc n",OF _ _ ag hyps(9), of f1] hyps(1,6-8) 
            weakening[where n=x,OF _ hyps(1)]
            inversion(4)[OF hyps(6)] hyps(5)[of _ _ f1 "shift_L 1 x s",OF _ _ ag hyps(9)] 
            not_less[of x n] nth_take[of n x \<Gamma>] nth_append[of "take x \<Gamma>" _ n, simplified]            
      by (force intro!: has_type_L.intros(4,10))

    with A show ?case
      using hyps(4)[of x \<sigma>1 f1 s] hyps(1,3,6-) ag
      by (force intro!: has_type_L.intros(10))
      
next
  case (has_type_LetPattern p B \<sigma> \<Gamma> t1 \<sigma>2 f t2 A)
    note hyps=this and ag = this(9)[unfolded "agrees_flag.simps"[of "Let pattern p := t1 in t2",simplified]]
    have A:"\<sigma>1 \<subseteq>\<^sub>f \<sigma>2 ++ \<sigma>"
      using hyps(10)
       sorry
    show ?case
      using hyps(5)[of n \<sigma>1 f1 s] hyps(1,2,7-) ag hyps(6)[of n \<sigma>1 f1 s, OF _ _ _ A]
      by (force intro!: has_type_L.intros)
next
  case (has_type_Case x \<Gamma> y t \<sigma>2 f A B t1 C t2)
    note hyps=this and ag=agrees_shift[OF this(11),of 1]
         
     have V_shifty:"y < n\<Longrightarrow> (Suc n, S) |\<in>| insert_nth y B \<Gamma>"
       proof -
         assume H: "y<n"
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
     
     have V_shiftx:"x < n\<Longrightarrow> (Suc n, S) |\<in>| insert_nth x A \<Gamma>"
       proof -
         assume H: "x < n"
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

     have Vx:"n\<noteq>x \<Longrightarrow> \<not>x < n\<Longrightarrow> (n, S) |\<in>| insert_nth x A \<Gamma>"
       using not_less[of x n] nth_take[of n x \<Gamma>] nth_append[of "take x \<Gamma>" _ n, simplified]
             inversion(4)[OF hyps(9), simplified] hyps(1)
       by auto

     have Vy:"n\<noteq>y \<Longrightarrow> \<not>y < n\<Longrightarrow> (n, S) |\<in>| insert_nth y B \<Gamma>"
       using not_less[of y n] nth_take[of n y \<Gamma>] nth_append[of "take y \<Gamma>" _ n, simplified]
             inversion(4)[OF hyps(9), simplified] hyps(1)
       by auto

     have B1:"n = x \<Longrightarrow> n \<noteq> y \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>subst_L n s (Case t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2)|;|\<sigma>2,f\<rparr> |:| C"
       proof -
         assume H: "n = x" "n \<noteq> y"
          
         from V_shifty have A:"n = x \<Longrightarrow> x \<noteq> y \<Longrightarrow> y < x \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Case subst_L x s t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> subst_L (Suc x) (shift_L 1 y s) t2|;|\<sigma>2,f\<rparr> |:| C"
           using hyps(8)[of "Suc x" \<sigma>1 f1 "shift_L 1 y s",OF _ _ ag hyps(12)]  hyps(1,2,4) 
                 hyps(6)[OF hyps(9,10) hyps(11,12)]  
                 weakening[OF hyps(10) hyps(2)] has_type_L.intros(4)
           by (force intro!: has_type_L.intros(22))
    
         have "n = x \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<not> y < x \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Case subst_L x s t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> subst_L x (shift_L 1 y s) t2|;|\<sigma>2,f\<rparr> |:| C"
           using hyps(1,2,4,12) hyps(6)[OF hyps(9,10) hyps(11,12)] 
                 hyps(8)[of x \<sigma>1 f1 "shift_L 1 y s",OF _ _ ag hyps(12)] 
                 weakening[OF hyps(10) hyps(2)] Vy[OF H(2)]
           by (force intro!: has_type_L.intros(4,22))
         with A H show ?thesis by force
     qed

    have B2: "n \<noteq> x \<Longrightarrow> n = y \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>subst_L n s (Case t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2)|;|\<sigma>2,f\<rparr> |:| C"
      proof -
        assume H: "n \<noteq> x" "n = y"

        from V_shiftx have A:" n \<noteq> x \<Longrightarrow> x < n \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Case subst_L y s t of Inl x \<Rightarrow> subst_L (Suc y) (shift_L 1 x s) t1 | Inr y \<Rightarrow> t2|;|\<sigma>2,f\<rparr> |:| C"
          using hyps(6)[OF hyps(9,10-12)] hyps(1,2,5) H ag weakening[OF hyps(10) hyps(1)]
                hyps(7)[of "Suc n" \<sigma>1 f1 "shift_L 1 x s", OF _ _ _ hyps(12)]                
          by (force intro!: has_type_L.intros(4,22))
        have "n \<noteq> x \<Longrightarrow> \<not> x < n \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Case subst_L y s t of Inl x \<Rightarrow> subst_L y (shift_L 1 x s) t1 | Inr y \<Rightarrow> t2|;|\<sigma>2,f\<rparr> |:| C"
          using hyps(1,2,5) H hyps(6)[OF hyps(9-12)] weakening[OF hyps(10) hyps(1)] Vx[OF H(1)]
                hyps(7)[of y \<sigma>1 f1 "shift_L 1 x s",OF _ _ _ hyps(12)] ag                 
          by (force intro!: has_type_L.intros(4,22))
        
        with A H show ?thesis by force
      qed
    
    have "n \<noteq> x \<Longrightarrow> n \<noteq> y \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>subst_L n s (Case t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2)|;|\<sigma>2,f\<rparr> |:| C"
      proof -
        assume H: "n \<noteq> x" "n \<noteq> y"
      
        have C1: "n \<noteq> x \<Longrightarrow> n \<noteq> y \<Longrightarrow> x < n \<Longrightarrow> y < n \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Case subst_L n s t of Inl x \<Rightarrow> subst_L (Suc n) (shift_L 1 x s) t1 | Inr y \<Rightarrow>
           subst_L (Suc n) (shift_L 1 y s) t2|;|\<sigma>2,f\<rparr> |:| C"
          using hyps(1,2,12) hyps(6)[OF hyps(9-12)] ag 
                hyps(7,8)[of "Suc n" \<sigma>1 f1 "shift_L 1 _ s", OF _ _ _ hyps(12)] weakening[OF hyps(10)]
                has_type_L.intros(4)[OF V_shiftx]  has_type_L.intros(4)[OF V_shifty]
          by (force intro!: has_type_L.intros(22))
        have C2: "n \<noteq> x \<Longrightarrow> n \<noteq> y \<Longrightarrow> x < n \<Longrightarrow> \<not>y < n \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Case subst_L n s t of Inl x \<Rightarrow> subst_L (Suc n) (shift_L 1 x s) t1 | Inr y \<Rightarrow>
           subst_L n (shift_L 1 y s) t2|;|\<sigma>2,f\<rparr> |:| C"
          using hyps(7,8)[of _ \<sigma>1 f1 "shift_L 1 _ s",OF _ _ _ hyps(12)] hyps(6)[OF hyps(9,10-12)]
                weakening[OF hyps(10)]  hyps(1,2)                 
                has_type_L.intros(4)[OF V_shiftx]  has_type_L.intros(4)[OF V_shifty] ag
                has_type_L.intros(4)[OF Vx] has_type_L.intros(4)[OF Vy]
          by (force intro!: has_type_L.intros(22))
        have C3: "n \<noteq> x \<Longrightarrow> n \<noteq> y \<Longrightarrow> \<not>x < n \<Longrightarrow> y < n \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Case subst_L n s t of Inl x \<Rightarrow> subst_L n (shift_L 1 x s) t1 | Inr y \<Rightarrow>
           subst_L (Suc n) (shift_L 1 y s) t2|;|\<sigma>2,f\<rparr> |:| C"
          using hyps(7,8)[of _ \<sigma>1 f1 "shift_L 1 _ s"] weakening[OF hyps(10)]  hyps(1,2,12) 
                hyps(6)[OF hyps(9,10-12)] ag 
                has_type_L.intros(4)[OF V_shiftx]  has_type_L.intros(4)[OF V_shifty]
                has_type_L.intros(4)[OF Vx] has_type_L.intros(4)[OF Vy]
          by (force intro!: has_type_L.intros(22))

        have "n \<noteq> x \<Longrightarrow> n \<noteq> y \<Longrightarrow> \<not>x < n \<Longrightarrow> \<not>y < n \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Case subst_L n s t of Inl x \<Rightarrow> subst_L n (shift_L 1 x s) t1 | Inr y \<Rightarrow>
           subst_L n (shift_L 1 y s) t2|;|\<sigma>2,f\<rparr> |:| C"
          using hyps(7,8)[of _ \<sigma>1 f1 "shift_L 1 _ s"] weakening[OF hyps(10)] ag hyps(1,2,12) 
                hyps(6)[OF hyps(9,10-12)]
                has_type_L.intros(4)[OF Vx] has_type_L.intros(4)[OF Vy]
          by (force intro!: has_type_L.intros(22))

        with C1 C2 C3 H show ?thesis by simp          
      qed
    
    with B1 B2 show ?case
      using hyps(6)[of x \<sigma>1 f1 s] hyps(9-) hyps(1,2,4,5) ag
      by (cases "n=x"; cases "n=y") (force intro: has_type_L.intros(22))
    
next
  case (has_type_CaseV L I TL LT \<Gamma> t \<sigma> f A)
    note hyps=this and ag= agrees_shift[OF this(11),of 1]

    have " \<forall>i<length L. insert_nth (I ! i) (TL ! i) \<Gamma> \<turnstile> 
          \<lparr>(map (\<lambda>p. if n = fst p then snd p else subst_L (if n>fst p then Suc n else n) (shift_L 1 (fst p) s) (snd p)) (zip I LT)!i)|;|\<sigma>,f\<rparr>|:| A"
      proof (rule+)
        fix i
        assume H1: "i<length L"
        have P:"\<And>n s \<sigma>1 fa. insert_nth (I ! i) (TL ! i) \<Gamma> \<turnstile> \<lparr>LVar n|;|\<sigma>1,fa\<rparr> |:| S \<Longrightarrow>
               insert_nth (I ! i) (TL ! i) \<Gamma> \<turnstile> \<lparr>s|;|\<sigma>1,fa\<rparr> |:| S \<Longrightarrow> agrees_flag s f \<Longrightarrow> \<sigma>1 \<subseteq>\<^sub>f \<sigma> \<Longrightarrow>
               insert_nth (I ! i) (TL ! i) \<Gamma> \<turnstile> \<lparr>subst_L n s (LT ! i)|;|\<sigma>,f\<rparr> |:| A"
               "I ! i \<le> length \<Gamma>"
          using hyps(8) H1
          by blast+
        
        have "n = I ! i \<Longrightarrow> insert_nth (I ! i) (TL ! i) \<Gamma> \<turnstile> \<lparr>(LT ! i)|;|\<sigma>,f\<rparr> |:| A" 
          using hyps(8) H1
          by blast

        moreover have "n \<noteq> I ! i \<Longrightarrow> insert_nth (I ! i) (TL ! i) \<Gamma> \<turnstile> \<lparr>subst_L (if n > I!i  then Suc n else n) (shift_L 1 (I!i) s) (LT ! i)|;|\<sigma>,f\<rparr> |:| A"
          proof -
            assume H:"n \<noteq> I ! i"
            have V_shift:"I!i < n\<Longrightarrow> (Suc n, S) |\<in>| insert_nth (I!i) (TL!i) \<Gamma>"
              proof -
                assume H: "I!i < n"
                have 1:"Suc n < length (insert_nth (I!i) (TL!i) \<Gamma>)"
                  using inversion(4)[OF hyps(9), simplified] P(2)
                  by force
                have "(insert_nth (I!i) (TL!i) \<Gamma>) ! (Suc n) = S"
                  proof -
                    have "(insert_nth (I!i) (TL!i) \<Gamma>) ! (Suc n) =  (drop (I!i) \<Gamma> |,| (TL!i)) ! (Suc n - I!i)"
                      using nth_append[of "take (I!i) \<Gamma>" "drop (I!i) \<Gamma> |,| (TL!i)" "Suc n", unfolded length_take,  simplified]
                            not_less[of "Suc n" "I!i"] less_imp_le[OF less_SucI[OF H]] P(2)
                      by (simp add: min.commute min_def) 
                    moreover have "... = drop (I!i) \<Gamma> ! (n - I!i)"
                      using nth_Cons[of "TL!i" "drop (I!i) \<Gamma>" "Suc n-(I!i)", simplified] 
                            less_SucI[OF H]
                      by force
                    ultimately show ?thesis
                      using nth_drop[of "I!i" "n-I!i" \<Gamma>] inversion(4)[OF hyps(9), simplified]
                            H
                      by force
                  qed
                with 1 show ?thesis by simp
              qed
              (*
            have ag_i: "agrees_flag (LT!i) f"
              using ag H1 has_type_CaseV(5)
              by force
*)
            have "n\<le>I!i \<Longrightarrow>  insert_nth (I ! i) (TL ! i) \<Gamma> \<turnstile> \<lparr>subst_L  n (shift_L 1 (I!i) s) (LT ! i)|;|\<sigma>,f\<rparr> |:| A"
              using P(1)[of n \<sigma>1 f1] inversion(4)[OF hyps(9)] has_type_LVar[of n S "insert_nth (I!i) (TL!i) \<Gamma>" _ ]
                    weakening[OF hyps(10), of "I!i" "TL!i"] H P(2) (*ag_i*) hyps(12) ag
                    nth_take[of n "I!i" \<Gamma>] nth_append[of "take (I!i) \<Gamma>" _ n, simplified]
              by force

            moreover have "\<not> n\<le>I!i \<Longrightarrow>  insert_nth (I ! i) (TL ! i) \<Gamma> \<turnstile> \<lparr>subst_L (Suc n) (shift_L 1 (I!i) s) (LT ! i)|;|\<sigma>,f\<rparr> |:| A"
              using P(1)[of "Suc n" \<sigma>1 f1] has_type_LVar[OF V_shift] not_le[of n "I!i"] ag
                    weakening[OF hyps(10), of "I!i" "TL!i"] P(2) hyps(12)
              by presburger
            ultimately show "insert_nth (I ! i) (TL ! i) \<Gamma> \<turnstile> \<lparr>subst_L (if n > I!i  then Suc n else n) (shift_L 1 (I!i) s) (LT ! i)|;|\<sigma>,f\<rparr> |:| A"
              by simp
          qed
        ultimately show "insert_nth (I ! i) (TL ! i) \<Gamma> \<turnstile> 
          \<lparr>(map (\<lambda>p. if n = fst p then snd p else subst_L (if n > fst p then Suc n else n) (shift_L 1 (fst p) s) (snd p)) (zip I LT)!i)|;|\<sigma>,f\<rparr>|:| A"
          using nth_map[of i "(zip I LT)" "(\<lambda>p. if n = fst p then snd p else subst_L (if n > fst p then Suc n else n) (shift_L 1 (fst p) s) (snd p))"]
                hyps(3,5) H1
          by simp
      qed

    then show ?case
      using hyps(1-5,7,8,9-) ag
      by (force intro!: has_type_L.intros(24))      
next
  case (has_type_tail \<Gamma> t \<sigma> A f)
    note hyps=this and ag = agrees_shift[OF this(5),of 1]
    show ?case
      using hyps(2)[of n \<sigma>1 f1 s] hyps(3,4-) ag 
      (*by (force intro!: has_type_L.intros)*) sorry
next
  case (has_type_head)
    note hyps=this and ag = this(5)[unfolded "agrees_flag.simps"[of "Lhead _ _", simplified]]
    show ?case
      using hyps(2)[of n \<sigma>1 f1 s] hyps(3,4-) ag 
     (* by (force intro!: has_type_L.intros)*) sorry
next
  case (has_type_LVar x A \<Gamma> \<sigma> f)
    note hyps=this
    show ?case
      using hyps(1,2) inversion(4) weakening_pattern_flag[OF hyps(3,5,4)]           
      by (force intro!: has_type_L.intros)
qed (auto intro!: has_type_L.intros agrees_shift dest: inversion(4))

method inv_eval = (match premises in H:"eval1_L t t1" for t and t1 \<Rightarrow>
                    \<open>insert eval1_L.simps[of t t1, simplified]\<close>)


inductive contains::"lterm\<Rightarrow>lterm\<Rightarrow> bool" where
 C_eq : "contains s s"|
 C_Unary: "subterms t = Unary t1 \<Longrightarrow> contains s t1 \<Longrightarrow> contains s t"|
 A_Binary: "subterms t = Bi t1 t2 \<Longrightarrow> contains s t1 \<or> contains s t2 \<Longrightarrow> contains s t"|
 A_Ternary: "subterms t = Ter t1 t2 t3\<Longrightarrow> contains s t1 \<or> contains s t2 \<or> contains s t3 
              \<Longrightarrow> contains s t"|
 A_Comp: "subterms t = Comp t1 L\<Longrightarrow> contains s t1 \<or> (\<exists>i<length L. contains s (L!i)) \<Longrightarrow>
            contains s t"|
 A_List: "subterms t = UList L\<Longrightarrow> (\<exists>i<length L. contains s (L!i)) \<Longrightarrow>
            contains s t"
 
method inv_contains = (match premises in H:"contains s t" for s t \<Rightarrow>
                        \<open>insert "contains.simps"[of s t, simplified]\<close>)

method m1 = (match premises in "\<not>contains (Lnil B) t" for t B\<Rightarrow> 
              \<open>insert "contains.simps"[of "Lnil _" t, simplified]\<close>)


lemma Flagged_contains_not_nil:
  "\<Gamma> \<turnstile> \<lparr>t|;|\<sigma>,True\<rparr> |:| A \<Longrightarrow> \<not> contains (Lnil B) t"
by (induction \<Gamma> t \<sigma> "True" A arbitrary: B rule: has_type_L.induct)
     ((rule notI, inv_contains, force)+)


method m2= (match premises in "\<forall>B. \<not>contains (Lnil B) t" for t\<Rightarrow> 
              \<open>insert "contains.simps"[of "Lnil _" t, simplified]\<close>)

lemma No_nil_imp_irr_flag:
  "\<Gamma> \<turnstile> \<lparr>t|;|\<sigma>,f\<rparr> |:| A \<Longrightarrow> (\<forall>B. \<not> contains (Lnil B) t) \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t|;|\<sigma>,f1\<rparr> |:| A"
proof (induction \<Gamma> t \<sigma> f A arbitrary: f1 rule: has_type_L.induct)
  case (has_type_RCD)
    note hyps=this
    show ?case 
      using hyps(7)[unfolded contains.simps[of _ "Record _ _", simplified]]
            hyps has_type_L.intros
      by presburger
next
  case (has_type_CaseV)
    note hyps=this
    show ?case
      using hyps(9)[unfolded contains.simps[of _ "CaseVar _ _ _ _", simplified]]
            hyps has_type_L.intros
      by force
qed  (m2, meson has_type_L.intros contains.simps[of _ "Lhead _ _"] contains.simps[of _ "Ltail _ _"] 
          "contains.simps"[of "Lnil _" "Lnil _", simplified])+





lemma pattern_substitution:
  "\<Gamma> \<turnstile> \<lparr>tb|;|(\<sigma>2 ++ \<sigma>1),f\<rparr> |:| A \<Longrightarrow> (\<forall>x\<in>dom \<sigma>1. \<exists>B t' f1. \<sigma>1 x = Some B \<and> \<sigma> x = Some t' \<and>\<emptyset> \<turnstile> \<lparr>t'|;|\<sigma>2,f1\<rparr> |:| B) \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>fill \<sigma> tb|;|\<sigma>2,f\<rparr> |:| A"
proof (induction \<Gamma> tb "\<sigma>2++\<sigma>1" f A arbitrary: \<sigma> rule: has_type_L.induct)
  case (has_type_ProjT)
    thus ?case using "has_type_L.intros"(15) by auto
next
  case (has_type_Let)
    thus ?case sorry
next
  case (has_type_PatternVar)
    thus ?case sorry
next
  case (has_type_LetPattern)
    thus ?case sorry
next
  case (has_type_Case)
    thus ?case sorry
next
  case (has_type_CaseV)
    thus ?case sorry
qed (auto intro: has_type_L.intros)

lemma lmatch_coherent_char:
  "Lmatch_Type p \<sigma>1 \<Longrightarrow> coherent p B \<Longrightarrow> Lmatch p t1 (fill \<sigma>) \<Longrightarrow> is_value_L t1\<Longrightarrow>
    \<Gamma> \<turnstile> \<lparr>t1|;|\<sigma>2,f\<rparr> |:| B \<Longrightarrow>\<forall>x\<in>dom \<sigma>1. \<exists>B t' f1. \<sigma>1 x = Some B \<and> \<sigma> x = Some t' \<and> \<emptyset> \<turnstile> \<lparr>t'|;|\<sigma>2,f1\<rparr> |:| B"
sorry

theorem Preservation:
  "\<Gamma> \<turnstile> \<lparr>t|;|\<sigma>,f\<rparr> |:| A \<Longrightarrow> eval1_L t t1 \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t1|;|\<sigma>,f\<rparr> |:| A"
proof (induction \<Gamma> t \<sigma> f A arbitrary: t1 rule: has_type_L.induct)
  case (has_type_LApp \<Gamma> ta \<sigma> f T11 T12 tb)
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
        have "\<Gamma> |,| T11 \<turnstile> \<lparr>subst_L 0 (shift_L 1 0 tb) t12|;|\<sigma>,f\<rparr> |:| T12"
          using substitution[of "\<Gamma>|,|T11" _ \<sigma> f T12 0 \<sigma> f T11 "shift_L 1 0 tb", simplified]
                hyps(1)[unfolded H(1) has_type_L.simps[of _ "LAbs _ _", simplified]]
                welltyped_agreesf has_type_L.intros(4)[of 0 T11 "\<Gamma>|,|T11", simplified]
                weakening[OF hyps(2),of 0 T11, simplified]
          by blast
        moreover have "\<And>x. x \<in> (if 0 \<in> FV t12 then FV t12 - {0} \<union> Suc ` FV tb else FV t12) \<Longrightarrow> 0 < x"
          by (cases "0\<in>FV t12") (fastforce, metis not_gr0) 
        ultimately show ?case
          using shift_down[of 0 T11 \<Gamma> "subst_L 0 (shift_L 1 0 tb) t12" \<sigma> f T12, unfolded FV_subst FV_shift[of 1 0,simplified],
                        simplified] H(2)
          by blast
      qed

    ultimately show ?case using inv by blast

next
  case (has_type_Let x \<Gamma> ta \<sigma> f A tb B)
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
          using FV_shift[of 1 x ta, unfolded image_def Bex_def]
          proof (simp)
            assume "\<exists>xa. xa \<in> FV ta \<and> x1 = (if x \<le> xa then xa + 1 else xa)"
            then obtain x2 where "x2 \<in> FV ta \<and> x1 = (if x \<le> x2 then x2 + 1 else x2)"
              by blast
            with H show False
              by (cases "x\<le>x2")fastforce+
          qed    
              
        then show False 
          using H(1)[unfolded FV_subst[of x "shift_L 1 x ta" tb] image_iff]
          by (cases "x\<in>FV tb") (simp add: H(2))+
      qed

    hence "t1 =shift_L (- 1) x (subst_L x (shift_L 1 x ta) tb) \<and> is_value_L ta \<Longrightarrow> ?case"
      using substitution[OF hyps(3) has_type_LVar[OF 1] weakening[OF hyps(2,1), of A], simplified] 
            agrees_shift[OF welltyped_agreesf[OF hyps(2)]] 
            shift_down[of x A \<Gamma> "(subst_L x (shift_L 1 x ta) tb)" \<sigma> f B, OF _ hyps(1)]
      by force      
     
    with inv show ?case using hyps(1,3,4) has_type_L.intros(10) by fast
next
  case (has_type_Tuple L TL \<Gamma> \<sigma> f)
    note hyps=this(1-4) and inv= this(5)[unfolded eval1_L.simps[of "Tuple _",simplified]]
    from inv obtain j t' where H: "t1 = Tuple (replace (j-1) t' L)"
                                  "Suc 0 \<le> j" "j \<le> length L" "is_value_L (Tuple (take (j - Suc 0) L))" 
                                  "eval1_L (L ! (j - Suc 0)) t'"
      by auto
    have "\<And>i. \<not> length L \<le> j - Suc 0 \<Longrightarrow>
         0 \<le> i \<Longrightarrow>
         i < length (take (j - Suc 0) L @ t' # drop (Suc (j - Suc 0)) L) \<Longrightarrow>
         \<Gamma> \<turnstile> \<lparr>((take (j - Suc 0) L @ t' # drop (Suc (j - Suc 0)) L) ! i)|;|\<sigma>,f\<rparr> |:| (TL ! i)"
      proof -
        fix i
        assume Hi:"\<not> length L \<le> j - Suc 0" "0 \<le> i" "i < length (take (j - Suc 0) L @ t' # drop (Suc (j - Suc 0)) L)"
        show "\<Gamma> \<turnstile> \<lparr>((take (j - Suc 0) L @ t' # drop (Suc (j - Suc 0)) L) ! i)|;|\<sigma>,f\<rparr> |:| (TL ! i)"
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
  case (has_type_RCD L LT TL \<Gamma> \<sigma> f)
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
  case (has_type_LetPattern p B \<sigma>1 \<Gamma> ta \<sigma>2 f tb A)
    note hyps=this(1-6) and inv=this(7)[unfolded eval1_L.simps[of "Let pattern _ := _ in _", simplified]]
    have "\<forall>x\<in>dom \<sigma>1. \<exists>B. \<sigma>1 x = Some B" by blast
      
    have "(\<exists>\<sigma>. t1 = \<sigma> tb \<and> is_value_L ta \<and> Lmatch p ta \<sigma>) \<Longrightarrow>?case"
      using pattern_substitution[OF hyps(4)] lmatch_is_fill[of p ta _]
            lmatch_coherent_char[OF hyps(2,1) _ _ hyps(3)]
      by force
   
    then show ?case using inv has_type_L.intros(19)[OF hyps(1,2,5,4)] by fast
next
  case (has_type_Case x \<Gamma> y t \<sigma>1 f A B ta C tb)
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
            assume H:"x1 \<in> FV (subst_L x (shift_L 1 x v) ta)" "x1 = x"
            have "x1\<in>FV (shift_L (int 1) x v) \<Longrightarrow> False"
              using FV_shift[of 1 x v, unfolded image_def Bex_def]
              proof (simp)
                assume "\<exists>xa. xa \<in> FV v \<and> x1 = (if x \<le> xa then xa + 1 else xa)"
                then obtain x2 where "x2 \<in> FV v \<and> x1 = (if x \<le> x2 then x2 + 1 else x2)"
                  by blast
                with H show False
                  by (cases "x\<le>x2")fastforce+
              qed    
                  
            then show False 
              using H(1)[unfolded FV_subst[of x "shift_L 1 x v" ta] image_iff]
              by (cases "x\<in>FV ta") (simp add: H(2))+
          qed
        with H show ?case 
          using hyps(1) has_type_LVar[of x A "insert_nth x A \<Gamma>"] 
                nth_append[of "take x \<Gamma>" "drop x \<Gamma>|,|A" x, simplified]
                weakening[of \<Gamma> v \<sigma>1 f A _ A,OF _ hyps(1)] 
                hyps(3)[unfolded H has_type_L.simps[of _ "inl _ as _", simplified]]
                substitution[OF hyps(4), of x \<sigma>1 f, simplified]
                agrees_shift[OF welltyped_agreesf[of \<Gamma> v \<sigma>1 f]] 
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
            assume H:"x1 \<in> FV (subst_L y (shift_L 1 y v) tb)" "x1 = y"
            have "x1\<in>FV (shift_L (int 1) y v) \<Longrightarrow> False"
              using FV_shift[of 1 y v, unfolded image_def Bex_def]
              proof (simp)
                assume "\<exists>xa. xa \<in> FV v \<and> x1 = (if y \<le> xa then xa + 1 else xa)"
                then obtain x2 where "x2 \<in> FV v \<and> x1 = (if y \<le> x2 then x2 + 1 else x2)"
                  by blast
                with H show False
                  by (cases "y\<le>x2")fastforce+
              qed    
                  
            then show False 
              using H(1)[unfolded FV_subst[of y "shift_L 1 y v" tb] image_iff]
              by (cases "y\<in>FV tb") (simp add: H(2))+
          qed
        with H show ?case 
          using hyps(2) has_type_LVar[of y B "insert_nth y B \<Gamma>"] 
                nth_append[of "take y \<Gamma>" "drop y \<Gamma>|,|B" y, simplified]
                weakening[of \<Gamma> v \<sigma>1 f B _ B,OF _ hyps(2)] 
                hyps(3)[unfolded H has_type_L.simps[of _ "inr _ as _", simplified]]
                substitution[OF hyps(5), of y \<sigma>1 f, simplified]
                agrees_shift[OF welltyped_agreesf[of \<Gamma> v \<sigma>1 f]] 
                shift_down[of y B \<Gamma> "(subst_L y (shift_L 1 y v) tb)", OF _ hyps(2)]
          by fastforce
      qed

    ultimately show ?case using inv has_type_L.intros(22)[OF hyps(1,2,6,4,5)] by fast
      
next
  case (has_type_CaseV L I TL LT \<Gamma> t \<sigma> f A)
    note hyps=this and inv=this(9)[unfolded eval1_L.simps[of "CaseVar _ _ _ _", simplified]]
    have P:" \<forall>i<length L. I ! i \<le> length \<Gamma> \<and> insert_nth (I ! i) (TL ! i) \<Gamma> \<turnstile> \<lparr>(LT ! i)|;|\<sigma>,f\<rparr> |:| A" 
      using hyps(8)
      by blast
    have "\<exists>l v. l\<in>set L \<and> (\<exists>A. t = <l:=v> as A) \<and>
           t1 = shift_L (- 1) (I ! index L l)
                 (subst_L (I ! index L l) (shift_L 1 (I ! index L l) v) (LT ! index L l))
          \<Longrightarrow> ?case"
      proof -
        assume "\<exists>l v. l\<in>set L \<and> (\<exists>A. t = <l:=v> as A) \<and> t1 = shift_L (- 1) (I ! index L l)
                 (subst_L (I ! index L l) (shift_L 1 (I ! index L l) v) (LT ! index L l))"
        then obtain v l A1 where H:"l\<in>set L" "t = <l:=v> as A1"
                                    "t1 = shift_L (- 1) (I!index L l) (subst_L (I!index L l) 
                                          (shift_L 1 (I!index L l) v) (LT! index L l))"
          by blast
        from H(1) obtain i where simps:"l= L!i" "index L (L!i) = i" "i<length L"
          using in_set_conv_nth[of l L] index_nth_id[OF hyps(2)]
          by fast
        note H = H[unfolded simps]

        have "\<And>xa. xa \<in> FV (subst_L (I ! i) (shift_L 1 (I ! i) v) (LT ! i)) \<Longrightarrow> xa \<noteq> (I!i)"        
          proof 
            fix x1
            assume H:"x1 \<in> FV (subst_L (I ! i) (shift_L 1 (I ! i) v) (LT ! i))" "x1 = I!i"
            have "x1\<in>FV (shift_L (int 1) (I!i) v) \<Longrightarrow> False"
              using FV_shift[of 1 "I!i" v, unfolded image_def Bex_def]
              proof (simp)
                assume "\<exists>xa. xa \<in> FV v \<and> x1 = (if I!i \<le> xa then xa + 1 else xa)"
                then obtain x2 where "x2 \<in> FV v \<and> x1 = (if I!i \<le> x2 then x2 + 1 else x2)"
                  by blast
                with H show False
                  by (cases "I!i\<le>x2")fastforce+
              qed    
                  
            then show False 
              using H(1)[unfolded FV_subst[of "I!i" "shift_L 1 (I!i) v" "LT!i"] image_iff]
              by (cases "(I!i)\<in>FV (LT!i)") (simp add: H(2))+
          qed
        moreover have "\<Gamma> \<turnstile> \<lparr>v|;|\<sigma>,f\<rparr> |:| (TL ! i)"
          using hyps(6)[unfolded H has_type_L.simps[of _ "<_:= _> as _", simplified]]
                hyps(2) index_nth_id simps(2)
          by fastforce
        ultimately show ?case 
          using P has_type_LVar[of "I!i" "TL!i" "insert_nth (I!i) (TL!i) \<Gamma>"] H(3) simps(3)
                nth_append[of "take (I!i) \<Gamma>" "drop (I!i) \<Gamma>|,|(TL!i)" "I!i", simplified]
                weakening[of \<Gamma> v \<sigma> f "TL!i" "I!i" "TL!i"] 
                substitution[of "insert_nth (I!i) (TL!i) \<Gamma>" "LT!i" \<sigma> f]
                agrees_shift[OF welltyped_agreesf[of \<Gamma> v \<sigma> f]] 
                shift_down[of "I!i" "TL!i" \<Gamma> "(subst_L (I!i) (shift_L 1 (I!i) v) (LT!i))"]
          by fastforce
      qed
    with inv show ?case using has_type_L.intros(24)[OF hyps(1-5,7)] hyps(8) by blast
next
  case (has_type_Fix \<Gamma> t \<sigma> f A t1)
    note hyps=this(1,2) and inv=this(3)[unfolded eval1_L.simps[of "fix t" t1, simplified]]
    have 1:"\<And>x t. x \<in> FV (subst_L 0 (fix LAbs A (shift_L 1 (Suc 0) t)) t) \<Longrightarrow> x \<noteq> 0"
      proof 
        fix x t1'
        assume A:"x \<in> FV (subst_L 0 (fix LAbs A (shift_L 1 (Suc 0) t1')) t1')" "x=0"
        show "False"           
          using A(1)[unfolded A(2)] FV_subst[of 0 "fix LAbs A (shift_L 1 (Suc 0) t1')" t1',unfolded FV.simps(25)] 
                FV.simps(5)[of A "shift_L 1 (Suc 0) t1'",unfolded image_def FV_shift[of 1 "Suc 0" t1', simplified]]
          by (cases "0\<in>FV t1'") fastforce+
      qed
    
    have "\<exists>A t'. t = LAbs A t' \<and> t1 = shift_L (- 1) 0 (subst_L 0 (fix LAbs A (shift_L 1 (Suc 0) t')) t')
          \<Longrightarrow> ?case"
      proof -
        assume "\<exists>A t'. t = LAbs A t' \<and> t1 = shift_L (- 1) 0 (subst_L 0 (fix LAbs A (shift_L 1 (Suc 0) t')) t')"
      
        then obtain A' t' where H:"t = LAbs A' t' \<and> t1 = shift_L (- 1) 0 (subst_L 0 (fix LAbs A' (shift_L 1 (Suc 0) t')) t')"
          by blast
        have 2:"\<Gamma> |,| A \<turnstile> \<lparr>fix LAbs A (shift_L 1 (Suc 0) t')|;|\<sigma>,f\<rparr> |:| A"
          using has_type_L.intros(25)[of "\<Gamma>|,|A" "LAbs A (shift_L 1 (Suc 0) t')" \<sigma> f A]
                has_type_L.intros(5)[OF weakening[of "\<Gamma>|,|A" t' \<sigma> f A "Suc 0" A, simplified]]
                inversion(5) hyps(1)[unfolded H[THEN conjunct1]] 
          by blast
        have "agrees_flag (fix LAbs A (shift_L 1 (Suc 0) t')) f"
          using "agrees_flag.intros"(1)[of "fix LAbs A (shift_L 1 (Suc 0) t')" _ f f, simplified]
                "agrees_flag.intros"(1)[of "LAbs A (shift_L 1 (Suc 0) t')" _ f f, simplified]
                agrees_shift[OF welltyped_agreesf[OF hyps(1)[unfolded H[THEN conjunct1]]], simplified]
                inversion(5) hyps(1)[unfolded H[THEN conjunct1]] 
          by fast

        hence "insert_nth 0 A \<Gamma> \<turnstile> \<lparr>subst_L 0 (fix LAbs A (shift_L 1 (Suc 0) t')) t'|;|\<sigma>,f\<rparr> |:| A"
          using inversion(5)[OF hyps(1)[unfolded H[THEN conjunct1]], simplified]
                substitution[OF _ _ 2,of t' \<sigma> f A 0,simplified]
                has_type_LVar[of 0 A "\<Gamma>|,|A" \<sigma> f, simplified]
          by fastforce
        
        with 1[of _ t'] show ?case
          using shift_down[of 0 A \<Gamma> "subst_L 0 (fix LAbs A (shift_L 1 (Suc 0) t')) t'" \<sigma> f A]
                H[THEN conjunct2] inversion(5)[OF hyps(1)[unfolded H[THEN conjunct1]], simplified]
          by fast
      qed
    then show ?case using inv hyps(2) has_type_L.intros(25) by blast      
next
  case (has_type_head \<Gamma> t \<sigma> A f)
    note hyps=this and inv=this(3)[unfolded eval1_L.simps[of "Lhead _ _", simplified]]
    show ?case
      using inv hyps(1)
            No_nil_imp_irr_flag[of \<Gamma> _ \<sigma> True A f] Flagged_contains_not_nil[of \<Gamma> _ \<sigma> A _ ]
            has_type_L.intros(28)[OF hyps(2)] inversion(30)
      by blast
next
  case (has_type_tail \<Gamma> t \<sigma> A f)
    note hyps=this and inv=this(3)[unfolded eval1_L.simps[of "Ltail _ _", simplified]]
    show ?case
      using inv hyps(1)
          No_nil_imp_irr_flag[of \<Gamma> _ \<sigma> True "\<lambda>List A" f] Flagged_contains_not_nil[of \<Gamma> _ \<sigma> "\<lambda>List A" _ ]
          has_type_L.intros(29)[OF hyps(2)] inversion(30)
      by meson
qed (inv_eval, force intro!: "has_type_L.intros" dest: inversion(11,12,14,16))+

end
