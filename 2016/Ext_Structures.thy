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
    "is_value_L v \<Longrightarrow> Lmatch (V n as A) v (fill (\<lambda>p. if (p=n) then v else (<|V p as A|>)))" |
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
    " m<length LT \<Longrightarrow> is_value_L (Record (take m L) (take m LT)) \<Longrightarrow> 
      eval1_L (LT ! m) (t') \<Longrightarrow> eval1_L (Record L LT) (Record L (replace m t' LT))" |   
 -- "Rules relating to evaluation of pattern matching"
  eval1_L_LetPV:
    "Lmatch p v1 \<sigma> \<Longrightarrow> eval1_L (Let pattern p := v1 in t2) (\<sigma> t2)" |
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
    "coherent p B\<Longrightarrow> Lmatch_Type p \<sigma> \<Longrightarrow> dom \<sigma>1 \<inter> dom \<sigma> = {} \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t1|;| \<sigma>1,f\<rparr> |:| B \<Longrightarrow>
     \<Gamma> \<turnstile> \<lparr>t2|;|(\<sigma> ++ \<sigma>1), f\<rparr> |:| A \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Let pattern p := t1 in t2|;| \<sigma>1, f\<rparr> |:| A" |
  has_type_Inl:
    "\<Gamma> \<turnstile> \<lparr>t1|;| \<sigma>1,f\<rparr> |:| A \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>inl t1 as A|+|B |;|\<sigma>1,f\<rparr> |:| A|+|B" |
  has_type_Inr:
    "\<Gamma> \<turnstile> \<lparr>t1|;| \<sigma>1,f\<rparr> |:| B \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>inr t1 as A|+|B |;| \<sigma>1,f\<rparr> |:| A|+|B" |
  has_type_Case:
    "x\<le>length \<Gamma> \<Longrightarrow> y\<le>length \<Gamma> \<Longrightarrow>\<Gamma> \<turnstile> \<lparr> t|;| \<sigma>1,f \<rparr> |:| A|+|B \<Longrightarrow> insert_nth x A \<Gamma> \<turnstile> \<lparr>t1|;| \<sigma>1,f\<rparr> |:| C \<Longrightarrow>
     insert_nth y B \<Gamma> \<turnstile> \<lparr>t2|;| \<sigma>1,f\<rparr> |:| C \<Longrightarrow> 
     \<Gamma> \<turnstile> \<lparr>Case t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2 |;| \<sigma>1,f\<rparr> |:| C" |
  has_type_Variant:
    "i<length L \<Longrightarrow> length L=length TL \<Longrightarrow> \<Gamma> \<turnstile> \<lparr> t |;| \<sigma>,f \<rparr> |:| (TL!i) \<Longrightarrow> 
      \<Gamma> \<turnstile> \<lparr> <(L!i):=t> as <L|,|TL> |;|\<sigma>,f \<rparr> |:| <L|,|TL>" |
  has_type_CaseV:
    " L\<noteq>\<emptyset> \<Longrightarrow> length I = length L \<Longrightarrow> length L = length TL \<Longrightarrow> 
      length L = length LT \<Longrightarrow>
      \<Gamma> \<turnstile> \<lparr> t |;| \<sigma>,f \<rparr> |:| <L|,|TL> \<Longrightarrow> 
      (\<forall>i<length L. insert_nth (I!i) (TL!i) \<Gamma> \<turnstile> \<lparr>(LT!i)|;| \<sigma>,f\<rparr> |:| A) \<Longrightarrow>
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
  "\<Gamma> \<turnstile> \<lparr> t as A |;| \<sigma>,f\<rparr> |:| R \<Longrightarrow> R = A"
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
  "\<Gamma> \<turnstile> \<lparr>Let pattern p := t1 in t2|;|\<sigma>1,f\<rparr> |:| R \<Longrightarrow>\<exists>\<sigma> B. coherent p B\<and> Lmatch_Type p \<sigma>  \<and> \<Gamma> \<turnstile> \<lparr>t1|;|\<sigma>1,f\<rparr> |:| B \<and>  dom \<sigma>1 \<inter> dom \<sigma> = {} \<and>
                                                  \<Gamma> \<turnstile> \<lparr>t2|;|(\<sigma> ++  \<sigma>1), f\<rparr> |:| R" 
  "\<Gamma> \<turnstile> \<lparr>inl t as R1|;|\<sigma>1,f\<rparr> |:| R \<Longrightarrow>R1 = R \<and> (\<exists>A B. R = A|+|B \<and> \<Gamma> \<turnstile> \<lparr>t|;|\<sigma>1,f\<rparr> |:| A)"
  "\<Gamma> \<turnstile> \<lparr>inr t as R1|;|\<sigma>1,f\<rparr> |:| R \<Longrightarrow>R1 = R \<and> (\<exists>A B. R = A|+|B \<and> \<Gamma> \<turnstile> \<lparr>t|;|\<sigma>1,f\<rparr> |:| B)"
  "\<Gamma> \<turnstile> \<lparr>Case t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2|;|\<sigma>1,f\<rparr> |:| R \<Longrightarrow>\<exists>A B C. R = C \<and> \<Gamma> \<turnstile> \<lparr>t|;|\<sigma>1,f\<rparr> |:| A|+|B \<and> x\<le>length \<Gamma> \<and> y\<le>length \<Gamma> \<and>
                                                          insert_nth x A \<Gamma> \<turnstile> \<lparr>t1|;|\<sigma>1,f\<rparr> |:| C \<and> insert_nth y B \<Gamma> \<turnstile> \<lparr>t2|;|\<sigma>1,f\<rparr> |:| C"
   "\<Gamma> \<turnstile> \<lparr> <l:=t> as R1 |;| \<sigma>1,f \<rparr> |:| R \<Longrightarrow>R=R1 \<and> (\<exists>L TL i. R=<L|,|TL> \<and> \<Gamma> \<turnstile> \<lparr> t |;| \<sigma>1,f \<rparr> |:| (TL!i) \<and> l = L!i \<and> i<length L \<and> length L = length TL)" 
    " \<Gamma> \<turnstile> \<lparr> Case t of <L1:=I> \<Rightarrow> LT |;| \<sigma>1,f\<rparr> |:| A \<Longrightarrow>\<exists>TL. L1\<noteq>\<emptyset> \<and> length I = length L1 \<and> length L1 = length TL \<and> length L1 = length LT \<and>
      \<Gamma> \<turnstile> \<lparr> t |;| \<sigma>1,f \<rparr> |:| <L1|,|TL> \<and> (\<forall>i<length L1. insert_nth (I!i) (TL!i) \<Gamma> \<turnstile> \<lparr>(LT!i)|;| \<sigma>1,f\<rparr> |:| A)"
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
  show "\<exists>\<sigma> B. coherent p B \<and> Lmatch_Type p \<sigma>  \<and>  \<Gamma> \<turnstile> \<lparr>t1|;|\<sigma>1,f\<rparr> |:| B \<and>  dom \<sigma>1 \<inter> dom \<sigma> = {} \<and> \<Gamma> \<turnstile> \<lparr>t2|;|(\<sigma> ++ \<sigma>1),f\<rparr> |:| R"
    using has_type_LetPE[OF H1]
    by metis
next
  assume H2: "\<Gamma> \<turnstile> \<lparr>Case t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2|;|\<sigma>1,f\<rparr> |:| R"
  show "\<exists>A B C. R = C \<and> \<Gamma> \<turnstile> \<lparr>t|;|\<sigma>1,f\<rparr> |:| A |+| B \<and> x\<le>length \<Gamma> \<and> y\<le>length \<Gamma> \<and> insert_nth x A \<Gamma> \<turnstile> \<lparr>t1|;|\<sigma>1,f\<rparr> |:| C \<and> insert_nth y B \<Gamma> \<turnstile> \<lparr>t2|;|\<sigma>1,f\<rparr> |:| C"
    using has_type_CaseSE[OF H2]
    by fastforce
next
  assume H4: "\<Gamma> \<turnstile> \<lparr><l:=t> as R1|;|\<sigma>1,f\<rparr> |:| R"
  show  "R=R1 \<and> (\<exists>L TL i. R = <L|,|TL> \<and> \<Gamma> \<turnstile> \<lparr>t|;|\<sigma>1,f\<rparr> |:| (TL ! i) \<and> l = L ! i \<and> i<length L \<and> length L = length TL)"
    using has_type_VariantE[OF H4]
    by metis    
next
  assume H5: "\<Gamma> \<turnstile> \<lparr>Case t of <L1:=I> \<Rightarrow> LT|;|\<sigma>1,f\<rparr> |:| A"
  show "\<exists>TL. L1\<noteq>\<emptyset> \<and> length I = length L1 \<and> length L1 = length TL \<and> length L1 = length LT \<and>
      \<Gamma> \<turnstile> \<lparr> t |;| \<sigma>1,f \<rparr> |:| <L1|,|TL> \<and> (\<forall>i<length L1. insert_nth (I!i) (TL!i) \<Gamma> \<turnstile> \<lparr>(LT!i)|;| \<sigma>1,f\<rparr> |:| A)"
    using has_type_CaseVE[OF H5]
    by (metis append_Cons append_Nil insert_nth_take_drop)
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


lemma fill_fill_comp:
  "fill \<sigma> \<circ> fill \<sigma>1 = fill (fill \<sigma> \<circ> \<sigma>1)"
proof (rule)
  fix x
  show "(fill \<sigma> \<circ> fill \<sigma>1) x= fill (fill \<sigma> \<circ> \<sigma>1) x"
    proof (induction x arbitrary: \<sigma> \<sigma>1)
      case (Pattern p)
        show ?case
          by (induction p, simp+)
    qed simp+
qed

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
            insert_nth_comp(1)[OF has_type_Let(6), of x S A]           
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
      using hyps(1,2,3) hyps(6)[OF hyps(8)]
            hyps(7)[OF hyps(8)]
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
       \<turnstile> \<lparr>((indexed_map 0 (\<lambda>k. shift_L 1 (if (I!k)<n then Suc n else n)) LT) ! i)|;| \<sigma>1,f\<rparr> |:| A"
      proof (rule+)
        fix i
        assume H:"i<length L"
        have P:"\<And>k. k\<le>length (insert_nth (I ! i) (TL ! i) \<Gamma>) \<Longrightarrow>
                     insert_nth k S (insert_nth (I ! i) (TL ! i) \<Gamma>) \<turnstile> \<lparr>shift_L 1 k (LT ! i)|;|\<sigma>1,f\<rparr>|:| A"
          using has_type_CaseV(7) H 
          by auto

        then have branches_type_n:"insert_nth n S (insert_nth (I ! i) (TL ! i) \<Gamma>) \<turnstile> \<lparr>shift_L 1 n (LT ! i)|;| \<sigma>1,f\<rparr> |:| A"
          using  has_type_CaseV(8)    
                 length_insert_nth[of "I!i" "TL!i" \<Gamma>]
          by (metis le_SucI)

        have branches_type_Sucn:"insert_nth (Suc n) S (insert_nth (I ! i) (TL ! i) \<Gamma>) \<turnstile> \<lparr>shift_L 1 (Suc n) (LT ! i)|;|\<sigma>1,f\<rparr> |:| A"
          using  has_type_CaseV(8)
                 length_insert_nth[of "I!i" "TL!i" \<Gamma>] P[of "Suc n"]
          by (metis Suc_le_mono)

        have 1:"n\<le> I!i \<Longrightarrow> insert_nth (map (\<lambda>x. if n \<le> x then nat (int x + 1) else x) I ! i) (TL ! i) (take n \<Gamma> @ drop n \<Gamma> |,| S)
                \<turnstile> \<lparr>((indexed_map 0 (\<lambda>k. shift_L 1 (if (I!k)<n then Suc n else n)) LT) ! i)|;|\<sigma>1,f\<rparr> |:| A"
          using has_type_CaseV(1,2,8) H        
          proof -
            
            assume hyps:"n \<le> I ! i" "L \<noteq> \<emptyset>" "length I = length L" "n \<le> length \<Gamma>" "i < length L"
            have simp_ind:"indexed_map 0 (\<lambda>k. shift_L 1 (if I ! k < n then Suc n else n)) LT ! i =
                  (shift_L 1 n (LT ! i))"
              using hyps(1,5)[unfolded has_type_CaseV(4)]
              by (simp add: index_not_index_cong[of 0 "\<lambda>k. shift_L 1 (if I ! k < n then Suc n else n)" LT, simplified])
            
            from branches_type_n
              have "insert_nth (Suc (I ! i)) (TL ! i) (take n \<Gamma> @ drop n \<Gamma> |,| S) \<turnstile> \<lparr>shift_L 1 n (LT ! i)|;|\<sigma>1,f\<rparr> |:| A"
                using insert_nth_comp(1)[OF hyps(4,1)] H has_type_CaseV(4)
                by force
            
            with simp_ind show ?thesis using hyps by force

          qed

        have  "\<not> n\<le> I!i \<Longrightarrow> insert_nth (map (\<lambda>x. if n \<le> x then nat (int x + 1) else x) I ! i) (TL ! i) (take n \<Gamma> @ drop n \<Gamma> |,| S)
                \<turnstile> \<lparr>((indexed_map 0 (\<lambda>k. shift_L 1 (if (I!k)<n then Suc n else n)) LT) ! i)|;|\<sigma>1,f\<rparr> |:| A"
          using has_type_CaseV(1,2,8) H        
          proof -            
            assume hyps:"\<not>n \<le> I ! i" "L \<noteq> \<emptyset>" "length I = length L" "n \<le> length \<Gamma>" "i < length L"
            
            have simp_ind:"indexed_map 0 (\<lambda>k. shift_L 1 (if I ! k < n then Suc n else n)) LT ! i =
                  (shift_L 1 (Suc n) (LT ! i))"
              using hyps(1,5)[unfolded has_type_CaseV(4)]
              by (simp add: index_not_index_cong[of 0 "\<lambda>k. shift_L 1 (if I ! k < n then Suc n else n)" LT, simplified])
            
            from branches_type_Sucn
              have  "insert_nth (I ! i) (TL ! i) (take n \<Gamma> @ drop n \<Gamma> |,| S) \<turnstile> \<lparr>shift_L 1 (Suc n) (LT ! i)|;|\<sigma>1,f\<rparr> |:| A"
                using insert_nth_comp(2)[OF hyps(4), of "I!i"] hyps(1)[unfolded not_le[of n "I!i"]]
                by fastforce

            with simp_ind show ?thesis using hyps by force
              
          qed

        with 1 show "insert_nth (map (\<lambda>x. if n \<le> x then nat (int x + 1) else x) I ! i) (TL ! i) (take n \<Gamma> @ drop n \<Gamma> |,| S)
         \<turnstile> \<lparr>((indexed_map 0 (\<lambda>k. shift_L 1 (if (I!k)<n then Suc n else n)) LT) ! i)|;| \<sigma>1,f\<rparr> |:| A"
          by blast
      qed 
    show ?case
      using has_type_CaseV(1-4) index_not_index_cong[of 0 "\<lambda>k. shift_L 1 (if I ! k < n then Suc n else n)" LT]
            has_type_CaseV(6)[OF has_type_CaseV(8)]
            branches_wtyped            
      by (force intro!: has_type_L.intros(24))
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

method inv_type = (match premises in H:"\<Gamma> \<turnstile> \<lparr> t|;| \<sigma>, f\<rparr> |:| A" for \<Gamma> t \<sigma> f A \<Rightarrow>
                   \<open>simp add:"has_type_L.simps"[of \<Gamma> t \<sigma> f A, simplified]\<close>)  
    
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
      using inversion(19)[OF hyps(8)]
            hyps(7) Lmatch_Type_det[OF hyps(2)]
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
                      metis One_nat_def Suc_less_eq Suc_pred le_neq_implies_less length_Cons nth_Cons'
                            "is_value_L.intros"(7) "is_value_L.simps"[of "Record L' LT'", simplified])              
          then show ?case
            using Cons(5)[of 0, simplified]
            by fastforce
      qed 
    then show ?case
      using eval1_L_RCD[of _ LT L] "is_value_L.intros"(7)[of "take _ LT" "take _ L", simplified]
      by force
next
  case (has_type_ProjT i TL t)
   thus ?case 
     by (metis eval1_L.intros canonical_forms)     
next
  case (has_type_CaseV L I TL LT t f A)
    note hyps=this
    show ?case
      using eval1_L.intros(32,33) hyps(6) canonical_forms(7)[OF _ hyps(5)]
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
      using hyps(5) coherent_val_imp_Lmatch[OF hyps(1,4)] eval1_L.intros(25,26) 
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
    have 1:"(\<And>x. x \<in> FV t1 \<Longrightarrow> x \<noteq> n)" "(\<And>y. y\<in> FV t2 \<Longrightarrow> y \<noteq> n)" "x\<noteq>n"
      using hyps(7)[simplified]
      by blast+
        
    hence "n\<le>x \<Longrightarrow>insert_nth x A (insert_nth n U \<Gamma>) = insert_nth n U (insert_nth (x - Suc 0) A \<Gamma>)"
      using insert_nth_comp(1)[OF hyps(6), of "x-Suc 0" U A, symmetric]
      by force
    with 1 have A:"n\<le>x \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Let var (x-Suc 0) := shift_L (-1) n t1 in shift_L (-1) n t2|;| \<sigma>1,f\<rparr> |:| B"
      using hyps(3)[OF _ hyps(6), simplified] 
             has_type_Let(5)[unfolded length_insert_nth, 
                            of n _ "insert_nth (x - Suc 0) A \<Gamma>"] 
            hyps(1,6) 
      by (force intro!: has_type_L.intros(10))
    have "\<And>x. x\<in>FV t2 \<Longrightarrow> x\<noteq>Suc n" sorry

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
    note hyps=this and FV_t=this(10)[simplified]
    have Sum_type: "\<Gamma> \<turnstile> \<lparr>shift_L (-1) n t|;| \<sigma>1,f\<rparr> |:| A |+| B"
      using hyps(4)[OF _ hyps(9), simplified] FV_t
      by auto
    
    have le_x:"n \<le> x \<Longrightarrow> insert_nth x A (insert_nth n U \<Gamma>) = insert_nth n U (insert_nth (x - Suc 0) A \<Gamma>)"
      using One_nat_def diff_Suc_1 insert_nth_comp(1)[of n \<Gamma> "x-Suc 0" U A,OF hyps(9)]
            FV_t[of x, simplified]
      by fastforce
    have le_y:"n \<le> y \<Longrightarrow> insert_nth y B (insert_nth n U \<Gamma>) = insert_nth n U (insert_nth (y - Suc 0) B \<Gamma>)"
      using One_nat_def diff_Suc_1 insert_nth_comp(1)[of n \<Gamma> "y-Suc 0" U B,OF hyps(9)]
            FV_t[of y, simplified]
      by fastforce
    
    have ge_x:"\<not> n \<le> x \<Longrightarrow>  insert_nth x A (insert_nth n U \<Gamma>) = insert_nth (Suc n) U (insert_nth x A \<Gamma>)"
      using not_le insert_nth_comp(2)[OF hyps(9),of x U A] 
      by metis

    have ge_y:"\<not> n \<le> y \<Longrightarrow> insert_nth y B (insert_nth n U \<Gamma>) = insert_nth (Suc n) U (insert_nth y B \<Gamma>)" 
      using not_le insert_nth_comp(2)[OF hyps(9),of y U B] 
      by metis

    have B1:"n \<le> x \<Longrightarrow> n \<le> y \<Longrightarrow> insert_nth (x-Suc 0) A \<Gamma> \<turnstile> \<lparr>shift_L (-1) n t1|;|\<sigma>1,f\<rparr> |:| C \<and>
                                  insert_nth (y-Suc 0) B \<Gamma> \<turnstile> \<lparr>shift_L (-1) n t2|;|\<sigma>1,f\<rparr> |:| C"
      using  hyps(6)[OF le_x] hyps(9) FV_t hyps(8)[OF le_y] 
      by force           

    have B2: " n \<le> x \<Longrightarrow> \<not> n \<le> y \<Longrightarrow> insert_nth (x-Suc 0) A \<Gamma> \<turnstile> \<lparr>shift_L (-1) n t1|;|\<sigma>1,f\<rparr> |:| C \<and> 
                                      insert_nth y B \<Gamma> \<turnstile> \<lparr>shift_L (-1) (Suc n) t2|;|\<sigma>1,f\<rparr> |:| C"
      using  hyps(6)[OF le_x] hyps(8)[OF ge_y] hyps(9) FV_t hyps
             
      sorry

    have B3: "\<not> n \<le> x \<Longrightarrow>  n \<le> y \<Longrightarrow> insert_nth x A \<Gamma> \<turnstile> \<lparr>shift_L (-1) (Suc n) t1|;|\<sigma>1,f\<rparr> |:| C \<and>
                                      insert_nth (y-Suc 0) B \<Gamma> \<turnstile> \<lparr>shift_L (-1) n t2|;|\<sigma>1,f\<rparr> |:| C"
      using hyps(6)[OF ge_x] hyps(8)[OF le_y] hyps(9) FV_t
      sorry

    have B4: "\<not> n \<le> x \<Longrightarrow> \<not> n \<le> y \<Longrightarrow> insert_nth x A \<Gamma> \<turnstile> \<lparr>shift_L (-1) (Suc n) t1|;|\<sigma>1,f\<rparr> |:| C \<and>
                                      insert_nth y B \<Gamma> \<turnstile> \<lparr>shift_L (-1) (Suc n) t2|;|\<sigma>1,f\<rparr> |:| C"
       using hyps(6)[OF ge_x] hyps(8)[OF ge_y] hyps(9) FV_t hyps
       sorry

    show ?case
      using Sum_type hyps(1,2,9)
            has_type_L.intros(22) B1 B2 B3 B4
      by force
next
  case (has_type_CaseV L I TL LT t \<sigma> f A)   
    have branches_wtyped:"\<forall>i<length L.
       insert_nth (map (\<lambda>x. if n \<le> x then nat (int x + - 1) else x) I ! i) (TL ! i) \<Gamma>
       \<turnstile> \<lparr>(indexed_map 0 (\<lambda>k. shift_L (- 1) (if I ! k < n then Suc n else n)) LT ! i)|;|\<sigma>,f\<rparr> |:| A"
      proof (rule+)
        fix i
        assume H:"i<length L"
        have P:"\<And>k \<Gamma>' U'. insert_nth (I ! i) (TL ! i) (insert_nth n U \<Gamma>) = insert_nth k U' \<Gamma>' \<Longrightarrow> 
                        k\<le>length \<Gamma>' \<Longrightarrow> (\<forall>x. x \<in> FV (LT ! i) \<longrightarrow> x \<noteq> k) \<Longrightarrow>
                        \<Gamma>' \<turnstile> \<lparr>shift_L (-1) k (LT ! i)|;|\<sigma>,f\<rparr>|:| A"
          using has_type_CaseV(7) H 
          by blast

        have 1:"n\<le> I!i \<Longrightarrow> insert_nth (map (\<lambda>x. if n \<le> x then nat (int x + -1) else x) I ! i) (TL ! i) \<Gamma>
                \<turnstile> \<lparr>((indexed_map 0 (\<lambda>k. shift_L (-1) (if (I!k)<n then Suc n else n)) LT) ! i)|;|\<sigma>,f\<rparr> |:| A"
          using has_type_CaseV(1,2,8) H        
          proof -
            
            assume hyps:"n \<le> I ! i" "L \<noteq> \<emptyset>" "length I = length L" "n \<le> length \<Gamma>" "i < length L"
            have simp_ind:"indexed_map 0 (\<lambda>k. shift_L (-1) (if I ! k < n then Suc n else n)) LT ! i =
                  (shift_L (-1) n (LT ! i))"
              using hyps(1,5)[unfolded has_type_CaseV(4)]
              by (simp add: index_not_index_cong[of 0 "\<lambda>k. shift_L (-1) (if I ! k < n then Suc n else n)" LT, simplified])
            
            have "insert_nth (I ! i) (TL ! i) (insert_nth n U \<Gamma>) =
                    insert_nth n U (insert_nth (I ! i - Suc 0) (TL ! i) \<Gamma>)"
             proof -
               have "n< I!i"
                 using hyps(1)  hyps(5)[unfolded hyps(3)[symmetric]]
                      has_type_CaseV(9)[of "I!i",simplified, unfolded in_set_conv_nth[of "I!i" I]]
                 by force
               then have "n\<le> I!i - Suc 0" "Suc (I!i-Suc 0) = I!i"
                 by linarith+
               thus ?thesis
                 using insert_nth_comp(1)[OF hyps(4),of "I!i-Suc 0", symmetric]
                 by presburger
             qed
            hence "insert_nth (I ! i - Suc 0) (TL ! i) \<Gamma> \<turnstile> \<lparr>shift_L (- 1) n (LT ! i)|;|\<sigma>,f\<rparr> |:| A"
              using has_type_CaseV(9)[simplified,unfolded Bex_def in_set_conv_nth[of _ LT]]
                    P[of n U "insert_nth (I ! i - Suc 0) (TL ! i) \<Gamma>"]
                    le_SucI[OF hyps(4)]
               by (metis H has_type_CaseV.hyps(4) length_insert_nth)
       
            with simp_ind show ?thesis
              by (simp add: hyps min_def del: insert_nth_take_drop)
              
          qed

        have  "\<not> n\<le> I!i \<Longrightarrow> insert_nth (map (\<lambda>x. if n \<le> x then nat (int x + -1) else x) I ! i) (TL ! i) \<Gamma>
                \<turnstile> \<lparr>((indexed_map 0 (\<lambda>k. shift_L (-1) (if (I!k)<n then Suc n else n)) LT) ! i)|;|\<sigma>,f\<rparr> |:| A"
          using has_type_CaseV(1,2,8) H        
          proof -            
            assume hyps:"\<not>n \<le> I ! i" "L \<noteq> \<emptyset>" "length I = length L" "n \<le> length \<Gamma>" "i < length L"
            
            have simp_ind:"indexed_map 0 (\<lambda>k. shift_L (-1) (if I ! k < n then Suc n else n)) LT ! i =
                  (shift_L (-1) (Suc n) (LT ! i))"
              using hyps(1,5)[unfolded has_type_CaseV(4)]
              by (simp add: index_not_index_cong[of 0 "\<lambda>k. shift_L (-1) (if I ! k < n then Suc n else n)" LT, simplified])
           
              have "\<forall>x. x \<in> FV (LT ! i) \<longrightarrow> x \<noteq> Suc n" sorry
           
              hence  "insert_nth (I ! i) (TL ! i) \<Gamma> \<turnstile> \<lparr>shift_L (-1) (Suc n) (LT ! i)|;|\<sigma>,f\<rparr> |:| A"
                using insert_nth_comp(2)[OF hyps(4), of "I!i"] hyps(4)[unfolded Suc_le_mono[of n,symmetric]]
                      P[of "Suc n"] hyps(1)[unfolded not_le]
                by fastforce

            with simp_ind show ?thesis using hyps by simp
              
          qed

       with 1 show "insert_nth (map (\<lambda>x. if n \<le> x then nat (int x + - 1) else x) I ! i) (TL ! i) \<Gamma>
       \<turnstile> \<lparr>(indexed_map 0 (\<lambda>k. shift_L (- 1) (if I ! k < n then Suc n else n)) LT ! i)|;|\<sigma>,f\<rparr> |:| A"
         by fast
      qed 
    show ?case
      using has_type_CaseV(1-4) index_not_index_cong[of 0 "\<lambda>k. shift_L (-1) (if I ! k < n then Suc n else n)" LT]
            has_type_CaseV(6)[OF _ has_type_CaseV(8), simplified]
            has_type_CaseV(9)[simplified] branches_wtyped
      by (force intro!: has_type_L.intros(24))
qed (fastforce intro: has_type_L.intros simp: nth_append min_def)+

lemma weaking_pattern:
  "\<Gamma> \<turnstile> \<lparr>t|;|\<sigma>,f\<rparr> |:| A \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t|;|(\<sigma>1++\<sigma>),f\<rparr> |:| A"
proof (induction \<Gamma> t \<sigma> f A arbitrary: \<sigma>1 rule: has_type_L.induct)
  case (has_type_ProjT i TL \<Gamma> t)
    note hyps=this
    show ?case 
      using hyps(1,2) hyps(4)[of \<sigma>1] has_type_L.intros(15)
      by force
next
  case (has_type_RCD L TL LT \<Gamma> \<sigma> f)
    note hyps=this
    show ?case 
      using hyps(1-4, 6)
      by (force intro!: has_type_L.intros(16))
next
  case (has_type_LetPattern p  B \<sigma> \<sigma>2 \<Gamma> t1 f t2 A)
    note hyps=this
    show ?case 
      apply rule
      using hyps(1,2)
      apply force+
      apply simp
      defer
      using hyps(6,7,3) map_add_comm map_add_assoc
      sorry
next
  case (has_type_Case)
    note hyps=this
    show ?case using hyps(1,2,6,7,8) by (force intro: has_type_L.intros)
next
  case (has_type_CaseV)
    note hyps=this
    show ?case using hyps(1-4,6,7) by (force intro!: has_type_L.intros)
qed (force intro: has_type_L.intros simp: nth_append min_def)+

lemma substitution:
  "\<Gamma> \<turnstile> \<lparr>t|;|\<sigma>,f\<rparr> |:| A \<Longrightarrow>  \<Gamma> \<turnstile> \<lparr>LVar n|;|\<sigma>,f\<rparr> |:| S \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>s|;|\<sigma>,f\<rparr> |:| S \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>subst_L n s t|;|\<sigma>,f\<rparr> |:| A"
proof (induction \<Gamma> t \<sigma> f A arbitrary: s n rule: has_type_L.induct)
  case (has_type_LAbs \<Gamma> T1 t \<sigma> f T2)
    note hyps=this
    show ?case 
      using weakening[where n=0, unfolded insert_nth_def nat.rec]
            inversion(4) hyps(2)[of "Suc n" "shift_L 1 0 s"]
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
    note hyps=this
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
      using hyps(4)[of n s] hyps(5)[of "Suc n"] hyps(1,6-)
            weakening[where n=x,OF _ hyps(1)]
            inversion(4)[OF hyps(6)] hyps(5)[of "Suc n" "shift_L 1 x s"] hyps(7,1)          
      by (force intro!: has_type_L.intros(4,10))
     
    have "x \<noteq> n \<Longrightarrow> \<not> x < n \<longrightarrow> \<Gamma> \<turnstile> \<lparr>Let var x := subst_L n s t1 in subst_L n (shift_L 1 x s) t2|;|\<sigma>,f\<rparr> |:| B"
      using hyps(4)[of n s] hyps(5)[of "Suc n"] hyps(1,6-)
            weakening[where n=x,OF _ hyps(1)]
            inversion(4)[OF hyps(6)] hyps(5)[of _ "shift_L 1 x s"] 
            not_less[of x n] nth_take[of n x \<Gamma>] nth_append[of "take x \<Gamma>" _ n, simplified]            
      by (force intro!: has_type_L.intros(4,10))

    with A show ?case
      using hyps(4)[of x s] hyps(1,3,6-)
      by (force intro!: has_type_L.intros(10))
      
next
  case (has_type_LetPattern p B \<sigma> \<sigma>1 \<Gamma> t1 f t2 A)
    note hyps=this
    
    show ?case
      apply simp
      apply rule
      using hyps(1,2,3)
      apply simp+
      using hyps(6)[of n s] hyps(8-)
      apply force
      using hyps(7)[of n s] hyps(8-)
      sorry
next
  case (has_type_Case x \<Gamma> y t \<sigma>1 f A B t1 C t2)
    note hyps=this
    
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

     have B1:"n = x \<Longrightarrow> n \<noteq> y \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>subst_L n s (Case t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2)|;|\<sigma>1,f\<rparr> |:| C"
       proof -
         assume H: "n = x" "n \<noteq> y"
          
         from V_shifty have A:"n = x \<Longrightarrow> x \<noteq> y \<Longrightarrow> y < x \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Case subst_L x s t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> subst_L (Suc x) (shift_L 1 y s) t2|;|\<sigma>1,f\<rparr> |:| C"
           using hyps(8)[of "Suc x" "shift_L 1 y s"] hyps(9-) hyps(1,2,4) hyps(6)[of x s] 
                 weakening[OF hyps(10) hyps(2)] has_type_L.intros(4)
           by (force intro!: has_type_L.intros(22))
    
         have "n = x \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<not> y < x \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Case subst_L x s t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> subst_L x (shift_L 1 y s) t2|;|\<sigma>1,f\<rparr> |:| C"
           using hyps(1,2,4) hyps(6)[OF hyps(9-)] hyps(8)[of x "shift_L 1 y s"]  
                 weakening[OF hyps(10) hyps(2)] Vy[OF H(2)]
           by (force intro!: has_type_L.intros(4,22))
         with A H show ?thesis by force
     qed

    have B2: "n \<noteq> x \<Longrightarrow> n = y \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>subst_L n s (Case t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2)|;|\<sigma>1,f\<rparr> |:| C"
      proof -
        assume H: "n \<noteq> x" "n = y"

        from V_shiftx have A:" n \<noteq> x \<Longrightarrow> x < n \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Case subst_L y s t of Inl x \<Rightarrow> subst_L (Suc y) (shift_L 1 x s) t1 | Inr y \<Rightarrow> t2|;|\<sigma>1,f\<rparr> |:| C"
          using hyps(6)[OF hyps(9-)] hyps(1,2,5) H  hyps(7)[of "Suc n" "shift_L 1 x s"]
                weakening[OF hyps(10) hyps(1)]
          by (force intro!: has_type_L.intros(4,22))
        have "n \<noteq> x \<Longrightarrow> \<not> x < n \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Case subst_L y s t of Inl x \<Rightarrow> subst_L y (shift_L 1 x s) t1 | Inr y \<Rightarrow> t2|;|\<sigma>1,f\<rparr> |:| C"
          using hyps(1,2,5) H hyps(6)[OF hyps(9-)] hyps(7)[of y "shift_L 1 x s"]  
                weakening[OF hyps(10) hyps(1)] Vx[OF H(1)]
          by (force intro!: has_type_L.intros(4,22))
        
        with A H show ?thesis by force
      qed
    
    have "n \<noteq> x \<Longrightarrow> n \<noteq> y \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>subst_L n s (Case t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2)|;|\<sigma>1,f\<rparr> |:| C"
      proof -
        assume H: "n \<noteq> x" "n \<noteq> y"
      
        have C1: "n \<noteq> x \<Longrightarrow> n \<noteq> y \<Longrightarrow> x < n \<Longrightarrow> y < n \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Case subst_L n s t of Inl x \<Rightarrow> subst_L (Suc n) (shift_L 1 x s) t1 | Inr y \<Rightarrow>
           subst_L (Suc n) (shift_L 1 y s) t2|;|\<sigma>1,f\<rparr> |:| C"
          using hyps(1,2) hyps(6)[OF hyps(9-)]
                hyps(7,8)[of "Suc n" "shift_L 1 _ s"] weakening[OF hyps(10)]
                has_type_L.intros(4)[OF V_shiftx]  has_type_L.intros(4)[OF V_shifty]
          by (force intro!: has_type_L.intros(22))
        have C2: "n \<noteq> x \<Longrightarrow> n \<noteq> y \<Longrightarrow> x < n \<Longrightarrow> \<not>y < n \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Case subst_L n s t of Inl x \<Rightarrow> subst_L (Suc n) (shift_L 1 x s) t1 | Inr y \<Rightarrow>
           subst_L n (shift_L 1 y s) t2|;|\<sigma>1,f\<rparr> |:| C"
          using hyps(7,8)[of _ "shift_L 1 _ s"] weakening[OF hyps(10)]  hyps(1,2) hyps(6)[OF hyps(9-)]
                has_type_L.intros(4)[OF V_shiftx]  has_type_L.intros(4)[OF V_shifty]
                has_type_L.intros(4)[OF Vx] has_type_L.intros(4)[OF Vy]
          by (force intro!: has_type_L.intros(22))
        have C3: "n \<noteq> x \<Longrightarrow> n \<noteq> y \<Longrightarrow> \<not>x < n \<Longrightarrow> y < n \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Case subst_L n s t of Inl x \<Rightarrow> subst_L n (shift_L 1 x s) t1 | Inr y \<Rightarrow>
           subst_L (Suc n) (shift_L 1 y s) t2|;|\<sigma>1,f\<rparr> |:| C"
          using hyps(7,8)[of _ "shift_L 1 _ s"] weakening[OF hyps(10)]  hyps(1,2) hyps(6)[OF hyps(9-)]
                has_type_L.intros(4)[OF V_shiftx]  has_type_L.intros(4)[OF V_shifty]
                has_type_L.intros(4)[OF Vx] has_type_L.intros(4)[OF Vy]
          by (force intro!: has_type_L.intros(22))

        have "n \<noteq> x \<Longrightarrow> n \<noteq> y \<Longrightarrow> \<not>x < n \<Longrightarrow> \<not>y < n \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Case subst_L n s t of Inl x \<Rightarrow> subst_L n (shift_L 1 x s) t1 | Inr y \<Rightarrow>
           subst_L n (shift_L 1 y s) t2|;|\<sigma>1,f\<rparr> |:| C"
          using hyps(7,8)[of _ "shift_L 1 _ s"] weakening[OF hyps(10)]  hyps(1,2) hyps(6)[OF hyps(9-)]
                has_type_L.intros(4)[OF Vx] has_type_L.intros(4)[OF Vy]
          by (force intro!: has_type_L.intros(22))

        with C1 C2 C3 H show ?thesis by simp          
      qed
    
    with B1 B2 show ?case
      using hyps(6)[of x s] hyps(9-) hyps(1,2,4,5) 
      by (cases "n=x"; cases "n=y") (force intro: has_type_L.intros(22))
    
next
  case (has_type_CaseV)
    note hyps=this
    show ?case sorry
next
  case (has_type_tail)
    note hyps=this
    show ?case sorry
next
  case (has_type_head)
    note hyps=this
    show ?case sorry
qed (auto intro!: has_type_L.intros dest: inversion(4))

end
