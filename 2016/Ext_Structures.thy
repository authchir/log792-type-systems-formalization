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
    "is_value_L v1 \<Longrightarrow> eval1_L (Let var x := v1 in t2) (subst_L x (shift_L 1 x v1) t2)" |
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
    "is_value_L v \<Longrightarrow> eval1_L (Case (inl v as A) of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2) (subst_L x (shift_L 1 x v) t1)" |
  eval1_L_CaseInr:
    "is_value_L v \<Longrightarrow> eval1_L (Case (inr v as A) of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2) (subst_L y (shift_L 1 y v) t2)" |
  eval1_L_CaseS:
    "eval1_L t t' \<Longrightarrow> eval1_L (Case t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2) (Case t' of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2)" |
  eval1_L_Inl:
    "eval1_L t t' \<Longrightarrow> eval1_L (inl t as A) (inl t' as A)" |
  eval1_L_Inr:
    "eval1_L t t' \<Longrightarrow> eval1_L (inr t as A) (inr t' as A)" |
  eval1_L_CaseVar:
    "index L l = i \<Longrightarrow> eval1_L (Case (<l:=v> as A) of <L:=I> \<Rightarrow> LT) (subst_L (I!i) (shift_L 1 (I!i) v) (LT!i))" |
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
                                                  \<Gamma> \<turnstile> \<lparr>t2|;|(\<sigma> ++  \<sigma>1), f\<rparr> |:| R" 
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
  show "\<exists>\<sigma> B. coherent p B \<and> Lmatch_Type p \<sigma>  \<and>  \<Gamma> \<turnstile> \<lparr>t1|;|\<sigma>1,f\<rparr> |:| B \<and>  \<Gamma> \<turnstile> \<lparr>t2|;|(\<sigma> ++ \<sigma>1),f\<rparr> |:| R"
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
              by (simp add: index_not_index_cong[of 0 "\<lambda>k. shift_L 1 (if I ! k < n then Suc n else n)" LT, simplified])
            
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
      next
        fix i
        assume H:"i<length L"
        show " map (\<lambda>x. if n \<le> x then nat (int x + 1) else x) I ! i
         \<le> length (insert_nth n S \<Gamma>)"
         using has_type_CaseV(3,8) H nth_map[of i I "\<lambda>x. if n \<le> x then nat (int x + 1) else x"]
         by force
      qed 

    show ?case
      using has_type_CaseV(1-5) index_not_index_cong[of 0 "\<lambda>k. shift_L 1 (if I ! k < n then Suc n else n)" LT]
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
      using eval1_L.intros(32,33) hyps(7) canonical_forms(7)[OF _ hyps(6)]
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
       \<turnstile> \<lparr>(indexed_map 0 (\<lambda>k. shift_L (- 1) (if I ! k < n then Suc n else n)) LT ! i)|;|\<sigma>,f\<rparr> |:| A \<and> map (\<lambda>x. if n \<le> x then nat (int x + - 1) else x) I ! i \<le> length \<Gamma>"
      proof (rule+)
        fix i
        assume H:"i<length L"
        have P:"\<And>k \<Gamma>' U'. insert_nth (I ! i) (TL ! i) (insert_nth n U \<Gamma>) = insert_nth k U' \<Gamma>' \<Longrightarrow> 
                        k\<le>length \<Gamma>' \<Longrightarrow> (\<forall>x. x \<in> FV (LT ! i) \<longrightarrow> x \<noteq> k) \<Longrightarrow>
                        \<Gamma>' \<turnstile> \<lparr>shift_L (-1) k (LT ! i)|;|\<sigma>,f\<rparr>|:| A"
          using has_type_CaseV(8) H 
          by blast

        have 1:"n\<le> I!i \<Longrightarrow> insert_nth (map (\<lambda>x. if n \<le> x then nat (int x + -1) else x) I ! i) (TL ! i) \<Gamma>
                \<turnstile> \<lparr>((indexed_map 0 (\<lambda>k. shift_L (-1) (if (I!k)<n then Suc n else n)) LT) ! i)|;|\<sigma>,f\<rparr> |:| A"
          using has_type_CaseV(1,3,9) H        
          proof -
            
            assume hyps:"n \<le> I ! i" "L \<noteq> \<emptyset>" "length I = length L" "n \<le> length \<Gamma>" "i < length L"
            have simp_ind:"indexed_map 0 (\<lambda>k. shift_L (-1) (if I ! k < n then Suc n else n)) LT ! i =
                  (shift_L (-1) n (LT ! i))"
              using hyps(1,5)[unfolded has_type_CaseV(5)]
              by (simp add: index_not_index_cong[of 0 "\<lambda>k. shift_L (-1) (if I ! k < n then Suc n else n)" LT, simplified])
            
            have "insert_nth (I ! i) (TL ! i) (insert_nth n U \<Gamma>) =
                    insert_nth n U (insert_nth (I ! i - Suc 0) (TL ! i) \<Gamma>)"
             proof -
               have "n< I!i"
                 using hyps(1)  hyps(5)[unfolded hyps(3)[symmetric]]
                      has_type_CaseV(10)[of "I!i",simplified, unfolded in_set_conv_nth[of "I!i" I]]
                 by force
               then have "n\<le> I!i - Suc 0" "Suc (I!i-Suc 0) = I!i"
                 by linarith+
               thus ?thesis
                 using insert_nth_comp(1)[OF hyps(4),of "I!i-Suc 0", symmetric]
                 by presburger
             qed
            hence "insert_nth (I ! i - Suc 0) (TL ! i) \<Gamma> \<turnstile> \<lparr>shift_L (- 1) n (LT ! i)|;|\<sigma>,f\<rparr> |:| A"
              using has_type_CaseV(10)[simplified,unfolded Bex_def in_set_conv_nth[of _ LT]]
                    P[of n U "insert_nth (I ! i - Suc 0) (TL ! i) \<Gamma>"]
                    le_SucI[OF hyps(4)]
               by (metis H has_type_CaseV.hyps(5) length_insert_nth)
       
            with simp_ind show ?thesis
              by (simp add: hyps min_def del: insert_nth_take_drop)
              
          qed

        have  "\<not> n\<le> I!i \<Longrightarrow> insert_nth (map (\<lambda>x. if n \<le> x then nat (int x + -1) else x) I ! i) (TL ! i) \<Gamma>
                \<turnstile> \<lparr>((indexed_map 0 (\<lambda>k. shift_L (-1) (if (I!k)<n then Suc n else n)) LT) ! i)|;|\<sigma>,f\<rparr> |:| A"
          using has_type_CaseV(1,3,9) H        
          proof -            
            assume hyps:"\<not>n \<le> I ! i" "L \<noteq> \<emptyset>" "length I = length L" "n \<le> length \<Gamma>" "i < length L"
            
            have simp_ind:"indexed_map 0 (\<lambda>k. shift_L (-1) (if I ! k < n then Suc n else n)) LT ! i =
                  (shift_L (-1) (Suc n) (LT ! i))"
              using hyps(1,5)[unfolded has_type_CaseV(5)]
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
      next
        fix i
        assume H:"i<length L"
        show "map (\<lambda>x. if n \<le> x then nat (int x + - 1) else x) I ! i \<le> length \<Gamma>"
          using has_type_CaseV(3,8,9) H nth_map[of i I "\<lambda>x. if n \<le> x then nat (int x + - 1) else x"]
          by (cases "n\<le>I!i") (force, presburger)
      qed 
    show ?case
      using has_type_CaseV(1-5) index_not_index_cong[of 0 "\<lambda>k. shift_L (-1) (if I ! k < n then Suc n else n)" LT]
            has_type_CaseV(7)[OF _ has_type_CaseV(9), simplified]
            has_type_CaseV(10)[simplified] branches_wtyped
      by (force intro!: has_type_L.intros(24))
qed (fastforce intro: has_type_L.intros simp: nth_append min_def)+

abbreviation incl_map::"pcontext \<Rightarrow> pcontext\<Rightarrow> bool" (infix "\<subseteq>\<^sub>f" 75) where
"\<sigma> \<subseteq>\<^sub>f \<sigma>1 \<equiv> (\<forall>x\<in>dom \<sigma>. \<sigma> x = \<sigma>1 x)"

lemma weaking_pattern:
  "\<Gamma> \<turnstile> \<lparr>t|;|\<sigma>,f\<rparr> |:| A \<Longrightarrow> \<sigma> \<subseteq>\<^sub>f \<sigma>1 \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t|;|\<sigma>1,f\<rparr> |:| A"
proof (induction \<Gamma> t \<sigma> f A arbitrary: \<sigma>1 rule: has_type_L.induct)
  case (has_type_ProjT i TL \<Gamma> t \<sigma> f)
    note hyps=this
    show ?case 
      using hyps(1,2) hyps(4)[of \<sigma>1] has_type_L.intros(15) hyps(5)
      by force
next
  case (has_type_RCD L TL LT \<Gamma> \<sigma> f)
    note hyps=this
    show ?case 
      using hyps(1-4, 6,7)
      by (force intro!: has_type_L.intros(16))
next
  case (has_type_LetPattern p  B \<sigma> \<Gamma> t1 \<sigma>2 f t2 A)
    note hyps=this
    have "\<sigma> ++ \<sigma>2 \<subseteq>\<^sub>f \<sigma> ++ \<sigma>1"
      apply simp
      apply rule
      using hyps(7)
      apply (cases "dom \<sigma>1 \<inter> dom \<sigma> = {}")
      apply (metis IntI Un_iff empty_iff has_type_LetPattern.prems map_add_def map_add_dom_app_simps(3))
      
          
      
      sorry
    then show ?case 
      using hyps(1,2) hyps(5)[OF hyps(7)] hyps(6)[of "\<sigma>++\<sigma>1"]
      by (force intro: has_type_L.intros)
next
  case (has_type_Case)
    note hyps=this
    show ?case using hyps(1,2,6-) by (force intro: has_type_L.intros)
next
  case (has_type_CaseV)
    note hyps=this
    show ?case using hyps(1-5,7-) by (force intro!: has_type_L.intros)
qed (force intro: has_type_L.intros simp: nth_append min_def)+

abbreviation af::"lterm \<Rightarrow> bool \<Rightarrow> bool" where
"af t f \<equiv> (case t of Lhead _ _ \<Rightarrow> f=True|Ltail _ _\<Rightarrow> f=True|_\<Rightarrow>True)"

inductive agrees_flag::"lterm \<Rightarrow> bool \<Rightarrow> bool" where
 A_Unary: "subterms t = Unary t1 \<Longrightarrow> af t f \<Longrightarrow> agrees_flag t1 f \<Longrightarrow> agrees_flag t f"|
 A_Binary: "subterms t = Bi t1 t2 \<Longrightarrow> agrees_flag t1 f \<Longrightarrow> agrees_flag t2 f \<Longrightarrow> agrees_flag t f"|
 A_Ternary: "subterms t = Ter t1 t2 t3\<Longrightarrow> agrees_flag t1 f \<Longrightarrow> agrees_flag t2 f \<Longrightarrow> 
              agrees_flag t3 f  \<Longrightarrow> agrees_flag t f"|
 A_Comp: "subterms t = Comp t1 L\<Longrightarrow> agrees_flag t1 f \<Longrightarrow> (\<forall>i<length L. agrees_flag (L!i) f) \<Longrightarrow>
            agrees_flag t f"|
 A_List: "subterms t = UList L\<Longrightarrow> (\<forall>i<length L. agrees_flag (L!i) f) \<Longrightarrow>
            agrees_flag t f"|
 A_Void: "subterms t = Void \<Longrightarrow> agrees_flag t f"

lemma welltyped_agreesf:
  "\<Gamma> \<turnstile> \<lparr>t|;|\<sigma>,f\<rparr> |:| A \<Longrightarrow> agrees_flag t f"
sorry

method inv_agrees_f= (match premises in H:"agrees_flag t f" for t and f\<Rightarrow>
                      \<open>insert "agrees_flag.simps"[of t f, simplified]\<close>)

lemma substitution:
  "\<Gamma> \<turnstile> \<lparr>t|;|\<sigma>,f\<rparr> |:| A \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>LVar n|;|\<sigma>1,f\<rparr> |:| S \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>s|;|\<sigma>1,f\<rparr> |:| S \<Longrightarrow>agrees_flag t f\<Longrightarrow> \<sigma>1 \<subseteq>\<^sub>f \<sigma>\<Longrightarrow> \<Gamma> \<turnstile> \<lparr>subst_L n s t|;|\<sigma>,f\<rparr> |:| A"
proof (induction \<Gamma> t \<sigma> f A arbitrary: s n \<sigma>1 rule: has_type_L.induct; inv_agrees_f)
  case (has_type_LAbs \<Gamma> T1 t \<sigma> f T2)
    note hyps=this
    show ?case 
      using weakening[where n=0, unfolded insert_nth_def nat.rec]
            inversion(4) hyps(2)[of "Suc n" \<sigma>1 "shift_L 1 0 s"] hyps(6)
            hyps(3,4) hyps(5)[unfolded "agrees_flag.simps"[of "LAbs _ _", simplified]]
      by (fastforce intro!: has_type_L.intros)
next
  case (has_type_ProjT i TL \<Gamma> t \<sigma> f)
    note hyps=this
    show ?case
      using has_type_L.intros(15)[OF hyps(1,2)] hyps(4-) 
      by (simp, inv_agrees_f, force)
next
  case (has_type_Let x \<Gamma> t1 \<sigma> f A t2 B)
    note hyps=this and ag = this(8)[unfolded "agrees_flag.simps"[of "Let var _:= _ in _",simplified]]
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
      using hyps(4)[of n \<sigma>1  s,OF _ _ _ hyps(9)] hyps(5)[of "Suc n",OF _ _ _ hyps(9)] hyps(1,6,7) ag
            weakening[where n=x,OF _ hyps(1)]
            inversion(4)[OF hyps(6)] hyps(5)[of "Suc n" \<sigma>1 "shift_L 1 x s",OF _ _ _ hyps(9)]           
      by (force intro!: has_type_L.intros(4,10))
     
    have "x \<noteq> n \<Longrightarrow> \<not> x < n \<longrightarrow> \<Gamma> \<turnstile> \<lparr>Let var x := subst_L n s t1 in subst_L n (shift_L 1 x s) t2|;|\<sigma>,f\<rparr> |:| B"
      using hyps(4)[of n _ s,OF _ _ _ hyps(9)] hyps(5)[of "Suc n",OF _ _ _ hyps(9)] hyps(1,6-8) ag
            weakening[where n=x,OF _ hyps(1)]
            inversion(4)[OF hyps(6)] hyps(5)[of _ _ "shift_L 1 x s",OF _ _ _ hyps(9)] 
            not_less[of x n] nth_take[of n x \<Gamma>] nth_append[of "take x \<Gamma>" _ n, simplified]            
      by (force intro!: has_type_L.intros(4,10))

    with A show ?case
      using hyps(4)[of x \<sigma>1 s] hyps(1,3,6-) ag
      by (force intro!: has_type_L.intros(10))
      
next
  case (has_type_LetPattern p B \<sigma> \<Gamma> t1 \<sigma>2 f t2 A)
    note hyps=this and ag = this(9)[unfolded "agrees_flag.simps"[of "Let pattern p := t1 in t2",simplified]]
    have A:"\<sigma>1 \<subseteq>\<^sub>f \<sigma> ++ \<sigma>2"
      using hyps(10)
      by force
    show ?case
      using hyps(5)[of n \<sigma>1 s] hyps(1,2,7-) ag hyps(6)[of n \<sigma>1 s,OF _ _ _ A]
      by (force intro!: has_type_L.intros)
next
  case (has_type_Case x \<Gamma> y t \<sigma>2 f A B t1 C t2)
    note hyps=this and ag= this(11)[unfolded "agrees_flag.simps"[of "Case t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2",simplified]]
    
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
           using hyps(8)[of "Suc x" \<sigma>1 "shift_L 1 y s"] hyps(9-) hyps(1,2,4) hyps(6)[of x \<sigma>1 s] ag
                 weakening[OF hyps(10) hyps(2)] has_type_L.intros(4)
           by (force intro!: has_type_L.intros(22))
    
         have "n = x \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<not> y < x \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Case subst_L x s t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> subst_L x (shift_L 1 y s) t2|;|\<sigma>2,f\<rparr> |:| C"
           using hyps(1,2,4,12) hyps(6)[OF hyps(9,10)] hyps(8)[of x \<sigma>1 "shift_L 1 y s"] ag 
                 weakening[OF hyps(10) hyps(2)] Vy[OF H(2)]
           by (force intro!: has_type_L.intros(4,22))
         with A H show ?thesis by force
     qed

    have B2: "n \<noteq> x \<Longrightarrow> n = y \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>subst_L n s (Case t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2)|;|\<sigma>2,f\<rparr> |:| C"
      proof -
        assume H: "n \<noteq> x" "n = y"

        from V_shiftx have A:" n \<noteq> x \<Longrightarrow> x < n \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Case subst_L y s t of Inl x \<Rightarrow> subst_L (Suc y) (shift_L 1 x s) t1 | Inr y \<Rightarrow> t2|;|\<sigma>2,f\<rparr> |:| C"
          using hyps(6)[OF hyps(9,10)] hyps(1,2,5,12) H  hyps(7)[of "Suc n" \<sigma>1 "shift_L 1 x s"] ag
                weakening[OF hyps(10) hyps(1)]
          by (force intro!: has_type_L.intros(4,22))
        have "n \<noteq> x \<Longrightarrow> \<not> x < n \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Case subst_L y s t of Inl x \<Rightarrow> subst_L y (shift_L 1 x s) t1 | Inr y \<Rightarrow> t2|;|\<sigma>2,f\<rparr> |:| C"
          using hyps(1,2,5,12) H hyps(6)[OF hyps(9,10)] hyps(7)[of y \<sigma>1 "shift_L 1 x s"] ag 
                weakening[OF hyps(10) hyps(1)] Vx[OF H(1)]
          by (force intro!: has_type_L.intros(4,22))
        
        with A H show ?thesis by force
      qed
    
    have "n \<noteq> x \<Longrightarrow> n \<noteq> y \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>subst_L n s (Case t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2)|;|\<sigma>2,f\<rparr> |:| C"
      proof -
        assume H: "n \<noteq> x" "n \<noteq> y"
      
        have C1: "n \<noteq> x \<Longrightarrow> n \<noteq> y \<Longrightarrow> x < n \<Longrightarrow> y < n \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Case subst_L n s t of Inl x \<Rightarrow> subst_L (Suc n) (shift_L 1 x s) t1 | Inr y \<Rightarrow>
           subst_L (Suc n) (shift_L 1 y s) t2|;|\<sigma>2,f\<rparr> |:| C"
          using hyps(1,2,12) hyps(6)[OF hyps(9,10)] ag
                hyps(7,8)[of "Suc n" \<sigma>1 "shift_L 1 _ s"] weakening[OF hyps(10)]
                has_type_L.intros(4)[OF V_shiftx]  has_type_L.intros(4)[OF V_shifty]
          by (force intro!: has_type_L.intros(22))
        have C2: "n \<noteq> x \<Longrightarrow> n \<noteq> y \<Longrightarrow> x < n \<Longrightarrow> \<not>y < n \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Case subst_L n s t of Inl x \<Rightarrow> subst_L (Suc n) (shift_L 1 x s) t1 | Inr y \<Rightarrow>
           subst_L n (shift_L 1 y s) t2|;|\<sigma>2,f\<rparr> |:| C"
          using hyps(7,8)[of _ \<sigma>1 "shift_L 1 _ s"] weakening[OF hyps(10)]  hyps(1,2,12) hyps(6)[OF hyps(9,10)]
                has_type_L.intros(4)[OF V_shiftx]  has_type_L.intros(4)[OF V_shifty] ag
                has_type_L.intros(4)[OF Vx] has_type_L.intros(4)[OF Vy]
          by (force intro!: has_type_L.intros(22))
        have C3: "n \<noteq> x \<Longrightarrow> n \<noteq> y \<Longrightarrow> \<not>x < n \<Longrightarrow> y < n \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Case subst_L n s t of Inl x \<Rightarrow> subst_L n (shift_L 1 x s) t1 | Inr y \<Rightarrow>
           subst_L (Suc n) (shift_L 1 y s) t2|;|\<sigma>2,f\<rparr> |:| C"
          using hyps(7,8)[of _ \<sigma>1 "shift_L 1 _ s"] weakening[OF hyps(10)]  hyps(1,2,12) hyps(6)[OF hyps(9,10)] ag
                has_type_L.intros(4)[OF V_shiftx]  has_type_L.intros(4)[OF V_shifty]
                has_type_L.intros(4)[OF Vx] has_type_L.intros(4)[OF Vy]
          by (force intro!: has_type_L.intros(22))

        have "n \<noteq> x \<Longrightarrow> n \<noteq> y \<Longrightarrow> \<not>x < n \<Longrightarrow> \<not>y < n \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Case subst_L n s t of Inl x \<Rightarrow> subst_L n (shift_L 1 x s) t1 | Inr y \<Rightarrow>
           subst_L n (shift_L 1 y s) t2|;|\<sigma>2,f\<rparr> |:| C"
          using hyps(7,8)[of _ \<sigma>1 "shift_L 1 _ s"] weakening[OF hyps(10)] ag hyps(1,2,12) hyps(6)[OF hyps(9,10)]
                has_type_L.intros(4)[OF Vx] has_type_L.intros(4)[OF Vy]
          by (force intro!: has_type_L.intros(22))

        with C1 C2 C3 H show ?thesis by simp          
      qed
    
    with B1 B2 show ?case
      using hyps(6)[of x \<sigma>1 s] hyps(9-) hyps(1,2,4,5) ag
      by (cases "n=x"; cases "n=y") (force intro: has_type_L.intros(22))
    
next
  case (has_type_CaseV L I TL LT \<Gamma> t \<sigma> f A)
    note hyps=this and ag= this(11)[unfolded "agrees_flag.simps"[of "Case t of <L:=I> \<Rightarrow> LT",simplified]]
    have " \<forall>i<length L. insert_nth (I ! i) (TL ! i) \<Gamma> \<turnstile> 
          \<lparr>(map (\<lambda>p. if n = fst p then snd p else subst_L (if n>fst p then Suc n else n) (shift_L 1 (fst p) s) (snd p)) (zip I LT)!i)|;|\<sigma>,f\<rparr>|:| A"
      proof (rule+)
        fix i
        assume H1: "i<length L"
        have P:"\<And>n s \<sigma>1. insert_nth (I ! i) (TL ! i) \<Gamma> \<turnstile> \<lparr>LVar n|;|\<sigma>1,f\<rparr> |:| S \<Longrightarrow>
               insert_nth (I ! i) (TL ! i) \<Gamma> \<turnstile> \<lparr>s|;|\<sigma>1,f\<rparr> |:| S \<Longrightarrow> agrees_flag (LT ! i) f \<Longrightarrow> \<sigma>1 \<subseteq>\<^sub>f \<sigma> \<Longrightarrow>
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

            have ag_i: "agrees_flag (LT!i) f"
              using ag H1 has_type_CaseV(5)
              by force

            have "n\<le>I!i \<Longrightarrow>  insert_nth (I ! i) (TL ! i) \<Gamma> \<turnstile> \<lparr>subst_L  n (shift_L 1 (I!i) s) (LT ! i)|;|\<sigma>,f\<rparr> |:| A"
              using P(1)[of n \<sigma>1] inversion(4)[OF hyps(9)] has_type_LVar[of n S "insert_nth (I!i) (TL!i) \<Gamma>" _ ]
                    weakening[OF hyps(10), of "I!i" "TL!i"] H P(2) ag_i hyps(12)
                    nth_take[of n "I!i" \<Gamma>] nth_append[of "take (I!i) \<Gamma>" _ n, simplified]
              by force

            moreover have "\<not> n\<le>I!i \<Longrightarrow>  insert_nth (I ! i) (TL ! i) \<Gamma> \<turnstile> \<lparr>subst_L (Suc n) (shift_L 1 (I!i) s) (LT ! i)|;|\<sigma>,f\<rparr> |:| A"
              using P(1)[of "Suc n" \<sigma>1] has_type_LVar[OF V_shift] not_le[of n "I!i"] ag_i
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
    note hyps=this and ag = this(5)[unfolded "agrees_flag.simps"[of "Ltail _ _", simplified]]
    show ?case
      using hyps(2) hyps(3,4-) ag
      by (force intro!: has_type_L.intros)
next
  case (has_type_head)
    note hyps=this and ag = this(5)[unfolded "agrees_flag.simps"[of "Lhead _ _", simplified]]
    show ?case
      using hyps(2) hyps(3,4-) ag
      by (force intro!: has_type_L.intros)
next
  case (has_type_LVar x A \<Gamma> \<sigma> f)
    note hyps=this
    show ?case
      using hyps(1,2) inversion(4) weaking_pattern[OF hyps(3,5)]            
      by (force intro!:has_type_L.intros)
qed (auto intro!: has_type_L.intros dest: inversion(4))

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

lemma gr_Suc_conv: "Suc x \<le> n \<longleftrightarrow> (\<exists>m. n = Suc m \<and> x \<le> m)"
  by (cases n) auto

lemma FV_shift:
  "FV (shift_L (int d) c t) = image (\<lambda>x. if x \<ge> c then x + d else x) (FV t)"
proof (induction t arbitrary: c rule: lterm.induct)
  case (LAbs T t)
    thus ?case  by (auto simp: gr_Suc_conv image_iff) force+
next
  case (LetBinder x t1 t2)
    note hyps=this
    show ?case
      apply simp
      apply rule
      apply (simp add: hyps[of c])
      apply auto[1]
      apply (simp add: hyps(1)[of c] hyps(2)[of "Suc c"])
      
      sorry
next
  case (CaseSum t x t1 y t2)
    note hyps=this
    
    have 1:"(\<lambda>x. x + d) ` FV t1 \<inter> (\<lambda>x. x + d) ` Collect (op \<le> (Suc c)) = (\<lambda>x. x + d) ` FV t1 \<inter> (\<lambda>x. x + d) ` Collect (op \<le> c)"
      sorry
    have 2: "FV t1 \<inter> {x. \<not> Suc c \<le> x} = FV t1 \<inter> {x. \<not> c \<le> x}" sorry
    have C1: "c \<le> y \<Longrightarrow> c \<le> x \<Longrightarrow> ?case"
      using hyps[of c]
      by fastforce
    have C2: "c \<le> y \<Longrightarrow> \<not>c \<le> x \<Longrightarrow> ?case"
      apply simp      
      apply (simp add: hyps(1,3)[of c] hyps(2)[of "Suc c"] image_Int[of "\<lambda>x. x + d", simplified] 1 2)
      apply (simp add: image_Un[of "(\<lambda>x. x + d)"])
    sorry
    have C3: "c \<le> x \<Longrightarrow> \<not>c \<le> y \<Longrightarrow> ?case"
      apply simp      
      apply (simp add: hyps(1,2)[of c] hyps(3)[of "Suc c"] image_Int[of "\<lambda>x. x + d", simplified])
      apply (simp add: image_Un[of "(\<lambda>x. x + d)"])
    sorry
    have "\<not>c \<le> y \<Longrightarrow> \<not>c \<le> x \<Longrightarrow> ?case"
      apply simp      
      apply (simp add: hyps(1)[of c] hyps(2,3)[of "Suc c"] image_Int[of "\<lambda>x. x + d", simplified])
      apply (simp add: image_Un[of "(\<lambda>x. x + d)"])
    sorry
    show ?case
     sorry
next
  case (CaseVar t L I LT)
    note hyps=this
    have A:"UNION (set (indexed_map 0 (\<lambda>k. shift_L (int d) (if I ! k < c then Suc c else c)) LT)) FV =
          (\<lambda>x. x + d) ` ((\<Union>x\<in>set LT. FV x) \<inter> {x. c \<le> x}) \<union> UNION (set LT) FV \<inter> {x. \<not> c \<le> x}"
          sorry
    show ?case
      apply (simp add: hyps(1)[of c])
      apply (simp add: A)
      apply rule      
      apply force
      sorry
qed auto

lemma FV_subst:
  "FV (subst_L n t u) = (if n \<in> FV u then (FV u - {n}) \<union> FV t else FV u)"
proof (induction u arbitrary: n t rule: lterm.induct)
  case (LAbs T u)
  thus ?case 
    by (auto simp: gr0_conv_Suc image_iff FV_shift[of 1, unfolded int_1],
        (metis DiffI One_nat_def UnCI diff_Suc_1 empty_iff imageI insert_iff nat.distinct(1))+)
next
  case (Record L LT)
    note hyps=this
    have "(\<exists>x\<in>set LT. n \<in> FV x) \<longrightarrow> (\<Union>x\<in>set LT. FV (subst_L n t x)) = UNION (set LT) FV - {n} \<union> FV t"
      proof (rule)
        assume "\<exists>x\<in>set LT. n \<in> FV x"
        then obtain x where H:"x\<in>set LT" "n\<in>FV x" by blast

        note H1= hyps[OF H(1), of n t, simplified H(2) if_True]
        
        have "(\<Union>x\<in>set LT. FV (subst_L n t x)) \<subseteq> UNION (set LT) FV - {n} \<union> FV t"
          proof (rule,simp)
            fix y
            assume "\<exists>xa\<in>set LT. y \<in> FV (subst_L n t xa)"
            then obtain x1 where A:"x1\<in>set LT" "y \<in> FV (subst_L n t x1)" by blast
            note H2=A(2)[unfolded hyps[OF A(1), of n t]]
            show "(\<exists>xa\<in>set LT. y \<in> FV xa) \<and> y \<noteq> n \<or> y \<in> FV t"
                using H2 A(1)
                by (cases "n\<in>FV x1") force+
          qed
        moreover have "UNION (set LT) FV - {n} \<union> FV t \<subseteq> (\<Union>x\<in>set LT. FV (subst_L n t x))"
          using hyps[of _ n t] H1 H
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
    note hyps= this
    have "(\<exists>x\<in>set LT. n \<in> FV x) \<longrightarrow> (\<Union>x\<in>set LT. FV (subst_L n t x)) = UNION (set LT) FV - {n} \<union> FV t"
      proof (rule)
        assume "\<exists>x\<in>set LT. n \<in> FV x"
        then obtain x where H:"x\<in>set LT" "n\<in>FV x" by blast

        note H1= hyps[OF H(1), of n t, simplified H(2) if_True]
        
        have "(\<Union>x\<in>set LT. FV (subst_L n t x)) \<subseteq> UNION (set LT) FV - {n} \<union> FV t"
          proof (rule,simp)
            fix y
            assume "\<exists>xa\<in>set LT. y \<in> FV (subst_L n t xa)"
            then obtain x1 where A:"x1\<in>set LT" "y \<in> FV (subst_L n t x1)" by blast
            note H2=A(2)[unfolded hyps[OF A(1), of n t]]
            show "(\<exists>xa\<in>set LT. y \<in> FV xa) \<and> y \<noteq> n \<or> y \<in> FV t"
                using H2 A(1)
                by (cases "n\<in>FV x1") force+
          qed
        moreover have "UNION (set LT) FV - {n} \<union> FV t \<subseteq> (\<Union>x\<in>set LT. FV (subst_L n t x))"
          using hyps[of _ n t] H1 H
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
    show ?case 
     
      sorry
next
  case (CaseSum )
    thus ?case sorry
next
  case (CaseVar)
    thus ?case sorry
qed (auto simp: gr0_conv_Suc image_iff FV_shift[of 1, unfolded int_1])


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
          using substitution[of "\<Gamma>|,|T11" _ \<sigma> f T12 0 \<sigma> T11 "shift_L 1 0 tb", simplified]
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
      have "t1 = subst_L x (shift_L 1 x ta) tb \<and> is_value_L ta \<Longrightarrow> ?case"
        using substitution[OF hyps(3) has_type_LVar[OF 1] weakening[OF hyps(2,1), of A], simplified] 
               welltyped_agreesf[OF hyps(3)]
              
        
        sorry
    show ?case sorry
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
  case (has_type_RCD)
    note hyps=this
    show ?case sorry

next
  case (has_type_LetPattern)
    note hyps=this
    show ?case sorry
next
  case (has_type_Case)
    note hyps=this
    show ?case sorry
next
  case (has_type_CaseV)
    note hyps=this
    show ?case sorry
next
  case (has_type_Fix)
    note hyps=this
    show ?case sorry
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
