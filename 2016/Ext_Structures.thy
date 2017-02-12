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
    " l\<in>set L \<Longrightarrow> index L l = m \<Longrightarrow> is_value_L (Record (take m L) (take m LT)) \<Longrightarrow> 
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


inductive has_type_L :: "lcontext \<Rightarrow> lterm \<Rightarrow> pcontext \<Rightarrow> ltype \<Rightarrow> bool" ("((_)/ \<turnstile> \<lparr>(_)|;|(_)\<rparr>/ |:| (_))" [150, 150, 150, 150] 150) where
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
    "\<Gamma> \<turnstile> \<lparr>t1|;| \<sigma>\<rparr> |:| A \<Longrightarrow> (insert_nth x A \<Gamma>) \<turnstile> \<lparr> t2|;| \<sigma>\<rparr> |:| B \<Longrightarrow> 
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
     \<Gamma> \<turnstile> \<lparr>t2|;|(\<sigma> ++ \<sigma>1)\<rparr> |:| A \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Let pattern p := t1 in t2|;| \<sigma>1\<rparr> |:| A" |
  has_type_Inl:
    "\<Gamma> \<turnstile> \<lparr>t1|;| \<sigma>1\<rparr> |:| A \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>inl t1 as A|+|B |;|\<sigma>1\<rparr> |:| A|+|B" |
  has_type_Inr:
    "\<Gamma> \<turnstile> \<lparr>t1|;| \<sigma>1\<rparr> |:| B \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>inr t1 as A|+|B |;| \<sigma>1\<rparr> |:| A|+|B" |
  has_type_Case:
    "\<Gamma> \<turnstile> \<lparr> t|;| \<sigma>1 \<rparr> |:| A|+|B \<Longrightarrow> insert_nth x A \<Gamma> \<turnstile> \<lparr>t1|;| \<sigma>1\<rparr> |:| C \<Longrightarrow>
     insert_nth y B \<Gamma> \<turnstile> \<lparr>t2|;| \<sigma>1\<rparr> |:| C \<Longrightarrow> 
     \<Gamma> \<turnstile> \<lparr>Case t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2 |;| \<sigma>1\<rparr> |:| C" |
  has_type_Variant:
    "\<Gamma> \<turnstile> \<lparr> t |;| \<sigma> \<rparr> |:| (TL!i) \<Longrightarrow> 
      \<Gamma> \<turnstile> \<lparr> <(L!i):=t> as <L|,|TL> |;|\<sigma> \<rparr> |:| <L|,|TL>" |
  has_type_CaseV:
    " L\<noteq>\<emptyset> \<Longrightarrow> length I = length L \<Longrightarrow> length L = length TL \<Longrightarrow> 
      length L = length LT \<Longrightarrow>
      \<Gamma> \<turnstile> \<lparr> t |;| \<sigma> \<rparr> |:| <L|,|TL> \<Longrightarrow> 
      (\<forall>i<length L. insert_nth (I!i) (TL!i) \<Gamma> \<turnstile> \<lparr>(LT!i)|;| \<sigma>\<rparr> |:| A) \<Longrightarrow>
      \<Gamma> \<turnstile> \<lparr> Case t of <L:=I> \<Rightarrow> LT |;| \<sigma>\<rparr> |:| A" |
  has_type_Fix:
    "\<Gamma> \<turnstile> \<lparr> t |;| \<sigma>\<rparr> |:| A\<rightarrow>A \<Longrightarrow> \<Gamma> \<turnstile> \<lparr> fix t |;| \<sigma>\<rparr> |:| A"|
  has_type_Nil:
    "\<Gamma> \<turnstile> \<lparr> Lnil A |;| \<sigma>\<rparr> |:| \<lambda>List A"|
  has_type_isNil:
    "\<Gamma> \<turnstile> \<lparr> t|;| \<sigma> \<rparr> |:| \<lambda>List A \<Longrightarrow>\<Gamma> \<turnstile> \<lparr> Lisnil A t|;| \<sigma> \<rparr> |:| Bool"| 
  has_type_head:
    "\<Gamma> \<turnstile> \<lparr> t|;| \<sigma> \<rparr> |:| \<lambda>List A \<Longrightarrow>\<Gamma> \<turnstile> \<lparr> Lhead A t|;| \<sigma> \<rparr> |:| A"| 
  has_type_tail:
    "\<Gamma> \<turnstile> \<lparr> t|;| \<sigma> \<rparr> |:| \<lambda>List A \<Longrightarrow>\<Gamma> \<turnstile> \<lparr> Ltail A t|;| \<sigma> \<rparr> |:| A"| 
  has_type_cons:
    "\<Gamma> \<turnstile> \<lparr> t|;| \<sigma> \<rparr> |:| A \<Longrightarrow> \<Gamma> \<turnstile> \<lparr> t' |;| \<sigma> \<rparr> |:| A \<Longrightarrow>
      \<Gamma> \<turnstile> \<lparr> Lcons A t t'|;| \<sigma> \<rparr> |:| \<lambda>List A"  

inductive_cases has_type_LetE : "\<Gamma> \<turnstile> \<lparr> Let var x := t1 in t2|;|\<sigma>1\<rparr>  |:| B"
inductive_cases has_type_ProjTE: "\<Gamma> \<turnstile> \<lparr> \<Pi> i t|;|\<sigma>1\<rparr> |:| R"
inductive_cases has_type_ProjRE: "\<Gamma> \<turnstile> \<lparr> ProjR l t|;|\<sigma>1\<rparr> |:| R"
inductive_cases has_type_LetPE: "\<Gamma> \<turnstile> \<lparr>Let pattern p := t1 in t2|;|\<sigma>1\<rparr> |:| A"
inductive_cases has_type_CaseSE: "\<Gamma> \<turnstile> \<lparr>Case t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2|;|\<sigma>1\<rparr> |:| R"
inductive_cases has_type_CaseVE: "\<Gamma> \<turnstile> \<lparr>Case t of <L:=I> \<Rightarrow> LT|;|\<sigma>1\<rparr> |:| R"
inductive_cases has_type_LAbsE: "\<Gamma> \<turnstile> \<lparr>LAbs T1 t2|;|\<sigma>1\<rparr> |:| R"
inductive_cases has_type_VariantE: "\<Gamma> \<turnstile> \<lparr><l:=t> as R |;|\<sigma>1\<rparr> |:| R"

lemma record_patterns_characterisation:
  "set (patterns (<|RCD L PL|>)) \<subseteq> S \<Longrightarrow> x \<in> set PL \<Longrightarrow> set(patterns (<|x|>)) \<subseteq> S"
by (induction PL arbitrary: S x, auto) 

lemma inversion:
  "\<Gamma> \<turnstile> \<lparr> LTrue |;| \<sigma>\<rparr> |:| R \<Longrightarrow> R = Bool"
  "\<Gamma> \<turnstile> \<lparr> LFalse |;| \<sigma>\<rparr> |:| R \<Longrightarrow> R = Bool"
  "\<Gamma> \<turnstile> \<lparr> LIf t1 t2 t3 |;| \<sigma>\<rparr> |:| R \<Longrightarrow>  \<Gamma> \<turnstile> \<lparr>t1|;| \<sigma>\<rparr> |:| Bool \<and> \<Gamma> \<turnstile> \<lparr>t2|;| \<sigma>\<rparr> |:| R \<and> \<Gamma> \<turnstile> \<lparr>t3|;| \<sigma>\<rparr> |:| R"
  "\<Gamma> \<turnstile> \<lparr> LVar x|;| \<sigma>\<rparr> |:| R \<Longrightarrow> (x, R) |\<in>| \<Gamma>"
  "\<Gamma> \<turnstile> \<lparr> LAbs T1 t2 |;| \<sigma>\<rparr> |:| R \<Longrightarrow> \<exists>R2. R = T1 \<rightarrow> R2 \<and>  \<Gamma> |,| T1 \<turnstile> \<lparr>t2|;| \<sigma>\<rparr> |:| R2 "
  "\<Gamma> \<turnstile> \<lparr> LApp t1 t2 |;| \<sigma>\<rparr> |:| R \<Longrightarrow> \<exists>T11. \<Gamma> \<turnstile> \<lparr>t1|;| \<sigma>\<rparr> |:| T11 \<rightarrow> R \<and> \<Gamma> \<turnstile> \<lparr>t2|;| \<sigma>\<rparr> |:| T11"
  "\<Gamma> \<turnstile> \<lparr> unit|;| \<sigma>\<rparr> |:| R \<Longrightarrow> R = Unit"
  "\<Gamma> \<turnstile> \<lparr> Seq t1 t2 |;| \<sigma>\<rparr> |:| R \<Longrightarrow> \<exists>A. R = A \<and> \<Gamma> \<turnstile> \<lparr>t2|;| \<sigma>\<rparr> |:| A \<and> \<Gamma> \<turnstile> \<lparr>t1|;| \<sigma>\<rparr> |:| Unit"
  "\<Gamma> \<turnstile> \<lparr> t as A |;| \<sigma>\<rparr> |:| R \<Longrightarrow> R = A"
  "\<Gamma> \<turnstile> \<lparr> Let var x := t in t1 |;| \<sigma>\<rparr> |:| R \<Longrightarrow> \<exists>A B. R = B \<and> \<Gamma> \<turnstile> \<lparr> t|;| \<sigma>\<rparr> |:| A \<and> (insert_nth x A \<Gamma>) \<turnstile> \<lparr>t1|;| \<sigma>\<rparr> |:| B"
  "\<Gamma> \<turnstile> \<lparr> \<lbrace>t1,t2\<rbrace>|;| \<sigma>\<rparr> |:| R \<Longrightarrow> \<exists>A B. \<Gamma> \<turnstile> \<lparr> t1|;| \<sigma>\<rparr> |:| A \<and> \<Gamma> \<turnstile> \<lparr> t2|;| \<sigma>\<rparr> |:| B \<and> R = A |\<times>| B"
  "\<Gamma> \<turnstile> \<lparr> \<pi>1 t|;| \<sigma>\<rparr> |:| R \<Longrightarrow> \<exists>A B. \<Gamma> \<turnstile> \<lparr> t|;| \<sigma>\<rparr> |:| A |\<times>| B \<and> R = A"
  "\<Gamma> \<turnstile> \<lparr> \<pi>2 t|;| \<sigma>\<rparr> |:| R \<Longrightarrow> \<exists>A B. \<Gamma> \<turnstile> \<lparr> t|;| \<sigma>\<rparr> |:| A |\<times>| B \<and> R = B"
  "\<Gamma> \<turnstile> \<lparr> Tuple L|;| \<sigma>\<rparr> |:| R \<Longrightarrow> \<exists>TL. length L = length TL \<and> (\<forall>i. 0\<le>i \<longrightarrow> i< length L \<longrightarrow> \<Gamma> \<turnstile> \<lparr>(L ! i)|;| \<sigma>\<rparr> |:| (TL ! i)) \<and> R = \<lparr>TL\<rparr>"
  "\<Gamma> \<turnstile> \<lparr> (\<Pi> i t)|;| \<sigma>\<rparr> |:| R \<Longrightarrow> \<exists>TL. R = (TL ! (i-1)) \<and> \<Gamma> \<turnstile> \<lparr>t|;| \<sigma>\<rparr> |:| \<lparr>TL\<rparr> \<and> 1\<le>i \<and> i\<le> length TL"
  "\<Gamma> \<turnstile> \<lparr> (Record L1 LT)|;| \<sigma>\<rparr> |:| R \<Longrightarrow> \<exists>TL. R = \<lparr>L1|:|TL\<rparr> \<and> length TL = length LT \<and> length L1 = length LT \<and> distinct L1 \<and> 
                                    (\<forall>i. 0\<le>i \<longrightarrow> i< length LT \<longrightarrow> \<Gamma> \<turnstile> \<lparr> (LT ! i)|;| \<sigma>\<rparr> |:| (TL ! i)) " 
  "\<Gamma> \<turnstile> \<lparr> (ProjR l t)|;| \<sigma>\<rparr> |:| R \<Longrightarrow>\<exists>m L TL. \<Gamma> \<turnstile> \<lparr>t |;| \<sigma>\<rparr> |:| \<lparr>L|:|TL\<rparr> \<and> index L l = m \<and> TL ! m = R \<and> distinct L \<and> length L = length TL
                              \<and> l \<in> set L"
  "\<Gamma> \<turnstile> \<lparr><|V k as A|>|;|\<sigma>\<rparr> |:| R \<Longrightarrow> \<sigma> k = Some A"
  "\<Gamma> \<turnstile> \<lparr>Let pattern p := t1 in t2|;|\<sigma>1\<rparr> |:| R \<Longrightarrow>\<exists>\<sigma> B. coherent p B\<and> Lmatch_Type p \<sigma>  \<and> \<Gamma> \<turnstile> \<lparr>t1|;|\<sigma>1\<rparr> |:| B \<and>
                                                  \<Gamma> \<turnstile> \<lparr>t2|;|(\<sigma> ++  \<sigma>1)\<rparr> |:| R" 
  "\<Gamma> \<turnstile> \<lparr>inl t as R|;|\<sigma>1\<rparr> |:| R \<Longrightarrow>\<exists>A B. R = A|+|B \<and> \<Gamma> \<turnstile> \<lparr>t|;|\<sigma>1\<rparr> |:| A"
  "\<Gamma> \<turnstile> \<lparr>inr t as R|;|\<sigma>1\<rparr> |:| R \<Longrightarrow>\<exists>A B. R = A|+|B \<and> \<Gamma> \<turnstile> \<lparr>t|;|\<sigma>1\<rparr> |:| B"
  "\<Gamma> \<turnstile> \<lparr>Case t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2|;|\<sigma>1\<rparr> |:| R \<Longrightarrow>\<exists>A B C. R = C \<and> \<Gamma> \<turnstile> \<lparr>t|;|\<sigma>1\<rparr> |:| A|+|B \<and>
                                                          insert_nth x A \<Gamma> \<turnstile> \<lparr>t1|;|\<sigma>1\<rparr> |:| C \<and> insert_nth y B \<Gamma> \<turnstile> \<lparr>t2|;|\<sigma>1\<rparr> |:| C"
   "\<Gamma> \<turnstile> \<lparr> <l:=t> as R |;| \<sigma>1 \<rparr> |:| R \<Longrightarrow>\<exists>L TL i. R=<L|,|TL> \<and> \<Gamma> \<turnstile> \<lparr> t |;| \<sigma>1 \<rparr> |:| (TL!i) \<and> l = L!i " 
    " \<Gamma> \<turnstile> \<lparr> Case t of <L1:=I> \<Rightarrow> LT |;| \<sigma>1\<rparr> |:| A \<Longrightarrow>\<exists>TL. L1\<noteq>\<emptyset> \<and> length I = length L1 \<and> length L1 = length TL \<and> length L1 = length LT \<and>
      \<Gamma> \<turnstile> \<lparr> t |;| \<sigma>1 \<rparr> |:| <L1|,|TL> \<and> (\<forall>i<length L1. insert_nth (I!i) (TL!i) \<Gamma> \<turnstile> \<lparr>(LT!i)|;| \<sigma>1\<rparr> |:| A)"
proof -
  assume H:"\<Gamma> \<turnstile> \<lparr> Let var x := t in t1|;|\<sigma>\<rparr> |:| R"
  show " \<exists>A B. R = B \<and> \<Gamma> \<turnstile> \<lparr> t|;| \<sigma>\<rparr> |:| A \<and> (insert_nth x A \<Gamma>) \<turnstile> \<lparr>t1|;| \<sigma>\<rparr> |:| B"
    using has_type_LetE[OF H] 
    by fastforce 
next
  assume H1: "\<Gamma> \<turnstile> \<lparr>Let pattern p := t1 in t2|;|\<sigma>1\<rparr> |:| R"
  show "\<exists>\<sigma> B. coherent p B \<and> Lmatch_Type p \<sigma>  \<and> \<Gamma> \<turnstile> \<lparr>t1|;|\<sigma>1\<rparr> |:| B \<and> \<Gamma> \<turnstile> \<lparr>t2|;|(\<sigma> ++ \<sigma>1)\<rparr> |:| R"
    using has_type_LetPE[OF H1]
    by metis
next
  assume H2: "\<Gamma> \<turnstile> \<lparr>Case t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2|;|\<sigma>1\<rparr> |:| R"
  show "\<exists>A B C. R = C \<and> \<Gamma> \<turnstile> \<lparr>t|;|\<sigma>1\<rparr> |:| A |+| B \<and> insert_nth x A \<Gamma> \<turnstile> \<lparr>t1|;|\<sigma>1\<rparr> |:| C \<and> insert_nth y B \<Gamma> \<turnstile> \<lparr>t2|;|\<sigma>1\<rparr> |:| C"
    using has_type_CaseSE[OF H2]
    by fastforce
next
  assume H4: "\<Gamma> \<turnstile> \<lparr><l:=t> as R|;|\<sigma>1\<rparr> |:| R"
  show  "\<exists>L TL i. R = <L|,|TL> \<and> \<Gamma> \<turnstile> \<lparr>t|;|\<sigma>1\<rparr> |:| (TL ! i) \<and> l = L ! i"
    using has_type_VariantE[OF H4]
    by metis    
next
  assume H5: "\<Gamma> \<turnstile> \<lparr>Case t of <L1:=I> \<Rightarrow> LT|;|\<sigma>1\<rparr> |:| A"
  show "\<exists>TL. L1\<noteq>\<emptyset> \<and> length I = length L1 \<and> length L1 = length TL \<and> length L1 = length LT \<and>
      \<Gamma> \<turnstile> \<lparr> t |;| \<sigma>1 \<rparr> |:| <L1|,|TL> \<and> (\<forall>i<length L1. insert_nth (I!i) (TL!i) \<Gamma> \<turnstile> \<lparr>(LT!i)|;| \<sigma>1\<rparr> |:| A)"
    using has_type_CaseVE[OF H5]
    by (metis append_Cons append_Nil insert_nth_take_drop)
qed (auto elim: has_type_L.cases has_type_ProjTE, metis has_type_ProjRE)


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
      by (force intro!: has_type_L.intros(14))+
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
  case (has_type_Let \<Gamma> t1 \<sigma>1 A x t2 B)
    
    have "n \<le> x \<Longrightarrow> (take n \<Gamma> @ drop n \<Gamma> |,| S) \<turnstile> \<lparr>Let var Suc x := shift_L 1 n t1 in shift_L 1 n t2|;| \<sigma>1\<rparr> |:| B"
      using has_type_Let(5) has_type_Let(3)
            has_type_Let(4)[unfolded length_insert_nth,  of n] 
            insert_nth_comp(1)[OF has_type_Let(5), of x S A] 
      by (auto intro!: has_type_L.intros(10))  
    then show ?case
      using has_type_Let(3)[OF has_type_Let(5)] 
            has_type_Let(4)[unfolded length_insert_nth, of "Suc n" ] 
            has_type_Let(5)
            insert_nth_comp(2)[OF has_type_Let(5),of x S A]  
      by (auto intro!: has_type_L.intros(10)) 
next
  case (has_type_LetPattern p B t1 \<sigma>1 \<Gamma> \<sigma>2 t2 A)
    note hyps=this
    show ?case
      using hyps(1,2) hyps(5)[OF hyps(7)]
            hyps(6)[OF hyps(7)]
      by (auto intro: has_type_L.intros(19))
next
  case (has_type_Case \<Gamma>1 t \<sigma>1 A B x t1 C y t2)


    have Sum_type: "insert_nth n S \<Gamma>1 \<turnstile> \<lparr>shift_L 1 n t|;| \<sigma>1\<rparr> |:| A |+| B"
      using has_type_Case(4)[OF has_type_Case(7)] 
      by auto

    have B1:"n \<le> x \<Longrightarrow> n \<le> y \<Longrightarrow> insert_nth (Suc x) A (insert_nth n S \<Gamma>1) \<turnstile> \<lparr>shift_L 1 n t1|;|\<sigma>1\<rparr> |:| C \<and>
                                  insert_nth (Suc y) B (insert_nth n S \<Gamma>1) \<turnstile> \<lparr>shift_L 1 n t2|;|\<sigma>1\<rparr> |:| C"
      using  has_type_Case(5)[of n] has_type_Case(7)
             has_type_Case(6)[of n]
             insert_nth_comp(1)[of n \<Gamma>1 _ S _] length_insert_nth
      by (metis le_SucI)+

    have B2: " n \<le> x \<Longrightarrow> \<not> n \<le> y \<Longrightarrow> insert_nth (Suc x) A (insert_nth n S \<Gamma>1) \<turnstile> \<lparr>shift_L 1 n t1|;|\<sigma>1\<rparr> |:| C \<and> 
                                      insert_nth y B (insert_nth n S \<Gamma>1) \<turnstile> \<lparr>shift_L 1 (Suc n) t2|;|\<sigma>1\<rparr> |:| C"
      using  has_type_Case(5)[of n, unfolded length_insert_nth]
             has_type_Case(6)[of "Suc n", unfolded length_insert_nth]  
             has_type_Case(7) insert_nth_comp[of n \<Gamma>1 _ S _] 
      by (metis Suc_le_mono not_le le_SucI)+

    have B3: "\<not> n \<le> x \<Longrightarrow>  n \<le> y \<Longrightarrow> insert_nth x A (insert_nth n S \<Gamma>1) \<turnstile> \<lparr>shift_L 1 (Suc n) t1|;|\<sigma>1\<rparr> |:| C \<and>
                                      insert_nth (Suc y) B (insert_nth n S \<Gamma>1) \<turnstile> \<lparr>shift_L 1 n t2|;|\<sigma>1\<rparr> |:| C"
      using  has_type_Case(5)[of "Suc n", unfolded length_insert_nth]
             has_type_Case(6)[of n, unfolded length_insert_nth]  
             has_type_Case(7) insert_nth_comp[of n \<Gamma>1 _ S _] 
      by (metis Suc_le_mono not_le le_SucI)+

    have B4: "\<not> n \<le> x \<Longrightarrow> \<not> n \<le> y \<Longrightarrow> insert_nth x A (insert_nth n S \<Gamma>1) \<turnstile> \<lparr>shift_L 1 (Suc n) t1|;|\<sigma>1\<rparr> |:| C \<and>
                                      insert_nth y B (insert_nth n S \<Gamma>1) \<turnstile> \<lparr>shift_L 1 (Suc n) t2|;|\<sigma>1\<rparr> |:| C"
       using has_type_Case(5)[of "Suc n", unfolded length_insert_nth]
             has_type_Case(6)[of "Suc n", unfolded length_insert_nth]  
             has_type_Case(7) insert_nth_comp(2)[of n \<Gamma>1 _ S _] 
      by (metis Suc_le_mono not_le)+

    show ?case
      using has_type_Case(4)[OF has_type_Case(7)]
            has_type_L.intros(22) B1 B2 B3 B4
      by force      
next
  case (has_type_CaseV L I TL LT \<Gamma> t \<sigma>1 A)
    have branches_wtyped:"\<forall>i<length L.
       insert_nth (map (\<lambda>x. if n \<le> x then nat (int x + 1) else x) I ! i) (TL ! i) (take n \<Gamma> @ drop n \<Gamma> |,| S)
       \<turnstile> \<lparr>((indexed_map 0 (\<lambda>k. shift_L 1 (if (I!k)<n then Suc n else n)) LT) ! i)|;| \<sigma>1\<rparr> |:| A"
      proof (rule+)
        fix i
        assume H:"i<length L"
        have P:"\<And>k. k\<le>length (insert_nth (I ! i) (TL ! i) \<Gamma>) \<Longrightarrow>
                     insert_nth k S (insert_nth (I ! i) (TL ! i) \<Gamma>) \<turnstile> \<lparr>shift_L 1 k (LT ! i)|;|\<sigma>1\<rparr>|:| A"
          using has_type_CaseV(7) H 
          by auto

        then have branches_type_n:"insert_nth n S (insert_nth (I ! i) (TL ! i) \<Gamma>) \<turnstile> \<lparr>shift_L 1 n (LT ! i)|;| \<sigma>1\<rparr> |:| A"
          using  has_type_CaseV(8)    
                 length_insert_nth[of "I!i" "TL!i" \<Gamma>]
          by (metis le_SucI)

        have branches_type_Sucn:"insert_nth (Suc n) S (insert_nth (I ! i) (TL ! i) \<Gamma>) \<turnstile> \<lparr>shift_L 1 (Suc n) (LT ! i)|;|\<sigma>1\<rparr> |:| A"
          using  has_type_CaseV(8)
                 length_insert_nth[of "I!i" "TL!i" \<Gamma>] P[of "Suc n"]
          by (metis Suc_le_mono)

        have 1:"n\<le> I!i \<Longrightarrow> insert_nth (map (\<lambda>x. if n \<le> x then nat (int x + 1) else x) I ! i) (TL ! i) (take n \<Gamma> @ drop n \<Gamma> |,| S)
                \<turnstile> \<lparr>((indexed_map 0 (\<lambda>k. shift_L 1 (if (I!k)<n then Suc n else n)) LT) ! i)|;|\<sigma>1\<rparr> |:| A"
          using has_type_CaseV(1,2,8) H        
          proof -
            
            assume hyps:"n \<le> I ! i" "L \<noteq> \<emptyset>" "length I = length L" "n \<le> length \<Gamma>" "i < length L"
            have simp_ind:"indexed_map 0 (\<lambda>k. shift_L 1 (if I ! k < n then Suc n else n)) LT ! i =
                  (shift_L 1 n (LT ! i))"
              using hyps(1,5)[unfolded has_type_CaseV(4)]
              by (simp add: index_not_index_cong[of 0 "\<lambda>k. shift_L 1 (if I ! k < n then Suc n else n)" LT, simplified])
            
            from branches_type_n
              have "insert_nth (Suc (I ! i)) (TL ! i) (take n \<Gamma> @ drop n \<Gamma> |,| S) \<turnstile> \<lparr>shift_L 1 n (LT ! i)|;|\<sigma>1\<rparr> |:| A"
                using insert_nth_comp(1)[OF hyps(4,1)] H has_type_CaseV(4)
                by force
            
            with simp_ind show ?thesis using hyps by force

          qed

        have  "\<not> n\<le> I!i \<Longrightarrow> insert_nth (map (\<lambda>x. if n \<le> x then nat (int x + 1) else x) I ! i) (TL ! i) (take n \<Gamma> @ drop n \<Gamma> |,| S)
                \<turnstile> \<lparr>((indexed_map 0 (\<lambda>k. shift_L 1 (if (I!k)<n then Suc n else n)) LT) ! i)|;|\<sigma>1\<rparr> |:| A"
          using has_type_CaseV(1,2,8) H        
          proof -            
            assume hyps:"\<not>n \<le> I ! i" "L \<noteq> \<emptyset>" "length I = length L" "n \<le> length \<Gamma>" "i < length L"
            
            have simp_ind:"indexed_map 0 (\<lambda>k. shift_L 1 (if I ! k < n then Suc n else n)) LT ! i =
                  (shift_L 1 (Suc n) (LT ! i))"
              using hyps(1,5)[unfolded has_type_CaseV(4)]
              by (simp add: index_not_index_cong[of 0 "\<lambda>k. shift_L 1 (if I ! k < n then Suc n else n)" LT, simplified])
            
            from branches_type_Sucn
              have  "insert_nth (I ! i) (TL ! i) (take n \<Gamma> @ drop n \<Gamma> |,| S) \<turnstile> \<lparr>shift_L 1 (Suc n) (LT ! i)|;|\<sigma>1\<rparr> |:| A"
                using insert_nth_comp(2)[OF hyps(4), of "I!i"] hyps(1)[unfolded not_le[of n "I!i"]]
                by fastforce

            with simp_ind show ?thesis using hyps by force
              
          qed

        with 1 show "insert_nth (map (\<lambda>x. if n \<le> x then nat (int x + 1) else x) I ! i) (TL ! i) (take n \<Gamma> @ drop n \<Gamma> |,| S)
         \<turnstile> \<lparr>((indexed_map 0 (\<lambda>k. shift_L 1 (if (I!k)<n then Suc n else n)) LT) ! i)|;| \<sigma>1\<rparr> |:| A"
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

lemma canonical_forms:
  "is_value_L v \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>v|;|\<sigma>\<rparr> |:| Bool \<Longrightarrow> v = LTrue \<or> v = LFalse"
  "is_value_L v \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>v|;|\<sigma>\<rparr> |:| T1 \<rightarrow> T2 \<Longrightarrow> \<exists>t n. v = LAbs T1 t"
  "is_value_L v \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>v|;|\<sigma>\<rparr> |:| Unit \<Longrightarrow> v = unit"
  "is_value_L v \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>v|;|\<sigma>\<rparr> |:| A |\<times>| B \<Longrightarrow> \<exists>v1 v2. is_value_L v1 \<and> is_value_L v2 \<and> v= \<lbrace>v1,v2\<rbrace>"
  "is_value_L v \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>v|;|\<sigma>\<rparr> |:| \<lparr>TL\<rparr> \<Longrightarrow> \<exists>L. is_value_L (Tuple L) \<and> v = Tuple L \<and> length TL = length L"
  "is_value_L v \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>v|;|\<sigma>\<rparr> |:| \<lparr>L|:|TL\<rparr> \<Longrightarrow> \<exists>LT. is_value_L (Record L LT) \<and> v = (Record L LT)" 
  "is_value_L v \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>v|;|\<sigma>\<rparr> |:| A|+|B \<Longrightarrow> (\<exists>v1. is_value_L v1 \<and> v = inl v1 as A|+|B) \<or> (\<exists>v1. v = inr v1 as A|+|B \<and> is_value_L v1)"
  "is_value_L v \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>v|;|\<sigma>\<rparr> |:| \<lambda>List A \<Longrightarrow> (v = Lnil A) \<or> (\<exists>v1 v2. is_value_L v1 \<and> is_value_L v2 \<and>
                                                                v = Lcons A v1 v2)"
proof -
  assume  val: "is_value_L v" and 
          typed: "\<Gamma> \<turnstile> \<lparr>v|;|\<sigma>\<rparr> |:| A|+|B"
  show "(\<exists>v1. is_value_L v1 \<and> v = inl v1 as A|+|B) \<or> (\<exists>v1. v = inr v1 as A|+|B \<and> is_value_L v1)"
    using val typed
    by (induction rule: is_value_L.induct, auto elim: "has_type_L.cases")
qed (auto elim: "is_value_L.cases" "has_type_L.cases")  

lemma progress:
  "\<emptyset> \<turnstile> \<lparr>t|;|empty\<rparr> |:| A \<Longrightarrow> is_value_L t \<or> (\<exists>t1. eval1_L t t1)"
proof (induction "\<emptyset>::ltype list" t "empty::nat\<rightharpoonup>ltype" A rule: has_type_L.induct)
  case (has_type_LIf t1 t2 A t3)
    thus ?case by (metis eval1_L.intros canonical_forms)
next
  case (has_type_LetPattern)
    thus ?case sorry
next
  case (has_type_Tuple L TL)
    note hyps=this
    have "(\<exists>j<length L. (\<forall>i<j. is_value_L (L ! i)) \<and> (\<exists>t1. eval1_L (L ! j) t1))\<or>
          is_value_L (Tuple L)"
      
      sorry
    thus ?case sorry
next
  case (has_type_RCD)
    thus ?case sorry
next
  case (has_type_ProjT i TL t)
   thus ?case 
     by (metis eval1_L.intros canonical_forms)     
next
  case (has_type_CaseV L I TL LT t A)
    note hyps=this
    show ?case
      sorry
next
  case (has_type_head t A)
    note hyps=this
    show ?case
      using canonical_forms(8)[OF _ hyps(1)]
            hyps(2)
      sorry
next
  case (has_type_tail t A)
     note hyps=this
    show ?case
      using canonical_forms(8)[OF _ hyps(1)]
            hyps(2)
      sorry
next
  case (has_type_Variant t TL i)
    thus ?case sorry
next
  case (has_type_isNil)
    thus ?case sorry
qed (force intro!: is_value_L.intros eval1_L.intros dest: canonical_forms)+

end
