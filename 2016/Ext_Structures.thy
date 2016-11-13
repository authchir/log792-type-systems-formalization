(*<*)
theory Ext_Structures
imports
   Main
   List_extra
  "~~/src/HOL/List"
  "~~/src/HOL/Eisbach/Eisbach"
  "~~/src/HOL/Eisbach/Eisbach_Tools"
  "$AFP/List-Index/List_Index" 
begin
(*>*)

section{*Pair, Tuples and Records*

text{* In this section,we extend our current lambda calculus with extended structures (pairs, tuples, records)*}

datatype ltype =
  Bool |
  T (num:nat) |
  Unit |
  Prod ltype ltype (infix "|\<times>|" 225)|
  Fun (domain: ltype) (codomain: ltype) (infixr "\<rightarrow>" 225)|
  TupleT "ltype list" ( "\<lparr>_\<rparr>" [150]225) |
  RecordT "string list" "ltype list" ( "\<lparr>_|:|_\<rparr>" [150,150] 225) |
  Sum ltype ltype (infix "|+|" 225)

datatype Lpattern = V nat | RCD "string list" "Lpattern list"

datatype lterm =
  LTrue |
  LFalse |
  LIf (bool_expr: lterm) (then_expr: lterm) (else_expr: lterm) |
  LVar nat |
  LAbs (arg_type: ltype) (body: lterm) |
  LApp lterm lterm |
  unit |
  Seq (fp: lterm) (sp: lterm) ("(_;;_)" [100,50] 200) |
  AS lterm ltype ("_/ as/ _" [100,150] 200) |
  LetBinder nat lterm lterm ("Let/ var/ (_)/ :=/ (_)/ in/ (_)" [100,120,150] 250) | 
  Pair lterm lterm ("\<lbrace>_,_\<rbrace>" [100,150] 250) |
  Proj1 lterm ("\<pi>1/ _" [100] 250) |
  Proj2 lterm ("\<pi>2/ _" [100] 250) |
  Tuple "lterm list" |
  ProjT nat lterm ("\<Pi>/ _/ (_)" [100,150] 250) |
  Record "string list" "lterm list" |
  ProjR string lterm |
  Pattern Lpattern ("<|_|>" [100] 250)|
  LetP Lpattern lterm lterm ("Let/ pattern/ (_)/ :=/ (_)/ in/ (_)"[100,120,150]250)|
  inl lterm ltype ("inl/ (_)/ as/ (_)" [100,100]200)|
  inr lterm ltype ("inr/ (_)/ as/ (_)" [100,100]200)|
  CaseSplit lterm nat lterm nat lterm ("Case/ (_)/ of/ Inl/ (_)/ \<Rightarrow>/ (_)/ |/ Inr/ (_)/ \<Rightarrow>/ (_)" [100, 100,100, 100, 100]200)

primrec shift_L :: "int \<Rightarrow> nat \<Rightarrow> lterm \<Rightarrow> lterm" where
  "shift_L d c LTrue = LTrue" |
  "shift_L d c LFalse = LFalse" |
  "shift_L d c (LIf t1 t2 t3) = LIf (shift_L d c t1) (shift_L d c t2) (shift_L d c t3)" |
  "shift_L d c (LVar k) = LVar (if k < c then k else nat (int k + d))" |
  "shift_L d c (LAbs T' t) = LAbs T' (shift_L d (Suc c) t)" |
  "shift_L d c (LApp t1 t2) = LApp (shift_L d c t1) (shift_L d c t2)" |
  "shift_L d c unit = unit" |
  "shift_L d c (Seq t1 t2) = Seq (shift_L d c t1) (shift_L d c t2)" |
  "shift_L d c (t as A) = (shift_L d c t) as A" |
  "shift_L d c (Let var x := t in t1) = 
    (if x\<ge> c then Let var (nat (int x + d)) := (shift_L d c t) in (shift_L d c t1)
     else  Let var x := (shift_L d c t) in (shift_L d c t1)
     )" |
  "shift_L d c (\<lbrace>t1,t2\<rbrace>) = \<lbrace> shift_L d c t1 , shift_L d c t2 \<rbrace>" |
  "shift_L d c (\<pi>1 t) = \<pi>1 (shift_L d c t)" |
  "shift_L d c (\<pi>2 t) = \<pi>2 (shift_L d c t)" |
  "shift_L d c (Tuple L) = Tuple (map (shift_L d c) L)" |
  "shift_L d c (\<Pi> i t)   = \<Pi> i (shift_L d c t)" |
  "shift_L d c (Record L LT)  = Record L (map (shift_L d c) LT)" |
  "shift_L d c (ProjR l t) = ProjR l (shift_L d c t)" |
  "shift_L d c (Pattern p) = <|p|>" |
  "shift_L d c (Let pattern p := t1 in t2) = (Let pattern p := (shift_L d c t1) in (shift_L d c t2))" |
  "shift_L d c (inl t as T') =  inl (shift_L d c t) as T'" |
  "shift_L d c (inr t as T') =  inr (shift_L d c t) as T'" |
  "shift_L d c (Case t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2) = 
    (Case (shift_L d c t) of 
        Inl (if x\<ge> c then (nat (int x + d)) else x) \<Rightarrow> shift_L d c t1 
      | Inr (if y\<ge> c then (nat (int y + d)) else y) \<Rightarrow> shift_L d c t2)" 

primrec subst_L :: "nat \<Rightarrow> lterm \<Rightarrow> lterm \<Rightarrow> lterm" where
  "subst_L j s LTrue = LTrue" |
  "subst_L j s LFalse = LFalse" |
  "subst_L j s (LIf t1 t2 t3) = LIf (subst_L j s t1) (subst_L j s t2) (subst_L j s t3)" |
  "subst_L j s (LVar k) = (if k = j then s else LVar k)" |
  "subst_L j s (LAbs T' t) = LAbs T' (subst_L (Suc j) (shift_L 1 0 s) t)" |
  "subst_L j s (LApp t1 t2) = LApp (subst_L j s t1) (subst_L j s t2)" |
  "subst_L j s unit = unit" |
  "subst_L j s (Seq t1 t2) = Seq (subst_L j s t1) (subst_L j s t2)" |
  "subst_L j s (t as A) = (subst_L j s t) as A" |
  "subst_L j s (Let var x := t in t1) = 
  (if j=x then Let var x := subst_L j s t in t1
    else  (Let var x := (subst_L j s t) in (subst_L j s t1))) " |
  "subst_L j s (\<lbrace>t1,t2\<rbrace>) = \<lbrace>subst_L j s t1, subst_L j s t2\<rbrace>" |
  "subst_L j s (\<pi>1 t) = \<pi>1 (subst_L j s t)" |
  "subst_L j s (\<pi>2 t) = \<pi>2 (subst_L j s t)" |
  "subst_L j s (\<Pi> i t) = \<Pi> i (subst_L j s t)" |
  "subst_L j s (Tuple L) = Tuple (map (subst_L j s) L)" |
  "subst_L j s (Record L LT) = Record L (map (subst_L j s) LT)" |
  "subst_L j s (ProjR l t) = ProjR l (subst_L j s t)" |
  "subst_L j s (Pattern p) = Pattern p" |
  "subst_L j s (Let pattern p := t1 in t2) = (Let pattern p := (subst_L j s t1) in (subst_L j s t2))" |
  "subst_L j s (inl t as T') =  inl (subst_L j s t) as T'" |
  "subst_L j s (inr t as T') =  inr (subst_L j s t) as T'" |
  "subst_L j s (Case t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2) = 
    (Case (subst_L j s t) of 
        Inl x \<Rightarrow> (if j=x then t1 else subst_L j s t1)
      | Inr y \<Rightarrow> (if j=y then t2 else subst_L j s t2))" 

fun nbinder :: "lterm \<Rightarrow> nat" where
"nbinder (LAbs A t) = Suc (nbinder t)" |
"nbinder _ = 0" 

text{*
      We want to restrict the considered pattern matching and filling to coherent cases, which are
      the cases when a pattern variable can only appear once in a given pattern.\\

      Furthermore, the same coherence principle is valid for the pattern context. A pattern variable can only 
      have on type at a time
*}

fun Pvars :: "Lpattern \<Rightarrow> nat list" where
"Pvars (V n) = [n]" |
"Pvars (RCD L PL) = (list_iter (\<lambda>x r. x @ r) [] (map Pvars PL))"


fun patterns::"lterm \<Rightarrow> nat list" where
"patterns (<|p|>) = Pvars p" |
"patterns (LIf c t1 t2)               = patterns c @ patterns t1 @ patterns t2" |
"patterns (LAbs A t1)                 = patterns t1" |
"patterns (LApp t1 t2)                = patterns t1 @ patterns t2" |
"patterns (Seq t1 t2)                 = patterns t1 @ patterns t2" |
"patterns (t1 as A)                   = patterns t1" |
"patterns (Let var x := t1 in t2)     = patterns t1 @ patterns t2" |
"patterns (\<lbrace>t1,t2\<rbrace>)                   = patterns t1 @ patterns t2" |
"patterns (Tuple L)                   = list_iter (\<lambda>e r. e @ r) [] (map (patterns) L)" |
"patterns (Record L LT)               = list_iter (\<lambda>e r. e @ r) [] (map (patterns) LT)" |
"patterns (\<pi>1 t)                      = patterns t" |
"patterns (\<pi>2 t)                      = patterns t" |
"patterns (\<Pi> i t)                     = patterns t" |
"patterns (ProjR l t)                 = patterns t" |
"patterns (Let pattern p := t1 in t2) = patterns t1 @ filter (\<lambda>x. x\<notin> set(Pvars p))(patterns t2)" |
"patterns (inl t as T') =  patterns t" |
"patterns (inr t as T') =  patterns t" |
"patterns (Case t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2) = patterns t @ patterns t1 @ patterns t2" |
"patterns t = []"

inductive is_value_L :: "lterm \<Rightarrow> bool" where
  VTrue : "is_value_L LTrue" |
  VFalse: "is_value_L LFalse" |
  VAbs  :"is_value_L (LAbs T' t)" |
  VUnit :"is_value_L unit" |
  VPair :"is_value_L v1 \<Longrightarrow> is_value_L v2 \<Longrightarrow> is_value_L (\<lbrace>v1,v2\<rbrace>)" |
  VTuple:"(\<And>i.0\<le>i \<Longrightarrow> i<length L \<Longrightarrow> is_value_L (L!i)) \<Longrightarrow> is_value_L (Tuple L)" |
  VRCD  :"(\<And>i.0\<le>i \<Longrightarrow> i<length LT \<Longrightarrow> is_value_L (LT!i)) \<Longrightarrow> is_value_L (Record L LT)"|
  VSumL :"is_value_L v \<Longrightarrow> is_value_L (inl v as A)"|
  VSumR :"is_value_L v \<Longrightarrow> is_value_L (inr v as A)"

primrec FV :: "lterm \<Rightarrow> nat set" where
  "FV LTrue = {}" |
  "FV LFalse = {}" |
  "FV (LIf t1 t2 t3) = FV t1 \<union> FV t2 \<union> FV t3" |
  "FV (LVar x) = {x}" |
  "FV (LAbs T1 t) = image (\<lambda>x. x - 1) (FV t - {0})" |
  "FV (LApp t1 t2) = FV t1 \<union> FV t2" |
  "FV unit = {}" |
  "FV (Seq t1 t2) = FV t1 \<union> FV t2" |
  "FV (t as A) = FV t" |
  "FV (Let var x:= t in t1) = 
    (if x \<in> FV t1 then (FV t1 - {x}) \<union> FV t else FV t1)" |
  "FV (\<lbrace>t1,t2\<rbrace>) = FV t1 \<union> FV t2" |
  "FV (\<pi>1 t) =  FV t" |
  "FV (\<pi>2 t) =  FV t" |
  "FV (Tuple L) = list_iter (\<lambda>x r. x \<union> r) {} (map FV L) "|
  "FV (\<Pi> i t) = FV t" |
  "FV (Record L LT) = list_iter (\<lambda>x r. x \<union> r) {} (map FV LT) "|
  "FV (ProjR l t) = FV t" |
  "FV (Pattern p) = {}" |
  "FV (Let pattern p := t1 in t2) = FV t1 \<union> FV t2" |
  "FV (inl t as A) = FV t" |
  "FV (inr t as A) = FV t" |
  "FV (Case t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2) = FV t1 \<union> FV t2"


text{*
    We implement pattern matching and replacing with the following function and definition:
    
    \begin{itemize}
      \item a \textbf{pattern context} 
      \item a \textbf{pattern substitution} is a list of pairs (pattern var index, lterm)
      \item \textbf{fill}, which will fill the patterns in a ltern with a lterm (based on a pattern substitution)
      \item \textbf{Lmatch} is a predicate on a pattern, a value and a pattern substitution indicating 
              if the pattern substitution associates the given pattern's variables to the corresponding part(s) of the
              given value
    \end{itemize}
*}

inductive same_dom:: "(nat \<Rightarrow> lterm) \<Rightarrow> nat list \<Rightarrow>bool" where
  empty: "(\<And>x. f x = <|V x|>)\<Longrightarrow> same_dom f []" |
  non_empty: "(\<And>x. x\<in>set A \<Longrightarrow> f x \<noteq> <|V x|>) \<Longrightarrow> same_dom f A"

fun p_instantiate::"(nat\<Rightarrow> lterm) \<Rightarrow> Lpattern \<Rightarrow> lterm" where
"p_instantiate \<Delta> (V k) = \<Delta> k"|
"p_instantiate \<Delta> (RCD L PL) =  (if (same_dom \<Delta> (Pvars (RCD L PL)) \<and> (Pvars (RCD L PL)\<noteq>[])) then Record L (map (p_instantiate \<Delta>) PL)
                                else <|RCD L PL|>)"

fun fill::"(nat \<Rightarrow> lterm) \<Rightarrow> lterm \<Rightarrow> lterm" where
"fill \<Delta> (Pattern p)                 = p_instantiate \<Delta> p" |
"fill \<Delta> (LIf c t1 t2)               = LIf (fill \<Delta> c) (fill \<Delta> t1) (fill \<Delta> t2)" |
"fill \<Delta> (LAbs A t1)                 = LAbs A (fill \<Delta> t1)" |
"fill \<Delta> (LApp t1 t2)                = LApp (fill \<Delta> t1) (fill \<Delta> t2)" |
"fill \<Delta> (Seq t1 t2)                 =  Seq (fill \<Delta> t1) (fill \<Delta> t2)" |
"fill \<Delta> (t1 as A)                   = (fill \<Delta> t1) as A" |
"fill \<Delta> (Let var x := t1 in t2)     = (Let var x := (fill \<Delta> t1) in (fill \<Delta> t2))" |
"fill \<Delta> (\<lbrace>t1,t2\<rbrace>)                   = \<lbrace>(fill \<Delta> t1), (fill \<Delta> t2)\<rbrace>" |
"fill \<Delta> (Tuple L)                   = Tuple (map (fill \<Delta>) L)" |
"fill \<Delta> (Record L LT)               = Record L (map (fill \<Delta>) LT)" |
"fill \<Delta> (\<pi>1 t)                      = \<pi>1 (fill \<Delta> t)" |
"fill \<Delta> (\<pi>2 t)                      = \<pi>2 (fill \<Delta> t)" |
"fill \<Delta> (\<Pi> i t)                     = \<Pi> i (fill \<Delta> t)" |
"fill \<Delta> (ProjR l t)                 = ProjR l (fill \<Delta> t)" |
"fill \<Delta> (Let pattern p := t1 in t2) = (Let pattern p := (fill \<Delta> t1) in (fill \<Delta> t2))" |
"fill \<Delta> (inl t as A) = inl (fill \<Delta> t) as A"|
"fill \<Delta> (inr t as A) = inr (fill \<Delta> t) as A"|
"fill \<Delta> (Case t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2) = (Case (fill \<Delta> t) of Inl x \<Rightarrow> (fill \<Delta> t1) | Inr y \<Rightarrow> (fill \<Delta> t2))"|
"fill \<Delta> t = t"

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
  eval1_L_Case:
    "eval1_L t t' \<Longrightarrow> eval1_L (Case t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2) (Case t' of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2)" |
  eval1_L_Inl:
    "eval1_L t t' \<Longrightarrow> eval1_L (inl t as A) (inl t' as A)" |
  eval1_L_Inr:
    "eval1_L t t' \<Longrightarrow> eval1_L (inr t as A) (inr t' as A)"

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
    "\<Gamma> \<turnstile> \<lparr>t|;|fill \<delta>1\<rparr> |:| A|+|B \<Longrightarrow> replace x A \<Gamma> \<turnstile> \<lparr>t1|;|fill \<delta>1\<rparr> |:| C \<Longrightarrow>
     replace y B \<Gamma> \<turnstile> \<lparr>t2|;|fill \<delta>1\<rparr> |:| C \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Case t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2 |;|fill \<delta>1\<rparr> |:| C"

inductive_cases has_type_LetE : "\<Gamma> \<turnstile> \<lparr> Let var x := t1 in t2|;|\<delta>1\<rparr>  |:| B"
inductive_cases has_type_ProjTE: "\<Gamma> \<turnstile> \<lparr> \<Pi> i t|;|\<delta>1\<rparr> |:| R"
inductive_cases has_type_ProjRE: "\<Gamma> \<turnstile> \<lparr> ProjR l t|;|\<delta>1\<rparr> |:| R"
inductive_cases has_type_LetPE: "\<Gamma> \<turnstile> \<lparr>Let pattern p := t1 in t2|;|\<delta>1\<rparr> |:| A"
inductive_cases has_type_CaseE: "\<Gamma> \<turnstile> \<lparr>Case t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2|;|\<delta>1\<rparr> |:| R"
inductive_cases has_type_LAbsE: "\<Gamma> \<turnstile> \<lparr>LAbs T1 t2|;|fill \<delta>'\<rparr> |:| R"

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
    by (cases "length \<Gamma> \<le> x"; cases "length \<Gamma> \<le> y"; insert has_type_CaseE[OF H2]; metis replace.simps)
next
  assume H3:"\<Gamma> \<turnstile> \<lparr>LAbs T1 t2|;|fill \<delta>'\<rparr> |:| R"
  show "\<exists>R2 \<Delta>. R = T1 \<rightarrow> R2 \<and> \<Gamma> |,| T1 \<turnstile> \<lparr>t2|;|fill (shift_L 1 (Suc (nbinder t2)) \<circ> \<Delta>)\<rparr> |:| R2 \<and> fill \<Delta> = fill \<delta>'"
    using has_type_LAbsE[OF H3]
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
            "has_type_L.intros"(15)[OF has_type_ProjT(1,2)]
      by fastforce
next
  case (has_type_RCD L LT TL \<Gamma> \<delta>1)
    show ?case
      using has_type_RCD(1-4) nth_map[of _ LT "shift_L 1 n"]
            has_type_RCD(6)[OF _ has_type_RCD(7,8)]           
      by (force intro!: "has_type_L.intros"(16))+
next
  case (has_type_Let \<Gamma>1 t1 \<delta>1 A x t2 B)
    have 1:"n\<le>x \<Longrightarrow> ?case"
      proof -
        assume le_x: "n\<le>x"
        show ?case
          using has_type_Let(4-6) le_x
                "has_type_L.intros"(10)[OF has_type_Let(2)[OF has_type_Let(5,6)], of "Suc x"]
          by  (simp add: le_x del: Fun.comp_apply,
                metis insert_nth_take_drop rep_ins replace_inv_length append_Cons append_Nil2 append_eq_append_conv_if)
      qed

    have "n>x \<Longrightarrow> ?case"
      using has_type_Let(4-6) rep_ins2[OF _ has_type_Let(6), of x S A]
            "has_type_L.intros"(10)[OF has_type_Let(2)[OF has_type_Let(5,6)], of x]
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
                "shift_L.simps"(18)
          by metis
      qed
    have 1:"insert_nth n S \<Gamma>1 \<turnstile> \<lparr>(fill (shift_L 1 n \<circ> \<delta>) ^^ m) (<|V k|>)|;|id\<rparr> |:| A" 
      using has_type_PatternVar(2)[OF fill_id has_type_PatternVar(5)]
            HOL.sym[OF fill_id] HB HC
      by simp
    have "set (patterns ((fill (shift_L 1 n \<circ> \<delta>) ^^ m) (<|V k|>))) = {}"
      using has_type_PatternVar(3,4) pattern_fill_shift[of m 1 n \<delta> "<|V k|>"]
      by fastforce  
    with 1 show ?case by (auto intro:"has_type_L.intros"(18)[where \<delta>="(shift_L 1 n \<circ> \<delta>)"])
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
      by (auto)(insert A B1 B2 B3 B4 "has_type_L.intros"(23), force+)
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
proof -
  assume  val: "is_value_L v" and 
          typed: "\<Gamma> \<turnstile> \<lparr>v|;|\<delta>\<rparr> |:| A|+|B"
  show "(\<exists>v1. is_value_L v1 \<and> v = inl v1 as A|+|B) \<or> (\<exists>v1. v = inr v1 as A|+|B \<and> is_value_L v1)"
    using val typed
    by (induction rule: is_value_L.induct, auto elim: "has_type_L.cases")
qed (auto elim: "is_value_L.cases" "has_type_L.cases")  



end
