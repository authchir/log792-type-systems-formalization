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

section{*Pair, Tuples and Records*}

text{* In this section,we extend our current lambda calculus with extended structures (pairs, tuples, records)*}

datatype ltype =
  Bool |
  T (num:nat) |
  Unit |
  Prod ltype ltype (infix "|\<times>|" 225)|
  Fun (domain: ltype) (codomain: ltype) (infixr "\<rightarrow>" 225)|
  TupleT "ltype list" ( "\<lparr>_\<rparr>" [150]225) |
  RecordT "string list" "ltype list" ( "\<lparr>_|:|_\<rparr>" [150,150] 225)

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
  LetP Lpattern lterm lterm ("Let/ pattern/ (_)/ :=/ (_)/ in/ (_)"[100,120,150]250)
  
abbreviation Record1 :: "(string\<times>lterm) list \<Rightarrow> lterm" where
"Record1 L \<equiv> Record (map fst L) (map snd L)"

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
  "shift_L d c (Pattern p) = Pattern p" |
  "shift_L d c (Let pattern p := t1 in t2) = (Let pattern p := (shift_L d c t1) in (shift_L d c t2))"

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
  "subst_L j s (Let pattern p := t1 in t2) = (Let pattern p := (subst_L j s t1) in (subst_L j s t2))"


text{*
      We want to restrict the considered pattern matching and filling to coherent cases, which are
      the cases when a pattern variable can only appear once in a given pattern.\\

      Furthermore, the same coherence principle is valid for the pattern context. A pattern variable can only 
      have on type at a time
*}

fun Pvars :: "Lpattern \<Rightarrow> nat list" where
"Pvars (V n) = [n]" |
"Pvars (RCD L PL) = (list_iter (\<lambda>x r. x @ r) [] (map Pvars PL))"

lemma Pvars_nil:
  "Pvars p = [] \<Longrightarrow>\<exists>L PL. p = RCD L PL \<and> (\<forall>i<length PL. Pvars (PL ! i) = [])"
sorry


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
"patterns (Let pattern p := t1 in t2) = patterns t1 @ patterns t2 " |
"patterns t = []"

inductive is_value_L :: "lterm \<Rightarrow> bool" where
  "is_value_L LTrue" |
  "is_value_L LFalse" |
  "is_value_L (LAbs T' t)" |
  "is_value_L unit" |
  "is_value_L v1 \<Longrightarrow> is_value_L v2 \<Longrightarrow> is_value_L (\<lbrace>v1,v2\<rbrace>)" |
  "(\<And>i.0\<le>i \<Longrightarrow> i<length L \<Longrightarrow> is_value_L (L!i)) \<Longrightarrow> is_value_L (Tuple L)" |
  "(\<And>i.0\<le>i \<Longrightarrow> i<length LT \<Longrightarrow> is_value_L (LT!i)) \<Longrightarrow> is_value_L (Record L LT)"

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
  "FV (Let pattern p := t1 in t2) = FV t1 \<union> FV t2"



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

fun p_instantiate::"(nat \<times> lterm) list \<Rightarrow> Lpattern \<Rightarrow> lterm" where
"p_instantiate \<Delta> (V k) = (case (find (\<lambda>p. fst p = k) \<Delta>) of None \<Rightarrow> <|V k|> | Some p \<Rightarrow> snd p)"|
"p_instantiate \<Delta> (RCD L PL) =  (if (set (Pvars (RCD L PL)) \<inter> set (fst_extract \<Delta>) = {}) then <|RCD L PL|>
                                 else Record L (map (p_instantiate \<Delta>) PL))"

fun fill::"(nat \<times> lterm) list \<Rightarrow> lterm \<Rightarrow> lterm" where
(*"fill \<Delta> (Pattern p)                 = (if(set (Pvars p) \<subseteq> set(fst_extract \<Delta>)) then p_instantiate \<Delta> p else Pattern p)" |*)
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
"fill \<Delta> t = t"

inductive Lmatch ::"Lpattern \<Rightarrow> lterm \<Rightarrow> (nat\<times>lterm) list \<Rightarrow> bool" where
  M_Var:
    "is_value_L v \<Longrightarrow> Lmatch (V n) v [(n,v)]" |
  M_RCD:
    "distinct L \<Longrightarrow> length L = length LT \<Longrightarrow> length F = length PL \<Longrightarrow> length PL = length LT 
    \<Longrightarrow> is_value_L (Record L LT) \<Longrightarrow> (\<And>i. i<length PL \<Longrightarrow> Lmatch (PL!i) (LT!i) (F!i))
    \<Longrightarrow> Lmatch (RCD L PL) (Record L LT) (list_iter (\<lambda>g r. g @ r) [] F)"

abbreviation coherent_Subst :: "(nat\<times>lterm) list \<Rightarrow> bool" where
"coherent_Subst \<Delta> \<equiv> distinct(fst_extract \<Delta>)"

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
    "coherent p \<Longrightarrow> is_value_L v1 \<Longrightarrow> Lmatch p v1 \<sigma> \<Longrightarrow> eval1_L (Let pattern p := v1 in t2) (fill \<sigma> t2)" |
  eval1_L_LetP:
    "eval1_L t1 t1' \<Longrightarrow> eval1_L (Let pattern p := t1 in t2) (Let pattern p := t1' in t2)"

type_synonym lcontext = "ltype list"
type_synonym pcontext = "(nat\<times>ltype) list"

notation Nil ("\<emptyset>")
abbreviation cons :: "lcontext \<Rightarrow> ltype \<Rightarrow> lcontext" (infixl "|,|" 200) where
  "cons \<Gamma> T' \<equiv> T' # \<Gamma>"
abbreviation elem' :: "(nat \<times> ltype) \<Rightarrow> lcontext \<Rightarrow> bool" (infix "|\<in>|" 200) where
  "elem' p \<Gamma> \<equiv> fst p < length \<Gamma> \<and> snd p = nth \<Gamma> (fst p)"


text{*  For the typing rule of letbinder, we require to replace the type 
        of the variable by the expected type 
    *}

(*

inductive_cases has_type_LetE : "\<Delta> |;| \<Gamma> \<turnstile> Let var x := t1 in t2 |:| B"
inductive_cases has_type_ProjTE: "\<Delta> |;| \<Gamma> \<turnstile> \<Pi> i t |:| R"
inductive_cases has_type_ProjRE: "\<Delta> |;| \<Gamma> \<turnstile> ProjR l t |:| R"
*)

inductive has_type_L :: "lcontext \<Rightarrow> lterm \<Rightarrow> (nat\<times>lterm) list \<Rightarrow> ltype \<Rightarrow> bool" ("((_)/ \<turnstile> \<lparr>(_)|;|(_)\<rparr>/ |:| (_))" [150, 150, 150, 150] 150) where
  -- "Rules relating to the type of Booleans"
  has_type_LTrue:
    "\<Gamma> \<turnstile> \<lparr>LTrue|;|\<delta>\<rparr> |:| Bool" |
  has_type_LFalse:
    "\<Gamma> \<turnstile> \<lparr>LFalse|;|\<delta>\<rparr> |:| Bool" |
  has_type_LIf:
    "\<Gamma> \<turnstile> \<lparr>t1|;|\<delta>\<rparr> |:| Bool \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t2|;|\<delta>\<rparr> |:| T' \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t3|;|\<delta>\<rparr> |:| T' \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>LIf t1 t2 t3|;|\<delta>\<rparr> |:| T'" |

  -- \<open>Rules relating to the type of the constructs of the $\lambda$-calculus\<close>
  has_type_LVar:
    "(x, T') |\<in>| \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>LVar x|;|\<delta>\<rparr> |:| (T')" |
  has_type_LAbs:
    "(\<Gamma> |,| T1) \<turnstile> \<lparr>t2|;|\<delta>\<rparr> |:| T2 \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>LAbs T1 t2|;|\<delta>\<rparr> |:| (T1 \<rightarrow> T2)" |
  has_type_LApp:
    "\<Gamma> \<turnstile> \<lparr>t1|;|\<delta>\<rparr> |:| (T11 \<rightarrow> T12) \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t2|;|\<delta>\<rparr> |:| T11 \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>LApp t1 t2|;|\<delta>\<rparr> |:| T12" |  
  has_type_LUnit:
    "\<Gamma> \<turnstile> \<lparr>unit|;|\<delta>\<rparr> |:| Unit " |  
  has_type_LSeq:
    "\<Gamma> \<turnstile> \<lparr>t1|;|\<delta>\<rparr> |:| Unit \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t2|;|\<delta>\<rparr> |:| A \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Seq t1 t2|;|\<delta>\<rparr> |:| A" |
  has_type_LAscribe:
    "\<Gamma> \<turnstile> \<lparr>t1|;|\<delta>\<rparr> |:| A \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t1 as A|;|\<delta>\<rparr> |:| A" |
  has_type_Let:
    "(\<forall>i<length \<delta>. x\<notin> FV (snd_extract \<delta> ! i)) \<Longrightarrow>\<Gamma> \<turnstile> \<lparr>t1|;|\<delta>\<rparr> |:| A \<Longrightarrow> (replace x A \<Gamma>) \<turnstile> \<lparr>t2|;|\<delta>\<rparr> |:| B \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Let var x := t1 in t2|;|\<delta>\<rparr> |:| B" |
  has_type_Pair:
    "\<Gamma> \<turnstile> \<lparr>t1|;|\<delta>\<rparr> |:| A \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t2|;|\<delta>\<rparr> |:| B \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>\<lbrace>t1,t2\<rbrace>|;|\<delta>\<rparr> |:| A |\<times>| B" |
  has_type_Proj1:
    "\<Gamma> \<turnstile> \<lparr>t1|;|\<delta>\<rparr> |:| A |\<times>| B \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>\<pi>1 t1|;|\<delta>\<rparr> |:| A" |
  has_type_Proj2:
    "\<Gamma> \<turnstile> \<lparr>t1|;|\<delta>\<rparr> |:| A |\<times>| B \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>\<pi>2 t1|;|\<delta>\<rparr> |:| B" |
  has_type_Tuple:
    "L\<noteq>[] \<Longrightarrow> length L = length TL \<Longrightarrow> (\<And>i. 0\<le>i \<Longrightarrow> i< length L \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>(L ! i)|;|\<delta>\<rparr> |:| (TL ! i))
      \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Tuple L|;|\<delta>\<rparr> |:| \<lparr>TL\<rparr>" |
  has_type_ProjT:
    "1\<le>i \<Longrightarrow> i\<le> length TL \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t|;|\<delta>\<rparr> |:| \<lparr>TL\<rparr> \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>\<Pi> i t|;|\<delta>\<rparr> |:| (TL ! (i-1))" |
  has_type_RCD:
    "L\<noteq>[] \<Longrightarrow> distinct L \<Longrightarrow> length LT = length TL \<Longrightarrow> length L = length LT \<Longrightarrow> (\<And>i. i< length LT \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>(LT ! i)|;|\<delta>\<rparr> |:| (TL ! i))
      \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Record L LT|;|\<delta>\<rparr> |:| \<lparr>L|:|TL\<rparr>" |
  has_type_ProjR:
    "distinct L1 \<Longrightarrow> l\<in> set L1  \<Longrightarrow> length L1 = length TL \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t|;|\<delta>\<rparr> |:| \<lparr>L1|:|TL\<rparr> \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>ProjR l t|;|\<delta>\<rparr> |:| (TL ! index L1 l)" |
  has_type_PatternVar:
    "\<Gamma> \<turnstile> \<lparr>t|;|\<emptyset>\<rparr> |:| A \<Longrightarrow> (k,t)\<in> set \<delta> \<Longrightarrow> \<Gamma> \<turnstile> \<lparr><|V k|>|;|\<delta>\<rparr> |:| A" |
  has_type_PatternRCD:
    "L\<noteq>[] \<Longrightarrow> distinct L \<Longrightarrow> length PL = length TL \<Longrightarrow> length L = length PL \<Longrightarrow> (\<And>i. i< length PL \<Longrightarrow> \<Gamma> \<turnstile> \<lparr><|PL ! i|>|;|\<delta>\<rparr> |:| (TL ! i))
      \<Longrightarrow> \<Gamma> \<turnstile> \<lparr><|RCD L PL|>|;|\<delta>\<rparr> |:| \<lparr>L|:|TL\<rparr>" |
  has_type_LetPattern:
    "coherent_Subst (\<delta>@\<delta>1) \<Longrightarrow> coherent p \<Longrightarrow> Lmatch p t1 \<delta>  \<Longrightarrow>
     \<Gamma> \<turnstile> \<lparr>t2|;|(\<delta>@\<delta>1)\<rparr> |:| A \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Let pattern p := t1 in t2|;|\<delta>1\<rparr> |:| A" 

  
lemma coherent_imp_distinct: "coherent_Subst L \<Longrightarrow> distinct L" 
by(induction L) (metis distinct_zipI1 zip_comp)+
  
lemma coherent_Subst_char: 
  "coherent_Subst L \<Longrightarrow> p \<in> set L \<Longrightarrow> (\<And>p1. p1\<in> set L-{p} \<Longrightarrow>  fst p \<noteq> fst p1)"
proof (induction L arbitrary:p)
  case (Cons a L')
    from this(2) have 1:"coherent_Subst L' \<and> a \<notin> set L'" 
      using coherent_imp_distinct
        by fastforce
    hence 2:"p=a \<Longrightarrow> fst p \<noteq> fst p1"
        by (metis Cons(2,4) zip_comp[of L'] Diff_insert_absorb distinct.simps(2) 
                  list.simps(15) list_iter.simps(2) prod.collapse set_zip_leftD)
    have "p\<noteq>a \<Longrightarrow> fst p \<noteq> fst p1"
      proof (cases "p1=a")
        case False
          note hyps=this
          assume H: "p\<noteq>a"
          with hyps Cons(1,4,3) 1 
            show ?thesis by auto
      next
        case True
          note hyps =this
          assume H: "p\<noteq>a"
          with hyps 
            show ?thesis
              proof -
                have "distinct (fst p1 # fst_extract L')"
                  using Cons.prems(1) hyps by auto
                then show ?thesis
                  by (metis (no_types) Cons.prems(2) H distinct.simps(2) prod.collapse set_ConsD set_zip_leftD zip_comp)
              qed
      qed              
    with 2 show ?case by auto
qed auto               
      
lemma coherent_imp_unique_index:
  "coherent_Subst L \<Longrightarrow> (n,A) \<in> set L \<Longrightarrow>find (\<lambda>p. fst p = n) L = Some (n,A)"
proof (induction L)
  case (Cons a L')
    have f1: "distinct (fst a # fst_extract L')"
      using Cons.prems(1) by auto
    { 
      assume "a \<noteq> (n, A)"
      then have "fst a \<noteq> n"
        by (metis (no_types) Cons.prems(2) Diff_insert_absorb Set.set_insert coherent_Subst_char[OF Cons(2,3)] fst_conv insertE list.set_intros(1))
      then have "find (\<lambda>p. fst p = n) (a # L') = Some (n, A) \<or> (n, A) = a"
        using f1 Cons.IH Cons.prems(2) by auto 
    }
    thus ?case
      by fastforce            
qed auto

lemma pcontext_inversion:
  "\<Gamma> \<turnstile> \<lparr>t|;|\<delta>\<rparr> |:| A \<Longrightarrow> set (patterns t) \<subseteq> set (fst_extract \<delta>)"
sorry

lemma weakening :
  "\<Gamma>' \<turnstile> \<lparr>t|;|\<delta>\<rparr> |:| A \<Longrightarrow> (\<exists>P. P@\<Gamma>' = \<Gamma>) \<Longrightarrow> set \<delta> \<subseteq> set \<delta>1 \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t|;|(\<delta>1)\<rparr> |:| A" sorry

lemma strengthening:
  "\<Gamma> \<turnstile> \<lparr>t|;|\<delta>\<rparr> |:| A \<Longrightarrow> set \<delta>1 \<subseteq> set \<delta> \<Longrightarrow> set (patterns t) \<subseteq> set(fst_extract \<delta>1) \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t|;|\<delta>1\<rparr> |:| A"
sorry

lemma fill_only_incl:
  "set(patterns t) \<inter> set (fst_extract \<delta>) = {} \<Longrightarrow> fill \<delta> t = t"
proof (induction t arbitrary: \<delta>)
  case (Tuple L)
    thus ?case by (induction L, auto)                  
next
  case (Record L LT)
    thus ?case by (induction LT, auto)
next
  case (Pattern p)
    from Pattern show ?case 
      proof (induction p)
        case (V x)
          thus ?case
            using find_None_iff[of "\<lambda>p. fst p = _" \<delta>]
                  prod.collapse
                  set_zip_leftD[of _ _ "fst_extract \<delta>" "snd_extract \<delta>"] 
                  zip_comp[of \<delta>]
            by force
      qed force
qed auto

lemma record_patterns_characterisation:
  "set (patterns (<|RCD L PL|>)) \<subseteq> S \<Longrightarrow> x \<in> set PL \<Longrightarrow> set(patterns (<|x|>)) \<subseteq> S"
sorry 

lemma fill_subsumption:
  "coherent_Subst \<delta> \<Longrightarrow> coherent_Subst \<delta>1 \<Longrightarrow> set(patterns t) \<subseteq> set (fst_extract \<delta>) \<Longrightarrow> set \<delta> \<subseteq> set \<delta>1 \<Longrightarrow> fill \<delta>1 t = fill \<delta> t"
proof (induction t)
 case (Tuple L)
    thus ?case
      by (induction L, auto)
next
  case (Record L LT)
    thus ?case by (induction LT, auto)
next
  case (Pattern p)
    thus ?case
      proof (induction p)
        case (V k)
          obtain v where 1:"find (\<lambda>p. fst p = k) \<delta> = Some (k, v)" "(k, v) \<in> set \<delta>"
            using inset_find_Some[of k \<delta>]
                  V(3)
            by auto
          hence "k \<in> set (fst_extract \<delta>1)"
            using zip_comp[of \<delta>1]
                  V(4)
                  set_zip_leftD[of k v "fst_extract \<delta>1" "snd_extract \<delta>1"]
            by auto
          hence "find (\<lambda>p. fst p = k) \<delta>1 = Some (k, v)"
            using inset_find_Some[of k \<delta>1]
                  1 V coherent_imp_unique_index subsetCE 
            by blast
          with 1 show ?case
            by auto
      next
        case (RCD L PL)
          have 1:"set (list_iter op @ \<emptyset> (map Pvars PL)) \<inter> set (fst_extract \<delta>1) = {} \<Longrightarrow> set (list_iter op @ \<emptyset> (map Pvars PL)) \<inter> set (fst_extract \<delta>) = {}"
            using incl_fst RCD(5)
            by blast  
          have 21:"set (list_iter op @ \<emptyset> (map Pvars PL)) \<inter> set (fst_extract \<delta>1) \<noteq> {} \<Longrightarrow>
                  set (list_iter op @ \<emptyset> (map Pvars PL)) \<inter> set (fst_extract \<delta>) \<noteq> {}"
            using RCD(4,5)
            by auto
          have "set (list_iter op @ \<emptyset> (map Pvars PL)) \<inter> set (fst_extract \<delta>1) \<noteq> {} \<Longrightarrow>
              (set (list_iter op @ \<emptyset> (map Pvars PL)) \<inter> set (fst_extract \<delta>) \<noteq> {} \<longrightarrow> (\<forall>x\<in>set PL. p_instantiate \<delta>1 x = p_instantiate \<delta> x))"
            using RCD(1)[OF _ RCD(2,3) _ RCD(5)]
                  record_patterns_characterisation[OF RCD(4) _]
            by auto                                      
          with 1 21 show ?case by auto
      qed 
qed (auto)


lemma fill_keep_value:
  "is_value_L v \<Longrightarrow> is_value_L (fill \<delta> v)"
by(induction v rule: is_value_L.induct, auto intro: "is_value_L.intros" )

lemma match_to_filled_match:
  "Lmatch p t1 \<delta>' \<Longrightarrow> Lmatch p (fill \<delta> t1) (update_snd (fill \<delta>) \<delta>')"
proof (induction p t1 \<delta>' rule: "Lmatch.induct")
  case (M_Var v n)
    show ?case
      using fill_keep_value[OF M_Var]
            "Lmatch.intros"(1)
      by auto
next
  case (M_RCD L LT F PL)
    thus ?case
      using M_RCD(2,3,4,5,7)
            "Lmatch.intros"(2)[OF M_RCD(1),of "map (fill \<delta>) LT" "map (update_snd (fill \<delta>)) F" PL]
            fill_keep_value
            list_it_map_app_map[of "fill \<delta>" F]
      by fastforce
qed

lemma has_type_filled:
  assumes coherence: "coherent_Subst (\<delta>@\<delta>1)" and
          well_typed: "\<Gamma>\<turnstile> \<lparr>t|;|(\<delta>@\<delta>1)\<rparr> |:| A"
  shows "\<Gamma> \<turnstile> \<lparr>fill \<delta> t|;|\<delta>1\<rparr> |:| A"
using assms(2,1) 
proof (induction \<Gamma> t "\<delta>@\<delta>1" A arbitrary: \<delta> \<delta>1 rule: has_type_L.induct)
  case (has_type_LAbs \<Gamma> A t2 B)
    show ?case
      using has_type_LAbs
            weakening[of \<Gamma> _ _ _"\<Gamma>|,|A"] "has_type_L.intros"
      by force
next  
  case (has_type_Let x \<Gamma> t1 A t2 B)
    have "\<forall>i<length \<delta>1. x \<notin> FV (snd_extract \<delta>1 ! i)" 
      proof (rule allI, rule impI)
        fix i
        assume H: "i<length \<delta>1"
        hence "x \<notin> FV (snd_extract (\<delta> @ \<delta>1) ! (length \<delta>+i))"
          using has_type_Let(1)
          by force
        thus "x \<notin> FV (snd_extract \<delta>1 ! i)"
          using nth_append[of "snd_extract \<delta>" "snd_extract \<delta>1"]
                snd_extract_app[of \<delta> \<delta>1]
                H
          by fastforce
      qed
    thus ?case
      using has_type_Let
      by (fastforce intro!:has_type_L.intros)     
next
  case (has_type_ProjT i TL \<Gamma> t)
    show ?case
      using has_type_L.intros(15)[OF has_type_ProjT(1,2), of \<Gamma> "fill \<delta> t" \<delta>1]
            has_type_ProjT(4,5)
      by simp
next
  case (has_type_PatternVar \<Gamma> t A k)
    obtain j where H:"j<length (\<delta>@\<delta>1) \<and> (\<delta>@\<delta>1) ! j = (k,t) \<and> 
                      (\<forall>l<j. fst ((\<delta>@\<delta>1) ! l) \<noteq> k)"
      using coherent_imp_unique_index[OF "has_type_PatternVar"(4,3)]
            find_Some_iff[of "\<lambda>p. fst p = k" "\<delta>@\<delta>1"]
      by metis     
    have "k \<in> set (fst_extract \<delta>) \<longrightarrow> find (\<lambda>p. fst p = k) \<delta> = Some (\<delta> ! j)
            \<and> j < length \<delta> \<and> \<delta> ! j = (k,t)"       
      proof (rule impI)
        assume hyp:"k \<in> set (fst_extract \<delta>)" 
        obtain j1 where T:"fst_extract \<delta> ! j1 = k \<and> j1<length \<delta>"
          by (metis in_set_conv_nth hyp len_fst_extract)          
        hence 1:"j<length \<delta>"
          by (cases "j>j1", auto)
              (metis (no_types) T append_same_eq list_update_append1 list_update_id list_update_same_conv H)
        hence 2:"\<delta> ! j = (k,t)"
          using H nth_append[of "\<delta>" _ j]
                "has_type_PatternVar.prems"(1)
          by simp
        have "\<forall>l<j. fst (\<delta> ! l) \<noteq> k"
          using 1 H nth_append[of \<delta> \<delta>1 ] 
            by fastforce
        with 1 2 have "find (\<lambda>p. fst p = k) \<delta> = Some (\<delta> ! j)"
          using find_Some_iff[of "\<lambda>p. fst p = k" \<delta> "\<delta> ! j"]
                fst_conv
                coherent_imp_distinct[OF "has_type_PatternVar"(4)]
          by metis
        with 1 2 show "find (\<lambda>p. fst p = k) \<delta> = Some (\<delta> ! j)
            \<and> j < length \<delta> \<and> \<delta> ! j = (k,t)"
          by auto
      qed
    hence 1:"k \<in> set (fst_extract \<delta>) \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>(case find (\<lambda>p. fst p = k) \<delta> of None \<Rightarrow> <|V k|> | Some x \<Rightarrow> snd x)|;|\<delta>1\<rparr> |:| A"
      using has_type_PatternVar
            weakening
      by fastforce
    have 2:"k \<notin> set (fst_extract \<delta>) \<Longrightarrow> \<Gamma> \<turnstile> \<lparr><|V k|>|;|\<delta>1\<rparr> |:| A"
      proof -
        assume hyp : "k \<notin> set (fst_extract \<delta>)"
        hence "(k,t) \<notin> set \<delta>"
          using zip_comp[of \<delta>]
                set_zip_leftD
          by metis
        hence "(k,t)\<in> set \<delta>1"
          using has_type_PatternVar(3)
                set_append
          by force
        thus ?thesis
          using "has_type_L.intros"(18)[OF has_type_PatternVar(1)]
          by blast      
      qed
    have "k \<notin> set(fst_extract \<delta>) \<Longrightarrow> find (\<lambda>p. fst p = k) \<delta> = None"
      using find_None_iff[of "\<lambda>p. fst p = k" \<delta>]
            prod.collapse
            zip_comp[of \<delta>] set_zip_leftD
      by metis      
    with 1 2 show ?case
      by(cases "k\<in> set(fst_extract \<delta>)", auto)
next
  case (has_type_PatternRCD L PL TL \<Gamma>)
    show ?case
      using has_type_PatternRCD
        by (force intro!: "has_type_L.intros"(16))+
next
  case (has_type_LetPattern \<delta>' p t1 \<Gamma> t2 A)
    have incl_cases:"set (patterns t2) \<subseteq> set (fst_extract \<delta>) \<and> set (patterns t2) \<inter> set (fst_extract (\<delta>'@\<delta>1)) = {} \<or>
          set (patterns t2) \<subseteq> set (fst_extract \<delta>') \<and> set (patterns t2) \<inter> set (fst_extract (\<delta>@\<delta>1)) = {}\<or>
          set (patterns t2) \<subseteq> set (fst_extract \<delta>1) \<and> set (patterns t2) \<inter> set (fst_extract (\<delta>'@\<delta>)) = {}"
    sorry
    have snd_updt_coherent: "coherent_Subst (update_snd (fill \<delta>) \<delta>' @ \<delta>1)"
      proof -
        have "coherent_Subst (\<delta>'@\<delta>1)"
          using has_type_LetPattern(1)
                fst_extract_app[of \<delta>' \<delta>]
                distinct_append[of "fst_extract \<delta>'" "fst_extract \<delta>"]
                fst_extract_app[of "\<delta>'@\<delta>" \<delta>1]
                distinct_append[of "fst_extract (\<delta>'@\<delta>)" "fst_extract \<delta>1"]
                fst_extract_app[of \<delta>' \<delta>1]
                distinct_append[of "fst_extract \<delta>'" "fst_extract \<delta>1"]
          by auto
        thus ?thesis
          using fst_updt_snd_is_fst[of \<delta>' "fill \<delta>"]
                fst_extract_app
          by metis
      qed    
    
    show ?case 
      apply simp
      apply (cases "patterns t1 = []")
      apply (simp add: fill_only_incl[of t1])      
      apply (auto intro!: "has_type_L.intros"(20)[of \<delta>' \<delta>1 p t1 \<Gamma> "fill \<delta> t2"] simp del: fst_extract_app)
      using has_type_LetPattern(1)
            distinct_append[of "fst_extract \<delta>'" "fst_extract \<delta>1"]
            distinct_append[of "fst_extract \<delta>'" "fst_extract (\<delta>@\<delta>1)"]
            set_append
      apply auto[1]
      using has_type_LetPattern(2,3)
      apply force+
      using incl_cases
      apply auto[1]
      using fill_subsumption[of t2 \<delta> "\<delta>'@\<delta>"]
            has_type_LetPattern(5)[of "\<delta>'@\<delta>" \<delta>1]
            has_type_LetPattern(1)
            weakening[of \<Gamma> "fill \<delta> t2" \<delta>1 A \<Gamma> "\<delta>'@\<delta>1"]
      apply auto[1]
      using fill_only_incl[of t2 \<delta>]
            strengthening[OF has_type_LetPattern(4), of "\<delta>'"]
            weakening[of \<Gamma> "fill \<delta> t2" \<delta>' A \<Gamma> "\<delta>'@\<delta>1"]
            fst_extract_app[of \<delta> \<delta>1]
      apply force
      using fill_only_incl[of t2 "\<delta>'@\<delta>"]
            fill_only_incl[of t2 \<delta>]
            fst_extract_app[of \<delta>' \<delta>]
            has_type_LetPattern(5)[of "\<delta>'@\<delta>" \<delta>1]
            has_type_LetPattern(1)            
            weakening[of \<Gamma> t2 \<delta>1 A \<Gamma> "\<delta>'@\<delta>1"]
      apply force   
      apply (auto intro!: "has_type_L.intros"(20)[of "update_snd (fill \<delta>) \<delta>'" \<delta>1 p "fill \<delta> t1" \<Gamma> "fill \<delta> t2"])
      using snd_updt_coherent
            has_type_LetPattern(2)
      apply force+
      using match_to_filled_match[OF has_type_LetPattern(3)]
      apply auto[1]
      using has_type_LetPattern(5)[of \<delta>' "\<delta>@\<delta>1"]
            has_type_LetPattern 
sorry
qed (auto intro!:has_type_L.intros)
(*
lemma inversion:
  "\<Delta> |;| \<Gamma> \<turnstile> LTrue |:| R \<Longrightarrow> R = Bool"
  "\<Delta> |;| \<Gamma> \<turnstile> LFalse |:| R \<Longrightarrow> R = Bool"
  "\<Delta> |;| \<Gamma> \<turnstile> LIf t1 t2 t3 |:| R \<Longrightarrow> \<Delta> |;| \<Gamma> \<turnstile> t1 |:| Bool \<and> \<Delta> |;| \<Gamma> \<turnstile> t2 |:| R \<and> \<Delta> |;| \<Gamma> \<turnstile> t3 |:| R"
  "\<Delta> |;| \<Gamma> \<turnstile> LVar x |:| R \<Longrightarrow> (x, R) |\<in>| \<Gamma>"
  "\<Delta> |;| \<Gamma> \<turnstile> LAbs T1 t2 |:| R \<Longrightarrow> \<exists>R2. R = T1 \<rightarrow> R2 \<and> \<Delta> |;| \<Gamma> |,| T1 \<turnstile> t2 |:| R2"
  "\<Delta> |;| \<Gamma> \<turnstile> LApp t1 t2 |:| R \<Longrightarrow> \<exists>T11. \<Delta> |;| \<Gamma> \<turnstile> t1 |:| T11 \<rightarrow> R \<and> \<Delta> |;| \<Gamma> \<turnstile> t2 |:| T11"
  "\<Delta> |;| \<Gamma> \<turnstile> unit |:| R \<Longrightarrow> R = Unit"
  "\<Delta> |;| \<Gamma> \<turnstile> Seq t1 t2 |:| R \<Longrightarrow> \<exists>A. R = A \<and> \<Delta> |;| \<Gamma> \<turnstile> t2 |:| A \<and> \<Delta> |;| \<Gamma> \<turnstile> t1 |:| Unit"
  "\<Delta> |;| \<Gamma> \<turnstile> t as A |:| R \<Longrightarrow> R = A"
  "\<Delta> |;| \<Gamma> \<turnstile> Let var x := t in t1 |:| R \<Longrightarrow> \<exists>A B. R = B \<and> \<Delta> |;| \<Gamma> \<turnstile> t |:| A \<and> \<Delta> |;| (replace x A \<Gamma>) \<turnstile> t1 |:| B"
  "\<Delta> |;| \<Gamma> \<turnstile> \<lbrace>t1,t2\<rbrace> |:| R \<Longrightarrow> \<exists>A B. \<Delta> |;| \<Gamma> \<turnstile> t1 |:| A \<and> \<Delta> |;| \<Gamma> \<turnstile> t2 |:| B \<and> R = A |\<times>| B"
  "\<Delta> |;| \<Gamma> \<turnstile> \<pi>1 t |:| R \<Longrightarrow> \<exists>A B. \<Delta> |;| \<Gamma> \<turnstile> t |:| A |\<times>| B \<and> R = A"
  "\<Delta> |;| \<Gamma> \<turnstile> \<pi>2 t |:| R \<Longrightarrow> \<exists>A B. \<Delta> |;| \<Gamma> \<turnstile> t |:| A |\<times>| B \<and> R = B"
  "\<Delta> |;| \<Gamma> \<turnstile> Tuple L |:| R \<Longrightarrow> \<exists>TL. length L = length TL \<and> (\<forall>i. 0\<le>i \<longrightarrow> i< length L \<longrightarrow> \<Delta> |;| \<Gamma> \<turnstile> (L ! i) |:| (TL ! i)) \<and> R = \<lparr>TL\<rparr>"
  "\<Delta> |;| \<Gamma> \<turnstile> (\<Pi> i t) |:| R \<Longrightarrow> \<exists>TL. R = (TL ! (i-1)) \<and> \<Delta> |;| \<Gamma> \<turnstile> t |:| \<lparr>TL\<rparr> \<and> 1\<le>i \<and> i\<le> length TL"
  "\<Delta> |;| \<Gamma> \<turnstile> (Record L1 LT) |:| R \<Longrightarrow> \<exists>TL. R = \<lparr>L1|:|TL\<rparr> \<and> length TL = length LT \<and> length L1 = length LT \<and> distinct L1 \<and> 
                                    (\<forall>i. 0\<le>i \<longrightarrow> i< length LT \<longrightarrow> \<Delta> |;| \<Gamma> \<turnstile> (LT ! i) |:| (TL ! i)) " 
  "\<Delta> |;| \<Gamma> \<turnstile> (ProjR l t) |:| R \<Longrightarrow>\<exists>A m L TL. R = A \<and> \<Delta> |;| \<Gamma> \<turnstile> t |:| \<lparr>L|:|TL\<rparr> \<and> index L l = m \<and> TL ! m = A \<and> distinct L \<and> length L = length TL
                              \<and> l \<in> set L"
proof (auto elim: has_type_L.cases has_type_ProjTE)
  assume H:"\<Delta> |;| \<Gamma> \<turnstile> Let var x := t in t1 |:| R"
  show "\<exists>A. (length \<Gamma> \<le> x \<longrightarrow> \<Delta> |;| \<Gamma> \<turnstile> t |:| A \<and> \<Delta> |;| \<Gamma> \<turnstile> t1 |:| R) \<and> (\<not> length \<Gamma> \<le> x \<longrightarrow> \<Delta> |;| \<Gamma> \<turnstile> t |:| A \<and> \<Delta> |;| (take x \<Gamma> @ drop (Suc x) \<Gamma> |,| A) \<turnstile> t1 |:| R)"
    using H has_type_LetE
    by (cases "x\<ge> length \<Gamma>", fastforce+)
qed (metis has_type_ProjRE)


lemma canonical_forms:
  "is_value_L v \<Longrightarrow> \<Delta> |;| \<Gamma> \<turnstile> v |:| Bool \<Longrightarrow> v = LTrue \<or> v = LFalse"
  "is_value_L v \<Longrightarrow> \<Delta> |;| \<Gamma> \<turnstile> v |:| T1 \<rightarrow> T2 \<Longrightarrow> \<exists>t. v = LAbs T1 t \<and> patterns t = []"
  "is_value_L v \<Longrightarrow> \<Delta> |;| \<Gamma> \<turnstile> v |:| Unit \<Longrightarrow> v = unit"
  "is_value_L v \<Longrightarrow> \<Delta> |;| \<Gamma> \<turnstile> v |:| A |\<times>| B \<Longrightarrow> \<exists>v1 v2. is_value_L v1 \<and> is_value_L v2 \<and> v= \<lbrace>v1,v2\<rbrace>"
  "is_value_L v \<Longrightarrow> \<Delta> |;| \<Gamma> \<turnstile> v |:| \<lparr>TL\<rparr> \<Longrightarrow> \<exists>L. is_value_L (Tuple L) \<and> v = Tuple L"
  "is_value_L v \<Longrightarrow> \<Delta> |;| \<Gamma> \<turnstile> v |:| \<lparr>L|:|TL\<rparr> \<Longrightarrow> \<exists>L LT. is_value_L (Record L LT) \<and> v = (Record L LT)" 
by (auto elim: has_type_L.cases is_value_L.cases)

lemma[simp]: "nat (int x + 1) = Suc x" by simp
      
lemma weakening:
  "\<Delta> |;| \<Gamma> \<turnstile> t |:| A \<Longrightarrow> n \<le> length \<Gamma> \<Longrightarrow> \<Delta> |;| insert_nth n S \<Gamma> \<turnstile> shift_L 1 n t |:| A"
proof (induction \<Delta> \<Gamma> t A arbitrary: n rule: has_type_L.induct)
  case (has_type_LAbs \<Delta> \<Gamma> T1 t2 T2)
    from has_type_LAbs.prems has_type_LAbs.hyps
      has_type_LAbs.IH[where n="Suc n"] show ?case
      by (auto intro: has_type_L.intros(5))
next
  case (has_type_Let \<Delta> \<Gamma> t A x t1 B)
    show ?case 
      proof (cases "x\<ge> n")
        assume H:"x\<ge>n"
        have 1:"\<Delta> |;| insert_nth n S \<Gamma> \<turnstile> shift_L 1 n t |:| A"
          using has_type_Let(3)[OF has_type_Let(5)]
          by blast
   
        have "\<Delta> |;| (replace (Suc x) A (insert_nth n S \<Gamma>)) \<turnstile> shift_L 1 n t1 |:| B"
          using has_type_Let(4,5) H 
                rep_ins[of n x \<Gamma> S A,OF H has_type_Let(5)]
                replace_inv_length[of x A \<Gamma>]
          by metis
        with 1 show "\<Delta> |;| insert_nth n S \<Gamma> \<turnstile> shift_L 1 n (Let var x := t in t1) |:| B"
          using "has_type_L.intros"(10) H
          by auto
      next
        assume H: "\<not> n \<le> x"
        have a:"\<Delta> |;| replace x A (take n \<Gamma> @ drop n \<Gamma> |,| S) \<turnstile> shift_L 1 n t1 |:| B"
          using has_type_Let(4)[of n] has_type_Let(5) H
                rep_ins2[of x n \<Gamma> S A]
                replace_inv_length[of n A \<Gamma>]
          by simp
        show "\<Delta> |;| insert_nth n S \<Gamma> \<turnstile> shift_L 1 n (Let var x := t in t1) |:| B"
          using has_type_Let(3,5) 
          by (simp add: H, auto intro: a  "has_type_L.intros"(10) )
      qed    
next
  case (has_type_ProjT i TL \<Delta> \<Gamma> t)
    show ?case
      using "has_type_L.intros"(15)[OF "has_type_ProjT"(1,2)]
            "has_type_ProjT"(4)[OF "has_type_ProjT"(5)]
      by force
next
  case (has_type_LetPattern p t1 \<delta> TL \<Delta> \<Gamma> t2 A)
    thus ?case sorry
qed (auto simp: nth_append min_def intro: has_type_L.intros)


*)

end
