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

fun bind_pvars :: "lterm \<Rightarrow> nat set" where
"bind_pvars (Let pattern p:= t1 in t2)      = set(Pvars p) \<union> bind_pvars t1 \<union> bind_pvars t2" |
"bind_pvars (LIf c t1 t2)               = bind_pvars c \<union> bind_pvars t1 \<union> bind_pvars t2" |
"bind_pvars (LAbs A t1)                 = bind_pvars t1" |
"bind_pvars (LApp t1 t2)                = bind_pvars t1 \<union> bind_pvars t2" |
"bind_pvars (Seq t1 t2)                 = bind_pvars t1 \<union> bind_pvars t2" |
"bind_pvars (t1 as A)                   = bind_pvars t1" |
"bind_pvars (\<lbrace>t1,t2\<rbrace>)                   = bind_pvars t1 \<union> bind_pvars t2" |
"bind_pvars (Tuple L)                   = (UN l : set (map (bind_pvars) L). l)" |
"bind_pvars (Record L LT)               = (UN l : set (map (bind_pvars) LT). l)" |
"bind_pvars (\<pi>1 t)                      = bind_pvars t" |
"bind_pvars (\<pi>2 t)                      = bind_pvars t" |
"bind_pvars (\<Pi> i t)                     = bind_pvars t" |
"bind_pvars (ProjR l t)                 = bind_pvars t" |
"bind_pvars (Let var x := t1 in t2) = bind_pvars t1 \<union> bind_pvars t2" |
"bind_pvars t                           = {}"

fun intern_patterns:: "lterm \<Rightarrow> nat list" where
"intern_patterns (LIf c t1 t2)               = intern_patterns c @ intern_patterns t1 @ intern_patterns t2" |
"intern_patterns (LAbs A t1)                 = intern_patterns t1" |
"intern_patterns (LApp t1 t2)                = intern_patterns t1 @ intern_patterns t2" |
"intern_patterns (Seq t1 t2)                 = intern_patterns t1 @ intern_patterns t2" |
"intern_patterns (t1 as A)                   = intern_patterns t1" |
"intern_patterns (Let var x := t1 in t2)     = intern_patterns t1 @ intern_patterns t2" |
"intern_patterns (\<lbrace>t1,t2\<rbrace>)                   = intern_patterns t1 @ intern_patterns t2" |
"intern_patterns (Tuple L)                   = list_iter op @ [] (map (intern_patterns) L)" |
"intern_patterns (Record L LT)               = list_iter op @ [] (map (intern_patterns) LT)" |
"intern_patterns (\<pi>1 t)                      = intern_patterns t" |
"intern_patterns (\<pi>2 t)                      = intern_patterns t" |
"intern_patterns (\<Pi> i t)                     = intern_patterns t" |
"intern_patterns (ProjR l t)                 = intern_patterns t" |
"intern_patterns (Let pattern p := t1 in t2) = (Pvars p) @ (intern_patterns t1) @(intern_patterns t2)" |
"intern_patterns t = []"


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
    "\<Gamma> \<turnstile> \<lparr>t1|;|\<delta>\<rparr> |:| A \<Longrightarrow> (replace x A \<Gamma>) \<turnstile> \<lparr>t2|;| \<delta>\<rparr> |:| B \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Let var x := t1 in t2|;|\<delta>\<rparr> |:| B" |
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
    "\<Gamma> \<turnstile> \<lparr>t|;|\<emptyset>\<rparr> |:| A \<Longrightarrow> bind_pvars t = {} \<Longrightarrow> (k,t)\<in> set \<delta> \<Longrightarrow> \<Gamma> \<turnstile> \<lparr><|V k|>|;|\<delta>\<rparr> |:| A" |
  has_type_PatternRCD:
    "L\<noteq>[] \<Longrightarrow> distinct L \<Longrightarrow> length PL = length TL \<Longrightarrow> length L = length PL \<Longrightarrow> (\<And>i. i< length PL \<Longrightarrow> \<Gamma> \<turnstile> \<lparr><|PL ! i|>|;|\<delta>\<rparr> |:| (TL ! i))
      \<Longrightarrow> \<Gamma> \<turnstile> \<lparr><|RCD L PL|>|;|\<delta>\<rparr> |:| \<lparr>L|:|TL\<rparr>" |
  has_type_LetPattern:
    "coherent_Subst (\<delta>@\<delta>1) \<Longrightarrow> coherent p \<Longrightarrow> Lmatch p t1 \<delta>  \<Longrightarrow> set (patterns t1) \<subseteq> set (fst_extract \<delta>1) \<Longrightarrow>
     \<Gamma> \<turnstile> \<lparr>t2|;|(update_snd (fill \<delta>1) \<delta>@\<delta>1)\<rparr> |:| A \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Let pattern p := t1 in t2|;|\<delta>1\<rparr> |:| A" 


  
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

lemma subset_coherent:
  "(\<forall>x\<in> set \<delta>1. count_list \<delta>1 x = count_list \<delta> x) \<Longrightarrow> set \<delta>1 \<subseteq> set \<delta> \<Longrightarrow> coherent_Subst \<delta> \<Longrightarrow> coherent_Subst \<delta>1"
proof -
  assume hyps: "\<forall>x\<in> set \<delta>1. count_list \<delta>1 x = count_list \<delta> x"  "set \<delta>1 \<subseteq> set \<delta>" "coherent_Subst \<delta>"
  show ?thesis
    proof (simp add: distinct_conv_nth[of "fst_extract \<delta>1"], rule+)
      fix i j
      assume hyps2: "i < length \<delta>1" "j < length \<delta>1" " i \<noteq> j" "fst(\<delta>1 ! i) = fst(\<delta>1 ! j)"
      obtain i1 j1 where H:"fst(\<delta>!i1) = fst(\<delta>1!i)" "i1 <length \<delta>" "j1 < length \<delta>" "fst(\<delta>!j1) = fst(\<delta>1!j)"
        using same_count_set_ex_commun_index[OF hyps(1,2)] hyps2
        sorry
      have "j1 \<noteq> i1" sorry
      with H show "False"
        using hyps(3)
              distinct_conv_nth[of "fst_extract \<delta>"] hyps2(4)
        by fastforce
      qed
qed
  
lemma record_patterns_characterisation:
  "set (patterns (<|RCD L PL|>)) \<subseteq> S \<Longrightarrow> x \<in> set PL \<Longrightarrow> set(patterns (<|x|>)) \<subseteq> S"
by (induction PL arbitrary: S x, auto) 

lemma Lmatch_pvars:
  "Lmatch p v \<delta> \<Longrightarrow> set(fst_extract \<delta>) = set(Pvars p)"
proof(induction rule: Lmatch.induct)
  case (M_Var v n)
    thus ?case by auto
next
  case (M_RCD L LT F PL)
    show ?case
      using M_RCD(3,4,6,7)
      proof (induction PL arbitrary: F LT)
        case Nil
          thus ?case by auto
      next
        case (Cons p PL1)
          from Cons(2) obtain f F1 where A:"F = f#F1"
            using length_Suc_conv
            by metis
          from Cons(3) obtain lt LT1 where C:"LT = lt#LT1"
            using length_Suc_conv
            by metis
          have B:"set (fst_extract f) = set (Pvars p)"
            using Cons(5)[of 0]
                  A
            by auto
          have "set (fst_extract (list_iter op @ \<emptyset> F1)) = set (list_iter op @ \<emptyset> (map Pvars PL1))"
            using Cons(1)[of F1 LT1]
                  Cons(2,3) A C
                  Cons(4,5)[of "Suc _"]
            by force
          with B show ?case
            by (simp add:A)
      qed
qed 

lemma lmatch_patterns:
  "Lmatch p t \<delta> \<Longrightarrow> i<length \<delta> \<Longrightarrow> set(patterns(snd(\<delta>!i))) \<subseteq> set(patterns t)"
proof (induction arbitrary: i rule:Lmatch.induct)
  case (M_RCD L LT F PL)
    obtain j k where "list_iter op @ \<emptyset> F ! i = F ! j ! k"
                       "k < length (F ! j)" "j < length F"
      using nth_list_it_app[of F i]
      by blast
    thus ?case
      using M_RCD(7)[of j k] M_RCD(3,4)
            set_conv_nth[of LT]
      by auto
qed auto

lemma fill_only_incl:
  "set(intern_patterns t) \<inter> set (fst_extract \<delta>) = {} \<Longrightarrow> set(patterns t) \<inter> set (fst_extract \<delta>) = {} \<Longrightarrow> fill \<delta> t = t"
proof (induction t)
  case (Tuple L)
    have "\<forall>l\<in>set L. (set \<circ> intern_patterns) l \<inter> set (fst_extract \<delta>) = {}" "\<forall>l\<in>set L. (set \<circ> patterns) l \<inter> set (fst_extract \<delta>) = {}"
      using UN_int_empty[of L "set \<circ> intern_patterns" "fst_extract \<delta>"]
            UN_int_empty[of L "set \<circ> patterns" "fst_extract \<delta>"]
            Tuple(2,3)
      by auto
    with Tuple(1) show ?case
      by (induction L, auto)                  
next
  case (Record L LT)    
    have "\<forall>l\<in>set LT. (set \<circ> intern_patterns) l \<inter> set (fst_extract \<delta>) = {}" "\<forall>l\<in>set LT. (set \<circ> patterns) l \<inter> set (fst_extract \<delta>) = {}"
      using UN_int_empty[of LT "set \<circ> intern_patterns" "fst_extract \<delta>"]
            UN_int_empty[of LT "set \<circ> patterns" "fst_extract \<delta>"]
            Record(2,3)
      by auto
    with Record(1) show ?case by (induction LT, auto)
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

lemma fill_subsumption:
  "coherent_Subst \<delta> \<Longrightarrow> coherent_Subst \<delta>1 \<Longrightarrow> set(patterns t) \<subseteq> set (fst_extract \<delta>) \<Longrightarrow> 
    set (intern_patterns t) \<inter> set (fst_extract \<delta>1) = {} \<Longrightarrow> set \<delta> \<subseteq> set \<delta>1 \<Longrightarrow> fill \<delta>1 t = fill \<delta> t"
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
                  V(5)
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
            using incl_fst RCD(6)
            by blast  
          have 21:"set (list_iter op @ \<emptyset> (map Pvars PL)) \<inter> set (fst_extract \<delta>1) \<noteq> {} \<Longrightarrow>
                  set (list_iter op @ \<emptyset> (map Pvars PL)) \<inter> set (fst_extract \<delta>) \<noteq> {}"
            using RCD(4,5)
            by auto
          have "set (list_iter op @ \<emptyset> (map Pvars PL)) \<inter> set (fst_extract \<delta>1) \<noteq> {} \<Longrightarrow>
              (set (list_iter op @ \<emptyset> (map Pvars PL)) \<inter> set (fst_extract \<delta>) \<noteq> {} \<longrightarrow> (\<forall>x\<in>set PL. p_instantiate \<delta>1 x = p_instantiate \<delta> x))"
            using RCD(1)[OF _ RCD(2,3) _ _ RCD(6)] RCD(5)
                  record_patterns_characterisation[OF RCD(4) _]
            by auto                                      
          with 1 21 show ?case by auto
      qed 
next
  case (LetP p t1 t2)
    thus ?case sorry
qed auto

lemma weakening :
  "\<Gamma>' \<turnstile> \<lparr>t|;|\<delta>\<rparr> |:| A \<Longrightarrow> (\<exists>P. \<Gamma>'@P = \<Gamma>) \<Longrightarrow> coherent_Subst \<delta>1 \<Longrightarrow> (\<exists>L. \<delta>1 = \<delta>@L \<and> bind_pvars t \<inter> set (fst_extract L) = {}) \<Longrightarrow> 
     \<Gamma> \<turnstile> \<lparr>t|;|(\<delta>1)\<rparr> |:| A"
proof(induction arbitrary: \<delta>1 \<Gamma> rule:has_type_L.induct)
  case (has_type_LVar x A \<Gamma>1 \<delta>)
    show ?case
      using has_type_LVar(1,2)
            nth_append[of \<Gamma>1 _ x]
      by (auto intro: has_type_L.intros)
next
  case (has_type_LIf \<Gamma>1 t1 \<delta> t2 A t3)
    obtain L where P:"\<delta>1 = \<delta> @ L" "bind_pvars (LIf t1 t2 t3) \<inter> set (fst_extract L) = {}"
      using has_type_LIf(9)
      by blast
    show ?case
      using "has_type_L.intros"(3)[of \<Gamma> t1 \<delta>1 t2 A t3]
            has_type_LIf(4,5,6)[OF has_type_LIf(7-8)]
            P
      by auto            
next
  case (has_type_ProjT i TL \<Gamma>1 t \<delta>)
    show ?case 
      using has_type_ProjT
            "has_type_L.intros"(15)[OF has_type_ProjT(1,2)]
      by auto
next
  case (has_type_LApp \<Gamma>1 t1 \<delta> A B t2)
    show ?case
      using has_type_LApp(3)[OF has_type_LApp(5,6)]
            has_type_L.intros(6)[of \<Gamma> t1 \<delta>1 A B t2]
            has_type_LApp(4)[OF has_type_LApp(5,6)]
            has_type_LApp(7)
      by auto
next
  case (has_type_LSeq \<Gamma>1 t1 \<delta> t2 A)
    from this(7) 
      obtain L where H:" \<delta>1 = \<delta> @ L"
                       "bind_pvars t1 \<inter> set (fst_extract L) = {}"
                       "bind_pvars t2 \<inter> set (fst_extract L) = {}"
      by auto
    thus ?case
      using "has_type_L.intros"(8)
            has_type_LSeq(3,4)[OF has_type_LSeq(5-6)]
      by blast
next
  case (has_type_Pair \<Gamma>1 t1 \<delta> A t2 B)
    from this(7) 
      obtain L where H:" \<delta>1 = \<delta> @ L"
                       "bind_pvars t1 \<inter> set (fst_extract L) = {}"
                       "bind_pvars t2 \<inter> set (fst_extract L) = {}"
      by auto
    thus ?case
      using "has_type_L.intros"(11)
            has_type_Pair(3,4)[OF has_type_Pair(5-6)]
      by blast
next
  case(has_type_Tuple L TL \<Gamma>1 \<delta>)
    show ?case
      using has_type_Tuple(4)[OF _ _ has_type_Tuple(5,6)]
            has_type_Tuple(7)
            "has_type_L.intros"(14)[OF has_type_Tuple(1,2), of \<Gamma> \<delta>1]
      by fastforce
next
  case (has_type_RCD L LT TL \<Gamma>1 \<delta>)
      show ?case
      using has_type_RCD(6)[OF _ has_type_RCD(7,8)]
            has_type_RCD(9)
            "has_type_L.intros"(16)[OF has_type_RCD(1-4), of \<Gamma> \<delta>1]
      by fastforce
next
  case (has_type_PatternVar \<Gamma>1 t A k \<delta>)
    show ?case
      using has_type_PatternVar(4)[OF has_type_PatternVar(5), of \<emptyset>]
            has_type_PatternVar(2,3,7)
      by (auto intro: "has_type_L.intros")
next
  case (has_type_Let \<Gamma>1 t1 \<delta> A x t2 B)
    have 1:"\<exists>P. replace x A \<Gamma>1 @ P = replace x A \<Gamma>"
      using has_type_Let(5)
      by (cases "x<length \<Gamma>1", auto)                    
    show ?case 
     using has_type_Let(3)[OF has_type_Let(5,6)]
           has_type_Let(4)[OF 1 has_type_Let(6)]
           has_type_Let(7)
           "has_type_L.intros"(10)[of \<Gamma> t1 \<delta>1 A x t2 B]
     by fastforce
next
  case (has_type_LetPattern \<delta> \<delta>2 p t1 \<Gamma>1 t2 A)
    have 1:"coherent_Subst (\<delta> @ \<delta>1)" 
      proof -
        obtain L where A:"\<delta>1 = \<delta>2 @ L" "bind_pvars (Let pattern p := t1 in t2) \<inter> set (fst_extract L) = {}"
          using has_type_LetPattern(9)
          by blast
        have "set(fst_extract \<delta>) \<inter> (set(fst_extract \<delta>2) \<union> set(fst_extract L)) = {}"
          using A has_type_LetPattern(1)
                Lmatch_pvars[OF has_type_LetPattern(3)]
          by auto
        thus ?thesis
          using A(1) has_type_LetPattern(1,8)
          by auto
      qed      
    hence 2:"\<exists>L. update_snd (fill \<delta>1) \<delta> @ \<delta>1 = (update_snd (fill \<delta>2) \<delta> @ \<delta>2) @ L \<and> bind_pvars t2 \<inter> set (fst_extract L) = {}"
      proof -
        obtain L where A:"\<delta>1 = \<delta>2 @ L" "bind_pvars (Let pattern p:=t1 in t2) \<inter> set (fst_extract L) = {}"
          using has_type_LetPattern(9)
          by blast
        hence C:"\<forall>i<length \<delta>. fill \<delta>1 (snd (\<delta> ! i)) = fill \<delta>2 (snd (\<delta> ! i))"
          using lmatch_patterns[OF has_type_LetPattern(3)]
                fill_subsumption[of \<delta>2 "\<delta>2@L" "snd(\<delta>!_)"]
                has_type_LetPattern(8)
                has_type_LetPattern(4)
          sorry
        show ?thesis
          using update_snd_rewrite_fun[OF C]
                A 
          by auto
      qed
    have 3: "set (patterns t1) \<subseteq> set (fst_extract \<delta>1)"
      using has_type_LetPattern(4,9)
            incl_fst[of \<delta>2 \<delta>1]
      by force
    show ?case
      using has_type_LetPattern(6)[OF has_type_LetPattern(7), of "update_snd (fill \<delta>1) \<delta> @ \<delta>1"]
            2 has_type_L.intros(20)[OF 1 has_type_LetPattern(2-3) 3,of \<Gamma> t2 A] 
            1
      by auto
qed (auto intro: has_type_L.intros)


lemma strengthening:
  "\<Gamma> \<turnstile> \<lparr>t|;|\<delta>\<rparr> |:| A \<Longrightarrow> coherent_Subst \<delta> \<Longrightarrow> \<forall>x\<in> set \<delta>1. count_list \<delta>1 x = count_list \<delta> x \<Longrightarrow>  set \<delta>1 \<subseteq> set \<delta>  \<Longrightarrow> set (patterns t) \<subseteq> set(fst_extract \<delta>1) \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t|;|\<delta>1\<rparr> |:| A"
proof(induction arbitrary: \<delta>1 rule:has_type_L.induct)
  case(has_type_LApp \<Gamma> t1 \<delta> A B t2)
    show ?case
      using has_type_LApp(3,4)[OF has_type_LApp(5,6)]
            has_type_LApp(7,8)
            "has_type_L.intros"(6)[of \<Gamma> t1 \<delta>1 A B t2]
      by auto
next
  case (has_type_Tuple L LT \<Gamma> \<delta>)
    show ?case
      using has_type_Tuple(4)[OF _ _ has_type_Tuple(5,6)]
            has_type_Tuple(7,8)
            "has_type_L.intros"(14)[OF has_type_Tuple(1,2), of \<Gamma> \<delta>1]
      by fastforce
next
  case (has_type_ProjT i TL \<Gamma> t \<delta>)
    show ?case
      using "has_type_L.intros"(15)[OF has_type_ProjT(1,2),of \<Gamma> t \<delta>1 ]
            has_type_ProjT(4)[OF has_type_ProjT(5,6)]
            has_type_ProjT(7,8)
      by fastforce
next
  case (has_type_RCD L LT TL \<Gamma> \<delta>)
    show ?case 
      using has_type_L.intros(16)[OF has_type_RCD(1-4), of \<Gamma> \<delta>1]
            has_type_RCD(6)[OF _ has_type_RCD(7,8)]
            has_type_RCD(9,10)
      by fastforce
next
  case (has_type_PatternVar \<Gamma> t A k \<delta>)
    have 1:"(k, t) \<in> set \<delta>1"
      proof -
        obtain t' where H1:"(k,t') \<in> set \<delta>1"
          using has_type_PatternVar(7,8)
                inset_find_Some
          by fastforce
        have "t\<noteq>t' \<Longrightarrow> False"
          using coherent_Subst_char[OF has_type_PatternVar(5,3), of "(k,t')"]
                has_type_PatternVar(6,7) H1
          by auto
        thus ?thesis
          using H1
          by (cases "t=t'", auto)
      qed    
    show ?case
      using has_type_PatternVar(1,2) 1
      by (auto intro: has_type_L.intros)  
next
  case (has_type_PatternRCD L PL TL \<Gamma> \<delta>)
    show ?case 
      using has_type_PatternRCD(6)[OF _ has_type_PatternRCD(7,8)]
            has_type_PatternRCD(9,10)
            has_type_L.intros(19)[OF has_type_PatternRCD(1-4), of \<Gamma> \<delta>1]
      by fastforce
next
  case (has_type_Let \<Gamma> t1 \<delta> A x t2 B)
    show ?case 
      using has_type_Let(3)[OF has_type_Let(5,6)]
            has_type_Let(7,8)
            has_type_Let(4)[OF has_type_Let(5,6)]
      by (auto intro: "has_type_L.intros")
next
  case (has_type_LetPattern \<delta> \<delta>2 p t1 \<Gamma> t2 A)
    have 1:"coherent_Subst (\<delta> @ \<delta>1)"
      using has_type_LetPattern(1)
            incl_fst[OF has_type_LetPattern(9)]            
            subset_coherent[OF has_type_LetPattern(8,9)]
            distinct_fst_imp_count_1[of \<delta>2]
      by auto        
    have 21:" update_snd (fill \<delta>1) \<delta> = update_snd (fill \<delta>2) \<delta>"
      proof -
         have C:"\<forall>i<length \<delta>. fill \<delta>1 (snd (\<delta> ! i)) = fill \<delta>2 (snd (\<delta> ! i))"
          using lmatch_patterns[OF has_type_LetPattern(3)]
                fill_subsumption[of \<delta>1 "\<delta>2" "snd(\<delta>!_)"]
                has_type_LetPattern(7-10)
                subset_coherent[OF has_type_LetPattern(8)] 
          sorry     
        show ?thesis
          using update_snd_rewrite_fun[OF C]  
          by auto
      qed
    have "\<forall>x\<in>set (update_snd (fill \<delta>1) \<delta> @ \<delta>1). count_list (update_snd (fill \<delta>1) \<delta> @ \<delta>1) x = count_list (update_snd (fill \<delta>2) \<delta> @ \<delta>2) x"
      proof (simp add: 21, auto simp: has_type_LetPattern(8))
        fix a b
        assume hyp: "(a, b) \<in> set (update_snd (fill \<delta>2) \<delta>)" 
        have "a \<notin> set (fst_extract \<delta>1) \<union> set (fst_extract \<delta>2)"
          using 1 set_zip_leftD[of a b "fst_extract \<delta>"] hyp
                zip_comp[of "update_snd (fill \<delta>2) \<delta>"]
                has_type_LetPattern(1) 
          by auto 
        hence "(a,b) \<notin> set \<delta>1 \<union> set \<delta>2"
          proof -
            have "a \<notin> set (fst_extract \<delta>2)"
              using \<open>a \<notin> set (fst_extract \<delta>1) \<union> set (fst_extract \<delta>2)\<close> by fastforce
            then have "(a, b) \<notin> set (zip (fst_extract \<delta>2) (snd_extract \<delta>2))"
              by (meson in_set_zipE)
            then show ?thesis
              using zip_comp[of \<delta>2] has_type_LetPattern.prems(3) by auto
          qed
        thus "count_list \<delta>1 (a, b) = count_list \<delta>2 (a, b)" 
          using count_notin[of "(a,b)"]
          by auto
      qed
    with 21 have 2: "\<Gamma> \<turnstile> \<lparr>t2|;|(update_snd (fill \<delta>1) \<delta> @ \<delta>1)\<rparr> |:| A" 
      using has_type_LetPattern(6)[of  "update_snd (fill \<delta>1) \<delta> @ \<delta>1" ]  
            has_type_LetPattern(1,9,10) lmatch_patterns[OF has_type_LetPattern(3)]
      sorry
    show ?case
      using has_type_LetPattern(9,10)
            has_type_L.intros(20)[OF 1 has_type_LetPattern(2,3) _ 2]
      by auto    
qed (auto intro: has_type_L.intros)


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
      using M_RCD(2-7)
            "Lmatch.intros"(2)[OF M_RCD(1),of "map (fill \<delta>) LT" "map (update_snd (fill \<delta>)) F" PL]
            fill_keep_value
            list_it_map_app_map[of "fill \<delta>" F]
      by fastforce
qed

lemma fill_empty[simp,intro]:
  "fill \<emptyset> = id"
proof (rule)
  fix x
  show "fill \<emptyset> x  = id x"
    proof (induction x)
      case (Tuple L)
        thus ?case by (induction L, auto)
    next
      case (Record L LT)
        thus ?case by (induction LT, auto)
    next
      case (Pattern p)
        show ?case by (induction p, auto)
    qed auto
qed


lemma coherent_imp_disjoint:
  "coherent_Subst (\<delta>@\<delta>1) \<Longrightarrow> set \<delta> \<inter> set \<delta>1 = {}"
by (metis coherent_imp_distinct distinct_append)

lemma fill_patterns_def:
  "(\<forall>i<length \<delta>. patterns(snd(\<delta>!i)) = []) \<Longrightarrow> set(patterns (fill \<delta> t)) = set (patterns t) - set (fst_extract \<delta>)"
proof(induction t arbitrary: \<delta>)
  case (Pattern p)
    show ?case
      proof(induction p)
        case (V x)
          have A:"find (\<lambda>p. fst p = x) \<delta> = None \<Longrightarrow> x \<notin>set(fst_extract \<delta>)"
            proof (rule)
              assume H:"find (\<lambda>p. fst p = x) \<delta> = None" "x \<in> set (fst_extract \<delta>)"
              show "False"
                using inset_find_Some[OF H(2)]
                      H(1)
                by auto
            qed
          have B: "find (\<lambda>p. fst p = x) \<delta> \<noteq> None \<Longrightarrow>(\<exists>i<length \<delta>. patterns (snd(\<delta>!i)) = [] \<and> find (\<lambda>p. fst p = x) \<delta> = Some (\<delta>!i)) \<and> x \<in> set (fst_extract \<delta>)"
            proof -
              assume H:"find (\<lambda>p. fst p = x) \<delta> \<noteq> None"
              obtain p where H1:"find (\<lambda>p. fst p = x) \<delta> = Some p"
                using H "option.distinct"
                by fast
              hence "\<exists>i<length \<delta>. p = \<delta>!i \<and> x\<in>set(fst_extract \<delta>)"
                using find_Some_iff[of "\<lambda>p. fst p = x" \<delta> p]
                      in_set_conv_nth[of x "fst_extract \<delta>"]
                by auto
              with H1 show ?thesis
                using Pattern
                by auto
            qed
          show ?case 
            using A Diff_eq[of "{x}" "set (fst_extract \<delta>)"] B 
            by (cases "find (\<lambda>p. fst p = x) \<delta> = None", auto)   
      next
        case (RCD L PL)
          thus ?case        
            using Diff_eq[of "(\<Union>a\<in>set PL. set (Pvars a))" "set(fst_extract \<delta>)"]
            by (simp, blast)
      qed
qed auto


lemma same_set_fill:
  "coherent_Subst \<delta> \<Longrightarrow> coherent_Subst \<delta>1 \<Longrightarrow> set \<delta> = set \<delta>1 \<Longrightarrow> fill \<delta> = fill \<delta>1"
proof (rule)
 fix x
 assume H: "coherent_Subst \<delta>" "coherent_Subst \<delta>1" "set \<delta> = set \<delta>1"
 have 1:"\<not> set (patterns x) \<subseteq> set (fst_extract \<delta>) \<Longrightarrow> fill \<delta> x = fill \<delta>1 x"
   proof -
     assume H1: "\<not> set (patterns x) \<subseteq> set (fst_extract \<delta>)"
     then obtain S1 S2 where set_props:"set (patterns x) = S1 \<union> S2" "S1 \<subseteq> set (fst_extract \<delta>)" 
                             "S2 \<inter> set (fst_extract \<delta>) = {}"
       using Un_Diff[of "set (patterns x) \<inter> set (fst_extract \<delta>)" "set (patterns x)" "set (patterns x) \<inter> set (fst_extract \<delta>)"]
       by (cases "set (patterns x) \<inter> set (fst_extract \<delta>) = {}", blast+)
     thus ?thesis
       using incl_fst[of \<delta> \<delta>1] incl_fst[of \<delta>1 \<delta>] H(3)
                   
      sorry
   qed
 show "fill \<delta> x = fill \<delta>1 x" 
   using fill_subsumption[OF H(1,2), of x] H(3)
         1
   (*by (cases "set (patterns x) \<subseteq> set (fst_extract \<delta>)", fastforce)*) sorry
qed 

lemma fill_append_red:
  "(set (patterns t) \<inter> set (fst_extract \<delta>) = {}) \<Longrightarrow> fill (\<delta>@\<delta>1) t = fill \<delta>1 t"
sorry

lemma fill_fill_to_update:
  "coherent_Subst(\<delta>@\<delta>1) \<Longrightarrow> (fill \<delta> \<circ> fill \<delta>1) = fill (update_snd (fill \<delta>) \<delta>1 @ \<delta>)"
proof (rule)
  fix x
  assume hyps:"coherent_Subst(\<delta>@\<delta>1)"
  then show "(fill \<delta> \<circ> fill \<delta>1) x = fill (update_snd (fill \<delta>) \<delta>1 @ \<delta>) x"
    proof(induction x arbitrary: \<delta> \<delta>1)
      case(Pattern p)                
        show ?case
          proof(induction p)
            case (V x)
              have 1:"x \<in> set (fst_extract \<delta>1) \<Longrightarrow> (fill \<delta> \<circ> fill \<delta>1) (<|V x|>) = fill (update_snd (fill \<delta>) \<delta>1 @ \<delta>) (<|V x|>)"
                proof -
                  assume H:"x \<in> set (fst_extract \<delta>1)"
                  obtain i where H1:"(fill \<delta> \<circ> fill \<delta>1) (<|V x|>) = fill \<delta> (snd(\<delta>1!i))" "i<length \<delta>1" "find (\<lambda>e. fst e = x) \<delta>1 = Some (\<delta>1!i)"
                     using inset_find_Some[OF H] zip_comp[of \<delta>1] set_zip[of "fst_extract \<delta>1" "snd_extract \<delta>1"]
                           snd_conv
                     by fastforce                          
                  hence "find (\<lambda>p. fst p = x) ((update_snd (fill \<delta>) \<delta>1) @ \<delta>) = Some (update_snd (fill \<delta>) \<delta>1 ! i)"
                    using find_zip1[of "fst_extract \<delta>1" "snd_extract \<delta>1" "fst_extract \<delta>" "map (fill \<delta>) (snd_extract \<delta>1) @ snd_extract \<delta>" i x] 
                          Pattern
                          zip_comp[of \<delta>1] zip_comp[of \<delta>] zip_append[of "fst_extract \<delta>1" _ "fst_extract \<delta>" "snd_extract \<delta>"]
                          nth_append[of "update_snd (fill \<delta>) \<delta>1" \<delta> i]
                    by force
                  hence "fill (update_snd (fill \<delta>) \<delta>1 @ \<delta>) (<|V x|>) = fill \<delta> (snd(\<delta>1!i))"
                    using nth_zip[of i "fst_extract \<delta>1" "map (fill \<delta>) (snd_extract \<delta>1)"] H1(2)
                          snd_conv nth_map[of i "snd_extract \<delta>1" "fill \<delta>"]
                    by force
                  with H1(1)
                    show ?thesis
                      by auto
                qed
              have "x \<notin> set (fst_extract \<delta>1) \<Longrightarrow> (fill \<delta> \<circ> fill \<delta>1) (<|V x|>) = fill (update_snd (fill \<delta>) \<delta>1 @ \<delta>) (<|V x|>)"
                proof -
                  assume H: "x \<notin> set (fst_extract \<delta>1)"
                  hence H1:"(fill \<delta> \<circ> fill \<delta>1) (<|V x|>) = fill \<delta> (<|V x|>)"
                    using fill_only_incl[of "<|V x|>" \<delta>1]
                    by simp
                  have "fill (update_snd (fill \<delta>) \<delta>1 @ \<delta>) (<|V x|>) = fill \<delta> (<|V x|>)"
                    using Pattern H fill_append_red[of "<|V x|>"]
                    by auto
                  with H1
                    show ?thesis
                      by presburger
                qed
              with 1 show ?case
                by blast
          next
            case (RCD L PL)
              have 1:"set (Pvars (RCD L PL)) \<inter> set (fst_extract \<delta>1) = {} \<Longrightarrow> ?case"
                proof -
                  assume H:"set (Pvars (RCD L PL)) \<inter> set (fst_extract \<delta>1) = {}"
                  hence H1:"(fill \<delta> \<circ> fill \<delta>1) (<|RCD L PL|>) = fill \<delta> (<|RCD L PL|>)"
                    using fill_only_incl[of "<|RCD L PL|>" \<delta>1]
                    by auto
                  have "fill (update_snd (fill \<delta>) \<delta>1 @ \<delta>) (<|RCD L PL|>) = fill \<delta> (<|RCD L PL|>)"
                    using fill_append_red[of "<|RCD L PL|>" "update_snd (fill \<delta>) \<delta>1"  \<delta>] H
                    by force
                  with H1
                    show ?thesis
                      by auto
                qed
              have "set (Pvars (RCD L PL)) \<inter> set (fst_extract \<delta>1) \<noteq> {} \<Longrightarrow> ?case"
                proof (induction PL)
                  case (Cons p PL')
                    thus ?case
                      sorry
                qed simp                
              with 1 show ?case
                by auto              
          qed
    qed auto
qed 

lemma pcontext_inversion:
  "\<Gamma> \<turnstile> \<lparr>t|;|\<delta>\<rparr> |:| A \<Longrightarrow> set(patterns t) \<subseteq> set (fst_extract \<delta>)"(* \<and> (i<length \<delta> \<longrightarrow> patterns(snd (\<delta>!i)) = [])*)
proof (induction rule: has_type_L.induct)
  case (has_type_Tuple L TL \<Gamma> \<delta>)
    show ?case
      using has_type_Tuple(4) set_conv_nth[of L]
      by auto
next
  case (has_type_RCD L LT TL \<Gamma> \<delta>)
    show ?case 
      using has_type_RCD(6) set_conv_nth[of LT]
      by auto
next
  case (has_type_PatternVar \<Gamma> t A k \<delta>)
    show ?case
      using has_type_PatternVar(3)
            zip_comp[of \<delta>]
            set_zip_leftD[of k t "fst_extract \<delta>" "snd_extract \<delta>"]
      by auto
next
  case (has_type_PatternRCD L PL TL \<Gamma> \<delta>)
    show ?case
      using has_type_PatternRCD(6) set_conv_nth[of PL]
      by auto
next
  case (has_type_LetPattern \<delta> \<delta>1 p t1 \<Gamma> t2 A)
    show ?case
      using has_type_LetPattern(4,6)
            Lmatch_pvars[OF has_type_LetPattern(3)]
      by auto
qed auto

lemma fill_to_type:
  "\<Gamma>\<turnstile> \<lparr>fill \<delta> t|;| \<delta>1\<rparr> |:| A \<Longrightarrow> \<Gamma>\<turnstile> \<lparr>t|;|(update_snd (fill \<delta>1) \<delta>@\<delta>1) \<rparr> |:| A"
(*proof (induction rule: fill.induct)
  use inversions
qed (auto intro: "has_type_L.intros")
*)

lemma coherence_order_independent:
  "coherent_Subst \<delta> \<Longrightarrow> (\<forall>x\<in>set \<delta>1. count_list \<delta>1 x = count_list \<delta> x) \<Longrightarrow> coherent_Subst \<delta>1"
sorry

lemma has_type_L_order_irr:
  "\<Gamma> \<turnstile> \<lparr>t|;|\<delta>\<rparr> |:| A \<Longrightarrow> (\<forall>x\<in>set \<delta>1. count_list \<delta>1 x = count_list \<delta> x) \<Longrightarrow> set \<delta> = set \<delta>1 \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t|;|\<delta>1\<rparr> |:| A"
sorry

lemma has_type_filled:
  assumes coherence: "coherent_Subst (\<delta>@\<delta>1)" and
          conform_pattern: "\<forall>x\<in>set \<Delta>. count_list \<Delta> x = count_list (update_snd (fill \<delta>1) \<delta>@\<delta>1) x"
                           "set \<Delta> = set (update_snd (fill \<delta>1) \<delta>@\<delta>1)"
          and
          well_typed: "\<Gamma>\<turnstile> \<lparr>t|;|\<Delta>\<rparr> |:| A"
  shows "\<Gamma> \<turnstile> \<lparr>fill \<delta> t|;|\<delta>1\<rparr> |:| A"
using assms(4,1,2,3) 
proof (induction \<Gamma> t \<Delta> A arbitrary: \<delta> \<delta>1 rule: has_type_L.induct)
  case (has_type_LAbs \<Gamma> A t2 B)
    show ?case
      using has_type_LAbs
            weakening[of \<Gamma> _ _ _"\<Gamma>|,|A"] "has_type_L.intros"
      by force
next
  case (has_type_ProjT i TL \<Gamma> t)
    show ?case
      using has_type_L.intros(15)[OF has_type_ProjT(1,2), of \<Gamma> "fill \<delta> t" \<delta>1]
            has_type_ProjT(4-7)
      by simp
next
  case (has_type_PatternVar \<Gamma> t A k \<delta>')
    
    have 1:"k \<in> set (fst_extract \<delta>) \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>(case find (\<lambda>p. fst p = k) \<delta> of None \<Rightarrow> <|V k|> | Some x \<Rightarrow> snd x)|;|\<delta>1\<rparr> |:| A"
      proof -
        assume H:"k\<in> set (fst_extract \<delta>)"
        
        obtain t' where H1:"find (\<lambda>p. fst p = k) \<delta> = Some (k, t') \<and> (k, t') \<in> set \<delta>"
          using inset_find_Some[OF H]
          by blast  
        (* only smt can solve Pb1 *)
        have "t= fill \<delta>1 t'"
          proof -
            obtain t2 where A:"fill \<delta>1 t' = t2"
              by auto
            hence "t2 \<in> set(map (fill \<delta>1) (snd_extract \<delta>))"
              using set_map[of "fill \<delta>1" "snd_extract \<delta>"]
                    image_iff[of t2 "fill \<delta>1" "set(snd_extract \<delta>)"]
                    H1 zip_comp[of \<delta>] 
                    set_zip_rightD[of k t' "fst_extract \<delta>" "snd_extract \<delta>"]
              by force
            hence "(k,t2) \<in> set(update_snd (fill \<delta>1) \<delta>)" 
              using in_set_zip[of "(k,t2)" "fst_extract \<delta>" "map (fill \<delta>1) (snd_extract \<delta>)"]
                    in_set_conv_nth H1 set_zip_leftD[of k t' "fst_extract \<delta>" "snd_extract \<delta>"]
                    A
                    in_set_conv_nth[of t2 "map (fill \<delta>1) (snd_extract \<delta>)"]
              by (smt fst_conv len_fst_extract len_snd_extract length_map map_fst_zip map_snd_zip nth_map snd_conv zip_comp)
            thus ?thesis
              using H1 has_type_PatternVar(4,5,7)
                    coherent_Subst_char[OF _ has_type_PatternVar(3),of "(k,t2)"] A
                    coherence_order_independent[OF _ has_type_PatternVar(6)]
              by (cases "t\<noteq>t2", auto)
          qed
        thus ?thesis
          using fill_to_type[of \<Gamma> \<delta>1 t' \<emptyset> A] H1 has_type_PatternVar(1)
                weakening[OF has_type_PatternVar(1), of \<Gamma> \<delta>1]
                zip_comp[of \<delta>1] 
          by auto                    
      qed    
    have 2:"k \<notin> set (fst_extract \<delta>) \<Longrightarrow> \<Gamma> \<turnstile> \<lparr><|V k|>|;|\<delta>1\<rparr> |:| A"
      proof -
        assume hyp : "k \<notin> set (fst_extract \<delta>)"
        hence "(k,t) \<notin> set \<delta>"
          using zip_comp[of \<delta>]
                set_zip_leftD
          by metis
        hence "(k,t)\<in> set \<delta>1"
          using has_type_PatternVar(3,7) hyp set_zip_leftD
          by(cases "(k,t) \<in> set  \<delta>'", fastforce+)            
        thus ?thesis
          using "has_type_L.intros"(18)[OF has_type_PatternVar(1,2)]
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
  case (has_type_PatternRCD L PL TL \<Gamma> \<delta>')
    have 1:"\<And>i. (\<Union>a\<in>set PL. set (Pvars a)) \<inter> set (fst_extract \<delta>) = {} \<Longrightarrow> i < length PL \<Longrightarrow> \<Gamma> \<turnstile> \<lparr><|PL ! i|>|;|\<delta>1\<rparr> |:| (TL ! i)"
      proof -
        fix i
        assume hyp: "i< length PL" "(\<Union>a\<in>set PL. set (Pvars a)) \<inter> set (fst_extract \<delta>) = {}"
        have "set (Pvars (PL ! i)) \<subseteq> set (fst_extract \<delta>1)"
          proof -
            have "set(Pvars (PL ! i)) \<subseteq> (\<Union>a\<in>set PL. set (Pvars a))"
              using hyp(1) in_set_conv_nth[of "PL!i" PL]
              by blast
            thus ?thesis
              using hyp(2) has_type_PatternRCD(9) incl_fst[of \<delta>'"update_snd (fill \<delta>1) \<delta> @ \<delta>1"]
                    pcontext_inversion[OF has_type_PatternRCD(5)[OF hyp(1)]]
              by fastforce           
          qed
        then show "\<Gamma> \<turnstile> \<lparr><|PL ! i|>|;|\<delta>1\<rparr> |:| (TL ! i)"
          using has_type_PatternRCD(7,9)
                strengthening[OF has_type_PatternRCD(5)[OF hyp(1)],of \<delta>1]
                coherence_order_independent[OF _ has_type_PatternRCD(8)]      
          by auto
      qed
    have 2:"(\<Union>a\<in>set PL. set (Pvars a)) \<inter> set (fst_extract \<delta>) \<noteq> {} \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Record L (map (p_instantiate \<delta>) PL)|;|\<delta>1\<rparr> |:| \<lparr>L|:|TL\<rparr>"
      proof -
        assume hyp:  "(\<Union>a\<in>set PL. set (Pvars a)) \<inter> set (fst_extract \<delta>) \<noteq> {}"
        show ?thesis
          using has_type_PatternRCD(1-4)
                has_type_PatternRCD(6)[OF _ has_type_PatternRCD(7-9)]
          by (force intro!: "has_type_L.intros")
      qed
    show ?case
      using has_type_PatternRCD
            1 2
      by (auto intro: "has_type_L.intros")
next
  case (has_type_LetPattern \<delta>' \<Delta> p t1 \<Gamma> t2 A)
    have 1:"coherent_Subst (update_snd (fill \<delta>) \<delta>' @ \<delta>1)"
      proof-
        have "coherent_Subst \<delta>' \<and> coherent_Subst \<delta>1"
          using  has_type_LetPattern(1,8,9)
                 coherence_order_independent[of \<Delta> "update_snd (fill \<delta>1) \<delta> @ \<delta>1"]
                 fst_updt_snd_is_fst[of \<delta> "fill \<delta>1"]
          by simp
        then show ?thesis  
          using has_type_LetPattern(1,9)
                incl_fst[of \<Delta> "update_snd (fill \<delta>1) \<delta> @ \<delta>1"]
                incl_fst[of "update_snd (fill \<delta>1) \<delta> @ \<delta>1" \<Delta>]
          by auto
      qed 
    have 4:"coherent_Subst (\<delta> @ update_snd (fill \<delta>1) (update_snd (fill \<delta>) \<delta>') @ \<delta>1)"
      proof -
        have H1:"distinct (fst_extract \<delta>) \<and> distinct(fst_extract \<delta>') \<and> distinct (fst_extract \<delta>1)" 
          using 1 has_type_LetPattern(7)
          by simp
        have "set (fst_extract \<delta>') \<inter> set (fst_extract \<delta>1) = {} \<and> set (fst_extract \<delta>) \<inter> (set (fst_extract \<delta>') \<union> set (fst_extract \<delta>1)) = {}"
          using has_type_LetPattern(1,7,9)
                incl_fst[of \<Delta> "update_snd (fill \<delta>1) \<delta> @ \<delta>1"]
                incl_fst[of "update_snd (fill \<delta>1) \<delta> @ \<delta>1" \<Delta>]
          by auto      
        with H1 show ?thesis
          using HOL.sym[OF Fun.comp_apply[of "update_snd (fill \<delta>1)" "update_snd (fill \<delta>)" \<delta>']]
          by (simp add: update_snd_comp)
      qed
    
    have 3: "\<forall>x\<in>set (update_snd (fill \<Delta>) \<delta>' @ \<Delta>).
       count_list (update_snd (fill \<Delta>) \<delta>' @ \<Delta>) x =
       count_list (update_snd (fill (update_snd (fill \<delta>1) (update_snd (fill \<delta>) \<delta>') @ \<delta>1)) \<delta> @ update_snd (fill \<delta>1) (update_snd (fill \<delta>) \<delta>') @ \<delta>1) x"
      proof (rule)
        fix x
        let ?goal ="count_list (update_snd (fill \<Delta>) \<delta>' @ \<Delta>) x = count_list (update_snd (fill (update_snd (fill \<delta>1) (update_snd (fill \<delta>) \<delta>')
                                                                    @ \<delta>1)) \<delta> @ update_snd (fill \<delta>1) (update_snd (fill \<delta>) \<delta>') @ \<delta>1) x"
        assume hyp1:"x \<in> set (update_snd (fill \<Delta>) \<delta>' @ \<Delta>)"
                      
        have Hyp1:"fill \<delta>1 \<circ> fill \<delta> = fill (update_snd (fill \<delta>1) \<delta> @ \<delta>1)" 
          using fill_fill_to_update[of \<delta>1 \<delta>]
                has_type_LetPattern(7)
          by auto
        have Hyp2: "fill \<Delta> = fill \<delta>1 \<circ> fill \<delta>"
          using same_set_fill[OF _ _ has_type_LetPattern(9)]
                4 has_type_LetPattern(1) Hyp1
          by auto
        have Hyp3: "\<forall>i<length \<delta>. fill (update_snd (fill \<delta>1 \<circ> fill \<delta>) \<delta>' @ \<delta>1) (snd (\<delta> ! i)) = fill \<delta>1 (snd (\<delta> ! i))"
          proof (rule+)
            fix i
            let ?goal3="fill (update_snd (fill \<delta>1 \<circ> fill \<delta>) \<delta>' @ \<delta>1) (snd (\<delta> ! i)) = fill \<delta>1 (snd (\<delta> ! i))"
            assume hyp: "i<length \<delta>"
            have "set (patterns (snd (\<delta> ! i))) \<subseteq> set (fst_extract \<delta>1)"
              proof -
                obtain sL sL1 where H:"sL = length (update_snd (fill \<Delta>) \<delta>')" "sL1 = length (update_snd (fill \<delta>1) \<delta>)"
                  by fastforce
              
                have T1:"\<forall>j<length \<Delta>. j + sL < length (update_snd (fill \<Delta>) \<delta>' @ \<Delta>) \<longrightarrow>
                         patterns (snd ((update_snd (fill \<Delta>) \<delta>' @ \<Delta>) ! (j + sL))) = \<emptyset>"
                  using pcontext_inversion[OF has_type_LetPattern(5),of "_+sL"]    
                  by blast
                have T:"\<forall>j<length \<Delta>. j+sL < length (update_snd (fill \<Delta>) \<delta>' @ \<Delta>)"
                  using hyp H same_count_set_length[OF has_type_LetPattern(8,9)]
                  by auto
                have T2: "\<forall>j<length \<delta>1. patterns (snd (\<delta>1!j)) = \<emptyset>"
                  proof (rule+)
                    fix j
                    assume H1:"j<length \<delta>1"
                    have L:"length \<Delta> = length (update_snd (fill \<delta>1) \<delta> @ \<delta>1)"
                      using same_count_set_length[OF has_type_LetPattern(8,9)]
                      by blast
                    obtain ja where "\<Delta> ! ja = (update_snd (fill \<delta>1) \<delta> @ \<delta>1) ! (j + sL1)" "ja < length \<Delta>"
                      using same_count_set_ex_commun_index[of "update_snd (fill \<delta>1) \<delta> @ \<delta>1" \<Delta> "j+sL1"]
                            H1 has_type_LetPattern(8,9) H(2)
                            nth_append[of "update_snd (fill \<delta>1) \<delta>" \<delta>1 "j+sL1"]
                      by auto
                    then show "patterns (snd (\<delta>1!j)) = \<emptyset>"
                      using nth_append[of "(update_snd (fill \<Delta>) \<delta>')" \<Delta> "ja + sL"]
                            H H1 spec[OF T1]
                            nth_append[of  "update_snd (fill \<delta>1) \<delta>" \<delta>1 "j+sL1"]
                      by force      
                  qed
                obtain j where "j<length \<Delta>" "fill \<delta>1 (snd (\<delta> ! i)) = snd(\<Delta>!j)"  
                  using has_type_LetPattern(8,9) hyp                       
                        same_count_set_ex_commun_index[of "update_snd (fill \<delta>1) \<delta> @ \<delta>1" \<Delta> i]
                        nth_append[of "update_snd (fill \<delta>1) \<delta>" \<delta>1 i]
                  by auto                                              
                hence "patterns (fill \<delta>1 (snd (\<delta> ! i))) = []"
                  using hyp H T1 T
                        nth_append[of "update_snd (fill \<Delta>) \<delta>'" \<Delta> "j+sL"]
                  by fastforce 
                then show ?thesis
                  using fill_patterns_def[OF T2, of "snd(\<delta>!i)"] 
                  by auto
              qed
            then show ?goal3 
              using fill_subsumption[of \<delta>1 "update_snd (fill \<delta>1 \<circ> fill \<delta>) \<delta>' @ \<delta>1" "snd(\<delta>!i)"]
                    1
              by force
          qed
        show ?goal
          using hyp1  has_type_LetPattern(1,8,9) 
                coherent_imp_disjoint[of "update_snd (fill \<Delta>) \<delta>'" \<Delta>]
                count_notin[of x]
          by (simp add: HOL.sym[OF Fun.comp_apply[of "update_snd (fill \<delta>1)" "update_snd (fill \<delta>)" \<delta>']]
                HOL.sym[OF Hyp1] Hyp2 update_snd_comp del: fst_updt_snd_is_fst)
              (force simp add:update_snd_rewrite_fun[OF Hyp3] simp del: fst_updt_snd_is_fst)+       
      qed    
    have 2:"set (update_snd (fill \<Delta>) \<delta>' @ \<Delta>) =
     set (update_snd (fill (update_snd (fill \<delta>1) (update_snd (fill \<delta>) \<delta>') @ \<delta>1)) \<delta> @ update_snd (fill \<delta>1) (update_snd (fill \<delta>) \<delta>') @ \<delta>1)"
      proof -
        have A0: "update_snd (fill \<delta>1) (update_snd (fill \<delta>) \<delta>') = update_snd (fill \<delta>1 \<circ> fill \<delta>) \<delta>'"
          using HOL.sym[OF Fun.comp_apply[of "update_snd (fill \<delta>1)" "update_snd (fill \<delta>)" \<delta>']]
          by (simp add:update_snd_comp[of "fill \<delta>1" "fill \<delta>"] del: fst_updt_snd_is_fst)
        have A: "set(update_snd (fill \<Delta>) \<delta>') = set (update_snd  (fill \<delta>1 \<circ> fill \<delta>) \<delta>')" 
          using has_type_LetPattern(1,9)
                fill_fill_to_update[of \<delta>1 \<delta>]
                4 subset_coherent same_set_fill[of \<Delta> "update_snd (fill \<delta>1) \<delta> @ \<delta>1"]
          by force
        have B:"\<forall>i<length \<delta>. set (patterns (snd (\<delta> ! i))) \<subseteq> set (fst_extract \<delta>1)" 
          proof (rule, rule)
            fix i
            assume hyp: "i<length \<delta>"
            obtain sL where H:"sL = length (update_snd (fill (update_snd (fill \<delta>1) \<delta> @ \<delta>1)) \<delta>')"
              by fastforce
            
            have "\<forall>x\<in>set (update_snd (fill (update_snd (fill \<delta>1) \<delta> @ \<delta>1)) \<delta>' @ update_snd (fill \<delta>1) \<delta> @ \<delta>1).
                  count_list (update_snd (fill (update_snd (fill \<delta>1) \<delta> @ \<delta>1)) \<delta>' @ update_snd (fill \<delta>1) \<delta> @ \<delta>1) x = 
                  count_list (update_snd (fill \<Delta>) \<delta>' @ \<Delta>) x"
              proof (rule)
                fix x
                let ?goal ="count_list (update_snd (fill (update_snd (fill \<delta>1) \<delta> @ \<delta>1)) \<delta>' @ update_snd (fill \<delta>1) \<delta> @ \<delta>1) x = 
                                        count_list (update_snd (fill \<Delta>) \<delta>' @ \<Delta>) x"
                assume hyp1:"x \<in> set (update_snd (fill (update_snd (fill \<delta>1) \<delta> @ \<delta>1)) \<delta>' @ update_snd (fill \<delta>1) \<delta> @ \<delta>1)"
                      
                have Hyp1:"fill \<delta>1 \<circ> fill \<delta> = fill (update_snd (fill \<delta>1) \<delta> @ \<delta>1)" 
                  using fill_fill_to_update[of \<delta>1 \<delta>]
                        has_type_LetPattern(7)
                  by auto
                have Hyp2: "fill \<Delta> = fill \<delta>1 \<circ> fill \<delta>"
                  using same_set_fill[OF _ _ has_type_LetPattern(9)]
                        4 has_type_LetPattern(1) Hyp1
                  by auto
                
                with hyp1 Hyp1 have Hyp3:"x \<in> set (update_snd (fill \<Delta>) \<delta>' @ \<Delta>)"
                  using has_type_LetPattern(9)
                  by force
                show ?goal
                  using HOL.sym[OF Hyp1] Hyp2 Hyp3
                        has_type_LetPattern(8)
                        has_type_LetPattern(1,9)
                        coherent_imp_disjoint[of "update_snd (fill \<Delta>) \<delta>'" \<Delta>]
                        count_notin[of x]
                  by force+
              qed
            hence T1:"i + sL < length (update_snd (fill (update_snd (fill \<delta>1) \<delta> @ \<delta>1)) \<delta>' @ update_snd (fill \<delta>1) \<delta> @ \<delta>1) \<Longrightarrow>
                  patterns (snd ((update_snd (fill (update_snd (fill \<delta>1) \<delta> @ \<delta>1)) \<delta>' @ update_snd (fill \<delta>1) \<delta> @ \<delta>1) ! (i + sL))) = \<emptyset>"
              using pcontext_inversion[of \<Gamma> t2 "update_snd (fill (update_snd (fill \<delta>1) \<delta> @ \<delta>1)) \<delta>' @ update_snd (fill \<delta>1) \<delta> @ \<delta>1" A "i+sL"]
                    has_type_L_order_irr[OF has_type_LetPattern(5)]
                    has_type_LetPattern(7,9) 
                    A fill_fill_to_update[of \<delta>1 \<delta>]
              by force   
            have T:"i+sL < length (update_snd (fill (update_snd (fill \<delta>1) \<delta> @ \<delta>1)) \<delta>' @ update_snd (fill \<delta>1) \<delta> @ \<delta>1)"
              using hyp H
              by auto              
            have "patterns (fill \<delta>1 (snd (\<delta> ! i))) = []"
              using hyp H T1[OF T]
                    nth_append[of "(update_snd (fill (update_snd (fill \<delta>1) \<delta> @ \<delta>1)) \<delta>')" "update_snd (fill \<delta>1) \<delta> @ \<delta>1" "i+sL"]
                    nth_append[of "update_snd (fill \<delta>1) \<delta>" \<delta>1 i]
              by fastforce
            then show "set (patterns (snd (\<delta> ! i))) \<subseteq> set (fst_extract \<delta>1)"
              using fill_patterns_def[of \<delta>1 "snd(\<delta>!i)"]
              by auto
          qed
        have "\<forall>x\<in>set (snd_extract \<delta>). fill (update_snd (fill \<delta>1 \<circ> fill \<delta>) \<delta>' @ \<delta>1) x = fill \<delta>1 x"
          proof(rule)
            fix x
            assume hyp: "x\<in> set(snd_extract \<delta>)"
            obtain j where H1:"snd(\<delta>!j) = x" "j<length \<delta>"
              using hyp
              by (metis last_index_less_size_conv len_snd_extract nth_last_index snd_extract_snd_index)
            show "fill (update_snd (fill \<delta>1 \<circ> fill \<delta>) \<delta>' @ \<delta>1) x = fill \<delta>1 x"
              using H1 fill_subsumption[of \<delta>1 "update_snd (fill \<delta>1 \<circ> fill \<delta>) \<delta>' @ \<delta>1" "snd (\<delta>!j)"]
                    has_type_LetPattern(7) 1
                    mp[OF spec[OF B] H1(2)]
              by auto
          qed
        hence "set (update_snd (fill (update_snd (fill \<delta>1 \<circ> fill \<delta>) \<delta>' @ \<delta>1)) \<delta>) = set (update_snd (fill \<delta>1) \<delta>)"
          using update_snd_rewrite_fun[of \<delta> "fill (update_snd (fill \<delta>1 \<circ> fill \<delta>) \<delta>' @ \<delta>1)" "fill \<delta>1"]
                zip_comp[of \<delta>] set_conv_nth[of "snd_extract \<delta>"] snd_extract_snd_index[of _ \<delta>]
          by fastforce
        then show ?thesis
          using A has_type_LetPattern(9) 
          by (simp add: A0 del: fst_updt_snd_is_fst, blast)
      qed  
   
    have 5: "set (patterns (fill \<delta> t1)) \<subseteq> set (fst_extract \<delta>1)"
      using has_type_LetPattern(4)
            has_type_LetPattern(9)
            incl_fst[of \<Delta> "update_snd (fill \<delta>1) \<delta> @ \<delta>1"]
            fill_patterns_def[of \<delta> t1]
      by force
    show ?case
      using has_type_LetPattern(6)[OF 4 3 2]
            has_type_L.intros(20)[OF 1
                                     has_type_LetPattern(2) 
                                     match_to_filled_match[OF has_type_LetPattern(3), of \<delta>]
                                     5 ]
      by (auto)      
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
