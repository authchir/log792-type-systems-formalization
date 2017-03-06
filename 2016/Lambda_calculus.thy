theory Lambda_calculus
  imports Main
          Pure
          List_extra
          "$AFP/List-Index/List_Index"
begin

datatype ltype =
  Bool |
  T (num:nat) |
  Unit |
  Prod ltype ltype (infix "|\<times>|" 225)|
  Fun (domain: ltype) (codomain: ltype) (infixr "\<rightarrow>" 225)|
  TupleT "ltype list" ( "\<lparr>_\<rparr>" [150]225) |
  RecordT "string list" "ltype list" ( "\<lparr>(_)|:|(_)\<rparr>" [101,100] 200) |
  Sum ltype ltype (infix "|+|" 225) |
  TVariant "string list" "ltype list" ( "<(_)|,|(_)>" [151,150] 225)|
  ListT ltype ("\<lambda>List (_)" 225)
  
datatype Lpattern = V nat ltype ("V/ (_)/ as/ (_)" [201,200]220)
                    | RCD "string list" "Lpattern list"


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
  Pattern Lpattern ("<|_|>" [100] 250) |
  LetP Lpattern lterm lterm ("Let/ pattern/ (_)/ :=/ (_)/ in/ (_)"[100,120,150]250) |
  inl lterm ltype ("inl/ (_)/ as/ (_)" [100,100]200) |
  inr lterm ltype ("inr/ (_)/ as/ (_)" [100,100]200) |
  CaseSum lterm nat lterm nat lterm ("Case/ (_)/ of/ Inl/ (_)/ \<Rightarrow>/ (_)/ |/ Inr/ (_)/ \<Rightarrow>/ (_)" [100, 100,100, 100, 100]200) |
  Variant string lterm ltype ("<(_):=(_)> as (_)" [100,55] 200) |
  CaseVar lterm "string list" "nat list" "lterm list" ("Case/ (_)/ of/ <(_):=(_)>/ \<Rightarrow>/ (_)" [100,100,100,100]200)|
  Fixpoint lterm  ("fix (_)" [201]200) |
  Lnil ltype |
  Lcons ltype lterm lterm |
  Lisnil ltype lterm |
  Lhead ltype lterm |
  Ltail ltype lterm

datatype subterm_set = Unary lterm | Bi lterm lterm | Ter lterm lterm lterm | Comp lterm "lterm list" |UList "lterm list" | Void


definition letR :: "ltype\<Rightarrow>lterm\<Rightarrow>lterm\<Rightarrow>lterm" ("letrec/ x:(_) =(_)/ in/ (_)" [100,100,100]200) where
 "letrec x:A = t1 in t2 \<equiv> (let x=fix(LAbs A t1) in t2)"     

fun shift_L :: "int \<Rightarrow> nat \<Rightarrow> lterm \<Rightarrow> lterm" where
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
     else  Let var x := (shift_L d c t) in (shift_L d (Suc c) t1)
     )" |
  "shift_L d c (\<lbrace>t1,t2\<rbrace>) = \<lbrace> shift_L d c t1 , shift_L d c t2 \<rbrace>" |
  "shift_L d c (\<pi>1 t) = \<pi>1 (shift_L d c t)" |
  "shift_L d c (\<pi>2 t) = \<pi>2 (shift_L d c t)" |
  "shift_L d c (Tuple L) = Tuple (map (shift_L d c) L)" |
  "shift_L d c (\<Pi> i t)   = \<Pi> i (shift_L d c t)" |
  "shift_L d c (Record L LT)  = Record L (map (shift_L d c) LT)" |
  "shift_L d c (ProjR l t) = ProjR l (shift_L d c t)" |
  "shift_L d c (<|p|>) = <|p|>" |
  "shift_L d c (Let pattern p := t1 in t2) = (Let pattern p := (shift_L d c t1) in (shift_L d c t2))" |
  "shift_L d c (inl t as T') =  inl (shift_L d c t) as T'" |
  "shift_L d c (inr t as T') =  inr (shift_L d c t) as T'" |
  "shift_L d c (Case t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2) = 
    (Case (shift_L d c t) of 
        Inl (if x\<ge> c then (nat (int x + d)) else x) \<Rightarrow> shift_L d (if x< c then Suc c else c) t1 
      | Inr (if y\<ge> c then (nat (int y + d)) else y) \<Rightarrow> shift_L d (if y< c then Suc c else c) t2)" |
  "shift_L d c (<l:=t> as A) = <l:= shift_L d c t> as A" |
  "shift_L d c (Case t of <L:=I> \<Rightarrow> LT) = 
    (Case (shift_L d c t) of <L:= (map (\<lambda>x. if x\<ge> c then (nat (int x + d)) else x) I)> \<Rightarrow> 
      indexed_map 0 (\<lambda>k. shift_L d (if (I!k)<c then Suc c else c)) LT)"|
  "shift_L d c (Fixpoint t) = Fixpoint (shift_L d c t)" |
  "shift_L d c (Lnil A) = Lnil A"|
  "shift_L d c (Lisnil A t) = Lisnil A (shift_L d c t)"|
  "shift_L d c (Lcons A t t') = Lcons A (shift_L d c t) (shift_L d c t')"|
  "shift_L d c (Lhead A t) = Lhead A (shift_L d c t)"|
  "shift_L d c (Ltail A t) = Ltail A (shift_L d c t)"

function subst_L :: "nat \<Rightarrow> lterm \<Rightarrow> lterm \<Rightarrow> lterm" where
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
    else  (Let var x := (subst_L j s t) in (subst_L (if j > x then Suc j else j) (shift_L 1 x s) t1))) " |
  "subst_L j s (\<lbrace>t1,t2\<rbrace>) = \<lbrace>subst_L j s t1, subst_L j s t2\<rbrace>" |
  "subst_L j s (\<pi>1 t) = \<pi>1 (subst_L j s t)" |
  "subst_L j s (\<pi>2 t) = \<pi>2 (subst_L j s t)" |
  "subst_L j s (\<Pi> i t) = \<Pi> i (subst_L j s t)" |
  "subst_L j s (Tuple L) = Tuple (map (subst_L j s) L)" |
  "subst_L j s (Record L LT) = Record L (map (subst_L j s) LT)" |
  "subst_L j s (ProjR l t) = ProjR l (subst_L j s t)" |
  "subst_L j s (<|p|>) = <|p|>" |
  "subst_L j s (Let pattern p := t1 in t2) = (Let pattern p := (subst_L j s t1) in (subst_L j s t2))" |
  "subst_L j s (inl t as T') =  inl (subst_L j s t) as T'" |
  "subst_L j s (inr t as T') =  inr (subst_L j s t) as T'" |
  "subst_L j s (Case t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2) = 
    (Case (subst_L j s t) of 
        Inl x \<Rightarrow> (if j=x then t1 else subst_L (if j > x then Suc j else j) (shift_L 1 x s) t1)
      | Inr y \<Rightarrow> (if j=y then t2 else subst_L (if j > y then Suc j else j) (shift_L 1 y s) t2))" |
  "subst_L j s (<l:=t> as T') =  <l:=subst_L j s t> as T'" |
  "subst_L j s (Case t of <L:=I> \<Rightarrow> LT) = 
    (Case (subst_L j s t) of <L:=I> \<Rightarrow> map (\<lambda>p. if j=fst p then snd p else subst_L (if j > fst p  then Suc j else j) (shift_L 1 (fst p) s) (snd p)) (zip I LT))" |
  "subst_L j s (Fixpoint t) = Fixpoint (subst_L j s t)"|
  "subst_L j s (Lnil A) = Lnil A"|
  "subst_L j s (Lisnil A t) = Lisnil A (subst_L j s t)"|
  "subst_L j s (Lcons A t t') = Lcons A (subst_L j s t) (subst_L j s t')"|
  "subst_L j s (Lhead A t) = Lhead A (subst_L j s t)" |
  "subst_L j s (Ltail A t) = Ltail A (subst_L j s t)"
by pat_completeness auto

termination
  by (relation "measure (\<lambda>(j,s,t). size t)", simp_all)
      (metis less_add_Suc1 size_list_estimation' set_zip_rightD 
              lessI not_less prod.collapse)+
  
text{*
      We want to restrict the considered pattern matching and filling to coherent cases, which are
      the cases when a pattern variable can only appear once in a given pattern.\\

      Furthermore, the same coherence principle is valid for the pattern context. A pattern variable can only 
      have on type at a time
*}

fun Pvars :: "Lpattern \<Rightarrow> nat list" where
"Pvars (V n as A) = [n]" |
"Pvars (RCD L PL) = (foldl (\<lambda>x r. x @ r) [] (map Pvars PL))" 

fun patterns::"lterm \<Rightarrow> nat list" where
"patterns (<|p|>) = Pvars p" |
"patterns (LIf c t1 t2)               = patterns c @ patterns t1 @ patterns t2" |
"patterns (LAbs A t1)                 = patterns t1" |
"patterns (LApp t1 t2)                = patterns t1 @ patterns t2" |
"patterns (Seq t1 t2)                 = patterns t1 @ patterns t2" |
"patterns (t1 as A)                   = patterns t1" |
"patterns (Let var x := t1 in t2)     = patterns t1 @ patterns t2" |
"patterns (\<lbrace>t1,t2\<rbrace>)                   = patterns t1 @ patterns t2" |
"patterns (Tuple L)                   = foldl (\<lambda>e r. e @ r) [] (map (patterns) L)" |
"patterns (Record L LT)               = foldl (\<lambda>e r. e @ r) [] (map (patterns) LT)" |
"patterns (\<pi>1 t)                      = patterns t" |
"patterns (\<pi>2 t)                      = patterns t" |
"patterns (\<Pi> i t)                     = patterns t" |
"patterns (ProjR l t)                 = patterns t" |
"patterns (Let pattern p := t1 in t2) = patterns t1 @ patterns t2" |
"patterns (inl t as T') =  patterns t" |
"patterns (inr t as T') =  patterns t" |
"patterns (Case t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2) = patterns t @ patterns t1 @ patterns t2" |
"patterns (<l:=t> as T') =  patterns t" |
"patterns (Case t of <L:=I> \<Rightarrow> LT) = patterns t @ foldl (\<lambda>e r. e @ r) [] (map (patterns) LT)" |
"patterns (Fixpoint t) = patterns t"|
"patterns (Lisnil A t)                  = patterns t" |
"patterns (Lhead A t)                  = patterns t" |
"patterns (Ltail A t)                 = patterns t" |
"patterns (Lcons A t t')              = patterns t @ patterns t'"|
"patterns t = []"


inductive is_value_L :: "lterm \<Rightarrow> bool" where
  VTrue : "is_value_L LTrue" |
  VFalse: "is_value_L LFalse" |
  VAbs  :"is_value_L (LAbs T' t)" |
  VUnit :"is_value_L unit" |
  VPair :"is_value_L v1 \<Longrightarrow> is_value_L v2 \<Longrightarrow> is_value_L (\<lbrace>v1,v2\<rbrace>)" |
  VTuple:"(\<And>i. 0\<le>i \<Longrightarrow> i<length L \<Longrightarrow> is_value_L (L!i)) \<Longrightarrow> is_value_L (Tuple L)" |
  VRCD  :"(\<And>i. 0\<le>i \<Longrightarrow> i<length LT \<Longrightarrow> is_value_L (LT!i)) \<Longrightarrow>  is_value_L (Record L LT)"|
  VSumL :"is_value_L v \<Longrightarrow> is_value_L (inl v as A)"|
  VSumR :"is_value_L v \<Longrightarrow> is_value_L (inr v as A)"|
  VVa   :"is_value_L v \<Longrightarrow> is_value_L (<l:=v> as A)"|
  VNil  :"is_value_L (Lnil A)"|
  VCons :"is_value_L v1 \<Longrightarrow> is_value_L v2 \<Longrightarrow> is_value_L (Lcons A v1 v2)"

function FV :: "lterm \<Rightarrow> nat set" where
  "FV LTrue = {}" |
  "FV LFalse = {}" |
  "FV (LIf t1 t2 t3) = FV t1 \<union> FV t2 \<union> FV t3" |
  "FV (LVar x) = {x}" |
  "FV (LAbs T1 t) = image (\<lambda>x. x - 1) (FV t - {0})" |
  "FV (LApp t1 t2) = FV t1 \<union> FV t2" |
  "FV unit = {}" |
  "FV (Seq t1 t2) = FV t1 \<union> FV t2" |
  "FV (t as A) = FV t" |
  "FV (Let var x := t in t1) = image (\<lambda>y. if (y\<ge>x) then y - 1 else y) (FV t1 -{x}) \<union> FV t \<union> {x}" |
  "FV (\<lbrace>t1,t2\<rbrace>) = FV t1 \<union> FV t2" |
  "FV (\<pi>1 t) =  FV t" |
  "FV (\<pi>2 t) =  FV t" |
  "FV (Tuple L) = foldl (\<lambda>x r. x \<union> r) {} (map FV L) "|
  "FV (\<Pi> i t) = FV t" |
  "FV (Record L LT) = foldl (\<lambda>x r. x \<union> r) {} (map FV LT) "|
  "FV (ProjR l t) = FV t" |
  "FV (Pattern p) = {}" |
  "FV (Let pattern p := t1 in t2) = FV t1 \<union> FV t2" |
  "FV (inl t as A) = FV t" |
  "FV (inr t as A) = FV t" |
  "FV (Case t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2) = image (\<lambda>y. if (y\<ge>x) then y - 1 else y) (FV t1 -{x}) \<union> 
                                              image (\<lambda>z. if (z\<ge>y) then z - 1 else z) (FV t2 -{y}) \<union> 
                                              FV t \<union> {x,y}" |
  "FV (<L:=t> as A) = FV t" |
  "FV (Case t of <L:=I> \<Rightarrow> LT) = FV t \<union> foldl (\<lambda>x r. x \<union> r) {} (indexed_map 0 (\<lambda>k t. image (\<lambda>y. if (y\<ge>I!k) then y - 1 else y) (FV t - {I!k})) LT) \<union> set I" |
  "FV (Fixpoint t) = FV t"|
  "FV (Lcons A t t') = FV t \<union> FV t'"|
  "FV (Ltail A t) = FV t"|
  "FV (Lhead A t) = FV t"|
  "FV (Lisnil A t) = FV t"|
  "FV (Lnil A) = {}"
by pat_completeness auto

termination
  by (relation "measure (\<lambda>t. size t)", simp_all)
      (metis less_add_Suc1 size_list_estimation' set_zip_rightD 
              lessI not_less prod.collapse)+

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


fun p_instantiate::"(nat\<Rightarrow> lterm) \<Rightarrow> Lpattern \<Rightarrow> lterm" where
"p_instantiate \<Sigma> (V k as A) = \<Sigma> k"|
"p_instantiate \<Sigma> (RCD L PL) = <|RCD L PL|>" 

fun fill::"(nat \<Rightarrow> lterm) \<Rightarrow> lterm \<Rightarrow> lterm" where
"fill \<Sigma> (Pattern p)                 = p_instantiate \<Sigma> p" |
"fill \<Sigma> (LIf c t1 t2)               = LIf (fill \<Sigma> c) (fill \<Sigma> t1) (fill \<Sigma> t2)" |
"fill \<Sigma> (LAbs A t1)                 = LAbs A (fill \<Sigma> t1)" |
"fill \<Sigma> (LApp t1 t2)                = LApp (fill \<Sigma> t1) (fill \<Sigma> t2)" |
"fill \<Sigma> (Seq t1 t2)                 =  Seq (fill \<Sigma> t1) (fill \<Sigma> t2)" |
"fill \<Sigma> (t1 as A)                   = (fill \<Sigma> t1) as A" |
"fill \<Sigma> (Let var x := t1 in t2)     = (Let var x := (fill \<Sigma> t1) in (fill \<Sigma> t2))" |
"fill \<Sigma> (\<lbrace>t1,t2\<rbrace>)                   = \<lbrace>(fill \<Sigma> t1), (fill \<Sigma> t2)\<rbrace>" |
"fill \<Sigma> (Tuple L)                   = Tuple (map (fill \<Sigma>) L)" |
"fill \<Sigma> (Record L LT)               = Record L (map (fill \<Sigma>) LT)" |
"fill \<Sigma> (\<pi>1 t)                      = \<pi>1 (fill \<Sigma> t)" |
"fill \<Sigma> (\<pi>2 t)                      = \<pi>2 (fill \<Sigma> t)" |
"fill \<Sigma> (\<Pi> i t)                     = \<Pi> i (fill \<Sigma> t)" |
"fill \<Sigma> (ProjR l t)                 = ProjR l (fill \<Sigma> t)" |
"fill \<Sigma> (Let pattern p := t1 in t2) = (Let pattern p := (fill \<Sigma> t1) in (fill \<Sigma> t2))" |
"fill \<Sigma> (inl t as A) = inl (fill \<Sigma> t) as A"|
"fill \<Sigma> (inr t as A) = inr (fill \<Sigma> t) as A"|
"fill \<Sigma> (Case t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2) = (Case (fill \<Sigma> t) of Inl x \<Rightarrow> (fill \<Sigma> t1) | Inr y \<Rightarrow> (fill \<Sigma> t2))"|
"fill \<Sigma> (<l:=t> as A) =  <l:=(fill \<Sigma> t)> as A"|
"fill \<Sigma> (Case t of <L:=I> \<Rightarrow> LT) = (Case (fill \<Sigma> t) of <L:=I> \<Rightarrow> map (fill \<Sigma>) LT)"|
"fill \<Sigma> (Fixpoint t) = Fixpoint (fill \<Sigma> t)" |
"fill \<Sigma> (Lisnil A t)                = Lisnil A (fill \<Sigma> t)" |
"fill \<Sigma> (Lhead A t)                 = Lhead A (fill \<Sigma> t)" |
"fill \<Sigma> (Ltail A t)                 = Ltail A (fill \<Sigma> t)" |
"fill \<Sigma> (Lcons A t t')              = Lcons A (fill \<Sigma> t) (fill \<Sigma> t')" |
"fill \<Sigma> t = t"

fun subterms :: "lterm\<Rightarrow>subterm_set" where
"subterms (LIf c t1 t2)               = Ter c t1 t2" |
"subterms (LAbs A t1)                 = Unary t1" |
"subterms (LApp t1 t2)                = Bi t1 t2" |
"subterms (Seq t1 t2)                 = Bi t1 t2" |
"subterms (t1 as A)                   = Unary t1" |
"subterms (Let var x := t1 in t2)     = Bi t1 t2" |
"subterms (\<lbrace>t1,t2\<rbrace>)                   = Bi t1 t2" |
"subterms (Tuple L)                   = UList L" |
"subterms (Record L LT)               = UList LT" |
"subterms (\<pi>1 t)                      = Unary t" |
"subterms (\<pi>2 t)                      = Unary t" |
"subterms (\<Pi> i t)                     = Unary t" |
"subterms (ProjR l t)                 = Unary t" |
"subterms (Let pattern p := t1 in t2) = Bi t1 t2" |
"subterms (inl t as A) = Unary t"|
"subterms (inr t as A) = Unary t"|
"subterms (Case t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2) = Ter t t1 t2"|
"subterms (<l:=t> as A) =  Unary t"|
"subterms (Case t of <L:=I> \<Rightarrow> LT) = Comp t LT"|
"subterms (Fixpoint t) = Unary t" |
"subterms (Lcons A t1 t2)               = Bi t1 t2" |
"subterms (Lhead A t)                  = Unary t" |
"subterms (Ltail A t)                  = Unary t" |
"subterms (Lisnil A t)                  = Unary t" |
"subterms t = Void"

lemma P_list_conv_nth:"(\<And>x. x\<in> A\<union>set L \<Longrightarrow> P x) \<Longrightarrow> (\<And>i. i<length L \<Longrightarrow> P (L!i))"
using set_conv_nth by auto

lemma P_pat_subterm_cases:
  "P (patterns t) \<Longrightarrow> (\<exists>t1. subterms t = Unary t1 \<and> P (patterns t1)) \<or>
    (\<exists>t1 t2. subterms t = Bi t1 t2 \<and> P (patterns t1) \<and> P (patterns t2)) \<or>
    (\<exists>t1 t2 t3. subterms t = Ter t1 t2 t3 \<and> P (patterns t1) \<and> P (patterns t2) \<and> P (patterns t3)) \<or>
    (\<exists>t1 L. subterms t = Comp t1 L \<and> P (patterns t1) \<and> (\<forall>i<length L. P (patterns (L!i)))) \<or>
    (\<exists>L. subterms t = UList L \<and> (\<forall>i<length L. P (patterns (L!i))))" 
sorry

ML \<open>
      fun rewrite_conj_under_all ctxt thm = 
        (case ctxt of
          Context.Theory _ => thm
          |Context.Proof prf =>
              thm
              |> Local_Defs.unfold prf [@{thm atomize_conj[symmetric]}, @{thm atomize_all[symmetric]}, 
                                          @{thm atomize_imp[symmetric]}]
        )
   \<close>
attribute_setup split_and_rule = \<open>Scan.succeed (Thm.rule_attribute [] rewrite_conj_under_all)\<close>


end