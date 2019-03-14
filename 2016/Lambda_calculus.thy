theory Lambda_calculus
imports
  Main
  List_extra
  "List-Index.List_Index"
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
  TVariant "string list" "ltype list" ( "<(_)|,|(_)>" [151,150] 225)
  
datatype Lpattern = V nat ltype ("V/ (_)/ as/ (_)" [201,200]220)
                    | RCD "string list" "Lpattern list"


datatype lterm =
  LTrue |
  LFalse|  
  LIf (bool_expr: lterm) (then_expr: lterm) (else_expr: lterm) |
  LVar nat |
  LAbs (arg_type: ltype) (body: lterm) |
  LApp lterm lterm |
  unit |
  Seq (fp: lterm) (sp: lterm) ("(_;;_)" [100,50] 200) |
  AS lterm ltype ("_/ as/ _" [100,150] 200) |
  LetBinder lterm lterm ("Let (_)/ in/ (_)" [120,150] 250) | 
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
  CaseSum lterm lterm lterm |
  Variant string lterm ltype ("<(_):=(_)> as (_)" [100,55] 200) |
  CaseVar lterm "string list" "lterm list"|
  Fixpoint lterm  ("fix (_)" [201]200)


datatype subterm_set = Unary lterm | Bi lterm lterm | Ter lterm lterm lterm | Comp lterm "lterm list" |UList "lterm list" | Void


definition letR :: "ltype\<Rightarrow>lterm\<Rightarrow>lterm\<Rightarrow>lterm" ("letrec/ x:(_) =(_)/ in/ (_)" [100,100,100]200) where
 "letrec x:A = t1 in t2 \<equiv> (Let (Fixpoint (LAbs A t1)) in t2)"     

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
  "shift_L d c (Let t in t1) = 
    (Let (shift_L d c t) in (shift_L d (Suc c) t1))" |
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
  "shift_L d c (CaseSum t t1 t2) = 
    (CaseSum (shift_L d c t) (shift_L d (Suc c) t1) (shift_L d (Suc c) t2))" |
  "shift_L d c (<l:=t> as A) = <l:= shift_L d c t> as A" |
  "shift_L d c (CaseVar t  L B) = 
    (CaseVar (shift_L d c t)  L (map (shift_L d (Suc c)) B))"|
  "shift_L d c (Fixpoint t) = Fixpoint (shift_L d c t)" 

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
  "subst_L j s (Let t in t1) = ((Let (subst_L j s t) in (subst_L (Suc j) (shift_L 1 0 s) t1))) " |
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
  "subst_L j s (CaseSum t t1 t2) = 
    (CaseSum (subst_L j s t) (subst_L (Suc j) (shift_L 1 0 s) t1) (subst_L (Suc j) (shift_L 1 0 s) t2))" |
  "subst_L j s (<l:=t> as T') =  <l:=subst_L j s t> as T'" |
  "subst_L j s (CaseVar t L B) = 
    (CaseVar (subst_L j s t) L (map (subst_L (Suc j) (shift_L 1 0 s)) B))" |
  "subst_L j s (Fixpoint t) = Fixpoint (subst_L j s t)"
by pat_completeness auto

termination
  by (relation "measure (\<lambda>(j,s,t). size t)", simp_all)
      (metis  size_list_estimation' lessI not_less add.commute le_imp_less_Suc 
            less_irrefl_nat not_less size_list_estimation trans_less_add2)+

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
"patterns (Let t1 in t2)     = patterns t1 @ patterns t2" |
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
"patterns (CaseSum t t1 t2) = patterns t @ patterns t1 @ patterns t2" |
"patterns (<l:=t> as T') =  patterns t" |
"patterns (CaseVar t L B) = patterns t @ foldl (\<lambda>e r. e @ r) [] (map patterns B)" |
"patterns (Fixpoint t) = patterns t"|
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
  VVa   :"is_value_L v \<Longrightarrow> is_value_L (<l:=v> as A)"

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
  "FV (Let t in t1) = image (\<lambda>y. y-1) (FV t1 -{0}) \<union> FV t" |
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
  "FV (CaseSum t t1 t2) = image (\<lambda>y. y - 1) (FV t1 -{0}) \<union> 
                          image (\<lambda>z. z - 1) (FV t2 -{0}) \<union> FV t " |
  "FV (<L:=t> as A) = FV t" |
  "FV (CaseVar t L B) = FV t \<union> (\<Union>i<length B. (image (\<lambda>y. y - 1) (FV (B!i)-{0})))" |
  "FV (Fixpoint t) = FV t"
by pat_completeness auto

termination
  by (relation "measure (\<lambda>t. size t)", simp_all)
     (((metis size_list_estimation' lessI not_less)+)[2],
      meson not_add_less1 not_less_eq nth_mem size_list_estimation)

fun p_instantiate::"(nat \<rightharpoonup> lterm) \<Rightarrow> Lpattern \<Rightarrow> lterm" where
"p_instantiate \<Sigma> (V k as A) = (case \<Sigma> k of Some t' \<Rightarrow> t' | None \<Rightarrow> <|V k as A|>)"|
"p_instantiate \<Sigma> (RCD L PL) = <|RCD L PL|>" 

fun fill::"(nat \<rightharpoonup> lterm) \<Rightarrow> lterm \<Rightarrow> lterm" where
"fill \<Sigma> (Pattern p)                 = p_instantiate \<Sigma> p" |
"fill \<Sigma> (LIf c t1 t2)               = LIf (fill \<Sigma> c) (fill \<Sigma> t1) (fill \<Sigma> t2)" |
"fill \<Sigma> (LAbs A t1)                 = LAbs A (fill \<Sigma> t1)" |
"fill \<Sigma> (LApp t1 t2)                = LApp (fill \<Sigma> t1) (fill \<Sigma> t2)" |
"fill \<Sigma> (Seq t1 t2)                 =  Seq (fill \<Sigma> t1) (fill \<Sigma> t2)" |
"fill \<Sigma> (t1 as A)                   = (fill \<Sigma> t1) as A" |
"fill \<Sigma> (Let t1 in t2)              = (Let (fill \<Sigma> t1) in (fill \<Sigma> t2))" |
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
"fill \<Sigma> (CaseSum t t1 t2) = (CaseSum (fill \<Sigma> t) (fill \<Sigma> t1) (fill \<Sigma> t2))"|
"fill \<Sigma> (<l:=t> as A) =  <l:=(fill \<Sigma> t)> as A"|
"fill \<Sigma> (CaseVar t L B) = (CaseVar (fill \<Sigma> t) L (map (fill \<Sigma>) B))"|
"fill \<Sigma> (Fixpoint t) = Fixpoint (fill \<Sigma> t)" |
"fill \<Sigma> t = t"

fun subterms :: "lterm\<Rightarrow>subterm_set" where
"subterms (LIf c t1 t2)               = Ter c t1 t2" |
"subterms (LAbs A t1)                 = Unary t1" |
"subterms (LApp t1 t2)                = Bi t1 t2" |
"subterms (Seq t1 t2)                 = Bi t1 t2" |
"subterms (t1 as A)                   = Unary t1" |
"subterms (Let t1 in t2)              = Bi t1 t2" |
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
"subterms (CaseSum t t1 t2) = Ter t t1 t2"|
"subterms (<l:=t> as A) =  Unary t"|
"subterms (CaseVar t L B) = Comp t B"|
"subterms (Fixpoint t) = Unary t" |
"subterms t = Void"


end