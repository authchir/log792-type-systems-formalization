theory Lambda_calculus
imports Main 
        Pure
        List_extra
        "$AFP/List-Index/List_Index"
begin

  datatype ltype =
  Nat  |
  Bool |
  T (num:nat) |
  Unit |
  Prod ltype ltype (infix "|\<times>|" 225)|
  Fun (domain: ltype) (codomain: ltype) (infixr "\<rightarrow>" 225)|
  TupleT "ltype list" ( "\<lparr>_\<rparr>" [150]225) |
  RecordT "string list" "ltype list" ( "\<lparr>_|:|_\<rparr>" [150,150] 225) |
  Sum ltype ltype (infix "|+|" 225) |
  TVariant "string list" "ltype list" ( "<_|,|_>" [150,150] 225) 
  
datatype Lpattern = V nat | RCD "string list" "Lpattern list"


datatype lterm =
  LTrue |
  LFalse |
  LIf (bool_expr: lterm) (then_expr: lterm) (else_expr: lterm) |
  LVar nat |
  LNat int |
  LPlus lterm lterm |
  UMinus lterm |
  IsZero lterm |
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
  Fixpoint "lterm"  ("fix (_)" [201]200)

datatype subterm_set = U lterm | Bi lterm lterm | Ter lterm lterm lterm | Comp lterm "lterm list" |UList "lterm list" | Void


definition letR :: "ltype\<Rightarrow>lterm\<Rightarrow>lterm\<Rightarrow>lterm" ("letrec/ x:(_) =(_)/ in/ (_)" [100,100,100]200) where
 "letrec x:A = t1 in t2 \<equiv> (let x=fix(LAbs A t1) in t2)"     

primrec shift_L :: "int \<Rightarrow> nat \<Rightarrow> lterm \<Rightarrow> lterm" where
  "shift_L d c LTrue = LTrue" |
  "shift_L d c LFalse = LFalse" |
  "shift_L d c (LIf t1 t2 t3) = LIf (shift_L d c t1) (shift_L d c t2) (shift_L d c t3)" |
  "shift_L d c (LVar k) = LVar (if k < c then k else nat (int k + d))" |
  "shift_L d c (LNat n) = LNat n"|
  "shift_L d c (UMinus t) = UMinus (shift_L d c t)"|
  "shift_L d c (IsZero t) = IsZero (shift_L d c t)"|
  "shift_L d c (LPlus t1 t2) = LPlus (shift_L d c t1) (shift_L d c t2)"|
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
      | Inr (if y\<ge> c then (nat (int y + d)) else y) \<Rightarrow> shift_L d c t2)" |
  "shift_L d c (<l:=t> as A) = <l:= shift_L d c t> as A" |
  "shift_L d c (Case t of <L:=I> \<Rightarrow> LT) = 
    (Case (shift_L d c t) of <L:= (map (\<lambda>x. if x\<ge> c then (nat (int x + d)) else x) I)> \<Rightarrow> map (shift_L d c) LT)"|
  "shift_L d c (Fixpoint t) = Fixpoint (shift_L d c t)"


function subst_L :: "nat \<Rightarrow> lterm \<Rightarrow> lterm \<Rightarrow> lterm" where
  "subst_L j s LTrue = LTrue" |
  "subst_L j s LFalse = LFalse" |
  "subst_L j s (LIf t1 t2 t3) = LIf (subst_L j s t1) (subst_L j s t2) (subst_L j s t3)" |
  "subst_L j s (LVar k) = (if k = j then s else LVar k)" |
  "subst_L j s (LNat n) = LNat n"|
  "subst_L j s (UMinus t) = UMinus (subst_L j s t)"|
  "subst_L j s (IsZero t) = IsZero (subst_L j s t)"|
  "subst_L j s (LPlus t1 t2) = LPlus (subst_L j s t1) (subst_L j s t2)"|
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
      | Inr y \<Rightarrow> (if j=y then t2 else subst_L j s t2))" |
  "subst_L j s (<l:=t> as T') =  <l:=subst_L j s t> as T'" |
  "subst_L j s (Case t of <L:=I> \<Rightarrow> LT) = 
    (Case (subst_L j s t) of <L:=I> \<Rightarrow> map (\<lambda>p. if j=fst p then snd p else subst_L j s (snd p)) (zip I LT))" |
  "subst_L j s (Fixpoint t) = Fixpoint (subst_L j s t)"
by pat_completeness auto

termination
  by (relation "measure (\<lambda>(j,s,t). size t)", auto)
      (metis less_add_Suc1 size_list_estimation' set_zip_rightD lessI not_less)+
  
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
"patterns (LPlus t1 t2)               = patterns t1 @ patterns t2" |
"patterns (UMinus t)                  = patterns t" |
"patterns (IsZero t)                  = patterns t" |
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
(*"patterns (Let pattern p := t1 in t2) = patterns t1 @ filter (\<lambda>x. x\<notin> set(Pvars p))(patterns t2)" |*)
"patterns (Let pattern p := t1 in t2) = patterns t1 @ patterns t2" |
"patterns (inl t as T') =  patterns t" |
"patterns (inr t as T') =  patterns t" |
"patterns (Case t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2) = patterns t @ patterns t1 @ patterns t2" |
"patterns (<l:=t> as T') =  patterns t" |
"patterns (Case t of <L:=I> \<Rightarrow> LT) = patterns t @ list_iter (\<lambda>e r. e @ r) [] (map (patterns) LT)" |
"patterns (Fixpoint t) = patterns t"|
"patterns t = []"


inductive is_value_L :: "lterm \<Rightarrow> bool" where
  VTrue : "is_value_L LTrue" |
  VFalse: "is_value_L LFalse" |
  VAbs  :"is_value_L (LAbs T' t)" |
  VUnit :"is_value_L unit" |
  VNat  : "is_value_L (LNat n)"|
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
  "FV (LNat n) = {}"|
  "FV (LPlus t1 t2) = FV t1 \<union> FV t2"|
  "FV (UMinus t) = FV t"|
  "FV (IsZero t) = FV t"|
  "FV (LAbs T1 t) = image (\<lambda>x. x - 1) (FV t - {0})" |
  "FV (LApp t1 t2) = FV t1 \<union> FV t2" |
  "FV unit = {}" |
  "FV (Seq t1 t2) = FV t1 \<union> FV t2" |
  "FV (t as A) = FV t" |
  "FV (Let var x := t in t1) = 
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
  "FV (Case t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2) = FV t1 \<union> FV t2" |
  "FV (<L:=t> as A) = FV t" |
  "FV (Case t of <L:=I> \<Rightarrow> LT) = FV t \<union> list_iter (\<lambda>x r. x \<union> r) {} (map FV LT)" |
  "FV (Fixpoint t) = FV t"


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
"fill \<Delta> (LPlus t1 t2)               = LPlus (fill \<Delta> t1) (fill \<Delta> t2)" |
"fill \<Delta> (UMinus t)                  = UMinus (fill \<Delta> t)" |
"fill \<Delta> (IsZero t)                  = IsZero (fill \<Delta> t)" |
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
"fill \<Delta> (<l:=t> as A) =  <l:=(fill \<Delta> t)> as A"|
"fill \<Delta> (Case t of <L:=I> \<Rightarrow> LT) = (Case (fill \<Delta> t) of <L:=I> \<Rightarrow> map (fill \<Delta>) LT)"|
"fill \<Delta> (Fixpoint t) = Fixpoint (fill \<Delta> t)" |
"fill \<Delta> t = t"

fun subterms :: "lterm\<Rightarrow>subterm_set" where
"subterms (LIf c t1 t2)               = Ter c t1 t2" |
"subterms (LAbs A t1)                 = U t1" |
"subterms (LApp t1 t2)                = Bi t1 t2" |
"subterms (LPlus t1 t2)               = Bi t1 t2" |
"subterms (UMinus t)                  = U t" |
"subterms (IsZero t)                  = U t" |
"subterms (Seq t1 t2)                 = Bi t1 t2" |
"subterms (t1 as A)                   = U t1" |
"subterms (Let var x := t1 in t2)     = Bi t1 t2" |
"subterms (\<lbrace>t1,t2\<rbrace>)                   = Bi t1 t2" |
"subterms (Tuple L)                   = UList L" |
"subterms (Record L LT)               = UList LT" |
"subterms (\<pi>1 t)                      = U t" |
"subterms (\<pi>2 t)                      = U t" |
"subterms (\<Pi> i t)                     = U t" |
"subterms (ProjR l t)                 = U t" |
"subterms (Let pattern p := t1 in t2) = Bi t1 t2" |
"subterms (inl t as A) = U t"|
"subterms (inr t as A) = U t"|
"subterms (Case t of Inl x \<Rightarrow> t1 | Inr y \<Rightarrow> t2) = Ter t t1 t2"|
"subterms (<l:=t> as A) =  U t"|
"subterms (Case t of <L:=I> \<Rightarrow> LT) = Comp t LT"|
"subterms (Fixpoint t) = U t" |
"subterms t = Void"

lemma P_pat_subterm_cases:
  "P (patterns t) \<longrightarrow> (\<exists>t1. subterms t = U t1 \<and> P (patterns t1)) \<or>
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