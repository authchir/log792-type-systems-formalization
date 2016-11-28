(*<*)
theory Extended_Typed_Lambda_Calculus
imports
  Main
  "~~/src/HOL/Eisbach/Eisbach"
  "~~/src/HOL/Eisbach/Eisbach_Tools"
  "$AFP/List-Index/List_Index" 
begin
(*>*)

section {* Derived form*}

text{*    
    This part will cover the classical lambda calculus extended with booleans , unit type, 
    type variables and sequence in two different ways. The goal is to show that 
    both implementations are  equivalent up to some isomorphism (e) 
    with respect to evaluation and typing.
*}


subsection {* Definitions *}

(* Redefinition of the typed lambda calculus
   and properties with extended types

   We add base types T(1) T(2) .... and Unit 
 *)

datatype ltype =
  Bool |
  T (num:nat) |
  Unit |
  Fun (domain: ltype) (codomain: ltype) (infixr "\<rightarrow>" 225)

(* internal language definition with Unit only*)
datatype ltermI =
  LTrue |
  LFalse |
  LIf (bool_expr: ltermI) (then_expr: ltermI) (else_expr: ltermI) |
  LVar nat |
  LAbs (arg_type: ltype) (body: ltermI) |
  LApp ltermI ltermI |
  unit


primrec shift_L :: "(int \<Rightarrow> int) \<Rightarrow> ltermI \<Rightarrow> ltermI" where
  "shift_L F LTrue = LTrue" |
  "shift_L F LFalse = LFalse" |
  "shift_L F (LIf t1 t2 t3) = LIf (shift_L F t1) (shift_L F t2) (shift_L F t3)" |
  "shift_L F (LVar k) = LVar (nat (F (int k)))" |
  "shift_L F (LAbs T' t) = LAbs T' (shift_L (\<lambda>x. F (x-1) + 1) t)" |
  "shift_L F (LApp t1 t2) = LApp (shift_L F t1) (shift_L F t2)" |
  "shift_L F unit = unit"

primrec subst_L :: "nat \<Rightarrow> ltermI \<Rightarrow> ltermI \<Rightarrow> ltermI" where
  "subst_L j s LTrue = LTrue" |
  "subst_L j s LFalse = LFalse" |
  "subst_L j s (LIf t1 t2 t3) = LIf (subst_L j s t1) (subst_L j s t2) (subst_L j s t3)" |
  "subst_L j s (LVar k) = (if k = j then s else LVar k)" |
  "subst_L j s (LAbs T' t) = LAbs T' (subst_L (Suc j) (shift_L (\<lambda>x. if x\<ge>0 then x + 1 else x) s) t)" |
  "subst_L j s (LApp t1 t2) = LApp (subst_L j s t1) (subst_L j s t2)" |
  "subst_L j s unit = unit"

(* unit is a value*)
inductive is_value_L :: "ltermI \<Rightarrow> bool" where
  "is_value_L LTrue" |
  "is_value_L LFalse" |
  "is_value_L (LAbs T' t)" |
  "is_value_L unit"

(* 
  a sequence is only valid if FV t2 doesn't contain 0
  so we will only consider shifted term t2 (always a valid term)
*)

abbreviation sequence :: "ltermI\<Rightarrow>ltermI\<Rightarrow>ltermI" (infix ";;" 200) where
 "sequence t1 t2 \<equiv> (LApp (LAbs Unit  (shift_L (\<lambda>x. if x\<ge>0 then x + 1 else x) t2)) t1)"

primrec FV :: "ltermI \<Rightarrow> nat set" where
  "FV LTrue = {}" |
  "FV LFalse = {}" |
  "FV (LIf t1 t2 t3) = FV t1 \<union> FV t2 \<union> FV t3" |
  "FV (LVar x) = {x}" |
  "FV (LAbs T1 t) = image (\<lambda>x. x - 1) (FV t - {0})" |
  "FV (LApp t1 t2) = FV t1 \<union> FV t2" |
  "FV unit = {}"


inductive eval1_L :: "ltermI \<Rightarrow> ltermI \<Rightarrow> bool" where
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
      (shift_L (\<lambda>x. if x\<ge>0 then x - 1 else x) (subst_L 0 (shift_L (\<lambda>x. if x\<ge>0 then x + 1 else x) v2) t12))" 


inductive_cases eval1_LIf_E: "eval1_L (LIf t t1 t2) t'"
inductive_cases eval1_LApp_E: "eval1_L (LApp t1 t2) t'"

type_synonym lcontext = "ltype list"


notation Nil ("\<emptyset>")
abbreviation cons :: "lcontext \<Rightarrow> ltype \<Rightarrow> lcontext" (infixl "|,|" 200) where
  "cons \<Gamma> T' \<equiv> T' # \<Gamma>"
abbreviation elem' :: "(nat \<times> ltype) \<Rightarrow> lcontext \<Rightarrow> bool" (infix "|\<in>|" 200) where
  "elem' p \<Gamma> \<equiv> fst p < length \<Gamma> \<and> snd p = nth \<Gamma> (fst p)"

(* had new typing rule for unit and sequence*)
inductive has_type_L :: "lcontext \<Rightarrow> ltermI \<Rightarrow> ltype \<Rightarrow> bool" ("((_)/ \<turnstile> (_)/ |:| (_))" [150, 150, 150] 150) where
  -- "Rules relating to the type of Booleans"
  has_type_LTrue:
    "\<Gamma> \<turnstile> LTrue |:| Bool" |
  has_type_LFalse:
    "\<Gamma> \<turnstile> LFalse |:| Bool" |
  has_type_LIf:
    "\<Gamma> \<turnstile> t1 |:| Bool \<Longrightarrow> \<Gamma> \<turnstile> t2 |:| T' \<Longrightarrow> \<Gamma> \<turnstile> t3 |:| T' \<Longrightarrow> \<Gamma> \<turnstile> (LIf t1 t2 t3) |:| T'" |

  -- \<open>Rules relating to the type of the constructs of the $\lambda$-calculus\<close>
  has_type_LVar:
    "(x, T') |\<in>| \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> (LVar x) |:| (T')" |
  has_type_LAbs:
    "(\<Gamma> |,| T1) \<turnstile> t2 |:| T2 \<Longrightarrow> \<Gamma> \<turnstile> (LAbs T1 t2) |:| (T1 \<rightarrow> T2)" |
  has_type_LApp:
    "\<Gamma> \<turnstile> t1 |:| (T11 \<rightarrow> T12) \<Longrightarrow> \<Gamma> \<turnstile> t2 |:| T11 \<Longrightarrow> \<Gamma> \<turnstile> (LApp t1 t2) |:| T12" |
  has_type_LUnit:
    "\<Gamma> \<turnstile> unit |:| Unit"

lemma[simp]: "nat (int x + 1) = Suc x" by simp
lemma[simp]: "nat (1 + int x) = Suc x" by simp
lemma[simp]: "nat (int x - 1) = x - 1" by simp

lemma gr_Suc_conv: "Suc x \<le> n \<longleftrightarrow> (\<exists>m. n = Suc m \<and> x \<le> m)"
  by (cases n) auto

lemma toto: 
  "n\<ge>0 \<Longrightarrow> Suc (nat n) = nat (n + 1)"
by simp

lemma shift_comp:
  "shift_L F (shift_L G t) = shift_L (F\<circ>G) t" sorry

lemma FV_shift:
  "FV (shift_L (\<lambda>x. if x \<ge> int c then x+d else x) t) = image (\<lambda>x. if x \<ge> c then  nat (int x + d) else x) (FV t)"
proof (induction t arbitrary: c rule: ltermI.induct)
  case (LAbs T t)
     have same_fun: "(\<lambda>x. (if int c \<le> x - 1 then x - 1 + d else x - 1) + 1) = (\<lambda>x. if int (c + 1) \<le> x then x + d else x)"
          by force        
  
    have 1:" FV (shift_L (\<lambda>x. if int c \<le> x then x + d else x) (LAbs T t)) \<subseteq> (\<lambda>x. if int c \<le> int x then nat (int x + d) else x) ` FV (LAbs T t)"
      proof 
        fix x
        assume H:  "x \<in> FV (shift_L (\<lambda>x. if int c \<le> x then x + d else x) (LAbs T t))"  
        
        obtain x1 where x1_def: "x1 \<in> (\<lambda>x. if c + 1 \<le>  x then nat (int x + d) else x) ` FV t - {0}"
                                "x= x1 - 1 "
          using H[unfolded shift_L.simps FV.simps same_fun LAbs image_iff Bex_def]
          by blast
        obtain x2 where x2_def:"x1 > 0" "x2\<in> FV t"
                               "c + 1 \<le> x2 \<and> x1= nat (int x2 + d) \<or> \<not>c + 1 \<le>  x2 \<and> x1=x2"
          using x1_def(1) image_iff
          by auto
        show "x \<in> (\<lambda>x. if int c \<le> int x then nat (int x + d) else x) ` FV (LAbs T t)"
          by (simp add: image_iff Bex_def, rule disjE[OF x2_def(3)])
              (insert  x1_def(2) x2_def(1,2), rule disjI1,force | force)+
      qed

    have 2:"(\<lambda>x. if int c \<le> int x then nat (int x + d) else x) ` FV (LAbs T t)  \<subseteq> FV (shift_L (\<lambda>x. if int c \<le> x then x + d else x) (LAbs T t))"
      proof 
        fix x
        assume H: "x \<in> (\<lambda>x. if int c \<le> int x then nat (int x + d) else x) ` FV (LAbs T t)"
        
        obtain x1 x2 where x12_def: "x = nat (int x1 + d) \<and> c \<le> x1 \<or> x = x1 \<and> \<not>c \<le> x1"
                                    "x2\<in> FV t - {0}" "x1 = x2 - 1"
          using H[unfolded FV.simps image_iff Bex_def] 
                if_splits(1)[where P="\<lambda>y. x = y"]
          by auto
        have s:"int (c+1) = 1 + int c" by simp
       
        
          
        show "x \<in> FV (shift_L (\<lambda>x. if int c \<le> x then x + d else x) (LAbs T t))"
          apply (rule disjE[OF x12_def(1)])
          prefer 2
          apply (simp add: same_fun[simplified]  LAbs[of "c+1", unfolded s] image_iff Bex_def)
          using x12_def(2,3)                     
          apply force
          apply (simp add: same_fun[simplified] LAbs[of "c+1", unfolded s] image_iff Bex_def)
          apply (cases "int x1 + d\<ge>0")
          apply rule
          apply rule
          prefer 2
          using x12_def(2,3)
          apply force
          apply rule
          apply rule
          using x12_def(2,3) toto[of "int (x2 - Suc 0) + d"]
          apply auto[1]
          apply (simp add: Suc_leI  of_nat_diff)
          apply rule
          apply rule
          prefer 2
          using x12_def(2,3)
          apply force
          apply rule
          apply rule
          using x12_def(2,3)
          (*
              from \<not> 0 \<le> int x1 + d \<rightarrow> d' > int x1 where obtain d' = -d (\<ge>0)
              from x1 = x2 - 1 \<rightarrow> int (x2-1) < d'\<rightarrow> x2 \<le> d'
              Suc 0 = nat (int x1 + d) \<rightarrow> Suc 0 = nat (int (x2 - 1) + d)
              given nat (int (d'+1) +d) = Suc 0 \<rightarrow> x2 = d'+2 contradiction with x2 \<le> d'
          *)          
          sorry
      qed
    show ?case 
      by(rule, insert 1 2, auto)
qed auto

lemma FV_subst:
  "FV (subst_L n t u) = (if n \<in> FV u then (FV u - {n}) \<union> FV t else FV u)"
proof (induction u arbitrary: n t rule: ltermI.induct)
  case (LAbs T u)
  thus ?case sorry
    (*by (auto simp: gr0_conv_Suc image_iff FV_shift[of 1, unfolded int_1],
        (metis DiffI One_nat_def UnCI diff_Suc_1 empty_iff imageI insert_iff nat.distinct(1))+)*)
qed (auto simp: gr0_conv_Suc image_iff FV_shift[of 1, unfolded int_1])



(* inversion, uniqueness and canonical form updated with unit*)
lemma inversion:
  "\<Gamma> \<turnstile> LTrue |:| R \<Longrightarrow> R = Bool"
  "\<Gamma> \<turnstile> LFalse |:| R \<Longrightarrow> R = Bool"
  "\<Gamma> \<turnstile> LIf t1 t2 t3 |:| R \<Longrightarrow> \<Gamma> \<turnstile> t1 |:| Bool \<and> \<Gamma> \<turnstile> t2 |:| R \<and> \<Gamma> \<turnstile> t3 |:| R"
  "\<Gamma> \<turnstile> LVar x |:| R \<Longrightarrow> (x, R) |\<in>| \<Gamma>"
  "\<Gamma> \<turnstile> LAbs T1 t2 |:| R \<Longrightarrow> \<exists>R2. R = T1 \<rightarrow> R2 \<and> \<Gamma> |,| T1 \<turnstile> t2 |:| R2"
  "\<Gamma> \<turnstile> LApp t1 t2 |:| R \<Longrightarrow> \<exists>T11. \<Gamma> \<turnstile> t1 |:| T11 \<rightarrow> R \<and> \<Gamma> \<turnstile> t2 |:| T11"
  "\<Gamma> \<turnstile>  unit |:| R \<Longrightarrow> R = Unit"
  by (auto elim: has_type_L.cases)
  

theorem uniqueness_of_types:
  "\<Gamma> \<turnstile> t |:| T1 \<Longrightarrow> \<Gamma> \<turnstile> t |:| T2 \<Longrightarrow> T1 = T2"
by (induction \<Gamma> t T1 arbitrary: T2 rule: has_type_L.induct)
  (metis prod.sel ltype.sel inversion)+

lemma canonical_forms:
  "is_value_L v \<Longrightarrow> \<Gamma> \<turnstile> v |:| Bool \<Longrightarrow> v = LTrue \<or> v = LFalse"
  "is_value_L v \<Longrightarrow> \<Gamma> \<turnstile> v |:| T1 \<rightarrow> T2 \<Longrightarrow> \<exists>t. v = LAbs T1 t"
  "is_value_L v \<Longrightarrow> \<Gamma> \<turnstile> v |:| Unit \<Longrightarrow> v = unit"
by (auto elim: has_type_L.cases is_value_L.cases)

lemma shift_down:
  "insert_nth n U \<Gamma> \<turnstile> t |:| A \<Longrightarrow> n \<le> length \<Gamma> \<Longrightarrow>
   (\<And>x. x \<in> FV t \<Longrightarrow> x \<noteq> n) \<Longrightarrow> \<Gamma> \<turnstile> shift_L (\<lambda>x. if x\<ge>int n then x - 1 else x) t |:| A"
proof (induction "insert_nth n U \<Gamma>" t A arbitrary: \<Gamma> n rule: has_type_L.induct)
  case (has_type_LAbs V t A)
  from this(1,3,4) show ?case sorry
   (* by (fastforce intro: has_type_L.intros has_type_LAbs.hyps(2)[where n="Suc n"])+*)
qed (fastforce intro: has_type_L.intros simp: nth_append min_def)+

lemma weakening:
  "\<Gamma> \<turnstile> t |:| A \<Longrightarrow> n \<le> length \<Gamma> \<Longrightarrow> insert_nth n S \<Gamma> \<turnstile> shift_L (\<lambda>x. if x\<ge>int n then x + 1 else x) t |:| A"
proof (induction \<Gamma> t A arbitrary: n rule: has_type_L.induct)
  case (has_type_LAbs \<Gamma> T1 t2 T2)
    have same_fun:"(\<lambda>x. (if int n < x then x - 1 + 1 else x - 1) + 1) = (\<lambda>x. if int (Suc n) \<le> x then x + 1 else x)"
      by force
    show ?case
      using has_type_LAbs(1,3) has_type_LAbs.IH[where n="Suc n", unfolded same_fun[symmetric]] 
      by (auto intro: has_type_L.intros)
qed (auto simp: nth_append min_def intro: has_type_L.intros)


(* sequence specific lemmas 
    evaluation
    typing
*)

theorem eval1_Lseq: 
  "eval1_L t1 t1' \<Longrightarrow> eval1_L (t1;;t2) (t1';;t2)"
  by (auto intro: eval1_L.intros is_value_L.intros)

lemma subst_free_var_only: "x\<notin>FV t \<Longrightarrow> subst_L x t1 t = t"
by (induction t arbitrary:t1 x, force+)

(*lemma shift_shift_invert: "a>0 \<Longrightarrow> shift_L (-a) b (shift_L a b t) = t"
by(induction t arbitrary: a b, auto)*)

lemma shift_id:
  "shift_L id t= id t"
by (induction t, auto)

theorem eval1_Lseq_next:
  " eval1_L (unit ;; t2) t2"
proof -  
  let ?s10="(\<lambda>x. if x\<ge>0 then x + 1 else x)" and
      ?sm10 = "(\<lambda>x. if x\<ge>0 then x - 1 else x)"
  have A:"eval1_L (unit ;; t2) (shift_L ?sm10 (subst_L 0 (shift_L ?s10 unit) (shift_L ?s10 t2)))"
    using eval1_LApp_LAbs
          "is_value_L.simps"
     by presburger

  have B:" subst_L 0 (shift_L ?s10 unit) (shift_L ?s10 t2) = (shift_L ?s10 t2)"
      using subst_free_var_only[of 0 "shift_L ?s10 t2" "unit"]  
            FV_shift[of 0 1 t2]
            image_iff
      by auto
  have C:"(\<lambda>x. if 0 \<le> x then x - 1 else x) \<circ> (\<lambda>x. if 0 \<le> x then x + 1 else x) = id" sorry
  show ?thesis 
    using A[unfolded B]
          shift_comp[of ?sm10 ?s10 t2, unfolded C shift_id]
    by force        
qed    

lemma eval1_LSeq_E:
  fixes t1 t2 t':: ltermI
  assumes H:"eval1_L (t1;;t2) t'" and 
          step1: "\<And>t1'. eval1_L t1 t1' \<Longrightarrow> t' = (t1';;t2) \<Longrightarrow> P" and
          step2: "t1 = unit \<Longrightarrow> t' = t2 \<Longrightarrow> P" and
          step3: "is_value_L t1 \<Longrightarrow> t' = t2 \<Longrightarrow> P"  
  shows "P"
using assms
proof (induction "(t1;;t2)" t' rule:eval1_L.induct)
  case (eval1_LApp_LAbs)
    let ?s10="(\<lambda>x. if x\<ge>0 then x + 1 else x)" and
        ?sm10 = "(\<lambda>x. if x\<ge>0 then x - 1 else x)"
    have annul_fun:"(\<lambda>x. if 0 \<le> x then x - 1 else x) \<circ> (\<lambda>x. if 0 \<le> x then x + 1 else x) = id" sorry
    have "shift_L ?sm10 (subst_L 0 (shift_L ?s10 t1) (shift_L ?s10 t2)) = t2"
      using subst_free_var_only[of 0 "shift_L ?s10 t2"  "shift_L ?s10 t1" ]
            FV_shift[of 0 1 t2]
            image_iff
            shift_comp[of ?sm10 ?s10, unfolded annul_fun shift_id] 
      by force
    with "eval1_LApp_LAbs.hyps" "eval1_LApp_LAbs.prems"(3)
      show ?case
        by auto
qed (auto elim: eval1_L.cases)
 

theorem has_type_LSeq: 
  "\<Gamma> \<turnstile> t1 |:| Unit \<Longrightarrow> \<Gamma> \<turnstile> t2 |:| A \<Longrightarrow> \<Gamma> \<turnstile> (t1 ;; t2) |:| A"
using has_type_LAbs has_type_LApp
      weakening[of _ t2 A 0 Unit]
by fastforce
  
(* external language definition with sequence as a term*)
datatype ltermE =
  LETrue |
  LEFalse |
  LEIf (bool_expr: ltermE) (then_expr: ltermE) (else_expr: ltermE) |
  LEVar nat |
  LEAbs (arg_type: ltype) (body: ltermE) |
  LEApp ltermE ltermE |
  unitE |
  SeqE (fp: ltermE) (sp: ltermE)

primrec shift_LE :: "(int \<Rightarrow> int) \<Rightarrow> ltermE \<Rightarrow> ltermE" where
  "shift_LE F LETrue = LETrue" |
  "shift_LE F LEFalse = LEFalse" |
  "shift_LE F (LEIf t1 t2 t3) = LEIf (shift_LE F t1) (shift_LE F t2) (shift_LE F t3)" |
  "shift_LE F (LEVar k) = LEVar (nat (F (int k)))" |
  "shift_LE F (LEAbs T' t) = LEAbs T' (shift_LE (\<lambda>x. F (x-1) + 1) t)" |
  "shift_LE F (LEApp t1 t2) = LEApp (shift_LE F t1) (shift_LE F t2)" |
  "shift_LE F unitE = unitE" |
  "shift_LE F (SeqE t1 t2) = 
SeqE (shift_LE F t1) (shift_LE F t2)"

primrec subst_LE :: "nat \<Rightarrow> ltermE \<Rightarrow> ltermE \<Rightarrow> ltermE" where
  "subst_LE j s LETrue = LETrue" |
  "subst_LE j s LEFalse = LEFalse" |
  "subst_LE j s (LEIf t1 t2 t3) = LEIf (subst_LE j s t1) (subst_LE j s t2) (subst_LE j s t3)" |
  "subst_LE j s (LEVar k) = (if k = j then s else LEVar k)" |
  "subst_LE j s (LEAbs T' t) = LEAbs T' (subst_LE (Suc j) (shift_LE (\<lambda>x. if x\<ge>0 then x + 1 else x) s) t)" |
  "subst_LE j s (LEApp t1 t2) = LEApp (subst_LE j s t1) (subst_LE j s t2)" |
  "subst_LE j s unitE = unitE" |
  "subst_LE j s (SeqE t1 t2) = SeqE (subst_LE j s t1) (subst_LE j s t2)"
  
(* unit is a value*)
inductive is_value_LE :: "ltermE \<Rightarrow> bool" where
  "is_value_LE LETrue" |
  "is_value_LE LEFalse" |
  "is_value_LE (LEAbs T' t)" |
  "is_value_LE unitE"

primrec FVE :: "ltermE \<Rightarrow> nat set" where
  "FVE LETrue = {}" |
  "FVE LEFalse = {}" |
  "FVE (LEIf t1 t2 t3) = FVE t1 \<union> FVE t2 \<union> FVE t3" |
  "FVE (LEVar x) = {x}" |
  "FVE (LEAbs T1 t) = image (\<lambda>x. x - 1) (FVE t - {0})" |
  "FVE (LEApp t1 t2) = FVE t1 \<union> FVE t2" |
  "FVE unitE = {}" |
  "FVE (SeqE t1 t2) = FVE t1 \<union> FVE t2"

inductive eval1_LE :: "ltermE \<Rightarrow> ltermE \<Rightarrow> bool" where
  -- "Rules relating to the evaluation of Booleans"
  eval1_LEIf_LTrue:
    "eval1_LE (LEIf LETrue t2 t3) t2" |
  eval1_LEIf_LFalse:
    "eval1_LE (LEIf LEFalse t2 t3) t3" |
  eval1_LEIf:
    "eval1_LE t1 t1' \<Longrightarrow> eval1_LE (LEIf t1 t2 t3) (LEIf t1' t2 t3)" |

  -- "Rules relating to the evaluation of function application"
  eval1_LEApp1:
    "eval1_LE t1 t1' \<Longrightarrow> eval1_LE (LEApp t1 t2) (LEApp t1' t2)" |
  eval1_LEApp2:
    "is_value_LE v1 \<Longrightarrow> eval1_LE t2 t2' \<Longrightarrow> eval1_LE (LEApp v1 t2) (LEApp v1 t2')" |
  eval1_LEApp_LEAbs:
    "is_value_LE v2 \<Longrightarrow> eval1_LE (LEApp (LEAbs T' t12) v2)
      (shift_LE (\<lambda>x. if x\<ge>0 then x-1 else x) (subst_LE 0 (shift_LE (\<lambda>x. if x\<ge>0 then x+1 else x) v2) t12))" |
  
  -- "Rules relating to evaluation of sequence"
  
  eval1_LE_E_Seq:
    "eval1_LE t1 t1' \<Longrightarrow> eval1_LE (SeqE t1 t2) (SeqE t1' t2)" |
  eval1_LE_E_Seq_Next:
    "eval1_LE (SeqE unitE t2) t2"


inductive_cases eval1_LEIf_E: "eval1_LE (LEIf t t1 t2) t'"
inductive_cases eval1_LEApp_E: "eval1_LE (LEApp t1 t2) t'"
inductive_cases eval1_LESeq_E: "eval1_LE (SeqE t1 t2) t'"

(* had new typing rule for unit and sequence*)
inductive has_type_LE :: "lcontext \<Rightarrow> ltermE \<Rightarrow> ltype \<Rightarrow> bool" ("((_)/ \<turnstile>\<^sup>E (_)/ |:| (_))" [150, 150, 150] 150) where
  -- "Rules relating to the type of Booleans"
  has_type_LETrue:
    "\<Gamma> \<turnstile>\<^sup>E LETrue |:| Bool" |
  has_type_LEFalse:
    "\<Gamma> \<turnstile>\<^sup>E LEFalse |:| Bool" |
  has_type_LEIf:
    "\<Gamma> \<turnstile>\<^sup>E t1 |:| Bool \<Longrightarrow> \<Gamma> \<turnstile>\<^sup>E t2 |:| T' \<Longrightarrow> \<Gamma> \<turnstile>\<^sup>E t3 |:| T' \<Longrightarrow> \<Gamma> \<turnstile>\<^sup>E (LEIf t1 t2 t3) |:| T'" |

  -- \<open>Rules relating to the type of the constructs of the $\lambda$-calculus\<close>
  has_type_LEVar:
    "(x, T') |\<in>| \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile>\<^sup>E (LEVar x) |:| (T')" |
  has_type_LEAbs:
    "(\<Gamma> |,| T1) \<turnstile>\<^sup>E t2 |:| T2 \<Longrightarrow> \<Gamma> \<turnstile>\<^sup>E (LEAbs T1 t2) |:| (T1 \<rightarrow> T2)" |
  has_type_LEApp:
    "\<Gamma> \<turnstile>\<^sup>E t1 |:| (T11 \<rightarrow> T12) \<Longrightarrow> \<Gamma> \<turnstile>\<^sup>E t2 |:| T11 \<Longrightarrow> \<Gamma> \<turnstile>\<^sup>E (LEApp t1 t2) |:| T12" |
  
  has_type_LEUnit:
    "\<Gamma> \<turnstile>\<^sup>E unitE |:| Unit " |  
  -- "Rule relating to sequence"
  has_type_LESeqE:
    "0\<notin>FVE t2 \<Longrightarrow> \<Gamma> \<turnstile>\<^sup>E t1 |:| Unit \<Longrightarrow> \<Gamma> \<turnstile>\<^sup>E t2 |:| A \<Longrightarrow> \<Gamma> \<turnstile>\<^sup>E (SeqE t1 t2) |:| A"

lemma inversionE:
  "\<Gamma> \<turnstile>\<^sup>E LETrue |:| R \<Longrightarrow> R = Bool"
  "\<Gamma> \<turnstile>\<^sup>E LEFalse |:| R \<Longrightarrow> R = Bool"
  "\<Gamma> \<turnstile>\<^sup>E LEIf t1 t2 t3 |:| R \<Longrightarrow> \<Gamma> \<turnstile>\<^sup>E t1 |:| Bool \<and> \<Gamma> \<turnstile>\<^sup>E t2 |:| R \<and> \<Gamma> \<turnstile>\<^sup>E t3 |:| R"
  "\<Gamma> \<turnstile>\<^sup>E LEVar x |:| R \<Longrightarrow> (x, R) |\<in>| \<Gamma>"
  "\<Gamma> \<turnstile>\<^sup>E LEAbs T1 t2 |:| R \<Longrightarrow> \<exists>R2. R = T1 \<rightarrow> R2 \<and> \<Gamma> |,| T1 \<turnstile>\<^sup>E t2 |:| R2"
  "\<Gamma> \<turnstile>\<^sup>E LEApp t1 t2 |:| R \<Longrightarrow> \<exists>T11. \<Gamma> \<turnstile>\<^sup>E t1 |:| T11 \<rightarrow> R \<and> \<Gamma> \<turnstile>\<^sup>E t2 |:| T11"
  "\<Gamma> \<turnstile>\<^sup>E unitE |:| R \<Longrightarrow> R = Unit"
  "\<Gamma> \<turnstile>\<^sup>E SeqE t1 t2 |:| R \<Longrightarrow> \<exists>A. R = A \<and> \<Gamma> \<turnstile>\<^sup>E t2 |:| A \<and> \<Gamma> \<turnstile>\<^sup>E t1 |:| Unit \<and> 0\<notin>FVE t2"
  by (auto elim: has_type_LE.cases)

lemma canonical_formsE:
  "is_value_LE v \<Longrightarrow> \<Gamma> \<turnstile>\<^sup>E v |:| Bool \<Longrightarrow> v = LETrue \<or> v = LEFalse"
  "is_value_LE v \<Longrightarrow> \<Gamma> \<turnstile>\<^sup>E v |:| T1 \<rightarrow> T2 \<Longrightarrow> \<exists>t. v = LEAbs T1 t"
  "is_value_LE v \<Longrightarrow> \<Gamma> \<turnstile>\<^sup>E v |:| Unit \<Longrightarrow> v = unitE"
by (auto elim: has_type_LE.cases is_value_LE.cases)
  

lemma FVE_shift:
  "FVE (shift_LE (\<lambda>x. if x \<ge> c then x+d else x) t) = image (\<lambda>x. if int x \<ge> c then  nat (int x + d) else x) (FVE t)"
proof (induction t arbitrary: c rule: ltermE.induct)
  case (LEAbs T t)
    show ?case 
  (*by (auto simp: gr_Suc_conv image_iff) force+*) sorry
qed auto

lemma weakeningE:
  "\<Gamma> \<turnstile>\<^sup>E t |:| A \<Longrightarrow> n \<le> length \<Gamma> \<Longrightarrow> insert_nth n S \<Gamma> \<turnstile>\<^sup>E shift_LE (\<lambda>x. if x\<ge>int n then x+1 else x) t |:| A"
proof (induction \<Gamma> t A arbitrary: n rule: has_type_LE.induct)
  case (has_type_LEAbs \<Gamma> T1 t2 T2)
    have same_fun:"(\<lambda>x. (if int n < x then x - 1 + 1 else x - 1) + 1) = (\<lambda>x. if int (Suc n) \<le> x then x + 1 else x)"
      by force
    show ?case
      using has_type_LEAbs(1,3) has_type_LEAbs.IH[where n="Suc n", unfolded same_fun[symmetric]] 
      by (auto intro: has_type_LE.intros)
next
  case (has_type_LESeqE t2 \<Gamma> t1 A)
    show ?case
      using has_type_LESeqE(1)
            FVE_shift[of "int n" 1 ]
            has_type_LESeqE(4,5,6)
      by (auto intro: has_type_LE.intros)
qed (auto simp: nth_append min_def intro: has_type_LE.intros)
 
(* Theorem 11.3.1 Sequence is a derived form*)

(*e is a translation function from external to internal language*)


fun e::"ltermE \<Rightarrow> ltermI" where
  "e LETrue = LTrue" |
  "e LEFalse = LFalse" |
  "e (LEIf t1 t2 t3) = LIf (e t1) (e t2) (e t3)" |
  "e (LEVar x) = LVar x" |
  "e (LEAbs A t1) = LAbs A (e t1)" |
  "e (LEApp t1 t2) = LApp (e t1) (e t2)" |
  "e unitE = unit" |
  "e (SeqE t1 t2) = (e t1 ;; e t2)"

(* 
  This theorem shows that both implementation of sequence are
   equivalent in term of typing and evaluation
*)

method e_elim uses rule1 = (auto intro: e.elims[OF rule1] is_value_LE.intros) 
method sym_then_elim = match premises in I: "A = B" for A and B \<Rightarrow>
            \<open>e_elim rule1: I[symmetric]\<close>

lemma value_equiv: "is_value_LE v1 \<longleftrightarrow> is_value_L (e v1)" (is "?P \<longleftrightarrow> ?Q")
proof
  show "?P \<Longrightarrow> ?Q"
    by (induction rule: is_value_LE.induct, auto intro:"is_value_L.intros")    
next
  show "?Q \<Longrightarrow> ?P" 
    by (induction "e v1" rule: is_value_L.induct, sym_then_elim+)
qed

lemma e_inv:
  "e t = LTrue \<Longrightarrow> t = LETrue"
  "e t = LFalse \<Longrightarrow> t = LEFalse" 
  "e t = LIf c t1 t2 \<Longrightarrow> \<exists>c' t1' t2'. e c'= c \<and>  e t1' = t1 \<and> t = LEIf c' t1' t2' \<and>  e t2' = t2"
  "e t = LAbs A t1 \<Longrightarrow> \<exists>t1'. t = LEAbs A t1' \<and> e t1' = t1"
  "e t = LVar x \<Longrightarrow> t = LEVar x"
  "e t = unit \<Longrightarrow> t = unitE"
  "e t = LApp t1 t2 \<Longrightarrow> \<exists>t1' t2'. e t1' = t1 \<and> e t2' = t2 \<and> t = LEApp t1' t2' 
                        \<or> (\<exists>t3 t3'. t1 = LAbs Unit (shift_L (\<lambda>x. if x\<ge>0 then x+1 else x) t3) \<and> e t3' = t3 \<and> t = SeqE t2' t3')"  
by (auto elim: e.elims)


theorem e_complete:
  fixes t::ltermI
  shows "\<exists>u. e u = t"
by (induction t)(blast intro:e.simps)+
      
theorem equiv_type:
  "\<Gamma> \<turnstile>\<^sup>E t |:| A \<longleftrightarrow> \<Gamma> \<turnstile> (e t) |:| A" (is "?P \<longleftrightarrow> ?Q")
proof 
  show "?P \<Longrightarrow> ?Q" sorry
next
  show "?Q \<Longrightarrow> ?P" sorry
qed

theorem equiv_eval :
  fixes   t t'::ltermE
  assumes welltyped: "\<Gamma> \<turnstile> (e t) |:| A" 
  shows   "(eval1_LE t t') \<longleftrightarrow> (eval1_L (e t) (e t'))" (is "?P \<longleftrightarrow> ?Q")
proof 
  show "?P \<Longrightarrow> ?Q"
    proof(induction t arbitrary: t' A)
      case (LEIf t1 t2 t3) 
        note H=this(4) 
        show ?case
          proof -
            obtain ll :: ltermE where
              f1: "t1 = LETrue \<and> t2 = t' \<or> t1 = LEFalse \<and> t3 = t' \<or> t' = LEIf ll t2 t3 \<and> eval1_LE t1 ll"
              by (metis H eval1_LEIf_E)       
            have "t' = LEIf ll t2 t3 \<and> eval1_LE t1 ll \<longrightarrow> eval1_L (LIf (e t1) (e t2) (e t3)) (LIf (e ll) (e t2) (e t3))"
              using LEIf.IH(1) eval1_LIf H
                by blast
            with f1 show ?thesis
              by (auto intro: "eval1_L.intros"(1,2))            
          qed
    next       
      case (LEApp t1 t2 t')
        note H=this(3)
        show ?case
          proof -
            obtain ll :: ltermE  and A::ltype where
              f1: "t' = LEApp ll t2 \<and> eval1_LE t1 ll
                    \<or>  t' = LEApp t1 ll \<and> is_value_LE t1 \<and> eval1_LE t2 ll \<or> 
                        t' = shift_LE (- 1) 0 (subst_LE 0 (shift_LE 1 0 t2) ll) \<and> is_value_LE t2 \<and> t1 = LEAbs A ll"
              by (metis eval1_LEApp_E H)
            let ?substll="shift_LE (- 1) 0 (subst_LE 0 (shift_LE 1 0 t2) ll)"
           
            have "t' = ?substll \<and> is_value_LE t2 \<and> t1 = LEAbs A ll
                    \<longrightarrow> eval1_L (LApp (e t1) (e t2)) (e ?substll)"  
              using value_equiv[of t2]
                    "LEApp.IH"
                    eval1_LApp_LAbs[of "e t2" A "e ll"]
              (*by simp*) sorry
            with f1 show ?thesis
              by(auto)
                (metis "LEApp.IH" H inversionE(6) eval1_L.intros(4,5) value_equiv)+
          qed
    next
      case (SeqE t1 t2)
        note H=this(3)
        show ?case
          proof -
            obtain ll :: ltermE where
              f1: "t' = SeqE ll t2 \<and> eval1_LE t1 ll \<or> t2 = t' \<and> t1 = unitE"
              by (metis eval1_LESeq_E H)
             then show ?thesis
              by (metis "SeqE.IH" eval1_Lseq eval1_Lseq_next e.simps(7,8))+
          qed
    qed (auto elim: eval1_LE.cases)
next
  from welltyped show "?Q \<Longrightarrow> ?P"
    proof(induction t arbitrary:t' A)
      case LETrue
        thus ?case
          by (induction "e LETrue" "e t'" rule: eval1_L.induct, auto)
    next
      case LEFalse
        thus ?case          
          by (induction "e LEFalse" "e t'" rule: eval1_L.induct, auto)
    next
      case (LEVar x)
        thus ?case          
          by (induction "e (LEVar x)" "e t'" rule: eval1_L.induct, auto)
    next
      case (unitE)
        thus ?case
          by (induction "e unitE" "e t'" rule: eval1_L.induct, auto)
    next
      case (LEAbs A t1 t' B)
        from this(2) show ?case          
          by (induction "e (LEAbs A t1)" "e t'" rule: eval1_L.induct, auto)
    next    
      case (LEIf c t1 t2)           
        note H=this(4) 
        show ?case
          proof -
            obtain ll :: ltermI and u::ltermE where
              f1: "e c = LTrue \<and> e t1 = e t' \<or> e c= LFalse \<and> e t2 = e t' \<or> e t' = LIf ll (e t1) (e t2) \<and> eval1_L (e c) ll \<and> e u = ll"
              using eval1_LIf_E[of "e c" "e t1" "e t2" "e t'"] H e_complete
              by fastforce
            have H1:
              "e t' = LIf ll (e t1) (e t2) \<and> eval1_L (e c) ll \<and> e u = ll \<longrightarrow> eval1_LE (LEIf c t1 t2) (LEIf u t1 t2) \<and>
                 e u = ll \<and> t' = LEIf u t1 t2 "
              sorry                            
            with f1 show ?thesis
              sorry               
          qed          
    next     
      case (SeqE t1 t2)
        note H=this(3)
        from H have A:"eval1_L (e t1;;e t2) (e t')" by simp
        show ?case
          proof -
            obtain ll :: ltermI and u::ltermE where
              f1: "e u = ll \<and> eval1_L (e t1) ll \<and> e t' = (ll;;e t2)  \<or> e t1 = unit \<and> e t' = e t2 \<or>
                    is_value_L (e t1) \<and> e t' = e t2"
              by (metis eval1_LSeq_E[OF A] e_complete) 
            have 1:"is_value_L (e t1) \<and> e t' = e t2 \<Longrightarrow> eval1_LE (SeqE t1 t2) t'"
              sorry
            with f1 show ?case
              sorry                  
          qed
    next
      case (LEApp t1 t2 t' B)
        hence H: "eval1_L (LApp (e t1) (e t2)) (e t')"
          by simp
        show ?case 
          proof -
            obtain ll :: ltermI and u::ltermE and C::ltype where
              f1: "e u = ll \<and> eval1_L (e t1) ll \<and> e t' = LApp ll (e t2)  \<or> 
                    e u = ll \<and> is_value_L (e t1) \<and> eval1_L (e t2) ll \<and> e t' = LApp (e t1) ll \<or>
                    is_value_L (e t2) \<and> e u = ll  \<and> e t1 = LAbs C ll \<and> e t' = shift_L (- 1) 0 (subst_L 0 (shift_L 1 0 (e t2)) ll)"
              by (metis eval1_LApp_E[OF H] e_complete)
            let ?substll = "shift_L (- 1) 0 (subst_L 0 (shift_L 1 0 (e t2)) (e u))"
                and ?substll1 = "shift_LE (- 1) 0 (subst_LE 0 (shift_LE 1 0 t2) u)"
            have "is_value_L (e t2) \<and> e u = ll \<and> e t1 = LAbs C ll \<and> e t' = ?substll 
                    \<Longrightarrow> eval1_LE (LEApp t1 t2) ?substll1"
              using e_inv(4)[of t1 C "e u"]
                    value_equiv[of t2]  
                    eval1_LEApp_LEAbs
              sorry
            with f1 show ?case sorry
          qed 
    qed
qed    

