theory Lc
imports Main 
         List_extra
          "$AFP/List-Index/List_Index"

begin

datatype ltype =
  T (num:nat) |
  Unit |  
  Fun (domain: ltype) (codomain: ltype) (infixr "\<rightarrow>" 225)
 
datatype lterm =
  LVar nat |
  LAbs (arg_type: ltype) (body: lterm) |
  LApp lterm lterm |
  unit |
  LetBinder nat lterm lterm ("Let/ var/ (_)/ :=/ (_)/ in/ (_)" [100,120,150] 250)

fun shift_L :: "int \<Rightarrow> nat \<Rightarrow> lterm \<Rightarrow> lterm" where
  "shift_L d c (LVar k) = LVar (if k < c then k else nat (int k + d))" |
  "shift_L d c (LAbs T' t) = LAbs T' (shift_L d (Suc c) t)" |
  "shift_L d c (LApp t1 t2) = LApp (shift_L d c t1) (shift_L d c t2)" |
  "shift_L d c unit = unit" |
  "shift_L d c (Let var x := t in t1) = 
    (if x> c then Let var (nat (int x + d)) := (shift_L d c t) in (shift_L d c t1)
     else  Let var x := (shift_L d c t) in (shift_L d (Suc c) t1)
     )" 

fun subst_L :: "nat \<Rightarrow> lterm \<Rightarrow> lterm \<Rightarrow> lterm" where
  "subst_L j s (LVar k) = (if k = j then s else LVar k)" |
  "subst_L j s (LAbs T' t) = LAbs T' (subst_L (Suc j) (shift_L 1 0 s) t)" |
  "subst_L j s (LApp t1 t2) = LApp (subst_L j s t1) (subst_L j s t2)" |
  "subst_L j s unit = unit" |
  "subst_L j s (Let var x := t in t1) = 
  ((Let var x := (subst_L j s t) in (subst_L (if j \<ge> x then Suc j else j) (shift_L 1 x s) t1)))"

inductive is_value_L :: "lterm \<Rightarrow> bool" where
  VAbs  :"is_value_L (LAbs T' t)" |
  VUnit :"is_value_L unit" 

fun FV :: "lterm \<Rightarrow> nat set" where
  "FV (LVar x) = {x}" |
  "FV (LAbs T1 t) = image (\<lambda>x. x - 1) (FV t - {0})" |
  "FV (LApp t1 t2) = FV t1 \<union> FV t2" |
  "FV unit = {}" |
  "FV (Let var x := t in t1) = image (\<lambda>y. if (y>x) then y-1 else y) (FV t1 -{x}) \<union> FV t"

inductive eval1_L :: "lterm \<Rightarrow> lterm \<Rightarrow> bool" where
  -- "Rules relating to the evaluation of function application"
  eval1_LApp1:
    "eval1_L t1 t1' \<Longrightarrow> eval1_L (LApp t1 t2) (LApp t1' t2)" |
  eval1_LApp2:
    "is_value_L v1 \<Longrightarrow> eval1_L t2 t2' \<Longrightarrow> eval1_L (LApp v1 t2) (LApp v1 t2')" |
  eval1_LApp_LAbs:
    "is_value_L v2 \<Longrightarrow> eval1_L (LApp (LAbs T' t12) v2)
      (shift_L (-1) 0 (subst_L 0 (shift_L 1 0 v2) t12))" |

 -- "Rules relating to evaluation of letbinder"
  eval1_L_LetV:
    "is_value_L v1 \<Longrightarrow> eval1_L (Let var x := v1 in t2) (shift_L (-1) x (subst_L x (shift_L 1 x v1) t2))" |
  eval1_L_Let:
    "eval1_L t1 t1' \<Longrightarrow> eval1_L (Let var x := t1 in t2) (Let var x := t1' in t2)"

type_synonym lcontext = "ltype list"
type_synonym pcontext = "(nat \<rightharpoonup> ltype)"

notation Nil ("\<emptyset>")
abbreviation cons :: "lcontext \<Rightarrow> ltype \<Rightarrow> lcontext" (infixl "|,|" 200) where
  "cons \<Gamma> T' \<equiv> T' # \<Gamma>"
abbreviation elem' :: "(nat \<times> ltype) \<Rightarrow> lcontext \<Rightarrow> bool" (infix "|\<in>|" 200) where
  "elem' p \<Gamma> \<equiv> fst p < length \<Gamma> \<and> snd p = nth \<Gamma> (fst p)"


inductive has_type_L :: "lcontext \<Rightarrow> lterm \<Rightarrow> pcontext \<Rightarrow> bool \<Rightarrow> ltype \<Rightarrow> bool" ("((_)/ \<turnstile> \<lparr>(_)|;|(_),(_)\<rparr>/ |:| (_))" [150, 150, 150, 150,150] 150) where
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
  has_type_Let:
    "x\<le>length \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>t1|;| \<sigma>,f\<rparr> |:| A \<Longrightarrow> (insert_nth x A \<Gamma>) \<turnstile> \<lparr> t2|;| \<sigma>,f\<rparr> |:| B \<Longrightarrow> 
      \<Gamma> \<turnstile> \<lparr>Let var x := t1 in t2|;| \<sigma>,f\<rparr> |:| B"

lemma pp2: "nat (int x + 1) = Suc x" by simp
lemma pp3: "nat (1 + int x) = Suc x" by simp
lemma pp4: "nat (int x - 1) = x - 1" by simp


lemma gr_Suc_conv: "Suc x \<le> n \<longleftrightarrow> (\<exists>m. n = Suc m \<and> x \<le> m)"
  by (cases n) auto

lemma FV_shift:
  "FV (shift_L (int d) c t) = image (\<lambda>x. if x \<ge> c then x + d else x) (FV t)"
proof (induction t arbitrary: c rule: lterm.induct)
  case (LAbs T t)      
    thus ?case           
      by (auto simp: gr_Suc_conv image_iff) force+
next 
  case (LetBinder x t1 t2)
    note hyps=this
    let ?S1 =" FV (shift_L (int d) c (Let var x := t1 in t2))" and
        ?S2 = "(\<lambda>x. if c \<le> x then x + d else x) ` FV (Let var x := t1 in t2)"
    have "c \<le> x \<Longrightarrow> ?S1 \<subseteq> ?S2"
      apply (simp add: image_def hyps Int_Collect Bex_def)
      apply meson
      apply rule
      apply simp
      apply (smt Nat.add_diff_assoc2 Suc_pred le_antisym less_Suc0 nat_int nat_int_add not_le not_less_eq_eq of_nat_0 of_nat_less_iff zless_nat_conj)
      apply rule
      apply simp_all
      apply (force+)[3]
      apply rule
      apply simp_all
      apply (metis Nat.add_diff_assoc2 One_nat_def Suc_leI Suc_le_lessD diff_Suc_1 gr_Suc_conv less_irrefl_nat zero_less_Suc)
      apply force
      apply auto[1]
      by fast
    moreover have "c \<le> x \<Longrightarrow> ?S2 \<subseteq> ?S1"
      apply (simp add: image_def hyps Int_Collect Bex_def)
      apply meson
      apply rule
      apply simp
      defer
      apply force
      apply rule
      apply simp
      apply meson
      apply simp_all
apply (metis Suc_leI le_add1 less_le_trans)
apply (metis Suc_leI add.commute trans_less_add2)
apply (metis Suc_leI add.commute trans_less_add2)
apply (metis Suc_leI add.commute trans_less_add2)
apply (metis Suc_pred add_gr_0 lessI less_le_trans less_nat_zero_code not_less_eq_eq)
apply (metis Suc_leI add.commute trans_less_add2)
apply (metis Suc_pred add_gr_0 le0 le_less_trans lessI not_less_eq_eq)
apply (metis Suc_leI add.commute trans_less_add2)
      apply force
      apply meson
      apply simp_all
      apply (metis add.commute add_less_cancel_left less_imp_diff_less nat_int_add not_less)
      apply (metis (no_types, hide_lams) add.commute less_imp_add_positive nat_add_left_cancel_less nat_int nat_less_le of_nat_add trans_less_add1)
      defer
      apply (smt add.commute less_imp_add_positive nat_add_left_cancel_less nat_int nat_less_le of_nat_add trans_less_add1)
      apply (smt add_gr_0 diff_Suc_less le_less_trans nat_eq_iff nat_less_le of_nat_0_le_iff of_nat_0_less_iff)
      apply (smt Suc_pred add_gr_0 le_less_trans less_SucI nat_less_le of_nat_0_le_iff of_nat_0_less_iff of_nat_eq_0_iff)
apply (smt add_gr_0 diff_Suc_less le_less_trans nat_eq_iff nat_less_le of_nat_0_le_iff of_nat_0_less_iff)
apply (smt Suc_pred add_gr_0 le_less_trans less_SucI nat_less_le of_nat_0_less_iff of_nat_le_0_iff)
      apply metis
      apply metis
      apply rule
      apply force
by (smt add.commute less_imp_add_positive nat_add_left_cancel_less nat_int nat_less_le of_nat_add trans_less_add1)

    moreover have "\<not>c\<le>x \<Longrightarrow> ?S1 \<subseteq> ?S2"
      apply (simp add: image_def hyps Int_Collect Bex_def)
      apply meson
      defer
      apply force
      apply blast
      apply fast
      apply rule
      apply simp
      apply meson
apply (smt Nat.add_diff_assoc2 One_nat_def Suc_leI Suc_le_lessD diff_Suc_1 gr_Suc_conv le_add_diff_inverse2 less_imp_le_nat nat_le_linear trans_less_add2 zero_less_Suc)
using Suc_pred apply linarith
apply (smt Nat.add_diff_assoc2 One_nat_def Suc_leI Suc_le_lessD diff_Suc_1 gr_Suc_conv le_add_diff_inverse2 less_imp_le_nat nat_le_linear trans_less_add2 zero_less_Suc)
apply (smt Nat.add_diff_assoc2 One_nat_def Suc_leD Suc_leI diff_Suc_1 gr_Suc_conv less_le_trans not_le zero_less_Suc)
apply (blast+)[3]
by linarith

     moreover have "\<not>c\<le>x \<Longrightarrow> ?S2 \<subseteq> ?S1"
      apply (simp add: image_def hyps Int_Collect Bex_def)
      apply meson
      defer
      apply force
      apply rule
      apply simp
      apply meson
      apply simp_all
      apply (metis Suc_diff_Suc Suc_leI le_add1 le_imp_less_Suc less_le_trans less_nat_zero_code minus_nat.diff_0 not_less)
      apply (metis One_nat_def Suc_leI diff_Suc_1 le_add1 le_imp_less_Suc less_imp_Suc_add less_le_trans)
      apply (metis Suc_leI Suc_pred add.commute gr_Suc_conv trans_less_add2 zero_less_Suc)
      apply (metis Suc_leI Suc_pred add.commute gr_Suc_conv trans_less_add2 zero_less_Suc)
      apply (metis Suc_le_mono Suc_pred add.commute diff_diff_left less_nat_zero_code neq0_conv zero_less_diff)
      by (metis Nat.le_diff_conv2 add.commute add.right_neutral add_Suc_right diff_add_zero diff_is_0_eq less_imp_Suc_add trans_less_add2)
    ultimately show ?case by blast
qed force+

lemma FV_subst:
  "FV (subst_L n t u) = (if n \<in> FV u then (FV u - {n}) \<union> FV t else FV u)"
proof (induction u arbitrary: n t rule: lterm.induct)
  case (LAbs T u)
  thus ?case 
    by (auto simp: gr0_conv_Suc image_iff FV_shift[of 1, unfolded int_1],
        (metis DiffI One_nat_def UnCI diff_Suc_1 empty_iff imageI insert_iff nat.distinct(1))+)
next
  case (LetBinder x t1 t2)
    note hyps=this
    let ?S1=" FV (subst_L n t (Let var x := t1 in t2))" and 
        ?S2="if n \<in> FV (Let var x := t1 in t2) then FV (Let var x := t1 in t2) - {n} \<union> FV t
              else FV (Let var x := t1 in t2)"
    have "x \<le> n \<Longrightarrow> ?S1 \<subseteq> ?S2"
      apply (simp add: image_def hyps Int_Collect Bex_def FV_shift[of 1, unfolded int_1])
      apply (cases "Suc n \<in> FV t2")
      apply simp_all
      apply (cases "n \<in> FV t1")
      apply simp_all
      apply meson
      apply (force+)[6]
      apply meson
      apply (force+)[3]
apply (metis One_nat_def diff_Suc_1 le_imp_less_Suc)
apply (metis One_nat_def diff_Suc_1 le_imp_less_Suc)
      apply (force+)[2]
apply (metis One_nat_def diff_Suc_1 le_imp_less_Suc)
apply (metis One_nat_def diff_Suc_1 le_imp_less_Suc)
      by (cases "n\<in> FV t1", auto)
      
    moreover have "x\<le>n \<Longrightarrow> ?S2 \<subseteq> ?S1"
      apply (simp add: image_def hyps Int_Collect Bex_def FV_shift[of 1, unfolded int_1])
      apply (cases "Suc n \<in> FV t2")
      apply simp_all
      apply (cases "n \<in> FV t1")
      apply simp_all
      apply meson
      apply auto[1]
      apply (fastforce+)[3]
      defer
      apply (cases "n \<in> FV t1")
      apply auto[2]
      apply meson
      apply auto[1]
      apply rule
      apply simp_all
      apply (metis One_nat_def diff_Suc_1 le_eq_less_or_eq le_imp_less_Suc nat_neq_iff)
      apply (metis One_nat_def diff_Suc_1 le_imp_less_Suc)
      using le_imp_less_Suc apply blast
      apply (metis One_nat_def diff_Suc_1 lessI)
      apply blast
      apply fastforce
      by auto
    moreover have "\<not>x\<le>n \<Longrightarrow> ?S1 \<subseteq> ?S2"
      apply (simp add: image_def hyps Int_Collect Bex_def FV_shift[of 1, unfolded int_1])
      apply (cases "n\<in>FV t2")
      apply (cases "n\<in>FV t1")
      apply simp_all
      apply rule
      apply force
      apply auto[1]
      apply rule
      apply force
      by auto
    moreover have "\<not>x\<le>n \<Longrightarrow> ?S2 \<subseteq> ?S1"
      apply (simp add: image_def hyps Int_Collect Bex_def FV_shift[of 1, unfolded int_1])
      apply (cases "n\<in>FV t2")
      apply (cases "n\<in>FV t1")
      apply simp_all
      apply rule
      apply force
      apply fastforce
      apply rule
      apply force
      apply rule
      apply fastforce
      apply rule
      apply simp
      apply (metis One_nat_def diff_Suc_1 le_eq_less_or_eq le_imp_less_Suc nat_neq_iff)
      apply (cases "n\<in>FV t1")
      apply fastforce
      by force
      
    ultimately show ?case by blast
qed (auto simp: gr0_conv_Suc image_iff FV_shift[of 1, unfolded int_1])



lemma shift_down:
  "insert_nth n U \<Gamma> \<turnstile> \<lparr>t|;|\<sigma>,f\<rparr> |:| A \<Longrightarrow>n \<le> length \<Gamma> \<Longrightarrow>
   (\<And>x. x \<in> FV t \<Longrightarrow> x \<noteq> n) \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>shift_L (- 1) n t|;|\<sigma>,f\<rparr> |:| A"
proof (induction "insert_nth n U \<Gamma>" t \<sigma> f A arbitrary: \<Gamma> n rule: has_type_L.induct)
  case (has_type_LAbs V t A)
  from this(1,3,4) show ?case
    by (fastforce intro: has_type_L.intros has_type_LAbs.hyps(2)[where n="Suc n"])+
next
  case (has_type_Let x t \<sigma> f A t1 B)
    note hyps=this
    have H1:"\<And>x. x \<in> FV t \<Longrightarrow> x \<noteq> n" "\<And>y.\<exists>xa. xa \<in> FV t1 \<and> xa \<noteq> x \<and> y = (if x < xa then xa - 1 else xa)\<Longrightarrow> y\<noteq>n"
            
      using hyps(7)[unfolded FV.simps Bex_def image_def, simplified]
      by auto
    
    hence H2: "n < x \<Longrightarrow> (\<And>y. y\<in> FV t1 \<Longrightarrow> y\<noteq> n)"
      using hyps H1
      by (metis leD nat_less_le)
      
    have "n<x \<Longrightarrow> Suc (nat (int x - 1)) = x"
      using H1
      by fastforce
    hence K:"n<x \<Longrightarrow>  insert_nth x A (insert_nth n U \<Gamma>) =
            insert_nth n U (insert_nth (nat (int x - 1)) A \<Gamma>)"
      using insert_nth_comp(2)[of "(nat (int x - 1))" \<Gamma> n A U]
            hyps(1)
      by force
      
    have K2:"\<And>y. \<not> n < x \<Longrightarrow> y\<in>FV t1 \<Longrightarrow> y\<noteq>Suc n"
      using H1(2)
      by force

    have "n < x \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Let var nat (int x - 1) := shift_L (- 1) n t in shift_L (- 1) n t1|;|\<sigma>,f\<rparr> |:| B"
      apply rule
      using hyps(1)
      apply (simp)
      using hyps(3)[OF _ hyps(6) _, simplified] H1(1)
      apply blast
      using K H2 
    by (metis hyps(5) hyps(6) le_SucI length_insert_nth)
    
    
    moreover have "\<not> n < x \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Let var x := shift_L (- 1) n t in shift_L (- 1) (Suc n) t1|;|\<sigma>,f\<rparr> |:| B"
      apply rule
      using hyps(6)
      apply fastforce
      using hyps(3)[OF _ hyps(6) _ , simplified] H1(1)
      apply blast
      using insert_nth_comp(2)[of "(nat (int x - 1))" \<Gamma> n A U]
            hyps(1) H1(2) hyps(5)[of "Suc n" ] K2
      by (metis Suc_leI hyps(5) hyps(6) insert_nth_comp(2) le_imp_less_Suc length_insert_nth not_le)

    ultimately show ?case by simp
qed (fastforce intro: has_type_L.intros simp: nth_append min_def pp2 pp3 pp4)+


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
  case (has_type_Let x \<Gamma> t1 \<sigma>1 f A t2 B)
    
    have "n < x \<Longrightarrow> (take n \<Gamma> @ drop n \<Gamma> |,| S) \<turnstile> \<lparr>Let var Suc x := shift_L 1 n t1 in shift_L 1 n t2|;| \<sigma>1,f\<rparr> |:| B"
      using has_type_Let(1,4,6)
            has_type_Let(5)[unfolded length_insert_nth, of n] 
            insert_nth_comp(1)[of n \<Gamma> x]
      by (auto intro!: has_type_L.intros(5))
    moreover have "\<not> n<x \<Longrightarrow> (take n \<Gamma> @ drop n \<Gamma> |,| S) \<turnstile> \<lparr>Let var x := shift_L 1 n t1 in shift_L 1 (Suc n) t2|;|\<sigma>1,f\<rparr> |:| B"
      using has_type_Let(4)[OF has_type_Let(6)] has_type_Let(1,6)
      apply simp      
      apply rule
      apply force+      
      using insert_nth_comp(2)[OF has_type_Let(6),of x S A]  
            has_type_Let(5)[unfolded length_insert_nth, of "Suc n" ] 
            has_type_Let(6)[unfolded Suc_le_mono[of n, symmetric]]
            not_less[of n x]
      by fastforce
      
    ultimately show ?case 
      by (simp,metis add.commute nat_int of_nat_Suc)
      
qed (auto intro!: has_type_L.intros simp: nth_append min_def pp2 pp3 pp4)

end