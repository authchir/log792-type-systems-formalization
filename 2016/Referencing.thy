theory Referencing
imports
  Main
  "List-Index.List_Index"
begin
  
datatype ltype=
  Unit | Fun ltype ltype (infixr "\<rightarrow>"  225) | Ref ltype

datatype lterm=
  LVar nat 
| LApp lterm lterm 
| LAbs ltype lterm 
| unit
| ref lterm
| deref lterm ("!(_)" [180]220)
| assign lterm lterm ("(_)::=(_)" [100,195] 220)
| L nat

fun shift_L :: "int \<Rightarrow> nat \<Rightarrow> lterm \<Rightarrow> lterm" where
 "shift_L d c (ref t) = ref (shift_L d c t)"|
 "shift_L d c (t1::=t2) = (shift_L d c t1)::=(shift_L d c t2)"|
 "shift_L d c (LVar k)    = LVar (if k < c then k else nat (int k + d))" |
 "shift_L d c (LApp t t1) = LApp (shift_L d c t) (shift_L d c t1)" |
 "shift_L d c (LAbs T t)  = LAbs T (shift_L d (Suc c) t)" |
 "shift_L d c (!t) =!(shift_L d c t)" |
 "shift_L d c unit = unit" | 
 "shift_L d c (L v) = L v"

fun subst_L :: "nat \<Rightarrow> lterm \<Rightarrow> lterm \<Rightarrow> lterm" where
  "subst_L j s (ref t) = ref (subst_L j s t)"|
  "subst_L j s (t1::=t2) = (subst_L j s t1)::=(subst_L j s t2)"|
  "subst_L j s (LApp t1 t2) = LApp (subst_L j s t1) (subst_L j s t2)" |
  "subst_L j s (LVar k) = (if k = j then s else LVar k)" |
  "subst_L j s (LAbs T t) = LAbs T (subst_L (Suc j) (shift_L 1 0 s) t)"|
  "subst_L j s unit = unit" |
  "subst_L j s (L n) = L n" |
  "subst_L j s (!t) = !(subst_L j s t)"

fun FV ::"lterm \<Rightarrow> nat set" where
  "FV (LVar k) = {k}"|
  "FV (LApp t1 t2) = FV t1 \<union> FV t2"|
  "FV (LAbs T t) =  image (\<lambda>x. x - 1) (FV t - {0})" |
  "FV (t1::=t2) = FV t1 \<union> FV t2"|
  "FV (ref t) = FV t"|
  "FV (!t) = FV t"|
  "FV _ = {}"

inductive is_value_L:: "lterm \<Rightarrow> bool" where
  "is_value_L unit"
| "is_value_L (L n)" 
| "is_value_L (LAbs T t)"

type_synonym lstore   = "lterm list"

abbreviation consS :: "lstore \<Rightarrow> lterm \<Rightarrow> lstore" (infixl "|\<leftarrow>|" 200) where
  "\<mu>|\<leftarrow>|v \<equiv> \<mu>@[v]"

inductive eval1_L :: "lterm \<Rightarrow> lstore \<Rightarrow> lterm \<Rightarrow> lstore \<Rightarrow> bool" where
  \<comment> \<open>Rules relating to the evaluation of function application\<close>
  eval1_LApp1:
    "eval1_L t1 \<mu> t1' \<mu>' \<Longrightarrow> eval1_L (LApp t1 t2) \<mu> (LApp t1' t2) \<mu>'" |
  eval1_LApp2:
    "is_value_L v1 \<Longrightarrow> eval1_L t2 \<mu> t2' \<mu>'\<Longrightarrow> eval1_L (LApp v1 t2) \<mu> (LApp v1 t2') \<mu>'" |
  eval1_LApp_LAbs:
    "is_value_L v2 \<Longrightarrow> eval1_L (LApp (LAbs T' t12) v2) \<mu>
      (shift_L (-1) 0 (subst_L 0 (shift_L 1 0 v2) t12)) \<mu>" | 
  eval1_LRefV:
    "is_value_L v \<Longrightarrow> eval1_L (ref v) \<mu> (L (length \<mu>)) (\<mu>|\<leftarrow>|v)" |
  eval1_LRef:
    "eval1_L t1 \<mu> t1' \<mu>' \<Longrightarrow> eval1_L (ref t1) \<mu> (ref t1') \<mu>'" |
  eval1_LDerefLoc:
    "n<length \<mu> \<Longrightarrow>  eval1_L (!(L n)) \<mu> (\<mu>!n) \<mu>" |
  eval1_LDeref:
    "eval1_L t1 \<mu> t1' \<mu>' \<Longrightarrow> eval1_L (!t1) \<mu> (!t1') \<mu>'" |
  eval1_LAssignLoc:
    "is_value_L v \<Longrightarrow> eval1_L (L n::=v) \<mu> unit (\<mu>[n:=v])"|
  eval1_LAssign1:
    "eval1_L t1 \<mu> t1' \<mu>' \<Longrightarrow> eval1_L (t1::=t2) \<mu> (t1'::=t2) \<mu>'" |
  eval1_LAssign2:
    "is_value_L v1 \<Longrightarrow> eval1_L t2 \<mu> t2' \<mu>'\<Longrightarrow> eval1_L (v1::=t2) \<mu> (v1::=t2') \<mu>'"


inductive_cases eval1_LAppE: "eval1_L (LApp t1 t2) \<mu> t' \<mu>'"

type_synonym lcontext = "ltype list"
type_synonym loc_ctx   = "ltype list"

notation Nil ("\<emptyset>")
abbreviation cons :: "lcontext \<Rightarrow> ltype \<Rightarrow> lcontext" (infixl "|,|" 200) where
  "cons \<Gamma> T' \<equiv> T' # \<Gamma>"
abbreviation elem' :: "(nat \<times> ltype) \<Rightarrow> lcontext \<Rightarrow> bool" (infix "|\<in>|" 200) where
  "elem' p \<Gamma> \<equiv> fst p < length \<Gamma> \<and> snd p = nth \<Gamma> (fst p)"

abbreviation consLoc :: "loc_ctx \<Rightarrow> ltype \<Rightarrow> loc_ctx" (infixl "|,|\<^sub>l" 200) where
  "\<Sigma> |,|\<^sub>l T' \<equiv> \<Sigma>@[T']"
abbreviation elemLoc :: "(nat \<times> ltype) \<Rightarrow> loc_ctx \<Rightarrow> bool" (infix "|\<in>\<^sub>l|" 200) where
  "elemLoc p \<Sigma> \<equiv> fst p < length \<Sigma> \<and> snd p = nth \<Sigma> (fst p)"


text{*  For the typing rule of letbinder, we require to replace the type 
        of the variable by the expected type 
    *}


inductive has_type_L :: "lcontext \<Rightarrow> loc_ctx \<Rightarrow> lterm \<Rightarrow> ltype \<Rightarrow> bool" ("((_)|;|(_)/ \<turnstile> (_)/ |:| (_))" [150,150, 150] 150) where
  \<comment> \<open>Rules relating to the type of Unit\<close>
  has_type_Lunit:
    "\<Gamma>|;|\<Sigma> \<turnstile> unit |:| Unit"|
  \<comment> \<open>Rules relating to the type of the constructs of the $\lambda$-calculus\<close>
  has_type_LVar:
    "(x, T') |\<in>| \<Gamma> \<Longrightarrow> \<Gamma>|;|\<Sigma> \<turnstile> LVar x |:| (T')" |
  has_type_LAbs:
    "(\<Gamma> |,| T1)|;|\<Sigma> \<turnstile> t2 |:| T2 \<Longrightarrow> \<Gamma>|;|\<Sigma> \<turnstile> LAbs T1 t2 |:| (T1 \<rightarrow> T2)" |
  has_type_LApp:
    "\<Gamma>|;|\<Sigma> \<turnstile> t1 |:| T11 \<rightarrow> T12 \<Longrightarrow> \<Gamma>|;|\<Sigma> \<turnstile> t2 |:| T11 \<Longrightarrow> \<Gamma>|;|\<Sigma> \<turnstile> LApp t1 t2 |:| T12" |
  has_type_Loc:
    "(n,T1) |\<in>\<^sub>l| \<Sigma> \<Longrightarrow> \<Gamma>|;|\<Sigma> \<turnstile> L n |:| Ref T1" |
  has_type_Ref:
    "\<Gamma>|;|\<Sigma> \<turnstile> t |:| T1 \<Longrightarrow> \<Gamma>|;|\<Sigma> \<turnstile> ref t |:| Ref T1"|
  has_type_Deref:
    "\<Gamma>|;|\<Sigma> \<turnstile> t |:| Ref T1 \<Longrightarrow> \<Gamma>|;|\<Sigma> \<turnstile> !t |:| T1"|
  has_type_Assign:
    "\<Gamma>|;|\<Sigma> \<turnstile> t1 |:| Ref T1 \<Longrightarrow> \<Gamma>|;|\<Sigma> \<turnstile> t2 |:| T1 \<Longrightarrow> \<Gamma>|;|\<Sigma> \<turnstile> (t1::=t2) |:| Unit"

lemma canonical_forms:
  "is_value_L v \<Longrightarrow> \<Gamma>|;|\<Sigma> \<turnstile> v |:| Unit \<Longrightarrow> v = unit"
  "is_value_L v \<Longrightarrow> \<Gamma>|;|\<Sigma> \<turnstile> v |:| T1 \<rightarrow> T2 \<Longrightarrow> \<exists>t. v = LAbs T1 t"
  "is_value_L v \<Longrightarrow> \<Gamma>|;|\<Sigma> \<turnstile> v |:| Ref T1 \<Longrightarrow>\<exists>n. n<length \<Sigma> \<and> v = L n \<and> \<Sigma>!n=T1"  
by (auto elim: has_type_L.cases is_value_L.cases)

abbreviation well_typed_store::"lcontext \<Rightarrow> loc_ctx \<Rightarrow> lstore \<Rightarrow> bool" ("(_)|;|(_) \<Turnstile> (_)" [150,150,190] 200) where
"\<Gamma>|;|\<Sigma> \<Turnstile> \<mu> \<equiv> (length \<Sigma> = length \<mu>) \<and> (\<forall>i<length \<Sigma>. \<Gamma>|;|\<Sigma> \<turnstile> (\<mu>!i) |:| (\<Sigma>!i))"

lemma[simp]: "nat (int x + 1) = Suc x" by simp
lemma[simp]: "nat (1 + int x) = Suc x" by simp
lemma[simp]: "nat (int x - 1) = x - 1" by simp

lemma gr_Suc_conv: "Suc x \<le> n \<longleftrightarrow> (\<exists>m. n = Suc m \<and> x \<le> m)"
  by (cases n) auto

lemma FV_shift:
  "FV (shift_L (int d) c t) = image (\<lambda>x. if x \<ge> c then x + d else x) (FV t)"
proof (induction t arbitrary: c rule: lterm.induct)
  case (LAbs T t)
  thus ?case  by (auto simp: gr_Suc_conv image_iff) force+
qed auto

lemmas int_1 = of_nat_1[where 'a=int]

lemma FV_subst:
  "FV (subst_L n t u) = (if n \<in> FV u then (FV u - {n}) \<union> FV t else FV u)"
proof (induction u arbitrary: n t rule: lterm.induct)
  case (LAbs T u)
  thus ?case 
    by (auto simp: gr0_conv_Suc image_iff FV_shift[of 1, unfolded int_1],
        (metis DiffI One_nat_def UnCI diff_Suc_1 empty_iff imageI insert_iff nat.distinct(1))+)
qed (auto simp: gr0_conv_Suc image_iff FV_shift[of 1, unfolded int_1])


lemma weakening:
  "\<Gamma> |;|\<Sigma> \<turnstile> t |:| T \<Longrightarrow> n \<le> length \<Gamma> \<Longrightarrow> insert_nth n S \<Gamma> |;|\<Sigma> \<turnstile> shift_L 1 n t |:| T"
proof (induction \<Gamma> \<Sigma> t T arbitrary: n rule: has_type_L.induct)
  case (has_type_LAbs \<Gamma> T1 t2 T2)
    from has_type_LAbs.prems has_type_LAbs.hyps
      has_type_LAbs.IH[where n="Suc n"] 
    show ?case
      by (auto intro: has_type_L.intros)
qed (auto simp: nth_append min_def intro: has_type_L.intros)

lemma substitution:
  "\<Gamma> |;|\<Sigma> \<turnstile> t |:| T \<Longrightarrow>  \<Gamma>|;|\<Sigma> \<turnstile> LVar n |:| S \<Longrightarrow> \<Gamma>|;|\<Sigma> \<turnstile> s |:| S \<Longrightarrow> \<Gamma>|;|\<Sigma> \<turnstile> subst_L n s t |:| T"  
proof (induction \<Gamma> \<Sigma>  t T arbitrary: s n rule: has_type_L.induct)
  case (has_type_LAbs \<Gamma> T1 \<Sigma> t T2)
  thus ?case
    using weakening[where n=0, unfolded insert_nth_def nat.rec]          
    by (force intro!: has_type_L.intros simp: has_type_L.simps[of _ _ "LVar _" _, simplified])
qed (auto intro!: has_type_L.intros simp: has_type_L.simps[of _ _ "LVar _" _, simplified])

lemma store_updt:
  "\<Gamma> |;|\<Sigma> \<Turnstile> \<mu> \<Longrightarrow> i<length \<Sigma> \<Longrightarrow> \<Sigma>!i = T \<Longrightarrow> \<Gamma> |;|\<Sigma> \<turnstile> v |:| T \<Longrightarrow> \<Gamma> |;|\<Sigma> \<Turnstile> (\<mu>[i:=v])"
by (simp, metis  nth_list_update_eq nth_list_update_neq)
       
lemma store_weakening:
  "\<Gamma> |;|\<Sigma> \<turnstile> t |:| T \<Longrightarrow> \<Gamma>|;|(\<Sigma>@\<Sigma>1) \<turnstile> t |:| T" 
by (induction \<Gamma> \<Sigma>  t T arbitrary: \<Sigma>1 rule: has_type_L.induct)
   (auto intro!: has_type_L.intros 
         simp: has_type_L.simps[of _ _ "LVar _" _, simplified] nth_append)

lemma progress:
  "\<Gamma>|;|\<Sigma> \<turnstile> t |:| T \<Longrightarrow> \<Gamma>=\<emptyset> \<Longrightarrow> is_value_L t \<or> (\<forall>\<mu>. \<Gamma>|;|\<Sigma> \<Turnstile> \<mu> \<longrightarrow> (\<exists>t' \<mu>'. eval1_L t \<mu> t' \<mu>'))"
proof (induction t T rule: has_type_L.induct)
  case (has_type_LApp \<Gamma> \<Sigma> t1 T11 T12 t2)
    note hyps=this
    show ?case
      using hyps(3-4)[OF hyps(5)]           
      by (metis eval1_L.intros(1-3) canonical_forms(2)[OF _ hyps(1)])
next
  case (has_type_Ref \<Gamma> \<Sigma> t T1)
    note hyps=this
    show ?case
      using hyps(2)[OF hyps(3)]
            eval1_L.intros(4,5)
      by meson
next
  case (has_type_Deref \<Gamma> \<Sigma> t T1)
    note hyps=this
    show ?case
      using hyps(2)[OF hyps(3)] canonical_forms(3)[OF _ hyps(1)]
            eval1_L.intros(6,7)
      by metis
next
  case (has_type_Assign \<Gamma> \<Sigma> t1 T1 t2)
    note hyps=this
    show ?case
      using hyps(3,4)[OF hyps(5)]
            canonical_forms(3)[OF _ hyps(1)] eval1_L.intros(8-10)
      by metis
qed (simp_all add: is_value_L.intros)

lemma shift_down:
  "insert_nth n U \<Gamma>|;|\<Sigma> \<turnstile> t |:| T \<Longrightarrow> n \<le> length \<Gamma> \<Longrightarrow>
   (\<And>x. x \<in> FV t \<Longrightarrow> x \<noteq> n) \<Longrightarrow> \<Gamma>|;|\<Sigma> \<turnstile> shift_L (- 1) n t |:| T"
proof (induction "insert_nth n U \<Gamma>" \<Sigma> t T arbitrary: \<Gamma> n rule: has_type_L.induct)     
  case (has_type_LAbs V t T)
    from this(1,3,4) show ?case
      by (fastforce intro: has_type_L.intros has_type_LAbs.hyps(2)[where n="Suc n"])+
qed (fastforce intro: has_type_L.intros simp: nth_append min_def)+


lemma preservation:
  "\<Gamma> |;|\<Sigma> \<turnstile> t |:| T \<Longrightarrow> \<Gamma> |;|\<Sigma> \<Turnstile> \<mu> \<Longrightarrow> eval1_L t \<mu> t' \<mu>' \<Longrightarrow> 
    \<exists>\<Sigma>1. \<Gamma> |;| (\<Sigma>@\<Sigma>1) \<Turnstile> \<mu>' \<and> \<Gamma> |;|(\<Sigma>@\<Sigma>1) \<turnstile> t' |:| T"
proof (induction \<Gamma> \<Sigma> t T arbitrary: \<mu>' t' rule: has_type_L.induct)
  case (has_type_LApp \<Gamma> \<Sigma> t1 T11 T12 t2)
    note hyps = this and has_T_Abs= has_type_L.simps[of _ _ "LAbs _ _", simplified]
    
    have 1:"(\<exists>t1'. t' = LApp t1' t2 \<and> eval1_L t1 \<mu> t1' \<mu>') \<Longrightarrow> ?case"
      using has_type_L.intros(4) eval1_L.intros(1)
            hyps(2) store_weakening[of \<Gamma> \<Sigma>] hyps(3)[OF hyps(5)]
      by meson
    
    have 2:"\<exists>t2'. t' = LApp t1 t2' \<and> is_value_L t1 \<and> eval1_L t2 \<mu> t2' \<mu>' \<Longrightarrow> ?case"
      using has_type_L.intros(4) eval1_L.intros(2)
            hyps(1) store_weakening[of \<Gamma> \<Sigma>] hyps(4)[OF hyps(5)]
      by meson

    have 3: "\<exists>T' t12.
        t1 = LAbs T' t12 \<and> t' = shift_L (- 1) 0 (subst_L 0 (shift_L 1 0 t2) t12) \<and> \<mu>' = \<mu> \<and> is_value_L t2
        \<Longrightarrow> ?case"
      proof -
        assume P:"\<exists>T' t12. t1 = LAbs T' t12 \<and> t' = shift_L (- 1) 0 (subst_L 0 (shift_L 1 0 t2) t12) \<and> 
                            \<mu>' = \<mu> \<and> is_value_L t2"
        then obtain T' t1' where H: "t1 = LAbs T' t1'" "t' = shift_L (- 1) 0 (subst_L 0 (shift_L 1 0 t2) t1')"
                                       "\<mu>'= \<mu>" "is_value_L t2"
          by fastforce

        have H':"\<Gamma> |,| T'|;|\<Sigma> \<turnstile> t1' |:| T12" "T'=T11"
          using  hyps(1)[unfolded H(1) has_type_L.simps[of _ _ "LAbs _ _", simplified]]
          by fast+

        have FV_after_subst:"(\<And>x. x \<in> FV (subst_L 0 (shift_L 1 0 t2) t1') \<Longrightarrow> x \<noteq> 0)"
          using FV_subst[of 0 "shift_L 1 0 t2" t1', unfolded FV_shift[of 1 0 t2, simplified]]
          by (cases "0\<in>FV t1'") (fastforce, metis)
          
        show ?thesis
          using substitution[OF H'(1), of 0 T11 "shift_L 1 0 t2", unfolded H'(2)]
                weakening[OF hyps(2),of 0 T', unfolded insert_nth_def nat.rec H'(2), simplified]                 
                hyps(5)[unfolded H(3)[symmetric]]
                shift_down[ of 0 T11 \<Gamma> \<Sigma> "subst_L 0 (shift_L 1 0 t2) t1'" T12, 
                            OF _  _ FV_after_subst, 
                            unfolded insert_nth_def nat.rec H(2)[symmetric], simplified]
                has_type_L.simps[of "\<Gamma>|,|T11" \<Sigma> "LVar 0", simplified]
          by simp
      qed
    show ?case
      using  hyps(6)[unfolded eval1_L.simps[of "LApp t1 t2" \<mu>, simplified]]
             1 2 3
      by force
next
  case (has_type_Ref \<Gamma> \<Sigma> t T1)
    note hyps=this
    have 1:" t' = L (length \<mu>) \<and> \<mu>' = \<mu> |\<leftarrow>| t \<and> is_value_L t \<Longrightarrow> ?case"
      using hyps(1) has_type_L.intros(5)[of "length \<mu>" T1 "\<Sigma>|,|\<^sub>lT1" \<Gamma>, simplified]
            hyps(3) store_weakening
      by (metis length_append_singleton less_Suc_eq nth_append nth_append_length)
    have "(\<exists>t1'. t' = ref t1' \<and> eval1_L t \<mu> t1' \<mu>') \<Longrightarrow> ?case"
      using hyps(2)[OF hyps(3), of _ \<mu>']
            has_type_L.intros(6)[of \<Gamma> "\<Sigma> @ _" _ T1]
      by meson
    with 1 show ?case
      using hyps(4)[unfolded eval1_L.simps[of "ref _",simplified]]
      by fast      
next
  case (has_type_Deref \<Gamma> \<Sigma> t T1)
    note hyps=this
    have 1:"(\<exists>n. t = L n \<and> t' = \<mu> ! n \<and> \<mu>' = \<mu> \<and> n < length \<mu>) \<Longrightarrow> ?case"
      using hyps(3) hyps(1) has_type_L.simps[of \<Gamma> \<Sigma> "L _" "Ref T1", simplified]
      by fastforce

    have "(\<exists>t1'. t' = !t1' \<and> eval1_L t \<mu> t1' \<mu>') \<Longrightarrow> ?case"
      using hyps(2)[OF hyps(3), of _ \<mu>']
            has_type_L.intros(7)[of \<Gamma> "\<Sigma>@_" _ T1]
      by meson

    with 1 show ?case 
      using hyps(4)[unfolded eval1_L.simps[of "!t",simplified]]
      by blast
next
  case (has_type_Assign \<Gamma> \<Sigma> t1 T1 t2)
    note hyps=this
    
    have 1: "\<exists>n. t1 = L n \<and> t' = unit \<and> \<mu>' = \<mu>[n := t2] \<and> is_value_L t2 \<Longrightarrow> ?case" 
      using has_type_L.simps[of \<Gamma> \<Sigma> "L _" "Ref T1", simplified] hyps(1) 
            store_updt[OF hyps(5) _ _ hyps(2)]
            has_type_Lunit
      by fastforce

    have 2: "\<exists>t1'. t' = t1'::=t2 \<and> eval1_L t1 \<mu> t1' \<mu>' \<Longrightarrow> ?case"
      using hyps(3)[OF hyps(5), of _ \<mu>']             
            has_type_L.intros(8)[OF _ store_weakening[OF hyps(2)]]
      by meson

    have "\<exists>t2'. t' = t1::=t2' \<and> is_value_L t1 \<and> eval1_L t2 \<mu> t2' \<mu>' \<Longrightarrow> ?case"
      using hyps(4)[OF hyps(5), of _ \<mu>']
            has_type_L.intros(8)[OF store_weakening[OF hyps(1)]]
      by meson

    with 1 2 show ?case 
      using hyps(6)[unfolded eval1_L.simps[of "t1::=t2", simplified]]
      by blast
qed (auto elim: eval1_L.cases)

end