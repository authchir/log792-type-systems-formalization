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
    let ?S3= "\<lambda>x t1 t2. (if c < x then FV (shift_L (int d) c t1) \<union> 
                  (\<lambda>y. if nat (int x + int d) < y then y - 1 else y) `(FV(shift_L (int d) c t2)- {nat (int x + int d)})
        else FV(shift_L (int d) c t1) \<union> ((\<lambda>y. if x < y then y - 1 else y) ` (FV(shift_L (int d) (Suc c) t2)-{x})))"
       and  ?S4 ="\<lambda>x t1 t2. (\<lambda>x. if c \<le> x then x + d else x) ` ((\<lambda>y. if x < y then y - 1 else y) ` (FV t2 - {x}) \<union> FV t1)"
    have simp_nat: "\<And>x. nat (int x + int d) = x + d" by auto
    have C1:"\<And>x t1 t2. c < x \<Longrightarrow> (\<And>c. FV (shift_L (int d) c t1) = (\<lambda>x. if c \<le> x then x + d else x) ` FV t1)
            \<Longrightarrow> (\<And>c. FV (shift_L (int d) c t2) = (\<lambda>x. if c \<le> x then x + d else x) ` FV t2) \<Longrightarrow>?S3 x t1 t2 \<subseteq> ?S4 x t1 t2"
      proof -
        fix x t1 t2
        assume supc:"c<x" and
               FV_s:"\<And>c. FV (shift_L (int d) c t1) = (\<lambda>x. if c \<le> x then x + d else x) ` FV t1"
                    "\<And>c. FV (shift_L (int d) c t2) = (\<lambda>x. if c \<le> x then x + d else x) ` FV t2"
        have " {y. \<exists>xa. ((\<exists>x. x \<in> FV t2 \<and> c \<le> x \<and> xa = x + d) \<or> xa \<in> FV t2 \<and> \<not> c \<le> xa) \<and>
                  xa \<noteq> nat (int x + int d) \<and> nat (int x + int d) < xa \<and> y = xa - Suc 0} \<subseteq> 
                  {y. \<exists>xa. ((\<exists>xb. xb \<in> FV t2 \<and> xb \<noteq> x \<and> x < xb \<and> xa = xb - Suc 0) \<or>
                 xa \<in> FV t2 \<and> xa \<noteq> x \<and> \<not> x < xa \<or> xa \<in> FV t1) \<and> c \<le> xa \<and> y = xa + d} \<union>
                 ({y. \<exists>xa. xa \<in> FV t2 \<and> xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0} \<union> (FV t2 - {x}) \<inter>
                  {y. \<not> x < y} \<union> FV t1) \<inter>  {x. \<not> c \<le> x}"
          proof (rule, simp)
            fix x1
            assume " \<exists>xaa. ((\<exists>x. x \<in> FV t2 \<and> c \<le> x \<and> xaa = x + d) \<or> xaa \<in> FV t2 \<and> \<not> c \<le> xaa) \<and>
               xaa \<noteq> nat (int x + int d) \<and> nat (int x + int d) < xaa \<and> x1 = xaa - Suc 0"
            then obtain xaa where H1:"((\<exists>x. x \<in> FV t2 \<and> c \<le> x \<and> xaa = x + d) \<or> xaa \<in> FV t2 \<and> \<not> c \<le> xaa)"
               "xaa \<noteq> nat (int x + int d)" "nat (int x + int d) < xaa" "x1 = xaa - Suc 0"
              by blast
            
            let ?goal= "(\<exists>xaa. ((\<exists>xb. xb \<in> FV t2 \<and> xb \<noteq> x \<and> x < xb \<and> xaa = xb - Suc 0) \<or>
                 xaa \<in> FV t2 \<and> xaa \<noteq> x \<and> \<not> x < xaa \<or> xaa \<in> FV t1) \<and> c \<le> xaa \<and> x1 = xaa + d) \<or>
                 ((\<exists>xaa. xaa \<in> FV t2 \<and> xaa \<noteq> x \<and> x < xaa \<and> x1 = xaa - Suc 0) \<or> x1 \<in> FV t2 \<and> x1 \<noteq> x \<and>
                 \<not> x < x1 \<or> x1 \<in> FV t1) \<and> \<not> c \<le> x1"

            have "(\<exists>x. x \<in> FV t2 \<and> c \<le> x \<and> xaa = x + d) \<Longrightarrow> ?goal"
              proof -
                assume "\<exists>x. x \<in> FV t2 \<and> c \<le> x \<and> xaa = x + d"
                then obtain xa where "xa \<in> FV t2" "c \<le> xa" "xaa = xa + d"
                  by blast
                hence "xa \<in> FV t2 \<and> xa \<noteq> x \<and> x < xa \<and> xa - Suc 0 = xa - Suc 0 \<and>
                        c \<le> xa - Suc 0 \<and> x1 = xa - Suc 0 + d"
                  using H1(2-)[unfolded simp_nat] supc
                  by force
                thus ?goal by metis
              qed      
            moreover have "xaa \<in> FV t2 \<and> \<not> c \<le> xaa \<Longrightarrow> ?goal"
              using H1(2-)[unfolded simp_nat] supc
              by simp
            ultimately show ?goal using H1(1) by satx
          qed       
  
        moreover have "({y. \<exists>x. x \<in> FV t2 \<and> c \<le> x \<and> y = x + d} \<union> FV t2 \<inter> {x. \<not> c \<le> x} - {nat (int x + int d)}) \<inter>
                {y. \<not> nat (int x + int d) < y} \<subseteq> {y. \<exists>xa. ((\<exists>xb. xb \<in> FV t2 \<and> xb \<noteq> x \<and> x < xb \<and> xa = xb - Suc 0) \<or>
                 xa \<in> FV t2 \<and> xa \<noteq> x \<and> \<not> x < xa \<or> xa \<in> FV t1) \<and> c \<le> xa \<and> y = xa + d} \<union>
                ({y. \<exists>xa. xa \<in> FV t2 \<and> xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0} \<union> (FV t2 - {x}) \<inter>
                {y. \<not> x < y} \<union> FV t1) \<inter> {x. \<not> c \<le> x}"
          using supc  by force
        
        moreover have " {y. \<exists>x. x \<in> FV t1 \<and> c \<le> x \<and> y = x + d} \<subseteq> {y. \<exists>xa. ((\<exists>xb. xb \<in> FV t2 \<and> xb \<noteq> x \<and> x < xb \<and> xa = xb - Suc 0) \<or>
                         xa \<in> FV t2 \<and> xa \<noteq> x \<and> \<not> x < xa \<or> xa \<in> FV t1) \<and> c \<le> xa \<and> y = xa + d} \<union>
                           ({y. \<exists>xa. xa \<in> FV t2 \<and> xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0} \<union> (FV t2 - {x}) \<inter> {y. \<not> x < y} \<union> FV t1) \<inter>
                           {x. \<not> c \<le> x}"
          using supc by force

        moreover have "FV t1 \<inter> {x. \<not> c \<le> x} \<subseteq> {y. \<exists>xa. ((\<exists>xb. xb \<in> FV t2 \<and> xb \<noteq> x \<and> x < xb \<and> xa = xb - Suc 0) \<or>
                        xa \<in> FV t2 \<and> xa \<noteq> x \<and> \<not> x < xa \<or> xa \<in> FV t1) \<and> c \<le> xa \<and> y = xa + d} \<union>
                          ({y. \<exists>xa. xa \<in> FV t2 \<and> xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0} \<union> (FV t2 - {x}) \<inter> 
                          {y. \<not> x < y} \<union> FV t1) \<inter> {x. \<not> c \<le> x}"
          by force

        ultimately show "?S3 x t1 t2 \<subseteq> ?S4 x t1 t2" 
          using supc 
          by (simp add: image_def FV_s Int_Collect Bex_def)
      qed
    have C2:"\<And>x t1 t2. c < x \<Longrightarrow> (\<And>c. FV (shift_L (int d) c t1) = (\<lambda>x. if c \<le> x then x + d else x) ` FV t1)
            \<Longrightarrow> (\<And>c. FV (shift_L (int d) c t2) = (\<lambda>x. if c \<le> x then x + d else x) ` FV t2) \<Longrightarrow>?S4 x t1 t2 \<subseteq> ?S3 x t1 t2"
      proof -
        fix x t1 t2
        assume supc:"c<x" and
               FV_s:"\<And>c. FV (shift_L (int d) c t1) = (\<lambda>x. if c \<le> x then x + d else x) ` FV t1"
                    "\<And>c. FV (shift_L (int d) c t2) = (\<lambda>x. if c \<le> x then x + d else x) ` FV t2"
        have "c<x \<Longrightarrow> ({y. \<exists>xa. xa \<in> FV t2 \<and> xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0} \<union> (FV t2 - {x}) \<inter> {y. \<not> x < y} \<union> FV t1) \<inter>
                {x. \<not> c \<le> x} \<subseteq> {y. \<exists>xa. ((\<exists>x. x \<in> FV t2 \<and> c \<le> x \<and> xa = x + d) \<or> xa \<in> FV t2 \<and> \<not> c \<le> xa) \<and>
                xa \<noteq> nat (int x + int d) \<and> nat (int x + int d) < xa \<and> y = xa - Suc 0} \<union>
               ({y. \<exists>x. x \<in> FV t2 \<and> c \<le> x \<and> y = x + d} \<union> FV t2 \<inter> {x. \<not> c \<le> x} - {nat (int x + int d)}) \<inter>
               {y. \<not> nat (int x + int d) < y} \<union> ({y. \<exists>x. x \<in> FV t1 \<and> c \<le> x \<and> y = x + d} \<union> FV t1
               \<inter> {x. \<not> c \<le> x})"
           by force  
        moreover have " c < x \<Longrightarrow> {y. \<exists>xa. ((\<exists>xb. xb \<in> FV t2 \<and> xb \<noteq> x \<and> x < xb \<and> xa = xb - Suc 0) \<or>
                        xa \<in> FV t2 \<and> xa \<noteq> x \<and> \<not> x < xa \<or> xa \<in> FV t1) \<and>  c \<le> xa \<and> y = xa + d}
                        \<subseteq> {y. \<exists>xa. ((\<exists>x. x \<in> FV t2 \<and> c \<le> x \<and> xa = x + d) \<or> xa \<in> FV t2 \<and> \<not> c \<le> xa) \<and>
                        xa \<noteq> nat (int x + int d) \<and> nat (int x + int d) < xa \<and> y = xa - Suc 0} \<union>
                        ({y. \<exists>x. x \<in> FV t2 \<and> c \<le> x \<and> y = x + d} \<union> FV t2 \<inter> {x. \<not> c \<le> x} - {nat (int x + int d)}) \<inter>
                        {y. \<not> nat (int x + int d) < y} \<union> ({y. \<exists>x. x \<in> FV t1 \<and> c \<le> x \<and> y = x + d} \<union> FV t1 \<inter> {x. \<not> c \<le> x})"
          proof (rule, simp)
            fix x1
            assume grc:"c<x"  and "\<exists>xaa. ((\<exists>xb. xb \<in> FV t2 \<and> xb \<noteq> x \<and> x < xb \<and> xaa = xb - Suc 0) \<or>
                                    xaa \<in> FV t2 \<and> xaa \<noteq> x \<and> \<not> x < xaa \<or> xaa \<in> FV t1) \<and> c \<le> xaa \<and> x1 = xaa + d"
            then obtain xaa where H1:"(\<exists>xb. xb \<in> FV t2 \<and> xb \<noteq> x \<and> x < xb \<and> xaa = xb - Suc 0) \<or>
                                    xaa \<in> FV t2 \<and> xaa \<noteq> x \<and> \<not> x < xaa \<or> xaa \<in> FV t1" "c \<le> xaa" "x1 = xaa + d"
              by blast
            let ?goal = "(\<exists>xaa. ((\<exists>x. x \<in> FV t2 \<and> c \<le> x \<and> xaa = x + d) \<or> xaa \<in> FV t2 \<and> \<not> c \<le> xaa) \<and>
                          xaa \<noteq> nat (int x + int d) \<and> nat (int x + int d) < xaa \<and> x1 = xaa - Suc 0) \<or>
                         ((\<exists>xa. xa \<in> FV t2 \<and> c \<le> xa \<and> x1 = xa + d) \<or> x1 \<in> FV t2 \<and> \<not> c \<le> x1) \<and>
                         x1 \<noteq> nat (int x + int d) \<and> \<not> nat (int x + int d) < x1 \<or>
                         (\<exists>xa. xa \<in> FV t1 \<and> c \<le> xa \<and> x1 = xa + d) \<or> x1 \<in> FV t1 \<and> \<not> c \<le> x1"
            have "\<exists>xb. xb \<in> FV t2 \<and> xb \<noteq> x \<and> x < xb \<and> xaa = xb - Suc 0 \<Longrightarrow> ?goal"
              proof -
                assume "\<exists>xb. xb \<in> FV t2 \<and> xb \<noteq> x \<and> x < xb \<and> xaa = xb - Suc 0"
                then obtain xb where "xb \<in> FV t2" "xb \<noteq> x" "x < xb" "xaa = xb - Suc 0"
                  by blast
                hence "xb \<in> FV t2 \<and> c \<le> xb \<and> xb+d \<noteq> nat (int x + int d) \<and> 
                        nat (int x + int d) < xb+d \<and> x1 = xb + d - Suc 0"
                  using H1(2-)[unfolded simp_nat] grc
                  by force
                thus ?goal by blast
              qed
            moreover have "xaa \<in> FV t2 \<and> xaa \<noteq> x \<and> \<not> x < xaa \<Longrightarrow> ?goal"
              using H1(2-)[unfolded simp_nat] grc
              by auto
            ultimately show ?goal using H1[unfolded simp_nat] grc by blast
          qed        
        ultimately show "?S4 x t1 t2 \<subseteq> ?S3 x t1 t2" 
          using supc 
          by (simp add: image_def FV_s Int_Collect Bex_def)
              (meson, auto simp add: inf_sup_aci(5))
      qed

     have C4:"\<And>x t1 t2. \<not>c<x \<Longrightarrow> (\<And>c. FV (shift_L (int d) c t1) = (\<lambda>x. if c \<le> x then x + d else x) ` FV t1)
            \<Longrightarrow> (\<And>c. FV (shift_L (int d) c t2) = (\<lambda>x. if c \<le> x then x + d else x) ` FV t2) \<Longrightarrow> ?S3 x t1 t2 \<subseteq> ?S4 x t1 t2"
      proof -
        fix x t1 t2
        assume infc: "\<not>c<x" and
               FV_s: "(\<And>c. FV (shift_L (int d) c t1) = (\<lambda>x. if c \<le> x then x + d else x) ` FV t1)"
                     " (\<And>c. FV (shift_L (int d) c t2) = (\<lambda>x. if c \<le> x then x + d else x) ` FV t2)"
        have " {y. \<exists>xa. ((\<exists>x. x \<in> FV t2 \<and> Suc c \<le> x \<and> xa = x + d) \<or> xa \<in> FV t2 \<and> \<not> Suc c \<le> xa) \<and>
                xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0} \<subseteq> {y. \<exists>xa. ((\<exists>xb. xb \<in> FV t2 \<and> xb \<noteq> x \<and> x < xb \<and>
                xa = xb - Suc 0) \<or> xa \<in> FV t2 \<and> xa \<noteq> x \<and> \<not> x < xa \<or> xa \<in> FV t1) \<and>
                c \<le> xa \<and> y = xa + d} \<union> ({y. \<exists>xa. xa \<in> FV t2 \<and> xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0} \<union>
                (FV t2 - {x}) \<inter> {y. \<not> x < y} \<union> FV t1) \<inter> {x. \<not> c \<le> x}"
        proof (rule, simp)
          (*generated with sledgehammer*)
          fix xa :: nat
          assume a1: "\<exists>xaa. ((\<exists>x. x \<in> FV t2 \<and> Suc c \<le> x \<and> xaa = x + d) \<or> xaa \<in> FV t2 \<and> \<not> Suc c \<le> xaa) \<and> xaa \<noteq> x \<and> x < xaa \<and> xa = xaa - Suc 0"
          obtain nna :: nat where
            f2: "(\<exists>v0. ((\<exists>v1. v1 \<in> FV t2 \<and> Suc c \<le> v1 \<and> v0 = v1 + d) \<or> v0 \<in> FV t2 \<and> \<not> Suc c \<le> v0) \<and> v0 \<noteq> x \<and> x < v0 \<and> xa = v0 - Suc 0) = (((\<exists>v1. v1 \<in> FV t2 \<and> Suc c \<le> v1 \<and> nna = v1 + d) \<or> nna \<in> FV t2 \<and> \<not> Suc c \<le> nna) \<and> nna \<noteq> x \<and> x < nna \<and> xa = nna - Suc 0)"
            by moura
          obtain nn :: nat where
             "(\<exists>v1. v1 \<in> FV t2 \<and> Suc c \<le> v1 \<and> nna = v1 + d) = (nn \<in> FV t2 \<and> Suc c \<le> nn \<and> nna = nn + d)"
            by moura
          then have f3: "(nn \<in> FV t2 \<and> Suc c \<le> nn \<and> nna = nn + d \<or> nna \<in> FV t2 \<and> \<not> Suc c \<le> nna) \<and> nna \<noteq> x \<and> x < nna \<and> xa = nna - Suc 0"
            using f2 a1 by presburger
          then have f4: "nna \<in> FV t2 \<and> \<not> Suc c \<le> nna \<longrightarrow> \<not> c \<le> xa"
            by (simp add: gr_Suc_conv)
          obtain nnb :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
            f5: "(\<not> Suc c \<le> nn \<or> nn = Suc (nnb nn c) \<and> c \<le> nnb nn c) \<and> (Suc c \<le> nn \<or> (\<forall>n. nn \<noteq> Suc n \<or> \<not> c \<le> n))"
            by (metis gr_Suc_conv)
          have "nn - Suc c + Suc c = nn \<and> Suc 0 \<le> nn \<and> nnb nn c = nn - Suc 0 \<and> nn = x \<longrightarrow> nn \<noteq> Suc (nnb nn c) \<or> \<not> c \<le> nnb nn c"
            by (metis (no_types) infc not_less_eq ordered_cancel_comm_monoid_diff_class.add_diff_inverse trans_less_add2)
          moreover
          { assume "nn \<noteq> x"
            { assume "nn \<noteq> x \<and> x < nn"
              moreover
              { assume "(\<exists>n. n \<in> FV t2 \<and> n \<noteq> x \<and> x < n \<and> nnb nn c = n - Suc 0) \<or> nnb nn c \<in> FV t2 \<and> nnb nn c \<noteq> x \<and> \<not> x < nnb nn c \<or> nnb nn c \<in> FV t1"
                moreover
                { assume "xa \<noteq> nnb nn c + d"
                  then have "Suc 0 \<le> nn \<and> nnb nn c = nn - Suc 0 \<longrightarrow> nn \<notin> FV t2 \<or> \<not> Suc c \<le> nn \<or> nna \<noteq> nn + d"
                    using f3 by (metis (no_types) Nat.add_diff_assoc2) }
                ultimately have "Suc 0 \<le> nn \<and> nnb nn c = nn - Suc 0 \<longrightarrow> (nn \<notin> FV t2 \<or> \<not> Suc c \<le> nn \<or> nna \<noteq> nn + d) \<or> (nn \<noteq> Suc (nnb nn c) \<or> \<not> c \<le> nnb nn c) \<or> (\<exists>n. ((\<exists>na. na \<in> FV t2 \<and> na \<noteq> x \<and> x < na \<and> n = na - Suc 0) \<or> n \<in> FV t2 \<and> n \<noteq> x \<and> \<not> x < n \<or> n \<in> FV t1) \<and> c \<le> n \<and> xa = n + d) \<or> ((\<exists>n. n \<in> FV t2 \<and> n \<noteq> x \<and> x < n \<and> xa = n - Suc 0) \<or> xa \<in> FV t2 \<and> xa \<noteq> x \<and> \<not> x < xa \<or> xa \<in> FV t1) \<and> \<not> c \<le> xa"
                  by blast }
              ultimately have "Suc 0 \<le> nn \<and> nnb nn c = nn - Suc 0 \<longrightarrow> (nn \<notin> FV t2 \<or> \<not> Suc c \<le> nn \<or> nna \<noteq> nn + d) \<or> (nn \<noteq> Suc (nnb nn c) \<or> \<not> c \<le> nnb nn c) \<or> (\<exists>n. ((\<exists>na. na \<in> FV t2 \<and> na \<noteq> x \<and> x < na \<and> n = na - Suc 0) \<or> n \<in> FV t2 \<and> n \<noteq> x \<and> \<not> x < n \<or> n \<in> FV t1) \<and> c \<le> n \<and> xa = n + d) \<or> ((\<exists>n. n \<in> FV t2 \<and> n \<noteq> x \<and> x < n \<and> xa = n - Suc 0) \<or> xa \<in> FV t2 \<and> xa \<noteq> x \<and> \<not> x < xa \<or> xa \<in> FV t1) \<and> \<not> c \<le> xa"
                by blast }
            moreover
            { assume "\<not> x < nn"
              then have "nn - Suc c + Suc c \<noteq> nn"
                by (metis (no_types) infc not_less_eq trans_less_add2) }
            ultimately have "nn - Suc c + Suc c = nn \<and> Suc 0 \<le> nn \<and> nnb nn c = nn - Suc 0 \<longrightarrow> (nn \<notin> FV t2 \<or> \<not> Suc c \<le> nn \<or> nna \<noteq> nn + d) \<or> (nn \<noteq> Suc (nnb nn c) \<or> \<not> c \<le> nnb nn c) \<or> (\<exists>n. ((\<exists>na. na \<in> FV t2 \<and> na \<noteq> x \<and> x < na \<and> n = na - Suc 0) \<or> n \<in> FV t2 \<and> n \<noteq> x \<and> \<not> x < n \<or> n \<in> FV t1) \<and> c \<le> n \<and> xa = n + d) \<or> ((\<exists>n. n \<in> FV t2 \<and> n \<noteq> x \<and> x < n \<and> xa = n - Suc 0) \<or> xa \<in> FV t2 \<and> xa \<noteq> x \<and> \<not> x < xa \<or> xa \<in> FV t1) \<and> \<not> c \<le> xa"
              by fastforce }
          moreover
          { assume "nn - Suc c + Suc c \<noteq> nn"
            then have "nn \<notin> FV t2 \<or> \<not> Suc c \<le> nn \<or> nna \<noteq> nn + d"
              using le_add_diff_inverse2 by blast }
          moreover
          { assume "nn \<noteq> Suc (nnb nn c) \<or> \<not> c \<le> nnb nn c"
            then have "nn \<notin> FV t2 \<or> \<not> Suc c \<le> nn \<or> nna \<noteq> nn + d"
              using f5 by fastforce }
          moreover
          { assume "\<not> Suc 0 \<le> nn"
            then have "nn \<noteq> Suc (nnb nn c) \<or> \<not> c \<le> nnb nn c"
              by simp }
          moreover
          { assume "nnb nn c \<noteq> nn - Suc 0"
            then have "nn \<noteq> Suc (nnb nn c) \<or> \<not> c \<le> nnb nn c"
              by (metis (no_types) One_nat_def diff_Suc_1) }
          moreover
          { assume "nn \<notin> FV t2 \<or> \<not> Suc c \<le> nn \<or> nna \<noteq> nn + d"
            then have "(nna \<in> FV t2 \<and> \<not> Suc c \<le> nna) \<and> ((\<exists>n. n \<in> FV t2 \<and> n \<noteq> x \<and> x < n \<and> xa = n - Suc 0) \<or> xa \<in> FV t2 \<and> xa \<noteq> x \<and> \<not> x < xa \<or> xa \<in> FV t1)"
              using f3 by blast
            then have "(\<exists>n. ((\<exists>na. na \<in> FV t2 \<and> na \<noteq> x \<and> x < na \<and> n = na - Suc 0) \<or> n \<in> FV t2 \<and> n \<noteq> x \<and> \<not> x < n \<or> n \<in> FV t1) \<and> c \<le> n \<and> xa = n + d) \<or> ((\<exists>n. n \<in> FV t2 \<and> n \<noteq> x \<and> x < n \<and> xa = n - Suc 0) \<or> xa \<in> FV t2 \<and> xa \<noteq> x \<and> \<not> x < xa \<or> xa \<in> FV t1) \<and> \<not> c \<le> xa"
              using f4 by force }
          ultimately show "(\<exists>n. ((\<exists>na. na \<in> FV t2 \<and> na \<noteq> x \<and> x < na \<and> n = na - Suc 0) \<or> n \<in> FV t2 \<and> n \<noteq> x \<and> \<not> x < n \<or> n \<in> FV t1) \<and> c \<le> n \<and> xa = n + d) \<or> ((\<exists>n. n \<in> FV t2 \<and> n \<noteq> x \<and> x < n \<and> xa = n - Suc 0) \<or> xa \<in> FV t2 \<and> xa \<noteq> x \<and> \<not> x < xa \<or> xa \<in> FV t1) \<and> \<not> c \<le> xa"
            by satx
        qed
      
        then show "?S3 x t1 t2 \<subseteq> ?S4 x t1 t2"
           using infc
           by (simp add: image_def FV_s Int_Collect Bex_def) force
      qed
     
    have "\<And>x t1 t2. \<not>c<x \<Longrightarrow>(\<And>c. FV (shift_L (int d) c t1) = (\<lambda>x. if c \<le> x then x + d else x) ` FV t1)
            \<Longrightarrow> (\<And>c. FV (shift_L (int d) c t2) = (\<lambda>x. if c \<le> x then x + d else x) ` FV t2) \<Longrightarrow>?S4 x t1 t2 \<subseteq> ?S3 x t1 t2"
     proof -
       fix x t1 t2
       assume infc:"\<not>c<x" and
              FV_s: "(\<And>c. FV (shift_L (int d) c t1) = (\<lambda>x. if c \<le> x then x + d else x) ` FV t1)"
                    "(\<And>c. FV (shift_L (int d) c t2) = (\<lambda>x. if c \<le> x then x + d else x) ` FV t2)"
       have "\<not> c < x \<Longrightarrow>
        {y. \<exists>xa. ((\<exists>xb. xb \<in> FV t2 \<and> xb \<noteq> x \<and> x < xb \<and> xa = xb - Suc 0) \<or> xa \<in> FV t2 \<and> xa \<noteq> x \<and> \<not> x < xa \<or> xa \<in> FV t1) \<and>
         c \<le> xa \<and> y = xa + d} \<subseteq> {y. \<exists>x. x \<in> FV t1 \<and> c \<le> x \<and> y = x + d} \<union> FV t1 \<inter> {x. \<not> c \<le> x} \<union>
         ({y. \<exists>xa. ((\<exists>x. x \<in> FV t2 \<and> Suc c \<le> x \<and> xa = x + d) \<or> xa \<in> FV t2 \<and> \<not> Suc c \<le> xa) \<and>
         xa \<noteq> x \<and> x < xa \<and> y = xa - Suc 0} \<union> ({y. \<exists>x. x \<in> FV t2 \<and> Suc c \<le> x \<and> y = x + d} \<union> 
         FV t2 \<inter> {x. \<not> Suc c \<le> x} - {x}) \<inter> {y. \<not> x < y})"
         proof (rule, simp)
            (*generated with sledgehammer*)
            fix xa :: nat
            assume a1: "\<exists>xb. ((\<exists>xa. xa \<in> FV t2 \<and> xa \<noteq> x \<and> x < xa \<and> xb = xa - Suc 0) \<or> xb \<in> FV t2 \<and> xb \<noteq> x \<and> \<not> x < xb \<or> xb \<in> FV t1) \<and> c \<le> xb \<and> xa = xb + d"
            assume a2: "\<not> c < x"
            obtain nna :: nat where
              f3:"(\<exists>v0. ((\<exists>v1. v1 \<in> FV t2 \<and> v1 \<noteq> x \<and> x < v1 \<and> v0 = v1 - Suc 0) \<or> v0 \<in> FV t2 \<and> v0 \<noteq> x \<and> \<not> x < v0 \<or> v0 \<in> FV t1) \<and> c \<le> v0 \<and> xa = v0 + d) = (((\<exists>v1. v1 \<in> FV t2 \<and> v1 \<noteq> x \<and> x < v1 \<and> nna = v1 - Suc 0) \<or> nna \<in> FV t2 \<and> nna \<noteq> x \<and> \<not> x < nna \<or> nna \<in> FV t1) \<and> c \<le> nna \<and> xa = nna + d)"
              by moura
            obtain nn :: nat where
              "(\<exists>v1. v1 \<in> FV t2 \<and> v1 \<noteq> x \<and> x < v1 \<and> nna = v1 - Suc 0) = (nn \<in> FV t2 \<and> nn \<noteq> x \<and> x < nn \<and> nna = nn - Suc 0)"
              by moura
            then have f4: "(nn \<in> FV t2 \<and> nn \<noteq> x \<and> x < nn \<and> nna = nn - Suc 0 \<or> nna \<in> FV t2 \<and> nna \<noteq> x \<and> \<not> x < nna \<or> nna \<in> FV t1) \<and> c \<le> nna \<and> xa = nna + d"
              using f3 a1 by presburger
            have f5: "\<forall>n na. \<not> n \<le> na \<or> n < Suc na"
              using le_imp_less_Suc by satx
            have f6: "\<forall>n na. \<not> n < na \<or> Suc n \<le> na"
              by simp
            obtain nnb :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
              "\<forall>x0 x1. (\<exists>v2>0. x1 + v2 = x0) = (0 < nnb x0 x1 \<and> x1 + nnb x0 x1 = x0)"
              by moura
            then have f7: "\<forall>n na. \<not> n < na \<or> 0 < nnb na n \<and> n + nnb na n = na"
              using less_imp_add_positive by presburger
            have f8: "\<forall>n na. \<not> (n::nat) \<le> na \<or> n + (na - n) = na"
              by fastforce
            have f9: "0 < Suc nna"
              by force
            have f10: "nna \<notin> FV t2 \<or> nna = x \<or> x < nna"
              using f8 f4 a2 by (metis le_neq_implies_less linorder_neqE_nat trans_less_add1)
            have "nn = Suc nna \<longrightarrow> (nn \<notin> FV t2 \<or> nn = x \<or> \<not> x < nn \<or> nna \<noteq> nn - Suc 0) \<or> (\<exists>n. n \<in> FV t1 \<and> c \<le> n \<and> xa = n + d) \<or> xa \<in> FV t1 \<and> \<not> c \<le> xa \<or> (\<exists>n. ((\<exists>na. na \<in> FV t2 \<and> Suc c \<le> na \<and> n = na + d) \<or> n \<in> FV t2 \<and> \<not> Suc c \<le> n) \<and> n \<noteq> x \<and> x < n \<and> xa = n - Suc 0) \<or> ((\<exists>n. n \<in> FV t2 \<and> Suc c \<le> n \<and> xa = n + d) \<or> xa \<in> FV t2 \<and> \<not> Suc c \<le> xa) \<and> xa \<noteq> x \<and> \<not> x < xa"
              using f9 f6 f5 f4 a2 by (metis (no_types) Nat.add_diff_assoc2 trans_less_add1)
            moreover
            { assume "nn \<noteq> Suc nna"
              then have "nn \<notin> FV t2 \<or> nn = x \<or> \<not> x < nn \<or> nna \<noteq> nn - Suc 0"
                using f9 f8 f7 f6 by (metis (no_types) One_nat_def add_gr_0 diff_Suc_1) }
            ultimately have "((\<exists>n. n \<in> FV t1 \<and> c \<le> n \<and> xa = n + d) \<or> xa \<in> FV t1 \<and> \<not> c \<le> xa \<or> (\<exists>n. ((\<exists>na. na \<in> FV t2 \<and> Suc c \<le> na \<and> n = na + d) \<or> n \<in> FV t2 \<and> \<not> Suc c \<le> n) \<and> n \<noteq> x \<and> x < n \<and> xa = n - Suc 0) \<or> ((\<exists>n. n \<in> FV t2 \<and> Suc c \<le> n \<and> xa = n + d) \<or> xa \<in> FV t2 \<and> \<not> Suc c \<le> xa) \<and> xa \<noteq> x \<and> \<not> x < xa) \<or> nn \<notin> FV t2 \<or> nn = x \<or> \<not> x < nn \<or> nna \<noteq> nn - Suc 0"
              by fastforce
            then show "(\<exists>n. n \<in> FV t1 \<and> c \<le> n \<and> xa = n + d) \<or> xa \<in> FV t1 \<and> \<not> c \<le> xa \<or> (\<exists>n. ((\<exists>na. na \<in> FV t2 \<and> Suc c \<le> na \<and> n = na + d) \<or> n \<in> FV t2 \<and> \<not> Suc c \<le> n) \<and> n \<noteq> x \<and> x < n \<and> xa = n - Suc 0) \<or> ((\<exists>n. n \<in> FV t2 \<and> Suc c \<le> n \<and> xa = n + d) \<or> xa \<in> FV t2 \<and> \<not> Suc c \<le> xa) \<and> xa \<noteq> x \<and> \<not> x < xa"
              using f10 f4 by auto
         qed
         
        
       then show "?S4 x t1 t2 \<subseteq> ?S3 x t1 t2"
         using infc
         by (simp add: image_def FV_s Int_Collect Bex_def) fastforce
     qed   

    note H= C1 C2  C4 this
    have A:" FV (if c < x then Let var nat (int x + int d) := shift_L (int d) c t1 in shift_L (int d) c t2
        else Let var x := shift_L (int d) c t1 in shift_L (int d) (Suc c) t2) = ?S3 x t1 t2"
      by auto

    have "?S3 x t1 t2 = ?S4 x t1 t2"
      using H[of x t1 t2,OF _ hyps]
      by (cases "c<x") fast+

    then show ?case
      by (simp only: shift_L.simps FV.simps A)
      
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
              else FV (Let var x := t1 in t2)" and
        ?S3="\<lambda>n t x t1 t2. (\<lambda>y. if x < y then y - 1 else y) ` (FV (subst_L (if x \<le> n then Suc n else n) (shift_L 1 x t) t2) - {x}) \<union>
              FV (subst_L n t t1)" and
        ?S4 ="\<lambda>n t x t1 t2. (if n \<in> (\<lambda>y. if x < y then y - 1 else y) ` (FV t2 - {x}) \<union> FV t1
                then (\<lambda>y. if x < y then y - 1 else y) ` (FV t2 - {x}) \<union> FV t1 - {n} \<union> FV t
                else (\<lambda>y. if x < y then y - 1 else y) ` (FV t2 - {x}) \<union> FV t1)"
        
    have C1:"\<And>n t x t1 t2. (\<And>n1 ta. FV (subst_L n1 ta t1) = (if n1 \<in> FV t1 then FV t1 - {n1} \<union> FV ta else 
                          FV t1)) \<Longrightarrow>
                         (\<And>n1 ta. FV (subst_L n1 ta t2) = (if n1 \<in> FV t2 then FV t2 - {n1} \<union> FV ta else 
                          FV t2)) \<Longrightarrow> x \<le> n \<Longrightarrow> ?S3 n t x t1 t2 \<subseteq> ?S4 n t x t1 t2"
      proof -
        fix n::nat and t x t1 t2
        assume le_n:"x\<le>n" and
                FV_s:"\<And>n1 ta. FV (subst_L n1 ta t1) = (if n1 \<in> FV t1 then FV t1 - {n1} \<union> FV ta else FV t1)"
                     "\<And>n1 ta. FV (subst_L n1 ta t2) = (if n1 \<in> FV t2 then FV t2 - {n1} \<union> FV ta else FV t2)"
        note FV_s= FV_s[of n t] FV_s[of "Suc n" "shift_L 1 x t"]
        have "Suc n \<in> FV t2 \<Longrightarrow> n\<in> FV t1 \<Longrightarrow> ?S3 n t x t1 t2 \<subseteq> ?S4 n t x t1 t2" 
          using le_n
          by (simp add: image_def FV_s Int_Collect Bex_def FV_shift[of 1, unfolded int_1]) force

        moreover have "Suc n \<in> FV t2 \<Longrightarrow> n \<notin> FV t1 \<Longrightarrow> ?S3 n t x t1 t2 \<subseteq> ?S4 n t x t1 t2" 
          using le_n
          by (simp add: image_def FV_s Int_Collect Bex_def FV_shift[of 1, unfolded int_1])
             (meson, (force+)[3], ((metis One_nat_def diff_Suc_1 le_imp_less_Suc)+)[2],
                 (force+)[2], (metis One_nat_def diff_Suc_1 le_imp_less_Suc)+)
          
        moreover have "Suc n \<notin> FV t2 \<Longrightarrow>?S3 n t x t1 t2 \<subseteq> ?S4 n t x t1 t2"
          using le_n
          by (simp add: image_def FV_s Int_Collect Bex_def FV_shift[of 1, unfolded int_1])
             (cases "n\<in> FV t1", auto)

        ultimately show "?S3 n t x t1 t2 \<subseteq> ?S4 n t x t1 t2" by linarith
      qed

    have C2:"\<And>n t x t1 t2. (\<And>n1 ta. FV (subst_L n1 ta t1) = (if n1 \<in> FV t1 then FV t1 - {n1} \<union> FV ta else 
                          FV t1)) \<Longrightarrow>
                         (\<And>n1 ta. FV (subst_L n1 ta t2) = (if n1 \<in> FV t2 then FV t2 - {n1} \<union> FV ta else 
                          FV t2)) \<Longrightarrow> x \<le> n \<Longrightarrow> ?S4 n t x t1 t2 \<subseteq> ?S3 n t x t1 t2" 
      proof -
        fix n::nat and t x t1 t2
        assume le_n:"x\<le>n" and
                FV_s:"\<And>n1 ta. FV (subst_L n1 ta t1) = (if n1 \<in> FV t1 then FV t1 - {n1} \<union> FV ta else FV t1)"
                     "\<And>n1 ta. FV (subst_L n1 ta t2) = (if n1 \<in> FV t2 then FV t2 - {n1} \<union> FV ta else FV t2)"
        note FV_s= FV_s[of n t] FV_s[of "Suc n" "shift_L 1 x t"]
        have "Suc n \<in> FV t2 \<Longrightarrow> n\<in> FV t1 \<Longrightarrow> ?S4 n t x t1 t2 \<subseteq> ?S3 n t x t1 t2" 
          using le_n
          by (simp add: image_def FV_s Int_Collect Bex_def FV_shift[of 1, unfolded int_1]) force

        moreover have "Suc n \<in> FV t2 \<Longrightarrow> n \<notin> FV t1 \<Longrightarrow> ?S4 n t x t1 t2 \<subseteq> ?S3 n t x t1 t2" 
          using le_n
          proof (simp add: image_def FV_s Int_Collect Bex_def FV_shift[of 1, unfolded int_1], meson)
            fix x1
            show "Suc (x1 - Suc 0) \<in> FV t2 \<Longrightarrow> x1 - Suc 0 \<notin> FV t1 \<Longrightarrow> x \<le> x1 - Suc 0 \<Longrightarrow> x1 \<in> FV t2 \<Longrightarrow>
                  x1 \<noteq> x \<Longrightarrow> x < x1 \<Longrightarrow> n = x1 - Suc 0 \<Longrightarrow> {y. \<exists>xa. xa \<in> FV t2 \<and> xa \<noteq> x \<and> x < xa \<and> 
                  y = xa - Suc 0} \<union> (FV t2 - {x}) \<inter> {y. \<not> x < y} \<union> FV t1 - {x1 - Suc 0}
                  \<subseteq> {y. \<exists>xb. (xb \<in> FV t2 \<and> xb \<noteq> Suc (x1 - Suc 0) \<or> (\<exists>xa. xa \<in> FV t \<and> x \<le> xa \<and> xb = Suc xa) \<or> xb \<in> FV t \<and> \<not> x \<le> xb) \<and>
                  xb \<noteq> x \<and> x < xb \<and> y = xb - Suc 0} \<union> (FV t2 - {Suc (x1 - Suc 0)} \<union> ({y. \<exists>xa. xa \<in> FV t \<and>
                  x \<le> xa \<and> y = Suc xa} \<union> FV t \<inter> {y. \<not> x \<le> y}) - {x}) \<inter> {y. \<not> x < y} \<union> FV t1"
              by auto
          next
            fix x1
            show "Suc (x1 - Suc 0) \<in> FV t2 \<Longrightarrow> x1 - Suc 0 \<notin> FV t1 \<Longrightarrow>  x \<le> x1 - Suc 0 \<Longrightarrow> x1 \<in> FV t2 \<Longrightarrow>
                  x1 \<noteq> x \<Longrightarrow> x < x1 \<Longrightarrow> n = x1 - Suc 0 \<Longrightarrow> FV t \<subseteq> {y. \<exists>xb. (xb \<in> FV t2 \<and>
                  xb \<noteq> Suc (x1 - Suc 0) \<or> (\<exists>xa. xa \<in> FV t \<and> x \<le> xa \<and> xb = Suc xa) \<or> xb \<in> FV t \<and> \<not> x \<le> xb) \<and>
                  xb \<noteq> x \<and> x < xb \<and> y = xb - Suc 0} \<union> (FV t2 - {Suc (x1 - Suc 0)} \<union> ({y. \<exists>xa. xa \<in> FV t \<and>
                  x \<le> xa \<and> y = Suc xa} \<union> FV t \<inter> {y. \<not> x \<le> y}) - {x}) \<inter> {y. \<not> x < y} \<union> FV t1"
              by (rule, simp, metis One_nat_def diff_Suc_1 le_eq_less_or_eq le_imp_less_Suc nat_neq_iff)
          qed fastforce+

        moreover have "Suc n \<notin> FV t2 \<Longrightarrow>?S4 n t x t1 t2 \<subseteq> ?S3 n t x t1 t2"
          using le_n
          by (simp add: image_def FV_s Int_Collect Bex_def FV_shift[of 1, unfolded int_1])
             (cases "n\<in> FV t1", auto)

        ultimately show "?S4 n t x t1 t2 \<subseteq> ?S3 n t x t1 t2" by linarith
      qed

    have C3:"\<And>n t x t1 t2. (\<And>n1 ta. FV (subst_L n1 ta t1) = (if n1 \<in> FV t1 then FV t1 - {n1} \<union> FV ta else 
                          FV t1)) \<Longrightarrow>
                         (\<And>n1 ta. FV (subst_L n1 ta t2) = (if n1 \<in> FV t2 then FV t2 - {n1} \<union> FV ta else 
                          FV t2)) \<Longrightarrow>\<not>x\<le>n \<Longrightarrow>?S3 n t x t1 t2 \<subseteq> ?S4 n t x t1 t2"
      proof -
        fix n::nat and t x t1 t2
        assume gr_n:"\<not>x\<le>n" and
                FV_s:"\<And>n1 ta. FV (subst_L n1 ta t1) = (if n1 \<in> FV t1 then FV t1 - {n1} \<union> FV ta else FV t1)"
                     "\<And>n1 ta. FV (subst_L n1 ta t2) = (if n1 \<in> FV t2 then FV t2 - {n1} \<union> FV ta else FV t2)"
        note FV_s= FV_s[of n t] FV_s[of "Suc n" "shift_L 1 x t"] FV_s[of n "shift_L 1 x t"]
        from gr_n have "n\<in>FV t2 \<Longrightarrow> n\<in>FV t1 \<Longrightarrow> ?S3 n t x t1 t2 \<subseteq> ?S4 n t x t1 t2"
          by (simp add: image_def FV_s Int_Collect Bex_def FV_shift[of 1, unfolded int_1]) force
        moreover from gr_n have "n\<notin>FV t2 \<Longrightarrow> ?S3 n t x t1 t2 \<subseteq> ?S4 n t x t1 t2"
          by (force simp add: image_def FV_s Int_Collect Bex_def FV_shift[of 1, unfolded int_1])

        moreover from gr_n have "n\<in>FV t2 \<Longrightarrow> n\<notin>FV t1 \<Longrightarrow> ?S3 n t x t1 t2 \<subseteq> ?S4 n t x t1 t2"
          by (simp add: image_def FV_s Int_Collect Bex_def FV_shift[of 1, unfolded int_1]) force
         
        ultimately  show "?S3 n t x t1 t2 \<subseteq> ?S4 n t x t1 t2"
          by (cases "n\<in>FV t2", cases "n\<in>FV t1", blast+)
      qed    
    have "\<And>n t x t1 t2. (\<And>n1 ta. FV (subst_L n1 ta t1) = (if n1 \<in> FV t1 then FV t1 - {n1} \<union> FV ta else 
                          FV t1)) \<Longrightarrow>
                         (\<And>n1 ta. FV (subst_L n1 ta t2) = (if n1 \<in> FV t2 then FV t2 - {n1} \<union> FV ta else 
                          FV t2)) \<Longrightarrow>\<not>x\<le>n \<Longrightarrow>?S4 n t x t1 t2 \<subseteq> ?S3 n t x t1 t2"
      proof -
        fix n::nat and t x t1 t2
        assume gr_n:"\<not>x\<le>n" and
                FV_s:"\<And>n1 ta. FV (subst_L n1 ta t1) = (if n1 \<in> FV t1 then FV t1 - {n1} \<union> FV ta else FV t1)"
                     "\<And>n1 ta. FV (subst_L n1 ta t2) = (if n1 \<in> FV t2 then FV t2 - {n1} \<union> FV ta else FV t2)"
        note FV_s= FV_s[of n t] FV_s[of "Suc n" "shift_L 1 x t"] FV_s[of n "shift_L 1 x t"]
        from gr_n have "n\<in>FV t2 \<Longrightarrow> n\<in>FV t1 \<Longrightarrow> ?S4 n t x t1 t2 \<subseteq> ?S3 n t x t1 t2"
          by (simp add: image_def FV_s Int_Collect Bex_def FV_shift[of 1, unfolded int_1]) force
        moreover from gr_n have "n\<notin>FV t2 \<Longrightarrow> ?S4 n t x t1 t2 \<subseteq> ?S3 n t x t1 t2"
          by (simp add: image_def FV_s Int_Collect Bex_def FV_shift[of 1, unfolded int_1]) fastforce

        moreover from gr_n have "n\<in>FV t2 \<Longrightarrow> n\<notin>FV t1 \<Longrightarrow> ?S4 n t x t1 t2 \<subseteq> ?S3 n t x t1 t2"
          proof (simp add: image_def FV_s Int_Collect Bex_def FV_shift[of 1, unfolded int_1], meson)
            show "n \<in> FV t2 \<Longrightarrow> n \<notin> FV t1 \<Longrightarrow> \<not> x \<le> n \<Longrightarrow> FV t \<subseteq> {y. \<exists>xa. (xa \<in> FV t2 \<and> xa \<noteq> n \<or> 
                  (\<exists>xb. xb \<in> FV t \<and> x \<le> xb \<and> xa = Suc xb) \<or> xa \<in> FV t \<and> \<not> x \<le> xa) \<and> xa \<noteq> x \<and> x < xa \<and>
                  y = xa - Suc 0} \<union> (FV t2 - {n} \<union> ({y. \<exists>xa. xa \<in> FV t \<and> x \<le> xa \<and> y = Suc xa} \<union> FV t \<inter>
                  {y. \<not> x \<le> y}) - {x}) \<inter> {y. \<not> x < y} \<union> FV t1"
              by (rule, simp, metis One_nat_def diff_Suc_1 le_eq_less_or_eq le_imp_less_Suc nat_neq_iff)
          qed fastforce      
         
        ultimately  show "?S4 n t x t1 t2 \<subseteq> ?S3 n t x t1 t2"
          by (cases "n\<in>FV t2", cases "n\<in>FV t1", blast+)
      qed
    note H = this C1 C2 C3
   
    from H[OF hyps,of x n] have "?S3 n t x t1 t2 = ?S4 n t x t1 t2" by blast      
      
    then show ?case using hyps by force

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
    have "n < x \<Longrightarrow> insert_nth (nat (int x - 1)) A \<Gamma> \<turnstile> \<lparr>shift_L (- 1) n t1|;|\<sigma>,f\<rparr> |:| B"
      by (metis hyps(5) K H2 hyps(6) le_SucI length_insert_nth)
    
    hence C1:"n < x \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Let var nat (int x - 1) := shift_L (- 1) n t in shift_L (- 1) n t1|;|\<sigma>,f\<rparr> |:| B"
      using hyps(1) hyps(3)[OF _ hyps(6) _, simplified] H1(1)
      by (force intro: "has_type_L.intros")
      
    have "\<not> n < x \<Longrightarrow> insert_nth x A \<Gamma> \<turnstile> \<lparr>shift_L (- 1) (Suc n) t1|;|\<sigma>,f\<rparr> |:| B"
      using insert_nth_comp(2)[of "(nat (int x - 1))" \<Gamma> n A U]
            hyps(1) H1(2) hyps(5)[of "Suc n" ] K2
      by (metis Suc_leI hyps(5) hyps(6) insert_nth_comp(2) le_imp_less_Suc length_insert_nth not_le)
    
    hence "\<not> n < x \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Let var x := shift_L (- 1) n t in shift_L (- 1) (Suc n) t1|;|\<sigma>,f\<rparr> |:| B"
      using hyps(6) hyps(3)[OF _ hyps(6) _ , simplified] H1(1)
      by (force intro: "has_type_L.intros")      

    with C1 show ?case by simp

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
             insert_nth_comp(2)[OF has_type_Let(6),of x S A]  
            has_type_Let(5)[unfolded length_insert_nth, of "Suc n" ] 
            has_type_Let(6)[unfolded Suc_le_mono[of n, symmetric]]
            not_less[of n x]
      by (force intro: "has_type_L.intros")
      
    ultimately show ?case 
      by (simp,metis add.commute nat_int of_nat_Suc)
      
qed (auto intro!: has_type_L.intros simp: nth_append min_def pp2 pp3 pp4)

end