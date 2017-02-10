theory Variant_Type_examples
imports Main
        Ext_Structures
        List
begin

section{* Option Type *}

abbreviation OptionType::"ltype \<Rightarrow> ltype" ("(_)/ option" [201]200) where
"A option \<equiv> <[''none'',''some'']|,|[Unit,A]>"    
 
abbreviation Table ::"ltype" where
"Table \<equiv> Nat\<rightarrow>(Nat option)"

abbreviation emptyTable ::"lterm" where
"emptyTable \<equiv> LAbs Nat (<''none'':=unit> as Nat option)"  


lemma emptyTable_well_typed:
  "\<Gamma> \<turnstile> \<lparr>emptyTable |;| fill \<delta>\<rparr> |:| Table"
 proof -
   
   let ?inner_term = "<''none'':= unit> as (Nat option)"
   have H:" \<Gamma> |,| Nat \<turnstile> \<lparr> ?inner_term|;| fill \<delta>\<rparr> |:| Nat option"
     using has_type_Variant[of "\<Gamma>|,|Nat" unit \<delta> "[Unit, Nat]" 0 "[''none'',''some'']"]
           has_type_LUnit[of "\<Gamma>|,|Nat" \<delta>]
     by fastforce
   
   then show ?thesis     
     using has_type_LAbs[of Nat "\<Gamma>" ?inner_term \<delta> "Nat option"]
     by auto
qed
   
abbreviation Lequal :: "lterm\<Rightarrow>lterm\<Rightarrow>lterm" where
"Lequal n m\<equiv> LApp (LApp (LAbs Nat (LAbs Nat (IsZero (LPlus (UMinus (LVar 0)) (LVar 1))))) n) m"

abbreviation extendTable :: "lterm" where
"extendTable \<equiv> LAbs Table (LAbs Nat (LAbs Nat (LAbs Nat 
                  (LIf (Lequal (LVar 0) (LVar 2)) (<''some'':= LVar 1> as Nat option) (LApp (LVar 3) (LVar 0))
                          ))))"

lemma Lequal_well_typed:
 "\<Gamma>\<turnstile> \<lparr>n |;| fill \<delta>\<rparr> |:| Nat \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>m |;| fill \<delta>\<rparr> |:| Nat \<Longrightarrow> \<Gamma> \<turnstile> \<lparr>Lequal n m |;| fill \<delta> \<rparr> |:| Bool" 
proof -
  assume args_types:"\<Gamma>\<turnstile> \<lparr>n |;| fill \<delta>\<rparr> |:| Nat" "\<Gamma> \<turnstile> \<lparr>m |;| fill \<delta>\<rparr> |:| Nat"
  
  have V1:" (Suc 0, Nat) |\<in>| (\<Gamma> |,| ltype.Nat |,| ltype.Nat)" by auto
  have V0:" (0, Nat) |\<in>| (\<Gamma> |,| ltype.Nat |,| ltype.Nat)" by auto

  have "\<Gamma> |,| ltype.Nat |,| ltype.Nat  \<turnstile> 
        \<lparr>IsZero (LPlus (UMinus (LVar 0)) (LVar (Suc 0)))|;|fill \<delta>\<rparr> |:| Bool" 
   using has_type_LPlus  has_type_UMinus has_type_IsZero
         has_type_LVar[OF V0,of \<delta>]
         has_type_LVar[OF V1,of \<delta>]         
   by blast
  then show "\<Gamma> \<turnstile> \<lparr>Lequal n m |;| fill \<delta> \<rparr> |:| Bool"
    using has_type_LApp[OF has_type_LApp[OF _ args_types(1)] args_types(2)]
          has_type_LAbs
    by auto
qed   


lemma extendTable_well_typed:
  "\<Gamma>\<turnstile> \<lparr> extendTable |;| fill \<delta>\<rparr> |:| Table\<rightarrow>Nat\<rightarrow>Nat\<rightarrow>Table"
proof-
  let ?ctx = "\<Gamma> |,| Table |,| ltype.Nat |,| ltype.Nat |,| ltype.Nat"  
  have 1: "?ctx \<turnstile> \<lparr>Lequal (LVar 0) (LVar 2)|;|fill \<delta> \<rparr> |:| Bool" 
    using Lequal_well_typed[of ?ctx _ \<delta>]
          has_type_LVar[of _ Nat ?ctx \<delta>]
    by fastforce

  have 2: "?ctx \<turnstile> \<lparr><''some'':= LVar 1> as Nat option |;|fill \<delta> \<rparr> |:| Nat option" 
    using has_type_Variant[of ?ctx "LVar 1" \<delta> "[Unit,Nat]" 1 "[''none'',''some'']"]
          has_type_LVar[of _ Nat ?ctx \<delta>]
    by force

  have "?ctx \<turnstile> \<lparr>LApp (LVar 3) (LVar 0) |;|fill \<delta> \<rparr> |:| Nat option"
    using has_type_LApp[of ?ctx "LVar 3" \<delta> Nat "Nat option" "LVar 0"] 
          has_type_LVar[of _ _ ?ctx \<delta>]
    by auto

  with 1 2 show ?thesis 
    using has_type_LAbs has_type_LIf[of ?ctx "Lequal (LVar 0) (LVar 2)" \<delta>]
    by force
qed

section{* Enumerations*}

abbreviation Weekday :: "ltype" where
  "Weekday \<equiv> <[''monday'',''tuesday'',''wednesday'',''thursday'',''friday'']|,|(replicate 5 Unit)>"

end