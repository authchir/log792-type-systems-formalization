theory Variant_Type_examples
imports Main
        Ext_Structures
begin
  
abbreviation OptionType::"ltype \<Rightarrow> ltype" ("(_)/ option" [201]200) where
"A option \<equiv> <[''none'',''some'']|,|[Unit,A]>"    
 
abbreviation Table ::"ltype" where
"Table \<equiv> Nat\<rightarrow>(Nat option)"

abbreviation emptyTable ::"lterm" where
"emptyTable \<equiv> LAbs Nat (<''none'':=unit> as Nat option)"  


lemma "\<emptyset> \<turnstile> \<lparr>emptyTable |;| id\<rparr> |:| Table"
 proof -
   let ?inner_term = "<''none'':= unit> as (Nat option)"
   have H:"[Nat] \<turnstile> \<lparr> ?inner_term|;| fill (shift_L 1 (Suc (nbinder ?inner_term))\<circ>(\<lambda>x. <|V x|>))\<rparr> |:| Nat option"
     using has_type_Variant[of "[Nat]" unit "shift_L 1 (Suc (nbinder ?inner_term))\<circ>(\<lambda>x. <|V x|>)" "[Unit, Nat]" 0 "[''none'',''some'']"]
           has_type_LUnit[of "[Nat]" "shift_L 1 (Suc (nbinder ?inner_term))\<circ>(\<lambda>x. <|V x|>)"] fill_id
     by fastforce
   
   then show ?thesis     
     using has_type_LAbs[of Nat \<emptyset> ?inner_term "\<lambda>x. <|V x|>" "Nat option"]
           fill_id     
     by auto
qed
      
end