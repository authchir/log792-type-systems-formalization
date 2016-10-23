theory List_extra
imports
   Main
  "~~/src/HOL/List"
  "~~/src/HOL/Eisbach/Eisbach"
  "~~/src/HOL/Eisbach/Eisbach_Tools"
  "$AFP/List-Index/List_Index" 
begin

text{*
  This theory contains all references to list iterators and extra functions (like replace,...) not present in the commun list library and
  the AFP list-index library
*}

fun list_iter ::"('a\<Rightarrow>'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a list \<Rightarrow> 'b" where
"list_iter f r [] = r" |
"list_iter f r (a#xs) = f a (list_iter f r xs)"

fun replace ::"nat \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"replace n x xs = 
  (if length xs \<le> n then xs 
    else (take n xs) @ [x] @ (drop (Suc n) xs))"


abbreviation fst_extract::"('a\<times>'b) list \<Rightarrow> 'a list" where
"fst_extract L \<equiv> (list_iter (\<lambda>p r. fst p # r) [] L)"

abbreviation snd_extract::"('a\<times>'b) list \<Rightarrow> 'b list" where
"snd_extract L \<equiv> (list_iter (\<lambda>p r. snd p # r) [] L)"

abbreviation update_snd::"('b \<Rightarrow> 'c) \<Rightarrow> ('a\<times>'b) list \<Rightarrow> ('a\<times>'c) list" where
"update_snd f L \<equiv> zip (fst_extract L) (map f (snd_extract L))"

lemma replace_inv_length[simp]:
  "length (replace n x S) = length S"  
by(induction S arbitrary: x n, auto)
      
lemma rep_ins:
  "n\<le>n1 \<Longrightarrow> n\<le> length W \<Longrightarrow> insert_nth n S (replace n1 A W) = replace (Suc n1) A (insert_nth n S W)" (is "?P\<Longrightarrow> ?R \<Longrightarrow> ?Q")
proof -
  assume H: "?R" "?P"
  have 1:"n1\<ge> length W \<Longrightarrow> ?Q"
    by (simp add: min_def)
  have "n1< length W \<Longrightarrow> ?Q"
    proof -
      assume H1: "n1<length W"
      have "(Suc (Suc n1) - n) = Suc (Suc n1 - n)"
            using H
            by fastforce
      with H show ?thesis
        by (simp add: H1 min_def, auto)(simp add: H Suc_diff_le take_drop)
    qed
  with 1 show "?Q" by linarith
qed

lemma rep_ins2:
  "n<n1 \<Longrightarrow> n1\<le> length W \<Longrightarrow> insert_nth n1 S (replace n A W) = replace n A (insert_nth n1 S W)" (is "?P\<Longrightarrow> ?R \<Longrightarrow> ?Q")
proof -
  assume H: "?R" "?P"
  from H show "?Q"
    proof (simp add: min_def, auto)
      have "Suc n \<le> n1"
        by (metis (no_types) H(2) Suc_leI)
      then show "take (n1 - n) (A # drop (Suc n) W) @ S # drop (n1 - n) (A # drop (Suc n) W) = A # drop (Suc n) (take n1 W) @ S # drop n1 W"
        by (simp add: drop_Cons' drop_take take_Cons')
    qed
qed      

lemma len_fst_extract[simp]:
  "length (fst_extract L) = length L"
by (induction L, auto)

lemma len_snd_extract[simp]:
  "length (snd_extract L) = length L"
by (induction L, auto)

lemma fst_extract_zip1:
  "length L = length L1 \<Longrightarrow> fst_extract (zip L L1) = L"
proof(induction L arbitrary: L1)
  case (Cons a L')
    obtain b L1' where "L1 = b#L1'"
      using Cons(2)
      by (metis length_Suc_conv)

    with Cons
      show ?case
        using fst_conv length_Cons list_iter.simps(2) nat.simps(1) zip_Cons_Cons 
          by auto
qed auto

lemma zip_comp:
  "L = zip (fst_extract L) (snd_extract L)"
by(induction L,auto)

lemma inset_find_Some:
  "x \<in> set (fst_extract L) \<Longrightarrow> \<exists>p. find (\<lambda>e. fst e = x) L = Some (x,p) \<and> (x,p) \<in> set L"
by (induction L arbitrary: x, auto)

lemma incl_fst:
  "set L \<subseteq> set L1 \<Longrightarrow> set (fst_extract L) \<subseteq> set (fst_extract L1)"
using zip_comp[of L1]
      set_zip_leftD[of _ _ "fst_extract L1" "snd_extract L1"]
by (induction L arbitrary: L1, auto)

lemma find_zip1:
  "distinct L \<Longrightarrow> length L = length L1 \<Longrightarrow> length L1  = length L2 \<Longrightarrow> j< length L \<Longrightarrow> find (\<lambda>p. fst p = k) (zip L L1) = Some ((zip L L1) ! j) 
   \<Longrightarrow> find (\<lambda>p. fst p = k) (zip L L2) =  Some ((zip L L2) ! j)"  
proof (induction L arbitrary: k j L1 L2)    
  case (Cons a L')
   from this(3,6) 
     have "j=0 \<Longrightarrow> a = k"
       using find_Some_iff[of "\<lambda>p. fst p = k" "zip (a#L') L1" "(a,L1!j)"] 
             nth_zip[of 0 "a#L'" L1]
             fst_conv length_greater_0_conv list.simps(3) nth_Cons_0 
       by fastforce
   with Cons(3,4)
     have H:"j=0 \<Longrightarrow> find (\<lambda>p. fst p = k) (zip (a#L') L2) =  Some (a,L2 ! j)"
       using find_Some_iff[of "\<lambda>p. fst p = k" "zip (a#L') L2" "(a,L2!j)"]
             nth_zip[of 0 "a#L'" L2]
             fst_conv length_greater_0_conv list.simps(3) nth_Cons_0 
     by fastforce
   obtain b L2' where 1:"L2 = b#L2'"
     using Cons(3,4) length_Suc_conv
     by metis
   obtain b1 L1' where 2:"L1 = b1#L1'"
     using Cons(2,3) length_Suc_conv
     by metis
   have H2:"j>0 \<Longrightarrow> find (\<lambda>p. fst p = k) (zip (a#L') L2) =  Some (zip (a # L') L2 ! j)"
     proof -
       let ?f = "\<lambda>p. fst p = k"
       assume C:"j>0"
       from Cons(2)
         have D:"distinct (zip L' L1') \<and> distinct (zip (a#L') (b1#L1'))"
           by (metis distinct.simps(2) distinct_zipI1)          
       from Cons(3,5)
         have C': "j<length (zip (a#L') L1)"
           by auto
       from C obtain p where C1:"j = Suc p" 
         using Suc_pred' by blast
       {
          have A:"find ?f (zip (a#L') (b1#L1')) = Some (zip L' L1' ! p)"
            using C1 Cons(6) 2 
                  nth_zip[of "Suc p"]
            by fastforce
          hence "Suc p<length (zip (a # L') (b1 # L1')) \<and> fst (zip (a # L') (b1 # L1') ! Suc p) = k \<and> 
                zip L' L1' ! p = zip (a # L') (b1 # L1') ! Suc p \<and> (\<forall>j<Suc p. fst (zip (a # L') (b1 # L1') ! j) \<noteq> k)"
            using find_Some_iff[of "?f" "zip (a#L') (b1#L1')" "zip L' L1' ! p"]
                  D C C' C1 2
            by (metis Cons.prems(5) nth_eq_iff_index_eq option.inject)            
            
          hence "p<length (zip L' L1') \<and> fst (zip L' L1' ! p) = k \<and> zip L' L1' ! p = zip L' L1' ! p \<and> (\<forall>j<p. fst (zip L' L1' ! j) \<noteq> k)"
            by auto  
          with A have "find ?f (zip (a#L') (b1#L1')) = find ?f (zip L' L1') \<and> find ?f (zip L' L1') = Some (zip L' L1' ! p) "
            using find_Some_iff[of "?f" "zip L' L1'" "zip L' L1' ! p"]
            by metis
       }
       thus ?thesis
         using C C' C1 Cons(2,3,4) 1 2 nth_zip[of "Suc p"]
               Cons(1)[of L1' L2' p]
         by auto     
     qed 
   show ?case
     proof (cases "j=0")
       case True
         with H show ?thesis 
           using nth_Cons_0 Cons(3,4)
           by (metis length_greater_0_conv list.simps(3) nth_zip)
     next
       case False
         with H2 show ?thesis        
           by blast
     qed       
qed auto

lemma list_iter_nil:
"list_iter op @ [] L = [] \<Longrightarrow> i<length L \<Longrightarrow> L!i = []" 
proof (induction L arbitrary: i)
  case (Cons a L')
    show ?case
      proof (cases "i>0")
        case True
          from this obtain j where "i = Suc j" 
            by (metis Suc_pred)
          thus ?thesis 
            using Cons(1)[of j]
                  Cons(2,3)
            by force
      next
        case False
          thus ?thesis
            using Cons(2)
            by auto
      qed 
qed auto  

lemma list_map_incl:
  "set (list_iter op @ [] (map f L)) \<subseteq> S \<Longrightarrow>  i<length L \<Longrightarrow> set(f (L!i)) \<subseteq> S"
proof (induction L arbitrary: f S i)
  case (Cons a L')
    from Cons show ?case
      by (induction i arbitrary: L', auto)        
qed auto

lemma list_map_incl2:
  "(\<And>i. i<length L \<Longrightarrow> set(f (L!i)) \<subseteq> S) \<Longrightarrow> set (list_iter op @ [] (map f L)) \<subseteq> S"
proof (induction "map f L" arbitrary: L f S)
  case (Cons a L')
    obtain b L1 where "L = b#L1"
      using Cons(2)
      by blast
    thus ?case
      using Cons(1)[of f L1]
            Cons(3)[of "Suc _"]
            Cons(3)[of 0]
            Cons(2)
      by auto     
qed auto  

lemma fst_extract_app[simp]:
  "fst_extract (L@L1) = fst_extract L @ fst_extract L1" 
by (induction L arbitrary: L1, auto)

lemma snd_extract_app[simp]:
  "snd_extract (L@L1) = snd_extract L @ snd_extract L1"
by (induction L arbitrary: L1, auto)

lemma fst_extract_fst_index[simp]:
  "i< length L \<Longrightarrow> fst_extract L ! i = fst (L ! i)"
proof (induction L arbitrary: i)
  case (Cons a L')
    thus ?case
      by (induction i arbitrary: L', auto)           
qed auto

lemma snd_extract_snd_index[simp]:
  "i< length L \<Longrightarrow> snd_extract L ! i = snd (L ! i)"
proof (induction L arbitrary: i)
  case (Cons a L')
    thus ?case
      by (induction i arbitrary: L', auto)           
qed auto

lemma fst_updt_snd_is_fst[simp]:
  "fst_extract (update_snd f L) = fst_extract L"
by (induction L arbitrary:f, auto)  

lemma fst_ext_com_list_it_app:
  "fst_extract (list_iter op @ [] L) = list_iter op @ [] (map fst_extract L)"
by(induction L, auto)

lemma snd_ext_com_list_it_app:
  "snd_extract (list_iter op @ [] L) = list_iter op @ [] (map snd_extract L)"
by(induction L, auto)

lemma map_com_list_it_app:
  "map F (list_iter op @ [] L) = list_iter op @ [] (map (map F) L)"
by (induction L arbitrary: F, auto)

lemma zip_com_list_it_app:
  "(\<And>L1. length (f L1) = length (g L1)) \<Longrightarrow> zip (list_iter op @ [] (map f L)) (list_iter op @ [] (map g L)) = 
    list_iter op @ [] (map (\<lambda>p. zip (f p) (g p)) L)"
by (induction L arbitrary: f g, auto)

lemma list_it_map_app_map:
  "list_iter op @ [] (map (update_snd F) L) = update_snd F (list_iter op @ [] L)"
using fst_ext_com_list_it_app[of L] snd_ext_com_list_it_app[of L]
      map_com_list_it_app[of F "map snd_extract L"]
      zip_com_list_it_app[of "fst_extract" "map F \<circ> snd_extract" L]
by force

lemma update_snd_subset:
  "set L \<subseteq> set L1 \<Longrightarrow> set (update_snd F L) \<subseteq> set (update_snd F L1)"
proof (induction L arbitrary: L1 F)
  case (Cons a L')
    obtain j where H:"j<length L1" "L1 ! j = a"
      using Cons(2)
            set_conv_nth[of L1]
      by auto
    have "(fst a, F (snd a)) \<in> set (update_snd F L1)"
      using H in_set_zip
      by force
    then show ?case
       using Cons
        by simp                 
qed auto

lemma set_list_it_app[simp]:
  "set(list_iter op @ [] L) = (UN l : set L. set l)"
sorry

lemma nth_list_it_app:
  "\<exists>j k. (list_iter op @ [] L) ! i = (L ! j) ! k \<and> k<length(L!j) \<and> j<length L" 
sorry

lemma update_snd_rewrite_fun:
  "(\<forall>i<length L. f (snd (L!i)) = g (snd (L!i))) \<Longrightarrow> update_snd f L = update_snd g L"
sorry

lemma update_snd_comp:
  "(update_snd F) \<circ> (update_snd G) = update_snd (F \<circ> G)"
sorry

lemma fst_map:
  "fst_extract L = map fst L" sorry
 
lemma count_rem1:
  "x \<in> set L \<Longrightarrow> count_list L x = count_list (remove1 x L) x + 1"
by(induction L arbitrary: x, auto)

lemma count_Suc:
  "count_list L x = Suc n \<Longrightarrow> x \<in> set L"
proof(induction L arbitrary: n x)
  case (Cons a L1)
    have "x \<notin> set L1 \<Longrightarrow> x = a"
      using count_notin[of x L1]
            Cons(2)
      by (cases "a=x",auto)
    then show ?case
      by (cases "x \<in> set L1", auto)      
qed auto

lemma count_inset:
  " x \<in> set L \<Longrightarrow> \<exists>n. count_list L x = Suc n"
proof(induction L arbitrary: x)
  case (Cons a L1)
    then show ?case
      by (cases "x \<in> set L1", auto)      
qed auto

lemma same_count_eq:
  "(\<forall>x\<in>set L \<union> set L1. count_list L x = count_list L1 x) \<Longrightarrow> length L1 = length L \<Longrightarrow> (set L1 = set L)"
proof -
  assume count:"\<forall>x\<in>set L \<union> set L1. count_list L x = count_list L1 x"    
         and len : "length L1 = length L"
  have 1:"\<And>x. x\<in> set L \<Longrightarrow> x \<in> set L1"
    proof -
      fix x
      assume H: "x\<in>set L"
      have H1: "count_list L x = count_list L1 x"
        using count H
        by auto
      with len H show "x\<in> set L1"       
        proof (induction L arbitrary: L1 x)
          case (Cons a L')
            obtain b L1' where H:"L1 = b#L1'"
              using Cons(2) length_Suc_conv
              by metis
            have C: "x = a \<or> x = b \<or> (x\<noteq>a \<and> x \<noteq> b)"
              by auto
            have  " x\<noteq>a \<Longrightarrow> x\<noteq>b \<Longrightarrow> x\<in> set L1"
              using Cons(2-4) H
                    Cons(1)[of L1' x]
              by fastforce
            with C show "x\<in> set L1" 
              using Cons(3,4) count_Suc H
              by fastforce+  
        qed auto
    qed
  have "\<And>x. x \<in> set L1 \<Longrightarrow> x \<in> set L"
    proof -
      fix x
      assume H: "x\<in>set L1"
      have H1: "count_list L x = count_list L1 x"
        using count H
        by auto
      with len H show "x \<in> set L"       
        proof (induction L1 arbitrary: L x)
          case (Cons b L1')
            obtain a L' where H:"L = a#L'"
              using Cons(2) length_Suc_conv
              by metis
            have C: "x = a \<or> x = b \<or> (x\<noteq>a \<and> x \<noteq> b)"
              by auto
            have  " x\<noteq>a \<Longrightarrow> x\<noteq>b \<Longrightarrow> x\<in> set L"
              using Cons(2-4) H
                    Cons(1)[of L' x]
              by fastforce
            with C show "x\<in> set L" 
              using Cons(3,4) count_Suc H
              by fastforce+  
        qed auto
    qed
  with 1 show ?thesis
    by auto
qed

lemma count_list_app[simp]:
  "count_list (L@L1) x = count_list L x + count_list L1 x"
sorry

end