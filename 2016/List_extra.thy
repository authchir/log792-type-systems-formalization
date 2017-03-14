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

fun BigCirc::"('a\<Rightarrow>'a) list \<Rightarrow> ('a\<Rightarrow>'a)" ("\<Odot> (_)" [75] 55) where
"\<Odot> [] = id" |
"\<Odot> (f#fs) = f \<circ> (\<Odot> fs)"

fun BigCircT::"('a\<rightharpoonup>'b) list \<Rightarrow> ('a\<rightharpoonup>'b)" ("\<Odot>\<^sub>T (_)" [75] 55) where
"\<Odot>\<^sub>T [] = empty" |
"\<Odot>\<^sub>T (f#fs) = f ++ (\<Odot>\<^sub>T fs)"

fun indexed_map::"nat \<Rightarrow> (nat\<Rightarrow>'a\<Rightarrow>'b) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
"indexed_map n f [] = []" |
"indexed_map n f (x#xs) = f n x # (indexed_map (Suc n) f xs)"

lemma indexed_map_cong[fundef_cong]:
  "n=n1 \<Longrightarrow> L = L1 \<Longrightarrow>(\<And>x m. x \<in> set L1 \<Longrightarrow> f m x = g m x) \<Longrightarrow> 
    indexed_map n f L = indexed_map n1 g L1"
by (induction L arbitrary: n n1 L1, auto)

lemma indexed_to_map:
 "indexed_map i f L = 
  map (\<lambda>p. f (fst p) (snd p)) (zip [i..<(i+length L)] L)"
proof (induction L arbitrary: i) 
  case (Cons a L')
    have "map (\<lambda>p. f (fst p) (snd p)) (zip [i..<(i + length (a # L'))] (a # L')) =
          f i a # map (\<lambda>p. f (fst p) (snd p)) (zip [Suc i..<(Suc i + length L')] L')"
      by (metis (no_types, lifting) enumerate_eq_zip enumerate_simps(2) fst_conv 
                map_eq_Cons_conv snd_conv)      
    thus ?case
      using Cons[of "Suc i"]
      by force
qed auto

lemma indexed_map_0_len[simp]:
  "length (indexed_map 0 f L) = length L"
by (force simp: indexed_to_map[of 0 f L])

lemma nth_indexed_map_0[simp]:
  "i<length L \<Longrightarrow> indexed_map 0 f L ! i = f i (L!i)"
by (simp add:indexed_to_map[of 0 f L])

lemma replace_inv_length[simp]:
  "length (replace n x S) = length S"  
by(induction S arbitrary: x n, auto)

lemma nth_replace[simp]:
  "i<length L \<Longrightarrow> (replace n x L)!i = (if i=n \<and> n<length L then x else (L!i))"
unfolding "replace.simps"
proof (induction L arbitrary: i n)
  case (Cons l L')
    have "n=0 \<Longrightarrow> ?case" by simp 
    moreover have "\<And>n1. n=Suc n1 \<Longrightarrow> length (l # L') \<le> n \<Longrightarrow> ?case"
      by simp
    moreover have "\<And>n1. n=Suc n1 \<Longrightarrow>\<not> length (l # L') \<le> n \<Longrightarrow> i = Suc n1 \<Longrightarrow> ?case"
      using Cons(1)[of "i-1" "n-1", simplified]
      by fastforce
    moreover have "\<And>n1. n=Suc n1 \<Longrightarrow>\<not> length (l # L') \<le> n \<Longrightarrow> i \<noteq> Suc n1 \<Longrightarrow> ?case"
      using Cons(1)[of "i-1" "n-1", simplified]
            Cons(2)
      by (cases i, simp+)
      
    ultimately show ?case by (metis old.nat.exhaust)      
qed simp

lemma insert_nth_comp:
  "n\<le> length L \<Longrightarrow> n\<le>n1 \<Longrightarrow> insert_nth n S (insert_nth n1 S1 L) = insert_nth (Suc n1) S1 (insert_nth n S L)"
  "n\<le> length L \<Longrightarrow> n>n1 \<Longrightarrow> insert_nth (Suc n) S (insert_nth n1 S1 L) = insert_nth (n1) S1 (insert_nth n S L)"
proof (induction L arbitrary: n n1)
  case (Cons a L')
    case (1)
      have "Suc n1 - n = Suc (n1-n)" using 1(2) by auto
      hence "S # drop n (take n1 (a # L')) @ S1 # drop n1 (a # L') = take (Suc n1 - n) (S # drop n (a # L')) 
                @ S1 # drop (Suc n1 - n) (S # drop n (a # L'))"
        using take_Cons[of "Suc n1 - n" S] drop_Cons[of "Suc n1 - n" S] drop_drop[of "n1-n" n]
               drop_take[of n n1 "a#L'"]
        by fastforce
      then show ?case using 1 by (simp add:min_def)
        
next
  case (Cons a L')   
    case (2)
      have "Suc n - n1 = Suc (n-n1)" using 2(2) by auto
      hence "take (Suc n - n1) (S1 # drop n1 (a # L')) @ S # drop (Suc n - n1) (S1 # drop n1 (a # L')) =
            S1 # drop n1 (take n (a # L')) @ S # drop n (a # L')"
        using  take_Cons[of "Suc n - n1" S1] drop_Cons[of "Suc n - n1" S1] drop_drop[of "n-n1" n1]
                   drop_take[of n1 n "a#L'"] 
        by fastforce
      then show ?case using 2 by (simp add: min_def)
qed simp+  
      
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
        by (simp add: H1 min_def)(simp add: H Suc_diff_le take_drop)
    qed
  with 1 show "?Q" by linarith
qed

lemma rep_ins2:
  "n<n1 \<Longrightarrow> n1\<le> length W \<Longrightarrow> insert_nth n1 S (replace n A W) = replace n A (insert_nth n1 S W)" (is "?P\<Longrightarrow> ?R \<Longrightarrow> ?Q")
proof -
  assume H: "?R" "?P"
  have "Suc n \<le> n1"
        by (metis (no_types) H(2) Suc_leI)
  with H show "?Q"
    by (simp add: drop_Cons' drop_take take_Cons' min_def) 
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

lemma incl_snd:
  "set L \<subseteq> set L1 \<Longrightarrow> set (snd_extract L) \<subseteq> set (snd_extract L1)"
using zip_comp[of L1]
      set_zip_rightD[of _ _ "fst_extract L1" "snd_extract L1"]
by (induction L arbitrary: L1, auto)

lemma find_zip1:
  "distinct L \<Longrightarrow> length L = length L1 \<Longrightarrow> length (L@L3)  = length L2 \<Longrightarrow> j< length L \<Longrightarrow> find (\<lambda>p. fst p = k) (zip L L1) = Some ((zip L L1) ! j) 
   \<Longrightarrow> find (\<lambda>p. fst p = k) (zip (L@L3) L2) =  Some ((zip (L@L3) L2) ! j)"  
proof (induction L arbitrary: k j L1 L2 L3)    
  case (Cons a L')
   from this(3,6) 
     have "j=0 \<Longrightarrow> a = k"
       using find_Some_iff[of "\<lambda>p. fst p = k" "zip (a#L') L1" "(a,L1!j)"] 
             nth_zip[of 0 "a#L'" L1]
             fst_conv length_greater_0_conv list.simps(3) nth_Cons_0 
       by fastforce
   with Cons(3,4)
     have H:"j=0 \<Longrightarrow> find (\<lambda>p. fst p = k) (zip (a#L'@L3) L2) =  Some (a,L2 ! j)"
       using find_Some_iff[of "\<lambda>p. fst p = k" "zip (a#L'@L3) L2" "(a,L2!j)"]
             nth_zip[of 0 "a#L'@L3" L2]
             fst_conv length_greater_0_conv list.simps(3) nth_Cons_0 
     by fastforce
   obtain b L2' where 1:"L2 = b#L2'"
     using Cons(3,4) length_Suc_conv[of L2 "length L' + length L3"]
           length_append[of "a#L'" L3]
     by auto
   obtain b1 L1' where 2:"L1 = b1#L1'"
     using Cons(2,3) length_Suc_conv
     by metis
   have H2:"j>0 \<Longrightarrow> find (\<lambda>p. fst p = k) (zip (a#L'@L3) L2) =  Some (zip (a # L'@L3) L2 ! j)"
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
               Cons(1)[of L1' L3  L2' p]
         by auto     
     qed 
   show ?case
     proof (cases "j=0")
       case True
         with H show ?thesis 
           using nth_Cons_0[of a "L'@L3"] Cons(3,4)
                 length_greater_0_conv[of L2] length_append 
                 list.simps(3)[of a "L'@L3"] nth_zip[of 0 "a#L'@L3" L2]
           by fastforce      
     next
       case False
         with H2 show ?thesis        
           by fastforce
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

lemma set_foldl_app[simp]:
  "set(foldl op @ L1 L) = (UN l : set L. set l) \<union> set L1"
by (induction L arbitrary: L1, auto)

lemma set_foldl_union[simp]:
  "foldl op \<union> S L = (UN l : set L. l) \<union> S"
by (induction L arbitrary: S, auto)

lemma update_snd_rewrite_fun:
  "(\<forall>i<length L. f (snd (L!i)) = g (snd (L!i))) \<Longrightarrow> update_snd f L = update_snd g L"
by (induction L, force+)

lemma update_snd_comp:
  "(update_snd F \<circ> update_snd G) L = update_snd (F \<circ> G) L"
by (induction L, force+)

lemma fst_map:
  "fst_extract L = map fst L"
by (induction L, auto)
 
lemma snd_map:
  "snd_extract L = map snd L"
by (induction L, auto)

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

lemma count_rem1_out:
  "x\<noteq>l1 \<Longrightarrow> count_list (remove1 l1 L) x = count_list L x"
by (induction L arbitrary: l1, auto) 

lemma count_conv_length:
  "(\<forall>x\<in>set L. count_list L x = count_list L1 x) \<Longrightarrow> set L \<subseteq> set L1 \<Longrightarrow> length L \<le> length L1"
proof (induction L arbitrary:L1)
  case (Cons l L')
    have A:"\<forall>x\<in>set L'. count_list L' x = count_list (remove1 l L1) x"
      using Cons(2,3) count_rem1[of l L1] count_rem1_out
      by (metis add_diff_cancel_right' count_rem1 remove1.simps(2) set_subset_Cons subsetCE)
    have "set L' \<subseteq> set (remove1 l L1)"
      using Cons(3) A count_notin count_rem1 
      by fastforce
    then show ?case 
      using Cons(1)[of "remove1 l L1"] A length_remove1[of l L1]
            subsetD[OF Cons(3), of l, simplified]
      by (metis One_nat_def Suc_le_mono Suc_pred length_Cons length_pos_if_in_set)      
qed force

lemma same_count_set_length:
  "(\<forall>x\<in>set L. count_list L x = count_list L1 x) \<Longrightarrow> set L = set L1 \<Longrightarrow> length L = length L1"
by (metis order_refl count_conv_length le_antisym)

lemma count_list_app[simp]:
  "count_list (L@L1) x = count_list L x + count_list L1 x"
by (induction L arbitrary: L1, auto)

lemma distinct_fst_imp_count_1:
  "distinct (fst_extract L) \<Longrightarrow> (\<forall>x\<in>set L. count_list L x = 1)"
proof(induction L)
  case (Cons a L')
    thus ?case 
      using in_set_zip[of a "fst_extract L'" "snd_extract L'"]
            set_conv_nth[of "fst_extract L'"]
            count_notin set_ConsD set_zip_leftD zip_comp
            length_pos_if_in_set nth_zip
      by (smt One_nat_def add.right_neutral add_Suc_right count_list.simps(2) distinct.simps(2) list_iter.simps(2) prod.collapse)
qed auto

lemma same_count_swap:
  "\<forall>x\<in>set L. count_list L x = count_list L1 x \<Longrightarrow> set L1 \<subseteq> set L \<Longrightarrow> \<forall>x\<in>set L1. count_list L x = count_list L1 x"
proof (rule+)
  fix x
  assume hyp: "\<forall>y\<in>set L. count_list L y = count_list L1 y" "set L1 \<subseteq> set L" "x\<in>set L1"
  thus "count_list L x = count_list L1 x"
    by auto
qed

lemma inset_rem1:
  "x\<in> set L \<Longrightarrow> \<exists>L1 L2. L = L1@[x]@L2 \<and> remove1 x L = L1@L2"
proof(induction L arbitrary: x)
  case (Cons x1 L')
    have "x \<in> set L' \<Longrightarrow> x\<noteq>x1 \<Longrightarrow> ?case"
      proof -
        assume H:"x\<in> set L'" "x\<noteq>x1"
        obtain L1 L2 where H1:"L' = L1 @ [x] @ L2 \<and> remove1 x L' = L1 @ L2"
          using Cons(1)[OF H(1)]
          by auto
        have "x1 # L' = (x1#L1) @ [x] @ L2 \<and> remove1 x (x1 # L') = (x1#L1) @ L2"
         using remove1_append H(2) H1
         by auto
        thus ?case by blast
      qed
    thus ?case using Cons(2) by auto
qed auto

lemma in_set_conv_card_Suc:
  "finite L \<Longrightarrow> x \<in> L \<Longrightarrow>\<exists>k. card L = Suc k"
proof -
  assume H:"x\<in>L" "finite L"
  have 1:"L = insert x (L - {x}) \<and> x \<notin> (L - {x})" using insert_Diff[OF H(1)] by blast
  have "card (L - {x}) = 0 \<longrightarrow> (L - {x}) = {}" 
    using card_eq_0_iff[of "L-{x}"] finite_Diff[OF H(2), of "{x}"]
    by meson
  with 1 show "\<exists>k. card L = Suc k"
    using card_Suc_eq[of L "card(L-{x})"] 
    by metis      
qed  

lemma set_zip_subset:
  "set (zip L TL) \<subseteq> set (zip L' TL') \<Longrightarrow> length L' = length TL' \<Longrightarrow> length L = length TL
    \<Longrightarrow> set L \<subseteq> set L' \<and> set TL \<subseteq> set TL'"
proof (induction L arbitrary: TL TL' L')
  case (Cons l L)
    obtain t TL1 where "TL = t#TL1"
      using length_Suc_conv Cons(4)
      by metis
    then show ?case
      using Cons(1)[OF _ Cons(3)] Cons(4,2)
            in_set_zip[of "(l,t)", simplified]
      by auto
qed auto

lemma set_zip_subset_app:
 "length L=length L1 \<Longrightarrow> length L'=length L1' \<Longrightarrow>
        set (zip L L1) \<subseteq> A \<Longrightarrow> set (zip L' L1') \<subseteq> A \<Longrightarrow> set (zip (L@L') (L1@L1')) \<subseteq> A"
proof (induction L arbitrary: L1 L' L1' A)
  case (Cons l' La)
    obtain l1 L1a where "L1 = l1#L1a"
      using Cons(2) length_Suc_conv
      by metis
    then show ?case 
      using Cons(1)[OF _ Cons(3) _ Cons(5),of L1a] 
            Cons(2,4) 
      by simp
qed auto

end