
section \<open> "Implementing Interval" \<close>

theory Interval_imp

imports Main Bool_algebra

begin

locale interval = 
  fixes sem_interval :: "('a::linorder) \<times> 'a \<Rightarrow> 'a set"
  fixes empty:: "'a \<times> 'a \<Rightarrow> bool"
  fixes noempty:: "'a \<times> 'a \<Rightarrow> bool"
  fixes intersect:: "'a \<times> 'a  \<Rightarrow> 'a \<times> 'a \<Rightarrow> 'a \<times> 'a"
  fixes elem:: "'a  \<Rightarrow> 'a \<times> 'a \<Rightarrow> bool"
  assumes 
    sem_interval_def : "sem_interval s = {e. (fst s) \<le> e \<and> e \<le> (snd s)}" and
    empty_sem: "empty s = ({e. (fst s) \<le> e \<and> e \<le> (snd s)} = {})" and
    noempty_sem: "noempty s = ({e. (fst s) \<le> e \<and> e \<le> (snd s)} \<noteq> {})" and
    intersect_sem: "{e. fst (intersect s1 s2) \<le> e \<and>
                     e \<le> snd (intersect s1 s2)} = 
                                 {e. (fst s1) \<le> e \<and> e \<le> (snd s1)} \<inter>
                                 {e. (fst s2) \<le> e \<and> e \<le> (snd s2)}" and
    elem_sem: "elem a s = ((fst s) \<le> a \<and> a \<le> (snd s))"
begin 

lemma empty_sem_alt: "empty s = (sem_interval s = {})" 
  by (auto simp add: empty_sem sem_interval_def)

lemma intersect_sem_alt: "sem_interval (intersect s1 s2) = 
                          sem_interval s1 \<inter> sem_interval s2" 
     by (auto simp add: intersect_sem sem_interval_def)

lemma elem_sem_alt: "elem a s = (a \<in> (sem_interval s))"
  by (auto simp add: elem_sem sem_interval_def)
end

definition semI :: "'a::linorder \<times> 'a \<Rightarrow> 'a set" where
    "semI s = {e. fst s \<le> e \<and> e \<le> snd s}"

definition empI where
    "empI s = ((snd s) < (fst s))"

definition nempI where
    "nempI s = ((fst s) \<le> (snd s))"


definition intersectI where
    "intersectI s1 s2 = ((if (fst s1) < (fst s2) then fst s2 else fst s1),
                        (if (snd s1) < (snd s2) then snd s1 else snd s2))"



definition elemI where
    "elemI a s = ((fst s) \<le> a \<and> a \<le> (snd s))"


theorem interval_impl_correct: "interval semI empI nempI intersectI elemI"
  by (auto simp add: interval_def empI_def intersectI_def elemI_def semI_def 
       nempI_def)
  

lemma inj_semI_aux: "\<And> x y. semI x \<noteq> {} \<and> semI y \<noteq> {} \<and> semI x = semI y 
                 \<Longrightarrow> fst x = fst y \<and> snd x = snd y"
proof -
  fix x y
  assume ass: "semI x \<noteq> {} \<and> semI y \<noteq> {} \<and> semI x = semI y"
  from this have cons1: "fst x \<le> snd x"
    by (metis (mono_tags, lifting) empI_def interval_def 
        interval_impl_correct not_le_imp_less)
  from ass have cons2: "fst y \<le> snd y"
        by (metis (mono_tags, lifting) empI_def interval_def 
        interval_impl_correct not_le_imp_less)
  from ass cons1 cons2 show "fst x = fst y \<and> snd x = snd y"
    apply (simp add: semI_def)
    using antisym by auto
qed

lemma inj_semI: "\<And> x y. semI x \<noteq> {} \<longrightarrow> semI y \<noteq> {}  \<longrightarrow> (semI x = semI y 
                 \<longleftrightarrow> x = y)"
  using inj_semI_aux by fastforce

lemma inter_correct : "semI (intersectI s1 s2) = 
                       (semI s1 \<inter> semI s2)"
  unfolding intersectI_def
  apply (simp add: if_split)
  apply auto
  apply (metis (mono_tags, lifting) dual_order.strict_trans1 fst_conv interval.sem_interval_def interval_impl_correct mem_Collect_eq order.strict_implies_order snd_conv)
  apply (metis (no_types, lifting) dual_order.strict_implies_order dual_order.strict_trans2 fst_conv interval.sem_interval_def interval_impl_correct mem_Collect_eq snd_conv)
       apply (simp add: semI_def)
  apply (metis (mono_tags, lifting) dual_order.strict_trans1 interval.sem_interval_def interval_impl_correct leI mem_Collect_eq order_less_imp_le)
  apply (metis (mono_tags, lifting) dual_order.strict_implies_order dual_order.strict_trans2 interval.sem_interval_def interval_impl_correct mem_Collect_eq not_le_imp_less)
  apply (metis (no_types, lifting) dual_order.strict_trans1 eq_fst_iff interval.sem_interval_def interval_impl_correct leI mem_Collect_eq snd_conv)
  apply (metis (no_types, lifting) dual_order.strict_trans2 eq_fst_iff interval.sem_interval_def interval_impl_correct mem_Collect_eq not_le_imp_less snd_conv)
  by (metis (no_types, lifting) fst_conv interval.sem_interval_def interval_impl_correct mem_Collect_eq snd_conv)

lemma inter_correct1: "semI (intersectI s1 s2) \<noteq> {} \<longrightarrow>
                       semI s1 \<noteq> {} \<and> semI s2 \<noteq> {}"
  by (auto simp add: inter_correct)

lemma inter_correct2: "semI s1  \<inter> semI s2 \<noteq> {} \<longrightarrow>
                       semI s1 \<noteq> {} \<and> semI s2 \<noteq> {}"
  by (auto simp add: inter_correct)

lemma nempI_correct: "nempI x \<longleftrightarrow> (semI x \<noteq> {})" 
  apply (simp add: nempI_def semI_def)
  by fastforce


lemma nempI_inter_correct: "nempI (intersectI (fst a) (snd a)) \<longleftrightarrow> 
                            semI (fst a) \<inter> semI (snd a) \<noteq> {}"
  by (simp add: inter_correct nempI_correct)

fun canonicalIs :: "('a :: linorder \<times> 'a) list \<Rightarrow> bool" where
  "canonicalIs [] = True" |
  "canonicalIs [i] = (fst i \<le> snd i)" |
  "canonicalIs (i1 # i2 # l) = ((fst i1 \<le> snd i1) \<and> 
                                (fst i2 \<le> snd i2) \<and>
                                (snd i1 < fst i2) \<and> 
                                (\<exists>e. snd i1 < e \<and> e < fst i2) 
                                 \<and> canonicalIs (i2 # l))"


locale intervals = 
  fixes sem_intervals :: "(('a::linorder) \<times> 'a) list \<Rightarrow> 'a set"
  fixes empty_intervals:: "('a \<times> 'a) list \<Rightarrow> bool"
  fixes noempty_intervals:: "('a \<times> 'a) list \<Rightarrow> bool"
  fixes intersect_intervals:: "('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list"
  fixes diff_intervals:: "('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list"
  fixes elem_intervals:: "'a  \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> bool"
  fixes canonical_intervals:: "('a \<times> 'a) list \<Rightarrow> bool"
  assumes 
    sem_interval_def : "sem_intervals s \<equiv> 
                            {e | e i. i \<in> (set s) \<and> (fst i) \<le> e \<and> e \<le> (snd i)}" and
    empty_interval_sem: "canonical_intervals s \<longrightarrow> 
                         empty_intervals s = (sem_intervals s = {})" and
    noempty_intervals_sem: "canonical_intervals s \<longrightarrow> 
                            noempty_intervals s =  (\<not> (empty_intervals s))" and
    intersect_intervals_sem: "canonical_intervals s1 \<and> canonical_intervals s2 \<longrightarrow>
                              sem_intervals (intersect_intervals s1 s2) = 
                              (sem_intervals s1) \<inter> (sem_intervals s2) \<and>
                              canonical_intervals (intersect_intervals s1 s2)" and
    diff_intervals_sem: "canonical_intervals s1 \<and> canonical_intervals s2 \<longrightarrow>
                              sem_intervals (diff_intervals s1 s2) = 
                              (sem_intervals s1) - (sem_intervals s2) \<and>
                              canonical_intervals (diff_intervals s1 s2)" and
    elem_sem: "elem_intervals a s \<equiv>  (a \<in> sem_intervals s)" and
    canonical_intervals_sem: "canonical_intervals s = canonicalIs s"
begin 

end

definition semIs :: "('a :: linorder \<times> 'a) list \<Rightarrow> 'a set" where
  "semIs s = {e | e i. i \<in> (set s) \<and> (fst i) \<le> e \<and> e \<le> (snd i)} "

lemma semIs_head: "semIs (i # l) = semI i \<union> semIs l"
  apply (simp only: set_eq_iff)
  apply simp
proof 
  fix x
  show "(x \<in> semIs (i # l)) = (x \<in> semI i \<or> x \<in> semIs l)"
  proof 
    {
      assume x_in: "x \<in> semIs (i # l)"
      from this semIs_def[of "i#l"] 
           semIs_def[of l] semI_def[of i]
      show "x \<in> semI i \<or> x \<in> semIs l"
        by auto
    }
    {
      assume x_in: "x \<in> semI i \<or> x \<in> semIs l"
      from this semIs_def[of "i#l"] 
           semIs_def[of l] semI_def[of i]
      show "x \<in> semIs (i # l)"
      proof (cases "x \<in> semI i")
        case True
        from this semIs_def[of "i#l"] semI_def[of i]
        show ?thesis by force
        next
          case False
          from this x_in have "x \<in> semIs l" by auto
          from this semIs_def[of "i#l"] semIs_def[of l]
          show ?thesis by auto
        qed 
      }
    qed
  qed


lemma semIs_comp: "semIs (i1 @ i2) = semIs i1 \<union> semIs i2"
  apply (induction i1)
  using semIs_def 
  apply fastforce
  using semIs_head 
  by fastforce

fun empIs :: "('a::linorder \<times> 'a) list \<Rightarrow> bool" where
  "empIs [] = True"
|"empIs (i # r) = ((snd i < fst i) \<and> empIs r)"

lemma empIs_correct: "empIs s = (semIs s = {})"
  apply (induction s)
  apply (simp add: semIs_def)
  apply simp
proof 
  fix a s
  assume ind: "empIs s = (semIs s = {})"
  {
    show "snd a < fst a \<and> semIs s = {} \<Longrightarrow> semIs (a # s) = {}"
    proof -
      assume p1: "snd a < fst a \<and> semIs s = {}"
      from semIs_head[of a s]
      show "semIs (a # s) = {}"
        apply simp
        using p1  semI_def[of a]
        by auto
    qed
  }{
    show "semIs (a # s) = {} \<Longrightarrow> snd a < fst a \<and> semIs s = {}"
    proof -
      assume p1: "semIs (a # s) = {}"
      from this semIs_head[of a s]
      have "semI a = {} \<and> semIs s = {}" by auto
      from this 
      show "snd a < fst a \<and> semIs s = {}"
        by (metis leI nempI_correct nempI_def)
    qed
  }
qed
  
fun intersectIs_aux :: "('a::linorder \<times> 'a) \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list" where
  "intersectIs_aux a [] = []" |
  "intersectIs_aux a (b # l) = 
    (if (nempI (intersectI a b)) then (intersectI a b) # (intersectIs_aux a l)
       else (intersectIs_aux a l))"

fun intersectIs :: "('a::linorder \<times> 'a) list \<Rightarrow> 
                    ('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list" where
  "intersectIs [] l2 = []" |
  "intersectIs (a # l1) l2 = (intersectIs_aux a l2) @ (intersectIs l1 l2)"

lemma canonicalIs_sub: "canonicalIs (a # l) \<Longrightarrow> canonicalIs l"  
  apply (induction l)
  apply simp
  by auto

lemma canonicalIs_concat: "canonicalIs (l1 @ [a]) \<Longrightarrow> canonicalIs (b # l2) \<Longrightarrow>
                           (snd a \<le> fst b \<and> (\<exists>e. snd a < e \<and> e < fst b)) \<Longrightarrow>
                           canonicalIs (l1 @ [a,b] @ l2)"  
  apply (induction l1)
  apply simp
  using canonicalIs.elims(2) dual_order.strict_trans apply auto[1]
proof -
  fix aa l1
  assume ind_hyp: "(canonicalIs (l1 @ [a]) \<Longrightarrow> canonicalIs (b # l2) \<Longrightarrow>
                    snd a \<le> fst b \<and> (\<exists>e>snd a. e < fst b) \<Longrightarrow> 
                    canonicalIs (l1 @ [a, b] @ l2))"
     and pre1: "canonicalIs ((aa # l1) @ [a])"
     and pre2: "canonicalIs (b # l2)"
     and pre3: "snd a \<le> fst b \<and> (\<exists>e>snd a. e < fst b)"

  from pre1 have pre1': "canonicalIs (l1 @ [a])" 
    by (simp add: canonicalIs_sub)

  from ind_hyp[OF pre1' pre2 pre3] pre1
  show "canonicalIs ((aa # l1) @ [a, b] @ l2)"
  proof (cases "l1 \<noteq> []")
    case True
    from this obtain na l1' 
    where na_def: "l1 = na # l1'" 
      using empIs.cases by blast 
    from this ind_hyp[OF pre1' pre2 pre3] pre1
    show ?thesis
      by simp
  next
    case False
    then show ?thesis 
      using \<open>canonicalIs (l1 @ [a, b] @ l2)\<close> pre1 by auto
  qed
qed

    

lemma canonicalIs_remove_snd: "canonicalIs (a # aa # l) \<Longrightarrow> canonicalIs (a # l)"
  apply (induction l)
  apply simp
proof -
  fix ab l
  assume p1: "canonicalIs (a # aa # ab # l)"
  from canonicalIs.simps(3)
  have case0: "canonicalIs (ab # l)" 
    using p1 by auto
   from canonicalIs.simps(3) p1
    have tran1: "fst a \<le> snd a \<and>
          fst aa \<le> snd aa \<and>
          (snd a \<le> fst aa) \<and>
          (\<exists>e. snd a < e \<and>  e < fst aa)" by auto

    from p1 canonicalIs_sub
    have p1': "canonicalIs (aa # ab # l)" by auto

    from p1' canonicalIs.simps(3)
    have tran2: "fst aa \<le> snd aa \<and>
          fst ab \<le> snd ab \<and>
          (snd aa < fst ab) \<and>
          (\<exists>e. snd aa < e \<and>  e < fst ab)" by auto
    
    have case1:
         "fst a \<le> snd a \<and>
          fst ab \<le> snd ab \<and>
          (snd a < fst ab) \<and>
          (\<exists>e. snd a < e \<and>  e < fst ab)"
      apply (rule_tac conjI)
      using tran1 apply simp
      apply (rule_tac conjI)
      using tran2 apply simp
      apply (rule_tac conjI)
      using tran1 tran2 apply force
      using tran1 tran2
      by auto
    from case0 case1 canonicalIs.simps(3)
    show "canonicalIs (a # ab # l)"
      by auto
  qed

lemma canonicalIs_disjoint_head: "canonicalIs (a # l) \<Longrightarrow> semI a \<inter> semIs l = {}"  
  apply (induction l)
  using semIs_def
  apply (simp add: semIs_def)
proof -
  fix aa l
  assume p1: "(canonicalIs (a # l) \<Longrightarrow> semI a \<inter> semIs l = {})"
     and p2: "canonicalIs (a # aa # l)"
  from p2 canonicalIs_remove_snd[of a aa l]
  have cano_a_l: "canonicalIs (a # l)" by simp
   
  from p2 canonicalIs.simps(3)[of a aa l] 
  have "semI a \<inter> semI aa = {}"
    unfolding semI_def
    apply simp
    by fastforce
  from this p1[OF cano_a_l] semIs_head[of aa l]
  show "semI a \<inter> semIs (aa # l) = {}"
    by auto
qed

lemma canonicalIs_fst_notin: "canonicalIs (a # l)  \<Longrightarrow> a \<notin> set l"
  apply (induction l)
  apply simp
  using canonicalIs_remove_snd by fastforce

lemma canonical_distinct: 
         "canonicalIs l \<Longrightarrow> distinct l"
  apply (induction l)
  apply simp
  by (simp add: canonicalIs_fst_notin canonicalIs_sub)

lemma canonical_disjoint: 
  fixes l
  assumes canonical_assm: "canonicalIs l"
  shows "\<forall> i1 i2. i1 \<in> set l \<and> i2 \<in> set l \<and> i1 \<noteq> i2
                              \<longrightarrow> semI i1 \<inter> semI i2 = {}"
  apply (rule allI impI)+
  using canonical_assm
  apply (induction l)
  apply simp
proof -
  {
    fix a l i1 i2
    assume indhyp: "(\<And>i1 i2. i1 \<in> set l \<and> i2 \<in> set l \<and> i1 \<noteq> i2 \<Longrightarrow> canonicalIs l
                                \<Longrightarrow> semI i1 \<inter> semI i2 = {})"
       and i12in: "i1 \<in> set (a # l) \<and> i2 \<in> set (a # l) \<and> i1 \<noteq> i2"
       and canonical_assm': "canonicalIs (a # l)"
    from canonical_assm' canonicalIs_sub[of a l]
    have canl: "canonicalIs l" 
      by auto
    show "semI i1 \<inter> semI i2 = {}"
    proof (cases "i1 \<in> set l \<and> i2 \<in> set l")
      case True
      from True canl indhyp[of i1 i2] i12in
      show ?thesis by auto
    next
      case False
      from this i12in
      have i12in': "(i1 = a \<or> i2 = a) \<and> i1 \<noteq> i2" by auto

      have "\<forall> x \<in> set l. semI x \<subseteq> semIs l"
        apply (induction l)
        apply simp
        using semIs_head by fastforce

      from this i12in' i12in canonicalIs_disjoint_head
                      [of a l, OF canonical_assm']
      show ?thesis 
        by auto
    qed
  }
qed

lemma intersectIs_aux_correct: "semIs (intersectIs_aux a l2) = semI a \<inter> semIs l2"
  apply (induction l2)
  apply simp
  using empIs_correct apply fastforce
  by (simp add: Int_Un_distrib inter_correct nempI_correct semIs_head)


lemma intersectIs_correct': "semIs (intersectIs (a # l1) l2) = 
          (semI a \<inter> semIs l2) \<union> semIs (intersectIs l1 l2)"
  using intersectIs.simps(2)[of a l1 l2]
        intersectIs_aux_correct[of a l2]
  by (simp add: semIs_comp)

lemma intersectIs_aux_hd_rel: "l' = intersectIs_aux a l \<Longrightarrow> 
       (\<forall> b \<in> set l'. fst a \<le> fst b)"
  apply (induction l arbitrary: a l')
  apply simp
proof -
  fix a l aa l'
  assume ind_hyp: "\<And>a l'. l' = intersectIs_aux a l \<Longrightarrow> \<forall>b\<in>set l'. fst a \<le> fst b"
     and pre: "l' = intersectIs_aux aa (a # l)"
  from pre intersectIs_aux.simps(2)[of aa a l]
  have l'_def: "l' = (if nempI (intersectI aa a) then 
                        intersectI aa a # intersectIs_aux aa l else
                        intersectIs_aux aa l)"
    by auto

  obtain l'' where l''_def: "l'' = intersectIs_aux aa l" by auto
  
  from ind_hyp[of l'' aa, OF l''_def] pre l'_def intersectI_def[of aa a]
  show "\<forall>b\<in>set l'. fst aa \<le> fst b"
    using l''_def by auto
qed

lemma intersectIs_hd_rel: 
      "canonicalIs (a # l1) \<Longrightarrow> 
       l = intersectIs (a # l1) l2 \<Longrightarrow> 
       l = a' # l' \<Longrightarrow> fst a \<le> fst a'"
proof -
  assume lcons: "l = intersectIs (a # l1) l2"
     and lcons': "l = a' # l'"
     and lcons'': "canonicalIs (a # l1)"
  thm intersectIs.simps(2)[of a l1 l2]
      intersectIs_aux_hd_rel[of _ a l2]
  show "fst a \<le> fst a'"
  proof (cases "intersectIs_aux a l2 \<noteq> []")
    case True
    from this intersectIs_aux_hd_rel
    show ?thesis 
      by (metis append_eq_Cons_conv intersectIs.simps(2) 
                lcons lcons' list.set_intros(1))
  next
    case False
    from this intersectIs.simps(2)[of a l1 l2]
    have a'_in: "a' \<in> set (intersectIs l1 l2)"
      using lcons lcons' by fastforce
    from this lcons''
    show ?thesis 
      apply (induction l1)
      apply simp
    proof -
      fix aa l1
      assume ind_hyp: "a' \<in> set (intersectIs l1 l2) \<Longrightarrow> canonicalIs (a # l1) \<Longrightarrow> 
                       fst a \<le> fst a'"
         and pre: "a' \<in> set (intersectIs (aa # l1) l2)"
         and pre': "canonicalIs (a # aa # l1)"
      from intersectIs.simps(2)[of aa l1 l2]
      have "intersectIs (aa # l1) l2 = intersectIs_aux aa l2 @ intersectIs l1 l2"
        by auto
      from this pre False
      show "fst a \<le> fst a'"
      proof (cases "intersectIs_aux aa l2 = []")
        case True
        then show ?thesis 
          using ind_hyp pre 
          using canonicalIs_remove_snd pre' by fastforce
      next
        case False 
        from this pre intersectIs_aux_hd_rel[of _ aa l2]
        show ?thesis  
        proof (cases "a' \<in> set (intersectIs_aux aa l2)")
          case True
          from this intersectIs_aux_hd_rel[of _ aa l2]
          show ?thesis 
            using pre' by force
        next
          case False
          then show ?thesis 
            using ind_hyp pre 
            using canonicalIs_remove_snd pre' by fastforce
          qed
      qed
    qed
  qed
qed

lemma canonicalIs_aux : "canonicalIs (a # l) \<Longrightarrow> (a' # l') = intersectIs_aux x (a # l) \<Longrightarrow>
       fst a \<le> fst a'"
proof -
  assume pre1: "canonicalIs (a # l)"
     and pre2: "(a' # l') = intersectIs_aux x (a # l)"
  have c1: "intersectIs_aux x (a # l) = (intersectI x a) # (intersectIs_aux x l) \<or>
        intersectIs_aux x (a # l) = (intersectIs_aux x l)"
    by simp     
  show "fst a \<le> fst a'"
  proof (cases "intersectIs_aux x (a # l) = (intersectI x a) # (intersectIs_aux x l)")
    case True
      then show ?thesis 
      proof -
        have "(fst a', snd a') = intersectI x a"
          using True pre2 by fastforce
        then show ?thesis
          by (simp add: intersectI_def leI)
      qed
    next
      case False
      from this
      have "intersectIs_aux x (a # l) = intersectIs_aux x l" 
        using c1 by blast
      from this pre1 pre2
      show ?thesis 
        apply (induction l arbitrary: l')
         apply simp
      proof -
        fix aa l l'
        assume ind_hyp: "\<And> l'. (intersectIs_aux x (a # l) = intersectIs_aux x l \<Longrightarrow>
                          canonicalIs (a # l) \<Longrightarrow>
                         a' # l' = intersectIs_aux x (a # l) \<Longrightarrow> fst a \<le> fst a')"
           and p1: "intersectIs_aux x (a # aa # l) = intersectIs_aux x (aa # l)"
           and p2: "canonicalIs (a # aa # l)"
           and p3: "a' # l' = intersectIs_aux x (a # aa # l)"
        from p1
        have t1: "intersectIs_aux x (a # l) = intersectIs_aux x l"
          by auto
        from p2
        have t2: "canonicalIs (a # l)"  
          using canonicalIs_remove_snd by blast
        show "fst a \<le> fst a'"
        proof (cases "nempI (intersectI x a)")
          case True
          then show ?thesis 
            using False by auto
          next
            case False
            from this p3
            have "a' # l' = intersectIs_aux x (aa # l)"
              by simp
            from this
            show ?thesis 
            proof (cases "nempI (intersectI x aa)")
              case True
              have "fst a \<le> fst aa" 
                using p2 by auto
              from p3 True False
              have "a' # l' = (intersectI x aa) # (intersectIs_aux x l)"
                by auto
              from this
              have "a' = (intersectI x aa)" by auto
              from this intersectI_def[of x aa]
              have "fst aa \<le> fst a'"
                by auto
              then show ?thesis 
                using \<open>fst a \<le> fst aa\<close> dual_order.trans by blast
              next
                case False
                from this 
                have t3: "a' # l' = intersectIs_aux x (a # l)"  
                  by (simp add: p3)
                from ind_hyp[OF t1 t2 t3]
                show ?thesis by auto
              qed
          qed
        qed
      qed
    qed

lemma intersectIs_correct : 
  "canonicalIs l1 \<and> canonicalIs l2 \<Longrightarrow>
        semIs (intersectIs l1 l2) = semIs l1 \<inter> semIs l2 \<and>
        canonicalIs (intersectIs l1 l2)"
  apply (induction l1 rule: canonicalIs.induct)
  apply simp
  using empIs.simps(1) empIs_correct apply blast
proof -
  {
    fix i
    show "canonicalIs [i] \<and> canonicalIs l2 \<Longrightarrow>
         semIs (intersectIs [i] l2) = semIs [i] \<inter> semIs l2 \<and>
         canonicalIs (intersectIs [i] l2)"
    proof -
      assume pre: "canonicalIs [i] \<and> canonicalIs l2"
      from intersectIs_correct'[of i "[]" l2]
      have case1: "semIs (intersectIs [i] l2) = semIs [i] \<inter> semIs l2"
        by (metis empIs.simps(1) empIs_correct intersectIs.simps(1) 
                  semIs_head sup_bot.right_neutral)
    
      from pre
      have "canonicalIs l2" by auto
      from this
      have case2: "canonicalIs (intersectIs [i] l2)"
        apply (induction l2)
        apply simp
      proof -
        fix a l2
        assume pre': "canonicalIs l2 \<Longrightarrow> canonicalIs (intersectIs [i] l2)"
           and pre'': "canonicalIs (a # l2)"
        have intersectIsial2: 
              "intersectIs [i] (a # l2) = 
              (intersectI i a) # (intersectIs [i] l2) \<or> 
              (intersectIs [i] (a # l2) = 
              (intersectIs [i] l2))"
          by auto
        have "\<exists>l a' l'. l = intersectIs [i] l2 \<and> (l = [] \<or> 
                      (l = (a' # l') \<and> fst i \<le> fst a'))"
          apply (induction l2)
          apply simp
          using intersectIs_hd_rel
          by (metis neq_Nil_conv pre)
        from this obtain l a' l' where
        lal'_def: "l = intersectIs [i] l2 \<and> (l = [] \<or> 
                   l = a' # l' \<and> fst i \<le> fst a')" by force
        from this intersectIsial2 pre' canonicalIs_concat
        show "canonicalIs (intersectIs [i] (a # l2))"
        proof (cases "intersectIs [i] (a # l2) = intersectIs [i] l2")
          case True
          then show ?thesis 
            using canonicalIs_sub pre' pre'' 
            by fastforce
        next
          case False
          from this intersectIsial2
          have eqis: "intersectIs [i] (a # l2) = intersectI i a # intersectIs [i] l2"
            by auto
          from this
          have "intersectIs [i] (a # l2) = [intersectI i a]  @ intersectIs [i] l2"
            by auto
          have t1: "canonicalIs ([] @ [intersectI i a])"
            using False nempI_def by fastforce
          show ?thesis 
          proof (cases "intersectIs [i] l2 = []")
            case True
            then show ?thesis 
              using t1 by auto
          next
            case False
            from this obtain b l' where
            bl'_def: "b # l' = intersectIs [i] l2"
              using lal'_def by fastforce
            obtain a2 l2' where a2l2'_def: "l2 = a2 # l2'"
              by (metis False append_Nil2 empIs.cases intersectIs.simps(1) 
                        intersectIs.simps(2) intersectIs_aux.simps(1))
            from bl'_def a2l2'_def canonicalIs_aux[of a2 l2' b l' i]
            have fsta2b: "fst a2 \<le> fst b" 
              using pre'' by auto
            have t2: "canonicalIs l2" 
              using canonicalIs_sub pre'' by blast
            have t2': "canonicalIs (b # l')" 
              using bl'_def pre' t2 by auto
            from pre'' this bl'_def intersectIs_hd_rel[of i "[]" "b # l'" l2 b l']
            have "fst i \<le> fst b" 
              using pre by blast
            from pre'' a2l2'_def canonicalIs.simps(3)[of a a2 l2]                 
            have "snd a < fst a2 \<and> (\<exists>e>snd a. e < fst a2)"
              by auto
            from this intersectI_def[of i a] fsta2b
            have "snd (intersectI i a) \<le> fst b \<and> 
                  (\<exists>e>snd (intersectI i a). e < fst b)" 
              by auto 
            from  this canonicalIs_concat[of "[]" "intersectI i a" b l', OF t1 t2']
            have "canonicalIs ([] @ [intersectI i a, b] @ l')"
              by auto
            from this
            show ?thesis 
              using bl'_def eqis by auto  
          qed
        qed
      qed 

    from case1 case2
    show "semIs (intersectIs [i] l2) = semIs [i] \<inter> semIs l2 \<and>
          canonicalIs (intersectIs [i] l2)"
      by auto
  qed
  }
  {
    fix i1 i2 l
    assume ind_hyp: "(canonicalIs (i2 # l) \<and> canonicalIs l2 \<Longrightarrow>
                      semIs (intersectIs (i2 # l) l2) = semIs (i2 # l) \<inter> semIs l2 \<and>
                      canonicalIs (intersectIs (i2 # l) l2))"
       and pre: "canonicalIs (i1 # i2 # l) \<and> canonicalIs l2"

    from pre 
    have pre': "canonicalIs (i2 # l) \<and> canonicalIs l2" 
      using canonicalIs_sub by blast

    from ind_hyp[OF pre']
    have case1: "semIs (intersectIs (i1 # i2 # l) l2) = 
                 semIs (i1 # i2 # l) \<inter> semIs l2"
      by (metis Int_Un_distrib2 intersectIs_correct' semIs_head)

    note intersectIs' =  intersectIs.simps(2)[of i1 "i2 # l" l2]

    from pre
    have c1: "canonicalIs (intersectIs_aux i1 l2)"
     using \<open>\<And>i. canonicalIs [i] \<and> canonicalIs l2 \<Longrightarrow> 
            semIs (intersectIs [i] l2) = semIs [i] \<inter> semIs l2 \<and> 
            canonicalIs (intersectIs [i] l2)\<close> by auto

   from ind_hyp[OF pre']
   have spart: "canonicalIs (intersectIs (i2 # l) l2)" by auto

    from ind_hyp[OF pre'] pre canonicalIs_concat
    have case2: "canonicalIs (intersectIs (i1 # i2 # l) l2)"
    proof (cases "intersectIs_aux i1 l2 = []")
    case True
    then show ?thesis 
      using \<open>semIs (intersectIs (i2 # l) l2) = semIs (i2 # l) \<inter> semIs l2 \<and> 
              canonicalIs (intersectIs (i2 # l) l2)\<close> by auto
    next
      case False
      from this obtain 
      ll tt1 where
      hd1tl1_def: "intersectIs_aux i1 l2 = ll @ [tt1]"
        using rev_exhaust by blast
      from this have fpart: "canonicalIs (ll @ [tt1])"
        using c1 by auto
      from spart
      show ?thesis 
      proof (cases "intersectIs (i2 # l) l2 = []")
      case True
        then show ?thesis 
          by (simp add: c1)
      next
        case False
        from this
        obtain tt2 ll2
        where tt2ll2_def: "intersectIs (i2 # l) l2 = tt2 # ll2"
          using empIs.cases by blast  
        from this spart
        have spart': "canonicalIs (tt2 # ll2)" by auto

        have c2: "fst i2 \<le> fst tt2"
          using intersectIs_hd_rel pre' tt2ll2_def by blast
        from pre
        have c1: "snd i1 \<le> fst i2 \<and> (\<exists> e. snd i1 < e \<and> e < fst i2)"
          by (simp add: order.strict_implies_order)
        from hd1tl1_def
        have "snd tt1 \<le> snd i1"
          apply (induction l2 arbitrary: ll)
          apply simp
        proof -
          fix a l2 ll
          assume ind_hyp: "\<And> ll. intersectIs_aux i1 l2 = ll @ [tt1] \<Longrightarrow> 
                               snd tt1 \<le> snd i1"
             and pre'': "intersectIs_aux i1 (a # l2) = ll @ [tt1]"
          show "snd tt1 \<le> snd i1"
          proof (cases "nempI (intersectI i1 a)")
            case True
            from this 
            have c1: "intersectIs_aux i1 (a # l2) = 
                  (intersectI i1 a) # (intersectIs_aux i1 l2)"
              by auto
            from this pre''
            show ?thesis 
            proof (cases "ll = []")
              case True
              from this c1 pre''
              have "intersectI i1 a = tt1"  by auto
              from this intersectI_def[of i1 a]
              show ?thesis by auto
            next
              case False
              from this obtain ll' aa' where
              llaa'_def: "ll = aa' # ll'" 
                using empIs.cases by blast
              from this c1 pre''
              have "intersectI i1 a = aa'"
                by auto
              have c2: "intersectIs_aux i1 l2 = ll' @ [tt1]"
                using c1 llaa'_def pre'' by auto
              from ind_hyp[OF c2]
              show ?thesis by simp
            qed
          next
          case False
            then show ?thesis 
              using ind_hyp pre'' by auto
          qed
        qed
        from this c2 c1
        have t3: "snd tt1 \<le> fst tt2 \<and> (\<exists>e>snd tt1. e < fst tt2)"
          using dual_order.strict_trans2 by fastforce

    from intersectIs' canonicalIs_concat[OF fpart spart' t3]
    show ?thesis 
      using hd1tl1_def tt2ll2_def by auto
      qed
    
    qed
    from this case1
    show "semIs (intersectIs (i1 # i2 # l) l2) = semIs (i1 # i2 # l) \<inter> semIs l2 \<and>
          canonicalIs (intersectIs (i1 # i2 # l) l2)"
      by auto
  }
qed

fun diffI :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 
             'a::linorder \<times> 'a \<Rightarrow> 'a \<times> 'a \<Rightarrow> ('a \<times> 'a) list " where
  "diffI suc pre ib is = (
  if (fst ib > snd ib) then []
   else (
    if (fst is > snd is) then [ib]
     else (
       if (snd is < fst ib) then [ib]
        else (
         if (snd is < snd ib) then 
          (if (fst is \<le> fst ib) then [(suc (snd is), snd ib)]
           else [(fst ib, pre (fst is)), (suc (snd is), snd ib)])
            else (
          if (fst is > snd ib) then [ib]
          else (
            if (fst is \<le> fst ib) then [] else
            [(fst ib, pre (fst is))]))))))"

fun elemIA :: "('a::linorder) \<Rightarrow> ('a \<times> 'a) list  \<Rightarrow> bool" where  
    "elemIA e is = (\<exists> i \<in> set is. fst i \<le> e \<and> e \<le> snd i )"


definition semIA :: "('a :: linorder \<times> 'a) list \<Rightarrow> 'a set" where
    "semIA itv = {e . elemIA e itv}"

lemma elemIA_semIA:
  "elemIA a \<sigma> \<longleftrightarrow> a \<in> semIA \<sigma>"
  by (simp add: semIA_def)

definition subIA :: "('a :: linorder \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> bool" where
     "subIA i1 i2 = (semIA i1 \<subseteq> semIA i2)"


lemma diffI_correct_aux:
  fixes f1 :: "'a ::linorder \<Rightarrow> 'a" 
  fixes f2 :: "'a ::linorder \<Rightarrow> 'a"
  assumes f1_cons: "\<forall> a. a < f1 a \<and> (\<forall> b. a < b \<longrightarrow> f1 a \<le> b)"
     and  f2_cons: "\<forall> a. a > f2 a \<and> (\<forall> b. a > b \<longrightarrow> f2 a \<ge> b)"
     and  ib_cano: "fst ib \<le> snd ib"
     and  is_cano: "fst is \<le> snd is"
   shows "semIA (diffI f1 f2 ib is) = (semI ib - semI is) \<and>
          canonicalIs (diffI f1 f2 ib is) \<and> 
          ((diffI f1 f2 ib is) \<noteq> [] \<longrightarrow>  fst ib \<le> fst (hd (diffI f1 f2 ib is))
                                       \<and> snd (last (diffI f1 f2 ib is)) \<le> snd ib)"
proof (cases "fst ib > snd ib")
  case True
  then show ?thesis 
    unfolding diffI.simps intersectI_def
    apply simp
    unfolding semIA_def semI_def
    by auto
next
  case False
  note else1 = False
  show ?thesis 
  proof (cases "fst is > snd is")
    case True
    show ?thesis 
      unfolding diffI.simps
      apply (simp add: True else1)
      unfolding semIA_def semI_def 
      apply (rule conjI)
      using True apply auto
      using ib_cano by blast
  next
    case False
    note else2 = False
    show ?thesis 
    proof (cases "snd is < fst ib")
      case True 
      show ?thesis
        apply (simp add: True else1 else2)
        unfolding semIA_def semI_def elemIA.simps
        using True
        apply auto[1]
        using ib_cano by blast
    next
      case False
      note else3 = False
      show ?thesis 
      proof (cases "snd is < snd ib")
        case True
        note then1= True
        then show ?thesis 
          proof (cases "fst is \<le> fst ib")
            case True
            show ?thesis
              unfolding diffI.simps
              apply (simp add: True then1 else1 else2 else3)
              unfolding semIA_def semI_def elemIA.simps
              apply simp
              using True then1 else1 else2 else3 f1_cons f2_cons
              by fastforce
          next
            case False
            note else4 = False
            show ?thesis 
              unfolding diffI.simps
              apply (simp add: then1 else1 else2 else3 else4)
              unfolding semIA_def semI_def elemIA.simps
              apply simp
              using False then1 else1 else2 else3 f1_cons f2_cons
              apply auto
              apply (meson leI order.strict_implies_order order.trans)
              apply force
              apply (meson not_le order.trans)
              apply force
              apply (metis dual_order.order_iff_strict 
                           dual_order.strict_trans is_cano)
              using is_cano le_less_trans by blast
          qed
      next
        case False
        note else5 = False
        show ?thesis 
        proof (cases "fst is > snd ib")
          case True
          show ?thesis 
            unfolding diffI.simps
            apply (simp add: True else1 else2 else3 else5)
            unfolding semIA_def semI_def elemIA.simps
            using True else1 else2 else3 else5
            by auto
        next
          case False
          note else6 = False
          show ?thesis 
          proof (cases "fst is \<le> fst ib")
            case True
            show ?thesis 
              unfolding diffI.simps
              apply (simp add: True else1 else2 else3 else5 else6)
              unfolding semIA_def semI_def elemIA.simps
              using True else1 else2 else3 else5 else6
              by force
          next
            case False
            show ?thesis 
              unfolding diffI.simps
              apply (simp add: False else1 else2 else3 else5 else6)
              unfolding semIA_def semI_def elemIA.simps
              apply simp
              using False else1 else2 else3 else5 else6 f1_cons f2_cons
              apply auto
               apply (meson dual_order.order_iff_strict not_le order.trans)
               apply (meson not_le order.trans)
              using less_trans not_le_imp_less by blast
          qed 
        qed
      qed
    qed
  qed
qed

lemma semIs_eq_semIA: "semIs l = semIA l"
  unfolding semIs_def semIA_def elemIA.simps
  by blast

lemma diffI_correct:
  fixes f1 :: "'a ::linorder \<Rightarrow> 'a" 
  fixes f2 :: "'a ::linorder \<Rightarrow> 'a"
  assumes f1_cons: "\<forall> a. a < f1 a \<and> (\<forall> b. a < b \<longrightarrow> f1 a \<le> b)"
     and  f2_cons: "\<forall> a. a > f2 a \<and> (\<forall> b. a > b \<longrightarrow> f2 a \<ge> b)"
     and  ib_cano: "fst ib \<le> snd ib"
     and  is_cano: "fst is \<le> snd is"
   shows "semIs (diffI f1 f2 ib is) = (semI ib - semI is) \<and>
          canonicalIs (diffI f1 f2 ib is) \<and> 
          ((diffI f1 f2 ib is) \<noteq> [] \<longrightarrow>  fst ib \<le> fst (hd (diffI f1 f2 ib is))
                                       \<and> snd (last (diffI f1 f2 ib is)) \<le> snd ib)"
  using diffI_correct_aux[OF f1_cons f2_cons ib_cano is_cano]
        semIs_eq_semIA
  by (simp add: semIs_eq_semIA)
  


fun diffIs_aux :: "('a::linorder \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow>  
                   ('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) \<Rightarrow> ('a \<times> 'a) list" where
  "diffIs_aux suc pre [] i = []" |
  "diffIs_aux suc pre (a # l) i = (diffI suc pre a i) @ (diffIs_aux suc pre l i)"


lemma diffIs_aux_correct:
  fixes f1 :: "'a ::linorder \<Rightarrow> 'a" 
  fixes f2 :: "'a ::linorder \<Rightarrow> 'a"
  assumes f1_cons: "\<forall> a. a < f1 a \<and> (\<forall> b. a < b \<longrightarrow> f1 a \<le> b)"
     and  f2_cons: "\<forall> a. a > f2 a \<and> (\<forall> b. a > b \<longrightarrow> f2 a \<ge> b)"
     and  l_cano: "canonicalIs l"
     and  i_cano: "fst i \<le> snd i"
   shows "semIs (diffIs_aux f1 f2 l i) = (semIs l - semI i) \<and>
          canonicalIs (diffIs_aux f1 f2 l i) \<and> 
          ((diffIs_aux f1 f2 l i) \<noteq> [] \<longrightarrow>  
            fst (hd l) \<le> fst (hd (diffIs_aux f1 f2 l i))
              \<and> snd (last (diffIs_aux f1 f2 l i)) \<le> snd (last l))"
  using l_cano
  apply (induction l)
  using empIs_correct apply force
proof -
  fix a l
  assume ind_hyp: "canonicalIs l \<Longrightarrow>
                   semIs (diffIs_aux f1 f2 l i) = semIs l - semI i \<and>
                   canonicalIs (diffIs_aux f1 f2 l i) \<and>
                   (diffIs_aux f1 f2 l i \<noteq> [] \<longrightarrow>
                   fst (hd l) \<le> fst (hd (diffIs_aux f1 f2 l i)) \<and>
                   snd (last (diffIs_aux f1 f2 l i)) \<le> snd (last l))"
     and pre: "canonicalIs (a # l)"
  from pre 
  have a_cons: "fst a \<le> snd a"
    by (metis canonicalIs.simps(2) 
              canonicalIs.simps(3) diffIs_aux.elims)
  note diffI_correct' = diffI_correct[OF f1_cons f2_cons a_cons i_cano]
  from ind_hyp pre
  have diffIs_aux_res: "semIs (diffIs_aux f1 f2 l i) = semIs l - semI i" 
    using canonicalIs_sub by blast

  from diffIs_aux.simps(2)[of f1 f2 a l i]
  have sem_diffis_aux: "semIs (diffIs_aux f1 f2 (a # l) i) = 
                        semIs (diffI f1 f2 a i) \<union> semIs (diffIs_aux f1 f2 l i)"
    by (simp add: semIs_comp)

  from ind_hyp pre
  have semIs_diffI: "semIs (diffI f1 f2 a i) = semI a - semI i"
    using diffI_correct' by linarith

  from sem_diffis_aux semIs_diffI diffIs_aux_res
  have case1: "semIs (diffIs_aux f1 f2 (a # l) i) = semIs (a # l) - semI i"
    by (simp add: Un_Diff semIs_head)

  from ind_hyp pre
  have "canonicalIs (diffIs_aux f1 f2 l i)" 
    using canonicalIs_sub by blast
  thm diffIs_aux.simps(2)[of f1 f2 a l i]

  thm diffI_correct[OF f1_cons f2_cons a_cons i_cano]
  have c1: "canonicalIs (diffI f1 f2 a i) \<and> (diffI f1 f2 a i \<noteq> [] \<longrightarrow> 
      snd (last (diffI f1 f2 a i)) \<le> snd a)" 
    using diffI_correct' by blast
  have case2: "canonicalIs (diffIs_aux f1 f2 (a # l) i) "
  proof (cases "diffI f1 f2 a i = []")
    case True
    from this diffIs_aux.simps(2)[of f1 f2 a l i]
    show ?thesis 
      by (simp add: \<open>canonicalIs (diffIs_aux f1 f2 l i)\<close>)
  next
    case False
    from this
    obtain ft fl where
    fdfl_def: "diffI f1 f2 a i = fl @ [ft]"
      using rev_exhaust by blast
    from this c1
    have c3: "snd ft \<le> snd a"
      by simp
    from this diffIs_aux.simps(2)[of f1 f2 a l i]
    show ?thesis 
    proof (cases "diffIs_aux f1 f2 l i = []")
      case True
      then show ?thesis 
        using diffI_correct' by auto
    next
      case False
      from this have "l \<noteq> []"
        using diffIs_aux.simps(1) by blast
      from this obtain lh ll where
      lhll_def: "l = lh # ll" 
        using empIs.cases by blast
      from False obtain sh sl
        where shsl_def: "diffIs_aux f1 f2 l i = sh # sl"
        using empIs.cases by blast

      have c2: "fst lh \<le> fst sh"
        using ind_hyp lhll_def pre shsl_def by auto

      have c4: "canonicalIs (fl @ [ft])"
        using c1 fdfl_def by auto

      have c5: "canonicalIs (sh # sl)"
        using \<open>canonicalIs (diffIs_aux f1 f2 l i)\<close> shsl_def by auto

      have c6: "snd ft \<le> fst sh \<and> (\<exists>e>snd ft. e < fst sh)"
        using c2 c3 dual_order.order_iff_strict dual_order.strict_trans1 
              lhll_def pre by fastforce

     from c2 c3 canonicalIs_concat[of fl ft sh sl, OF c4 c5 c6]
     show ?thesis 
        using fdfl_def shsl_def by auto
    qed
  qed

  from ind_hyp pre
  have pre': "(diffIs_aux f1 f2 l i \<noteq> [] \<longrightarrow>
              fst (hd l) \<le> fst (hd (diffIs_aux f1 f2 l i)) \<and>
              snd (last (diffIs_aux f1 f2 l i)) \<le> snd (last l))"
    using canonicalIs_sub by blast
  
  have case3: "(diffIs_aux f1 f2 (a # l) i \<noteq> [] \<longrightarrow>
            fst (hd (a # l)) \<le> fst (hd (diffIs_aux f1 f2 (a # l) i)) \<and>
            snd (last (diffIs_aux f1 f2 (a # l) i)) \<le> snd (last (a # l)))"
    apply (rule impI)
  proof -
    assume p1: "diffIs_aux f1 f2 (a # l) i \<noteq> []"

    from diffIs_aux.simps(2)[of f1 f2 a l i]
    show "fst (hd (a # l)) \<le> fst (hd (diffIs_aux f1 f2 (a # l) i)) \<and>
          snd (last (diffIs_aux f1 f2 (a # l) i)) \<le> snd (last (a # l))"
    proof (cases "diffI f1 f2 a i = []")
      case True note fpartnot = True
      show ?thesis
      proof (cases "diffIs_aux f1 f2 l i = []")
        case True 
        from this fpartnot
        show ?thesis 
          using p1 by auto
      next
        case False
        from pre' False
        have c0: "fst (hd l) \<le> fst (hd (diffIs_aux f1 f2 l i)) \<and>
              snd (last (diffIs_aux f1 f2 l i)) \<le> snd (last l)" by auto
        from pre
        have "fst a \<le> fst (hd l)" 
        proof -
          have "l \<noteq> []"
            using fpartnot p1 by force
          then show ?thesis
            by (metis canonicalIs.simps(3) empIs.cases linear list.sel(1) not_le order.trans pre)
        qed
        from this c0
        show ?thesis 
          using fpartnot p1 by auto
      qed
    next
      case False note spartnot = False
      from False diffIs_aux.simps(2)[of f1 f2 a l i] pre'
      show ?thesis 
      proof (cases "diffIs_aux f1 f2 l i \<noteq> []")
        case True
        then show ?thesis 
          using False diffI_correct' pre' by auto
        next
          case False
          thm diffI_correct' spartnot
          have "fst a \<le> fst (hd (diffI f1 f2 a i)) \<and> 
                      snd (last (diffI f1 f2 a i)) \<le> snd a"
            using diffI_correct' spartnot by blast
          from pre
          have "snd a \<le> snd (last (a # l))"
            apply (induction l)
            apply simp
            by (metis (mono_tags) canonicalIs.simps(3) canonicalIs_remove_snd 
                last.simps linear not_le order.trans)
          from False spartnot pre' this diffIs_aux.simps(2)[of f1 f2 a l i]       
          show ?thesis
            using diffI_correct' by force
          qed
    qed
  qed
  from case1 case2 case3
  show "semIs (diffIs_aux f1 f2 (a # l) i) = semIs (a # l) - semI i \<and>
           canonicalIs (diffIs_aux f1 f2 (a # l) i) \<and>
           (diffIs_aux f1 f2 (a # l) i \<noteq> [] \<longrightarrow>
            fst (hd (a # l)) \<le> fst (hd (diffIs_aux f1 f2 (a # l) i)) \<and>
            snd (last (diffIs_aux f1 f2 (a # l) i)) \<le> snd (last (a # l)))"
    by auto
qed

fun diffIs :: "('a::linorder \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 
                  ('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list" where
  "diffIs suc pre l1 [] = l1" |
  "diffIs suc pre l1 (i # l2) = diffIs suc pre (diffIs_aux suc pre l1 i) l2"


lemma diffIs_correct:
  fixes f1 :: "'a ::linorder \<Rightarrow> 'a" 
  fixes f2 :: "'a ::linorder \<Rightarrow> 'a"
  assumes f1_cons: "\<forall> a. a < f1 a \<and> (\<forall> b. a < b \<longrightarrow> f1 a \<le> b)"
     and  f2_cons: "\<forall> a. a > f2 a \<and> (\<forall> b. a > b \<longrightarrow> f2 a \<ge> b)"
     and  l1_cano: "canonicalIs l1"
     and  l2_cano: "canonicalIs l2"
   shows "semIs (diffIs f1 f2 l1 l2) = (semIs l1 - semIs l2) \<and>
          canonicalIs (diffIs f1 f2 l1 l2)"
  using l1_cano l2_cano
  apply (induction l2 arbitrary: l1)
  using empIs_correct apply force
proof -
  fix a l2 l1
  show "(\<And>l1. canonicalIs l1 \<Longrightarrow>
              canonicalIs l2 \<Longrightarrow>
              semIs (diffIs f1 f2 l1 l2) = semIs l1 - semIs l2 \<and>
              canonicalIs (diffIs f1 f2 l1 l2)) \<Longrightarrow>
       canonicalIs l1 \<Longrightarrow>
       canonicalIs (a # l2) \<Longrightarrow>
       semIs (diffIs f1 f2 l1 (a # l2)) = semIs l1 - semIs (a # l2) \<and>
       canonicalIs (diffIs f1 f2 l1 (a # l2))"
  proof -
  assume ind_hyp: "\<And>l1. canonicalIs l1 \<Longrightarrow>
              canonicalIs l2 \<Longrightarrow>
              semIs (diffIs f1 f2 l1 l2) = semIs l1 - semIs l2 \<and>
              canonicalIs (diffIs f1 f2 l1 l2)"
     and pre1: "canonicalIs l1"
     and pre2: "canonicalIs (a # l2)"

  have a_cons : "fst a \<le> snd a"
    using canonicalIs.elims(2) pre2 by blast


  let ?l1 = "(diffIs_aux f1 f2 l1 a)"
  from diffIs_aux_correct[OF f1_cons f2_cons pre1 a_cons]
  have canol1': "canonicalIs ?l1" by auto
  from pre2 
  have pre2': "canonicalIs l2" 
    using canonicalIs_sub by blast

  have "semIs (a # l2) = semI a \<union> semIs l2"
    by (metis semIs_head)

  from this diffIs_aux_correct[OF f1_cons f2_cons pre1 a_cons]
  have "semIs (diffIs_aux f1 f2 l1 a) - semIs l2 = 
        semIs l1 - semIs (a # l2)"
    apply simp
    by blast
    

  from this ind_hyp[of ?l1, OF canol1' pre2'] diffIs.simps(2)[of f1 f2 l1 a l2]
  show "semIs (diffIs f1 f2 l1 (a # l2)) = semIs l1 - semIs (a # l2) \<and>
       canonicalIs (diffIs f1 f2 l1 (a # l2))"
    apply (rule_tac conjI)
    defer
    apply simp
    by simp
qed
qed

fun eqIs :: "('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> bool" where
  "eqIs [] [] = True"
| "eqIs (a1 # l1) (a2 # l2) = ((a1 = a2) \<and> eqIs l1 l2)"
| "eqIs [] (a2 # l2) = False"
| "eqIs (a1 # l1) [] = False"

lemma eqIs_corret: "eqIs l1 l2 = (l1 = l2)"
  apply (induction l1 l2 rule: eqIs.induct)
  by auto

lemma inj_semIs_aux: "\<And> l1 l2. canonicalIs l1 \<and> canonicalIs l2 \<and> semIs l1 = semIs l2 
                 \<Longrightarrow> l1 = l2"
proof -
  fix l1 l2
  assume pre: "canonicalIs l1 \<and> canonicalIs l2 \<and> semIs l1 = semIs l2"
  from pre
  show "l1 = l2"
  apply (induction l1 l2 rule: eqIs.induct)
  apply simp
  proof -
    {
      fix a2 l2
      assume p1: "canonicalIs [] \<and> canonicalIs (a2 # l2) \<and> semIs [] = semIs (a2 # l2)"
      from this
      have "semIs (a2 # l2) \<noteq> {}"
        by (metis (full_types) canonicalIs.simps(2) 
                  canonicalIs.simps(3) empIs.simps(2) empIs_correct 
                   leD map_tailrec_rev.elims)
      from this p1
      show "[] = a2 # l2"
        using empIs.simps(1) empIs_correct by blast
    }
{
      fix a1 l1
      assume p1: "canonicalIs (a1 # l1) \<and> canonicalIs [] \<and> semIs (a1 # l1) = semIs []"
      from this
      have "semIs (a1 # l1) \<noteq> {}"
        by (metis (full_types) canonicalIs.simps(2) 
                  canonicalIs.simps(3) empIs.simps(2) empIs_correct 
                   leD map_tailrec_rev.elims)
      from this p1
      show "a1 # l1 = []"
        using empIs.simps(1) empIs_correct by blast
    }
    {
      fix a1 l1 a2 l2
      assume p1: "(canonicalIs l1 \<and> canonicalIs l2 \<and> semIs l1 = semIs l2 \<Longrightarrow> l1 = l2)"
         and p2: "canonicalIs (a1 # l1) \<and>
                  canonicalIs (a2 # l2) \<and> semIs (a1 # l1) = semIs (a2 # l2)"
      have a1l1nempty: "semI a1 \<inter> semIs l1 = {} \<and> semIs (a1 # l1) = semI a1 \<union> semIs l1"
        by (simp add: canonicalIs_disjoint_head p2 semIs_head)


      have a2l2nempty: "semI a2 \<inter> semIs l2 = {} \<and> semIs (a2 # l2) = semI a2 \<union> semIs l2" 
        by (simp add: canonicalIs_disjoint_head p2 semIs_head)

      

      show "a1 # l1 = a2 # l2 "
      proof (cases "semI a1 = semI a2")
        case True
        from this a1l1nempty a2l2nempty
        have "semIs l1 = semIs l2" 
          using p2 by auto
        from this True p1
        have "l1 = l2" 
          using canonicalIs_sub p2 by blast
        from p2
        have "fst a1 \<le> snd a1 \<and> fst a2 \<le> snd a2"
          using canonicalIs.elims(2) by auto
        from this semI_def
        have "semI a1 \<noteq> {} \<and> semI a2 \<noteq> {}"
          by blast
        from True
        have "a1 = a2" 
          using \<open>semI a1 \<noteq> {} \<and> semI a2 \<noteq> {}\<close> inj_semI by blast
        from this
        show ?thesis 
          using \<open>l1 = l2\<close> by blast 
      next
        case False
        from this semI_def
        have neqor: "fst a1 \<noteq> fst a2 \<or> snd a1 \<noteq> snd a2"
          by metis
        have case1: "fst a1 \<noteq> fst a2 \<longrightarrow> 
                      semIs (a1 # l1) \<noteq> semIs (a2 # l2)"
        proof (cases "fst a1 < fst a2")
          case True 
          from p2
          have "canonicalIs (a2 # l2)" by auto
          from this True
          have "fst a1 \<in> semI a1 \<and> fst a1 \<notin> semIs (a2 # l2)"
            apply (rule_tac conjI)
            using semI_def 
            using canonicalIs.elims(2) p2 apply blast
            apply (induction l2)
            apply (metis (no_types, lifting) CollectD a2l2nempty empIs.simps(1) 
                    empIs_correct leD semI_def semIs_head sup_inf_absorb)
          proof -
            fix a l2
            assume ind_hyp': "(canonicalIs (a2 # l2) \<Longrightarrow> 
                              fst a1 < fst a2 \<Longrightarrow> fst a1 \<notin> semIs (a2 # l2))"
               and pre1: "canonicalIs (a2 # a # l2)"
               and pre2: "fst a1 < fst a2"
            have c1: "fst a1 \<notin> semI a2" 
              by (meson elemI_def interval.elem_sem_alt interval_impl_correct leD pre2)
            have c2: "fst a1 \<notin> semI a" 
              by (metis (no_types, lifting) CollectD canonicalIs.simps(3) 
                      dual_order.strict_trans leD less_le_trans pre1 pre2 semI_def) 
            from ind_hyp' pre1
            have c3: "fst a1 \<notin> semIs (a2 # l2)" 
              using canonicalIs_remove_snd pre2 by blast
            from c1 c2 c3 semIs_head
            show "fst a1 \<notin> semIs (a2 # a # l2)"
              by (simp add: semIs_head)
          qed
          from this
          show ?thesis 
            using a1l1nempty by blast
        next
          case False note fal1 = False
          from this neqor 
          show ?thesis
            apply (rule_tac impI)
          proof -
            assume pp1: "fst a1 \<noteq> fst a2"
            from False pp1 have nc1: "fst a2 < fst a1" by auto
            from p2
          have "canonicalIs (a1 # l1)" by auto
          from this nc1
          have "fst a2 \<in> semI a2 \<and> fst a2 \<notin> semIs (a1 # l1)"
            apply (rule_tac conjI)
            using semI_def 
            using canonicalIs.elims(2) p2 apply blast
            apply (induction l1)
            apply (metis (no_types, lifting) CollectD a1l1nempty empIs.simps(1) 
                    empIs_correct leD semI_def semIs_head sup_inf_absorb)
          proof -
            fix a l1
            assume ind_hyp': "(canonicalIs (a1 # l1) \<Longrightarrow> 
                              fst a2 < fst a1 \<Longrightarrow> fst a2 \<notin> semIs (a1 # l1))"
               and pre1: "canonicalIs (a1 # a # l1)"
               and pre2: "fst a2 < fst a1"
            have c1: "fst a2 \<notin> semI a1" 
              by (meson elemI_def interval.elem_sem_alt interval_impl_correct leD pre2)
            have c2: "fst a2 \<notin> semI a" 
              by (metis (no_types, lifting) CollectD canonicalIs.simps(3) 
                      dual_order.strict_trans leD less_le_trans pre1 pre2 semI_def) 
            from ind_hyp' pre1
            have c3: "fst a2 \<notin> semIs (a1 # l1)" 
              using canonicalIs_remove_snd pre2 by blast
            from c1 c2 c3 semIs_head
            show "fst a2 \<notin> semIs (a1 # a # l1)"
              by (simp add: semIs_head)
          qed
          from this
          show "semIs (a1 # l1) \<noteq> semIs (a2 # l2)" 
            using a2l2nempty by blast
        qed
      qed
      have case2: " fst a1 = fst a2 \<Longrightarrow> snd a1 \<noteq> snd a2 \<Longrightarrow> 
                   semIs (a1 # l1) \<noteq> semIs (a2 # l2)"
      proof -
        assume pp1: "fst a1 = fst a2"
           and pp2: "snd a1 \<noteq> snd a2"
        show ?thesis 
        proof (cases "snd a1 < snd a2")
          case True note caset1 = True
          then show ?thesis 
          proof (cases "l1 = []")
            case True
            from this pp1 pp2 caset1
            show ?thesis 
              apply simp
              using semIs_def 
            proof -
              assume a1: "fst a1 = fst a2"
              assume "snd a1 < snd a2"
              then have "intersectI a1 a1 = intersectI a1 a2"
                using a1 by (simp add: intersectI_def)
              then show "semIs [a1] \<noteq> semIs (a2 # l2)"
                by (metis (no_types) Diff_Diff_Int Diff_eq_empty_iff False Int_commute Un_Diff_Int Un_upper1 empIs.simps(1) empIs_correct inter_correct semIs_head)
            qed
          next
            case False
            from this obtain a1' l1' where a'_def: "l1 = a1' # l1'" 
              by (metis hd_Cons_tl)
            show ?thesis 
            proof (cases "fst a1' \<le> snd a2")
              case True 
              from this p2 a'_def
              obtain e where e_def: "snd a1 < e \<and> e < fst a1'" 
                using canonicalIs.simps(3) by blast
              have c1: "e \<in> semI a2" 
                by (metis (mono_tags, lifting) CollectI True 
                   \<open>fst a1 = fst a2\<close> a'_def canonicalIs.simps(3) 
                   dual_order.trans e_def less_imp_le p2 semI_def)
              from this semIs_head
              have c2:  "e \<in> semIs (a2 # l2)" 
                by blast
              have c3: "e \<notin> semI a1" 
                by (metis CollectD e_def leD semI_def) 
              from p2
              have "canonicalIs (a1' # l1')" 
                using a'_def canonicalIs_sub by blast
              from this e_def
              have  c4: "e \<notin> semIs (a1' # l1')"
                apply (induction l1')
                 apply (metis CollectD boolean_algebra_cancel.sup0 empIs.simps(1) 
                        empIs_correct leD semI_def semIs_head)
              proof-
                fix a l1'
                assume ind_hyp2: "canonicalIs (a1' # l1') \<Longrightarrow>
                                snd a1 < e \<and> e < fst a1' \<Longrightarrow> e \<notin> semIs (a1' # l1')"
                   and pre1: "canonicalIs (a1' # a # l1')"
                   and pre2: "snd a1 < e \<and> e < fst a1'"
                from ind_hyp2 pre1 pre2
                have c1: "e \<notin> semIs (a1' # l1')"  
                  using canonicalIs_remove_snd by blast
                from pre1 pre2
                have c2: "e \<notin> semI a" 
                  by (metis (no_types, lifting) CollectD canonicalIs.simps(3) 
                        dual_order.strict_trans leD less_le_trans semI_def)
                from c1 c2 semIs_head
                show "e \<notin> semIs (a1' # a # l1')"
                  by (simp add: semIs_head)
              qed
              from this
              have "e \<notin> semIs (a1 # l1)" 
                by (simp add: a'_def c3 semIs_head)
              from this
              show ?thesis 
                using c2 by blast
            next
              case False
              from this have sa2fa1: "snd a2 < fst a1'" by simp
              from this caset1
              obtain e where e_def: "snd a1 < e \<and> e \<le> snd a2" 
                by blast 
              from this have ea1a2: "e \<notin> semI a1 \<and> e \<in> semI a2" 
                by (metis (mono_tags, lifting) \<open>fst a1 = fst a2\<close> a'_def   
                          canonicalIs.simps(3)
                         leD less_imp_le mem_Collect_eq order.trans p2 semI_def)
              from this semIs_head
              have c1: "e \<in> semIs (a2 # l2)" 
                by blast
              show ?thesis 
              proof (cases "l1 = []")
                case True
                then show ?thesis 
                  using a'_def by blast
              next
                case False
                from this obtain ah l1' where a1l1'_def: "l1 = ah # l1'" 
                  using a'_def by blast
                from p2 have "canonicalIs (ah # l1')" 
                  using \<open>l1 = ah # l1'\<close> canonicalIs_sub by blast
                from e_def this sa2fa1
                have c3: "e \<notin> semIs (ah # l1')"
                  apply (induction l1')
                   apply (metis (no_types, lifting) CollectD a'_def a1l1'_def 
                            boolean_algebra_cancel.sup0 empIs.simps(1) 
                            empIs_correct leD le_less_trans list.inject semI_def semIs_head)
                proof -
                  fix a l1'
                  assume ind_hyp: "(snd a1 < e \<and> e \<le> snd a2 \<Longrightarrow>
                                    canonicalIs (ah # l1') \<Longrightarrow>
                                    snd a2 < fst a1' \<Longrightarrow> 
                                    e \<notin> semIs (ah # l1'))"
                     and pre1: "snd a1 < e \<and> e \<le> snd a2"
                     and pre2: "canonicalIs (ah # a # l1')"
                     and pre3: "snd a2 < fst a1'"
                  from pre2 have pre2': "canonicalIs (ah # l1')" 
                    using canonicalIs_remove_snd by blast
                  from ind_hyp[OF pre1 pre2' pre3] 
                  have c1: "e \<notin> semIs (ah # l1')"  by auto
                  have c2: "e \<notin> semI a" 
                    by (metis CollectD a'_def a1l1'_def canonicalIs.simps(3) 
                              dual_order.strict_trans2 less_le_not_le list.inject 
                              pre1 pre2 sa2fa1 semI_def)
                  from c1 c2 semIs_head
                  show "e \<notin> semIs (ah # a # l1')" by blast
                qed
                from this
                show ?thesis 
                  using a1l1'_def a1l1nempty c1 ea1a2 by blast
              qed
            qed
          qed
        next
          case False 
          have pp3: "snd a2 < snd a1"
            using False \<open>snd a1 \<noteq> snd a2\<close> by auto
              note caset1 = this
          then show ?thesis 
          proof (cases "l2 = []")
            case True
            from pp1 pp3 
            obtain e where 
            e_def : "(snd a2 < e \<and> e \<le> snd a1)"
              by blast
  
            have  "fst a1 \<le> snd a1 \<and> fst a2 \<le> snd a2"
              using True p2 pp1 pp3 by auto
            from this semI_def[of a1] semI_def[of a2] e_def pp1
            have "e \<in> semI a1 \<and> e \<notin> semI a2"
              by force
            from this True semIs_head
            show ?thesis 
              apply simp
              using a1l1nempty a2l2nempty empIs_correct by fastforce
          next
            case False
            from this obtain a2' l2' where a'_def: "l2 = a2' # l2'" 
              by (metis hd_Cons_tl)
            show ?thesis 
            proof (cases "fst a2' \<le> snd a1")
              case True 
              from this p2 a'_def
              obtain e where e_def: "snd a2 < e \<and> e < fst a2'" 
                using canonicalIs.simps(3) by blast
              have c1: "e \<in> semI a1" 
                by (metis (mono_tags, lifting) CollectI True 
                   \<open>fst a1 = fst a2\<close> a'_def canonicalIs.simps(3) 
                   dual_order.trans e_def less_imp_le p2 semI_def)
              from this semIs_head
              have c2:  "e \<in> semIs (a1 # l1)" 
                by blast
              have c3: "e \<notin> semI a2" 
                by (metis CollectD e_def leD semI_def) 
              from p2
              have "canonicalIs (a2' # l2')" 
                using a'_def canonicalIs_sub by blast
              from this e_def
              have  c4: "e \<notin> semIs (a2' # l2')"
                apply (induction l2')
                 apply (metis CollectD boolean_algebra_cancel.sup0 empIs.simps(1) 
                        empIs_correct leD semI_def semIs_head)
              proof-
                fix a l2'
                assume ind_hyp2: "canonicalIs (a2' # l2') \<Longrightarrow>
                        snd a2 < e \<and> e < fst a2' \<Longrightarrow> e \<notin> semIs (a2' # l2')"
                   and pre1: "canonicalIs (a2' # a # l2')"
                   and pre2: "snd a2 < e \<and> e < fst a2'"
                from ind_hyp2 pre1 pre2
                have c1: "e \<notin> semIs (a2' # l2')"  
                  using canonicalIs_remove_snd by blast
                from pre1 pre2
                have c2: "e \<notin> semI a" 
                  by (metis (no_types, lifting) CollectD canonicalIs.simps(3) 
                        dual_order.strict_trans leD less_le_trans semI_def)
                from c1 c2 semIs_head
                show "e \<notin> semIs (a2' # a # l2')"
                  by (simp add: semIs_head)
              qed
              from this
              have "e \<notin> semIs (a2 # l2)" 
                by (simp add: a'_def c3 semIs_head)
              from this
              show ?thesis 
                using c2 by blast
            next
              case False
              from this have sa2fa1: "snd a1 < fst a2'" by simp
              from this caset1
              obtain e where e_def: "snd a2 < e \<and> e \<le> snd a1" 
                by blast 
              from this have ea1a2: "e \<notin> semI a2 \<and> e \<in> semI a1" 
                by (metis (mono_tags, lifting) \<open>fst a1 = fst a2\<close> a'_def   
                          canonicalIs.simps(3)
                         leD less_imp_le mem_Collect_eq order.trans p2 semI_def)
              from this semIs_head
              have c1: "e \<in> semIs (a1 # l1)" 
                by blast
              show ?thesis 
              proof (cases "l2 = []")
                case True
                then show ?thesis 
                  using a'_def by blast
              next
                case False
                from this obtain ah l2' where a1l1'_def: "l2 = ah # l2'" 
                  using a'_def by blast
                from p2 have "canonicalIs (ah # l2')" 
                  using \<open>l2 = ah # l2'\<close> canonicalIs_sub by blast
                from e_def this sa2fa1
                have c3: "e \<notin> semIs (ah # l2')"
                  apply (induction l2')
                   apply (metis (no_types, lifting) CollectD a'_def a1l1'_def 
                            boolean_algebra_cancel.sup0 empIs.simps(1) 
                            empIs_correct leD le_less_trans list.inject semI_def semIs_head)
                proof -
                  fix a l2'
                  assume ind_hyp: "(snd a2 < e \<and> e \<le> snd a1 \<Longrightarrow>
                         canonicalIs (ah # l2') \<Longrightarrow> snd a1 < fst a2' 
                         \<Longrightarrow> e \<notin> semIs (ah # l2'))"
                     and pre1: "snd a2 < e \<and> e \<le> snd a1"
                     and pre2: "canonicalIs (ah # a # l2')"
                     and pre3: "snd a1 < fst a2'"
                  from pre2 have pre2': "canonicalIs (ah # l2')" 
                    using canonicalIs_remove_snd by blast
                  from ind_hyp[OF pre1 pre2' pre3] 
                  have c1: "e \<notin> semIs (ah # l2')"  by auto
                  have c2: "e \<notin> semI a" 
                    by (metis CollectD a'_def a1l1'_def canonicalIs.simps(3) 
                              dual_order.strict_trans2 less_le_not_le list.inject 
                              pre1 pre2 sa2fa1 semI_def)
                  from c1 c2 semIs_head
                  show "e \<notin> semIs (ah # a # l2')" by blast
                qed
                from this
                show ?thesis 
                  using a1l1'_def a2l2nempty c1 ea1a2 by blast
              qed
            qed
          qed
        qed
      qed
      from case1 case2
      have "semIs (a1 # l1) \<noteq> semIs (a2 # l2)" 
        using neqor by blast
      from this p2
      show ?thesis
          by auto
      qed
    }
   qed
  qed        


lemma inj_semIs: "\<And> l1 l2. canonicalIs l1 \<and> canonicalIs l2 \<longrightarrow> 
                           (semIs l1 = semIs l2 
                       \<longleftrightarrow> l1 = l2)"
  using inj_semIs_aux by fastforce

fun emptyIs :: "('a ::linorder \<times> 'a) list \<Rightarrow> bool" where
  "emptyIs l = (l = [])"

lemma emptyIs_correct: "canonicalIs l \<longrightarrow> (emptyIs l \<longleftrightarrow> (semIs l = {}))"
  by (metis canonicalIs.simps(1) empIs.simps(1) 
          empIs_correct emptyIs.simps inj_semIs)

fun nemptyIs :: "('a ::linorder \<times> 'a) list \<Rightarrow> bool" where
  "nemptyIs l = (l \<noteq> [])"

lemma nemptyIs_correct: "canonicalIs l \<longrightarrow> (nemptyIs l \<longleftrightarrow> (semIs l \<noteq> {}))"
  using emptyIs_correct by auto

fun elemIs :: "'a::linorder \<Rightarrow> ('a ::linorder \<times> 'a) list \<Rightarrow> bool" where
    "elemIs a [] = False" |
    "elemIs a (i # l) = (if (fst i \<le> a \<and> a \<le> snd i) then True else elemIs a l)"


lemma elemIs_correct: "elemIs a l \<longleftrightarrow> (a \<in> semIs l)"
  apply (induction l)
  apply (simp add: semIs_def)
  by (metis (mono_tags, lifting) Un_iff elemIs.simps(2)   
            mem_Collect_eq semI_def semIs_head)

lemma intervals_imp_instance : 
 fixes f1 :: "'a ::linorder \<Rightarrow> 'a" 
 fixes f2 :: "'a ::linorder \<Rightarrow> 'a"
 assumes f1_cons: "\<forall> a. a < f1 a \<and> (\<forall> b. a < b \<longrightarrow> f1 a \<le> b)"
     and  f2_cons: "\<forall> a. a > f2 a \<and> (\<forall> b. a > b \<longrightarrow> f2 a \<ge> b)"
   shows "intervals semIs emptyIs nemptyIs intersectIs (diffIs f1 f2) elemIs canonicalIs"
  apply (simp add: intervals_def)
  apply (rule conjI)
  using semIs_def 
  apply auto[1]
  apply (rule conjI)
  using emptyIs.simps emptyIs_correct apply blast
  apply (rule conjI)
  using intersectIs_correct
  apply (simp add: intersectIs_correct)
  apply (rule conjI)
  using diffIs_correct[OF f1_cons f2_cons]
  apply blast
  using elemIs_correct
  by auto 

lemma interval_bool_algebra:
 "bool_algebra semIs emptyIs nemptyIs intersectIs diffIs elemIs canonicalIs"
  apply (simp add: bool_algebra_def)
  apply (rule conjI)
  using inj_semIs apply blast
  apply (rule conjI)
  using nemptyIs.simps nemptyIs_correct apply blast
  apply (rule conjI)
  using intersectIs_correct apply blast
  apply (rule conjI)
  apply (simp add: diffIs_correct)
  apply (simp add: elemIs_correct)
  done

end



