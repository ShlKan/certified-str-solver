
theory NFA_Split_Impl

imports Main "Collections.Collections" LTSSpec 
        LTSGA NFA_interval_Spec LTS_Impl "../DFA"
        RBT_LTSImpl 
begin

locale nfa_split_tran_imp =
  s: StdSet s_ops (* Set operations on states *) +
  l: StdSet l_ops (* Set operations on labels *) +
  d_nfa: StdLTS d_nfa_ops elemIs (* An LTS *) 
  for s_ops::"('q::{NFA_states},'q_set,_) set_ops_scheme"
  and l_ops::"(('a::linorder \<times> 'a) list, 'a_set,_) set_ops_scheme"
  and d_nfa_ops::"('q,('a \<times> 'a) list,'a,'d_nfa,_) lts_ops_scheme"

begin 

definition split_sing_impl :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> 'a_set \<Rightarrow> 'a_set nres"
  where 
  "split_sing_impl f1 f2 \<alpha>' S = 
        FOREACH {a. a \<in> l.\<alpha> S}
                  (\<lambda> \<alpha>1 tS. if (nemptyIs (intersectIs \<alpha>1 \<alpha>'))
                    then (if \<alpha>1 = (intersectIs \<alpha>1 \<alpha>') 
                                    then RETURN (l.ins \<alpha>1 tS)
                          else RETURN (l.ins (intersectIs \<alpha>1 \<alpha>') 
                                      (l.ins (diffIs f1 f2 \<alpha>1 (intersectIs \<alpha>1 \<alpha>')) tS)))
                    else 
                        RETURN (l.ins \<alpha>1 tS)
                  ) (l.empty ())"

schematic_goal split_sing_impl_gcode:
  fixes D_it1 :: "'a_set \<Rightarrow> (('a \<times> 'a) list, 'a_set) set_iterator"
  assumes D_it1_OK[rule_format, refine_transfer]: 
          "set_iterator (D_it1 S) {v. v \<in> l.\<alpha> S}"
  shows "RETURN ?code \<le> split_sing_impl f1 f2 \<alpha>' S"
  unfolding split_sing_impl_def
  by (rule refine_transfer | assumption | erule conjE )+


definition split_sing_code where
   "split_sing_code D_it f1 f2 \<alpha>' S = 
    (D_it S (\<lambda>_. True)
    (\<lambda>x \<sigma>. if nemptyIs (intersectIs x \<alpha>')
           then if x = intersectIs x \<alpha>' then l.ins x \<sigma>
                else l.ins (intersectIs x \<alpha>')
                      (l.ins (diffIs f1 f2 x (intersectIs x \<alpha>')) \<sigma>)
           else l.ins x \<sigma>)
    (l.empty ()))"

schematic_goal split_sing_impl_code: 
    "split_sing_code D_it f1 f2 \<alpha>' S = ?code"
  unfolding split_sing_code_def
  by (rule refl)+

definition split_rel where "split_rel = {(i, a). a = 
                                (semIs ` (l.\<alpha> i)) \<and> l.invar i \<and> card a = card (l.\<alpha> i) \<and>
                                (\<forall> x \<in> (l.\<alpha> i). canonicalIs x) \<and> l.invar i}"
abbreviation "sr \<equiv> split_rel"
lemmas sr_def[refine_rel_defs] = split_rel_def


lemma split_sing_impl_correct: 
  fixes f1 f2 a S a' S'
  assumes S'_OK1: "\<forall> i \<in> l.\<alpha> S. canonicalIs i"
      and S'_OK2: "S' = semIs ` {a. a \<in> l.\<alpha> S} \<and> card S' = card (l.\<alpha> S)"
      and a_OK: "canonicalIs a \<and> a' = semIs a"
      and f1_cons: "\<forall> a. a < f1 a \<and> (\<forall> b. a < b \<longrightarrow> f1 a \<le> b)"
     and  f2_cons: "\<forall> a. a > f2 a \<and> (\<forall> b. a > b \<longrightarrow> f2 a \<ge> b)"
  shows "(split_sing_impl f1 f2 a S) \<le>\<Down> sr (split_sing a' S')"
  unfolding split_sing_def split_sing_impl_def 
  apply (refine_rcg)
  apply (subgoal_tac "inj_on semIs {a. a \<in> l.\<alpha> S}")
  apply assumption
  using S'_OK1 inj_semIs
  apply (metis (no_types, lifting) inj_onI mem_Collect_eq)
  using S'_OK2 apply force
  unfolding sr_def 
  using l.correct(1,2)
  apply force
  using a_OK 
  apply (metis S'_OK1 intersectIs_correct mem_Collect_eq nemptyIs_correct subsetD)
  using a_OK
  apply (metis (no_types, lifting) S'_OK1 inj_semIs intersectIs_correct mem_Collect_eq subsetD)
proof -
  {
    fix x it \<sigma> x' it' \<sigma>'
    assume x'x: "x' = semIs x"
       and x_it: "x \<in> it"
       and x'_it: "x' \<in> it'"
       and itit': "it' = semIs ` it"
       and it_sub: "it \<subseteq> {a. a \<in> l.\<alpha> S}"
       and it'_sub: "it' \<subseteq> S'"
       and \<sigma>\<sigma>': "(\<sigma>, \<sigma>')
       \<in> {(i, a).
           a = semIs ` l.\<alpha> i \<and>  l.invar i \<and>
           card a = card (l.\<alpha> i) \<and> Ball (l.\<alpha> i) canonicalIs \<and> l.invar i}"
    from \<sigma>\<sigma>' x'x
    show "(l.ins x \<sigma>, \<sigma>' \<union> {x'})
           \<in> {(i, a).
           a = semIs ` l.\<alpha> i \<and>  l.invar i \<and>
           card a = card (l.\<alpha> i) \<and> Ball (l.\<alpha> i) canonicalIs \<and> l.invar i}"
      apply simp
      apply (rule conjI)
      apply (simp add: l.ins_correct(1))
      apply (rule conjI)
      defer
      using S'_OK1 it_sub l.ins_correct(1) l.ins_correct(2) x_it apply auto[1]  
    proof -
      { 
        assume p1: "\<sigma>' = semIs ` l.\<alpha> \<sigma>" 
           and p2: "card (semIs ` l.\<alpha> \<sigma>) = card (l.\<alpha> \<sigma>)"
           and p3: "(\<forall>x\<in>l.\<alpha> \<sigma>. canonicalIs x)"
        have con1:  "canonicalIs x" 
          using S'_OK1 it_sub x_it by blast
        from p1 p2 p3
        have con2: "\<forall> y \<in> l.\<alpha> \<sigma>. canonicalIs y" by auto
        show "card (insert (semIs x) (semIs ` l.\<alpha> \<sigma>)) = card (insert x (l.\<alpha> \<sigma>))"
        proof (cases "\<exists> e \<in> l.\<alpha> \<sigma>. semIs x = semIs e")
          case True
          from this obtain e 
            where e_def: "e \<in> l.\<alpha> \<sigma> \<and> semIs x = semIs e" by auto
          from this inj_semIs[of x e]
          have "x = e"  
            using con1 con2 by blast
          from e_def
          show ?thesis 
            using \<open>x = e\<close> insert_absorb   
                 l.ins_correct(1) p1
            by (simp add: insert_absorb p2)
          next
            case False
            from this
            have c1: "\<forall> e \<in> l.\<alpha> \<sigma>. semIs x \<noteq> semIs e" by auto
            from this have c3: "\<forall> e \<in> l.\<alpha> \<sigma>. x \<noteq> e" 
              by blast
            from c1 have c2: "\<forall> a \<in> (semIs ` l.\<alpha> \<sigma>). a \<noteq> (semIs x) " by auto
            from p1 inj_semIs
            have c4: "\<forall> a b. {a, b} \<subseteq> (l.\<alpha> \<sigma>) \<and> a \<noteq> b \<longrightarrow> semIs a \<noteq> (semIs b)"
              by (simp add: inj_semIs p3) 
            from this have c5: "card (semIs ` l.\<alpha> \<sigma>) = card (l.\<alpha> \<sigma>)"
              using p2 by blast
            have "\<forall> e \<in> l.\<alpha> \<sigma>. x \<noteq> e" 
              using c3 by linarith
            from this l.correct(6)[of \<sigma> x] p1 \<sigma>\<sigma>'
            have c6: "card (l.\<alpha> (l.ins x \<sigma>)) = card (l.\<alpha> \<sigma>) + 1" 
              by force
            from c2 c3 p1 c5 \<sigma>\<sigma>'
            have "card (insert (semIs x) (semIs ` l.\<alpha> \<sigma>)) = card (l.\<alpha> \<sigma>) + 1"
              by fastforce
            from this c6 l.correct(6)[of \<sigma> x]  \<sigma>\<sigma>'
            show ?thesis 
              by fastforce
          qed
        }
        from \<sigma>\<sigma>' l.correct
        show "l.invar (l.ins x \<sigma>)"
          by fastforce
      qed
    }
    {
      fix x it \<sigma> x' it' \<sigma>'
      assume x'x: "x' = semIs x"
       and x_it: "x \<in> it"
       and x'_it: "x' \<in> it'"
       and itit': "it' = semIs ` it"
       and it_sub: "it \<subseteq> {a. a \<in> l.\<alpha> S}"
       and it'_sub: "it' \<subseteq> S'"
       and \<sigma>\<sigma>': "(\<sigma>, \<sigma>')
       \<in> {(i, a).
           a = semIs ` l.\<alpha> i \<and>
           l.invar i \<and> card a = card (l.\<alpha> i) \<and> Ball (l.\<alpha> i) canonicalIs \<and> l.invar i}"
      from \<sigma>\<sigma>'
      show "(l.ins (intersectIs x a) (l.ins (diffIs f1 f2 x (intersectIs x a)) \<sigma>),
             \<sigma>' \<union> {x' \<inter> a', x' - x' \<inter> a'})
              \<in> {(i, a).
               a = semIs ` l.\<alpha> i \<and> l.invar i \<and> 
            card a = card (l.\<alpha> i) \<and> Ball (l.\<alpha> i) canonicalIs \<and> l.invar i}"
        apply simp
        apply (rule conjI)
        using intersectIs_correct[of x a] 
              diffIs_correct[of f1 f2 x "(intersectIs x a)", OF f1_cons f2_cons]
              a_OK x'x
         apply (smt S'_OK1 image_insert it_sub l.ins_correct(1) 
                  l.ins_correct(2) mem_Collect_eq subsetD x_it)
        apply (rule conjI)
        defer
        using intersectIs_correct[of x a] 
              diffIs_correct[of f1 f2 x "(intersectIs x a)", OF f1_cons f2_cons]
              a_OK x'x
        using S'_OK1 it_sub l.ins_correct(1) l.ins_correct(2) x_it apply auto[1]
      proof -
        {
        assume p1: "\<sigma>' = semIs ` l.\<alpha> \<sigma>"
           and p2: "card (semIs ` l.\<alpha> \<sigma>) = card (l.\<alpha> \<sigma>)" 
           and p3: "(\<forall>x\<in>l.\<alpha> \<sigma>. canonicalIs x)"
           and p4: "l.invar \<sigma>"

        have c1: "card (semIs ` l.\<alpha> \<sigma>) = card (l.\<alpha> \<sigma>)" 
          using p1 p2 by blast

        have imp1: "\<And> e1 e2 \<sigma> \<sigma>'. l.invar \<sigma>  \<Longrightarrow>
                             (\<forall> x \<in> l.\<alpha> \<sigma>. canonicalIs x) \<Longrightarrow> 
                             canonicalIs e2 \<and> e1 = semIs e2 \<Longrightarrow>
                             card \<sigma>' = card (l.\<alpha> \<sigma>) \<and> semIs ` (l.\<alpha> \<sigma>) = \<sigma>' \<Longrightarrow>
                             card ((insert e1 \<sigma>')) =
                             card (l.\<alpha> (l.ins e2 \<sigma>)) \<and> 
                             (insert e1 \<sigma>') = semIs ` (l.\<alpha> (l.ins e2 \<sigma>))"
        proof -
          fix e1 e2 \<sigma> \<sigma>'
          show "l.invar \<sigma> \<Longrightarrow>
       \<forall>x\<in>l.\<alpha> \<sigma>. canonicalIs x \<Longrightarrow>
       canonicalIs e2 \<and> e1 = semIs e2 \<Longrightarrow>
       card \<sigma>' = card (l.\<alpha> \<sigma>) \<and> semIs ` l.\<alpha> \<sigma> = \<sigma>' \<Longrightarrow>
       card (insert e1 \<sigma>') = card (l.\<alpha> (l.ins e2 \<sigma>)) \<and>
       insert e1 \<sigma>' = semIs ` l.\<alpha> (l.ins e2 \<sigma>)"
          proof -
          assume p1: "l.invar \<sigma>"
             and p2: "\<forall> x \<in> l.\<alpha> \<sigma>. canonicalIs x"
             and p3: "canonicalIs e2 \<and> e1 = semIs e2"
             and p4: "card \<sigma>' = card (l.\<alpha> \<sigma>) \<and> semIs ` (l.\<alpha> \<sigma>) = \<sigma>'"
          show "card ((insert e1 \<sigma>')) =
                             card (l.\<alpha> (l.ins e2 \<sigma>)) \<and> 
                             (insert e1 \<sigma>') = semIs ` (l.\<alpha> (l.ins e2 \<sigma>))"
          proof (cases "\<exists> x \<in> l.\<alpha> \<sigma>. e2 = x")
            case True
            from this p3 p1 l.correct(6)[of \<sigma> e2]
            have "l.\<alpha> (l.ins e2 \<sigma>) = l.\<alpha> \<sigma>" by auto
            then show ?thesis 
              using True p3 p4 by auto
          next
            case False        
            from this 
            have c1: "\<forall> x \<in> l.\<alpha> \<sigma>. e2 \<noteq> x" by auto
            from this l.correct(6)[of \<sigma> e2] p1
            have c2: "card (l.\<alpha> (l.ins e2 \<sigma>)) = 1 + card (l.\<alpha> \<sigma>)" 
              apply simp 
              by force
            from c1 p4 p3 p2
            have "\<forall> x \<in> semIs ` (l.\<alpha> \<sigma>). semIs e2 \<noteq> x" 
              by (metis (mono_tags, lifting) image_iff inj_semIs)
            from this p3 p4
            have c6: "e1 \<notin> (semIs ` l.\<alpha> \<sigma>)" by auto
            from this p4
            have "card (semIs ` l.\<alpha> \<sigma>) = card (l.\<alpha> \<sigma>)"
              by simp
            from this c6 p4 p3 p2 p1
            have c3: "card (insert e1 (semIs ` l.\<alpha> \<sigma>)) = card (l.\<alpha> \<sigma>) + 1"
              by fastforce
            from this p4
            have c3: "card (insert e1 \<sigma>') = card \<sigma>' + 1"
              by simp
            from this c2 p4
            show ?thesis 
              apply (rule_tac conjI)
              apply force
              by (simp add: l.ins_correct(1) p1 p3)
          qed
        qed
      qed
      from x_it 
      have "canonicalIs x"
        using S'_OK1 it_sub by blast
      from p1 this a_OK intersectIs_correct 
           diffIs_correct[of f1 f2 x a, OF f1_cons f2_cons]
      have "canonicalIs (diffIs f1 f2 x (intersectIs x a)) \<and>
            x' - x' \<inter> a' = semIs (diffIs f1 f2 x (intersectIs x a))"
        by (simp add: intersectIs_correct
                \<open>\<lbrakk>canonicalIs x; canonicalIs (intersectIs x a)\<rbrakk> \<Longrightarrow> 
                  semIs (diffIs f1 f2 x (intersectIs x a)) =
                   semIs x - semIs (intersectIs x a) \<and> 
                    canonicalIs (diffIs f1 f2 x (intersectIs x a))\<close> x'x)

      from imp1[of \<sigma> "(diffIs f1 f2 x (intersectIs x a))" 
                     "(x' - x' \<inter> a')" "(semIs ` l.\<alpha> \<sigma>)"]
           p1 this p2 p3 p4
      have "card (insert (x' - x' \<inter> a') (semIs ` l.\<alpha> \<sigma>)) =
            card (l.\<alpha> (l.ins (diffIs f1 f2 x (intersectIs x a)) \<sigma>)) \<and>
            insert (x' - x' \<inter> a') (semIs ` l.\<alpha> \<sigma>) =
            semIs ` l.\<alpha> (l.ins (diffIs f1 f2 x (intersectIs x a)) \<sigma>)"
        by auto
      from this
      show "card
     (insert (semIs x \<inter> semIs a) (insert (semIs x - semIs x \<inter> semIs a) (semIs ` l.\<alpha> \<sigma>))) =
    card (insert (intersectIs x a) (insert (diffIs f1 f2 x (intersectIs x a)) (l.\<alpha> \<sigma>)))"
      proof -
        have "x' \<inter> a' = semIs (intersectIs x a)"
          by (simp add: \<open>canonicalIs x\<close> a_OK intersectIs_correct x'x)
        then show ?thesis
          by (metis \<open>canonicalIs (diffIs f1 f2 x (intersectIs x a)) 
                    \<and> x' - x' \<inter> a' = semIs (diffIs f1 f2 x (intersectIs x a))\<close> 
                    \<open>canonicalIs x\<close> \<open>card (insert (x' - x' \<inter> a') 
                    (semIs ` l.\<alpha> \<sigma>)) = card (l.\<alpha> (l.ins (diffIs f1 f2 x 
                    (intersectIs x a)) \<sigma>)) \<and> insert (x' - x' \<inter> a') (semIs ` l.\<alpha> \<sigma>) =
                     semIs ` l.\<alpha> (l.ins (diffIs f1 f2 x (intersectIs x a)) \<sigma>)\<close> 
                     a_OK imp1 insertE intersectIs_correct l.ins_correct(1) 
                     l.ins_correct(2) p3 p4 x'x)
      qed
    }
    {
      assume p1: "\<sigma>' = semIs ` l.\<alpha> \<sigma> \<and>
            l.invar \<sigma> \<and> card \<sigma>' = card (l.\<alpha> \<sigma>) \<and> (\<forall>x\<in>l.\<alpha> \<sigma>. canonicalIs x) \<and> l.invar \<sigma>"
      from this
      show "l.invar (l.ins (intersectIs x a) 
            (l.ins (diffIs f1 f2 x (intersectIs x a)) \<sigma>))"
        by (simp add: l.ins_correct(2))
    }
    qed
  }
  {
    fix x it \<sigma> x' it' \<sigma>'
      assume x'x: "x' = semIs x"
       and x_it: "x \<in> it"
       and x'_it: "x' \<in> it'"
       and itit': "it' = semIs ` it"
       and it_sub: "it \<subseteq> {a. a \<in> l.\<alpha> S}"
       and it'_sub: "it' \<subseteq> S'"
       and \<sigma>\<sigma>': "(\<sigma>, \<sigma>')
       \<in> {(i, a).
           a = semIs ` l.\<alpha> i \<and> l.invar i \<and>
           card a = card (l.\<alpha> i) \<and> Ball (l.\<alpha> i) canonicalIs \<and> l.invar i}"
      from \<sigma>\<sigma>'
      show "(l.ins x \<sigma>, \<sigma>' \<union> {x'})
             \<in> {(i, a).
              a = semIs ` l.\<alpha> i \<and> l.invar i \<and>
              card a = card (l.\<alpha> i) \<and> Ball (l.\<alpha> i) canonicalIs \<and> l.invar i}"
        apply simp
        apply (rule_tac conjI)
        apply (simp add: l.ins_correct(1) x'x)
      proof -
        assume p1: "\<sigma>' = semIs ` l.\<alpha> \<sigma> \<and>
    l.invar \<sigma> \<and> card \<sigma>' = card (l.\<alpha> \<sigma>) \<and> (\<forall>x\<in>l.\<alpha> \<sigma>. canonicalIs x) \<and> l.invar \<sigma>"
        show "l.invar (l.ins x \<sigma>) \<and>
    card (insert x' (semIs ` l.\<alpha> \<sigma>)) = card (l.\<alpha> (l.ins x \<sigma>)) \<and>
    (\<forall>x\<in>l.\<alpha> (l.ins x \<sigma>). canonicalIs x) \<and> l.invar (l.ins x \<sigma>)"
        proof (cases "x \<notin> l.\<alpha> \<sigma>")
          case True
          from this p1 x'x
          have "x' \<notin> (semIs ` l.\<alpha> \<sigma>)" 
          proof -
            have f1: "\<forall>A f P. ((A::'a set) \<in> f ` P) = (\<exists>ps. (ps::('a \<times> 'a) list) \<in> P \<and> A = f ps)"
              by blast
            have "canonicalIs x"
              by (metis (no_types) S'_OK1 in_mono it_sub mem_Collect_eq x_it)
            then show ?thesis
              using f1 by (metis (no_types) True inj_semIs_aux p1 x'x)
          qed
          from this True p1
          have c1: "card (insert x' (semIs ` l.\<alpha> \<sigma>)) = 1 + card (semIs ` l.\<alpha> \<sigma>)"
            by auto
          from p1 True l.correct
          have "card (l.\<alpha> (l.ins x \<sigma>)) = 1 + card (l.\<alpha> \<sigma>)"  
            by fastforce
          from this c1 p1
          have "card (insert x' (semIs ` l.\<alpha> \<sigma>)) = card (l.\<alpha> (l.ins x \<sigma>))"
            by auto
          from this p1 x_it it_sub S'_OK1 l.correct(6)[of \<sigma> x]
          show ?thesis 
            by (simp add: in_mono l.ins_correct(2))
          next
          case False
            then show ?thesis 
              by (metis image_insert insert_absorb l.ins_correct(1) l.ins_correct(2) p1 x'x)
          qed
        qed
  }
qed

definition split_mult_impl :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow>'a_set \<Rightarrow> ('a \<times> 'a) list  \<Rightarrow> 'a_set nres"
  where 
  "split_mult_impl f1 f2 lbs \<alpha> = 
        (FOREACH  
             {a. a \<in> l.\<alpha> lbs}
             (\<lambda> \<alpha>' s_lbs. 
                split_sing_impl f1 f2 \<alpha>' s_lbs
              ) (l.ins \<alpha> (l.empty ()))
            )"

schematic_goal split_mult_impl_gcode:
  fixes D_it1 :: "'a_set \<Rightarrow> (('a \<times> 'a) list, 'a_set) set_iterator" and
        D_it2 :: "'a_set \<Rightarrow> (('a \<times> 'a) list, 'a_set) set_iterator"
  assumes D_it1_OK[rule_format, refine_transfer]: 
          "\<And> x. set_iterator (D_it1 x) {v. v \<in> l.\<alpha> x}" 
  shows "RETURN ?code \<le> split_mult_impl f1 f2 lbs \<alpha>"
  unfolding split_mult_impl_def split_sing_impl_def
  by (rule refine_transfer | assumption | erule conjE )+

lemma split_mult_impl_correct: 
  fixes f1 f2 a lbs a' lbs'
  assumes S'_OK1: "\<forall> i \<in> l.\<alpha> lbs. canonicalIs i"
      and S'_OK2: "lbs' = semIs ` {a. a \<in> l.\<alpha> lbs} \<and> card lbs' = card (l.\<alpha> lbs)"
      and a_OK: "canonicalIs a \<and> a' = semIs a"
      and f1_cons: "\<forall> a. a < f1 a \<and> (\<forall> b. a < b \<longrightarrow> f1 a \<le> b)"
     and  f2_cons: "\<forall> a. a > f2 a \<and> (\<forall> b. a > b \<longrightarrow> f2 a \<ge> b)"
  shows "(split_mult_impl f1 f2 lbs a) \<le>\<Down> sr (split_mult lbs' a')"
  unfolding split_mult_def split_mult_impl_def 
  apply (refine_rcg)
  apply (subgoal_tac "inj_on semIs {a. a \<in> l.\<alpha> lbs}")
  apply assumption
  using S'_OK1 inj_semIs
  apply (simp add: inj_semIs inj_on_def)
  using S'_OK2 apply simp
  apply (simp add: a_OK l.correct sr_def)
proof -
  fix x it \<sigma> x' it' \<sigma>'
  show "x' = semIs x \<Longrightarrow>
       x \<in> it \<Longrightarrow>
       x' \<in> it' \<Longrightarrow>
       it' = semIs ` it \<Longrightarrow>
       it \<subseteq> {a. a \<in> l.\<alpha> lbs} \<Longrightarrow>
       it' \<subseteq> lbs' \<Longrightarrow>
       (\<Union> \<sigma>' = a' \<and> finite \<sigma>') \<and>
       (\<forall>\<alpha>1 \<alpha>2. \<alpha>1 \<in> \<sigma>' \<and> \<alpha>2 \<in> \<sigma>' \<longrightarrow> \<alpha>1 = \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {}) \<and>
       (\<forall>\<alpha>3 \<alpha>4. \<alpha>3 \<in> \<sigma>' \<and> \<alpha>4 \<in> lbs' - it' \<longrightarrow> \<alpha>3 \<subseteq> \<alpha>4 \<or> \<alpha>3 \<inter> \<alpha>4 = {}) \<and>
       (\<forall>\<alpha>5\<in>\<sigma>'.
           \<exists>s\<subseteq>lbs' - it'.
              (\<alpha>5 \<subseteq> \<Inter> s \<inter> a' \<and> (\<forall>\<alpha>6\<in>lbs' - it' - (s \<union> {a'}). \<alpha>5 \<inter> \<alpha>6 = {})) \<and>
              (\<forall>\<alpha>7. \<alpha>7 \<subseteq> \<Inter> s \<inter> a' \<and> (\<forall>\<alpha>8\<in>lbs' - it' - (s \<union> {a'}). \<alpha>7 \<inter> \<alpha>8 = {}) \<longrightarrow>
                     \<alpha>7 \<subseteq> \<alpha>5)) \<Longrightarrow>
       (\<sigma>, \<sigma>') \<in> sr \<Longrightarrow> split_sing_impl f1 f2 x \<sigma> \<le> \<Down> sr (split_sing x' \<sigma>')"
  proof -
  assume xx': "x' = semIs x"
     and xit: "x \<in> it"
     and x'it': "x' \<in> it'"
     and itit': "it' = semIs ` it"
     and itin: "it \<subseteq> {a. a \<in> l.\<alpha> lbs}"
     and it'in: "it' \<subseteq> lbs'"
     and \<sigma>\<sigma>': "(\<sigma>, \<sigma>') \<in> sr"
  
  from \<sigma>\<sigma>' sr_def
  have pre1: "\<forall>i\<in>l.\<alpha> \<sigma>. canonicalIs i"
    by simp

  from \<sigma>\<sigma>' sr_def
  have pre2: "\<sigma>' = semIs ` {a. a \<in> l.\<alpha> \<sigma>} \<and> card \<sigma>' = card (l.\<alpha> \<sigma>)"
    apply simp
    by blast
  
  have pre3: "canonicalIs x \<and> x' = semIs x"
    using S'_OK1 itin xit xx' by blast

  from split_sing_impl_correct[of \<sigma> \<sigma>' x x' f1 f2, OF pre1 pre2 pre3 f1_cons f2_cons]
  show "split_sing_impl f1 f2 x \<sigma> \<le> \<Down> sr (split_sing x' \<sigma>')"
    by simp
qed
qed



definition split_tran_impl :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 
              'q \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> 'q \<Rightarrow> 'a_set \<Rightarrow> 'd_nfa nres" 
  where "split_tran_impl f1 f2 q \<alpha> q' lbs = do {
           s_lbs \<leftarrow> split_mult_impl f1 f2 lbs \<alpha>;
         FOREACH
             {a. a \<in> l.\<alpha> s_lbs}
             (\<lambda> \<alpha>' new_trans'. 
               RETURN (d_nfa.add q \<alpha>' q' new_trans'))
          (d_nfa.empty)
        }"

schematic_goal split_tran_impl_gcode:
  fixes D_it1 :: "'a_set \<Rightarrow> (('a \<times> 'a) list, 'a_set) set_iterator"
    and D_it2 :: "'a_set \<Rightarrow> (('a \<times> 'a) list, 'd_nfa) set_iterator"
  assumes D_it1_OK[rule_format, refine_transfer]: 
          "\<And> x. set_iterator (D_it1 x) {a. a \<in> l.\<alpha> x}" and
          D_it2_OK[rule_format, refine_transfer]: 
          "\<And> x. set_iterator (D_it2 x) {a. a \<in> l.\<alpha> x}"
  shows "RETURN ?code \<le> split_tran_impl f1 f2 q \<alpha> q' lbs"
  unfolding split_tran_impl_def split_mult_impl_def split_sing_impl_def
  by (rule refine_transfer | assumption | erule conjE )+

definition split_tran_code where
  "split_tran_code D_it1 D_it2 f1 f2 q \<alpha> q' lbs = 
   (let x = D_it1 lbs (\<lambda>_. True)
            (\<lambda>x \<sigma>. D_it1 \<sigma> (\<lambda>_. True)
                    (\<lambda>xa \<sigma>'.
                        if nemptyIs (intersectIs xa x)
                        then if xa = intersectIs xa x then l.ins xa \<sigma>'
                             else l.ins (intersectIs xa x)
                                   (l.ins (diffIs f1 f2 xa (intersectIs xa x)) \<sigma>')
                        else l.ins xa \<sigma>')
                    (l.empty ()))
            (l.ins \<alpha> (l.empty ()))
   in D_it2 x (\<lambda>_. True) (\<lambda>xa. d_nfa.add q xa q') d_nfa.empty)"
  
  

fun interval_to_set :: "'q \<times> ('a \<times> 'a) list \<times> 'q \<Rightarrow> 'q \<times> 'a set \<times> 'q"  where
    "interval_to_set (q, s, q') = (q, semIs s, q')"

definition split_tran_rel where "split_tran_rel = {(i, a). 
                                a =
                                (interval_to_set ` (d_nfa.\<alpha> i)) \<and> 
                                card a = card (d_nfa.\<alpha> i) \<and>
                                (\<forall> x \<in> (d_nfa.\<alpha> i). canonicalIs (fst (snd x))) \<and> 
                                d_nfa.invar i}"
abbreviation "str \<equiv> split_tran_rel"
lemmas str_def[refine_rel_defs] = split_tran_rel_def

lemma split_tran_impl_correct: 
  fixes f1 f2 a lbs a' lbs'
  assumes S'_OK1: "\<forall> i \<in> l.\<alpha> lbs. canonicalIs i"
      and S'_OK2: "lbs' = semIs ` {a. a \<in> l.\<alpha> lbs} \<and> card lbs' = card (l.\<alpha> lbs) \<and> finite lbs'"
      and a_OK: "canonicalIs a \<and> a' = semIs a"
      and f1_cons: "\<forall> a. a < f1 a \<and> (\<forall> b. a < b \<longrightarrow> f1 a \<le> b)"
     and  f2_cons: "\<forall> a. a > f2 a \<and> (\<forall> b. a > b \<longrightarrow> f2 a \<ge> b)"
   shows "(split_tran_impl f1 f2 q a q' lbs) \<le>\<Down> str (split_tran q a' q' lbs')"
  unfolding split_tran_impl_def split_tran_def
  apply (refine_rcg)
  apply (subgoal_tac "split_mult_impl f1 f2 lbs a \<le> \<Down> sr (split_mult lbs' a')")
  apply assumption
  using split_mult_impl_correct[OF S'_OK1 _ a_OK f1_cons f2_cons] S'_OK2
  apply force
  apply (subgoal_tac "inj_on ((\<lambda> _ _. semIs) s_lbs s_lbsa) {a. a \<in> l.\<alpha> s_lbs}")
  apply assumption
  unfolding sr_def
  apply simp
  apply (simp add: inj_onI inj_semIs_aux)
  apply simp
  unfolding str_def
  apply simp
  using d_nfa.correct
  apply simp
proof -
  fix s_lbs s_lbsa x it \<sigma> x' it' \<sigma>'
  show "(s_lbs, s_lbsa)
       \<in> {(i, a).
           a = semIs ` l.\<alpha> i \<and> l.invar i \<and>
           card a = card (l.\<alpha> i) \<and> Ball (l.\<alpha> i) canonicalIs \<and> l.invar i} \<Longrightarrow>
       x' = semIs x \<Longrightarrow>
       x \<in> it \<Longrightarrow>
       x' \<in> it' \<Longrightarrow>
       it' = semIs ` it \<Longrightarrow>
       it \<subseteq> {a. a \<in> l.\<alpha> s_lbs} \<Longrightarrow>
       it' \<subseteq> s_lbsa \<Longrightarrow>
       (\<forall>(q1, \<alpha>1', q1')\<in>\<sigma>'. q = q1 \<and> q' = q1') \<and>
       \<Union> {\<alpha>1. (q, \<alpha>1, q') \<in> \<sigma>'} = \<Union> (s_lbsa - it') \<and>
       {\<alpha>1. (q, \<alpha>1, q') \<in> \<sigma>'} = s_lbsa - it' \<and>
       (\<forall>(q, \<alpha>1, q')\<in>\<sigma>'.
           \<exists>s\<subseteq>lbs'.
              (\<alpha>1 \<subseteq> \<Inter> s \<and> (\<forall>\<alpha>2\<in>lbs' - s. \<alpha>1 \<inter> \<alpha>2 = {})) \<and>
              (\<forall>\<alpha>3. \<alpha>3 \<subseteq> \<Inter> s \<and> (\<forall>\<alpha>4\<in>lbs' - s. \<alpha>3 \<inter> \<alpha>4 = {}) \<longrightarrow> \<alpha>3 \<subseteq> \<alpha>1)) \<and>
       (\<forall>\<alpha>1 \<alpha>2. {\<alpha>1, \<alpha>2} \<subseteq> {\<alpha>1. (q, \<alpha>1, q') \<in> \<sigma>'} \<longrightarrow> \<alpha>1 = \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {}) \<and>
       (\<forall>\<alpha>1 \<alpha>2. \<alpha>1 \<in> {\<alpha>1. (q, \<alpha>1, q') \<in> \<sigma>'} \<and> \<alpha>2 \<in> lbs' \<longrightarrow> \<alpha>1 \<subseteq> \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {}) \<Longrightarrow>
       (\<sigma>, \<sigma>')
       \<in> {(i, a).
           a = interval_to_set ` d_nfa.\<alpha> i \<and>
           card a = card (d_nfa.\<alpha> i) \<and>
           (\<forall>x\<in>d_nfa.\<alpha> i. canonicalIs (fst (snd x))) \<and> d_nfa.invar i} \<Longrightarrow>
       (d_nfa.add q x q' \<sigma>, \<sigma>' \<union> {(q, x', q')})
       \<in> {(i, a).
           a = interval_to_set ` d_nfa.\<alpha> i \<and>
           card a = card (d_nfa.\<alpha> i) \<and>
           (\<forall>x\<in>d_nfa.\<alpha> i. canonicalIs (fst (snd x))) \<and> d_nfa.invar i}"
  proof -
  assume p1: "(s_lbs, s_lbsa)
       \<in> {(i, a).
           a = semIs ` l.\<alpha> i \<and> l.invar i \<and>
           card a = card (l.\<alpha> i) \<and> Ball (l.\<alpha> i) canonicalIs \<and> l.invar i}"
     and xx': "x' = semIs x"
     and xin: "x \<in> it"
     and xin': "x' \<in> it'"
     and itit': "it' = semIs ` it"
     and itin: "it \<subseteq> {a. a \<in> l.\<alpha> s_lbs} "
     and p2: "(\<forall>(q1, \<alpha>1', q1')\<in>\<sigma>'. q = q1 \<and> q' = q1') \<and>
    \<Union> {\<alpha>1. (q, \<alpha>1, q') \<in> \<sigma>'} = \<Union> (s_lbsa - it') \<and>
    {\<alpha>1. (q, \<alpha>1, q') \<in> \<sigma>'} = s_lbsa - it' \<and>
    (\<forall>(q, \<alpha>1, q')\<in>\<sigma>'.
        \<exists>s\<subseteq>lbs'.
           (\<alpha>1 \<subseteq> \<Inter> s \<and> (\<forall>\<alpha>2\<in>lbs' - s. \<alpha>1 \<inter> \<alpha>2 = {})) \<and>
           (\<forall>\<alpha>3. \<alpha>3 \<subseteq> \<Inter> s \<and> (\<forall>\<alpha>4\<in>lbs' - s. \<alpha>3 \<inter> \<alpha>4 = {}) \<longrightarrow> \<alpha>3 \<subseteq> \<alpha>1)) \<and>
    (\<forall>\<alpha>1 \<alpha>2. {\<alpha>1, \<alpha>2} \<subseteq> {\<alpha>1. (q, \<alpha>1, q') \<in> \<sigma>'} \<longrightarrow> \<alpha>1 = \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {}) \<and>
    (\<forall>\<alpha>1 \<alpha>2. \<alpha>1 \<in> {\<alpha>1. (q, \<alpha>1, q') \<in> \<sigma>'} \<and> \<alpha>2 \<in> lbs' \<longrightarrow> \<alpha>1 \<subseteq> \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {})"
     and p3: "(\<sigma>, \<sigma>')
    \<in> {(i, a).
        a = interval_to_set ` d_nfa.\<alpha> i \<and>
        card a = card (d_nfa.\<alpha> i) \<and>
        (\<forall>x\<in>d_nfa.\<alpha> i. canonicalIs (fst (snd x))) \<and> d_nfa.invar i}"

  from p3
  have invar\<sigma>: "d_nfa.invar \<sigma>"
    by auto
  from p2 
  have \<sigma>'qq': "\<forall> (q1, a, q2) \<in> \<sigma>'. q1 = q \<and> q2 = q'" by auto

  from p3 this
  have \<sigma>qq': "\<forall> (q1, a, q2) \<in> d_nfa.\<alpha> \<sigma>. q1 = q \<and> q2 = q'" by auto

  show "(d_nfa.add q x q' \<sigma>, \<sigma>' \<union> {(q, x', q')})
          \<in> {(i, a).
           a = interval_to_set ` d_nfa.\<alpha> i \<and>
           card a = card (d_nfa.\<alpha> i) \<and>
           (\<forall>x\<in>d_nfa.\<alpha> i. canonicalIs (fst (snd x))) \<and> d_nfa.invar i}"
  proof -
    from p3
    have \<sigma>\<sigma>'': "\<sigma>' = interval_to_set ` d_nfa.\<alpha> \<sigma>"
      by auto
   
    from d_nfa.correct(9)[OF invar\<sigma>, of q x q']
         d_nfa.correct(10)[OF invar\<sigma>, of q x q']
    have dnfaeq: "d_nfa.\<alpha> (d_nfa.add q x q' \<sigma>) = insert (q, x, q') (d_nfa.\<alpha> \<sigma>)"
      by auto

    from this \<sigma>\<sigma>'' xx'
    have c1: "\<sigma>' \<union> {(q, x', q')} = interval_to_set ` d_nfa.\<alpha> (d_nfa.add q x q' \<sigma>)"
      by simp

    from xin p1 itin
    have cnIx: "canonicalIs x"
      by force

    from p3 cnIx dnfaeq
    have c2: "\<forall> x \<in> d_nfa.\<alpha> (d_nfa.add q x q' \<sigma>). canonicalIs (fst (snd x))"
      by simp

    from d_nfa.correct(9)[OF invar\<sigma>, of q x q']
    have c3: "d_nfa.invar (d_nfa.add q x q' \<sigma>)"
      by simp

    from p3 
    have seteq: "\<sigma>' = interval_to_set ` (d_nfa.\<alpha> \<sigma>)"
      by auto
    from p3
    have cardeq: "card \<sigma>' = card (d_nfa.\<alpha> \<sigma>)" by auto

    from dnfaeq cardeq seteq
    have c4: "card (\<sigma>' \<union> {(q, x', q')}) = card (d_nfa.\<alpha> (d_nfa.add q x q' \<sigma>))"
      apply simp
    proof (cases "\<exists> a. (q, a, q') \<in> (d_nfa.\<alpha> \<sigma>) \<and> a = x")
      case True
      then show "card (insert (q, x', q') (interval_to_set ` d_nfa.\<alpha> \<sigma>)) =
                 card (insert (q, x, q') (d_nfa.\<alpha> \<sigma>))" 
        by (metis c1 cardeq dnfaeq insert_absorb 
                  insert_is_Un seteq sup.commute)
    next
      case False
      from this xx' cnIx c2 \<sigma>qq'
      have "\<forall> a. (q, a, q') \<in> interval_to_set ` d_nfa.\<alpha> \<sigma> \<longrightarrow> a \<noteq> x'"
        apply (rule_tac allI impI)+
      proof -
        fix a
        assume p1: "(q, a, q') \<in> interval_to_set ` d_nfa.\<alpha> \<sigma>"
        show "a \<noteq> x'"
        proof (rule ccontr)
          assume p2: "\<not> a \<noteq> x'"
          from this have "a = x'"
            by auto
          from p1 interval_to_set.simps
          obtain a' where a'_def: "(q, a', q') \<in> d_nfa.\<alpha> \<sigma> 
                                            \<and> semIs a' = a"
            by force
          from this have "semIs a' = x' \<and> canonicalIs a'" 
            using \<open>a = x'\<close> c2 dnfaeq by auto
          from this False a'_def
          show "False"
            using cnIx inj_semIs xx' by auto
        qed
      qed


      from this
      have notin: "(q, x', q') \<notin> (interval_to_set ` d_nfa.\<alpha> \<sigma>)"
        by auto

      from p3
      have cd0: "card (interval_to_set ` d_nfa.\<alpha> \<sigma>) = 
                 card (d_nfa.\<alpha> \<sigma>)"
        by auto

      have "card (d_nfa.\<alpha> \<sigma>) \<ge> 0"
        by blast
      from this 
      have finite\<sigma>: "finite (d_nfa.\<alpha> \<sigma>) \<and> finite (interval_to_set ` d_nfa.\<alpha> \<sigma>)"
        using invar\<sigma> by blast

      have plus1card: "\<And> a S. a \<notin> S \<and> finite S \<Longrightarrow> card (insert a S) = 1 + card S"
        by simp

      from finite\<sigma> notin cd0 plus1card
      have cd1: "card (insert (q, x', q') (interval_to_set ` d_nfa.\<alpha> \<sigma>)) = 
                1 + card (interval_to_set ` d_nfa.\<alpha> \<sigma>)"
        apply (rule_tac plus1card)
        by auto

      have cd2: "card (insert (q, x, q') (d_nfa.\<alpha> \<sigma>)) = 
                1 + card (d_nfa.\<alpha> \<sigma>)"
        apply (rule_tac plus1card)
        using False invar\<sigma> by blast

      from cd1 cd2
      show "card (insert (q, x', q') (interval_to_set ` d_nfa.\<alpha> \<sigma>)) =
                 card (insert (q, x, q') (d_nfa.\<alpha> \<sigma>))" 
        apply simp
        using cd0 by blast
    qed

    from c1 c2 c3 c4
    show "(d_nfa.add q x q' \<sigma>, \<sigma>' \<union> {(q, x', q')})
    \<in> {(i, a).
        a = interval_to_set ` d_nfa.\<alpha> i \<and>
        card a = card (d_nfa.\<alpha> i) \<and>
        (\<forall>x\<in>d_nfa.\<alpha> i. canonicalIs (fst (snd x))) \<and> d_nfa.invar i}"
      by simp
  qed
qed
qed

definition labels_impl_aux :: "'d_nfa \<Rightarrow> 'a_set nres" 
  where
  "labels_impl_aux T = do {
    (FOREACHi (\<lambda> S1 S2. l.invar S2 \<and> l.\<alpha> S2 = {a | q a q'. 
                             (q, a, q') \<in> {\<alpha>. \<alpha> \<in> d_nfa.\<alpha> T} - S1}) 
                             {\<alpha>. \<alpha> \<in> d_nfa.\<alpha> T} (\<lambda> (q, a, q') S. RETURN (l.ins a S)) (l.empty ()))
   }"

lemma labels_impl_aux_correct: 
  fixes T' T
  assumes T_OK1 : "card (d_nfa.\<alpha> T') = card T \<and> finite T \<and> d_nfa.invar T'"
      and T_OK2 : "\<forall> (q, a, q') \<in> (d_nfa.\<alpha> T'). canonicalIs a"
      and T_OK3 : "T = interval_to_set ` (d_nfa.\<alpha> T')"
  shows "(labels_impl_aux T') \<le>\<Down> sr (labels T)"
  unfolding labels_impl_aux_def labels_def sr_def
  apply (refine_rcg)
  apply (intro refine_vcg)
  using T_OK1
  apply auto[1]
  using l.correct
  apply force
proof -
  {
    fix x it \<sigma>
    show "x \<in> it \<Longrightarrow>
       it \<subseteq> {\<alpha>'. \<alpha>' \<in> d_nfa.\<alpha> T'} \<Longrightarrow>
       l.invar \<sigma> \<and>
       l.\<alpha> \<sigma> = {uu. \<exists>q a q'. uu = a \<and> (q, a, q') \<in> {\<alpha>'. \<alpha>' \<in> d_nfa.\<alpha> T'} - it} \<Longrightarrow>
       (case x of (q, a, q') \<Rightarrow> \<lambda>S. RETURN (l.ins a S)) \<sigma>
       \<le> SPEC (\<lambda>S2. l.invar S2 \<and> l.\<alpha> S2 =
                     {uu.
                      \<exists>q a q'. uu = a \<and> (q, a, q') \<in> {\<alpha>'. \<alpha>' \<in> d_nfa.\<alpha> T'} - (it - {x})})"
    proof -
      assume xin: "x \<in> it"
         and itin: "it \<subseteq> {\<alpha>'. \<alpha>' \<in> d_nfa.\<alpha> T'}"
         and l\<sigma>: "l.invar \<sigma> \<and> l.\<alpha> \<sigma> = {uu. \<exists>q a q'. uu = a \<and> 
                   (q, a, q') \<in> {\<alpha>'. \<alpha>' \<in> d_nfa.\<alpha> T'} - it}"
      from this
      obtain q a q' where qaq'_def: "x = (q, a, q')" 
        using interval_to_set.cases by blast
      
      from this l\<sigma> xin itin
      show "(case x of (q, a, q') \<Rightarrow> \<lambda>S. RETURN (l.ins a S)) \<sigma>
             \<le> SPEC (\<lambda>S2. l.invar S2 \<and> l.\<alpha> S2 =
                  {uu. \<exists>q a q'. uu = a \<and> (q, a, q') \<in> {\<alpha>'. \<alpha>' \<in> d_nfa.\<alpha> T'} - (it - {x})})"
        apply simp
      proof -
        from l\<sigma> xin itin
        have c1: "l.\<alpha> (l.ins a \<sigma>) = {a} \<union> (l.\<alpha> \<sigma>)"
          using l.ins_correct(1) by auto
        from xin itin qaq'_def
        have c2: "{uu.
         \<exists>qa q'a.
        (qa, uu, q'a) \<in> d_nfa.\<alpha> T' \<and> ((qa, uu, q'a) \<in> it \<longrightarrow> uu = a \<and> qa = q \<and> q'a = q')} = 
        {a} \<union> {uu. \<exists>q q'. (q, uu, q') \<in> d_nfa.\<alpha> T' \<and> (q, uu, q') \<notin> it}"
          by force
        show " l.invar (l.ins a \<sigma>) \<and>
    l.\<alpha> (l.ins a \<sigma>) =
    {uu.
     \<exists>qa q'a.
        (qa, uu, q'a) \<in> d_nfa.\<alpha> T' \<and> ((qa, uu, q'a) \<in> it \<longrightarrow> uu = a \<and> qa = q \<and> q'a = q')}"
          apply (rule conjI)
          using l\<sigma> l.correct apply force
          using c1 c2 l\<sigma> by force
      qed
    qed
  }
  {
    fix \<sigma>
    assume p1: "l.invar \<sigma> \<and>
         l.\<alpha> \<sigma> = {uu. \<exists>q a q'. uu = a \<and> (q, a, q') \<in> {\<alpha>'. \<alpha>' \<in> d_nfa.\<alpha> T'} - {}}"

    from p1
    have p1': "l.\<alpha> \<sigma> = {a | q a q'. (q, a, q') \<in> d_nfa.\<alpha> T'}"
      by force
 
    show "(\<sigma>, {uu. \<exists>q \<alpha> q'. uu = \<alpha> \<and> (q, \<alpha>, q') \<in> T})
            \<in> {(i, a).
             a = semIs ` l.\<alpha> i \<and>
             l.invar i \<and> card a = card (l.\<alpha> i) \<and> Ball (l.\<alpha> i) canonicalIs \<and> l.invar i}"
      apply simp
      apply (rule conjI)
      defer
      apply (rule conjI)
      using p1 T_OK3 T_OK1 T_OK2
      apply simp
      apply (rule conjI) 
      defer
      using p1 T_OK2
      apply force
    proof -
      {
        show "{uu. \<exists>q q'. (q, uu, q') \<in> T} = semIs ` l.\<alpha> \<sigma>"
        proof 
          {
            show "{uu. \<exists>q q'. (q, uu, q') \<in> T} \<subseteq> semIs ` l.\<alpha> \<sigma>"
            proof 
              fix x
              assume xin: "x \<in> {uu. \<exists>q q'. (q, uu, q') \<in> T}"
              from this obtain q q' where qq'_def: "(q, x, q') \<in> T" by auto
              from this T_OK3 interval_to_set.simps[of q _ q']
              obtain x' where x'_def: "(q, x', q') \<in> d_nfa.\<alpha> T' \<and> semIs x' = x"
                by auto
              from this T_OK1 p1
              show "x \<in> semIs ` l.\<alpha> \<sigma>"
                by force
            qed
          }
          {
            show "semIs ` l.\<alpha> \<sigma> \<subseteq> {uu. \<exists>q q'. (q, uu, q') \<in> T}"
            proof 
              fix x
              assume xin: "x \<in> semIs ` l.\<alpha> \<sigma>"
              from this p1'
              obtain q x' q' 
                where qqx_def: "(q, x', q') \<in> d_nfa.\<alpha> T' \<and> semIs x' = x"
                by auto
              from this T_OK3
              show "x \<in> {uu. \<exists>q q'. (q, uu, q') \<in> T}" 
                by (metis (mono_tags, lifting) Set.set_insert 
                          image_insert insertI1 interval_to_set.simps mem_Collect_eq)
            qed
          }
        qed
      }
      {
        from p1 T_OK1 T_OK2
        have canoa: "\<forall> a \<in> l.\<alpha> \<sigma>. canonicalIs a" by force
        from p1 T_OK1
        have "bij_betw semIs (l.\<alpha> \<sigma>) {uu. \<exists>q q'. (q, uu, q') \<in> T}"
          unfolding bij_betw_def
          apply (rule_tac conjI)
          using canoa inj_semIs
          apply (metis (no_types, lifting) inj_onI)
          using T_OK3
          using \<open>{uu. \<exists>q q'. (q, uu, q') \<in> T} = semIs ` l.\<alpha> \<sigma>\<close> by auto
        from this
        show "card {uu. \<exists>q q'. (q, uu, q') \<in> T} = card (l.\<alpha> \<sigma>)"
          using bij_betw_same_card by force
      }
qed
}
qed

definition labels_impl :: "'d_nfa \<Rightarrow> 'a_set nres" 
  where
  "labels_impl T = do {
    (FOREACH {\<alpha>. \<alpha> \<in> d_nfa.\<alpha> T} (\<lambda> (q, a, q') S. RETURN (l.ins a S)) (l.empty ()))
   }"

definition eq_rel where "eq_rel = {(i, a). a = i}"
abbreviation "er \<equiv> eq_rel"
lemmas er_def[refine_rel_defs] = eq_rel_def

lemma labeleq: "(labels_impl T) \<le> \<Down> er (labels_impl_aux T)"
  unfolding labels_impl_def labels_impl_aux_def
  apply (refine_vcg)
  apply (subgoal_tac "inj_on id {\<alpha>'. \<alpha>' \<in> d_nfa.\<alpha> T}")
  apply assumption
  apply force
  apply simp
  using eq_rel_def apply force
  unfolding eq_rel_def 
  by simp

  

definition split_trans_impl :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'd_nfa \<Rightarrow> 'd_nfa nres" 
 where
  "split_trans_impl f1 f2 TS = do {
    lbs \<leftarrow> labels_impl_aux TS; 
    (FOREACH
        {a. a \<in> d_nfa.\<alpha> TS} 
        (\<lambda> (q, \<alpha>, q') Trans. 
         do {
           Tran  \<leftarrow> (split_tran_impl f1 f2 q \<alpha> q' lbs);
           RETURN (d_nfa.union Trans Tran)
         })
         (d_nfa.empty)
      )
    }"


lemma inj_interval_to_set: 
      "\<And> S. (\<forall> (q, a, q') \<in> S. canonicalIs a) \<longrightarrow>  inj_on interval_to_set S"
proof 
  fix S
  show "\<forall>(q, a, q')\<in>S. canonicalIs a \<Longrightarrow> inj_on interval_to_set S"
  proof -
     assume p1: "\<forall>(q, a, q')\<in>S. canonicalIs a"
     show "inj_on interval_to_set S"
       unfolding inj_on_def
       apply (rule)
       apply (rule)
       apply (rule)
     proof -
       fix x y
       assume xin: "x \<in> S"
          and yin: "y \<in> S"
          and eq1: "interval_to_set x = interval_to_set y"

       from this obtain q1 q2 a a' q1' q2'
         where qa_def1: "x = (q1, a, q2)" and
               qa_def2: "y = (q1', a', q2')"
         by (meson interval_to_set.cases)

       from this eq1
       have "y = (q1, a', q2) \<and> semIs a = semIs a'"
         by force

       from this qa_def1 inj_semIs[of a a'] p1 xin yin 
       show "x = y"
         by force
     qed
   qed
 qed

lemma split_trans_impl_correct: 
  fixes f1 f2 a lbs a' lbs'
  assumes S'_OK1: "\<forall> i \<in> l.\<alpha> lbs. canonicalIs i"
      and S'_OK2: "lbs' = semIs ` {a. a \<in> l.\<alpha> lbs} \<and> card lbs' = card (l.\<alpha> lbs) \<and> finite lbs'"
      and a_OK: "canonicalIs a \<and> a' = semIs a"
      and f1_cons: "\<forall> a. a < f1 a \<and> (\<forall> b. a < b \<longrightarrow> f1 a \<le> b)"
      and  f2_cons: "\<forall> a. a > f2 a \<and> (\<forall> b. a > b \<longrightarrow> f2 a \<ge> b)"
      and T_OK1 : "card (d_nfa.\<alpha> T') = card T \<and> finite T \<and> d_nfa.invar T'"
      and T_OK2 : "\<forall> (q, a, q') \<in> (d_nfa.\<alpha> T'). canonicalIs a"
      and T_OK3 : "T = interval_to_set ` (d_nfa.\<alpha> T')"
   shows "(split_trans_impl f1 f2 T') \<le>\<Down> str (split_trans T)"
  unfolding split_trans_impl_def split_trans_def
  apply (refine_rcg)
  apply (subgoal_tac "labels_impl_aux T' \<le> \<Down> sr (labels T)")
  apply assumption
  using labels_impl_aux_correct[OF T_OK1 T_OK2 T_OK3]
  apply simp
  apply (subgoal_tac "inj_on ((\<lambda> _ _. interval_to_set) lbs lbsa) {a. a \<in> d_nfa.\<alpha> T'}")
  apply assumption
  using T_OK2 inj_interval_to_set
      apply force
  using T_OK3 apply force  
  using d_nfa.correct(1) str_def sr_def
  apply simp
  using d_nfa.correct(2) apply force  
  apply (subgoal_tac "split_tran_impl f1 f2 x1b x1c x2c lbs
       \<le> \<Down> str
           (split_tran x1 x1a x2a lbsa)")
    apply assumption
proof -
  {
    fix lbs lbsa x it \<sigma> x' it' \<sigma>' x1 x2 x1a x2a x1b x2b x1c x2c
    assume xx'_re: "x' = interval_to_set x"   
       and x2_def: "x2 = (x1a, x2a)"
       and x'_def: "x' = (x1, x2)"
       and x2b_def: "x2b = (x1c, x2c)"
       and x_def: "x = (x1b, x2b)"
       and lbs_cons: "(lbs, lbsa) \<in> sr"
       and xit: "x \<in> it"
       and itin: "it \<subseteq> {a. a \<in> d_nfa.\<alpha> T'}"
    from this have x_def': "x = (x1b, x1c, x2c)" by auto
    from x2_def x'_def have x'_def': "x' = (x1, x1a, x2a)" by auto
    from x_def' x'_def' xx'_re
    have eqxx': "x1b = x1 \<and> x2c = x2a \<and> semIs x1c = x1a"
      by force

    from lbs_cons sr_def
    have split_tran_pre1: "\<forall>i\<in>l.\<alpha> lbs. canonicalIs i"
      by simp

    from lbs_cons sr_def inj_semIs
    have split_tran_pre2: "lbsa = semIs ` {a. a \<in> l.\<alpha> lbs} \<and> 
                           card lbsa = card (l.\<alpha> lbs) \<and> finite lbsa"
      apply simp
      by blast

    from split_tran_pre1 eqxx' itin xit T_OK2
    have split_tran_pre3: "canonicalIs x1c \<and> x1a = semIs x1c"
      apply auto    
      using x_def' by force
  
    from split_tran_impl_correct[of lbs lbsa x1c x1a f1 f2 x1b x2c, 
          OF split_tran_pre1 split_tran_pre2 _ f1_cons f2_cons ] eqxx' split_tran_pre3
    show "split_tran_impl f1 f2 x1b x1c x2c lbs \<le> \<Down> str (split_tran x1 x1a x2a lbsa)"
      by force
  }
  {
    fix lbs lbsa x it \<sigma> x' it' \<sigma>' x1 x2 x1a x2a x1b x2b x1c x2c Tran Trana
    assume tran_cons: "(Tran, Trana) \<in> str"
       and lbs_cons: "(lbs, lbsa) \<in> sr"
       and \<sigma>_cons: "(\<sigma>, \<sigma>') \<in> str"
    show "(d_nfa.union \<sigma> Tran, \<sigma>' \<union> Trana) \<in> str"
      unfolding str_def
      apply simp
    proof - 
      from \<sigma>_cons
      have \<sigma>_eq: "\<sigma>' = interval_to_set ` (d_nfa.\<alpha> \<sigma>)"
        unfolding str_def
        by simp

      from tran_cons
      have Tran_eq: "Trana = interval_to_set ` d_nfa.\<alpha> Tran"
        unfolding str_def
        by simp

      from \<sigma>_cons tran_cons
      have invar\<sigma>tran: "d_nfa.invar \<sigma> \<and> d_nfa.invar Tran"
        unfolding str_def
        by simp

      from \<sigma>_eq Tran_eq invar\<sigma>tran d_nfa.correct
      have c1: "\<sigma>' \<union> Trana = interval_to_set ` d_nfa.\<alpha> (d_nfa.union \<sigma> Tran)"
        by auto

      from \<sigma>_cons str_def
      have cano\<sigma>: "(\<forall>x\<in>d_nfa.\<alpha> \<sigma>. canonicalIs (fst (snd x)))"
        by simp

      from tran_cons str_def
      have canotran: "(\<forall>x\<in>d_nfa.\<alpha> Tran. canonicalIs (fst (snd x)))"
        by simp

      from cano\<sigma> canotran invar\<sigma>tran d_nfa.correct
      have c2: "(\<forall>x\<in>d_nfa.\<alpha> (d_nfa.union \<sigma> Tran). canonicalIs (fst (snd x)))"
        by auto

      from invar\<sigma>tran d_nfa.correct
      have c3: "d_nfa.invar (d_nfa.union \<sigma> Tran)"
        by auto

      from \<sigma>_cons str_def 
      have card\<sigma>: "card \<sigma>' = card (d_nfa.\<alpha> \<sigma>)"
        apply simp
        by blast

      from tran_cons str_def
      have cardtran: "card Trana = card (d_nfa.\<alpha> Tran)"
        apply simp
        by blast

      from tran_cons \<sigma>_cons str_def d_nfa.correct
      have uneq: "interval_to_set ` d_nfa.\<alpha> (d_nfa.union \<sigma> Tran) = \<sigma>' \<union> Trana"
        using c1 by presburger

      from c2 inj_semIs
      have inj\<sigma>tran: "inj_on interval_to_set (d_nfa.\<alpha> (d_nfa.union \<sigma> Tran))"
        
proof -
  have f1: "\<forall>P f. (\<exists>p pa. ((p::'q \<times> ('a \<times> 'a) list \<times> 'q) \<in> P \<and> pa \<in> P \<and> (f p::'q \<times> 'a set \<times> 'q) = f pa) \<and> p \<noteq> pa) \<or> inj_on f P"
    by (meson inj_onI)
obtain pp :: "('q \<times> ('a \<times> 'a) list \<times> 'q \<Rightarrow> 'q \<times> 'a set \<times> 'q) \<Rightarrow> ('q \<times> ('a \<times> 'a) list \<times> 'q) set \<Rightarrow> 'q \<times> ('a \<times> 'a) list \<times> 'q" and ppa :: "('q \<times> ('a \<times> 'a) list \<times> 'q \<Rightarrow> 'q \<times> 'a set \<times> 'q) \<Rightarrow> ('q \<times> ('a \<times> 'a) list \<times> 'q) set \<Rightarrow> 'q \<times> ('a \<times> 'a) list \<times> 'q" where
"\<forall>x0 x1d. (\<exists>v2 v3. (v2 \<in> x1d \<and> v3 \<in> x1d \<and> x0 v2 = x0 v3) \<and> v2 \<noteq> v3) = ((pp x0 x1d \<in> x1d \<and> ppa x0 x1d \<in> x1d \<and> x0 (pp x0 x1d) = x0 (ppa x0 x1d)) \<and> pp x0 x1d \<noteq> ppa x0 x1d)"
by moura
  then have "\<forall>P f. (pp f P \<in> P \<and> ppa f P \<in> P \<and> f (pp f P) = f (ppa f P)) \<and> pp f P \<noteq> ppa f P \<or> inj_on f P"
using f1 by presburger
  moreover
{ assume "pp interval_to_set (d_nfa.\<alpha> (d_nfa.union \<sigma> Tran)) \<noteq> ppa interval_to_set (d_nfa.\<alpha> (d_nfa.union \<sigma> Tran))"
have "(fst (ppa interval_to_set (d_nfa.\<alpha> (d_nfa.union \<sigma> Tran))), semIs (fst (snd (ppa interval_to_set (d_nfa.\<alpha> (d_nfa.union \<sigma> Tran))))), snd (snd (ppa interval_to_set (d_nfa.\<alpha> (d_nfa.union \<sigma> Tran))))) = (fst (pp interval_to_set (d_nfa.\<alpha> (d_nfa.union \<sigma> Tran))), semIs (fst (snd (pp interval_to_set (d_nfa.\<alpha> (d_nfa.union \<sigma> Tran))))), snd (snd (pp interval_to_set (d_nfa.\<alpha> (d_nfa.union \<sigma> Tran))))) \<longrightarrow> pp interval_to_set (d_nfa.\<alpha> (d_nfa.union \<sigma> Tran)) \<notin> d_nfa.\<alpha> (d_nfa.union \<sigma> Tran) \<or> ppa interval_to_set (d_nfa.\<alpha> (d_nfa.union \<sigma> Tran)) \<notin> d_nfa.\<alpha> (d_nfa.union \<sigma> Tran) \<or> interval_to_set (pp interval_to_set (d_nfa.\<alpha> (d_nfa.union \<sigma> Tran))) \<noteq> interval_to_set (ppa interval_to_set (d_nfa.\<alpha> (d_nfa.union \<sigma> Tran))) \<or> pp interval_to_set (d_nfa.\<alpha> (d_nfa.union \<sigma> Tran)) = ppa interval_to_set (d_nfa.\<alpha> (d_nfa.union \<sigma> Tran))"
by (metis (no_types) Pair_inject c2 inj_semIs prod.exhaust_sel)
then have "pp interval_to_set (d_nfa.\<alpha> (d_nfa.union \<sigma> Tran)) \<notin> d_nfa.\<alpha> (d_nfa.union \<sigma> Tran) \<or> ppa interval_to_set (d_nfa.\<alpha> (d_nfa.union \<sigma> Tran)) \<notin> d_nfa.\<alpha> (d_nfa.union \<sigma> Tran) \<or> interval_to_set (pp interval_to_set (d_nfa.\<alpha> (d_nfa.union \<sigma> Tran))) \<noteq> interval_to_set (ppa interval_to_set (d_nfa.\<alpha> (d_nfa.union \<sigma> Tran))) \<or> pp interval_to_set (d_nfa.\<alpha> (d_nfa.union \<sigma> Tran)) = ppa interval_to_set (d_nfa.\<alpha> (d_nfa.union \<sigma> Tran))"
by (metis interval_to_set.simps prod.exhaust_sel) }
ultimately show ?thesis
by meson
qed

      from uneq card_image[of interval_to_set "d_nfa.\<alpha> (d_nfa.union \<sigma> Tran)", OF inj\<sigma>tran]
      have c4: "card (\<sigma>' \<union> Trana) = card (d_nfa.\<alpha> (d_nfa.union \<sigma> Tran))"
        by auto
        
      from c1 c2 c3 c4
      show "\<sigma>' \<union> Trana = interval_to_set ` d_nfa.\<alpha> (d_nfa.union \<sigma> Tran) \<and>
    card (\<sigma>' \<union> Trana) = card (d_nfa.\<alpha> (d_nfa.union \<sigma> Tran)) \<and>
    (\<forall>x\<in>d_nfa.\<alpha> (d_nfa.union \<sigma> Tran). canonicalIs (fst (snd x))) \<and>
    d_nfa.invar (d_nfa.union \<sigma> Tran)"
        by simp
    qed
  }
qed

schematic_goal split_trans_impl_gcode:
  fixes D_it1 :: "'a_set \<Rightarrow> (('a \<times> 'a) list, 'a_set) set_iterator"
    and D_it2 :: "'a_set \<Rightarrow> (('a \<times> 'a) list, 'd_nfa) set_iterator"
    and D_it3 :: "'d_nfa \<Rightarrow> (('q \<times> ('a \<times> 'a) list \<times> 'q), 'd_nfa) set_iterator"
    and D_it4 :: "'d_nfa \<Rightarrow> (('q \<times> ('a \<times> 'a) list \<times> 'q), 'a_set) set_iterator"
  assumes D_it1_OK[rule_format, refine_transfer]: 
          "\<And> x. set_iterator (D_it1 x) {a. a \<in> l.\<alpha> x}" and
          D_it2_OK[rule_format, refine_transfer]: 
          "\<And> x. set_iterator (D_it2 x) {a. a \<in> l.\<alpha> x}" and
          D_it3_OK[rule_format, refine_transfer]: 
          "\<And> x. set_iterator (D_it3 x) {\<alpha>'. \<alpha>' \<in> d_nfa.\<alpha> x}" and
          D_it4_OK[rule_format, refine_transfer]: 
          "\<And> x. set_iterator (D_it4 x) {\<alpha>'. \<alpha>' \<in> d_nfa.\<alpha> x}"
  shows "RETURN ?code \<le> split_trans_impl f1 f2 TS"
  unfolding split_trans_impl_def split_tran_impl_def 
            split_mult_impl_def split_sing_impl_def labels_impl_aux_def
  apply (unfold split_def snd_conv fst_conv prod.collapse)
  by (rule refine_transfer | assumption | erule conjE )+

definition split_trans_code where
  "split_trans_code D_it1 D_it2 D_it3 D_it4 f1 f2 TS = 
   (let x = D_it4 TS (\<lambda>_. True) (\<lambda>x. l.ins (fst (snd x))) (l.empty ())
   in D_it3 TS (\<lambda>_. True)
       (\<lambda>xa \<sigma>.
           Let (let xb = D_it1 x (\<lambda>_. True)
                          (\<lambda>xb \<sigma>'.
                              D_it1 \<sigma>' (\<lambda>_. True)
                               (\<lambda>xc \<sigma>''.
                                   if nemptyIs (intersectIs xc xb)
                                   then if xc = intersectIs xc xb then l.ins xc \<sigma>''
                                        else l.ins (intersectIs xc xb)
 (l.ins (diffIs f1 f2 xc (intersectIs xc xb)) \<sigma>'')
                                   else l.ins xc \<sigma>'')
                               (l.empty ()))
                          (l.ins (fst (snd xa)) (l.empty ()))
                in D_it2 xb (\<lambda>_. True) (\<lambda>xc. d_nfa.add (fst xa) xc (snd (snd xa)))
                    d_nfa.empty)
            (d_nfa.union \<sigma>))
       d_nfa.empty)"

schematic_goal split_trans_impl_code: 
    "split_trans_code D_it1 D_it2 D_it3 D_it4 f1 f2 TS = ?code"
  unfolding split_trans_code_def
  by (rule refl)+

definition nfa_uniq_trans_impl 
where
  "nfa_uniq_trans_impl D_it1 D_it2 D_it3 D_it4 f1 f2 = 
   (\<lambda>(Q, A, D, I, F). 
   (Q, A, (split_trans_code 
    D_it1 D_it2 D_it3 D_it4 f1 f2 D), I, F))"

schematic_goal nfa_uniq_trans_impl_code:
  "nfa_uniq_trans_impl D_it1 D_it2 D_it3 D_it4 f1 f2 (Q, A, D, I, F) = ?code"
  unfolding nfa_uniq_trans_impl_def
  by (rule refl)+


section \<open>tran complement\<close>

definition label_addup_impl where
  "label_addup_impl q TS = 
   FOREACH {t. t \<in> d_nfa.\<alpha> TS}
   (\<lambda> (q1, \<alpha>, q2) S. 
            if (q = q1) then RETURN (\<alpha> # S) 
                        else RETURN S) ([])"



definition split_lrel where 
    "split_lrel = {(i, a). (\<forall> x \<in> (set i). canonicalIs x)
                    \<and> List.map semIs i = a}"
abbreviation "slr \<equiv> split_lrel"
lemmas slr_def[refine_rel_defs] = split_lrel_def

lemma label_addup_correct: 
  fixes q TS TS'
  assumes TS_OK1: "\<forall> (q, i, q') \<in> (d_nfa.\<alpha> TS). canonicalIs i"
      and TS_OK2: "TS' = interval_to_set ` (d_nfa.\<alpha> TS)"
  shows "(label_addup_impl q TS) \<le>\<Down> slr (label_addup_gen q TS')"
  unfolding label_addup_impl_def label_addup_gen_def
  apply (refine_rcg)
  apply (subgoal_tac "inj_on interval_to_set {t. t \<in> d_nfa.\<alpha> TS}")
  apply (assumption)
  using TS_OK1 inj_semIs
  apply (simp add: inj_interval_to_set)
  using TS_OK2 apply simp
  apply (simp add: slr_def)
  apply (simp add: l.empty_correct(1) l.empty_correct(2))
proof -
  fix x it \<sigma> x' it' \<sigma>' x1 x2 x1a x2a x1b x2b x1c x2c
  show "x' = interval_to_set x \<Longrightarrow>
       x \<in> it \<Longrightarrow>
       x' \<in> it' \<Longrightarrow>
       it' = interval_to_set ` it \<Longrightarrow>
       it \<subseteq> {t. t \<in> d_nfa.\<alpha> TS} \<Longrightarrow>
       it' \<subseteq> TS' \<Longrightarrow>
       set \<sigma>' = {uu. \<exists>\<alpha>1 q'. uu = \<alpha>1 \<and> (q, \<alpha>1, q') \<in> TS' - it'} \<Longrightarrow>
       (\<sigma>, \<sigma>') \<in> split_lrel \<Longrightarrow>
       x2 = (x1a, x2a) \<Longrightarrow>
       x' = (x1, x2) \<Longrightarrow>
       x2b = (x1c, x2c) \<Longrightarrow>
       x = (x1b, x2b) \<Longrightarrow> q = x1b \<Longrightarrow> q = x1 \<Longrightarrow> (x1c # \<sigma>, x1a # \<sigma>') \<in> split_lrel"
  proof -
  assume \<sigma>sr: "(\<sigma>, \<sigma>') \<in> split_lrel"
     and xit: "x \<in> it"
     and xit': "x' \<in> it'"
     and xx' : "x' = interval_to_set x"
     and itin: "it \<subseteq> {t. t \<in> d_nfa.\<alpha> TS}"
     and itin': "it' \<subseteq> TS'"
     and x2dem: "x2 = (x1a, x2a)"
     and x'dem: "x' = (x1, x2)"
     and x2bdem: "x2b = (x1c, x2c)"
     and xdem: "x = (x1b, x2b)"
  from this
  have semeq: "semIs x1c = x1a"
    by simp
  from xit itin xdem x2bdem TS_OK1
  have canox1c: "canonicalIs x1c"
    by auto

  from \<sigma>sr
  have c1: "(\<forall> x \<in> set (x1c # \<sigma>). canonicalIs x)"
    unfolding slr_def
    apply simp
    using canox1c
    by auto

  from \<sigma>sr
  have c2: "x1a # \<sigma>' = List.map semIs (x1c # \<sigma>)" 
    unfolding slr_def
    apply simp
    using semeq l.correct
    by auto

  from \<sigma>sr
  have c2': "\<sigma>' = List.map semIs \<sigma>"
    unfolding slr_def
    by simp
  thm  \<sigma>sr slr_def
    show ?thesis
      unfolding slr_def
      apply simp
      by (simp add: c1 c2' semeq)
  qed
qed    

term List.foldl
term "(diffIs f1 f2)"
definition diffS where
  "diffS f1 f2 i s = List.foldl (diffIs f1 f2) i s"

lemma diffS_correct:
  fixes f1 :: "'a ::linorder \<Rightarrow> 'a" 
  fixes f2 :: "'a ::linorder \<Rightarrow> 'a"
  assumes f1_cons: "\<forall> a. a < f1 a \<and> (\<forall> b. a < b \<longrightarrow> f1 a \<le> b)"
     and  f2_cons: "\<forall> a. a > f2 a \<and> (\<forall> b. a > b \<longrightarrow> f2 a \<ge> b)"
     and  i_cano: "canonicalIs i"
     and  s_cano: "\<forall> x \<in> set s. canonicalIs x"
     and i_ok: "canonicalIs i"
   shows "semIs (diffS f1 f2 i s) = (semIs i - \<Union> {semIs x| x. x \<in> set s})
          \<and> canonicalIs (diffS f1 f2 i s)"
  unfolding diffS_def 
  using s_cano i_ok
  apply (induction s arbitrary: i)
  apply simp 
proof -
  fix a s i
  show "(\<And>i. Ball (set s) canonicalIs \<Longrightarrow>
             canonicalIs i \<Longrightarrow>
             semIs (foldl (diffIs f1 f2) i s) = semIs i - \<Union> {semIs x |x. x \<in> set s}\<and>
             canonicalIs (foldl (diffIs f1 f2) i s)) \<Longrightarrow>
       Ball (set (a # s)) canonicalIs \<Longrightarrow>
       canonicalIs i \<Longrightarrow>
       semIs (foldl (diffIs f1 f2) i (a # s)) = semIs i - \<Union> {semIs x |x. x \<in> set (a # s)}\<and>
       canonicalIs (foldl (diffIs f1 f2) i (a # s))"
  proof -
  assume ind_hyp: "\<And>i. Ball (set s) canonicalIs \<Longrightarrow>
          canonicalIs i \<Longrightarrow>
          semIs (foldl (diffIs f1 f2) i s) = semIs i - \<Union> {semIs x |x. x \<in> set s} \<and>
          canonicalIs (foldl (diffIs f1 f2) i s)"
     and pre: "Ball (set (a # s)) canonicalIs"
     and pre': "canonicalIs i"
  from pre
  have cano_a: "canonicalIs a" by auto

  from diffIs_correct[OF f1_cons f2_cons pre' cano_a]
  have canoi':  "canonicalIs (diffIs f1 f2 i a)"
    by auto

  from pre ind_hyp canoi'
  have semeq: "semIs (foldl (diffIs f1 f2) (diffIs f1 f2 i a) s) = 
            semIs (diffIs f1 f2 i a) - \<Union> {semIs x |x. x \<in> set s}"
    by auto

  from diffIs_correct[OF f1_cons f2_cons i_cano cano_a] semeq
       diffIs_correct[OF f1_cons f2_cons canoi' cano_a]
  show "semIs (foldl (diffIs f1 f2) i (a # s)) = semIs i - \<Union> {semIs x |x. x \<in> set (a # s)} \<and>
    canonicalIs (foldl (diffIs f1 f2) i (a # s))"
    apply simp
    by (simp add: \<open>semIs (diffIs f1 f2 i a) = semIs i - semIs a \<and> canonicalIs (diffIs f1 f2 i a)\<close> 
          ind_hyp pre set_diff_diff_left)
    qed
qed


definition complete_trans_impl where
  "complete_trans_impl f1 f2 Q L q_dead ST =
    FOREACH
    {q. q \<in> s.\<alpha> Q}
    (\<lambda> q ST'. do {
      L' \<leftarrow> label_addup_impl q ST;
      df \<leftarrow> RETURN (diffS f1 f2 L L');
      if (emptyIs df) then RETURN ST' 
      else RETURN (d_nfa.add q df q_dead ST')})
    ST"

lemma complete_trans_impl_correct: 
  fixes Q Q'
  fixes f1 :: "'a ::linorder \<Rightarrow> 'a" 
  fixes f2 :: "'a ::linorder \<Rightarrow> 'a"
  assumes f1_cons: "\<forall> a. a < f1 a \<and> (\<forall> b. a < b \<longrightarrow> f1 a \<le> b)"
     and  f2_cons: "\<forall> a. a > f2 a \<and> (\<forall> b. a > b \<longrightarrow> f2 a \<ge> b)"
     and QQ': "Q = {q. q \<in> s.\<alpha> Q'}"
      and ST_OK: "(ST, ST') \<in> str"
      and ST_OK1: "\<forall> (q, i, q') \<in> (d_nfa.\<alpha> ST). canonicalIs i"
      and ST_OK2: "ST' = interval_to_set ` (d_nfa.\<alpha> ST)"
      and diff_OK: "\<And> L L'. diff L L' = L - \<Union> (set L')"
      and L_OK: "canonicalIs L'"
      and LL'_OK: "semIs L' = L"
  shows "complete_trans_impl f1 f2 Q' L' q_dead ST \<le>\<Down> str 
         (complete_trans_gen diff Q L q_dead ST')"
  unfolding complete_trans_impl_def complete_trans_gen_def RETURN_def
  apply (refine_rcg)
  apply (subgoal_tac "inj_on id {q. q \<in> s.\<alpha> Q'}")
  apply assumption
  apply force
  using QQ' apply force
  using ST_OK apply force
  apply (subgoal_tac "label_addup_impl x ST \<le> \<Down> slr (label_addup_gen x' ST')")
  apply assumption
  apply (insert label_addup_correct[OF ST_OK1 ST_OK2])
     apply force
    defer
  apply force
proof -
  {
    fix x it \<sigma> x' it' \<sigma>' L'a L'aa df
    assume slrrel: "(L'a, L'aa) \<in> split_lrel"
       and strrel: "(\<sigma>, \<sigma>') \<in> str"
       and df_def: "df \<in> {diffS f1 f2 L' L'a}"
    from slrrel
    have canoLa: "\<forall> x \<in> set L'a. canonicalIs x"
      unfolding split_lrel_def by simp
    from diff_OK
    have "diff L L'aa = L - \<Union> (set L'aa)" by auto

    from slrrel this
    have c1: "diff L L'aa = L - \<Union>  {semIs x |x. x \<in> set L'a}"
      unfolding slr_def
      by force

    from df_def L_OK slrrel slr_def diffS_correct[OF f1_cons f2_cons L_OK canoLa]
    have canodf: "canonicalIs df"
      by auto

    from diffS_correct[OF f1_cons f2_cons L_OK canoLa L_OK]
         df_def
    have c2: "semIs df = semIs L' - \<Union> {semIs x |x. x \<in> set L'a}"
      by auto
  from c1 c2 LL'_OK emptyIs_correct canodf
  show "emptyIs df = (diff L L'aa = {})"
    by metis
  }
  {
    fix x it \<sigma> x' it' \<sigma>' L'a L'aa df
    show " x' = id x \<Longrightarrow>
       x \<in> it \<Longrightarrow>
       x' \<in> it' \<Longrightarrow>
       it' = id ` it \<Longrightarrow>
       it \<subseteq> {q. q \<in> s.\<alpha> Q'} \<Longrightarrow>
       it' \<subseteq> Q \<Longrightarrow>
       \<sigma>' =
       ST' \<union>
       {(q, L - \<Union> {uu. \<exists>\<alpha>' q'. uu = \<alpha>' \<and> (q, \<alpha>', q') \<in> ST'}, q_dead) |q.
        q \<in> Q - it' \<and> L - \<Union> {uu. \<exists>\<alpha>' q'. uu = \<alpha>' \<and> (q, \<alpha>', q') \<in> ST'} \<noteq> {}} \<Longrightarrow>
       (\<sigma>, \<sigma>') \<in> str \<Longrightarrow>
       (L'a, L'aa) \<in> split_lrel \<Longrightarrow>
       df \<in> {diffS f1 f2 L' L'a} \<Longrightarrow>
       \<not> emptyIs df \<Longrightarrow>
       diff L L'aa \<noteq> {} \<Longrightarrow>
       (\<And>q. label_addup_impl q ST \<le> \<Down> split_lrel (label_addup_gen q ST')) \<Longrightarrow>
       RES {d_nfa.add x df q_dead \<sigma>}
       \<le> SPEC (\<lambda>c. (c, \<sigma>' \<union> {(x', diff L L'aa, q_dead)}) \<in> str)"
    proof -
    assume \<sigma>str: "(\<sigma>, \<sigma>') \<in> str"
       and srel: "(L'a, L'aa) \<in> split_lrel"
       and df_def: "df \<in> {diffS f1 f2 L' L'a}"
       and nemptydf: "\<not> emptyIs df"
       and nemptyab: "diff L L'aa \<noteq> {}"
       and xxeq: "x' = id x"

    from srel 
    have srel_cons: "(\<forall>x\<in>set L'a. canonicalIs x) \<and> map semIs L'a = L'aa"
      unfolding split_lrel_def
      by simp

    from diffS_correct[OF f1_cons f2_cons L_OK _ L_OK, of L'a] diff_OK[of L L'aa]
         srel_cons df_def LL'_OK
    have "semIs df = semIs L' - \<Union> {semIs x |x. x \<in> set L'a}" by auto
    from this diffS_correct[OF f1_cons f2_cons L_OK _ L_OK, of L'a] diff_OK[of L L'aa]
         srel_cons df_def LL'_OK
    have labeleq: "semIs df = diff L L'aa \<and> canonicalIs df"
      by fastforce

    from \<sigma>str str_def
    have \<sigma>\<sigma>'_cons:  "\<sigma>' = interval_to_set ` d_nfa.\<alpha> \<sigma> \<and>
          card \<sigma>' = card (d_nfa.\<alpha> \<sigma>) \<and>
          (\<forall>x\<in>d_nfa.\<alpha> \<sigma>. canonicalIs (fst (snd x))) \<and> d_nfa.invar \<sigma>"
      by auto

    from d_nfa.correct(10)[of \<sigma> x df q_dead] \<sigma>\<sigma>'_cons labeleq xxeq
    have c1: "insert (x', diff L L'aa, q_dead) \<sigma>' =
              interval_to_set ` d_nfa.\<alpha> (d_nfa.add x df q_dead \<sigma>)"
      by simp

    from \<sigma>\<sigma>'_cons labeleq
    have c2: "(\<forall>x\<in>d_nfa.\<alpha> (d_nfa.add x df q_dead \<sigma>). canonicalIs (fst (snd x))) \<and>
              d_nfa.invar (d_nfa.add x df q_dead \<sigma>)"
      by (simp add: d_nfa.lts_add_correct(1) d_nfa.lts_add_correct(2))

    from \<sigma>\<sigma>'_cons
    have c3: "card (insert (x', diff L L'aa, q_dead) \<sigma>') =
              card (d_nfa.\<alpha> (d_nfa.add x df q_dead \<sigma>))"
    proof (cases "(x', diff L L'aa, q_dead) \<in> \<sigma>'")
      case True
      from this 
      have eq1: "card (insert (x', diff L L'aa, q_dead) \<sigma>') = card \<sigma>'"
        by (simp add: insert_absorb)

      from True \<sigma>\<sigma>'_cons
      obtain \<alpha>1 where \<alpha>1_def: "(x', \<alpha>1, q_dead) \<in> d_nfa.\<alpha> \<sigma> \<and> semIs \<alpha>1 = diff L L'aa"
        by force

      from this labeleq \<sigma>\<sigma>'_cons inj_semIs_aux
      have "(x', \<alpha>1, q_dead) = (x', df, q_dead)"
        by (metis fst_conv snd_conv)

      from this \<alpha>1_def
      have eq2: "card (d_nfa.\<alpha> (d_nfa.add x df q_dead \<sigma>)) = card (d_nfa.\<alpha> \<sigma>)"
        by (simp add: \<sigma>\<sigma>'_cons d_nfa.lts_add_correct(2) insert_absorb xxeq)
      from eq1 eq2 \<sigma>\<sigma>'_cons
      show ?thesis by auto
  next
    case False
    from \<sigma>\<sigma>'_cons
    have "finite \<sigma>'" by force
    from False this card_insert
    have eq1: "card (insert (x', diff L L'aa, q_dead) \<sigma>') = 1 + card \<sigma>'"
      by auto

    from \<sigma>\<sigma>'_cons
    have finite\<sigma>: "finite (d_nfa.\<alpha> \<sigma>)"
      by force
    from False
    have "(x', df, q_dead) \<notin> d_nfa.\<alpha> \<sigma>"
      using \<sigma>\<sigma>'_cons image_iff labeleq by fastforce
    from this d_nfa.correct(10)[of \<sigma> x df q_dead] \<sigma>\<sigma>'_cons  card_insert[OF finite\<sigma>]
    have eq2: "card (d_nfa.\<alpha> (d_nfa.add x df q_dead \<sigma>)) = 1 + card (d_nfa.\<alpha> \<sigma>)"
      by (simp add: xxeq)
    from eq1 eq2 \<sigma>\<sigma>'_cons
    show ?thesis 
      by force
  qed

  show "RES {d_nfa.add x df q_dead \<sigma>} \<le> 
        SPEC (\<lambda>c. (c, \<sigma>' \<union> {(x', diff L L'aa, q_dead)}) \<in> str)"
      unfolding str_def
      apply simp
      using c1 c2 c3
      by auto
  qed
}
qed


definition nfa_tran_complete where
    "nfa_tran_complete f1 f2 = (\<lambda>(Q, A, D, I, F) q_dead. do { 
     \<Delta>' \<leftarrow> complete_trans_impl f1 f2 Q A q_dead D;
     RETURN (s.ins q_dead Q, A, d_nfa.add q_dead A q_dead \<Delta>', I, F)})"

schematic_goal nfa_tran_complete_impl_code:
  fixes D_it1 :: "'q_set \<Rightarrow> ('q, 'd_nfa) set_iterator"
  fixes D_it2 :: "'d_nfa \<Rightarrow> (('q \<times> ('a \<times> 'a) list \<times> 'q), 
                            ('a \<times> 'a) list list) set_iterator"
  assumes D_it1_OK [rule_format, refine_transfer]:
          "\<And>x. set_iterator (D_it1 x) {q. q \<in> s.\<alpha> x}" and
          D_it4_OK[rule_format, refine_transfer]: 
          "\<And> x. set_iterator (D_it2 x) {\<alpha>'. \<alpha>' \<in> d_nfa.\<alpha> x}" 
  shows "RETURN ?code \<le> nfa_tran_complete f1 f2 (Q, A, D, I, F) q_dead"
  unfolding nfa_tran_complete_def complete_trans_impl_def 
            label_addup_impl_def
  apply (unfold split_def snd_conv fst_conv prod.collapse) 
  by (rule refine_transfer | assumption| erule conjE )+
  
definition nfa_tran_complete_code where 
  "nfa_tran_complete_code D_it1 D_it2 f1 f2 = (\<lambda> (Q, A, D, I, F) q_dead. 
  (let x = D_it1 Q (\<lambda>_. True)
            (\<lambda>x \<sigma>. let xa = D_it2 D (\<lambda>_. True)
                             (\<lambda>xa \<sigma>'. if x = fst xa then fst (snd xa) # \<sigma>' else \<sigma>') [];
                       xb = diffS f1 f2 A xa
                   in if emptyIs xb then \<sigma> else d_nfa.add x xb q_dead \<sigma>)
            D
   in (s.ins q_dead Q, A, d_nfa.add q_dead A q_dead x, I, F)))"

schematic_goal nfa_trans_complete_impl_code:
  "nfa_tran_complete_code D_it1 D_it2 f1 f2 (Q, A, D, I, F) q_dead = ?code"
  unfolding nfa_tran_complete_code_def
  by (rule refl)+

end


interpretation rs_nfa_split_defs: nfa_split_tran_imp rs_ops rs_ops rs_lts_ops
  by intro_locales

definition dnfa_iter where
  "dnfa_iter = (\<lambda> x c f s. rm_iteratei x c (\<lambda> (q, aq') s1. rm_iteratei aq' 
        (\<lambda> _. True) (\<lambda> (a, mq') s2. rs_iteratei mq' (\<lambda> _. True) 
         (\<lambda> q' s3. f (q, a, q') s3) s2) s1) s)"

definition rs_split_trans_code where 
    "rs_split_trans_code = rs_nfa_split_defs.split_trans_code 
                          (\<lambda> x. rs_iteratei x) (\<lambda> x. rs_iteratei x) 
                          (\<lambda> x. dnfa_iter x) (\<lambda> x. dnfa_iter x) 
                         "

definition rs_nfa_uniq where
    "rs_nfa_uniq = rs_nfa_split_defs.nfa_uniq_trans_impl 
                          (\<lambda> x. rs_iteratei x) (\<lambda> x. rs_iteratei x)
                          (\<lambda> x. dnfa_iter x) (\<lambda> x. dnfa_iter x)"

definition rs_nfa_tran_complement where
    "rs_nfa_tran_complement = 
        rs_nfa_split_defs.nfa_tran_complete_code (\<lambda> x. rs_iteratei x) 
        (\<lambda> x. dnfa_iter x)"

lemmas rs_split_set_defs =
        rs_split_trans_code_def
        rs_nfa_uniq_def
        rs_nfa_tran_complement_def

lemmas rs_split_trans_code [code] = 
      rs_nfa_split_defs.split_trans_impl_code[of "(\<lambda> x. rs_iteratei x)" 
                                                 "(\<lambda> x. rs_iteratei x)"
                                                 "(\<lambda> x. dnfa_iter x)"
                                                 "(\<lambda> x. dnfa_iter x)",
                                                   folded rs_split_set_defs]

lemmas rs_nfa_uniq_code [code] = 
      rs_nfa_split_defs.nfa_uniq_trans_impl_code[of "(\<lambda> x. rs_iteratei x)" 
                                                 "(\<lambda> x. rs_iteratei x)"
                                                 "(\<lambda> x. dnfa_iter x)"
                                                 "(\<lambda> x. dnfa_iter x)",
                                                   folded rs_split_set_defs]


lemmas rs_nfa_tran_complement_code [code] = 
      rs_nfa_split_defs.nfa_trans_complete_impl_code[of "(\<lambda> x. rs_iteratei x)" 
                                                    "(\<lambda> x. dnfa_iter x)",
                                                   folded rs_split_set_defs]



end











