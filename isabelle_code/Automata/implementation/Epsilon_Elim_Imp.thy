
theory Epsilon_Elim_Imp

imports Main "../Epsilon_elim"  Automatic_Refinement.Automatic_Refinement

begin

term prod_rel

definition f :: "('a \<Rightarrow> _) \<Rightarrow> 'a \<Rightarrow> _" where "f g x = g x"

definition init_state :: "'q \<Rightarrow> ('q \<times> 'q) set \<Rightarrow> 'q set nres" where
    "init_state q t \<equiv>  
     FOREACHi
      (\<lambda> T S. S = {q'. (q, q') \<in> t - T \<or> q' = q})
      {p . p \<in> t} 
      (\<lambda> (x, y) S. (if x = q then RETURN (insert y S) else RETURN S)) {q}"


lemma init_state_correct:
  fixes q tn
  assumes tn_ok: "finite tn"
  shows "init_state q tn \<le> SPEC (\<lambda> S. S = {q'. (q, q') \<in> tn \<or> q' = q})"
  unfolding init_state_def
  apply (rule refine_vcg)
  using tn_ok apply simp
  apply blast
  defer
  apply blast
proof -
  fix x it \<sigma>
  assume xit: "x \<in> it"
     and itin: "it \<subseteq> {p. p \<in> tn}"
     and \<sigma>_ok: "\<sigma> = {q'. (q, q') \<in> tn - it \<or> q' = q}"

  from xit obtain q1 q2 where
  qq'_def: "x = (q1, q2)" 
    by fastforce

  from xit itin \<sigma>_ok qq'_def
  have c1: "q = q1 \<longrightarrow> {q'. (q, q') \<in> tn \<and> ((q, q') \<in> it \<longrightarrow> q' = q2)} = 
        {q'. (q, q') \<in> tn - it} \<union> {q2}"
    by force
    
  
  show "(case x of (x, y) \<Rightarrow> \<lambda>S. if x = q then RETURN (insert y S) 
            else RETURN S) \<sigma>
         \<le> SPEC (\<lambda>S. S = {q'. (q, q') \<in> tn - (it - {x}) \<or> q' = q})"
    apply (simp add: qq'_def)
    apply (rule_tac conjI)
    defer
    using \<sigma>_ok xit itin
    apply auto[1]
    using \<sigma>_ok xit itin c1
    by force
qed

definition init_closure :: "'q set \<Rightarrow> ('q \<times> 'q) set \<Rightarrow> 
                            ('q, 'q set) map nres" where
    "init_closure S T \<equiv> do {
       FOREACHi
        (\<lambda> S' P. dom P = (S - S') \<and> (\<forall> q \<in> S - S'. 
                  (P q) = Some {q'. (q, q') \<in> T \<or> q' = q})) 
        {q. q \<in> S} 
        (\<lambda> q P. do { 
            onestep \<leftarrow> init_state q T;
            RETURN (P (q \<mapsto>  onestep))}) (Map.empty)
      }"

lemma init_closure_correct:
  fixes S T
  assumes finite_S: "finite S"
      and T_ok: "finite T"
  shows "init_closure S T \<le> SPEC (\<lambda> P. (\<forall> q \<in> S. 
                (P q) = Some {q'. (q, q') \<in> T \<or> q' = q}))"
  unfolding init_closure_def
  apply (refine_vcg)
  using finite_S apply simp
  apply simp apply force
  defer
  apply force 
proof -
  fix x it \<sigma>
  assume xin: "x \<in> it"
     and itin: "it \<subseteq> {q. q \<in> S}"
     and pinvar: "dom \<sigma> = S - it \<and> (\<forall>q\<in>S - it. \<sigma> q = Some {q'. (q, q') \<in> T \<or> q' = q})"
  from init_state_correct[OF T_ok, of x]
  have c1: "init_state x T \<le> SPEC (\<lambda>S. S = {q'. (x, q') \<in> T \<or> q' = x})"
    by auto
  have "SPEC (\<lambda>S. S = {q'. (x, q') \<in> T \<or> q' = x}) \<le>
        SPEC (\<lambda>onestep.
                   RETURN (\<sigma>(x \<mapsto> onestep))
                   \<le> SPEC (\<lambda>P. dom P = S - (it - {x}) \<and>
                                (\<forall>q\<in>S - (it - {x}).
                                    P q = Some {q'. (q, q') \<in> T \<or> q' = q})))"
    apply simp
    apply rule
    apply rule 
    using itin pinvar xin apply force 
    using pinvar apply blast
    using pinvar by blast
    
      
 from this c1
  show "init_state x T
       \<le> SPEC (\<lambda>onestep.
                   RETURN (\<sigma>(x \<mapsto> onestep))
                   \<le> SPEC (\<lambda>P. dom P = S - (it - {x}) \<and>
                                (\<forall>q\<in>S - (it - {x}).
                                    P q = Some {q'. (q, q') \<in> T \<or> q' = q})))"
    using SPEC_trans by blast
qed

lemma init_closure_correct':
  fixes S T
  assumes finite_S: "finite S"
      and T_ok: "finite T"
  shows "init_closure S T \<le> SPEC (\<lambda> P. (\<forall> q \<in> S. 
                \<forall> q' \<in> the (P q). epsilon_reachable q q' T))"
proof -
  have "SPEC (\<lambda>P. \<forall>q\<in>S. P q = Some {q'. (q, q') \<in> T \<or> q' = q}) \<le> 
        SPEC (\<lambda> P. (\<forall> q \<in> S. 
                \<forall> q' \<in> the (P q). epsilon_reachable q q' T))"
    apply simp
  proof 
    fix x
    assume xin: "x \<in> {P. \<forall>q\<in>S. P q = Some {q'. (q, q') \<in> T \<or> q' = q}}"
    from this have x_cons: "\<forall>q\<in>S. the (x q) = {q'. (q, q') \<in> T \<or> q' = q}"
      by auto
    from this epsilon_reachable_def
    have "\<forall>q\<in>S. \<forall>q'\<in>the (x q). epsilon_reachable q q' T"
      by (metis (mono_tags, lifting) epsilon_reach.simps(2) 
                  epsilon_reach.simps(3) last.simps list.distinct(1) 
                    list.sel(1) mem_Collect_eq)
    from this
    show "x \<in> {P. \<forall>q\<in>S. \<forall>q'\<in>the (P q). epsilon_reachable q q' T}"
      by auto
  qed
  from this init_closure_correct[OF finite_S T_ok]
  show "init_closure S T \<le> 
            SPEC (\<lambda>P. \<forall>q\<in>S. \<forall>q'\<in>the (P q). epsilon_reachable q q' T)"
    using SPEC_trans by blast
qed


definition one_step_state :: "'q \<Rightarrow> ('q, 'q set) map \<Rightarrow> 
                                    ('q, 'q set) map nres" where
    "one_step_state q P \<equiv> do {
       newset \<leftarrow> 
        (FOREACHi
          (\<lambda> S S'. 
              S' = \<Union> { the (P q')| q'. q' \<in> the (P q) - S } \<union> (the (P q)))
          {q'. q'\<in> (the (P q))}
          (\<lambda> q RS. do { 
              RETURN (RS \<union> (the (P q)))}) 
                (the (P q)));
       RETURN ([q \<mapsto> newset])
      }"

lemma one_step_state_correct:
  fixes q P
  assumes finite_Pq : "finite ((the (P q)))"
  shows "one_step_state q P \<le> 
          SPEC (\<lambda> P'. dom P' = {q} \<and> 
                  the (P' q) = \<Union> {the (P q') | q'. q' \<in> the (P q)} \<union> the (P q))"
  unfolding one_step_state_def
  apply (refine_vcg)
  using finite_Pq apply simp
  apply simp
  apply simp
  defer
  apply force
  apply force
proof -
  fix x it \<sigma>
  assume xin: "x \<in> it"
     and itin: "it \<subseteq> the (P q)"
     and \<sigma>_OK: "\<sigma> = \<Union> {the (P q') |q'. q' \<in> the (P q) \<and> q' \<notin> it} \<union> the (P q)"
  
  show "\<Union> {the (P q') |q'. q' \<in> the (P q) \<and> q' \<notin> it} \<union> the (P q) \<union> the (P x) =
        \<Union> {the (P q') |q'. q' \<in> the (P q) \<and> (q' \<in> it \<longrightarrow> q' = x)} \<union> the (P q)"  
    using \<sigma>_OK xin itin
    by fastforce
qed

definition one_step :: "'q set \<Rightarrow> ('q, 'q set) map 
                              \<Rightarrow> ('q, 'q set) map nres" where
    "one_step S P \<equiv> do {
       FOREACHi
          (\<lambda> S' P'. dom P' = S - S' \<and> \<Union> (ran P') \<subseteq> S \<and>
                    (\<forall> q \<in> S - S'. 
                      (the (P' q) = 
                      \<Union> {the (P q')| 
                           q'. q' \<in> (the (P q))} \<union> 
                           the (P q))))
          {q'. q'\<in> S}
          (\<lambda> q P'. do {
              qM \<leftarrow> (one_step_state q P);
              RETURN (P' ++ qM)}) (Map.empty)
      }"

lemma one_step_correct:
  fixes S P
  assumes finite_S: "finite S"
      and invarSP: "dom P = S \<and> \<Union> (ran P) \<subseteq> S"
      and finite_P: "\<forall> s \<in> (ran P). finite s"
  shows "one_step S P \<le> 
          SPEC (\<lambda> P'. dom P' = S \<and> \<Union> (ran P') \<subseteq> S \<and> (\<forall> q \<in> S. 
            (the (P' q)) = \<Union> {the (P q')| q'. q' \<in> (the (P q))} \<union> the (P q)))"
  unfolding one_step_def
  apply (refine_vcg)
  using finite_S apply simp
  apply simp 
  apply force 
  apply force
  defer  
  apply force 
  apply force
  apply force
  apply simp
proof -
  fix x it \<sigma>
  assume xin: "x \<in> it"
     and itin: "it \<subseteq> S"
     and \<sigma>_OK: 
        "dom \<sigma> = S - it \<and>
       \<Union> (ran \<sigma>) \<subseteq> S \<and> 
        (\<forall>q\<in>S - it. the (\<sigma> q) = \<Union> {the (P q') |q'. q' \<in> the (P q)} \<union> the (P q))"
 
  from this finite_P invarSP xin itin
  have c1: "finite (the (P x))"
    apply simp
    unfolding ran_def
    by force

  have "SPEC (\<lambda>P'. dom P' = {x} \<and>
              the (P' x) = \<Union> {the (P q') |q'. q' \<in> the (P x)} \<union> the (P x)) \<le>
        SPEC (\<lambda>qM.  dom qM \<union> (S - it) = S - (it - {x}) \<and>
                     \<Union> (ran (\<sigma> ++ qM)) \<subseteq> S \<and> (\<forall>q\<in>S - (it - {x}).
                        the ((\<sigma> ++ qM) q) =
                        \<Union> {the (P q') |q'. q' \<in> the (P q)} \<union> the (P q)))"
    apply simp
  proof 
    fix xa
    assume xain: "xa \<in> {P'. dom P' = {x} \<and>
                    the (P' x) =
                    \<Union> {the (P q') |q'. q' \<in> the (P x)} \<union> the (P x)}"
    from this
    have c0: "dom xa = {x} \<and>
              the (xa x) = \<Union> {the (P q') |q'. q' \<in> the (P x)} \<union> the (P x)"
      by auto
    thm this invarSP
    have ranxa: "\<Union> (ran xa) \<subseteq> S"
      unfolding ran_def
      apply rule
      apply (rename_tac x')
    proof -
      fix x'
      assume x'in: "x' \<in> \<Union> {b. \<exists>a. xa a = Some b}"
      from this c0 obtain b where
      a_def: "xa x = Some b \<and> x' \<in> b"
        by force
      from this c0
      have c0: "b = \<Union> {the (P q') |q'. q' \<in> the (P x)} \<union> the (P x)"
        by auto

      from invarSP  xin itin ranI[of P x]
      have c1: "the (P x) \<subseteq> S"
        unfolding ran_def 
        using subset_iff by fastforce
      thm invarSP ranI
      have c2: "\<Union> {the (P q') |q'. q' \<in> the (P x)} \<subseteq> S"
        apply (rule)
      proof -
        fix xa
        assume xain: "xa \<in> \<Union> {the (P q') |q'. q' \<in> the (P x)}"
        from this obtain q' S' where
        q'S'_def: "q' \<in> the (P x) \<and> S' = the (P q') \<and> xa \<in> S'"
          by auto
        from this have "q' \<in> S" 
          using c1 by blast
        from this q'S'_def invarSP ranI
        have "S' \<subseteq> S"
          unfolding ran_def
          using subset_iff by fastforce
        from this q'S'_def
        show "xa \<in> S" by auto
      qed
      from this c0 c1 c2 a_def
      show "x' \<in>  S"
        by auto
    qed

 
    from \<sigma>_OK c0 xin itin
    have c3: "dom \<sigma> \<inter> dom xa = {}"
      by simp
    
    have c4:"dom xa \<union> (S - it) = S - (it - {x}) \<and>
                     \<Union> (ran (\<sigma> ++ xa)) \<subseteq> S"
      apply (rule conjI)
      using xin itin c0
      apply force
      using \<sigma>_OK ranxa c0 ran_map_add[OF c3]
      by auto
 

    from itin xin
    have c2: "S - (it - {x}) = (S - it) \<union> {x} \<and> x \<notin> (S - it)"
      by force
  
    from this
    have c1: "\<forall>q\<in>S - (it - {x}). the ((\<sigma> ++ xa) q) =
                        \<Union> {the (P q') |q'. q' \<in> the (P q)} \<union> the (P q)"
      apply simp
      apply (rule conjI)
      using c0 \<sigma>_OK c2
      apply force
      by (metis (no_types, lifting) 
          Diff_iff Diff_insert_absorb \<sigma>_OK c0 map_add_dom_app_simps(3))
    from this c4
    show "xa \<in> {qM. dom qM \<union> (S - it) = S - (it - {x}) \<and>
                     \<Union> (ran (\<sigma> ++ qM)) \<subseteq> S \<and>
                     (\<forall>q\<in>S - (it - {x}).
                         the ((\<sigma> ++ qM) q) =
                         \<Union> {the (P q') |q'. q' \<in> the (P q)} \<union> the (P q))}"
      by blast
  qed
  from this one_step_state_correct[of P x, OF c1]
  show "one_step_state x P
       \<le> SPEC (\<lambda>qM. dom qM \<union> (S - it) = S - (it - {x}) \<and>
                     \<Union> (ran (\<sigma> ++ qM)) \<subseteq> S \<and> (\<forall>q\<in>S - (it - {x}).
                        the ((\<sigma> ++ qM) q) =
                        \<Union> {the (P q') |q'. q' \<in> the (P q)} \<union> the (P q)))"
    using SPEC_trans by blast
qed

lemma one_step_correct':
  fixes S P T
  assumes finite_S: "finite S"
      and invarSP: "dom P = S \<and> \<Union> (ran P) \<subseteq> S"
      and finite_P: "\<forall> s \<in> (ran P). finite s"
      and P_reach: "\<forall>q\<in>S. \<forall>q'\<in>the (P q). epsilon_reachable q q' T"
  shows "one_step S P \<le> 
          SPEC (\<lambda> P'. dom P' = S \<and> \<Union> (ran P') \<subseteq> S \<and> 
                      (\<forall>q\<in>S. \<forall>q'\<in>the (P' q). epsilon_reachable q q' T))"
proof -
  thm one_step_correct[of S P, OF finite_S invarSP finite_P]
  have "SPEC (\<lambda>P'. dom P' = S \<and>
              \<Union> (ran P') \<subseteq> S \<and>
              (\<forall>q\<in>S. the (P' q) =
                      \<Union> {the (P q') |q'. q' \<in> the (P q)} \<union> the (P q)))
        \<le> SPEC (\<lambda> P'. dom P' = S \<and> \<Union> (ran P') \<subseteq> S \<and> 
                      (\<forall>q\<in>S. \<forall>q'\<in>the (P' q). epsilon_reachable q q' T))"
    apply simp
  proof
    fix x
    assume xin: "x \<in> {P'. dom P' = S \<and>
                  \<Union> (ran P') \<subseteq> S \<and>
                  (\<forall>q\<in>S. the (P' q) =
                          \<Union> {the (P q') |q'. q' \<in> the (P q)} \<union> the (P q))}"
    from this 
    have xin': "dom x = S \<and>  \<Union> (ran x) \<subseteq> S \<and>
          (\<forall>q\<in>S. the (x q) = \<Union> {the (P q') |q'. q' \<in> the (P q)} \<union> the (P q))"
      by auto
    have "dom x = S \<and> \<Union> (ran x) \<subseteq> S \<and> 
               (\<forall>q\<in>S. \<forall>q'\<in>the (x q). epsilon_reachable q q' T)"    
      apply (rule conjI)
      using xin' apply simp
      apply (rule conjI)
      using xin' apply simp
      apply (rule) +
    proof -
      fix q q'
      assume qin: "q \<in> S"
         and q'in: "q' \<in> the (x q)"

      show "epsilon_reachable q q' T"
      proof (cases "q' \<in> the (P q)")
      case True 
      from True P_reach qin
      show ?thesis by auto
      next
        case False
        from this q'in xin' qin
        have "q' \<in> \<Union> {the (P q') |q'. q' \<in> the (P q)}" by auto
        from this
        obtain qi where 
        qi_def: "qi \<in> the (P q) \<and> q' \<in> the (P qi)"
          by auto
        from this P_reach qin 
        have reach1: "epsilon_reachable q qi T" and
             reach2: "epsilon_reachable qi q' T"
           apply blast
          by (metis (no_types, lifting) P_reach Sup_le_iff 
                domD in_mono option.sel qi_def qin ranI sup_ge2 xin')
        from this 
        obtain l1 l2 where 
         l1_def: "l1 \<noteq> [] \<and> epsilon_reach l1 T \<and> hd l1 = q \<and> last l1 = qi" and
         l2_def: "l2 \<noteq> [] \<and> epsilon_reach l2 T \<and> hd l2 = qi \<and> last l2 = q'"
          unfolding epsilon_reachable_def
          by auto
        let ?l = "l1 @ (tl l2)"
        from l1_def l2_def
        have c0: "hd ?l = q \<and> last l2 = q'"
          by simp
        from l1_def
        have c1: "?l \<noteq> []" by auto

        have c2: "epsilon_reach ?l T"      
          by (metis append_Cons append_butlast_last_id 
                    append_eq_append_conv2 epsilon_reach_concate 
                    hd_Cons_tl l1_def l2_def self_append_conv)
        from c0 c1 c2
        show ?thesis 
          unfolding epsilon_reachable_def
          by (metis l1_def l2_def last.simps last_append list.exhaust_sel)
      qed
    qed
    from this
    show "x \<in> {P'. dom P' = S \<and>
                   \<Union> (ran P') \<subseteq> S \<and>
                   (\<forall>q\<in>S. \<forall>q'\<in>the (P' q). epsilon_reachable q q' T)}"
      by auto
  qed
  from this one_step_correct[OF finite_S invarSP finite_P]
  show "one_step S P
    \<le> SPEC (\<lambda>P'. dom P' = S \<and>
                  \<Union> (ran P') \<subseteq> S \<and>
                  (\<forall>q\<in>S. \<forall>q'\<in>the (P' q). epsilon_reachable q q' T))"
    using SPEC_trans by blast
qed

(*
definition reach_closed :: "('q, bool) set_iterator \<Rightarrow> ('q, 'q set) map \<Rightarrow> bool" where
  "reach_closed it R \<equiv> 
     it (\<lambda> _. True)  
        (\<lambda> x b. (\<Union> {the (R y) | y. y \<in> the (R x)} \<subseteq> the (R x)) \<and> b) True"
*)

definition reach_closed :: "'q set \<Rightarrow> ('q, 'q set) map \<Rightarrow> bool" where
  "reach_closed S R \<equiv> (\<forall> q \<in> S. (\<forall> q' \<in> the (R q). the (R q') \<subseteq> the (R q)))"

lemma reach_closed_correct: 
  fixes S R
  assumes R_OK: "dom R = S \<and> \<Union> (ran R) \<subseteq> S"
  shows "reach_closed S R \<longleftrightarrow> 
         (\<forall> q \<in> S. \<Union> {the (R y) | y. y \<in> the (R q)} \<subseteq> the (R q))"
  unfolding reach_closed_def
  by auto

(*
lemma reach_closed_correct: 
  fixes S it R
  assumes it_OK: "set_iterator it S"
      and R_OK: "dom R = S \<and> \<Union> (ran R) \<subseteq> S"
  shows "reach_closed it R \<longleftrightarrow> 
         (\<forall> q \<in> S. \<Union> {the (R y) | y. y \<in> the (R q)} \<subseteq> the (R q))"
  unfolding reach_closed_def
  using it_OK
proof -
  assume set_it: "set_iterator it S"
  from this
  obtain l0 where
  l0_def: "distinct l0 \<and> S = set l0 \<and> 
         sorted_wrt (\<lambda>_ _. True) l0 \<and> it = foldli l0"
  unfolding set_iterator_def set_iterator_genord_def
  by auto
 
  show "it (\<lambda>_. True) (\<lambda>x. (\<and>) (\<Union> {the (R y) |y. y \<in> the (R x)} \<subseteq> the (R x))) True =
    (\<forall>q\<in>S. \<Union> {the (R y) |y. y \<in> the (R q)} \<subseteq> the (R q))"
    apply (simp add: l0_def)
    apply (induction l0)
     apply simp
  proof -
    fix a l0
    assume p1 : "foldli l0 (\<lambda>_. True)
        (\<lambda>x. (\<and>) (\<Union> {the (R y) |y. y \<in> the (R x)} \<subseteq> the (R x))) True =
       (\<forall>q\<in>set l0. \<Union> {the (R y) |y. y \<in> the (R q)} \<subseteq> the (R q))"
    show "foldli (a # l0) (\<lambda>_. True)
          (\<lambda>x. (\<and>) (\<Union> {the (R y) |y. y \<in> the (R x)} \<subseteq> the (R x))) True =
         (\<forall>q\<in>set (a # l0). \<Union> {the (R y) |y. y \<in> the (R q)} \<subseteq> the (R q))"
      apply simp
    proof (cases "(\<Union> {the (R y) |y. y \<in> the (R a)} \<subseteq> the (R a))")
    case True
    from this p1
    show "foldli l0 (\<lambda>_. True) (\<lambda>x. (\<and>) (\<Union> {the (R y) |y. y \<in> the (R x)} \<subseteq> the (R x)))
     (\<Union> {the (R y) |y. y \<in> the (R a)} \<subseteq> the (R a)) =
    (\<Union> {the (R y) |y. y \<in> the (R a)} \<subseteq> the (R a) \<and>
     (\<forall>q\<in>set l0. \<Union> {the (R y) |y. y \<in> the (R q)} \<subseteq> the (R q)))" 
      by simp
    next
      case False
      then show "foldli l0 (\<lambda>_. True) (\<lambda>x. (\<and>) (\<Union> {the (R y) |y. y \<in> the (R x)} \<subseteq> the (R x)))
     (\<Union> {the (R y) |y. y \<in> the (R a)} \<subseteq> the (R a)) =
    (\<Union> {the (R y) |y. y \<in> the (R a)} \<subseteq> the (R a) \<and>
     (\<forall>q\<in>set l0. \<Union> {the (R y) |y. y \<in> the (R q)} \<subseteq> the (R q)))" 
        apply simp
        apply (induction l0)
        apply simp
        by simp
    qed
  qed
qed
*)

definition reach_closure_imp  where
 "reach_closure_imp S T \<equiv> do {
  R \<leftarrow> init_closure S T;
  WHILEIT
  (\<lambda> R. dom R = S \<and> (\<Union> (ran R)) \<subseteq> S \<and> 
        (\<forall> q \<in> S. q \<in> the (R q) \<and> (\<forall> q'. (q, q') \<in> T \<longrightarrow> q' \<in> the (R q)) \<and> 
        (\<forall> q' \<in> the (R q). epsilon_reachable q q' T))) 
  (\<lambda> R. \<not> (reach_closed S R)) 
    (\<lambda> R. one_step S R) R}"

definition submap :: "'q set \<Rightarrow> (('q, 'q set) map \<times> ('q, 'q set) map) set" where 
  "submap S = {(R2, R1)| 
                  R1 R2. dom R1 = S \<and> dom R2 = S \<and> 
                  \<Union> (ran R1) \<subseteq> S \<and> \<Union> (ran R2) \<subseteq> S \<and>
                  (\<forall> q \<in> S. the (R1 q) \<subseteq> the (R2 q) \<and> 
                     finite (the (R1 q)) \<and>
                     finite (the (R2 q))) \<and> 
                  (\<exists> q \<in> S. the (R1 q) \<subset> the (R2 q))}"

definition lessmap :: "'q set \<Rightarrow> ('q, 'q set) map \<Rightarrow> nat" where
  "lessmap S R = card S * card S - (\<Sum>q \<in> S.(card (the (R q))))"


lemma wf_submap:
  fixes S
  assumes finite_S: "finite S"
  shows "wf (submap S)"
  apply (unfold submap_def)
  apply (rule wf_measure [THEN wf_subset])
  apply (simp add: measure_def inv_image_def less_than_def less_eq)
  apply (subgoal_tac "{(R2, R1) |R1 R2.
     dom R1 = S \<and>
     dom R2 = S \<and>
     \<Union> (ran R1) \<subseteq> S \<and>
     \<Union> (ran R2) \<subseteq> S \<and>
     (\<forall>q\<in>S. the (R1 q) \<subseteq> the (R2 q) \<and>
             finite (the (R1 q)) \<and> finite (the (R2 q))) \<and>
     (\<exists>q\<in>S. the (R1 q) \<subset> the (R2 q))}
    \<subseteq> {(x, y). lessmap S x < lessmap S y}")
   apply assumption
   unfolding lessmap_def 
proof 
  fix x
  assume xin: "x \<in> {(R2, R1) |R1 R2.
              dom R1 = S \<and>
              dom R2 = S \<and>
              \<Union> (ran R1) \<subseteq> S \<and>
              \<Union> (ran R2) \<subseteq> S \<and>
              (\<forall>q\<in>S. the (R1 q) \<subseteq> the (R2 q) \<and>
                      finite (the (R1 q)) \<and> finite (the (R2 q))) \<and>
              (\<exists>q\<in>S. the (R1 q) \<subset> the (R2 q))}"
  from this obtain R1 R2
    where R1R2_def: "x = (R2,R1) \<and>dom R1 = S \<and>
              dom R2 = S \<and>
              \<Union> (ran R1) \<subseteq> S \<and>
              \<Union> (ran R2) \<subseteq> S \<and>
              (\<forall>q\<in>S. the (R1 q) \<subseteq> the (R2 q) \<and>
              finite (the (R1 q)) \<and> finite (the (R2 q))) \<and>
              (\<exists>q\<in>S. the (R1 q) \<subset> the (R2 q))"
    by auto

  from this 
  have c0:"\<forall> q \<in> S. card (the (R1 q)) \<le> card (the (R2 q))"
    by (simp add: card_mono)

  from R1R2_def 
  have c1:"\<exists> q \<in> S. card (the (R1 q)) < card (the (R2 q))"
    using psubset_card_mono by blast
  from sum_subtractf_nat[of S "\<lambda> q. card (the (R1 q))" 
                              "\<lambda> q. card (the (R2 q))"] c0
  have c2: "(\<Sum>x\<in>S. card (the (R2 x)) - card (the (R1 x))) =
        (\<Sum>x\<in>S. card (the (R2 x))) - (\<Sum>x\<in>S. card (the (R1 x)))"
    by force

  from R1R2_def
  have c3:"(\<Sum>x\<in>S. card (the (R2 x)) - card (the (R1 x))) > 0"
    using c1 finite_S nat_less_le zero_less_diff by auto

  from R1R2_def 
  have con0: "(\<Sum>q\<in>dom R1. card (the (R1 q))) < 
        (\<Sum>q\<in>dom R2. card (the (R2 q)))"
    apply simp
    using c2 c3
    by force

  from R1R2_def ranI
  have "\<forall> q \<in> S. (the (R1 q)) \<subseteq> S"
    unfolding ran_def
    by fastforce

  have c3:"(\<Sum>x\<in>S. card S - card (the (R1 x))) \<ge> 0"
    using c1 finite_S nat_less_le zero_less_diff by auto 

  from R1R2_def this
  have con1: "(\<Sum>q\<in>dom R1. card (the (R1 q))) \<le> (\<Sum>q\<in>dom R1. card S)"
    by (metis \<open>\<forall>q\<in>S. the (R1 q) \<subseteq> S\<close> card_mono finite_S sum_mono)


  from R1R2_def
  have "dom R2 = S \<and> \<Union> (ran R2) \<subseteq> S" by auto
  
  from this ranI
  have "\<forall> q \<in> S. (the (R2 q)) \<subseteq> S"
    unfolding ran_def
    using Sup_le_iff mem_Collect_eq option.sel by fastforce

  have c3:"(\<Sum>x\<in>S. card S - card (the (R2 x))) \<ge> 0"
    using c1 finite_S nat_less_le zero_less_diff by auto 

  from R1R2_def this
  have con2: "(\<Sum>q\<in>dom R2. card (the (R2 q))) \<le> (\<Sum>q\<in>dom R2. card S)"
    by (metis \<open>\<forall>q\<in>S. the (R2 q) \<subseteq> S\<close> card_mono finite_S sum_mono)


  from con1 con2 con0 R1R2_def
  have "(\<Sum>q\<in>S. card S) - (\<Sum>q\<in>dom R2. card (the (R2 q))) <
        (\<Sum>q\<in>S. card S) - (\<Sum>q\<in>dom R1. card (the (R1 q)))"
    by simp
  from this R1R2_def
  have "(card S * card S) - (\<Sum>q\<in>S. card (the (R2 q))) <
        (card S * card S) - (\<Sum>q\<in>S. card (the (R1 q)))"
    by simp
  from this R1R2_def
  show "x \<in> {(x, y).
               card S * card S - (\<Sum>q\<in>S. card (the (x q)))
               < card S * card S - (\<Sum>q\<in>S. card (the (y q)))}"
    by auto
qed

lemma reach_closure_imp_correct:
  fixes S T
  assumes finiteS: "finite S"
      and T_ok: "finite T"
      and ST_ok: "\<forall> (q,q') \<in> T. q \<in> S \<and> q' \<in> S"
    shows "reach_closure_imp S T \<le> 
                  SPEC (\<lambda> P. (\<forall> q q'. dom P = S \<and> (\<Union> (ran P) \<subseteq> S) \<and>
                               (q \<in> S \<longrightarrow> 
                                (epsilon_reachable q q' T = (q' \<in> the (P q))))))"
  unfolding reach_closure_imp_def init_closure_def
  apply (refine_vcg)
  using finiteS apply simp
  apply simp apply force
  defer
  apply (subgoal_tac 
          "\<And>\<sigma>. dom \<sigma> = S - {} \<and> (\<forall>q\<in>S - {}. \<sigma> q = 
            Some {q'. (q, q') \<in> T \<or> q' = q}) \<Longrightarrow> 
        wf ((\<lambda> x. submap S) \<sigma>)")
  apply assumption
  using finiteS wf_submap
  apply force
  apply force 
  using ST_ok 
      defer
proof -
  {
    fix \<sigma> 
    assume \<sigma>_cons: "dom \<sigma> = S - {} \<and> (\<forall>q\<in>S - {}. 
                          \<sigma> q = Some {q'. (q, q') \<in> T \<or> q' = q})"
    show "\<forall>q\<in>S. q \<in> the (\<sigma> q) \<and> (\<forall>q'. (q, q') \<in> T \<longrightarrow> q' \<in> the (\<sigma> q)) \<and>
          (\<forall>q'\<in>the (\<sigma> q). epsilon_reachable q q' T)"
      apply rule
    proof -
      fix q
      assume qin: "q \<in> S"
      show "q \<in> the (\<sigma> q) \<and> (\<forall>q'. (q, q') \<in> T \<longrightarrow> q' \<in> the (\<sigma> q)) \<and>
              (\<forall>q'\<in>the (\<sigma> q). epsilon_reachable q q' T)"
        apply (rule conjI)
        using \<sigma>_cons qin apply force
        apply (rule conjI)
        using \<sigma>_cons 
        apply (simp add: qin)
      proof 
      fix q'
      assume q'in: "q' \<in> the (\<sigma> q)"
    from \<sigma>_cons qin
    have "\<sigma> q = Some {q'. (q, q') \<in> T \<or> q' = q}" by auto
    from this q'in epsilon_reachable_def
    show "epsilon_reachable q q' T"
      by (metis (mono_tags, lifting) epsilon_reach.simps(2) 
           epsilon_reach.simps(3) last_ConsL last_ConsR 
            list.distinct(1) list.sel(1) mem_Collect_eq option.sel)
  qed
qed
}{
  fix \<sigma>
  assume \<sigma>_cons: "dom \<sigma> = S - {} \<and> (\<forall>q\<in>S - {}. \<sigma> q = Some {q'. (q, q') \<in> T \<or> q' = q})"
  from \<sigma>_cons ST_ok
  have "\<forall> q \<in> S. the (\<sigma> q) \<subseteq> S"
    by force
  from this  \<sigma>_cons
  show "\<forall>(q, q')\<in>T. q \<in> S \<and> q' \<in> S \<Longrightarrow> \<Union> (ran \<sigma>) \<subseteq> S"
    unfolding ran_def
    apply simp
  proof 
    fix x
    assume xin: "x \<in> \<Union> {b. \<exists>a. \<sigma> a = Some b}"
       and p1: "dom \<sigma> = S \<and> (\<forall>q\<in>S. \<sigma> q = Some {q'. (q, q') \<in> T \<or> q' = q})"
    from this
    obtain a b where 
    a_def: "\<sigma> a = Some b \<and> x \<in> b "
      by blast
    from this p1
    have "a \<in> S" by blast
    from this p1
    have "b \<subseteq> S \<and> b = {q'. (a, q') \<in> T \<or> q' = a}"
      using \<open>\<forall>q\<in>S. the (\<sigma> q) \<subseteq> S\<close> a_def by auto
    from this a_def ST_ok
    show "x \<in> S"
      by auto
  qed
}
  {
    fix x it \<sigma>
    assume xin: "x \<in> it"
       and itin: "it \<subseteq> {q. q \<in> S}"
       and \<sigma>_cons: "dom \<sigma> = S - it \<and> 
                      (\<forall>q\<in>S - it. \<sigma> q = Some {q'. (q, q') \<in> T \<or> q' = q})"
    thm init_state_correct[of T x, OF T_ok]
    have c1: "SPEC (\<lambda>S. S = {q'. (x, q') \<in> T \<or> q' = x}) \<le> 
          SPEC (\<lambda>onestep.
                insert x (dom \<sigma>) = S - (it - {x}) \<and>
                (\<forall>q\<in>S - (it - {x}).
                    (q = x \<longrightarrow> onestep = {q'. (x, q') \<in> T \<or> q' = x}) \<and>
                    (q \<noteq> x \<longrightarrow> \<sigma> q = Some {q'. (q, q') \<in> T \<or> q' = q})))"
      apply simp
      apply (rule conjI)
      using xin itin \<sigma>_cons
      apply force
      using xin itin \<sigma>_cons
      by force
    
    show "init_state x T
              \<le> SPEC (\<lambda>onestep.
                   RETURN (\<sigma>(x \<mapsto> onestep))
                   \<le> SPEC (\<lambda>P. dom P = S - (it - {x}) \<and>
                                (\<forall>q\<in>S - (it - {x}).
                                    P q = Some {q'. (q, q') \<in> T \<or> q' = q})))"
      apply simp
      using c1 init_state_correct[of T x, OF T_ok]
      using SPEC_trans by blast
  }
  {
    fix \<sigma> s
    assume \<sigma>_cons: "dom \<sigma> = S - {} \<and> (\<forall>q\<in>S - {}. 
              \<sigma> q = Some {q'. (q, q') \<in> T \<or> q' = q})"
       and epsilo: "dom s = S \<and>
           \<Union> (ran s) \<subseteq> S \<and> (\<forall>q\<in>S. q \<in> the (s q) \<and> 
                          (\<forall>q'. (q, q') \<in> T \<longrightarrow> q' \<in> the (s q)) \<and>
                              (\<forall>q'\<in>the (s q). epsilon_reachable q q' T))"
       and reachclose: "\<not> reach_closed S s"

    from epsilo finiteS
    have cc1: "\<forall>s\<in>ran s. finite s" 
      by (meson Sup_upper infinite_super)

    from one_step_correct[of S s, OF finiteS] epsilo cc1
    have c1: "one_step S s \<le> SPEC (\<lambda>P'. dom P' = S \<and> \<Union> (ran P') \<subseteq> S \<and>
                          (\<forall>q\<in>S. the (P' q) =
                            \<Union> {the (s q') |q'. q' \<in> the (s q)} \<union> the (s q)))"
      by auto
    from one_step_correct'[of S s T, OF finiteS] epsilo cc1
    have c2: "one_step S s \<le> SPEC (\<lambda>P'. dom P' = S \<and>
                      \<Union> (ran P') \<subseteq> S \<and> (\<forall>q\<in>S. \<forall>q'\<in>the (P' q). 
                            epsilon_reachable q q' T))"
      by auto

    from c1 c2
    have onestep_com: "one_step S s \<le> SPEC (\<lambda>P'. dom P' = S \<and>
                      \<Union> (ran P') \<subseteq> S \<and> 
              (\<forall>q\<in>S. the (P' q) = \<Union> {the (s q') |q'. q' \<in> the (s q)} \<union> the (s q)) \<and>
              (\<forall>q\<in>S. \<forall>q'\<in>the (P' q). epsilon_reachable q q' T))"
      by (auto simp: pw_le_iff refine_pw_simps)
  

    have "SPEC (\<lambda>P'. dom P' = S \<and>
                      \<Union> (ran P') \<subseteq> S \<and> 
              (\<forall>q\<in>S. the (P' q) = \<Union> {the (s q') |q'. q' \<in> the (s q)} \<union> the (s q)) \<and>
              (\<forall>q\<in>S. \<forall>q'\<in>the (P' q). epsilon_reachable q q' T)) \<le> 
          SPEC (\<lambda>s'. (dom s' = S \<and>
                          \<Union> (ran s') \<subseteq> S \<and>
                          (\<forall>q\<in>S. q \<in> the (s' q) \<and> 
                            (\<forall>q'. (q, q') \<in> T \<longrightarrow> q' \<in> the (s' q)) \<and> (\<forall>q'\<in>the (s' q). epsilon_reachable q q' T)) \<and>
                         (s', s) \<in> submap S))"
      apply simp
      apply rule
    proof 
      fix x
      assume xin: "x \<in> {P'. dom P' = S \<and>
                  \<Union> (ran P') \<subseteq> S \<and>
                  (\<forall>q\<in>S. the (P' q) =
                          \<Union> {the (s q') |q'. q' \<in> the (s q)} \<union> the (s q)) \<and>
                  (\<forall>q\<in>S. \<forall>q'\<in>the (P' q). epsilon_reachable q q' T)}"
      from this 
      have xin': "dom x = S \<and>
                  \<Union> (ran x) \<subseteq> S \<and>
                  (\<forall>q\<in>S. the (x q) =
                         \<Union> {the (s q') |q'. q' \<in> the (s q)} \<union> the (s q))\<and>
                  (\<forall>q\<in>S. \<forall>q'\<in>the (x q). epsilon_reachable q q' T)" by auto

      from epsilo finiteS ranI
      have s_finite: "\<forall> q \<in> S. finite (the (s q))"
        unfolding ran_def
        by (simp add: cc1 domD ranI)

      from this epsilo finiteS ranI
      have x_finite: "\<forall> q \<in> S. finite (the (x q))"
        unfolding ran_def
        using Sup_le_iff cc1 domD option.sel ranI rev_finite_subset xin
      proof -
        show ?thesis
          by (metis \<open>\<And>B A. \<lbrakk>finite B; A \<subseteq> B\<rbrakk> \<Longrightarrow> finite A\<close> 
                    \<open>\<And>b A. (Sup A \<le> b) = (\<forall>a\<in>A. a \<le> b)\<close> 
                    \<open>\<And>m a. a \<in> dom m \<Longrightarrow> \<exists>b. m a = Some b\<close> 
                    \<open>\<And>m b a. m a = Some b \<Longrightarrow> b \<in> ran m\<close> 
                    \<open>\<And>x2. the (Some x2) = x2\<close> finiteS xin')
      qed

      from reach_closed_correct[of ]
      have "(x, s) \<in> submap S"
        unfolding submap_def
        apply simp
        apply (rule_tac conjI)
        using epsilo apply simp
        apply (rule_tac conjI)
        using xin' apply simp
        apply (rule_tac conjI)
        using epsilo apply simp
        apply (rule_tac conjI)
        using xin' apply simp
        apply (rule_tac conjI)
        using  x_finite s_finite xin'
         apply simp
      proof -
        from reachclose epsilo 
        obtain q where
        q_def: "\<not> (\<Union> {the (s y) |y. y \<in> the (s q)} \<subseteq> the (s q)) \<and> q \<in> S"
          unfolding reach_closed_def
          by auto
        from this xin'
        show "\<exists>q\<in>S. the (s q) \<subset> the (x q)"
          by auto
      qed
      from this xin' epsilo
      show "dom x = S \<and>
         \<Union> (ran x) \<subseteq> S \<and>
         (\<forall>q\<in>S. q \<in> the (x q) \<and> (\<forall>q'. (q, q') \<in> T \<longrightarrow> q' \<in> the (x q)) \<and>
            (\<forall>q'\<in>the (x q). epsilon_reachable q q' T)) \<and> (x, s) \<in> submap S"
        by auto
    qed
    from this onestep_com
    show "one_step S s
           \<le> SPEC (\<lambda>s'. (dom s' = S \<and>
                          \<Union> (ran s') \<subseteq> S \<and>
                          (\<forall>q\<in>S. q \<in> the (s' q) \<and> 
              (\<forall>q'. (q, q') \<in> T \<longrightarrow> q' \<in> the (s' q)) \<and>
                    (\<forall>q'\<in>the (s' q). epsilon_reachable q q' T))) \<and>
                         (s', s) \<in> submap S)"
      apply simp
      by (simp add: SPEC_trans)
      
  }
  {
    fix \<sigma> s q q'
    assume p1: "dom s = S \<and>
       \<Union> (ran s) \<subseteq> S \<and> (\<forall>q\<in>S. q \<in> the (s q) \<and> (\<forall>q'. (q, q') \<in> T \<longrightarrow> q' \<in> the (s q)) \<and> (\<forall>q'\<in>the (s q). epsilon_reachable q q' T))"
    then show "dom s = S"
      by auto
  }
  {
    fix \<sigma> s q q'
    assume "dom s = S \<and>
       \<Union> (ran s) \<subseteq> S \<and> (\<forall>q\<in>S. q \<in> the (s q) \<and> (\<forall>q'. (q, q') \<in> T \<longrightarrow> q' \<in> the (s q)) \<and>
        (\<forall>q'\<in>the (s q). epsilon_reachable q q' T))"
    then show "\<Union> (ran s) \<subseteq> S"
      by auto
  }
  {
    fix \<sigma> s q q'
    assume dom\<sigma>: "dom \<sigma> = S - {} \<and> (\<forall>q\<in>S - {}. 
                  \<sigma> q = Some {q'. (q, q') \<in> T \<or> q' = q})"
       and s_cons: "dom s = S \<and>
       \<Union> (ran s) \<subseteq> S \<and> (\<forall>q\<in>S. q \<in> the (s q) \<and> 
         (\<forall>q'. (q, q') \<in> T \<longrightarrow> q' \<in> the (s q)) \<and>
         (\<forall>q'\<in>the (s q). epsilon_reachable q q' T))"
       and reachClose: "\<not> \<not> reach_closed S s"
       and qin: "q \<in> S"
    from s_cons qin
    have nextcons: "(\<forall> q \<in> S. \<forall>q'. (q, q') \<in> T \<longrightarrow> q' \<in> the (s q))"
      by force
    from reachClose reach_closed_correct[OF , of s] s_cons
    have subset_s: "\<forall> q \<in> S. \<Union> {the (s y) |y. y \<in> the (s q)} \<subseteq> the (s q)" 
      by auto
    show "epsilon_reachable q q' T = (q' \<in> the (s q))"
    proof 
      {
        assume q'in: "q' \<in> the (s q) "
        from this s_cons qin
        show "epsilon_reachable q q' T"
          by auto
      }
      {
        assume reach: "epsilon_reachable q q' T"
        from this epsilon_reachable_def[of q q' T]
        obtain l where 
        l_def: "l \<noteq> [] \<and> epsilon_reach l T \<and> hd l = q \<and> last l = q'"
          by auto
        from this qin ST_ok nextcons
        show "q' \<in> the (s q)"
          apply (induction l T arbitrary:  q rule: epsilon_reach.induct)
          apply simp
          using s_cons apply simp apply blast
        proof -
          fix q1 q2 l D q
          assume ind_hyp: "(\<And>q. q2 # l \<noteq> [] \<and>
             epsilon_reach (q2 # l) D \<and> hd (q2 # l) = q \<and> 
             last (q2 # l) = q' \<Longrightarrow> q \<in> S \<Longrightarrow> \<forall>(q, q')\<in>D. q \<in> S \<and> q' \<in> S 
              \<Longrightarrow> \<forall>q\<in>S. \<forall>q'. (q, q') \<in> D \<longrightarrow> q' \<in> the (s q)\<Longrightarrow> q' \<in> the (s q))"
             and pre: "q1 # q2 # l \<noteq> [] \<and> epsilon_reach (q1 # q2 # l) D \<and>
                        hd (q1 # q2 # l) = q \<and> last (q1 # q2 # l) = q'"
             and qinS: "q \<in> S"
             and inS: "\<forall>(q, q')\<in>D. q \<in> S \<and> q' \<in> S"
             and qinsq: "\<forall>q\<in>S. \<forall>q'. (q, q') \<in> D \<longrightarrow> q' \<in> the (s q)"
          from this
          have pre': "q2 # l \<noteq> [] \<and> epsilon_reach (q2 # l) D \<and> 
                hd (q2 # l) = q2 \<and> last (q2 # l) = q'"
            by force
          from pre
          have qq1eq: "q = q1" by auto
          from this pre inS
          have q12D: "(q1,q2) \<in> D" by auto
          from this inS
          have q2inS: "q2 \<in> S" by auto
          from qinsq qq1eq q12D qinS
          have "q2 \<in> the (s q)" by auto
          from this ind_hyp[of q2, OF pre' q2inS inS qinsq]
               subset_s qinS
          show "q' \<in> the (s q)"
            by auto
        qed
      }
    qed
  }
qed

definition compute_ep_I where 
     "compute_ep_I I P = 
      FOREACHi (\<lambda> S R. R = {q' | q q'. q \<in> I - S 
                             \<and> P q \<noteq> None \<and> q' \<in> (the (P q))}) I 
           (\<lambda> q NI. if P q = None then RETURN NI else
                    RETURN (NI \<union> (the (P q)))
      ) {}"

lemma compute_eq_I_correct:
  fixes I Q P
  assumes finite_I: "finite I"
  shows "compute_ep_I I P \<le> 
          SPEC (\<lambda> NI. NI = {q' | q q'. q \<in> I \<and>
                                       P q \<noteq> None \<and> q' \<in> (the (P q))})"
  unfolding compute_ep_I_def
  apply (refine_vcg)
  using finite_I apply simp
  apply simp
  apply force
  apply fastforce
  by force

definition compute_ep_F where 
     "compute_ep_F F Q P = 
      FOREACHi (\<lambda> S R. R = {q' | q q'. q \<in> F - S \<and> q' \<in> Q
                             \<and> q \<in> (the (P q'))}) F (\<lambda> q NI. do {
            TI \<leftarrow> (FOREACHi 
                    (\<lambda> Q1 RQ. RQ = {q' | q'. q' \<in> Q - Q1 \<and> q \<in> (the (P q'))}) 
                      Q (\<lambda> q' NII. 
                        if q \<in> the (P q') then RETURN (NII \<union> {q'}) 
                        else RETURN NII) {});
            RETURN (TI \<union> NI)
          }
      ) {}"

lemma compute_eq_F_correct:
  fixes F Q P
  assumes finite_I: "finite F"
      and finite_Q: "finite Q"
  shows "compute_ep_F F Q P \<le> 
          SPEC (\<lambda> NI. NI = {q' | q q'. q \<in> F \<and> q' \<in> Q 
                                      \<and> q \<in> (the (P q'))})"
  unfolding compute_ep_F_def
  apply (refine_vcg)
  using finite_I apply simp
  apply simp
  using finite_Q apply simp
  by force+


definition compute_ep_Trans where 
     "compute_ep_Trans Tran Q P = 
      FOREACHi (\<lambda> T T'. T' = {(q'', \<alpha>, q') | q \<alpha> q' q''. 
                                (q, \<alpha>, q') \<in> Tran - T \<and> q'' \<in> Q \<and> P q'' \<noteq> None
                                     \<and> q \<in> (the (P q''))})
         Tran (\<lambda> (q, \<alpha>, q') NI. do {
            TI \<leftarrow> (FOREACHi (\<lambda> Q' TT. TT = {(q1, \<alpha>, q') 
                              | q1. q1 \<in> Q - Q' \<and> q \<in> the (P q1)})
                  Q (\<lambda> q'' NII. 
                        if q \<in> the (P q'') then RETURN (NII \<union> {(q'', \<alpha> ,q')}) 
                        else RETURN NII) {});
            RETURN (TI \<union> NI)
          }
      ) {}"

lemma compute_eq_Trans_correct:
  fixes Tran P Q
  assumes finite_Tran: "finite Tran \<and> 
                        (\<forall> q a q'. (q, a, q') \<in> Tran \<longrightarrow> q \<in> Q \<and> q' \<in> Q)"
      and P_ok: "dom P = Q"
      and finite_Q: "finite Q"
      and P_correct: "\<forall> x. P x \<noteq> None \<longrightarrow> finite (the (P x))"
  shows "compute_ep_Trans Tran Q P \<le> 
          SPEC (\<lambda> T. T = {(q, \<alpha>, q'') | q \<alpha> q' q''. (q', \<alpha>, q'') \<in> Tran \<and> q \<in> Q
                                                    \<and> P q \<noteq> None \<and> q' \<in> (the (P q))})"
  unfolding compute_ep_Trans_def
  apply (refine_vcg)
  using finite_Tran apply force
  apply force
  using finite_Q apply force
  using P_correct apply force
  apply force
  apply fastforce
  defer
  apply force
proof -
  fix x it \<sigma> x1 x2 x1a x2a \<sigma>'
  assume xin: "x \<in> it"
     and itin: "it \<subseteq> Tran"
     and \<sigma>_def: "\<sigma> =
       {uu.
        \<exists>q \<alpha> q' q''.
           uu = (q'', \<alpha>, q') \<and>
           (q, \<alpha>, q') \<in> Tran - it \<and> q'' \<in> Q \<and> P q'' \<noteq> None \<and> q \<in> the (P q'')}"
     and x2_def: "x2 = (x1a, x2a)"
     and x_def: "x = (x1, x2)"
     and \<sigma>'_def: "\<sigma>' = {(q1, x1a, x2a) |q1. q1 \<in> Q - {} \<and> x1 \<in> the (P q1)} "
  show "\<sigma>' \<union> \<sigma> =
       {uu.
        \<exists>q \<alpha> q' q''.
           uu = (q'', \<alpha>, q') \<and>
           (q, \<alpha>, q') \<in> Tran - (it - {x}) \<and> q'' \<in> Q \<and> P q'' \<noteq> None \<and> q \<in> the (P q'')}"
    apply (rule)
    apply (rule)
    defer
    apply (rule)
  proof -
    {
      fix xa 
      assume xain: " xa \<in> {uu. \<exists>q \<alpha> q' q''.
                       uu = (q'', \<alpha>, q') \<and>
                       (q, \<alpha>, q') \<in> Tran - (it - {x}) \<and>
                       q'' \<in> Q \<and> P q'' \<noteq> None \<and> q \<in> the (P q'')}"
      from this obtain q \<alpha> q' q''
        where xa_def: "xa = (q'', \<alpha>, q') \<and>
                       (q, \<alpha>, q') \<in> Tran - (it - {x}) \<and>
                       q'' \<in> Q \<and> P q'' \<noteq> None \<and> q \<in> the (P q'')" by force
      have branch: "Tran - (it - {x}) = (Tran - it) \<union> {x}" 
        by (simp add: it_step_insert_iff itin xin)
      show "xa \<in> \<sigma>' \<union> \<sigma>"
      proof (cases "(q, \<alpha>, q') \<in> (Tran - it)")
        case True
        then show ?thesis 
          using \<sigma>_def xa_def by blast
        next
          case False
          from this branch have "(q, \<alpha>, q') = x" 
            using xa_def by blast
        then show ?thesis 
          using \<sigma>'_def x2_def x_def xa_def finite_Tran
          by auto
        qed
      }
      {
        fix xa
        assume xain: "xa \<in> \<sigma>' \<union> \<sigma>"
         
        have branch: "Tran - (it - {x}) = (Tran - it) \<union> {x}"
          by (simp add: it_step_insert_iff itin xin)

        show "xa \<in> {uu. \<exists>q \<alpha> q' q''.
                        uu = (q'', \<alpha>, q') \<and>
                        (q, \<alpha>, q') \<in> Tran - (it - {x}) \<and>
                        q'' \<in> Q \<and> P q'' \<noteq> None \<and> q \<in> the (P q'')}"
        proof (cases "xa \<in> \<sigma>'")
          case True
          from this \<sigma>'_def
          obtain q1 where
              q1_def: "xa = (q1, x1a, x2a) \<and> q1 \<in> Q - {} \<and> x1 \<in> the (P q1)" by auto
          from this P_ok have "P q1 \<noteq> None" 
            by blast
          from this x_def q1_def x2_def
          show ?thesis 
            using  branch 
            using P_ok finite_Tran by blast
          next
            case False
            from this branch \<sigma>_def
            obtain q \<alpha> q' q'' where 
        xa_def: "xa = (q'', \<alpha>, q') \<and> (q, \<alpha>, q') \<in> Tran - it \<and> q'' \<in> Q \<and>
                  P q'' \<noteq> None \<and> q \<in> the (P q'')" 
              using xain by blast
          then show ?thesis 
            by blast
          qed
        }
      qed
    qed


definition NFA_elim_Impl ::"('q, 'a) NFAe_rec
        \<Rightarrow> ('q, 'a) NFA_rec nres" where 
     "NFA_elim_Impl A = do {
       P \<leftarrow> reach_closure_imp (\<Q>e A) (\<Delta>e' A);
       N\<Delta> \<leftarrow> (compute_ep_Trans (\<Delta>e A) (\<Q>e A) P);
       N\<I> \<leftarrow>  compute_ep_I (\<I>e A) P;
       N\<F> \<leftarrow>  compute_ep_F (\<F>e A) (\<Q>e A) P;
       RETURN \<lparr> \<Q> = \<Q>e A, 
                \<Sigma> = \<Sigma>e A, 
                \<Delta> = (\<Delta>e A) \<union> N\<Delta>, 
                \<I> = (\<I>e A) \<union> N\<I>, 
                \<F> = (\<F>e A) \<union> N\<F> \<rparr>
     }"

lemma NFA_elim_impl_correct:
  fixes \<A>e
  assumes wfA: "NFAe \<A>e"
      and finite\<Delta>A: "finite (\<Delta>e' \<A>e) \<and> finite (\<Delta>e \<A>e)"
  shows "NFA_elim_Impl \<A>e \<le> 
          SPEC (\<lambda> \<A>. \<A> = epsilon_elim \<A>e)"
  unfolding NFA_elim_Impl_def 
  apply (refine_vcg)
proof -
  from reach_closure_imp_correct[of "\<Q>e \<A>e" "\<Delta>e' \<A>e" ] wfA
  have c1: "reach_closure_imp (\<Q>e \<A>e) (\<Delta>e' \<A>e)
        \<le> SPEC (\<lambda>P. \<forall>q q'. dom P = \<Q>e \<A>e \<and>
                    \<Union> (ran P) \<subseteq> \<Q>e \<A>e \<and>
                    (q \<in> \<Q>e \<A>e \<longrightarrow>
                     epsilon_reachable q q' (\<Delta>e' \<A>e) = (q' \<in> the (P q))))"
    unfolding NFAe_def
    using finite\<Delta>A 
    by blast

  have "SPEC (\<lambda>P. \<forall>q q'. dom P = \<Q>e \<A>e \<and>
                    \<Union> (ran P) \<subseteq> \<Q>e \<A>e \<and>
                    (q \<in> \<Q>e \<A>e \<longrightarrow>
                     epsilon_reachable q q' (\<Delta>e' \<A>e) = (q' \<in> the (P q)))) \<le>
        SPEC (\<lambda>P. compute_ep_Trans (\<Delta>e \<A>e) (\<Q>e \<A>e) P \<bind>
                 (\<lambda>N\<Delta>. compute_ep_I (\<I>e \<A>e) P \<bind>
                        (\<lambda>N\<I>. compute_ep_F (\<F>e \<A>e) (\<Q>e \<A>e) P \<bind>
                              (\<lambda>N\<F>. RETURN
                                      \<lparr>\<Q> = \<Q>e \<A>e, \<Sigma> = \<Sigma>e \<A>e, \<Delta> = \<Delta>e \<A>e \<union> N\<Delta>,
                                         \<I> = \<I>e \<A>e \<union> N\<I>, \<F> = \<F>e \<A>e \<union> N\<F>\<rparr>)))
                 \<le> SPEC (\<lambda>\<A>. \<A> = epsilon_elim \<A>e))"
    apply simp
    apply rule
  proof 
    fix x
    assume xin: "x \<in> {P. dom P = \<Q>e \<A>e \<and>
                 \<Union> (ran P) \<subseteq> \<Q>e \<A>e \<and>
                 (\<forall>q. q \<in> \<Q>e \<A>e \<longrightarrow>
                      (\<forall>q'. epsilon_reachable q q' (\<Delta>e' \<A>e) = (q' \<in> the (P q))))}"
    from this 
    have xin': "dom x = \<Q>e \<A>e \<and>
                 \<Union> (ran x) \<subseteq> \<Q>e \<A>e \<and>
                 (\<forall>q. q \<in> \<Q>e \<A>e \<longrightarrow>
                      (\<forall>q'. epsilon_reachable q q' (\<Delta>e' \<A>e) = (q' \<in> the (x q))))"
      by auto
    thm this wfA NFAe_def
    have b1: "\<forall>xa. x xa \<noteq> None \<longrightarrow> finite (the (x xa))"
      apply (rule allI impI)
    proof 
      fix xa
      assume p1: "x xa \<noteq> None"
      from this have "\<exists> S. x xa = Some S" by auto
      from this obtain S where S_def: "x xa = Some S" by auto
      from this xin' wfA NFAe_def
      show "finite (the (x xa))"
        by (metis Sup_le_iff finite_subset option.sel ranI)
    qed
    from this wfA NFAe_def[of \<A>e] finite\<Delta>A
    have "finite (\<Delta>e \<A>e) \<and> (\<forall>q a q'. (q, a, q') \<in> \<Delta>e \<A>e \<longrightarrow> q \<in> \<Q>e \<A>e \<and> q' \<in> \<Q>e \<A>e)
          \<and> finite (\<Q>e \<A>e)"
      by auto
    
    from b1 xin' compute_eq_Trans_correct[of "\<Delta>e \<A>e" "\<Q>e \<A>e" x] this
    have cc1: "compute_ep_Trans (\<Delta>e \<A>e) (\<Q>e \<A>e) x
               \<le> SPEC (\<lambda>T. T = {uu.
                      \<exists>q \<alpha> q' q''.
                         uu = (q, \<alpha>, q'') \<and>
                         (q', \<alpha>, q'') \<in> \<Delta>e \<A>e \<and>
                         q \<in> \<Q>e \<A>e \<and> x q \<noteq> None \<and> q' \<in> the (x q)})"
      by auto

    from wfA NFAe_def[of \<A>e]
    have "finite (\<I>e \<A>e)"
      using infinite_super by blast

    from compute_eq_I_correct[of "\<I>e \<A>e" x] this
    have cc2: "compute_ep_I (\<I>e \<A>e) x
            \<le> SPEC (\<lambda>NI. NI = {uu. \<exists>q q'. uu = q' \<and> q \<in> \<I>e \<A>e \<and> 
                                x q \<noteq> None \<and> q' \<in> the (x q)})"
      by auto

    from wfA NFAe_def[of \<A>e]
    have "finite (\<F>e \<A>e) \<and> finite (\<Q>e \<A>e)" 
      using infinite_super by blast
    
    from this compute_eq_F_correct[of "(\<F>e \<A>e)" "(\<Q>e \<A>e)" x]
    have cc3: "compute_ep_F (\<F>e \<A>e) (\<Q>e \<A>e) x \<le> SPEC (\<lambda>NI. NI =
                {uu. \<exists>q q'. uu = q' \<and> q \<in> \<F>e \<A>e \<and> q' \<in> \<Q>e \<A>e \<and> q \<in> the (x q')})"
      by auto

    have "compute_ep_Trans (\<Delta>e \<A>e) (\<Q>e \<A>e) x \<bind>
         (\<lambda>N\<Delta>. compute_ep_I (\<I>e \<A>e) x \<bind>
                (\<lambda>N\<I>. compute_ep_F (\<F>e \<A>e) (\<Q>e \<A>e) x \<bind>
                      (\<lambda>N\<F>. RETURN
                              \<lparr>\<Q> = \<Q>e \<A>e, \<Sigma> = \<Sigma>e \<A>e, \<Delta> = \<Delta>e \<A>e \<union> N\<Delta>,
                                 \<I> = \<I>e \<A>e \<union> N\<I>, \<F> = \<F>e \<A>e \<union> N\<F>\<rparr>)))
         \<le> SPEC (\<lambda>\<A>. \<A> = epsilon_elim \<A>e)"
      apply (refine_vcg)
    proof -
      have "SPEC (\<lambda>T. T = {uu.
                      \<exists>q \<alpha> q' q''.
                         uu = (q, \<alpha>, q'') \<and>
                         (q', \<alpha>, q'') \<in> \<Delta>e \<A>e \<and>
                         q \<in> \<Q>e \<A>e \<and> x q \<noteq> None \<and> q' \<in> the (x q)}) \<le> 
            SPEC (\<lambda>N\<Delta>. compute_ep_I (\<I>e \<A>e) x \<bind>
                  (\<lambda>N\<I>. compute_ep_F (\<F>e \<A>e) (\<Q>e \<A>e) x \<bind>
                        (\<lambda>N\<F>. RETURN
                                \<lparr>\<Q> = \<Q>e \<A>e, \<Sigma> = \<Sigma>e \<A>e, \<Delta> = \<Delta>e \<A>e \<union> N\<Delta>,
                                   \<I> = \<I>e \<A>e \<union> N\<I>, \<F> = \<F>e \<A>e \<union> N\<F>\<rparr>))
                  \<le> SPEC (\<lambda>\<A>. \<A> = epsilon_elim \<A>e))"
        apply simp
      proof -
        have "compute_ep_I (\<I>e \<A>e) x \<bind>
    (\<lambda>N\<I>. compute_ep_F (\<F>e \<A>e) (\<Q>e \<A>e) x \<bind>
          (\<lambda>N\<F>. RETURN
                  \<lparr>\<Q> = \<Q>e \<A>e, \<Sigma> = \<Sigma>e \<A>e,
                     \<Delta> = \<Delta>e \<A>e \<union>
                          {uu.
                           \<exists>q \<alpha> q' q''.
                              uu = (q, \<alpha>, q'') \<and>
                              (q', \<alpha>, q'') \<in> \<Delta>e \<A>e \<and>
                              q \<in> \<Q>e \<A>e \<and> (\<exists>y. x q = Some y) \<and> q' \<in> the (x q)},
                     \<I> = \<I>e \<A>e \<union> N\<I>, \<F> = \<F>e \<A>e \<union> N\<F>\<rparr>))
            \<le>SPEC (\<lambda>\<A>. \<A> = epsilon_elim \<A>e)"
          apply (refine_vcg)
        proof -
          from cc2
          have "SPEC (\<lambda>NI. NI = {uu. \<exists>q q'. uu = q' \<and> q \<in> \<I>e \<A>e 
                           \<and> x q \<noteq> None \<and> q' \<in> the (x q)}) \<le> 
               SPEC (\<lambda>N\<I>. compute_ep_F (\<F>e \<A>e) (\<Q>e \<A>e) x \<bind>
                  (\<lambda>N\<F>. RETURN
                          \<lparr>\<Q> = \<Q>e \<A>e, \<Sigma> = \<Sigma>e \<A>e,
                             \<Delta> = \<Delta>e \<A>e \<union>
                                  {uu.
                                   \<exists>q \<alpha> q' q''.
                                      uu = (q, \<alpha>, q'') \<and>
                                      (q', \<alpha>, q'') \<in> \<Delta>e \<A>e \<and>
                                      q \<in> \<Q>e \<A>e \<and>
                                      (\<exists>y. x q = Some y) \<and> q' \<in> the (x q)},
                             \<I> = \<I>e \<A>e \<union> N\<I>, \<F> = \<F>e \<A>e \<union> N\<F>\<rparr>)
                  \<le> SPEC (\<lambda>\<A>. \<A> = epsilon_elim \<A>e))"
            apply simp
          proof -
            have "compute_ep_F (\<F>e \<A>e) (\<Q>e \<A>e) x \<bind>
    (\<lambda>N\<F>. RETURN
            \<lparr>\<Q> = \<Q>e \<A>e, \<Sigma> = \<Sigma>e \<A>e,
               \<Delta> = \<Delta>e \<A>e \<union>
                    {uu.
                     \<exists>q \<alpha> q' q''.
                        uu = (q, \<alpha>, q'') \<and>
                        (q', \<alpha>, q'') \<in> \<Delta>e \<A>e \<and>
                        q \<in> \<Q>e \<A>e \<and> (\<exists>y. x q = Some y) \<and> q' \<in> the (x q)},
               \<I> = \<I>e \<A>e \<union> {uu. \<exists>q. q \<in> \<I>e \<A>e \<and> (\<exists>y. x q = Some y) \<and> uu \<in> the (x q)},
               \<F> = \<F>e \<A>e \<union> N\<F>\<rparr>)
    \<le> SPEC (\<lambda>\<A>. \<A> = epsilon_elim \<A>e)"
              apply (refine_vcg)
            proof -
              
              have "SPEC (\<lambda>NI. NI = {uu. \<exists>q q'. uu = q' \<and> q \<in> \<F>e \<A>e \<and> 
                     q' \<in> \<Q>e \<A>e \<and> q \<in> the (x q')}) \<le> SPEC (\<lambda>N\<F>. RETURN
                   \<lparr>\<Q> = \<Q>e \<A>e, \<Sigma> = \<Sigma>e \<A>e,
                      \<Delta> = \<Delta>e \<A>e \<union>
                           {uu.
                            \<exists>q \<alpha> q' q''.
                               uu = (q, \<alpha>, q'') \<and>
                               (q', \<alpha>, q'') \<in> \<Delta>e \<A>e \<and>
                               q \<in> \<Q>e \<A>e \<and> (\<exists>y. x q = Some y) \<and> q' \<in> the (x q)},
                      \<I> = \<I>e \<A>e \<union>
                          {uu. \<exists>q. q \<in> \<I>e \<A>e \<and> (\<exists>y. x q = Some y) \<and> uu \<in> the (x q)},
                      \<F> = \<F>e \<A>e \<union> N\<F>\<rparr>
                  \<le> SPEC (\<lambda>\<A>. \<A> = epsilon_elim \<A>e))"
                apply simp
                unfolding epsilon_elim_def
                using xin'
                apply simp
              proof -
                assume p1: " dom x = \<Q>e \<A>e \<and>  \<Union> (ran x) \<subseteq> \<Q>e \<A>e \<and>
                              (\<forall>q. q \<in> \<Q>e \<A>e \<longrightarrow> 
                                  (\<forall>q'. epsilon_reachable q q' (\<Delta>e' \<A>e) = 
                                     (q' \<in> the (x q))))"
                have xqnotNone:"\<forall> q. q \<in> \<Q>e \<A>e \<longrightarrow> x q \<noteq> None"
                  apply (rule allI impI) +
                proof -
                  fix q
                  assume qin: "q \<in> \<Q>e \<A>e"
                  from p1 this
                  have exeq: "(epsilon_reachable q q (\<Delta>e' \<A>e) = 
                                     (q \<in> the (x q)))"
                    by auto
                  have "epsilon_reachable q q (\<Delta>e' \<A>e)"
                    unfolding epsilon_reachable_def 
                    by force
                  from exeq this
                  have "q \<in> the (x q)"
                    by auto
                  from this
                  show xqnotNone: "x q \<noteq> None"
                    using qin xin' by blast
                qed
                from this p1
                show "\<Delta>e \<A>e \<union>
    {uu.
     \<exists>q \<alpha> q' q''.
        uu = (q, \<alpha>, q'') \<and>
        (q', \<alpha>, q'') \<in> \<Delta>e \<A>e \<and> q \<in> \<Q>e \<A>e \<and> (\<exists>y. x q = Some y) \<and> q' \<in> the (x q)} =
    \<Delta>e \<A>e \<union>
    {uu.
     \<exists>q \<alpha> q' q''.
        uu = (q, \<alpha>, q'') \<and>
        epsilon_reachable q q' (\<Delta>e' \<A>e) \<and> (q', \<alpha>, q'') \<in> \<Delta>e \<A>e} \<and>
    \<I>e \<A>e \<union> {uu. \<exists>q. q \<in> \<I>e \<A>e \<and> (\<exists>y. x q = Some y) \<and> uu \<in> the (x q)} =
    \<I>e \<A>e \<union> {uu. \<exists>q. epsilon_reachable q uu (\<Delta>e' \<A>e) \<and> q \<in> \<I>e \<A>e} \<and>
    \<F>e \<A>e \<union> {uu. \<exists>q. q \<in> \<F>e \<A>e \<and> uu \<in> \<Q>e \<A>e \<and> q \<in> the (x uu)} =
    \<F>e \<A>e \<union> {uu. \<exists>q'. epsilon_reachable uu q' (\<Delta>e' \<A>e) \<and> q' \<in> \<F>e \<A>e}"
                using wfA NFAe_def[of "\<A>e"] 
                apply (rule_tac conjI)
              proof - 
                {
                  have "{uu.
     \<exists>q \<alpha> q' q''.
        uu = (q, \<alpha>, q'') \<and>
        (q', \<alpha>, q'') \<in> \<Delta>e \<A>e \<and> q \<in> \<Q>e \<A>e \<and> (\<exists>y. x q = Some y) \<and> q' \<in> the (x q)} = {uu.
     \<exists>q \<alpha> q' q''.
        uu = (q, \<alpha>, q'') \<and> epsilon_reachable q q' (\<Delta>e' \<A>e) \<and> (q', \<alpha>, q'') \<in> \<Delta>e \<A>e}"
                    apply rule
                     apply rule
                     defer
                     apply rule
                  proof -
                    {
                      fix xa
                      assume xain: "xa \<in> {uu. \<exists>q \<alpha> q' q''.
                       uu = (q, \<alpha>, q'') \<and>
                       epsilon_reachable q q' (\<Delta>e' \<A>e) \<and> (q', \<alpha>, q'') \<in> \<Delta>e \<A>e}"
                      from this obtain q \<alpha> q' q'' where
                      xa_def: "xa = (q, \<alpha>, q'') \<and>
                       epsilon_reachable q q' (\<Delta>e' \<A>e) \<and> (q', \<alpha>, q'') \<in> \<Delta>e \<A>e"
                        by auto
                      from this epsilon_reachable_def[of q q' "\<Delta>e' \<A>e"]
                      obtain l where l_def:
                       "l \<noteq> [] \<and> epsilon_reach l (\<Delta>e' \<A>e) \<and> hd l = q \<and> last l = q'"
                        by auto
                      from this 
                      have "q \<in> \<Q>e \<A>e"
                        apply (induction l "\<Delta>e' \<A>e" arbitrary: q rule: epsilon_reach.induct )
                        apply simp
                        using NFAe.\<Delta>_consistent wfA xa_def apply fastforce
                        using NFAe.\<Delta>'_consistent wfA by fastforce

                      from xqnotNone p1 this
                      have "(q' \<in> the (x q))"
                        using xa_def by blast
                      from this
                      have "(\<exists>y. x q = Some y) \<and> q' \<in> the (x q)"
                        using \<open>q \<in> \<Q>e \<A>e\<close> xqnotNone by auto
                      from this
                      show " xa \<in> {uu. \<exists>q \<alpha> q' q''.
                        uu = (q, \<alpha>, q'') \<and>
                        (q', \<alpha>, q'') \<in> \<Delta>e \<A>e \<and>
                        q \<in> \<Q>e \<A>e \<and> (\<exists>y. x q = Some y) \<and> q' \<in> the (x q)}"
                        using \<open>q \<in> \<Q>e \<A>e\<close> xa_def by blast
                    }
                    {
                      fix xa
                      assume xain: "xa \<in> {uu. \<exists>q \<alpha> q' q''.
                       uu = (q, \<alpha>, q'') \<and>
                       (q', \<alpha>, q'') \<in> \<Delta>e \<A>e \<and>
                       q \<in> \<Q>e \<A>e \<and> (\<exists>y. x q = Some y) \<and> q' \<in> the (x q)}"
                      from this
                      obtain q \<alpha> q' q'' where
                      xa_def: "xa = (q, \<alpha>, q'') \<and>
                       (q', \<alpha>, q'') \<in> \<Delta>e \<A>e \<and>
                       q \<in> \<Q>e \<A>e \<and> (\<exists>y. x q = Some y) \<and> q' \<in> the (x q)"
                        by blast
                      from this
                      have "epsilon_reachable q q' (\<Delta>e' \<A>e)"
                        by (simp add: xin')
                      from this
                      show " xa \<in> {uu. \<exists>q \<alpha> q' q''.
                        uu = (q, \<alpha>, q'') \<and>
                        epsilon_reachable q q' (\<Delta>e' \<A>e) \<and> (q', \<alpha>, q'') \<in> \<Delta>e \<A>e}"
                        using xa_def by blast
                    }
                  qed
                  from this
                  show "\<Delta>e \<A>e \<union>
    {uu.
     \<exists>q \<alpha> q' q''.
        uu = (q, \<alpha>, q'') \<and>
        (q', \<alpha>, q'') \<in> \<Delta>e \<A>e \<and> q \<in> \<Q>e \<A>e \<and> (\<exists>y. x q = Some y) \<and> q' \<in> the (x q)} =
    \<Delta>e \<A>e \<union>
    {uu.
     \<exists>q \<alpha> q' q''.
        uu = (q, \<alpha>, q'') \<and> epsilon_reachable q q' (\<Delta>e' \<A>e) \<and> (q', \<alpha>, q'') \<in> \<Delta>e \<A>e}"
                    by auto}
                {
                  show "\<I>e \<A>e \<union> {uu. \<exists>q. q \<in> \<I>e \<A>e \<and> (\<exists>y. x q = Some y) \<and> uu \<in> the (x q)} =
    \<I>e \<A>e \<union> {uu. \<exists>q. epsilon_reachable q uu (\<Delta>e' \<A>e) \<and> q \<in> \<I>e \<A>e} \<and>
    \<F>e \<A>e \<union> {uu. \<exists>q. q \<in> \<F>e \<A>e \<and> uu \<in> \<Q>e \<A>e \<and> q \<in> the (x uu)} =
    \<F>e \<A>e \<union> {uu. \<exists>q'. epsilon_reachable uu q' (\<Delta>e' \<A>e) \<and> q' \<in> \<F>e \<A>e}"
                    apply (rule conjI)
                  proof -
                    {
                      have "{uu. \<exists>q. q \<in> \<I>e \<A>e \<and> (\<exists>y. x q = Some y) \<and> uu \<in> the (x q)}
                            = {uu. \<exists>q. epsilon_reachable q uu (\<Delta>e' \<A>e) \<and> q \<in> \<I>e \<A>e}"
                        apply rule
                         apply rule defer apply rule
                      proof - {
                          fix xa
                          assume xain: "xa \<in> {uu. \<exists>q. epsilon_reachable q uu (\<Delta>e' \<A>e) \<and> q \<in> \<I>e \<A>e}"
                          from this obtain q where 
                          q_def: "epsilon_reachable q xa (\<Delta>e' \<A>e) \<and> q \<in> \<I>e \<A>e" by auto
                          from this
                          have "(\<exists>y. x q = Some y) \<and> xa \<in> the (x q)"
                            using NFAe.\<I>_consistent wfA xin' by blast
                          from this
                          show "xa \<in> {uu. \<exists>q. q \<in> \<I>e \<A>e \<and> (\<exists>y. x q = Some y) \<and> uu \<in> the (x q)}"
                            using q_def by blast
                        }
                        {
                          fix xa 
                          assume xain: "xa \<in> {uu. \<exists>q. q \<in> \<I>e \<A>e \<and> (\<exists>y. x q = Some y) \<and> 
                                            uu \<in> the (x q)}"
                          from this obtain q
                            where q_def: "q \<in> \<I>e \<A>e \<and> (\<exists>y. x q = Some y) \<and> 
                                            xa \<in> the (x q)" by auto
                          from this 
                          have "epsilon_reachable q xa (\<Delta>e' \<A>e)" 
                            using xin' by blast
                          show "xa \<in> {uu. \<exists>q. epsilon_reachable q uu (\<Delta>e' \<A>e) \<and> q \<in> \<I>e \<A>e}"
                            using \<open>epsilon_reachable q xa (\<Delta>e' \<A>e)\<close> q_def by blast
                        }
                      qed
                      from this
                      show "\<I>e \<A>e \<union> {uu. \<exists>q. q \<in> \<I>e \<A>e \<and> (\<exists>y. x q = Some y) \<and> uu \<in> the (x q)} =
                             \<I>e \<A>e \<union> {uu. \<exists>q. epsilon_reachable q uu (\<Delta>e' \<A>e) \<and> q \<in> \<I>e \<A>e}"
                        by auto
                    }
                    {
                      have "{uu. \<exists>q. q \<in> \<F>e \<A>e \<and> uu \<in> \<Q>e \<A>e \<and> q \<in> the (x uu)} =
                            {uu. \<exists>q'. epsilon_reachable uu q' (\<Delta>e' \<A>e) \<and> q' \<in> \<F>e \<A>e}"
                        apply rule
                         apply rule defer apply rule
                      proof - 
                        {
                          fix xa 
                          assume xain: "xa \<in> {uu. \<exists>q'. 
                                  epsilon_reachable uu q' (\<Delta>e' \<A>e) \<and> q' \<in> \<F>e \<A>e}"
                          from this obtain q'
                            where q'_def: "epsilon_reachable xa q' (\<Delta>e' \<A>e) \<and> 
                                              q' \<in> \<F>e \<A>e" by blast
                          from this wfA NFAe_def
                          have q'in: "q' \<in> \<Q>e \<A>e" 
                            by (simp add: NFAe_def subset_iff)
                          from q'_def epsilon_reachable_def[of xa q' "\<Delta>e' \<A>e"]
                          obtain l where 
                           l_def: "l \<noteq> [] \<and> epsilon_reach l (\<Delta>e' \<A>e) \<and> hd l = xa \<and> last l = q'"
                            by auto
                          from this q'in
                          have "xa \<in> \<Q>e \<A>e"
                            apply (induction l "\<Delta>e' \<A>e" arbitrary: 
                                    xa rule: epsilon_reach.induct)
                              apply simp apply force 
                              using NFAe.\<Delta>'_consistent wfA by fastforce
                          from p1 this
                          have "xa \<in> \<Q>e \<A>e \<and> q' \<in> the (x xa)"
                            using q'_def by blast
                          from this
                          show "xa \<in> {uu. \<exists>q. q \<in> \<F>e \<A>e \<and> uu \<in> \<Q>e \<A>e \<and> q \<in> the (x uu)}"
                           using q'_def by blast
                       }{
                         fix xa 
                         assume xain: "xa \<in> {uu. \<exists>q. q \<in> \<F>e \<A>e \<and> uu \<in> \<Q>e \<A>e \<and> q \<in> the (x uu)}"
                         from this obtain q where 
                         q_def: "q \<in> \<F>e \<A>e \<and> xa \<in> \<Q>e \<A>e \<and> q \<in> the (x xa)"
                           by auto
                         from p1 this
                         have "epsilon_reachable xa q (\<Delta>e' \<A>e)" by auto
                         from this
                         show "xa \<in> {uu. \<exists>q'. epsilon_reachable uu q' (\<Delta>e' \<A>e) \<and> 
                                          q' \<in> \<F>e \<A>e}"
                           using q_def by blast
                       }
                     qed
                     from this
                      show "\<F>e \<A>e \<union> {uu. \<exists>q. q \<in> \<F>e \<A>e \<and> uu \<in> \<Q>e \<A>e \<and> q \<in> the (x uu)} =
    \<F>e \<A>e \<union> {uu. \<exists>q'. epsilon_reachable uu q' (\<Delta>e' \<A>e) \<and> q' \<in> \<F>e \<A>e}"
                        by auto
                    }
                  qed
                }
              qed
            qed
              from this cc3
              show "compute_ep_F (\<F>e \<A>e) (\<Q>e \<A>e) x
    \<le> SPEC (\<lambda>N\<F>. RETURN
                   \<lparr>\<Q> = \<Q>e \<A>e, \<Sigma> = \<Sigma>e \<A>e,
                      \<Delta> = \<Delta>e \<A>e \<union>
                           {uu.
                            \<exists>q \<alpha> q' q''.
                               uu = (q, \<alpha>, q'') \<and>
                               (q', \<alpha>, q'') \<in> \<Delta>e \<A>e \<and>
                               q \<in> \<Q>e \<A>e \<and> (\<exists>y. x q = Some y) \<and> q' \<in> the (x q)},
                      \<I> = \<I>e \<A>e \<union>
                          {uu. \<exists>q. q \<in> \<I>e \<A>e \<and> (\<exists>y. x q = Some y) \<and> uu \<in> the (x q)},
                      \<F> = \<F>e \<A>e \<union> N\<F>\<rparr>
                  \<le> SPEC (\<lambda>\<A>. \<A> = epsilon_elim \<A>e))"
                
                using SPEC_trans by blast
            qed
            from this show "compute_ep_F (\<F>e \<A>e) (\<Q>e \<A>e) x \<bind>
    (\<lambda>N\<F>. RETURN
            \<lparr>\<Q> = \<Q>e \<A>e, \<Sigma> = \<Sigma>e \<A>e,
               \<Delta> = \<Delta>e \<A>e \<union>
                    {uu.
                     \<exists>q \<alpha> q' q''.
                        uu = (q, \<alpha>, q'') \<and>
                        (q', \<alpha>, q'') \<in> \<Delta>e \<A>e \<and>
                        q \<in> \<Q>e \<A>e \<and> (\<exists>y. x q = Some y) \<and> q' \<in> the (x q)},
               \<I> = \<I>e \<A>e \<union> {uu. \<exists>q. q \<in> \<I>e \<A>e \<and> (\<exists>y. x q = Some y) \<and> uu \<in> the (x q)},
               \<F> = \<F>e \<A>e \<union> N\<F>\<rparr>)
    \<le> RES {epsilon_elim \<A>e}"
              by auto
          qed
          from this cc2
          show "compute_ep_I (\<I>e \<A>e) x
    \<le> SPEC (\<lambda>N\<I>. compute_ep_F (\<F>e \<A>e) (\<Q>e \<A>e) x \<bind>
                  (\<lambda>N\<F>. RETURN
                          \<lparr>\<Q> = \<Q>e \<A>e, \<Sigma> = \<Sigma>e \<A>e,
                             \<Delta> = \<Delta>e \<A>e \<union>
                                  {uu.
                                   \<exists>q \<alpha> q' q''.
                                      uu = (q, \<alpha>, q'') \<and>
                                      (q', \<alpha>, q'') \<in> \<Delta>e \<A>e \<and>
                                      q \<in> \<Q>e \<A>e \<and>
                                      (\<exists>y. x q = Some y) \<and> q' \<in> the (x q)},
                             \<I> = \<I>e \<A>e \<union> N\<I>, \<F> = \<F>e \<A>e \<union> N\<F>\<rparr>)
                  \<le> SPEC (\<lambda>\<A>. \<A> = epsilon_elim \<A>e))"
            using SPEC_trans by blast
        qed
          from this
          show "compute_ep_I (\<I>e \<A>e) x \<bind>
    (\<lambda>N\<I>. compute_ep_F (\<F>e \<A>e) (\<Q>e \<A>e) x \<bind>
          (\<lambda>N\<F>. RETURN
                  \<lparr>\<Q> = \<Q>e \<A>e, \<Sigma> = \<Sigma>e \<A>e,
                     \<Delta> = \<Delta>e \<A>e \<union>
                          {uu.
                           \<exists>q \<alpha> q' q''.
                              uu = (q, \<alpha>, q'') \<and>
                              (q', \<alpha>, q'') \<in> \<Delta>e \<A>e \<and>
                              q \<in> \<Q>e \<A>e \<and> (\<exists>y. x q = Some y) \<and> q' \<in> the (x q)},
                     \<I> = \<I>e \<A>e \<union> N\<I>, \<F> = \<F>e \<A>e \<union> N\<F>\<rparr>))
    \<le> RES {epsilon_elim \<A>e}"
            by auto
        qed
        from this cc1
        show "compute_ep_Trans (\<Delta>e \<A>e) (\<Q>e \<A>e) x
    \<le> SPEC (\<lambda>N\<Delta>. compute_ep_I (\<I>e \<A>e) x \<bind>
                  (\<lambda>N\<I>. compute_ep_F (\<F>e \<A>e) (\<Q>e \<A>e) x \<bind>
                        (\<lambda>N\<F>. RETURN
                                \<lparr>\<Q> = \<Q>e \<A>e, \<Sigma> = \<Sigma>e \<A>e, \<Delta> = \<Delta>e \<A>e \<union> N\<Delta>,
                                   \<I> = \<I>e \<A>e \<union> N\<I>, \<F> = \<F>e \<A>e \<union> N\<F>\<rparr>))
                  \<le> SPEC (\<lambda>\<A>. \<A> = epsilon_elim \<A>e))"
          
          using SPEC_trans by blast
      qed
    from this
    show "compute_ep_Trans (\<Delta>e \<A>e) (\<Q>e \<A>e) x \<bind>
         (\<lambda>N\<Delta>. compute_ep_I (\<I>e \<A>e) x \<bind>
                (\<lambda>N\<I>. compute_ep_F (\<F>e \<A>e) (\<Q>e \<A>e) x \<bind>
                      (\<lambda>N\<F>. RETURN
                              \<lparr>\<Q> = \<Q>e \<A>e, \<Sigma> = \<Sigma>e \<A>e, \<Delta> = \<Delta>e \<A>e \<union> N\<Delta>,
                                 \<I> = \<I>e \<A>e \<union> N\<I>, \<F> = \<F>e \<A>e \<union> N\<F>\<rparr>)))
         \<le> RES {epsilon_elim \<A>e}"
      by auto
  qed


  from this c1
  show "reach_closure_imp (\<Q>e \<A>e) (\<Delta>e' \<A>e)
    \<le> SPEC (\<lambda>P. compute_ep_Trans (\<Delta>e \<A>e) (\<Q>e \<A>e) P \<bind>
                 (\<lambda>N\<Delta>. compute_ep_I (\<I>e \<A>e) P \<bind>
                        (\<lambda>N\<I>. compute_ep_F (\<F>e \<A>e) (\<Q>e \<A>e) P \<bind>
                              (\<lambda>N\<F>. RETURN
                                      \<lparr>\<Q> = \<Q>e \<A>e, \<Sigma> = \<Sigma>e \<A>e, \<Delta> = \<Delta>e \<A>e \<union> N\<Delta>,
                                         \<I> = \<I>e \<A>e \<union> N\<I>, \<F> = \<F>e \<A>e \<union> N\<F>\<rparr>)))
                 \<le> SPEC (\<lambda>\<A>. \<A> = epsilon_elim \<A>e))"
    using SPEC_trans by blast
qed

end












