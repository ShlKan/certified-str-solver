theory Epsilon_elim

imports Main NFA_set_interval NFA_epsilon

begin

definition epsilon_elim :: "('q, 'a) NFAe_rec \<Rightarrow> ('q, 'a) NFA_rec" where
    "epsilon_elim \<A>e = \<lparr>
     \<Q> = \<Q>e \<A>e,
     \<Sigma> = \<Sigma>e \<A>e,
     \<Delta> = (\<Delta>e \<A>e) \<union> {(q, \<alpha> ,q'') | q \<alpha> q' q''. 
                                    epsilon_reachable q q' (\<Delta>e' \<A>e) \<and>
                                      (q', \<alpha>, q'') \<in> \<Delta>e \<A>e},
     \<I> = \<I>e \<A>e \<union> {q' | q q'. epsilon_reachable q q' (\<Delta>e' \<A>e) \<and> q \<in> \<I>e \<A>e},
     \<F> = \<F>e \<A>e \<union> {q | q q'. epsilon_reachable q q' (\<Delta>e' \<A>e) \<and> q' \<in> \<F>e \<A>e}
    \<rparr>"

lemma epsilon_reach_concate_fst:
      "epsilon_reach (l1@l2) D \<longrightarrow> epsilon_reach l1 D"
  apply (induction l1)
  apply simp
  by (metis Cons_eq_appendI epsilon_reach.elims(3) 
            epsilon_reach.simps(3) list_tail_coinc)  

lemma epsilon_reach_concate:
      "epsilon_reach (l1@[q]) D \<and> epsilon_reach ([q]@l2) D \<longrightarrow> 
          epsilon_reach (l1@[q]@l2) D"
  apply (induction l1)
  apply simp 
  apply rule
proof -
  fix a l1
  assume ind_hyp: "epsilon_reach (l1 @ [q]) D \<and> epsilon_reach ([q] @ l2) D \<longrightarrow>
                   epsilon_reach (l1 @ [q] @ l2) D"
     and  p1: "epsilon_reach ((a # l1) @ [q]) D \<and> epsilon_reach ([q] @ l2) D"

  from p1 
  have c1: "epsilon_reach (l1 @ [q]) D"
    by (metis append_Cons epsilon_reach.elims(3) epsilon_reach.simps(3))
  from this p1
  have "epsilon_reach (l1 @ [q] @ l2) D"  
    using ind_hyp by blast
  from this p1 
  show "epsilon_reach ((a # l1) @ [q] @ l2) D"
  proof (cases "l1 = []")
    case True
    then show ?thesis 
      using p1 by auto
  next
    case False
    from this obtain a1 l1'
      where l1'_def: "l1 = a1 # l1'" 
      using neq_NilE by blast
    from this epsilon_reach.simps(3)[of a a1 l1 "D"]
    show ?thesis 
      using ind_hyp p1 by auto
  qed
qed

lemma reachable_hd:
  assumes reachableqq': "LTS_is_reachable_epsilon D D' q (a # x) q'"
  shows "\<exists> q1 q2 \<alpha>. epsilon_reachable q q1 D' \<and> (q1, \<alpha>, q2) \<in> D \<and>
                    a \<in> \<alpha> \<and>
                    LTS_is_reachable_epsilon D D' q2 x q'"
  using reachableqq'
  by auto

lemma reachable_last:
  fixes \<A> q x q'
  assumes reachableqq': "LTS_is_reachable_epsilon (\<Delta>e \<A>) (\<Delta>e' \<A>) q x q'"
  shows "\<exists>q''. LTS_is_reachable (\<Delta> (epsilon_elim \<A>)) q x q'' \<and> 
                            epsilon_reachable q'' q' (\<Delta>e' \<A>)"
    using reachableqq'
    apply (induction x arbitrary: q)
    apply (simp add: epsilon_reachable_def) 
    proof -
      fix a x q
      assume ind_hyp: "(\<And>q. LTS_is_reachable_epsilon (\<Delta>e \<A>) (\<Delta>e' \<A>) q x q' \<Longrightarrow>
            \<exists>q''. LTS_is_reachable (\<Delta> (epsilon_elim \<A>)) q x q'' \<and>
                   epsilon_reachable q'' q' (\<Delta>e' \<A>))"
         and p1: "LTS_is_reachable_epsilon (\<Delta>e \<A>) (\<Delta>e' \<A>) q (a # x) q'"  
      from reachable_hd[of "\<Delta>e \<A>" "\<Delta>e' \<A>" q a x q'] p1
      obtain q1 q2 \<alpha> where
      q12\<alpha>_def: "epsilon_reachable q q1 (\<Delta>e' \<A>) \<and>
                 (q1, \<alpha>, q2) \<in> \<Delta>e \<A> \<and> a \<in> \<alpha> \<and> 
                  LTS_is_reachable_epsilon (\<Delta>e \<A>) (\<Delta>e' \<A>) q2 x q'"
        by auto

      from q12\<alpha>_def epsilon_elim_def[of \<A>]
      have q\<alpha>q2in: "(q, \<alpha>, q2) \<in> \<Delta> (epsilon_elim \<A>)"
        apply simp
        by blast

      from q12\<alpha>_def ind_hyp[of q2]
      obtain q'' where
      q''l_def: "LTS_is_reachable (\<Delta> (epsilon_elim \<A>)) q2 x q'' \<and>
                 epsilon_reachable q'' q' (\<Delta>e' \<A>)"
        by auto

      from this q\<alpha>q2in
      have "LTS_is_reachable (\<Delta> (epsilon_elim \<A>)) q (a # x) q''"
        using q12\<alpha>_def by auto

      from this q''l_def
      show "\<exists>q''. LTS_is_reachable (\<Delta> (epsilon_elim \<A>)) q (a # x) q'' \<and>
             epsilon_reachable q'' q' (\<Delta>e' \<A>)"
        by auto    
    qed

lemma reachable_to_reachable_epsilon:
  fixes \<A> q x q'
  assumes reachable: "LTS_is_reachable (\<Delta> (epsilon_elim \<A>)) q x q'"
  shows "LTS_is_reachable_epsilon (\<Delta>e \<A>) (\<Delta>e' \<A>) q x q'"
  using reachable
  apply (induction x arbitrary: q)
  apply (simp add: epsilon_reachable_def) 
  apply (meson epsilon_reach.simps(2) last.simps list.sel(1))
  apply (meson epsilon_reach.simps(2) last.simps list.sel(1) not_Cons_self2)
proof -
  fix a x q
  assume ind_hyp: "(\<And>q. LTS_is_reachable (\<Delta> (epsilon_elim \<A>)) q x q' \<Longrightarrow>
                     LTS_is_reachable_epsilon (\<Delta>e \<A>) (\<Delta>e' \<A>) q x q')"
     and p1: "LTS_is_reachable (\<Delta> (epsilon_elim \<A>)) q (a # x) q'"


  from p1 epsilon_elim_def[of \<A>]
  have inelim: "\<forall> \<alpha> q1. (q, \<alpha>, q1) \<in> \<Delta> (epsilon_elim \<A>) \<and> a \<in> \<alpha> \<longrightarrow> 
            (q, \<alpha>, q1) \<in> (\<Delta>e \<A>) \<union> {(q, \<alpha> ,q'') | q \<alpha> q' q''. 
                                    epsilon_reachable q q' (\<Delta>e' \<A>) \<and>
                                      (q', \<alpha>, q'') \<in> \<Delta>e \<A>}"
    by auto

  from p1
  obtain q1 \<alpha> where
  q1\<alpha>_def: "(q, \<alpha>, q1) \<in> (\<Delta> (epsilon_elim \<A>)) \<and> a \<in> \<alpha> \<and>
            LTS_is_reachable (\<Delta> (epsilon_elim \<A>)) q1 x q'"
  proof -
    assume "\<And>\<alpha> q1. (q, \<alpha>, q1) \<in> \<Delta> (epsilon_elim \<A>) \<and> a \<in> \<alpha> \<and> LTS_is_reachable (\<Delta> (epsilon_elim \<A>)) q1 x q' \<Longrightarrow> thesis"
    then show ?thesis
      using \<open>LTS_is_reachable (\<Delta> (epsilon_elim \<A>)) q (a # x) q'\<close> by auto
  qed

  from this inelim
  have qaq1in: "(q, \<alpha>, q1) \<in> \<Delta>e \<A> \<union>
          {(q, \<alpha>, q'') |
            q \<alpha> q' q''.
              epsilon_reachable q q' (\<Delta>e' \<A>) \<and> (q', \<alpha>, q'') \<in> \<Delta>e \<A>}"
    by force

  from this
  have "\<exists> q2. epsilon_reachable q q2 (\<Delta>e' \<A>) \<and> (q2, \<alpha>, q1) \<in> (\<Delta>e \<A>)"
  proof (cases "(q, \<alpha>, q1) \<in> \<Delta>e \<A>")
  case True
  then show ?thesis 
    using epsilon_reachable_def
    by (metis epsilon_reach.simps(2) last_appendR 
              last_snoc list.distinct(1) list.sel(1))
  next
    case False
    from this qaq1in
    have "(q, \<alpha>, q1) \<in> {(q, \<alpha>, q'') |
            q \<alpha> q' q''.
              epsilon_reachable q q' (\<Delta>e' \<A>) \<and> (q', \<alpha>, q'') \<in> \<Delta>e \<A>}"
      by auto
  then show ?thesis by force
qed
  from this 
  obtain q2 where
  q2_def: "epsilon_reachable q q2 (\<Delta>e' \<A>) \<and> (q2, \<alpha>, q1) \<in> \<Delta>e \<A>"
    by auto
  from q1\<alpha>_def q2_def ind_hyp[of q1]
  have "LTS_is_reachable_epsilon (\<Delta>e \<A>) (\<Delta>e' \<A>) q1 x q'"
    by auto
  from this q2_def q1\<alpha>_def
  show "LTS_is_reachable_epsilon (\<Delta>e \<A>) (\<Delta>e' \<A>) q (a # x) q'"
    by force
qed

lemma add_suffix:
  fixes \<A> q w q' qi
  assumes reach_path: "LTS_is_reachable_epsilon (\<Delta>e \<A>) (\<Delta>e' \<A>) q w q'"
      and reach_step: "epsilon_reachable q' qa (\<Delta>e' \<A>)"
    shows "LTS_is_reachable_epsilon (\<Delta>e \<A>) (\<Delta>e' \<A>) q w qa"
  using reach_path reach_step
  apply (induction w arbitrary: q)
  apply simp
proof -
  {
    fix q
    assume p1: "\<exists>l. l \<noteq> [] \<and> epsilon_reach l (\<Delta>e' \<A>) \<and> hd l = q \<and> last l = q'"
       and p2: "epsilon_reachable q' qa (\<Delta>e' \<A>)"

    from p1 
    obtain l  where l_def: "l \<noteq> [] \<and> epsilon_reach l (\<Delta>e' \<A>) \<and> 
                             hd l = q \<and> last l = q'"
      by auto
    from p2 epsilon_reachable_def[of q' qa "\<Delta>e' \<A>"]
    obtain l' where
    l'_def: "l' \<noteq> [] \<and> epsilon_reach l' (\<Delta>e' \<A>) 
              \<and> hd l' = q' \<and> last l' = qa"
      by auto

    from l_def
    obtain l1 where l1_def: "l = l1@[q']" 
      by (metis append_butlast_last_id)

    from l'_def
    obtain l2 where l2_def: "l' = [q'] @ l2" 
      by (metis append_Cons empty_append_eq_id list.sel(1) neq_NilE)

    from epsilon_reach_concate[of l1 q' "\<Delta>e' \<A>" l2]
    have "epsilon_reach (l1 @ [q'] @ l2) (\<Delta>e' \<A>)"
      using l'_def l1_def l2_def l_def by auto

    from this
    show "\<exists>l. l \<noteq> [] \<and> epsilon_reach l (\<Delta>e' \<A>) \<and> hd l = q \<and> last l = qa"
      by (metis append_is_Nil_conv hd_append l'_def l1_def l2_def 
            l_def last_append)
  }
  {
    fix a w q
    assume ind_hyp: "\<And> q. LTS_is_reachable_epsilon (\<Delta>e \<A>) (\<Delta>e' \<A>) q w q' \<Longrightarrow>
            epsilon_reachable q' qa (\<Delta>e' \<A>) \<Longrightarrow>
            LTS_is_reachable_epsilon (\<Delta>e \<A>) (\<Delta>e' \<A>) q w qa"
       and p1: "LTS_is_reachable_epsilon (\<Delta>e \<A>) (\<Delta>e' \<A>) q (a # w) q'"
       and p2: "epsilon_reachable q' qa (\<Delta>e' \<A>)"

    from p1 LTS_is_reachable_epsilon.simps(2)[of "\<Delta>e \<A>" "\<Delta>e' \<A>" q a w q']
    obtain qi qj \<sigma> where
     ij\<sigma>_def: "epsilon_reachable q qi (\<Delta>e' \<A>) \<and>  a \<in> \<sigma> \<and>
        (qi, \<sigma>, qj) \<in> \<Delta>e \<A> \<and> 
        LTS_is_reachable_epsilon (\<Delta>e \<A>) (\<Delta>e' \<A>) qj w q'"
      by auto

    from ind_hyp[of qj] ij\<sigma>_def p2
    have "LTS_is_reachable_epsilon (\<Delta>e \<A>) (\<Delta>e' \<A>) qj w qa"
      by auto
    from this ij\<sigma>_def 
          LTS_is_reachable_epsilon.simps(2)[of "\<Delta>e \<A>" "\<Delta>e' \<A>" q a w qa]
    show "LTS_is_reachable_epsilon (\<Delta>e \<A>) (\<Delta>e' \<A>) q (a # w) qa"
      by auto
  }
qed

lemma add_prefix:
  fixes \<A> q w q' qi
  assumes reach_path: "LTS_is_reachable_epsilon (\<Delta>e \<A>) (\<Delta>e' \<A>) q w q'"
      and reach_step: "epsilon_reachable qi q (\<Delta>e' \<A>)"
    shows "LTS_is_reachable_epsilon (\<Delta>e \<A>) (\<Delta>e' \<A>) qi w q'"
  using reach_path
  apply (induction w)
proof -
  {
    assume p1: "LTS_is_reachable_epsilon (\<Delta>e \<A>) (\<Delta>e' \<A>) q [] q'"
    from p1 LTS_is_reachable_epsilon.simps(1)[of "(\<Delta>e \<A>)" "\<Delta>e' \<A>" q q']
    obtain l where
    l_def: "l \<noteq> [] \<and>  epsilon_reach l (\<Delta>e' \<A>) \<and> hd l = q \<and> last l = q'"
      by auto

    from reach_step epsilon_reachable_def[of qi q "\<Delta>e' \<A>"]
    obtain l' where
    l'_def: "l' \<noteq> [] \<and> epsilon_reach l' (\<Delta>e' \<A>) \<and> hd l' = qi \<and> last l' = q"
      by auto

    from this 
    obtain l'' where
    l''_def: "l' = l'' @ [q]" 
      by (metis append_butlast_last_id)

    from this l'_def
    have l''q: "l'' \<noteq> [] \<longrightarrow> (last l'', q) \<in> (\<Delta>e' \<A>)"
      apply (induction l'' arbitrary: l' qi)
      apply simp
    proof -
      fix a l'' l' qi
      assume ind_hyp: "(\<And>l' qi. l' = l'' @ [q] \<Longrightarrow>
        l' \<noteq> [] \<and> epsilon_reach l' (\<Delta>e' \<A>) \<and> hd l' = qi \<and> last l' = q \<Longrightarrow>
        l'' \<noteq> [] \<longrightarrow> (last l'', q) \<in> \<Delta>e' \<A>)"
        and p1: "l' = (a # l'') @ [q]"
        and p2: "l' \<noteq> [] \<and> epsilon_reach l' (\<Delta>e' \<A>) \<and>  
                  hd l' = qi \<and> last l' = q"

      from p1 p2 epsilon_reach.simps(3)[of a]
      have c1: "epsilon_reach (l''@[q]) (\<Delta>e' \<A>)" 
      proof (cases "l'' = []")
        case True
        then show ?thesis 
          by simp
        next
          case False
          from this obtain q1 l1 where
          q1l1_def: "l'' = q1 # l1" 
            by (metis hd_Cons_tl)
          from this epsilon_reach.simps(3)[of a q1 "l1@[q]" "\<Delta>e' \<A>"]
          show ?thesis 
            using p1 p2 by auto
        qed
      from this
      show "a # l'' \<noteq> [] \<longrightarrow> (last (a # l''), q) \<in> \<Delta>e' \<A>"
      proof (cases "l'' = []")
      case True
        then show ?thesis 
          using p1 p2 by auto
      next
        case False
        from this obtain q1 l1 where
          q1l1_def: "l'' = q1 # l1" 
          by (metis hd_Cons_tl)
        from this
        have c2: "hd (l'' @ [q]) = q1 \<and> last (l'' @ [q]) = q"
          by force
        from ind_hyp[of "l'' @ [q]" q1] c1 c2
        have "l'' \<noteq> [] \<longrightarrow> (last l'', q) \<in> \<Delta>e' \<A>"
          by auto
        from this
        show ?thesis 
          by (simp add: False)
      qed
    qed
  
    
    from l'_def
    have "hd l' = qi \<and> last l' = q" by auto
    
    from l''q l''_def l_def this
    have "epsilon_reach (l''@l) (\<Delta>e' \<A>) \<and> hd (l''@l) = qi \<and> last (l''@l) = q'"
    proof (cases "l'' = []")
      case True
      then show ?thesis 
        apply simp
        using l''_def l'_def l_def by auto
    next
      case False
      from this l'_def l''_def
      show ?thesis 
        apply (induction l'' arbitrary: l' qi)
        apply simp
      proof -
        fix a l'' l' qi
        assume ind_hyp: "(\<And> l' qi. l'' \<noteq> [] \<Longrightarrow>
        l' \<noteq> [] \<and> epsilon_reach l' (\<Delta>e' \<A>) \<and> hd l' = qi \<and> last l' = q \<Longrightarrow>
        l' = l'' @ [q] \<Longrightarrow>
        epsilon_reach (l'' @ l) (\<Delta>e' \<A>) \<and>
        hd (l'' @ l) = qi \<and> last (l'' @ l) = q')"
        and p1: "a # l'' \<noteq> []"
        and p2: "l' \<noteq> [] \<and> epsilon_reach l' (\<Delta>e' \<A>) \<and> hd l' = qi \<and> last l' = q"
        and p3: "l' = (a # l'') @ [q]"
        thm ind_hyp[OF _ p2]
        show "epsilon_reach ((a # l'') @ l) (\<Delta>e' \<A>) \<and>
              hd ((a # l'') @ l) = qi \<and> last ((a # l'') @ l) = q'"
        proof (cases "l'' = []")
          case True
          from p1 p3 p2
          have aqieq: "a = qi" by auto
          from this l'_def p2 p3 True
          have "(qi, q) \<in> (\<Delta>e' \<A>)" by auto
        
          from this True l_def this aqieq
          show ?thesis 
            apply simp
            by (metis epsilon_reach.elims(3) list.sel(1) list_tail_coinc)
        next
          case False
          from this 
          obtain q2 l2 where
          q2l2_def: "l'' = q2 # l2" 
            using neq_NilE by blast
          from p2 p3 q2l2_def
          have c3: "l'' @ [q] \<noteq> [] \<and> epsilon_reach (l'' @ [q]) (\<Delta>e' \<A>) \<and> 
                hd (l'' @ [q]) = q2 \<and> last (l'' @ [q]) = q"
            by simp
          from ind_hyp[OF False c3]
          have c4: "epsilon_reach (l'' @ l) (\<Delta>e' \<A>) \<and> 
                        hd (l'' @ l) = q2 \<and> last (l'' @ l) = q'"
            by auto
          then show ?thesis 
            using p2 p3 q2l2_def by auto
        qed
    qed
  qed
  from this
  show "LTS_is_reachable_epsilon (\<Delta>e \<A>) (\<Delta>e' \<A>) qi [] q'"
    using l_def by auto
  }
  {
    fix a w
    assume ind_hyp: "(LTS_is_reachable_epsilon (\<Delta>e \<A>) (\<Delta>e' \<A>) q w q' \<Longrightarrow>
            LTS_is_reachable_epsilon (\<Delta>e \<A>) (\<Delta>e' \<A>) qi w q')"
       and p1: "LTS_is_reachable_epsilon (\<Delta>e \<A>) (\<Delta>e' \<A>) q (a # w) q'"

    from reach_step epsilon_reachable_def[of qi q "\<Delta>e' \<A>"]
    obtain l where
    l_def: "l \<noteq> [] \<and> epsilon_reach l (\<Delta>e' \<A>) \<and> hd l = qi \<and> last l = q"
      by auto   
    from this
    obtain l1 where 
    l1_def: "l = l1@[q]" 
      by (metis append_butlast_last_id)

    from p1 LTS_is_reachable_epsilon.simps(2)[of "\<Delta>e \<A>" "\<Delta>e' \<A>" q a w q']
    obtain qi' qj \<sigma> where
    qiqj\<sigma>_def: "epsilon_reachable q qi' (\<Delta>e' \<A>) \<and>
          a \<in> \<sigma> \<and> (qi', \<sigma>, qj) \<in> \<Delta>e \<A> \<and> 
          LTS_is_reachable_epsilon (\<Delta>e \<A>) (\<Delta>e' \<A>) qj w q'"
      by auto

    from this epsilon_reachable_def[of q qi' "\<Delta>e' \<A>"]
    obtain l' where
    l'_def: "l' \<noteq> [] \<and> epsilon_reach l' (\<Delta>e' \<A>) \<and> hd l' = q \<and> last l' = qi'"
      by auto
    from this
    obtain l2 where
    l2_def: "l' = [q]@l2" 
      by (metis append_Cons empty_append_eq_id list.sel(1) neq_NilE)

    from l_def l1_def l'_def l2_def
         epsilon_reach_concate[of l1 q "\<Delta>e' \<A>" l2]
    have c6: "epsilon_reach (l1 @ [q] @ l2) (\<Delta>e' \<A>)"
      by simp

    from this l_def l1_def
    have "epsilon_reachable qi qi' (\<Delta>e' \<A>)" 
      by (metis Nil_is_append_conv append_assoc 
                epsilon_reachable_def hd_append2 l'_def l2_def last_appendR)

    from p1 reach_step LTS_is_reachable_epsilon.simps(2)
                        [of "\<Delta>e \<A>" "\<Delta>e' \<A>" qi a w q']
        qiqj\<sigma>_def this
    show c5: "LTS_is_reachable_epsilon (\<Delta>e \<A>) (\<Delta>e' \<A>) qi (a # w) q'"
      by force
  }
qed

lemma epsilon_elim_correct: 
      "\<L> (epsilon_elim \<A>) = \<L>e \<A>"
  unfolding \<L>_def \<L>e_def NFA_accept_def NFAe_accept_def
  apply rule
  apply rule
  defer
  apply rule
proof -
  {
    fix x
    assume x_in: " x \<in> {w. \<exists>q\<in>\<I>e \<A>.
                    Bex (\<F>e \<A>)
                     (LTS_is_reachable_epsilon (\<Delta>e \<A>) (\<Delta>e' \<A>) q w)}"
    from this
    obtain q q' where 
    qq'_def: "q \<in> \<I>e \<A> \<and> q' \<in> \<F>e \<A> \<and> 
              LTS_is_reachable_epsilon (\<Delta>e \<A>) (\<Delta>e' \<A>) q x q'"
      by auto

    from this 
    have reachable: "LTS_is_reachable_epsilon (\<Delta>e \<A>) (\<Delta>e' \<A>) q x q'"
      by auto
    from this
    have reachable': "\<exists>q''. LTS_is_reachable (\<Delta> (epsilon_elim \<A>)) q x q'' \<and> 
                            epsilon_reachable q'' q' (\<Delta>e' \<A>)"
      apply (induction x arbitrary: q)
      apply (simp add: epsilon_reachable_def)  
    proof -
      fix a x q
      assume ind_hyp: "(\<And>q. LTS_is_reachable_epsilon (\<Delta>e \<A>) (\<Delta>e' \<A>) q x q' \<Longrightarrow>
            \<exists>q''. LTS_is_reachable (\<Delta> (epsilon_elim \<A>)) q x q'' \<and>
                   epsilon_reachable q'' q' (\<Delta>e' \<A>))"
         and p1: "LTS_is_reachable_epsilon (\<Delta>e \<A>) (\<Delta>e' \<A>) q (a # x) q'"  

 

      from reachable_hd[of "\<Delta>e \<A>" "\<Delta>e' \<A>" q a x q'] p1
      obtain q1 q2 \<alpha> where
      q12\<alpha>_def: "epsilon_reachable q q1 (\<Delta>e' \<A>) \<and>
                 (q1, \<alpha>, q2) \<in> \<Delta>e \<A> \<and> a \<in> \<alpha> \<and> 
                  LTS_is_reachable_epsilon (\<Delta>e \<A>) (\<Delta>e' \<A>) q2 x q'"
        by auto

      from q12\<alpha>_def epsilon_elim_def[of \<A>]
      have q\<alpha>q2in: "(q, \<alpha>, q2) \<in> \<Delta> (epsilon_elim \<A>)"
        apply simp
        by blast

      from q12\<alpha>_def ind_hyp[of q2]
      obtain q'' where
      q''l_def: "LTS_is_reachable (\<Delta> (epsilon_elim \<A>)) q2 x q'' \<and>
                 epsilon_reachable q'' q' (\<Delta>e' \<A>)"
        by auto

      from this q\<alpha>q2in
      have "LTS_is_reachable (\<Delta> (epsilon_elim \<A>)) q (a # x) q''"
        using q12\<alpha>_def by auto

      from this q''l_def
      show "\<exists>q''. LTS_is_reachable (\<Delta> (epsilon_elim \<A>)) q (a # x) q'' \<and>
             epsilon_reachable q'' q' (\<Delta>e' \<A>)"
        by auto    
    qed

    from this
    obtain q'' where
    q''_def: "LTS_is_reachable (\<Delta> (epsilon_elim \<A>)) q x q'' \<and>
              epsilon_reachable q'' q' (\<Delta>e' \<A>)"
      by auto

    from this epsilon_elim_def[of \<A>]
    have "q \<in> \<I> (epsilon_elim \<A>) \<and>
                     q'' \<in>(\<F> (epsilon_elim \<A>)) \<and>
                      (LTS_is_reachable (\<Delta> (epsilon_elim \<A>)) q x q'')"
      apply (rule_tac conjI)
      apply (simp add: qq'_def)
      apply (rule_tac conjI)
      using qq'_def
      apply force
      by simp
    from this
    show "x \<in> {w. \<exists>q\<in>\<I> (epsilon_elim \<A>).
                     Bex (\<F> (epsilon_elim \<A>))
                      (LTS_is_reachable (\<Delta> (epsilon_elim \<A>)) q w)}"
      by auto
  }{
    fix x
    assume xin: "x \<in> {w. \<exists>q\<in>\<I> (epsilon_elim \<A>).
                    Bex (\<F> (epsilon_elim \<A>))
                     (LTS_is_reachable (\<Delta> (epsilon_elim \<A>)) q w)}"
    from this
    obtain q q' where
    qq'_def: "q \<in> \<I> (epsilon_elim \<A>) \<and> q' \<in> \<F> (epsilon_elim \<A>) \<and>
              (LTS_is_reachable (\<Delta> (epsilon_elim \<A>)) q x q')"
      by auto

    from reachable_to_reachable_epsilon[of \<A> q x q'] qq'_def
    have reachableqxq': "LTS_is_reachable_epsilon (\<Delta>e \<A>) (\<Delta>e' \<A>) q x q'"
      by auto

    have qini: "q \<in> \<I>e \<A> \<union> {q' | q q'. epsilon_reachable q q' (\<Delta>e' \<A>) \<and> q \<in> \<I>e \<A>}"
      by (metis (mono_tags, lifting) NFA_rec.select_convs(4) 
                 epsilon_elim_def qq'_def)

    from this 
    have "\<exists> q_ini. epsilon_reachable q_ini q (\<Delta>e' \<A>) \<and> q_ini \<in> \<I>e \<A>"
    proof (cases "q \<in> \<I>e \<A>")
      case True
      from this
      have "epsilon_reachable q q (\<Delta>e' \<A>)"
        unfolding epsilon_reachable_def
        by (meson LTS_is_reachable.simps(1) 
              LTS_is_reachable_epsilon.simps(1) reachable_to_reachable_epsilon)
      from this True
      show ?thesis by auto
    next
      case False
      from this qini
      have "q \<in> {q' | q q'. epsilon_reachable q q' (\<Delta>e' \<A>) \<and> q \<in> \<I>e \<A>}"
        by force
    then show ?thesis by force
  qed
  from this
  obtain q_ini where
  q_ini_def: "epsilon_reachable q_ini q (\<Delta>e' \<A>) \<and> q_ini \<in> \<I>e \<A>"
    by auto

  from qq'_def epsilon_elim_def[of \<A>]
  have q'accin: "q' \<in> \<F>e \<A> \<union> {q | q q'. epsilon_reachable q q' (\<Delta>e' \<A>) \<and> q' \<in> \<F>e \<A>}"
    by simp

  from this
  have "\<exists> q_acc. epsilon_reachable q' q_acc (\<Delta>e' \<A>) \<and> q_acc \<in> \<F>e \<A>"
  proof (cases "q' \<in> \<F>e \<A>")
    case True
    from this
    have "epsilon_reachable q' q' (\<Delta>e' \<A>)" 
      unfolding epsilon_reachable_def 
      by (meson LTS_is_reachable.simps(1) 
              LTS_is_reachable_epsilon.simps(1) reachable_to_reachable_epsilon)
    from this True
    show ?thesis by auto
  next
    case False
    from this q'accin
    have "q' \<in> {uu. \<exists>q q'. uu = q \<and>
                   epsilon_reachable q q' (\<Delta>e' \<A>) \<and> q' \<in> \<F>e \<A>}"
      by force
    from this
    show ?thesis 
      by blast
  qed
  from this obtain q_acc where
  q_acc_def: "epsilon_reachable q' q_acc (\<Delta>e' \<A>) \<and> q_acc \<in> \<F>e \<A>"
    by auto

  from add_prefix[of \<A> q x q' q_ini, OF reachableqxq'] 
      q_ini_def
  have leftass: "LTS_is_reachable_epsilon (\<Delta>e \<A>) (\<Delta>e' \<A>) q_ini x q'"
    by auto

  from add_suffix[OF leftass, of q_acc] q_acc_def
  have "LTS_is_reachable_epsilon (\<Delta>e \<A>) (\<Delta>e' \<A>) q_ini x q_acc"
    by auto
  from this
  show "x \<in> {w. \<exists>q\<in>\<I>e \<A>.
                 Bex (\<F>e \<A>) (LTS_is_reachable_epsilon (\<Delta>e \<A>) (\<Delta>e' \<A>) q w)}"
    using q_acc_def q_ini_def by blast
}
qed

end













