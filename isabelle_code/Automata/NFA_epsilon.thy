
theory NFA_epsilon

imports Main LTS_set 

begin

fun epsilon_reach :: "'q list \<Rightarrow> ('q * 'q) set \<Rightarrow> bool" where
  "epsilon_reach [] D = True" |
  "epsilon_reach [q] D = True" |
  "epsilon_reach (q1#q2#l) D = ((q1,q2) \<in> D \<and> epsilon_reach (q2 # l) D)"

lemma epsilon_reach_concat:
  fixes l1 l2 q q' \<Delta>' q''
  assumes pre: "l1 \<noteq> [] \<and> epsilon_reach l1 \<Delta>' \<and> hd l1 = q \<and> last l1 = q' \<and> 
                l2 \<noteq> [] \<and> epsilon_reach l2 \<Delta>' \<and> hd l2 = q' \<and> last l2 = q''"
  shows  "epsilon_reach (l1 @ (tl l2)) \<Delta>' \<and> hd (l1 @ (tl l2)) = q \<and> 
          last (l1 @ (tl l2)) = q''"
      apply (rule conjI)
      defer
      apply (metis hd_append2 pre last.simps last_appendR 
                    list.exhaust_sel self_append_conv)
  apply (subgoal_tac "epsilon_reach l1 \<Delta>' \<and> last l1 = hd l2")
   defer
  using pre apply auto[1]
      apply (induction l1)
      apply simp
      apply (metis epsilon_reach.elims(3) 
                      epsilon_reach.simps(3) hd_Cons_tl pre)
      apply simp
    proof - 
      {
        fix a l1
        assume ind_hyp: "epsilon_reach l1 \<Delta>' \<and> last l1 = hd l2 \<Longrightarrow> 
                         epsilon_reach (l1 @ tl l2) \<Delta>'"
           and p1: "epsilon_reach (a # l1) \<Delta>' \<and> 
                        (if l1 = [] then a else last l1) = hd l2"
        
        from  p1
        show "epsilon_reach (a # l1 @ tl l2) \<Delta>'" 
          apply (induction l1 arbitrary: a)
          apply simp
          apply (metis pre list.exhaust_sel)
          by auto
      }
    qed


definition epsilon_reachable :: "'q \<Rightarrow> 'q \<Rightarrow> ('q * 'q) set \<Rightarrow> bool" where
  "epsilon_reachable q q' \<Delta>' \<equiv> 
          (\<exists> l. l \<noteq> [] \<and> epsilon_reach l \<Delta>' \<and> hd l = q \<and> last l = q') "


fun LTS_is_reachable_epsilon :: "('q, 'a) LTS \<Rightarrow> ('q * 'q) set
                                   \<Rightarrow> 'q \<Rightarrow> 'a list \<Rightarrow> 'q \<Rightarrow> bool" 
 where
   "LTS_is_reachable_epsilon \<Delta> \<Delta>' q [] q' = (\<exists> l. l \<noteq> [] \<and> epsilon_reach l \<Delta>' \<and> 
                                              (hd l) = q \<and> last l = q')"
 | "LTS_is_reachable_epsilon \<Delta> \<Delta>' q (a # w) q' = 
      (\<exists> qi qj \<sigma>. epsilon_reachable q qi \<Delta>' \<and> 
              a \<in> \<sigma> \<and> (qi, \<sigma>, qj) \<in> \<Delta> \<and> 
              LTS_is_reachable_epsilon \<Delta> \<Delta>' qj w q')"

  

lemma LTS_is_reachable_epsilon_add_empty_head:
  fixes q q' \<Delta> \<Delta>' \<pi>
  assumes pre: "epsilon_reachable q q' \<Delta>' \<and> LTS_is_reachable_epsilon \<Delta> \<Delta>' q' \<pi> q''"
  shows "LTS_is_reachable_epsilon \<Delta> \<Delta>' q \<pi> q''"
  using pre
  apply (induction \<pi>)
  unfolding epsilon_reachable_def
   apply simp
proof -
  {
    assume p1: "(\<exists>l. l \<noteq> [] \<and> epsilon_reach l \<Delta>' \<and> hd l = q \<and> last l = q') \<and>
    (\<exists>l. l \<noteq> [] \<and> epsilon_reach l \<Delta>' \<and> hd l = q' \<and> last l = q'')"
    from this obtain l1 l2 where l12_def: 
    "l1 \<noteq> [] \<and> epsilon_reach l1 \<Delta>' \<and> hd l1 = q \<and> last l1 = q' \<and> 
     l2 \<noteq> [] \<and> epsilon_reach l2 \<Delta>' \<and> hd l2 = q' \<and> last l2 = q''"
      by blast
    from this have l1_reach: "epsilon_reach l1 \<Delta>' \<and> last l1 = hd l2" by auto
    have "epsilon_reach (l1 @ (tl l2)) \<Delta>' \<and> hd (l1 @ (tl l2)) = q \<and> 
          last (l1 @ (tl l2)) = q''"
      apply (rule conjI)
      defer
      apply (metis hd_append2 l12_def last.simps last_appendR 
                    list.exhaust_sel self_append_conv)
      using l1_reach
      apply (induction l1)
      apply simp
      apply (metis epsilon_reach.elims(3) 
                      epsilon_reach.simps(3) hd_Cons_tl l12_def)
      apply simp
    proof - 
      {
        fix a l1
        assume ind_hyp: "epsilon_reach l1 \<Delta>' \<and> last l1 = hd l2 \<Longrightarrow> 
                         epsilon_reach (l1 @ tl l2) \<Delta>'"
           and p1: "epsilon_reach (a # l1) \<Delta>' \<and> 
                        (if l1 = [] then a else last l1) = hd l2"
        
        from  p1
        show "epsilon_reach (a # l1 @ tl l2) \<Delta>'" 
          apply (induction l1 arbitrary: a)
          apply simp
          apply (metis l12_def list.exhaust_sel)
          by auto
      }
    qed
    from this
    show "\<exists>l. l \<noteq> [] \<and> epsilon_reach l \<Delta>' \<and> hd l = q \<and> last l = q''"
      using l12_def by blast
  }
  {
    fix a \<pi>
    assume ind_hyp: "(\<exists>l. l \<noteq> [] \<and> epsilon_reach l \<Delta>' \<and> hd l = q \<and> last l = q') \<and>
            LTS_is_reachable_epsilon \<Delta> \<Delta>' q' \<pi> q'' \<Longrightarrow>
            LTS_is_reachable_epsilon \<Delta> \<Delta>' q \<pi> q''"
       and p1: "(\<exists>l. l \<noteq> [] \<and> epsilon_reach l \<Delta>' \<and> hd l = q \<and> last l = q') \<and>
           LTS_is_reachable_epsilon \<Delta> \<Delta>' q' (a # \<pi>) q''"

    from p1 obtain l1 where
    l1_def: "l1 \<noteq> [] \<and> epsilon_reach l1 \<Delta>' \<and> hd l1 = q \<and> last l1 = q'" 
      by blast

    from p1 LTS_is_reachable_epsilon.simps(2)[of \<Delta> \<Delta>' q' a \<pi> q'']
    obtain qi qj \<sigma> where
     qij\<sigma>_def: "epsilon_reachable q' qi \<Delta>' \<and>
        a \<in> \<sigma> \<and> (qi, \<sigma>, qj) \<in> \<Delta> \<and> LTS_is_reachable_epsilon \<Delta> \<Delta>' qj \<pi> q''"
      by auto

    from this 
    obtain l2 where 
    l2_def: "l2 \<noteq> [] \<and> epsilon_reach l2 \<Delta>' \<and> hd l2 = q' \<and> last l2 = qi"
      unfolding epsilon_reachable_def
      by auto

    from l2_def l1_def epsilon_reach_concat[of l1 \<Delta>' q q' l2 qi]
    have "epsilon_reach (l1 @ tl l2) \<Delta>' \<and> 
              hd (l1 @ tl l2) = q \<and> last (l1 @ tl l2) = qi"
      by simp
    from this epsilon_reachable_def[of q qi \<Delta>']
    have "epsilon_reachable q qi \<Delta>'"
      using l1_def by blast
    from this LTS_is_reachable_epsilon.simps(2)[of \<Delta> \<Delta>' q a \<pi> q'']
    show "LTS_is_reachable_epsilon \<Delta> \<Delta>' q (a # \<pi>) q''"
      using qij\<sigma>_def by blast
  }
qed

record ('q,'a) NFAe_rec =
  \<Q>e :: "'q set"           (* The set of states *)
  \<Delta>e :: "('q,'a) LTS"      (* The transition relation *)
  \<Delta>e' :: "('q * 'q) set"   (* epsilon transition *)
  \<I>e :: "'q set"            (* The set of initial states *)
  \<F>e :: "'q set"           (* The set of final states *)

locale NFAe =  
  fixes \<A> :: "('q, 'a) NFAe_rec" 
  assumes \<Delta>_consistent: "\<And>q \<sigma> q'. (q, \<sigma>, q') \<in> \<Delta>e \<A>
                \<Longrightarrow> (q \<in> \<Q>e \<A>) \<and> (q' \<in> \<Q>e \<A>)"
      and \<Delta>'_consistent: "\<And>q q'. (q, q') \<in> \<Delta>e' \<A>
                \<Longrightarrow> (q \<in> \<Q>e \<A>)  \<and> (q' \<in> \<Q>e \<A>)"
      and \<I>_consistent: "\<I>e \<A> \<subseteq> \<Q>e \<A>"
      and \<F>_consistent: "\<F>e \<A> \<subseteq> \<Q>e \<A>"
      and finite_\<Q>: "finite (\<Q>e \<A>)"

definition NFAe_accept :: "('a, 'b) NFAe_rec \<Rightarrow> 'b list \<Rightarrow> bool" where
  "NFAe_accept \<A> w = (\<exists> q \<in> (\<I>e \<A>). \<exists> q' \<in> (\<F>e \<A>). 
                 LTS_is_reachable_epsilon (\<Delta>e \<A>) (\<Delta>e' \<A>) q w q')"


definition \<L>e where "\<L>e \<A> = {w. NFAe_accept \<A> w}"

end