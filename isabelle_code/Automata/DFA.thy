(*  Title:       Deterministic Finite Automata
    Authors:     Shuanglong Kan <shuanglong@cs.uni-kl.de>
                 Thomas Tuerk <tuerk@in.tum.de>
                 Petra Dietrich <petra@ecs.vuw.ac.nz>

    using Peter Lammich <peter.lammich@uni-muenster.de> work on
    Finite state machines
*)

(* Deterministic Finite Automata *)

theory DFA
imports Main LTS_set NFA_set_interval "Deriving.Derive"

begin

derive linorder "('a \<times> 'a) list"

(* Basic Definitions *)

definition NFA_is_deterministic :: "('q, 'a) NFA_rec \<Rightarrow> bool" where
  "NFA_is_deterministic \<A> \<equiv>
   (LTS_is_deterministic (\<Q> \<A>) (\<Sigma> \<A>) (\<Delta> \<A>) \<and> (\<exists>q0. \<I> \<A> = {q0}))"

definition NFA_is_weak_deterministic :: "('q, 'a) NFA_rec \<Rightarrow> bool" where
  "NFA_is_weak_deterministic \<A> \<equiv>
   (LTS_is_weak_deterministic (\<Delta> \<A>) \<and> (\<exists>q0. \<I> \<A> = {q0}))"




locale weak_detNFA = 
  fixes \<A>::"('q,'a) NFA_rec"
  assumes deterministic_LTS: "NFA_is_weak_deterministic \<A>"

locale weak_DFA = weak_detNFA \<A> + NFA \<A>
  for \<A>::"('q,'a) NFA_rec"

lemma (in weak_DFA) det_weak_NFA : "weak_detNFA \<A>" by unfold_locales
lemma (in weak_DFA) wf_weak_DFA : "weak_DFA \<A>" by unfold_locales

lemma weak_DFA_alt_def :
  "weak_DFA \<A> \<equiv> NFA_is_weak_deterministic \<A> \<and> NFA \<A>"
  by (simp add: weak_DFA_def weak_detNFA_def)

lemma weak_DFA_implies_NFA[simp] :
  "weak_DFA \<A> \<Longrightarrow> NFA \<A>" unfolding weak_DFA_alt_def by simp


lemma (in weak_detNFA) weak_deterministic : 
      "LTS_is_weak_deterministic (\<Delta> \<A>) \<and> (\<exists>q0. \<I> \<A> = {q0})"
  using deterministic_LTS
  by (simp add: NFA_is_weak_deterministic_def)



(* The unique initial state *)

lemma (in weak_detNFA) unique_initial : "\<exists>! x. x \<in> \<I> \<A>"
using weak_deterministic by (auto) 

(* the destruction function of the initial state *)
definition \<i> :: "('a, 'b) NFA_rec \<Rightarrow> 'a" 
            where "\<i> \<A> \<equiv> SOME q. q \<in> \<I> \<A>"

lemma (in weak_detNFA) \<I>_is_set_\<i> [simp] : "\<I> \<A> = {\<i> \<A>}"
proof -
  obtain x where x: "\<I> \<A> = {x}" using unique_initial by blast
  then show "\<I> \<A> = {\<i> \<A>}" unfolding \<i>_def by simp
qed

definition \<delta> where "\<delta> \<A> \<equiv> LTS_to_DLTS (\<Delta> \<A>)"

lemma (in weak_DFA) \<delta>_to_\<Delta> [simp] : "DLTS_to_LTS (\<delta> \<A>) = \<Delta> \<A>"
  by (simp add: \<delta>_def LTS_to_DLTS_inv weak_deterministic )


lemma (in weak_DFA) weak_DFA_LTS_is_reachable_DLTS_reach_simp :
  "(\<exists> \<pi>. inPath w \<pi> \<and> (DLTS_reach (\<delta> \<A>) q \<pi> = Some q'))
           \<longleftrightarrow>  LTS_is_reachable (\<Delta> \<A>) q w q'"
  apply (simp add: eq_iff) 
  apply (simp add: LTS_is_reachable_weak_determistic weak_deterministic \<delta>_def)
  apply (rule_tac conjI)
  apply (rule impI)+
  defer
  apply (rule impI)  
proof -
  {
    assume left: "(\<exists>\<pi>. inPath w \<pi> \<and> DLTS_reach (LTS_to_DLTS (\<Delta> \<A>)) q \<pi> = Some q')"
    from this obtain \<pi>
      where \<pi>_def: "inPath w \<pi> \<and> DLTS_reach (LTS_to_DLTS (\<Delta> \<A>)) q \<pi> = Some q'"
      by auto
    from \<pi>_def
    show "LTS_is_reachable (\<Delta> \<A>) q w q'"
      apply (induction w arbitrary: \<pi> q')
      using LTS_is_reachable_DLTS_to_LTS apply fastforce
      by (metis LTS_is_reachable_DLTS_to_LTS \<delta>_def \<delta>_to_\<Delta>)
  }
  {
    assume right: "LTS_is_reachable (\<Delta> \<A>) q w q'"
    from this
    show "\<exists>\<pi>. inPath w \<pi> \<and> DLTS_reach (LTS_to_DLTS (\<Delta> \<A>)) q \<pi> = Some q'"
      apply (induction w arbitrary: q)
      using inPath.simps(1) apply fastforce
      by (meson LTS_is_deterministic_def 
                LTS_is_reachable_weak_determistic3 weak_deterministic)
  }
qed



locale detNFA = 
  fixes \<A>::"('q,'a) NFA_rec"
  assumes deterministic_NFA: "NFA_is_deterministic \<A>"

(* DFA is well-formed (checked by locale NFA) and 
   deterministic (checked by locale detNFA) *)
locale DFA = detNFA \<A> + NFA \<A>
  for \<A>::"('q,'a) NFA_rec"


lemma (in DFA) det_NFA : "detNFA \<A>" by unfold_locales
lemma (in DFA) wf_DFA : "DFA \<A>" by unfold_locales

lemma DFA_alt_def :
  "DFA \<A> \<equiv> NFA_is_deterministic \<A> \<and> NFA \<A>"
by (simp add: DFA_def detNFA_def)

lemma DFA_implies_NFA[simp] :
  "DFA \<A> \<Longrightarrow> NFA \<A>" unfolding DFA_alt_def by simp


lemma (in detNFA) deterministic : 
      "LTS_is_deterministic (\<Q> \<A>) (\<Sigma> \<A>) (\<Delta> \<A>) \<and> (\<exists>q0. \<I> \<A> = {q0})"
using deterministic_NFA by (simp add: NFA_is_deterministic_def)

(* The unique initial state *)

lemma (in detNFA) unique_initial : "\<exists>! x. x \<in> \<I> \<A>"
using deterministic by (auto) 


lemma (in detNFA) \<I>_is_set_\<i> [simp] : "\<I> \<A> = {\<i> \<A>}"
proof -
  obtain x where x: "\<I> \<A> = {x}" using unique_initial by blast
  then show "\<I> \<A> = {\<i> \<A>}" unfolding \<i>_def by simp
qed

lemma (in DFA) \<i>_is_state : "\<i> \<A> \<in> \<Q> \<A>" using \<I>_consistent by simp
lemma (in DFA) \<Q>_not_Emp: "\<Q> \<A> \<noteq> {}" using \<i>_is_state by auto

lemma (in detNFA) \<L>_in_state_\<i> : "\<L>_in_state \<A> (\<i> \<A>) = \<L> \<A>" 
       using \<L>_alt_def by force

subsection \<open> The unique transition function \<close>



lemma (in DFA) \<delta>_to_\<Delta> [simp] : "DLTS_to_LTS (\<delta> \<A>) = \<Delta> \<A>"
  apply (simp add: \<delta>_def LTS_to_DLTS_inv deterministic )
  using LTS_is_deterministic_def[of "\<Q> \<A>" "\<Delta> \<A>"] deterministic
        LTS_to_DLTS_inv[of "\<Delta> \<A>"]
  by (simp add: LTS_is_deterministic_def)

lemma (in detNFA) \<delta>_in_\<Delta>_iff :
  "(q, \<sigma>, q') \<in> \<Delta> \<A> \<longleftrightarrow> (\<delta> \<A>) (q, \<sigma>) = Some q'"
  unfolding \<delta>_def 
  using LTS_to_DLTS_is_some_det deterministic
        LTS_is_deterministic_def
  by (simp add: LTS_is_deterministic_def LTS_to_DLTS_is_some_det)

lemma (in DFA) \<delta>_wf :
  assumes "\<delta> \<A> (q,\<sigma>) = Some q'" 
  shows "q \<in> \<Q> \<A> \<and> (q' \<in> \<Q> \<A>)"
using assms
by (simp add: \<delta>_in_\<Delta>_iff [symmetric] \<Delta>_consistent)

subsection \<open> Lemmas about deterministic automata \<close>

lemma (in DFA) DFA_LTS_is_reachable_DLTS_reach_simp :
  "(\<exists> \<pi>. inPath w \<pi> \<and> (DLTS_reach (\<delta> \<A>) q \<pi> = Some q'))
           \<longleftrightarrow>  LTS_is_reachable (\<Delta> \<A>) q w q'"
  apply (simp add: eq_iff) 
  apply (simp add: LTS_is_reachable_weak_determistic deterministic \<delta>_def)
  apply (rule_tac conjI)
  apply (rule impI)+
  defer
  apply (rule impI)  
proof -
  {
    assume left: "(\<exists>\<pi>. inPath w \<pi> \<and> DLTS_reach (LTS_to_DLTS (\<Delta> \<A>)) q \<pi> = Some q')"
    from this obtain \<pi>
      where \<pi>_def: "inPath w \<pi> \<and> DLTS_reach (LTS_to_DLTS (\<Delta> \<A>)) q \<pi> = Some q'"
      by auto
    from \<pi>_def
    show "LTS_is_reachable (\<Delta> \<A>) q w q'"
      apply (induction w arbitrary: \<pi> q')
      using LTS_is_reachable_DLTS_to_LTS apply fastforce
      by (metis LTS_is_reachable_DLTS_to_LTS \<delta>_def \<delta>_to_\<Delta>)
  }
  {
    assume right: "LTS_is_reachable (\<Delta> \<A>) q w q'"
    from this
    show "\<exists>\<pi>. inPath w \<pi> \<and> DLTS_reach (LTS_to_DLTS (\<Delta> \<A>)) q \<pi> = Some q'"
      apply (induction w arbitrary: q)
      using inPath.simps(1) apply fastforce
      by (meson LTS_is_deterministic_def LTS_is_reachable_weak_determistic3 deterministic)
  }
qed

(*
lemma (in DFA) DFA_\<delta>_is_none_iff :
  "(\<delta> \<A> (q, \<sigma>) = None) \<and> \<sigma> \<noteq> {} \<longleftrightarrow> \<not> (q \<in> \<Q> \<A> \<and> \<sigma> \<noteq> {})"
apply (insert deterministic)
apply (simp add: \<delta>_def LTS_to_DLTS_def LTS_is_deterministic_def)
apply (auto simp add: \<Delta>_consistent)
done
*)

lemma (in DFA) DFA_reach_is_none_iff :
  "(\<forall> \<pi>. (inPath w \<pi> \<longrightarrow> DLTS_reach (\<delta> \<A>) q \<pi> = None)) 
       \<longleftrightarrow> \<not>((w \<noteq> [] \<longrightarrow> q \<in> \<Q> \<A>) \<and> w \<in>  lists (\<Sigma> \<A>))"

proof (induct w arbitrary: q)
  case Nil thus ?case 
    using inPath.simps(1) by fastforce
next
  case (Cons a w)
  note ind_hyp  = this
  
  from ind_hyp[of q]
  show ?case
    apply simp
  proof
    {
      assume left: "\<forall>\<pi>. inPath (a # w) \<pi> \<longrightarrow> DLTS_reach (\<delta> \<A>) q \<pi> = None"
      thm ind_hyp
      show "a \<in> \<Sigma> \<A> \<longrightarrow> q \<in> \<Q> \<A> \<longrightarrow> w \<notin> lists (\<Sigma> \<A>)"
      proof (cases "w = []")
        case True
        from this left ind_hyp
        show ?thesis 
          apply (rule_tac impI)
          apply simp
        proof 
          assume ind_hyp': "\<forall>\<pi>. inPath [a] \<pi> \<longrightarrow> DLTS_reach (\<delta> \<A>) q \<pi> = None"
             and left': "(\<And>q. \<exists>\<pi>. inPath [] \<pi> \<and> (\<exists>y. DLTS_reach (\<delta> \<A>) q \<pi> = Some y))"
             and q_in_\<A>: "q \<in> \<Q> \<A>"
             and a_in_\<Sigma>\<A>: "a \<in> \<Sigma> \<A>"
          from DFA_alt_def[of \<A>] wf_DFA
               NFA_is_deterministic_def[of \<A>]
               LTS_is_deterministic_def[of "\<Q> \<A>" "\<Sigma> \<A>" "\<Delta> \<A>"]
               q_in_\<A> a_in_\<Sigma>\<A>
          obtain q' \<alpha> where 
           q'_\<alpha>: "\<delta> \<A> (q, \<alpha>) = Some q' \<and> a \<in> \<alpha>"
            by (meson detNFA.\<delta>_in_\<Delta>_iff det_NFA)
          from this
          have "inPath [a] [\<alpha>]" 
            using inPath.simps  
            by force
          from this ind_hyp' 
          have "DLTS_reach (\<delta> \<A>) q [\<alpha>] = None"
            by blast
          from this DLTS_reach.simps
          have "\<delta> \<A> (q, \<alpha>) = None"
            by auto
          from this q'_\<alpha>
          show "False"
            by auto
        qed
      next
        case False
        from this  
        show ?thesis 
          apply auto
        proof -
          assume q_in_\<A>: "q \<in> \<Q> \<A>"
             and a_in_\<Sigma>: "a \<in> \<Sigma> \<A>"
             and w_in_\<Sigma>: "\<forall>x\<in>set w. x \<in> \<Sigma> \<A>"
          from DFA_alt_def[of \<A>]
               wf_DFA NFA_is_deterministic_def[of \<A>]
               LTS_is_deterministic_def[of "\<Q> \<A>"]
               q_in_\<A> a_in_\<Sigma>
          obtain q' \<alpha> where 
           q'_\<alpha>: "\<delta> \<A> (q, \<alpha>) = Some q' \<and> a \<in> \<alpha> \<and> q' \<in> \<Q> \<A>"
            by (metis \<delta>_in_\<Delta>_iff \<delta>_wf)

          from w_in_\<Sigma> 
          have w_in_\<Sigma>': "w \<notin> lists (\<Sigma> \<A>) = False"
            by blast
  
          from q'_\<alpha> left ind_hyp[of q'] this
          show False
            apply (simp add: w_in_\<Sigma>)
          proof - 
            assume left': "\<forall>\<pi>. inPath (a # w) \<pi> \<longrightarrow> DLTS_reach (\<delta> \<A>) q \<pi> = None"
            and ind_hyp': "\<exists>\<pi>. inPath w \<pi> \<and> (\<exists>y. DLTS_reach (\<delta> \<A>) q' \<pi> = Some y)"
            and    w_in_\<Sigma>'': "w \<in> lists (\<Sigma> \<A>)"

            from ind_hyp' 
            obtain \<pi> where
            \<pi>_def: "inPath w \<pi> \<and> (\<exists>y. DLTS_reach (\<delta> \<A>) q' \<pi> = Some y)"
              by auto 

            from this 
            have "inPath (a # w) (\<alpha> # \<pi>)"
              by (simp add: q'_\<alpha>)
            from this left'
            have "DLTS_reach (\<delta> \<A>) q (\<alpha> # \<pi>) = None"
              by blast
            from this q'_\<alpha> DLTS_reach.simps(2)[of "\<delta> \<A>" q \<alpha> \<pi>]
            have "DLTS_reach (\<delta> \<A>) q' \<pi> = None"
              by force
            from this \<pi>_def
            show False
              by auto
          qed qed qed
        }
        {
         
          thm ind_hyp
          assume q_not_\<A>: "a \<in> \<Sigma> \<A> \<longrightarrow> q \<in> \<Q> \<A> \<longrightarrow> w \<notin> lists (\<Sigma> \<A>)"
          from this 
          show "\<forall>\<pi>. inPath (a # w) \<pi> \<longrightarrow> DLTS_reach (\<delta> \<A>) q \<pi> = None"
            apply (rule_tac allI impI) 
          proof
            fix \<pi>
            assume p1: "a \<in> \<Sigma> \<A> \<longrightarrow> q \<in> \<Q> \<A> \<longrightarrow> w \<notin> lists (\<Sigma> \<A>)"  
               and p2: "inPath (a # w) \<pi>"            
            show "DLTS_reach (\<delta> \<A>) q \<pi> = None"
            proof (cases "a \<in> \<Sigma> \<A> \<and> q \<in> \<Q> \<A>")
              case True
              from this p1 
              have w_notin_\<Sigma>: "w \<notin> lists (\<Sigma> \<A>)"
                by auto
              from DFA_alt_def[of \<A>]
               wf_DFA NFA_is_deterministic_def[of \<A>]
               LTS_is_deterministic_def[of "\<Q> \<A>"]
               True 
          obtain q' \<alpha> where 
           q'_\<alpha>: "\<delta> \<A> (q, \<alpha>) = Some q' \<and> a \<in> \<alpha> \<and> q' \<in> \<Q> \<A>"
            by (metis \<delta>_in_\<Delta>_iff \<delta>_wf)
          from p2 
          obtain \<pi>' \<alpha>' where \<pi>'_def: "\<pi> = \<alpha>' # \<pi>' \<and> a \<in> \<alpha>' \<and> inPath w \<pi>'"
            using inPath.elims(2) by blast
          from ind_hyp[of q'] w_notin_\<Sigma>
          have "(\<forall>\<pi>. inPath w \<pi> \<longrightarrow> DLTS_reach (\<delta> \<A>) q' \<pi> = None)"
            by auto
          from this \<pi>'_def
          have DLTS_reach_q'_\<pi>': "DLTS_reach (\<delta> \<A>) q' \<pi>' = None"
            by auto
          from this
          show ?thesis 
          proof (cases "\<nexists> q'. (q, \<alpha>', q') \<in> \<Delta> \<A>")
            case True
            from this
            have "\<delta> \<A> (q, \<alpha>') = None"
              by (simp add: \<delta>_in_\<Delta>_iff)
            from this DLTS_reach.simps(2)[of "\<delta> \<A>" q \<alpha>' \<pi>']
                 \<pi>'_def
            show ?thesis
              by auto
          next
            case False
            from this 
            have "\<exists> q'. (q, \<alpha>', q') \<in> \<Delta> \<A> \<and> a \<in> \<alpha>'"
              using \<pi>'_def by blast
            from this obtain q'' where q''_def: "(q, \<alpha>', q'') \<in> \<Delta> \<A> \<and> a \<in> \<alpha>'"
              by auto
            from  q'_\<alpha>
            have q'_def: "(q, \<alpha>, q') \<in> \<Delta> \<A> \<and> a \<in> \<alpha> \<and> q' \<in> \<Q> \<A>"
              using \<delta>_in_\<Delta>_iff by blast
            from wf_DFA
            have "(\<forall>q \<sigma>1 \<sigma>2.
        (\<exists>q1'. (q, \<sigma>1, q1') \<in> \<Delta> \<A> \<and> (\<exists>q2'. (q, \<sigma>2, q2') \<in> \<Delta> \<A> \<and> q1' \<noteq> q2')) \<longrightarrow>
        \<sigma>1 \<inter> \<sigma>2 = {})"
              unfolding DFA_def detNFA_def NFA_is_deterministic_def
                        LTS_is_deterministic_def
                        LTS_is_weak_deterministic_def
              by blast
            from this q'_def q''_def
            have q'_eq_q'': "q' = q''"
              by blast
            from this wf_DFA 
            have "(q, \<alpha>', q') \<in> \<Delta> \<A>"
              using q''_def by blast
            from this 
            have "\<delta> \<A> (q, \<alpha>') = Some q'" 
              using \<delta>_in_\<Delta>_iff by blast
            from this DLTS_reach_q'_\<pi>' \<pi>'_def
            show ?thesis by auto
          qed
              next
                case False
                from p2
                obtain \<alpha> \<pi>' where 
                \<alpha>_\<pi>'_def: "\<pi> = \<alpha> # \<pi>' \<and> inPath w \<pi>' \<and> a \<in> \<alpha>"
                  using inPath.elims(2) by blast
                
                from wf_DFA
                have "\<forall> (q, \<alpha>, q') \<in> \<Delta> \<A>. q \<in> \<Q> \<A>"
                  unfolding DFA_def NFA_def
                  by auto
                from this 
                have "\<forall> q \<alpha>. q \<notin> \<Q> \<A> \<longrightarrow> \<delta> \<A> (q, \<alpha>) = None"
                  by (meson \<delta>_wf not_Some_eq)
                from this \<alpha>_\<pi>'_def DLTS_reach.simps(2)[of "\<delta> \<A>" q \<alpha> \<pi>']
                have cond2: "q \<notin> \<Q> \<A> \<Longrightarrow> DLTS_reach (\<delta> \<A>) q \<pi> = None"
                  by auto

                have cond1: "a \<notin> \<Sigma> \<A> \<Longrightarrow> DLTS_reach (\<delta> \<A>) q \<pi> = None"
                proof -
                  assume a_notin_\<Sigma>: "a \<notin> \<Sigma> \<A>"
                  from this \<alpha>_\<pi>'_def
                  have "\<alpha> \<subseteq> \<Sigma> \<A> = False"
                    by auto
                  show "DLTS_reach (\<delta> \<A>) q \<pi> = None"
                  proof (cases "q \<notin> \<Q> \<A>")
                  case True
                  from this cond2 
                   show ?thesis by auto
                  next
                    case False
                    from this wf_DFA
                    have "\<forall> \<alpha> q'. \<alpha> \<subseteq> \<Sigma> \<A> = False \<longrightarrow> (q, \<alpha>, q') \<notin> \<Delta> \<A>"
                      unfolding DFA_def NFA_def
                      by auto
                    from this 
                    have "\<delta> \<A> (q, \<alpha>) = None"
                      by (simp add: \<delta>_in_\<Delta>_iff \<open>(\<alpha> \<subseteq> \<Sigma> \<A>) = False\<close>)
                    from this \<alpha>_\<pi>'_def
                    show ?thesis by auto
                  qed qed

                from cond1 cond2 False
                show ?thesis 
                  by auto
              qed
            qed}
        qed
      qed

lemma (in DFA) DFA_DLTS_reach_is_some :
  "\<lbrakk>q \<in> \<Q> \<A>; w \<in> lists (\<Sigma> \<A>)\<rbrakk> \<Longrightarrow>  
   (\<exists> \<pi> q'. inPath w \<pi> \<and> DLTS_reach (\<delta> \<A>) q \<pi> = Some q' \<and> q' \<in> \<Q> \<A>)"
  using DFA_reach_is_none_iff[of w q]
  apply simp
  using DFA_LTS_is_reachable_DLTS_reach_simp 
        NFA_\<Delta>_cons___LTS_is_reachable 
  by blast


lemma (in DFA) DFA_DLTS_reach_wf : 
  "\<lbrakk> q \<in> \<Q> \<A>; DLTS_reach (\<delta> \<A>) q \<pi> = Some q'; inPath w \<pi>\<rbrakk> \<Longrightarrow>  q' \<in> \<Q> \<A>"
  using DFA_LTS_is_reachable_DLTS_reach_simp 
        NFA_\<Delta>_cons___LTS_is_reachable by blast

lemma (in DFA) DFA_left_languages___pairwise_disjoint :
assumes p_in_Q : "p \<in> \<Q> \<A>"
    and q_in_Q : "q \<in> \<Q> \<A>"
    and p_neq_Q: "p \<noteq> q"
shows "\<L>_left \<A> p \<inter> \<L>_left \<A> q = {}"
proof (rule ccontr)
  assume "\<L>_left \<A> p \<inter> \<L>_left \<A> q \<noteq> {}"
  then obtain w where "w \<in> \<L>_left \<A> p" and "w \<in> \<L>_left \<A> q" by auto
  then have "LTS_is_reachable (\<Delta> \<A>) (\<i> \<A>) w p" and 
            "LTS_is_reachable (\<Delta> \<A>) (\<i> \<A>) w q"
    unfolding \<L>_left_def by auto
  from this LTS_is_reachable_weak_determistic2  deterministic
  obtain \<pi>1 \<pi>2 where
  \<pi>1_def: "DLTS_reach (LTS_to_DLTS (\<Delta> \<A>)) (\<i> \<A>) \<pi>1 = Some p" and
  \<pi>2_def: "DLTS_reach (LTS_to_DLTS (\<Delta> \<A>)) (\<i> \<A>) \<pi>2 = Some q"
    by (metis DFA_LTS_is_reachable_DLTS_reach_simp \<delta>_def)
  from this p_neq_Q
  have "\<pi>1 \<noteq> [] \<and> \<pi>2 \<noteq> []"
    by (meson LTS_is_deterministic_def LTS_is_reachable___LTS_is_weak_deterministic 
              \<open>LTS_is_reachable (\<Delta> \<A>) (\<i> \<A>) w p\<close> \<open>LTS_is_reachable (\<Delta> \<A>) (\<i> \<A>) w q\<close> 
              deterministic)  
  from this deterministic \<pi>1_def \<pi>2_def
  show "False"
    by (meson LTS_is_deterministic_def 
              LTS_is_reachable___LTS_is_weak_deterministic 
              \<open>LTS_is_reachable (\<Delta> \<A>) (\<i> \<A>) w p\<close> 
              \<open>LTS_is_reachable (\<Delta> \<A>) (\<i> \<A>) w q\<close> p_neq_Q)  
qed

lemma (in DFA) DFA_accept_alt_def :
  "NFA_accept \<A> w = 
   (\<exists> \<pi> q'. inPath w \<pi> \<and> (DLTS_reach (\<delta> \<A>) (\<i> \<A>) \<pi>) = Some q' \<and> q' \<in> \<F> \<A>)"
  apply (simp add: NFA_accept_wf_def wf_NFA Bex_def DFA_LTS_is_reachable_DLTS_reach_simp
         split: option.split)
proof 
  {
    assume p1: "\<exists>x. x \<in> \<F> \<A> \<and> LTS_is_reachable (\<Delta> \<A>) (\<i> \<A>) w x"
    from p1 obtain q' where
    q'_def: "q' \<in> \<F> \<A> \<and> LTS_is_reachable (\<Delta> \<A>) (\<i> \<A>) w q'"
      by auto
    from deterministic q'_def LTS_is_reachable_weak_determistic3[of "\<Delta> \<A>" "\<i> \<A>" w q']
    show "\<exists>\<pi>. inPath w \<pi> \<and> (\<exists>q'. DLTS_reach (\<delta> \<A>) (\<i> \<A>) \<pi> = Some q' \<and> q' \<in> \<F> \<A>)"
      using DFA_LTS_is_reachable_DLTS_reach_simp by blast   
  }
  {
    assume p1: "\<exists>\<pi>. inPath w \<pi> \<and> 
                    (\<exists>q'. DLTS_reach (\<delta> \<A>) (\<i> \<A>) \<pi> = Some q' \<and> q' \<in> \<F> \<A>)"
    from p1 obtain \<pi> q' where
    \<pi>_q'_def: "inPath w \<pi> \<and> DLTS_reach (\<delta> \<A>) (\<i> \<A>) \<pi> = Some q' \<and> q' \<in> \<F> \<A>"
      by blast
    from this deterministic
    show "\<exists>x. x \<in> \<F> \<A> \<and> LTS_is_reachable (\<Delta> \<A>) (\<i> \<A>) w x"
      using DFA_LTS_is_reachable_DLTS_reach_simp by blast
  }qed
  
  

lemma \<L>_in_state___DFA___eq_reachable_step :
assumes DFA_\<A>: "DFA \<A>"
    and DFA_\<A>': "DFA \<A>'"
    and in_D1: "(q1, \<sigma>, q1') \<in> \<Delta> \<A>"
    and in_D2: "(q2, \<sigma>, q2') \<in> \<Delta> \<A>'"
    and \<sigma>_nemp: "\<sigma> \<noteq> {}"
    and lang_eq : "\<L>_in_state \<A> q1 = \<L>_in_state \<A>' q2"
shows "\<L>_in_state \<A> q1' = \<L>_in_state \<A>' q2'"
proof -
  interpret DFA1 : DFA \<A> by (fact DFA_\<A>)    
  interpret DFA2 : DFA \<A>' by (fact DFA_\<A>')    

  from DFA1.deterministic in_D1 have q1'_unique: 
     "\<And>q1''. (q1, \<sigma>, q1'') \<in> \<Delta> \<A> = (q1'' = q1')"
    using DFA1.\<delta>_in_\<Delta>_iff by auto

  from DFA2.deterministic in_D2 have q2'_unique: 
     "\<And>q2''. (q2, \<sigma>, q2'') \<in> \<Delta> \<A>' = (q2'' = q2')"
    using DFA2.\<delta>_in_\<Delta>_iff by auto

  thm \<L>_in_state_remove_prefix
  from lang_eq 
  have remove_eq: "\<Union> {remove_prefix [a] (\<L>_in_state \<A> q1) | a. a \<in> \<sigma>} = 
        \<Union> {remove_prefix [a] (\<L>_in_state \<A>' q2) | a. a \<in> \<sigma>}" by simp
  from DFA1.deterministic in_D1
  have q1'_unique: "\<exists>! q'. (q1, \<sigma>, q') \<in> \<Delta> \<A>"
    by (simp add: q1'_unique)

  from DFA2.deterministic in_D2
  have q2'_unique: "\<exists>! q'. (q2, \<sigma>, q') \<in> \<Delta> \<A>'"
    by (simp add: q2'_unique)

  from q1'_unique
  have "\<Union>{\<L>_in_state \<A> q' |q'. (q1, \<sigma>, q') \<in> \<Delta> \<A>} = 
        \<Union>{\<L>_in_state \<A> q1'}"
    using in_D1 by blast

  from q2'_unique
  have "\<Union>{\<L>_in_state \<A>' q' |q'. (q2, \<sigma>, q') \<in> \<Delta> \<A>'} = 
        \<Union>{\<L>_in_state \<A>' q2'}"
    using in_D2 by blast

  thm \<L>_in_state_remove_prefix[of _ \<A> q1] DFA1.deterministic
       q1'_unique in_D1
  have aq1: "\<L>_right \<A> q1' = \<Union> {remove_prefix [a] (\<L>_right \<A> q1) | a . a \<in> \<sigma>}"
       unfolding \<L>_in_state_def remove_prefix_def
       apply (auto)
     proof -
       {
         fix x xa
         assume pr1: "xa \<in> \<F> \<A>"
            and pr2: "LTS_is_reachable (\<Delta> \<A>) q1' x xa"    
         from \<sigma>_nemp
         obtain ax where ax_def:  "ax \<in> \<sigma>" by blast
         have c1: "LTS_is_reachable (\<Delta> \<A>) q1 (ax # x) xa \<and> xa \<in> \<F> \<A>"
           using \<open>ax \<in> \<sigma>\<close> in_D1 pr2 pr1 by auto
       
         have "\<exists> xa . (xa =
                 drop (Suc 0) `
                 ({w. \<exists>x\<in>\<F> \<A>. LTS_is_reachable (\<Delta> \<A>) q1 w x} \<inter>
                  {uu. \<exists>w. uu = ax # w}) \<and>
                 ax \<in> \<sigma>) \<and> x \<in> xa"
           apply simp
           apply (rule conjI)
           using ax_def apply simp
         proof -
           from c1 have "ax # x \<in> {w. \<exists>x\<in>\<F> \<A>. LTS_is_reachable (\<Delta> \<A>) q1 w x} \<inter> {uu. \<exists>w. uu = ax # w}"
             by blast 
           from this show 
           "x \<in> drop (Suc 0) `
         ({w. \<exists>x\<in>\<F> \<A>. LTS_is_reachable (\<Delta> \<A>) q1 w x} \<inter> {uu. \<exists>w. uu = ax # w})"
             by force
         qed
         from this
         show "\<exists>xa. (\<exists>a. xa =
                 drop (Suc 0) `
                 ({w. \<exists>x\<in>\<F> \<A>. LTS_is_reachable (\<Delta> \<A>) q1 w x} \<inter>
                  {uu. \<exists>w. uu = a # w}) \<and>
                 a \<in> \<sigma>) \<and>
            x \<in> xa"
           by blast 
       }
       {
         fix a xb w q'' \<sigma>'
         assume pt1: "a \<in> \<sigma>"
            and pt2: "xb \<in> \<F> \<A>"
            and pt3: "a \<in> \<sigma>'"
            and pt4: "(q1, \<sigma>', q'') \<in> \<Delta> \<A>"
            and pt5: "LTS_is_reachable (\<Delta> \<A>) q'' w xb"
         from pt1 pt3 pt4 in_D1 DFA1.deterministic
         have "q'' = q1'" 
           using LTS_is_weak_deterministic_def LTS_is_deterministic_def
           by (metis (no_types, lifting) Int_iff empty_iff)
         from this pt5 pt2
         show "\<exists>x\<in>\<F> \<A>. LTS_is_reachable (\<Delta> \<A>) q1' w x"
           by blast
       } qed

  have aq2: "\<L>_right \<A>' q2' = \<Union> {remove_prefix [a] (\<L>_right \<A>' q2) | a . a \<in> \<sigma>}"
       unfolding \<L>_in_state_def remove_prefix_def
       apply (auto)
     proof -
       {
         fix x xa
         assume pr1: "xa \<in> \<F> \<A>'"
            and pr2: "LTS_is_reachable (\<Delta> \<A>') q2' x xa"    
         from \<sigma>_nemp
         obtain ax where ax_def:  "ax \<in> \<sigma>" by blast
         have c1: "LTS_is_reachable (\<Delta> \<A>') q2 (ax # x) xa \<and> xa \<in> \<F> \<A>'"
           using \<open>ax \<in> \<sigma>\<close> in_D2 pr2 pr1 by auto
       
         have "\<exists> xa . (xa =
                 drop (Suc 0) `
                 ({w. \<exists>x\<in>\<F> \<A>'. LTS_is_reachable (\<Delta> \<A>') q2 w x} \<inter>
                  {uu. \<exists>w. uu = ax # w}) \<and>
                 ax \<in> \<sigma>) \<and> x \<in> xa"
           apply simp
           apply (rule conjI)
           using ax_def apply simp
         proof -
           from c1 have "ax # x \<in> {w. \<exists>x\<in>\<F> \<A>'. LTS_is_reachable (\<Delta> \<A>') q2 w x} 
                          \<inter> {uu. \<exists>w. uu = ax # w}"
             by blast 
           from this show 
           "x \<in> drop (Suc 0) `
         ({w. \<exists>x\<in>\<F> \<A>'. LTS_is_reachable (\<Delta> \<A>') q2 w x} \<inter> {uu. \<exists>w. uu = ax # w})"
             by force
         qed
         from this
         show "\<exists>xa. (\<exists>a. xa =
                 drop (Suc 0) `
                 ({w. \<exists>x\<in>\<F> \<A>'. LTS_is_reachable (\<Delta> \<A>') q2 w x} \<inter>
                  {uu. \<exists>w. uu = a # w}) \<and>
                 a \<in> \<sigma>) \<and>
            x \<in> xa"
           by blast 
       }
       {
         fix a xb w q'' \<sigma>'
         assume pt1: "a \<in> \<sigma>"
            and pt2: "xb \<in> \<F> \<A>'"
            and pt3: "a \<in> \<sigma>'"
            and pt4: "(q2, \<sigma>', q'') \<in> \<Delta> \<A>'"
            and pt5: "LTS_is_reachable (\<Delta> \<A>') q'' w xb"
         from pt1 pt3 pt4 in_D2 DFA2.deterministic
         have "q'' = q2'" 
           using LTS_is_deterministic_def
                 LTS_is_weak_deterministic_def
           by (metis (no_types, hide_lams) insert_disjoint(2) insert_subset subsetI subset_antisym)
         from this pt5 pt2
         show "\<exists>x\<in>\<F> \<A>'. LTS_is_reachable (\<Delta> \<A>') q2' w x"
           by blast
       } qed

     from aq1 aq2 
     show "\<L>_right \<A> q1' = \<L>_right \<A>' q2'"
       by (simp add: remove_eq)
qed
(*
lemma \<L>_in_state___DFA___eq_DLTS_reachable :
assumes DFA_\<A>: "DFA \<A>"
    and DFA_\<A>': "DFA \<A>'"
    and DLTS_reach_1: "LTS_is_reachable (\<Delta> \<A>) q1 w q1'"
    and DLTS_reach_2: "LTS_is_reachable (\<Delta> \<A>') q2 w q2'"
    and lang_eq : "\<L>_in_state \<A> q1 = \<L>_in_state \<A>' q2"
  shows "\<L>_in_state \<A> q1' = \<L>_in_state \<A>' q2'"

using DLTS_reach_1 DLTS_reach_2 lang_eq
proof (induct w arbitrary: q1 q2)
  case Nil thus ?thesis by simp
next
  case (Cons a w)
  note ind_hyp = Cons (1)
  note DLTS_reach_1 = Cons (2)
  note DLTS_reach_2 = Cons (3)
  note lang_eq = Cons (4)

  from DLTS_reach_1 obtain q1'' \<sigma> where 
      in_D1 : "(q1, \<sigma>, q1'') \<in> (\<Delta> \<A>) \<and> a \<in> \<sigma>" and
  DLTS_reach_1' : "LTS_is_reachable (\<Delta> \<A>) q1'' w q1'" 
    by auto
  from DLTS_reach_2 obtain q2'' where 
      in_D2 : "(q2, \<sigma>, q2'') \<in> (\<Delta> \<A>')" and
  DLTS_reach_2' : "LTS_is_reachable (\<Delta> \<A>') q2'' w q2'" 
    by auto
  from in_D1 
  have in_D1': "(q1, \<sigma>1, q1'') \<in> (\<Delta> \<A>)" by auto
  thm \<L>_in_state___DFA___eq_reachable_step[OF DFA_\<A> DFA_\<A>' ]

  have lang_eq' : "\<L>_in_state \<A> q1'' = \<L>_in_state \<A>' q2''"
    by (fact \<L>_in_state___DFA___eq_reachable_step 
              [OF DFA_\<A> DFA_\<A>' in_D1 in_D2 lang_eq])

  note ind_hyp [OF DLTS_reach_1' DLTS_reach_2' lang_eq']
  thus ?thesis by assumption
qed
*)

lemma (in weak_DFA) NFA_is_weak_deterministic___inj_rename :
assumes inj_f: "inj_on f (\<Q> \<A>)"
shows "NFA_is_weak_deterministic (NFA_rename_states \<A> f)"
proof -
  have step1: 
    "\<And>\<sigma>1 \<sigma>2 s1 s1' s2 s2'.
       \<lbrakk>f s1 = f s1'; (s1, \<sigma>1, s2) \<in> \<Delta> \<A>; (s1', \<sigma>2, s2') \<in> \<Delta> \<A>; f s2 \<noteq> f s2'\<rbrakk> 
          \<Longrightarrow> \<sigma>1 \<noteq> {} \<and> \<sigma>2 \<noteq> {} \<and> \<sigma>1 \<inter> \<sigma>2 = {}"
  proof -
    fix \<sigma>1 \<sigma>2 s1 s1' s2 s2'
    assume in_D: "(s1, \<sigma>1, s2) \<in> \<Delta> \<A>" 
       and in_D': "(s1', \<sigma>2, s2') \<in> \<Delta> \<A>"
       and s1_s1'_f: "f s1 = f s1'"
       and s2_s2'_f: "f s2 \<noteq> f s2'"
    
    from \<Delta>_consistent in_D have s1_in: "s1 \<in> \<Q> \<A>" by fast
    from \<Delta>_consistent in_D' have s1'_in: "s1' \<in> \<Q> \<A>" by fast

    from s1_s1'_f s1_in s1'_in inj_f 
    have s1_eq: "s1 = s1'"
      unfolding inj_on_def by simp
    
    from weak_deterministic this inj_f
         LTS_is_deterministic_def
         LTS_is_weak_deterministic_def
    show "\<sigma>1 \<noteq> {} \<and> \<sigma>2 \<noteq> {} \<and> \<sigma>1 \<inter> \<sigma>2 = {}" 
      by (metis (no_types, lifting) in_D in_D' s2_s2'_f)
  qed
  

  show "NFA_is_weak_deterministic (NFA_rename_states \<A> f)"
    apply (simp add: NFA_is_weak_deterministic_def  
                     LTS_is_weak_deterministic_def
       NFA_rename_states_def LTS_is_deterministic_def)
    apply (simp del: ex_simps add: ex_simps[symmetric])
    apply (rule conjI)
    using LTS_is_deterministic_def[of "\<Q> \<A>" "\<Delta> \<A>"] 
          LTS_is_weak_deterministic_def[of "\<Delta> \<A>"] 
              \<Delta>_consistent weak_deterministic inj_f inj_on_eq_iff
    using step1 apply fastforce
    using inj_f
    using step1 by blast    
qed

lemma (in DFA) NFA_is_deterministic___inj_rename :
assumes inj_f: "inj_on f (\<Q> \<A>)"
shows "NFA_is_deterministic (NFA_rename_states \<A> f)"
proof -
  have step1: 
    "\<And>\<sigma>1 \<sigma>2 s1 s1' s2 s2'.
       \<lbrakk>f s1 = f s1'; (s1, \<sigma>1, s2) \<in> \<Delta> \<A>; (s1', \<sigma>2, s2') \<in> \<Delta> \<A>; f s2 \<noteq> f s2'\<rbrakk> 
          \<Longrightarrow> \<sigma>1 \<noteq> {} \<and> \<sigma>2 \<noteq> {} \<and> \<sigma>1 \<inter> \<sigma>2 = {}"
  proof -
    fix \<sigma>1 \<sigma>2 s1 s1' s2 s2'
    assume in_D: "(s1, \<sigma>1, s2) \<in> \<Delta> \<A>" 
       and in_D': "(s1', \<sigma>2, s2') \<in> \<Delta> \<A>"
       and s1_s1'_f: "f s1 = f s1'"
       and s2_s2'_f: "f s2 \<noteq> f s2'"
    
    from \<Delta>_consistent in_D have s1_in: "s1 \<in> \<Q> \<A>" by fast
    from \<Delta>_consistent in_D' have s1'_in: "s1' \<in> \<Q> \<A>" by fast

    from s1_s1'_f s1_in s1'_in inj_f 
    have s1_eq: "s1 = s1'"
      unfolding inj_on_def by simp
    
    from deterministic this inj_f
         LTS_is_deterministic_def
         LTS_is_weak_deterministic_def
    show "\<sigma>1 \<noteq> {} \<and> \<sigma>2 \<noteq> {} \<and> \<sigma>1 \<inter> \<sigma>2 = {}" 
      by (metis (no_types, lifting) in_D in_D' s2_s2'_f)
  qed
  from LTS_is_deterministic_def[of "\<Q> \<A>" "\<Sigma> \<A>" "\<Delta> \<A>"] deterministic
  have step2: "(\<forall>q\<in>\<Q> \<A>. \<forall>a \<in> \<Sigma> \<A>. \<exists>q' \<sigma>. (q, \<sigma>, q') \<in> \<Delta> \<A> \<and> a \<in> \<sigma>)"
    by fastforce

  show "NFA_is_deterministic (NFA_rename_states \<A> f)"
    apply (simp add: NFA_is_deterministic_def  
                     LTS_is_weak_deterministic_def
       NFA_rename_states_def LTS_is_deterministic_def)
    apply (simp del: ex_simps add: ex_simps[symmetric])
    apply (rule conjI)
    using LTS_is_deterministic_def[of "\<Q> \<A>" "\<Sigma> \<A>" "\<Delta> \<A>"] 
          LTS_is_weak_deterministic_def[of "\<Delta> \<A>"] 
              \<Delta>_consistent deterministic inj_f inj_on_eq_iff
    using step1 apply fastforce
    using step2 inj_f
    using step1 by blast    
qed

lemma DFA___inj_rename :
assumes DFA_\<A>: "DFA \<A>"
    and inj_f: "inj_on f (\<Q> \<A>)"
shows "DFA (NFA_rename_states \<A> f)"
using DFA_\<A> DFA.NFA_is_deterministic___inj_rename [OF DFA_\<A> inj_f]
unfolding DFA_alt_def
  by (simp add: NFA_rename_states___is_well_formed)

lemma weak_DFA___inj_rename :
assumes weak_DFA_\<A>: "weak_DFA \<A>"
    and inj_f: "inj_on f (\<Q> \<A>)"
shows "weak_DFA (NFA_rename_states \<A> f)"
using weak_DFA_\<A> weak_DFA.NFA_is_weak_deterministic___inj_rename [OF weak_DFA_\<A> inj_f]
unfolding weak_DFA_alt_def
by (simp add: NFA_rename_states___is_well_formed)

lemma NFA_isomorphic___is_well_formed_weak_DFA :
assumes wf_A1: "weak_DFA \<A>1"
    and eq_A12: "NFA_isomorphic \<A>1 \<A>2"
shows "weak_DFA \<A>2"
proof -
  from eq_A12 obtain f where
    inj_f: "inj_on f (\<Q> \<A>1)" and
    A2_eq: "\<A>2 = NFA_rename_states \<A>1 f"
    unfolding NFA_isomorphic_def by blast

  from A2_eq weak_DFA___inj_rename [OF wf_A1 inj_f]
  show "weak_DFA \<A>2" by simp
qed

lemma NFA_isomorphic___is_well_formed_DFA :
assumes wf_A1: "DFA \<A>1"
    and eq_A12: "NFA_isomorphic \<A>1 \<A>2"
shows "DFA \<A>2"
proof -
  from eq_A12 obtain f where
    inj_f: "inj_on f (\<Q> \<A>1)" and
    A2_eq: "\<A>2 = NFA_rename_states \<A>1 f"
    unfolding NFA_isomorphic_def by blast

  from A2_eq DFA___inj_rename [OF wf_A1 inj_f]
  show "DFA \<A>2" by simp
qed

lemma NFA_isomorphic_wf___DFA :
fixes \<A>1 :: "('q1, 'a) NFA_rec" and \<A>2 :: "('q2, 'a) NFA_rec"
assumes iso: "NFA_isomorphic_wf \<A>1 \<A>2"
shows "DFA \<A>1 \<longleftrightarrow> DFA \<A>2"
using assms
by (metis NFA_isomorphic_wf_sym 
          NFA_isomorphic_wf_def 
          NFA_isomorphic___is_well_formed_DFA)

lemma NFA_isomorphic_wf___weak_DFA :
fixes \<A>1 :: "('q1, 'a) NFA_rec" and \<A>2 :: "('q2, 'a) NFA_rec"
assumes iso: "NFA_isomorphic_wf \<A>1 \<A>2"
shows "weak_DFA \<A>1 \<longleftrightarrow> weak_DFA \<A>2"
using assms
by (metis NFA_isomorphic_wf_sym 
          NFA_isomorphic_wf_def 
          NFA_isomorphic___is_well_formed_weak_DFA)

lemma NFA_normalise_states_DFA [simp] :
assumes wf_A: "DFA \<A>" 
shows "DFA (NFA_normalise_states \<A>)"
by (metis NFA_isomorphic_wf_normalise_states[unfolded NFA_isomorphic_wf_def] 
    NFA_isomorphic___is_well_formed_DFA DFA_alt_def assms)


subsection \<open> Determinisation \<close>

definition determinise_NFA where
  "determinise_NFA \<A> = 
   \<lparr> \<Q> = {q | q. q \<subseteq> (\<Q> \<A>) \<and> q \<noteq> {}},
     \<Sigma> = \<Sigma> \<A>,
     \<Delta> = {(Q, \<sigma>, {q'. (\<exists> q \<in> Q. (q, \<sigma>, q') \<in> \<Delta> \<A>)}) | 
                  Q \<sigma>. Q \<subseteq> \<Q> \<A> \<and> Q \<noteq> {} \<and>  
                 (\<exists> q q'. q \<in> Q \<and> (q, \<sigma>, q') \<in> \<Delta> \<A>) \<and>
                  \<sigma> \<noteq> {}},
     \<I> = {\<I> \<A>},
     \<F> = {fs. (fs \<subseteq> (\<Q> \<A>)) \<and> (fs \<inter> \<F> \<A>) \<noteq> {}} \<rparr>"

definition uniq_label_NFA where
   "uniq_label_NFA \<A> = (\<forall> q1 \<alpha>1 q1' q2 \<alpha>2 q2'. 
                              (q1, \<alpha>1, q1') \<in> (\<Delta> \<A>) \<and> (q2, \<alpha>2, q2') \<in> (\<Delta> \<A>) \<longrightarrow> 
                              \<alpha>1 = \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {})"

definition nonempty_label_NFA where
   "nonempty_label_NFA \<A> = (\<forall> (q, \<alpha>, q') \<in> (\<Delta> \<A>). \<alpha> \<noteq> {})"

lemma [simp] : "\<I> (determinise_NFA \<A>) = {\<I> \<A>}" by (simp add: determinise_NFA_def)
lemma [simp] : "(q \<in> \<Q> (determinise_NFA \<A>)) \<longleftrightarrow> q \<subseteq> \<Q> \<A> \<and> q \<noteq> {}" 
                 by (simp add: determinise_NFA_def)
lemma [simp] : "q \<in> \<F> (determinise_NFA \<A>) \<longleftrightarrow> (q \<subseteq> (\<Q> \<A>)) \<and> q \<inter> \<F> \<A> \<noteq> {}" by (simp add: determinise_NFA_def)

lemma [simp] : "Q\<sigma>Q' \<in> \<Delta> (determinise_NFA \<A>) \<longrightarrow> 
  ((snd (snd Q\<sigma>Q') = {q'. \<exists>q\<in>(fst Q\<sigma>Q'). (q, fst (snd Q\<sigma>Q'), q') \<in> \<Delta> \<A>}) \<and>
   (fst Q\<sigma>Q' \<subseteq> \<Q> \<A>))" 
  by (cases Q\<sigma>Q', simp add: determinise_NFA_def)



lemma determinise_NFA_is_weak_detNFA :
  "uniq_label_NFA \<A> \<Longrightarrow>
   NFA_is_weak_deterministic (determinise_NFA \<A>)"
proof -
  assume uniq_label: "uniq_label_NFA \<A>"
  let ?\<A> = "determinise_NFA \<A>"
  have q0_I: "\<exists>q0. \<I> ?\<A> = {q0}" by simp
  moreover
  show "NFA_is_weak_deterministic ?\<A>"
    unfolding NFA_is_weak_deterministic_def 
              LTS_is_weak_deterministic_def  
    apply simp
    apply (insert uniq_label)
    unfolding uniq_label_NFA_def
    apply simp
  proof -
    assume uniq_label_unfold: "\<forall>q1 \<alpha>1 q1' q2 \<alpha>2.
          (q1, \<alpha>1, q1') \<in> \<Delta> \<A> \<and> (\<exists>q2'. (q2, \<alpha>2, q2') \<in> \<Delta> \<A>) \<longrightarrow>
          \<alpha>1 = \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {}"
    let ?conj1 = "(\<forall>q \<sigma>. (\<exists>q'. (q, \<sigma>, q') \<in> \<Delta> (determinise_NFA \<A>)) \<longrightarrow> \<sigma> \<noteq> {})" 
    have conj1: ?conj1
      unfolding determinise_NFA_def
      by simp
    let ?conj2 = "(\<forall>q \<sigma>1 \<sigma>2.
        (\<exists>q1'. (q, \<sigma>1, q1') \<in> \<Delta> (determinise_NFA \<A>) \<and>
               (\<exists>q2'. (q, \<sigma>2, q2') \<in> \<Delta> (determinise_NFA \<A>) \<and> q1' \<noteq> q2')) \<longrightarrow>
        \<sigma>1 \<inter> \<sigma>2 = {})"
    from uniq_label_unfold 
    have conj2: ?conj2 
      unfolding determinise_NFA_def
      apply simp
      apply (rule allI impI)+
    proof -
      fix q \<sigma>1 \<sigma>2
      assume determinise_premise: 
       "q \<subseteq> \<Q> \<A> \<and>
        q \<noteq> {} \<and> (\<exists>qa. qa \<in> q \<and> (\<exists>q'. (qa, \<sigma>1, q') \<in> \<Delta> \<A>)) \<and>
        \<sigma>1 \<noteq> {} \<and>
        q \<subseteq> \<Q> \<A> \<and> 
       q \<noteq> {} \<and> (\<exists>qa. qa \<in> q \<and> (\<exists>q'. (qa, \<sigma>2, q') \<in> \<Delta> \<A>)) \<and>
        \<sigma>2 \<noteq> {} \<and> 
        {q'. \<exists>q\<in>q. (q, \<sigma>1, q') \<in> \<Delta> \<A>} \<noteq> {q'. \<exists>q\<in>q. (q, \<sigma>2, q') \<in> \<Delta> \<A>}"
      show "\<sigma>1 \<inter> \<sigma>2 = {}"
      proof (cases "\<sigma>1 = \<sigma>2")
        case True
        from this 
        have "{q'. \<exists>q\<in>q. (q, \<sigma>1, q') \<in> \<Delta> \<A>} = {q'. \<exists>q\<in>q. (q, \<sigma>2, q') \<in> \<Delta> \<A>}"
          by auto
        from this determinise_premise
        show ?thesis by blast
      next
        case False
        show ?thesis 
        using uniq_label_unfold False determinise_premise
        by blast
      qed
    qed
    from conj1 conj2
    show "?conj1 \<and> ?conj2"
      by blast
  qed
qed

lemma determinise_NFA_is_detNFA :
  "uniq_label_NFA \<A> \<and> 
  (\<forall> q \<in> \<Q> \<A>. \<forall> a \<in> \<Sigma> \<A>. \<exists> \<alpha> q'. a \<in> \<alpha> \<and> (q, \<alpha>, q') \<in> \<Delta> \<A>)\<Longrightarrow>
   NFA_is_deterministic (determinise_NFA \<A>)"
  unfolding NFA_is_deterministic_def
            LTS_is_deterministic_def
  apply (rule conjI)
  apply (rule conjI)
  using determinise_NFA_is_weak_detNFA[of \<A>] 
        NFA_is_weak_deterministic_def
    apply auto[1]
   defer
   apply auto[1]
  apply simp
  unfolding determinise_NFA_def
  apply simp
  by blast

lemma determinise_NFA___is_well_formed :
  "NFA \<A> \<and> \<I> \<A> \<noteq> {}\<Longrightarrow> NFA (determinise_NFA \<A>)"
  apply ( simp add: NFA_def determinise_NFA_def)
  by auto

lemma determinise_NFA_is_DFA :
  "uniq_label_NFA \<A> \<and> NFA \<A> \<and> \<I> \<A> \<noteq> {} \<and> 
  (\<forall> q \<in> \<Q> \<A>. \<forall> a \<in> \<Sigma> \<A>. \<exists> \<alpha> q'. a \<in> \<alpha> \<and> (q, \<alpha>, q') \<in> \<Delta> \<A>)\<Longrightarrow>
   DFA (determinise_NFA \<A>)"
  unfolding DFA_def
  unfolding detNFA_def
  apply (rule_tac conjI)
  using determinise_NFA_is_detNFA
  apply blast
  using determinise_NFA___is_well_formed[of \<A>]
  by simp


lemma weak_det_determinise: "uniq_label_NFA \<A> \<Longrightarrow> 
      weak_detNFA (determinise_NFA \<A>)"
  by (simp add: weak_detNFA_def determinise_NFA_is_weak_detNFA)


lemma determinised_\<i> [simp] : "uniq_label_NFA \<A> \<Longrightarrow> \<i> (determinise_NFA \<A>) = \<I> \<A>" 
proof -
  assume uniq_label: "uniq_label_NFA \<A>"
  from uniq_label weak_det_determinise
  interpret  weak_det: weak_detNFA "determinise_NFA \<A>" 
    by auto
  from weak_det.\<I>_is_set_\<i> 
  show " \<i> (determinise_NFA \<A>) = \<I> \<A>"
    by force
qed

lemma determinised_\<delta> :
  "\<delta> (determinise_NFA \<A>) = (\<lambda>(Q,\<sigma>). 
     if (Q \<subseteq> (\<Q> \<A>) \<and> \<sigma> \<noteq> {} \<and> (\<exists> q q'. q \<in> Q \<and> (q, \<sigma>, q') \<in> \<Delta> \<A>)) then 
    Some {q' |q q'. q \<in> Q \<and> (q, \<sigma>, q') \<in> \<Delta> \<A>} else None)"
apply (subst fun_eq_iff, clarify)
apply (simp add: determinise_NFA_def \<delta>_def LTS_to_DLTS_def Bex_def)
done


  

lemma determinise_NFA___DFA :
  "NFA \<A> \<and> uniq_label_NFA \<A> \<and> \<I> \<A> \<noteq> {} \<Longrightarrow> weak_DFA (determinise_NFA \<A>)"
  by (simp add: determinise_NFA___is_well_formed weak_DFA_alt_def
              determinise_NFA_is_weak_detNFA)

lemma DLTS_decomp: "DLTS_reach (\<delta> \<A>) q (a#\<pi>) = Some q' \<Longrightarrow>
      (\<exists> q''.(q, a, q'') \<in> (\<Delta> \<A>) \<and> DLTS_reach (\<delta> \<A>) q'' \<pi> = Some q')"
proof -
  assume dlts_reach: "DLTS_reach (\<delta> \<A>) q (a#\<pi>) = Some q'"
  show "(\<exists> q''.(q, a, q'') \<in> (\<Delta> \<A>) \<and> DLTS_reach (\<delta> \<A>) q'' \<pi> = Some q')"
  proof (cases "\<delta> \<A> (q, a) = None")
    case True
    from True DLTS_reach.simps(2)[of "\<delta> \<A>" q a \<pi>]
    have "DLTS_reach (\<delta> \<A>) q (a#\<pi>) = None"
      by simp
    from this dlts_reach
    show ?thesis 
      by auto
  next
  case False
  from False 
  obtain q'' where 
  q''_def: "\<delta> \<A> (q, a) = Some q''"
    by blast
  from q''_def dlts_reach
  DLTS_reach.simps(2)[of "\<delta> \<A>" q a \<pi>]
  have dlts_q'': "DLTS_reach (\<delta> \<A>) q'' \<pi> = Some q'"
    by auto
  from q''_def dlts_q''
  show ?thesis
    by (metis LTS_to_DLTS_is_some \<delta>_def)   
qed
qed

lemma (in NFA) determinise_NFA___DLTS_reach_noempty :
  assumes uniq_label: "uniq_label_NFA \<A> \<and> NFA \<A>"
  shows " Q \<subseteq> \<Q> \<A> \<and> Q \<noteq> {} \<Longrightarrow>
  DLTS_reach (\<delta> (determinise_NFA \<A>)) Q \<pi> = Some Q' \<Longrightarrow> Q' \<noteq> {}"
proof (induct \<pi> arbitrary: Q)
  case Nil
  then show ?case 
    by auto
next
  case (Cons a \<pi>)
  note ind_hyp = Cons(1) 
  note QC = Cons(2)
  note ind_assu = Cons(3)
  from ind_assu DLTS_decomp[of "(determinise_NFA \<A>)" Q a \<pi> Q']
  obtain Q'' where
  Q''_def: "(Q, a, Q'') \<in> \<Delta> (determinise_NFA \<A>) \<and>
             DLTS_reach (\<delta> (determinise_NFA \<A>)) Q'' \<pi> = Some Q'"
    by auto
  from this
  have "(Q, a, Q'') \<in> \<Delta> (determinise_NFA \<A>)" by simp
  from this uniq_label
  have  "Q'' \<subseteq> \<Q> \<A> \<and> Q'' \<noteq> {}"
    unfolding determinise_NFA_def
    apply simp
    using \<Delta>_consistent by blast
  from this ind_hyp[of Q'', OF this] QC Q''_def
  show ?case 
    by auto
qed
  

lemma (in NFA) determinise_NFA___DLTS_reach :
  assumes uniq_label: "uniq_label_NFA \<A> \<and> NFA \<A> \<and> \<I> \<A> \<noteq> {}"
  shows " Q \<subseteq> \<Q> \<A> \<and> Q \<noteq> {} \<Longrightarrow>
  DLTS_reach (\<delta> (determinise_NFA \<A>)) Q \<pi> = Some Q' \<longrightarrow> 
  (\<forall> w q'. q' \<in> Q' \<and> inPath w \<pi> \<longrightarrow> 
    (\<exists> q. LTS_is_reachable (\<Delta> \<A>) q w q' \<and> q \<in> Q \<and> q' \<in> Q'))"
  apply (rule impI)
proof (induct \<pi> arbitrary: Q)
  case Nil thus ?case
    apply (rule_tac allI impI)+
  proof - 
    fix w q'
    have "\<And> w. inPath w [] \<Longrightarrow> w = []"
      using inPath.elims(2) by blast
    from this
    show "q' \<in> Q' \<and> inPath w [] \<Longrightarrow> 
            \<exists>q. LTS_is_reachable (\<Delta> \<A>) q w q' \<and> q \<in> Q \<and> q' \<in> Q'"
      using Nil.prems(1) Nil.prems(2) by fastforce
  qed
next
  case (Cons a \<pi>)
  note ind_hyp = Cons(1)
  note Q_subset = Cons(2)
  note DLTS_reach_deter = Cons(3)
  interpret DFA_detA: weak_DFA "(determinise_NFA \<A>)" 
    using determinise_NFA___DFA wf_NFA uniq_label
    by blast
  
  let ?\<A> = "determinise_NFA \<A>"
  have "LTS_is_weak_deterministic (\<Delta> ?\<A>)"
    using DFA_detA.weak_deterministic by blast
  thm DFA_detA.weak_DFA_LTS_is_reachable_DLTS_reach_simp
      LTS_to_DLTS_is_some_det
  from DLTS_reach_deter 
       DLTS_decomp[of "(determinise_NFA \<A>)" Q a \<pi> Q']
  obtain Q1 where
  Q1_def: "(Q, a, Q1) \<in> \<Delta> (determinise_NFA \<A>) \<and>
        DLTS_reach (\<delta> (determinise_NFA \<A>)) Q1 \<pi> = Some Q'"
    by auto

  
  from uniq_label
  have Q1_\<alpha>: "Q1 \<noteq> {} \<and> Q1 \<subseteq> \<Q> \<A> \<and> a \<noteq> {}"
    using Q1_def Q_subset determinise_NFA_def[of \<A>]
    apply simp
    using DFA_detA.\<Delta>_consistent by auto


  from Q1_\<alpha> 
  have Q1_subset : "Q1 \<subseteq> \<Q> \<A> \<and> Q1 \<noteq> {}"
    by simp

  show ?case
    apply (rule_tac allI impI) +
  proof -
    fix w q'
    assume inPath_w_\<alpha>_\<pi>: "q' \<in> Q' \<and> inPath w (a # \<pi>)"
    from this 
    obtain a' w' where
    a_\<pi>_def: "w = a' # w' \<and> a' \<in> a \<and> inPath w' \<pi>"
      using inPath.elims(2) by blast
        
  note ind_hyp' = ind_hyp [OF Q1_subset]
  from ind_hyp' Q1_def a_\<pi>_def inPath_w_\<alpha>_\<pi>
  obtain q'' where 
   w_q_q': "LTS_is_reachable (\<Delta> \<A>) q'' w' q' \<and> q'' \<in> Q1 \<and> q' \<in> Q'"
     by blast
  obtain q where q_def: "q \<in> Q \<and> (q, a, q'') \<in> (\<Delta> \<A>)"
    using w_q_q' Q1_def determinise_NFA_def[of \<A>]
    apply simp
    by auto
  from q_def w_q_q' a_\<pi>_def
  have "LTS_is_reachable (\<Delta> \<A>) q w q' \<and> q \<in> Q \<and> q' \<in> Q'"
    by auto
  thus "\<exists>q. LTS_is_reachable (\<Delta> \<A>) q w q' \<and> q \<in> Q \<and> q' \<in> Q'"
    by auto
qed 
qed

lemma (in NFA) determinise_NFA___DLTS_reach' :
  assumes uniq_label: "uniq_label_NFA \<A> \<and> NFA \<A> \<and> \<I> \<A> \<noteq> {}"
  shows " Q \<subseteq> \<Q> \<A> \<and> Q \<noteq> {} \<Longrightarrow>
  DLTS_reach (\<delta> (determinise_NFA \<A>)) Q \<pi> = Some Q' \<longrightarrow> 
  (\<forall> w. inPath w \<pi> \<longrightarrow> 
    (\<exists> q q'. LTS_is_reachable (\<Delta> \<A>) q w q' \<and> q \<in> Q \<and> q' \<in> Q'))"
  apply (rule impI)
proof (induct \<pi> arbitrary: Q)
  case Nil thus ?case
    apply (rule_tac allI impI)+
  proof - 
    fix w
    have "\<And> w. inPath w [] \<Longrightarrow> w = []"
      using inPath.elims(2) by blast
    from this
    show "inPath w [] \<Longrightarrow> 
            \<exists>q q'. LTS_is_reachable (\<Delta> \<A>) q w q' \<and> q \<in> Q \<and> q' \<in> Q'"
      using Nil.prems(1) Nil.prems(2) by fastforce
  qed
next
  case (Cons \<alpha> \<pi>)
  note ind_hyp = Cons(1)
  note Q_subset = Cons(2)
  note DLTS_reach_deter = Cons(3)
  interpret DFA_detA: weak_DFA "(determinise_NFA \<A>)" 
    using determinise_NFA___DFA wf_NFA uniq_label
    by blast

  let ?\<A> = "determinise_NFA \<A>"
  have "LTS_is_weak_deterministic (\<Delta> ?\<A>)"
    using DFA_detA.weak_deterministic by blast
  thm DFA_detA.weak_DFA_LTS_is_reachable_DLTS_reach_simp
      LTS_to_DLTS_is_some_det
  from DLTS_reach_deter 
       DLTS_decomp[of "(determinise_NFA \<A>)" Q \<alpha> \<pi> Q']
  obtain Q1 where
  Q1_def: "(Q, \<alpha>, Q1) \<in> \<Delta> (determinise_NFA \<A>) \<and>
        DLTS_reach (\<delta> (determinise_NFA \<A>)) Q1 \<pi> = Some Q'"
    by auto
  
  from uniq_label
  have Q1_\<alpha>: "Q1 \<noteq> {} \<and> Q1 \<subseteq> \<Q> \<A> \<and> \<alpha> \<noteq> {}"
    using Q1_def Q_subset determinise_NFA_def[of \<A>]
    apply simp
    using DFA_detA.\<Delta>_consistent by auto


  from Q1_\<alpha> 
  have Q1_subset : "Q1 \<subseteq> \<Q> \<A> \<and> Q1 \<noteq> {}"
    by simp

  show ?case
    apply (rule_tac allI impI) +
  proof -
    fix w
    assume inPath_w_\<alpha>_\<pi>: "inPath w (\<alpha> # \<pi>)"
    from this 
    obtain a w' where
    a_\<pi>_def: "w = a # w' \<and> a \<in> \<alpha> \<and> inPath w' \<pi>"
      using inPath.elims(2) by blast

  note ind_hyp' = ind_hyp [OF Q1_subset]
  from ind_hyp' Q1_def a_\<pi>_def
  obtain q'' q' where 
   w_q_q': "LTS_is_reachable (\<Delta> \<A>) q'' w' q' \<and> q'' \<in> Q1 \<and> q' \<in> Q'"
    by auto
  obtain q where q_def: "q \<in> Q \<and> (q, \<alpha>, q'') \<in> (\<Delta> \<A>)"
    using w_q_q' Q1_def determinise_NFA_def[of \<A>]
    apply simp
    by auto
  from q_def w_q_q' a_\<pi>_def
  have "LTS_is_reachable (\<Delta> \<A>) q w q' \<and> q \<in> Q \<and> q' \<in> Q'"
    by auto
  thus "\<exists>q q'. LTS_is_reachable (\<Delta> \<A>) q w q' \<and> q \<in> Q \<and> q' \<in> Q'"
    by auto
qed 
qed

lemma (in NFA) determinise_NFA___LTS_reach :
  assumes uniq_label: "uniq_label_NFA \<A> \<and> NFA \<A> \<and> \<I> \<A> \<noteq> {}"
  shows 
  "LTS_is_reachable (\<Delta> \<A>) q w q' \<and> q' \<in> (\<Q> \<A>) \<and> q \<in> (\<Q> \<A>) \<longrightarrow> 
   (\<forall> Q \<subseteq> (\<Q> \<A>). q \<in> Q \<longrightarrow> (\<exists> \<pi> Q'. inPath w \<pi> \<and> Q' \<subseteq> (\<Q> \<A>) \<and>
   DLTS_reach (\<delta> (determinise_NFA \<A>)) Q \<pi> = Some Q' \<and> q' \<in> Q'))"
  apply (rule impI)
proof -
  assume LTS_reachable: "LTS_is_reachable (\<Delta> \<A>) q w q' \<and> q' \<in> \<Q> \<A> \<and> q \<in> \<Q> \<A>"
  from this
  show "\<forall>Q\<subseteq>\<Q> \<A>.
       q \<in> Q \<longrightarrow>
       (\<exists>\<pi> Q'. inPath w \<pi> \<and> Q' \<subseteq> \<Q> \<A> \<and>
        DLTS_reach (\<delta> (determinise_NFA \<A>)) Q \<pi> = Some Q' \<and> q' \<in> Q')"
    apply (induction w arbitrary: q) 
    apply (metis DLTS_reach.simps(1) 
    LTS_is_reachable.simps(1) inPath.simps(1))
   proof -
    fix a w q
    assume induct_hyp: "(\<And>q. LTS_is_reachable (\<Delta> \<A>) q w q' \<and> q' \<in> \<Q> \<A> \<and> q \<in> \<Q> \<A> \<Longrightarrow>
             \<forall>Q\<subseteq>\<Q> \<A>.
                q \<in> Q \<longrightarrow>
                (\<exists>\<pi> Q'.
                    inPath w \<pi> \<and>
                    Q' \<subseteq> \<Q> \<A> \<and>
                    DLTS_reach (\<delta> (determinise_NFA \<A>)) Q \<pi> = Some Q' \<and> q' \<in> Q'))"
       and lts_reachable: "LTS_is_reachable (\<Delta> \<A>) q (a # w) q' \<and> 
                           q' \<in> \<Q> \<A> \<and> q \<in> \<Q> \<A>"

    from lts_reachable LTS_is_reachable.simps(2)[of "\<Delta> \<A>" q a w q']
    obtain qi \<sigma> where
    qi_\<sigma>_def: "qi \<in> (\<Q> \<A>) \<and> (q,\<sigma>,qi) \<in> (\<Delta> \<A>) \<and> a \<in> \<sigma>
               \<and> LTS_is_reachable (\<Delta> \<A>) qi w q'"
      by (meson \<Delta>_consistent)
    from this lts_reachable
         induct_hyp[of qi]
    have DLTS_reach_tail: "\<forall>Q\<subseteq>\<Q> \<A>.
            qi \<in> Q \<longrightarrow>
              (\<exists>\<pi> Q'.
                    inPath w \<pi> \<and> Q' \<subseteq> \<Q> \<A> \<and>
                    DLTS_reach (\<delta> (determinise_NFA \<A>)) Q \<pi> = Some Q' \<and> q' \<in> Q')"
      by fastforce
    show "\<forall>Q \<subseteq> \<Q> \<A>.
          q \<in> Q \<longrightarrow>
          (\<exists>\<pi> Q'.
              inPath (a # w) \<pi> \<and> Q' \<subseteq> \<Q> \<A> \<and>
              DLTS_reach (\<delta> (determinise_NFA \<A>)) Q \<pi> = Some Q' \<and> q' \<in> Q')"
      apply (rule allI impI) +
    proof -
      fix Q
      assume Q_\<Q>_sub: "Q \<subseteq> \<Q> \<A>"
         and q_in_Q: "q \<in> Q"
      from qi_\<sigma>_def this uniq_label
      have 
      Qi_def: "\<exists> Qi \<sigma>. \<delta> (determinise_NFA \<A>) (Q, \<sigma>) = Some Qi \<and> a \<in> \<sigma> \<and> 
               qi \<in> Qi \<and> Qi \<subseteq> \<Q> \<A>"
        unfolding determinise_NFA_def \<delta>_def LTS_to_DLTS_def NFA_def
        apply simp
      proof -
        assume a1: "qi \<in> \<Q> \<A> \<and> (q, \<sigma>, qi) \<in> \<Delta> \<A> \<and> a \<in> \<sigma> \<and> LTS_is_reachable (\<Delta> \<A>) qi w q'"
        assume a2: "q \<in> Q"
        assume "uniq_label_NFA \<A> \<and> (\<forall>q \<sigma> q'. (q, \<sigma>, q') \<in> \<Delta> \<A> \<longrightarrow> q \<in> \<Q> \<A> \<and> \<sigma> \<subseteq> \<Sigma> \<A> \<and> q' \<in> \<Q> \<A>)
                 \<and> \<I> \<A> \<subseteq> \<Q> \<A> \<and> \<F> \<A> \<subseteq> \<Q> \<A> \<and> finite (\<Q> \<A>) \<and> \<I> \<A> \<noteq> {}"
        then have "{q. \<exists>qa. qa \<in> Q \<and> (qa, \<sigma>, q) \<in> \<Delta> \<A>} \<subseteq> \<Q> \<A>"
          by blast
        then show "Q \<noteq> {} \<and>
    (\<exists>\<sigma>. (\<exists>q. q \<in> Q \<and> (\<exists>q'. (q, \<sigma>, q') \<in> \<Delta> \<A>)) \<and>
         \<sigma> \<noteq> {} \<and>
         a \<in> \<sigma> \<and> (\<exists>q\<in>Q. (q, \<sigma>, qi) \<in> \<Delta> \<A>) \<and> {q'. \<exists>q\<in>Q. (q, \<sigma>, q') \<in> \<Delta> \<A>} \<subseteq> \<Q> \<A>)"
          using a2 a1 by blast
      qed
      from this 
      obtain Qi \<sigma> where
      Qi_def': "\<delta> (determinise_NFA \<A>) (Q, \<sigma>) = Some Qi \<and> 
                a \<in> \<sigma> \<and> qi \<in> Qi \<and> Qi \<subseteq> \<Q> \<A>"
        by auto
    from DLTS_reach_tail Qi_def'
    obtain \<pi> Q' where
     \<pi>_Q'_def: "inPath w \<pi> \<and> Q' \<subseteq> \<Q> \<A> \<and>
          DLTS_reach (\<delta> (determinise_NFA \<A>)) Qi \<pi> = Some Q' \<and> q' \<in> Q'"
      by presburger
    from this 
    have "inPath (a#w) (\<sigma>#\<pi>)"
      by (simp add: Qi_def')
    from this DLTS_reach_tail Qi_def' \<pi>_Q'_def
    have "inPath (a # w) (\<sigma> # \<pi>) \<and> Q' \<subseteq> \<Q> \<A> \<and>
            DLTS_reach (\<delta> (determinise_NFA \<A>)) Q (\<sigma> # \<pi>) = Some Q' \<and> q' \<in> Q'"
      by simp
    from this
    show "\<exists>\<pi> Q'.
            inPath (a # w) \<pi> \<and> Q' \<subseteq> \<Q> \<A> \<and>
            DLTS_reach (\<delta> (determinise_NFA \<A>)) Q \<pi> = Some Q' \<and> q' \<in> Q'"
      by blast
  qed
qed
qed


lemma (in NFA) determinise_NFA___\<L>_in_state :
  assumes Q_subset: "Q \<subseteq> \<Q> \<A> \<and> Q \<noteq> {}"
      and uniq_label: "uniq_label_NFA \<A> \<and> \<I> \<A> \<noteq> {}"
  shows "\<L>_in_state (determinise_NFA \<A>) Q = \<Union> {\<L>_in_state \<A> q | q. q \<in> Q}"
        (is "?s1 = ?s2")
proof (intro set_eqI)
  fix x
  interpret DFA_detA: weak_DFA "(determinise_NFA \<A>)" 
    using determinise_NFA___DFA  wf_NFA uniq_label
    by auto

  show "(x \<in> \<L>_right (determinise_NFA \<A>) Q) = (x \<in> \<Union> {\<L>_right \<A> q |q. q \<in> Q})"
    unfolding \<L>_in_state_def
  proof 
    {
      assume x_in_determinise: "x \<in> {w. Bex (\<F> (determinise_NFA \<A>))
                                (LTS_is_reachable (\<Delta> (determinise_NFA \<A>)) Q w)}"
      from this 
      obtain Q' where
      Q'_def: "Q' \<in> \<F> (determinise_NFA \<A>) \<and> 
                (LTS_is_reachable (\<Delta> (determinise_NFA \<A>)) Q x Q')"
        by blast
      from this DFA_detA.weak_DFA_LTS_is_reachable_DLTS_reach_simp[of x Q Q']
      obtain \<pi> where
      \<pi>_def: "inPath x \<pi> \<and> DLTS_reach (\<delta> (determinise_NFA \<A>)) Q \<pi> = Some Q'"
        by blast
      from this determinise_NFA___DLTS_reach_noempty[OF _ Q_subset, of \<pi> Q'] 
           uniq_label
      have "Q'\<noteq> {}"
        using wf_NFA by linarith

      from this Q'_def 
      obtain q' where q'_def: "q' \<in> Q' \<and> q' \<in> \<F> \<A>" 
        unfolding determinise_NFA_def
        apply simp
        by blast
          
      from determinise_NFA___DLTS_reach[OF _ Q_subset, of \<pi> Q'] this \<pi>_def
      obtain q where
      q_def: "LTS_is_reachable (\<Delta> \<A>) q x q' \<and> q \<in> Q \<and> q' \<in> Q'"
        using uniq_label wf_NFA by blast
      from this q'_def
      show "x \<in> \<Union> {{w. Bex (\<F> \<A>) (LTS_is_reachable (\<Delta> \<A>) q w)} |q. q \<in> Q}"
        by auto
    }
    {
      assume x_\<A>: "x \<in> \<Union> {{w. Bex (\<F> \<A>) (LTS_is_reachable (\<Delta> \<A>) q w)} |q. q \<in> Q}"
      from this 
      obtain q q' where
      q_q'_def: "q \<in> Q \<and> q' \<in> (\<F> \<A>) \<and> LTS_is_reachable (\<Delta> \<A>) q x q'"
        by blast
      from determinise_NFA___LTS_reach[of q x q'] q_q'_def
      obtain \<pi> Q' where
      \<pi>_Q'_def: "inPath x \<pi> \<and> Q' \<subseteq> \<Q> \<A> \<and>
                 DLTS_reach (\<delta> (determinise_NFA \<A>)) Q \<pi> = Some Q' \<and> 
                 q' \<in> Q'"
        using Q_subset \<F>_consistent uniq_label wf_NFA by blast
      from \<pi>_Q'_def
      have Q'_in_F: "Q' \<in> \<F> (determinise_NFA \<A>)"
        unfolding determinise_NFA_def
        apply simp
        using q_q'_def by blast

      from \<pi>_Q'_def DFA_detA.weak_DFA_LTS_is_reachable_DLTS_reach_simp[of x Q Q']
      have "LTS_is_reachable (\<Delta> (determinise_NFA \<A>)) Q x Q'" 
        by blast
      from this Q'_in_F
      show "x \<in> {w. Bex (\<F> (determinise_NFA \<A>))
              (LTS_is_reachable (\<Delta> (determinise_NFA \<A>)) Q w)}"
        by blast 
    }
  qed
qed
 

lemma (in NFA) determinise_NFA_\<L> [simp] :
"uniq_label_NFA \<A> \<and> \<I> \<A> \<noteq> {} \<Longrightarrow> \<L> (determinise_NFA \<A>) = \<L> \<A>"
proof -
  assume uniq_label_\<A>: "uniq_label_NFA \<A> \<and> \<I> \<A> \<noteq> {}"
  from \<I>_consistent this 
  have "\<I> \<A> \<in> \<Q> (determinise_NFA \<A>)" by (simp add: NFA_def)
  thus ?thesis
    apply (auto simp add: \<L>_alt_def determinise_NFA___\<L>_in_state)
  proof -
    {
      fix x
      assume \<I>_\<Q>_sub: "\<I> \<A> \<subseteq> \<Q> \<A>"
         and    left: "x \<in> \<L>_right (determinise_NFA \<A>) (\<I> \<A>)"
      show "\<exists>xa\<in>\<I> \<A>. x \<in> \<L>_right \<A> xa"
      proof -
        from uniq_label_\<A> left
                determinise_NFA___\<L>_in_state[of "\<I> \<A>"]
        have "x \<in> \<Union> {\<L>_right \<A> q |q. q \<in> \<I> \<A>}"
          using  \<I>_consistent by blast
        from this
        show ?thesis 
          by blast
      qed
    }
    {
      fix x xa
      assume \<I>_\<Q>_sub: "\<I> \<A> \<subseteq> \<Q> \<A>"
         and right: "x \<in> \<L>_right \<A> xa"
         and xa_\<I>: "xa \<in> \<I> \<A>"
      from uniq_label_\<A>  \<I>_consistent
                determinise_NFA___\<L>_in_state[of "\<I> \<A>"]
      have "\<L>_right (determinise_NFA \<A>) (\<I> \<A>) = \<Union> {\<L>_right \<A> q |q. q \<in> \<I> \<A>}"
        by auto
      from this right xa_\<I>
      show "x \<in> \<L>_right (determinise_NFA \<A>) (\<I> \<A>)"
        by blast
    }
  qed
qed

lemma (in NFA) determinise_NFA_accept [simp] :
  "uniq_label_NFA \<A> \<and> \<I> \<A> \<noteq> {} \<Longrightarrow> 
  NFA_accept (determinise_NFA \<A>) w = NFA_accept \<A> w"
by (simp add: NFA_accept_alt_def)

definition efficient_determinise_NFA where
  "efficient_determinise_NFA \<A> = NFA_remove_unreachable_states (determinise_NFA \<A>)"

lemma NFA_is_weak_deterministic___NFA_remove_unreachable_states :
  "NFA_is_weak_deterministic \<A> \<Longrightarrow>
   NFA_is_weak_deterministic (NFA_remove_unreachable_states \<A>)"
proof -
  have det_impl: 
    "LTS_is_weak_deterministic (\<Delta> \<A>) \<Longrightarrow>
     LTS_is_weak_deterministic 
           (\<Delta> (NFA_remove_unreachable_states \<A>))" 
    by (simp add: LTS_is_deterministic_def LTS_is_weak_deterministic_def 
                  NFA_remove_unreachable_states_def Ball_def,
        metis NFA_unreachable_states_extend)
  assume "NFA_is_weak_deterministic \<A>"
  with det_impl show ?thesis 
    by (simp add: NFA_is_weak_deterministic_def)
qed

lemma NFA_is_deterministic___NFA_remove_unreachable_states :
  "NFA_is_deterministic \<A> \<Longrightarrow>
   NFA_is_deterministic (NFA_remove_unreachable_states \<A>)"
proof -
  have det_impl: 
    "LTS_is_deterministic (\<Q> \<A>) (\<Sigma> \<A>) (\<Delta> \<A>) \<Longrightarrow>
     LTS_is_deterministic (\<Q> (NFA_remove_unreachable_states \<A>)) 
                          (\<Sigma> (NFA_remove_unreachable_states \<A>))
           (\<Delta> (NFA_remove_unreachable_states \<A>))" 
    by (simp add: LTS_is_deterministic_def LTS_is_weak_deterministic_def 
                  NFA_remove_unreachable_states_def Ball_def,
        metis NFA_unreachable_states_extend)
  assume "NFA_is_deterministic \<A>"
  with det_impl show ?thesis 
    by (simp add: NFA_is_deterministic_def)
qed

lemma weak_DFA___NFA_remove_unreachable_states :
  "weak_DFA \<A> \<Longrightarrow> weak_DFA (NFA_remove_unreachable_states \<A>)"
unfolding weak_DFA_alt_def
by (metis NFA_is_weak_deterministic___NFA_remove_unreachable_states
          NFA_remove_unreachable_states___is_well_formed)

lemma DFA___NFA_remove_unreachable_states :
  "DFA \<A> \<Longrightarrow> DFA (NFA_remove_unreachable_states \<A>)"
unfolding DFA_alt_def
by (metis NFA_is_deterministic___NFA_remove_unreachable_states
          NFA_remove_unreachable_states___is_well_formed)



lemma efficient_weak_determinise_NFA_is_detNFA :
  "uniq_label_NFA \<A> \<and> \<I> \<A> \<noteq> {}\<Longrightarrow> 
    NFA_is_weak_deterministic (efficient_determinise_NFA \<A>)"
unfolding efficient_determinise_NFA_def
  apply (rule NFA_is_weak_deterministic___NFA_remove_unreachable_states)
  apply (rule determinise_NFA_is_weak_detNFA)
  by blast

lemma efficient_determinise_NFA_is_detNFA :
  "uniq_label_NFA \<A> \<and> \<I> \<A> \<noteq> {} \<and> 
   (\<forall>q\<in>\<Q> \<A>. \<forall>a\<in>\<Sigma> \<A>. \<exists>\<alpha> q'. a \<in> \<alpha> \<and> (q, \<alpha>, q') \<in> \<Delta> \<A>) \<Longrightarrow> 
    NFA_is_deterministic (efficient_determinise_NFA \<A>)"
unfolding efficient_determinise_NFA_def
  apply (rule NFA_is_deterministic___NFA_remove_unreachable_states)
  apply (rule determinise_NFA_is_detNFA)
  by blast
  
lemma efficient_determinise_NFA_is_weak_DFA :
  "uniq_label_NFA \<A> \<and> NFA \<A> \<and> \<I> \<A> \<noteq> {} \<Longrightarrow> 
         weak_DFA (efficient_determinise_NFA \<A>)"
unfolding weak_DFA_def weak_detNFA_def
proof
  assume uniq_wf: "uniq_label_NFA \<A> \<and> NFA \<A> \<and> \<I> \<A> \<noteq> {}"
  show "NFA_is_weak_deterministic (efficient_determinise_NFA \<A>)" 
    using efficient_weak_determinise_NFA_is_detNFA uniq_wf
    by auto
next
  assume wf_A: "uniq_label_NFA \<A> \<and> NFA \<A> \<and> \<I> \<A> \<noteq> {}"
  show "NFA (efficient_determinise_NFA \<A>)"
    unfolding efficient_determinise_NFA_def
    apply (rule NFA_remove_unreachable_states___is_well_formed)
    using wf_A determinise_NFA___is_well_formed
    by (simp add: determinise_NFA___is_well_formed)
qed


lemma (in NFA) efficient_determinise_NFA_accept [simp] :
  "uniq_label_NFA \<A> \<and> \<I> \<A> \<noteq> {} \<Longrightarrow>
   NFA_accept (efficient_determinise_NFA \<A>) w = NFA_accept \<A> w"
  using efficient_determinise_NFA_def[of \<A>]
          determinise_NFA_accept
          NFA_remove_unreachable_states_accept_iff[of "determinise_NFA \<A>"]
  by force

lemma (in NFA) efficient_determinise_NFA_\<L> [simp] :
"uniq_label_NFA \<A> \<and> \<I> \<A> \<noteq> {} \<Longrightarrow> \<L> (efficient_determinise_NFA \<A>) = \<L> \<A>"
  unfolding efficient_determinise_NFA_def
  by force

lemma efficient_determinise_NFA___is_initially_connected :
  "NFA_is_initially_connected (efficient_determinise_NFA \<A>)"
unfolding efficient_determinise_NFA_def
by (simp add: NFA_remove_unreachable_states___NFA_is_initially_connected)


lemma (in NFA) efficient_determinise_NFA_compute :
"uniq_label_NFA \<A> \<and> \<I> \<A> \<noteq> {}  \<Longrightarrow> 
  efficient_determinise_NFA \<A> = 
   (NFA_construct_reachable (\<Sigma> \<A>) {\<I> \<A>}
     (\<lambda>Q.  (Q \<subseteq> \<Q> \<A>) \<and> Q \<inter> (\<F> \<A>) \<noteq> {}) 
   {(Q, \<sigma>, {q'. \<exists> q \<in> Q. (q, \<sigma>, q') \<in> \<Delta> \<A>}) |Q \<sigma>. Q \<subseteq> \<Q> \<A> \<and> Q \<noteq> {} \<and> 
               (\<exists> q q'. q \<in> Q \<and> (q, \<sigma>, q') \<in> \<Delta> \<A>) \<and> \<sigma> \<noteq> {}})" 
proof -
  assume uniq_label_\<A>: "uniq_label_NFA \<A> \<and> \<I> \<A> \<noteq> {}"
  from this wf_NFA 
  have prem: "NFA \<A> \<and> \<I> \<A> \<noteq> {}" by auto
   note determinise_NFA___is_well_formed[OF prem] 
   hence wf_det: "NFA (determinise_NFA \<A>)" .

   thus ?thesis
     unfolding efficient_determinise_NFA_def determinise_NFA_def
     by (simp add: NFA.NFA_remove_unreachable_states_implementation)
qed

lemma NFA_isomorphic_wf___NFA_determinise_cong :
assumes equiv: "NFA_isomorphic_wf \<A>1 \<A>2 \<and> \<I> \<A>1 \<noteq> {}"
shows "NFA_isomorphic_wf (determinise_NFA \<A>1) (determinise_NFA \<A>2)"
proof -
  from equiv obtain f where inj_f : "inj_on f (\<Q> \<A>1)" and
                            \<A>2_eq: "\<A>2 = NFA_rename_states \<A>1 f" and
                            wf_\<A>1: "NFA \<A>1" and
                            \<I>\<A>1: "\<I> \<A>1 \<noteq> {}"
    unfolding NFA_isomorphic_wf_def NFA_isomorphic_def by auto

  obtain F where F_def : "F = (\<lambda>S. f ` S)" by blast

  have F_elim: "\<And>Q1 Q2. \<lbrakk>Q1 \<subseteq> \<Q> \<A>1; Q2 \<subseteq> \<Q> \<A>1\<rbrakk> \<Longrightarrow> 
                (F Q1 = F Q2) \<longleftrightarrow> Q1 = Q2"
  proof -
    fix Q1 Q2    
    assume "Q1 \<subseteq> \<Q> \<A>1" "Q2 \<subseteq> \<Q> \<A>1"
    hence "Q1 \<union> Q2 \<subseteq> \<Q> \<A>1" by simp
    with inj_f have "inj_on f (Q1 \<union> Q2)" by (rule subset_inj_on)

    thus "(F Q1 = F Q2) \<longleftrightarrow> Q1 = Q2"
      using inj_on_Un_image_eq_iff [of f Q1 Q2] F_def
      by simp
  qed

  from F_elim have inj_F : "inj_on F (\<Q> (determinise_NFA \<A>1))"
    unfolding determinise_NFA_def inj_on_def
    by simp

  have \<A>2_eq' : "determinise_NFA \<A>2 = 
                 NFA_rename_states (determinise_NFA \<A>1) F"
    unfolding determinise_NFA_def \<A>2_eq NFA_rename_states_def 
    apply simp
  proof (intro conjI)
    show "f ` \<I> \<A>1 = F (\<I> \<A>1)" unfolding F_def by simp
  next
    show "{uu. uu \<subseteq> f ` \<Q> \<A>1 \<and> uu \<noteq> {}} = F ` {uu. uu \<subseteq> \<Q> \<A>1 \<and> uu \<noteq> {}}"
      apply (rule set_eqI)
      apply (simp add: subset_image_iff F_def image_iff)
      apply blast
    done
  next
    have "\<And>Q. Q \<subseteq> (\<Q> \<A>1) \<Longrightarrow> (f ` Q \<inter> (f ` (\<F> \<A>1)) \<noteq> {}) = (Q \<inter> \<F> \<A>1 \<noteq> {})"
    proof -
      fix Q
      assume Q_sub: "Q \<subseteq> (\<Q> \<A>1)"
      
      from NFA.\<F>_consistent [OF wf_\<A>1] 
      have F_sub: "\<F> \<A>1 \<subseteq> \<Q> \<A>1" .

      from inj_on_image_Int [OF inj_f Q_sub F_sub, symmetric]
      show "(f ` Q \<inter> (f ` (\<F> \<A>1)) \<noteq> {}) = (Q \<inter> \<F> \<A>1 \<noteq> {})"
        by simp
    qed
    thus "{fs. fs \<subseteq> f ` \<Q> \<A>1 \<and> fs \<inter> f ` \<F> \<A>1 \<noteq> {}} = F ` {fs. fs \<subseteq> \<Q> \<A>1 \<and> fs \<inter> \<F> \<A>1 \<noteq> {}}"
      apply (rule_tac set_eqI)
      apply (simp add: subset_image_iff F_def image_iff)
      apply metis
    done
  next
    from inj_f NFA.\<Delta>_consistent [OF wf_\<A>1]
    have lem: "\<And>\<sigma> Q. \<lbrakk>Q \<subseteq> \<Q> \<A>1; (\<exists>q. q \<in> Q \<and> (\<exists>q'. (q, \<sigma>, q') \<in> \<Delta> \<A>1)) ; \<sigma> \<noteq> {}\<rbrakk> 
                      \<Longrightarrow> 
        {q'. \<exists> q \<in> Q. \<exists>s1 s2. f q = f s1 \<and> q' = f s2 \<and> (s1, \<sigma>, s2) \<in> \<Delta> \<A>1} =
        f ` {q'. \<exists> q \<in> Q. (q, \<sigma>, q') \<in> \<Delta> \<A>1}" 
      apply (rule_tac set_eqI)
      apply (simp add: image_iff inj_on_def subset_iff Bex_def)
      apply auto
      apply metis
    done

 
  show "{(Q, \<sigma>, {q'. \<exists>q\<in>Q. \<exists>s1. q = f s1 \<and> (\<exists>s2. q' = f s2 \<and> (s1, \<sigma>, s2) \<in> \<Delta> \<A>1)}) |Q \<sigma>.
     Q \<subseteq> f ` \<Q> \<A>1 \<and>
     Q \<noteq> {} \<and>
     (\<exists>q. q \<in> Q \<and> (\<exists>q' s1. q = f s1 \<and> (\<exists>s2. q' = f s2 \<and> (s1, \<sigma>, s2) \<in> \<Delta> \<A>1))) \<and>
     \<sigma> \<noteq> {}} =
    {(F s1, a, F {q'. \<exists>q\<in>s1. (q, a, q') \<in> \<Delta> \<A>1}) |s1 a.
     s1 \<subseteq> \<Q> \<A>1 \<and> s1 \<noteq> {} \<and> (\<exists>q. q \<in> s1 \<and> (\<exists>q'. (q, a, q') \<in> \<Delta> \<A>1)) \<and> a \<noteq> {}}"
    apply (rule_tac set_eqI)
  proof 
    {
      fix x
      assume x_in: " x \<in> {(Q, \<sigma>,
               {q'. \<exists>q\<in>Q. \<exists>s1. q = f s1 \<and> (\<exists>s2. q' = f s2 \<and> (s1, \<sigma>, s2) \<in> \<Delta> \<A>1)}) |
              Q \<sigma>.
              Q \<subseteq> f ` \<Q> \<A>1 \<and>
              Q \<noteq> {} \<and>
              (\<exists>q. q \<in> Q \<and>
                   (\<exists>q' s1. q = f s1 \<and> (\<exists>s2. q' = f s2 \<and> (s1, \<sigma>, s2) \<in> \<Delta> \<A>1))) \<and>
              \<sigma> \<noteq> {}}"
      from this 
      obtain Q \<sigma> where
      Q_\<sigma>_def: "x = (Q, \<sigma>, {q'. \<exists>q\<in>Q. \<exists>s1. q = f s1 \<and> 
                                (\<exists>s2. q' = f s2 \<and> (s1, \<sigma>, s2) \<in> \<Delta> \<A>1)})" and
      Q_subset: "Q \<subseteq> f ` \<Q> \<A>1 \<and> Q \<noteq> {}" and
      Q_\<Delta>: "(\<exists>q. q \<in> Q \<and> (\<exists>q' s1. q = f s1 \<and> 
             (\<exists>s2. q' = f s2 \<and> (s1, \<sigma>, s2) \<in> \<Delta> \<A>1))) \<and> \<sigma> \<noteq> {}"
        by force
      from this
      obtain s1 where s1_def: "s1 \<subseteq> \<Q> \<A>1 \<and> Q = f ` s1"
        by (meson subset_imageE)

      thm Q_\<sigma>_def Q_subset Q_\<Delta> s1_def
      have F_eq: "F {q'. \<exists>q\<in>s1. (q, \<sigma>, q') \<in> \<Delta> \<A>1} = 
            {q'. \<exists>q\<in>Q. \<exists>s1. q = f s1 \<and> (\<exists>s2. q' = f s2 \<and> (s1, \<sigma>, s2) \<in> \<Delta> \<A>1)}"
        apply (rule_tac set_eqI)
      proof 
        {
          fix x
          assume x_F: "x \<in> F {q'. \<exists>q\<in>s1. (q, \<sigma>, q') \<in> \<Delta> \<A>1}"
          from this obtain q1 q2 where
          s1_s2_def: "x = f q2 \<and> q1 \<in> s1 \<and> (q1, \<sigma>,q2) \<in> \<Delta> \<A>1" 
            using F_def by blast
          from this s1_def
          show "x \<in> {q'. \<exists>q\<in>Q. \<exists>s1. q = f s1 \<and> 
                (\<exists>s2. q' = f s2 \<and> (s1, \<sigma>, s2) \<in> \<Delta> \<A>1)}"
            by auto
        }
        {
          fix x
          assume right: "x \<in> {q'. \<exists>q\<in>Q. \<exists>s1. q = f s1 \<and> 
                        (\<exists>s2. q' = f s2 \<and> (s1, \<sigma>, s2) \<in> \<Delta> \<A>1)}"
          from this
          show "x \<in> F {q'. \<exists>q\<in>s1. (q, \<sigma>, q') \<in> \<Delta> \<A>1}"
            unfolding F_def
            apply simp
            using s1_def
            by (metis (mono_tags, lifting) 
                NFA.\<Delta>_consistent imageI inj_f 
                inj_on_image_mem_iff mem_Collect_eq wf_\<A>1)
        }
      qed
        

      from Q_\<sigma>_def Q_subset Q_\<Delta> s1_def
      have "\<exists>q. q \<in> s1 \<and> (\<exists>q'. (q, \<sigma>, q') \<in> \<Delta> \<A>1)"
      by (metis (mono_tags, lifting) 
                NFA.\<Delta>_consistent imageI inj_f 
                inj_on_image_mem_iff mem_Collect_eq wf_\<A>1)
  
      from this s1_def Q_\<sigma>_def Q_subset Q_\<Delta> F_eq
      show "x \<in> {(F s1, a, F {q'. \<exists>q\<in>s1. (q, a, q') \<in> \<Delta> \<A>1}) |s1 a.
               s1 \<subseteq> \<Q> \<A>1 \<and>
               s1 \<noteq> {} \<and> (\<exists>q. q \<in> s1 \<and> (\<exists>q'. (q, a, q') \<in> \<Delta> \<A>1)) \<and> a \<noteq> {}}"
        apply simp
        by (metis F_def)
    }
    {
      fix x
      assume right: "x \<in> {(F s1, a, F {q'. \<exists>q\<in>s1. (q, a, q') \<in> \<Delta> \<A>1}) |s1 a.
              s1 \<subseteq> \<Q> \<A>1 \<and>
              s1 \<noteq> {} \<and> (\<exists>q. q \<in> s1 \<and> (\<exists>q'. (q, a, q') \<in> \<Delta> \<A>1)) \<and> a \<noteq> {}}"
      from this
      obtain s1 \<alpha> where 
      s1_\<alpha>_def: "s1 \<subseteq> \<Q> \<A>1 \<and> s1 \<noteq> {} \<and> (\<exists>q. q \<in> s1 \<and> 
                 (\<exists>q'. (q, \<alpha>, q') \<in> \<Delta> \<A>1)) \<and> \<alpha> \<noteq> {}"
      and x_s1_\<alpha>: "x = (F s1, \<alpha>, F {q'. \<exists>q\<in>s1. (q, \<alpha>, q') \<in> \<Delta> \<A>1})"
        by blast
      from this F_def
      have s1_Q: "F s1 \<subseteq> f ` \<Q> \<A>1"
        by blast
      have "F {q'. \<exists> q \<in> s1. (q, \<alpha>, q') \<in> \<Delta> \<A>1} = 
            {q'. \<exists> q \<in> F s1. 
                     \<exists>s1. q = f s1 \<and> (\<exists>s2. q' = f s2 \<and> (s1, \<alpha>, s2) \<in> \<Delta> \<A>1)}"
        using F_def lem s1_\<alpha>_def by auto
      from this s1_Q
      show "x \<in> {(Q, \<sigma>,
                {q'. \<exists>q\<in>Q. \<exists>s1. q = f s1 \<and> (\<exists>s2. q' = f s2 \<and> (s1, \<sigma>, s2) \<in> \<Delta> \<A>1)}) |
               Q \<sigma>.
               Q \<subseteq> f ` \<Q> \<A>1 \<and>
               Q \<noteq> {} \<and>
               (\<exists>q. q \<in> Q \<and>
                    (\<exists>q' s1. q = f s1 \<and> (\<exists>s2. q' = f s2 \<and> (s1, \<sigma>, s2) \<in> \<Delta> \<A>1))) \<and>
               \<sigma> \<noteq> {}}"
        apply simp
        using F_def s1_\<alpha>_def x_s1_\<alpha> by auto 
    }
  qed
qed
  from this show "NFA_isomorphic_wf (determinise_NFA \<A>1) (determinise_NFA \<A>2)"
    unfolding NFA_isomorphic_wf_def NFA_isomorphic_def
    apply (rule_tac conjI)
    using inj_F apply blast
    by (simp add: determinise_NFA___is_well_formed wf_\<A>1 \<I>\<A>1)
qed 


lemma NFA_isomorphic_efficient_determinise :
assumes equiv: "NFA_isomorphic_wf \<A>1 \<A>2 \<and> \<I> \<A>1 \<noteq> {}"
shows "NFA_isomorphic_wf (efficient_determinise_NFA \<A>1) (efficient_determinise_NFA \<A>2)"
unfolding efficient_determinise_NFA_def
by (intro NFA_isomorphic_wf___NFA_remove_unreachable_states 
          NFA_isomorphic_wf___NFA_determinise_cong equiv)

definition NFA_determinise :: "('q::{NFA_states}, 'a, _) NFA_rec_scheme \<Rightarrow> ('q, 'a) NFA_rec" where
  "NFA_determinise \<A> = NFA_normalise_states (efficient_determinise_NFA \<A>)"

lemma NFA_determinise_isomorphic_wf :
assumes wf_A: "uniq_label_NFA \<A> \<and> NFA \<A> \<and> \<I> \<A> \<noteq> {}"
shows  "NFA_isomorphic_wf (efficient_determinise_NFA \<A>) 
                          (NFA_determinise \<A>)"
unfolding NFA_determinise_def
  apply (rule NFA_isomorphic_wf_normalise_states)
  using efficient_determinise_NFA_is_weak_DFA
  by (simp add: efficient_determinise_NFA_is_weak_DFA wf_A)


lemma NFA_determinise_is_weak_DFA :
assumes wf_A : "uniq_label_NFA \<A> \<and> NFA \<A> \<and> \<I> \<A> \<noteq> {}"
shows "weak_DFA (NFA_determinise \<A>)"
proof -
  note step1 = efficient_determinise_NFA_is_weak_DFA [OF wf_A]
  note step2 = NFA_determinise_isomorphic_wf [OF wf_A]
  thm NFA_isomorphic___is_well_formed_weak_DFA
  note step3 = NFA_isomorphic___is_well_formed_weak_DFA 
        [OF step1 NFA_isomorphic_wf_D(3)[OF step2]]
  thus ?thesis .
qed

lemma NFA_determinise_NFA_accept :
assumes wf_A : "uniq_label_NFA \<A> \<and> NFA \<A> \<and> \<I> \<A> \<noteq> {}"
    and I_nempty: "\<I> \<A> \<noteq> {}"    
shows  "NFA_accept (NFA_determinise \<A>) w = NFA_accept \<A> w"
proof -
  note iso = NFA_determinise_isomorphic_wf [OF wf_A]
  from NFA_isomorphic_wf_accept [OF iso] 
       NFA.efficient_determinise_NFA_accept  wf_A
       I_nempty
  show ?thesis by auto
qed

lemma NFA_determinise_\<L> :
"uniq_label_NFA \<A> \<and> NFA \<A> \<and> \<I> \<A> \<noteq> {} \<Longrightarrow> 
          \<L> (NFA_determinise \<A>) = \<L> \<A>"
by (simp add: \<L>_def NFA_determinise_NFA_accept)



subsection \<open> Complement \<close>
definition DFA_complement :: "('q, 'a) NFA_rec \<Rightarrow> ('q, 'a) NFA_rec" where
  "DFA_complement \<A> = \<lparr> \<Q> = \<Q> \<A>, \<Sigma> = \<Sigma> \<A>, \<Delta> = \<Delta> \<A>, \<I> = \<I> \<A>, \<F> = \<Q> \<A> - \<F> \<A> \<rparr>"

lemma [simp] : "\<Q> (DFA_complement \<A>) = \<Q> \<A>" by (simp add: DFA_complement_def)
lemma [simp] : "\<Sigma> (DFA_complement \<A>) = \<Sigma> \<A>" by (simp add: DFA_complement_def)
lemma [simp] : "\<Delta> (DFA_complement \<A>) = \<Delta> \<A>" by (simp add: DFA_complement_def)
lemma [simp] : "\<I> (DFA_complement \<A>) = \<I> \<A>" by (simp add: DFA_complement_def)
lemma [simp] : "\<F> (DFA_complement \<A>) = \<Q> \<A> - \<F> \<A>" by (simp add: DFA_complement_def)

lemma [simp] : "\<delta> (DFA_complement \<A>) = \<delta> \<A>" by (simp add: DFA_complement_def \<delta>_def)
lemma [simp] : "\<i> (DFA_complement \<A>) = \<i> \<A>" by (simp add: DFA_complement_def \<i>_def)

lemma DFA_complement___is_well_formed : "NFA \<A> \<Longrightarrow> NFA (DFA_complement \<A>)"
unfolding NFA_def by auto

lemma DFA_complement_of_DFA_is_DFA :
  "DFA \<A> \<Longrightarrow> DFA (DFA_complement \<A>)"
unfolding DFA_alt_def detNFA_def NFA_def NFA_is_deterministic_def by auto

lemma DFA_complement___DLTS_reach :
  "DLTS_reach (\<delta> (DFA_complement \<A>)) q w = DLTS_reach (\<delta> \<A>) q w" by simp

lemma DFA_complement_DFA_complement [simp] :
  "NFA \<A> \<Longrightarrow> DFA_complement (DFA_complement \<A>) = \<A>"
proof -
  assume a: "NFA \<A>"
  then have "\<Q> \<A> - (\<Q> \<A> - \<F> \<A>) = \<F> \<A>" using NFA.\<F>_consistent by auto
  thus ?thesis unfolding DFA_complement_def by simp
qed


lemma (in DFA) uniq_reachable: 
  "q \<in> \<Q> \<A> \<Longrightarrow> 
        LTS_is_reachable (\<Delta> \<A>) q w q1 \<and> LTS_is_reachable (\<Delta> \<A>) q w q2 \<Longrightarrow> q1 = q2"
  apply (induction w arbitrary: q)
  apply auto[1]
proof -
  fix a w q
  assume ind_hyp: "(\<And>q. q \<in> \<Q> \<A> \<Longrightarrow> LTS_is_reachable (\<Delta> \<A>) q w q1 \<and> 
                        LTS_is_reachable (\<Delta> \<A>) q w q2 \<Longrightarrow>
                        q1 = q2)"
     and  q_in_\<Q>_\<A>: "q \<in> \<Q> \<A>"

  from wf_DFA q_in_\<Q>_\<A>
  have exist_q'': "\<forall> a. a \<in> \<Sigma> \<A> \<longrightarrow> (\<exists> q''.\<exists> \<alpha>. (q, \<alpha>, q'') \<in> (\<Delta> \<A>) \<and> a \<in> \<alpha>)"
  unfolding DFA_def detNFA_def NFA_is_deterministic_def
              NFA_def LTS_is_deterministic_def
              LTS_is_weak_deterministic_def
  by simp
   
  have uniq_q'': "\<And> a. a \<in> \<Sigma> \<A> \<Longrightarrow> (\<exists>! q''. \<exists> \<alpha>. (q, \<alpha>, q'') \<in> (\<Delta> \<A>) \<and> a \<in> \<alpha>)"
  proof - fix a
    assume a_in_\<Sigma>: "a \<in> \<Sigma> \<A>"
    show "\<exists>!q''. \<exists>\<alpha>. (q, \<alpha>, q'') \<in> \<Delta> \<A> \<and> a \<in> \<alpha>"
  proof (rule_tac ccontr)
    assume exists_two: "\<nexists>!q''. \<exists>\<alpha>. (q, \<alpha>, q'') \<in> \<Delta> \<A> \<and> a \<in> \<alpha>"
    from this exist_q'' a_in_\<Sigma>
    have "\<exists> q1 q2 \<alpha>1 \<alpha>2. 
              q1 \<noteq> q2 \<and> (q, \<alpha>1, q1) \<in> (\<Delta> \<A>) \<and> a \<in> \<alpha>1 \<and>
                         (q, \<alpha>2, q2) \<in> (\<Delta> \<A>) \<and> a \<in> \<alpha>2"
      by blast
    from this obtain q1 q2 \<alpha>1 \<alpha>2 where
    q12\<alpha>12_def: "q1 \<noteq> q2 \<and> (q, \<alpha>1, q1) \<in> (\<Delta> \<A>) \<and> a \<in> \<alpha>1 \<and>
                         (q, \<alpha>2, q2) \<in> (\<Delta> \<A>) \<and> a \<in> \<alpha>2"
      by auto
    from this wf_DFA
    show False
    unfolding DFA_def detNFA_def NFA_is_deterministic_def
              NFA_def LTS_is_deterministic_def
              LTS_is_weak_deterministic_def
    apply simp
    by fastforce 
  qed  qed
  from this ind_hyp
  show "LTS_is_reachable (\<Delta> \<A>) q (a # w) q1 \<and> 
        LTS_is_reachable (\<Delta> \<A>) q (a # w) q2 \<Longrightarrow>
       q1 = q2"
  proof -
    assume reachable: "LTS_is_reachable (\<Delta> \<A>) q (a # w) q1 \<and> 
        LTS_is_reachable (\<Delta> \<A>) q (a # w) q2"
    from this have "a \<in> \<Sigma> \<A>"
      using \<Delta>_consistent by auto
    from this uniq_q'' ind_hyp
    show "q1 = q2"
      by (metis LTS_is_reachable.simps(2) \<Delta>_consistent reachable)
  qed
qed


lemma DFA_complement_word :
  assumes wf_A: "DFA \<A>"
      and    wf_w: "w \<in> lists (\<Sigma> \<A>)"
  shows "NFA_accept (DFA_complement \<A>) w \<longleftrightarrow> \<not> NFA_accept \<A> w"
proof -
  let ?c\<A> = "DFA_complement \<A>"

  interpret DFA_A: DFA \<A> by (fact wf_A)
  interpret DFA_cA: DFA ?c\<A> by (simp add: DFA_complement_of_DFA_is_DFA wf_A)
  from  DFA_A.\<i>_is_state wf_w
  obtain \<pi> where
  \<pi>_def: "inPath w \<pi> \<and> ~(DLTS_reach (\<delta> \<A>) (\<i> \<A>) \<pi> = None)" 
    using  DFA_A.DFA_DLTS_reach_is_some
    by blast
  then obtain q' where 
  DLTS_reach_eq_q': "DLTS_reach (\<delta> \<A>) (\<i> \<A>) \<pi> = Some q'" by auto
   
  from DLTS_reach_eq_q' DFA_A.\<i>_is_state have
   "q' \<in> \<Q> \<A>" 
    using DFA_A.DFA_DLTS_reach_wf
    using \<pi>_def by blast

  thm DFA_A.DFA_LTS_is_reachable_DLTS_reach_simp
      DFA_cA.DFA_LTS_is_reachable_DLTS_reach_simp
  with DLTS_reach_eq_q' show ?thesis
    unfolding NFA_accept_def Bex_def
    apply simp
    using DFA_A.uniq_reachable[of "\<i> \<A>" w]
    using DFA_A.DFA_LTS_is_reachable_DLTS_reach_simp DFA_A.\<i>_is_state \<pi>_def 
    by blast
qed


lemma DFA_complement_\<L>___lists_\<Sigma> :
  "NFA \<A> \<longrightarrow> \<L> (DFA_complement \<A>) \<subseteq> lists (\<Sigma> \<A>)"
  apply (simp add: DFA_complement_def \<L>_def NFA_accept_def, auto)
  unfolding NFA_def
  apply simp
  apply auto
  apply (rename_tac w a q q')
proof -
  fix  w a q q'
  assume a_in_w: "a \<in> set w"
     and reachable: "LTS_is_reachable (\<Delta> \<A>) q w q'"
     and q_in_\<I>: "q \<in> \<I> \<A>"
     and q_in_\<Q>: "q' \<in> \<Q> \<A>"
     and tran_wf: "\<forall>q \<sigma> q'. (q, \<sigma>, q') \<in> \<Delta> \<A> \<longrightarrow> q \<in> \<Q> \<A> \<and> \<sigma> \<subseteq> \<Sigma> \<A> \<and> q' \<in> \<Q> \<A>"
     and \<I>_\<Q>: "\<I> \<A> \<subseteq> \<Q> \<A>"
  from a_in_w reachable
  show "a \<in> \<Sigma> \<A>"
    apply (induction w arbitrary: q)
    apply force
  proof -
    fix aa w q
    assume ind_hyp: "(\<And>q. a \<in> set w \<Longrightarrow> LTS_is_reachable (\<Delta> \<A>) q w q' \<Longrightarrow> a \<in> \<Sigma> \<A>)"
       and a_in_w': "a \<in> set (aa # w)"
       and reachable' : " LTS_is_reachable (\<Delta> \<A>) q (aa # w) q'"
    show "a \<in> \<Sigma> \<A>"
    proof (cases "a = aa")
    case True
      then show ?thesis 
        by (meson LTS_is_reachable.simps(2) reachable' subsetD tran_wf)
    next
      case False
      then show ?thesis
        using a_in_w' ind_hyp reachable' by auto
    qed
  qed
qed

lemma NFA_\<L>___lists_\<Sigma>:
  "NFA \<A> \<Longrightarrow> \<L> \<A> \<subseteq> lists (\<Sigma> \<A>)"
  apply (simp add: DFA_complement_def \<L>_def NFA_accept_def, auto)
  unfolding NFA_def
apply simp
  apply auto
  apply (rename_tac w a q q')
proof -
  fix  w a q q'
  assume a_in_w: "a \<in> set w"
     and reachable: "LTS_is_reachable (\<Delta> \<A>) q w q'"
     and q_in_\<I>: "q \<in> \<I> \<A>"
     and q_in_\<Q>: "q' \<in> \<F> \<A>"
     and tran_wf: "\<forall>q \<sigma> q'. (q, \<sigma>, q') \<in> \<Delta> \<A> \<longrightarrow> q \<in> \<Q> \<A> \<and> \<sigma> \<subseteq> \<Sigma> \<A> \<and> q' \<in> \<Q> \<A>"
     and \<I>_\<Q>: "\<I> \<A> \<subseteq> \<Q> \<A>"
     and \<F>_\<Q>: "\<F> \<A> \<subseteq> \<Q> \<A>"
  from a_in_w reachable
  show "a \<in> \<Sigma> \<A>"
    apply (induction w arbitrary: q)
    apply force
  proof -
    fix aa w q
    assume ind_hyp: "(\<And>q. a \<in> set w \<Longrightarrow> LTS_is_reachable (\<Delta> \<A>) q w q' \<Longrightarrow> a \<in> \<Sigma> \<A>)"
       and a_in_w': "a \<in> set (aa # w)"
       and reachable' : " LTS_is_reachable (\<Delta> \<A>) q (aa # w) q'"
    show "a \<in> \<Sigma> \<A>"
    proof (cases "a = aa")
    case True
      then show ?thesis 
        by (meson LTS_is_reachable.simps(2) reachable' subsetD tran_wf)
    next
      case False
      then show ?thesis
        using a_in_w' ind_hyp reachable' by auto
    qed
  qed
qed

lemma (in DFA) DFA_complement_\<L> [simp] : 
  shows "\<L> (DFA_complement \<A>) = lists (\<Sigma> \<A>) - \<L> \<A>"
proof
  from wf_DFA have NFA_\<A>: "NFA \<A>"
    unfolding DFA_def by simp
  {
    show "\<L> (DFA_complement \<A>) \<subseteq> lists (\<Sigma> \<A>) - \<L> \<A>"
    proof
      fix x
      assume x_in_complement: "x \<in> \<L> (DFA_complement \<A>)"
      from this \<L>_def
      have x_complement_accept: "NFA_accept (DFA_complement \<A>) x"
        by auto
      from x_in_complement 
           DFA_complement_\<L>___lists_\<Sigma>[of \<A>] NFA_\<A>
      have "x \<in> lists (\<Sigma> \<A>)"
        by blast
      from this DFA_complement_word[OF wf_DFA] \<L>_def[of \<A>]
           x_complement_accept
      show "x \<in> lists (\<Sigma> \<A>) - \<L> \<A>"
        by auto
    qed
  }
  {
    show "lists (\<Sigma> \<A>) - \<L> \<A> \<subseteq> \<L> (DFA_complement \<A>)"
    proof 
      fix x
      assume x_in_complement: "x \<in> lists (\<Sigma> \<A>) - \<L> \<A>"
      from this \<L>_def NFA_\<L>___lists_\<Sigma>[of \<A>] NFA_\<A>
      have "\<not> NFA_accept \<A> x"
        by blast
      from this DFA_complement_word[of \<A> x, OF wf_DFA]
      have "NFA_accept (DFA_complement \<A>) x"
        using x_in_complement by blast
      from this \<L>_def[of "DFA_complement \<A>"]
      show "x \<in> \<L> (DFA_complement \<A>)"
        by simp
    qed
  }
qed

lemma NFA_isomorphic_wf___DFA_complement_cong :
assumes equiv: "NFA_isomorphic_wf \<A>1 \<A>2"
shows "NFA_isomorphic_wf (DFA_complement \<A>1) (DFA_complement \<A>2)"
proof -
  from equiv obtain f where inj_f : "inj_on f (\<Q> \<A>1)" and
                 \<A>2_eq: "\<A>2 = NFA_rename_states \<A>1 f" and
                 wf_\<A>1: "NFA \<A>1" 
    unfolding NFA_isomorphic_wf_def NFA_isomorphic_def by auto

  with inj_f have inj_f' : "inj_on f (\<Q> (DFA_complement \<A>1))"
    by simp

  have \<A>2_eq': "DFA_complement \<A>2 = NFA_rename_states (DFA_complement \<A>1) f"
    unfolding DFA_complement_def \<A>2_eq 
    apply (rule NFA_rec.equality)
    apply (simp_all)
    apply (simp add: NFA_rename_states_def)
    apply (insert inj_on_image_set_diff [of f "\<Q> \<A>1" "\<Q> \<A>1" "\<F> \<A>1"])
    apply (insert NFA.\<F>_consistent[OF wf_\<A>1])
    apply (simp add: inj_f)
  done

  from inj_f' \<A>2_eq' DFA_complement___is_well_formed [OF wf_\<A>1] 
  show ?thesis
    unfolding NFA_isomorphic_wf_def NFA_isomorphic_def by blast
qed


(*
  Transition label spliting unique
*)


definition labels :: "('q, 'a) LTS \<Rightarrow> 'a set set nres" 
  where
  "labels T = RETURN {\<alpha> | q \<alpha> q'. (q, \<alpha>, q') \<in> T}" 

definition split_sing :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set set nres"
  where 
  "split_sing \<alpha>' S = 
        FOREACHi
          (\<lambda> s1 s2. s2 = {\<alpha>. \<alpha> \<inter> \<alpha>' = {} \<and> \<alpha> \<in> S - s1} \<union> 
                         {\<alpha> | \<alpha> \<alpha>1. \<alpha>1 \<in> S - s1 \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> (\<alpha> = \<alpha>1 \<inter> \<alpha>')} \<union>
                         {\<alpha> | \<alpha> \<alpha>1. \<alpha>1 \<in> S - s1 \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<not> (\<alpha>1 \<subseteq> \<alpha>') \<and> 
                              \<alpha> = \<alpha>1 - \<alpha>1 \<inter> \<alpha>'}) 
                  S 
                  (\<lambda> \<alpha>1 tS. if (\<alpha>1 \<inter> \<alpha>' \<noteq> {})
                    then (if \<alpha>1 = \<alpha>1 \<inter> \<alpha>' then RETURN (tS \<union> {\<alpha>1})
                          else RETURN (tS \<union> {\<alpha>1 \<inter> \<alpha>', \<alpha>1 - \<alpha>1 \<inter> \<alpha>'}))
                    else 
                        RETURN (tS \<union> {\<alpha>1})
                  ) {}"

lemma split_sing_correct: 
  fixes S
  assumes finite_S: "finite S"
  shows "split_sing \<alpha>' S \<le> 
         SPEC (\<lambda> S'. S' = {\<alpha>. \<alpha> \<inter> \<alpha>' = {} \<and> \<alpha> \<in> S} \<union>
                          {\<alpha> | \<alpha> \<alpha>1. \<alpha>1 \<in> S \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<alpha> = \<alpha>1 \<inter> \<alpha>'} \<union> 
                          {\<alpha> | \<alpha> \<alpha>1. \<alpha>1 \<in> S \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<not> (\<alpha>1 \<subseteq> \<alpha>')  \<and> 
                               \<alpha> = \<alpha>1 - \<alpha>1 \<inter> \<alpha>'})"
                           
  unfolding split_sing_def
  apply (intro refine_vcg)
  using finite_S apply simp
      apply simp
     defer defer defer
  apply force
proof -
  {
    fix x it \<sigma>
    assume x_in_it: "x \<in> it"
       and it_subset_S: "it \<subseteq> S"
       and \<sigma>_def: "\<sigma> =
       {\<alpha>. \<alpha> \<inter> \<alpha>' = {} \<and> \<alpha> \<in> S - it} \<union>
       {uu. \<exists>\<alpha> \<alpha>1. uu = \<alpha> \<and> \<alpha>1 \<in> S - it \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<alpha> = \<alpha>1 \<inter> \<alpha>'} \<union>
       {uu.
        \<exists>\<alpha> \<alpha>1. uu = \<alpha> \<and> \<alpha>1 \<in> S - it \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and>\<not> (\<alpha>1 \<subseteq> \<alpha>')  \<and> \<alpha> = \<alpha>1 - \<alpha>1 \<inter> \<alpha>'}"
       and x\<alpha>': "x \<inter> \<alpha>' \<noteq> {}"
       and x\<alpha>'': "x = x \<inter> \<alpha>'"

   show "\<sigma> \<union> {x} =
       {\<alpha>. \<alpha> \<inter> \<alpha>' = {} \<and> \<alpha> \<in> S - (it - {x})} \<union>
       {uu. \<exists>\<alpha> \<alpha>1. uu = \<alpha> \<and> \<alpha>1 \<in> S - (it - {x}) \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<alpha> = \<alpha>1 \<inter> \<alpha>'} \<union>
       {uu.
        \<exists>\<alpha> \<alpha>1.
           uu = \<alpha> \<and> \<alpha>1 \<in> S - (it - {x}) \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<not> (\<alpha>1 \<subseteq> \<alpha>')  \<and> \<alpha> = \<alpha>1 - \<alpha>1 \<inter> \<alpha>'}"
   proof
     {
     show "\<sigma> \<union> {x}
           \<subseteq> {\<alpha>. \<alpha> \<inter> \<alpha>' = {} \<and> \<alpha> \<in> S - (it - {x})} \<union>
             {uu. \<exists>\<alpha> \<alpha>1. uu = \<alpha> \<and> \<alpha>1 \<in> S - (it - {x}) \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<alpha> = \<alpha>1 \<inter> \<alpha>'} \<union>
             {uu. \<exists>\<alpha> \<alpha>1. uu = \<alpha> \<and> \<alpha>1 \<in> S - (it - {x}) \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<not> (\<alpha>1 \<subseteq> \<alpha>') 
                  \<and> \<alpha> = \<alpha>1 - \<alpha>1 \<inter> \<alpha>'}"
     proof
       fix xa
       assume xa_def: "xa \<in> \<sigma> \<union> {x}"
       let ?res = "xa \<in> {\<alpha>. \<alpha> \<inter> \<alpha>' = {} \<and> \<alpha> \<in> S - (it - {x})} \<union>
                {uu.
                 \<exists>\<alpha> \<alpha>1. uu = \<alpha> \<and> \<alpha>1 \<in> S - (it - {x}) \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<alpha> = \<alpha>1 \<inter> \<alpha>'} \<union>
                {uu.
                 \<exists>\<alpha> \<alpha>1.
                    uu = \<alpha> \<and>
                    \<alpha>1 \<in> S - (it - {x}) \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<not> (\<alpha>1 \<subseteq> \<alpha>') \<and> \<alpha> = \<alpha>1 - \<alpha>1 \<inter> \<alpha>'}"
       from \<sigma>_def
       have res1: "xa \<in> \<sigma> \<Longrightarrow> ?res"
         by auto
       from x\<alpha>' x\<alpha>'' x_in_it it_subset_S
       have res2: "x \<in> {\<alpha>. \<alpha> \<inter> \<alpha>' = {} \<and> \<alpha> \<in> S - (it - {x})} \<union>
                {uu.
                 \<exists>\<alpha> \<alpha>1. uu = \<alpha> \<and> \<alpha>1 \<in> S - (it - {x}) \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<alpha> = \<alpha>1 \<inter> \<alpha>'} \<union>
                {uu.
                 \<exists>\<alpha> \<alpha>1.
                    uu = \<alpha> \<and>
                    \<alpha>1 \<in> S - (it - {x}) \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<not> (\<alpha>1 \<subseteq> \<alpha>') \<and> 
                    \<alpha> = \<alpha>1 - \<alpha>1 \<inter> \<alpha>'}"
         by auto
       from res1 res2 xa_def
       show ?res
         by auto
     qed
   }
   {
  show "{\<alpha>. \<alpha> \<inter> \<alpha>' = {} \<and> \<alpha> \<in> S - (it - {x})} \<union>
    {uu. \<exists>\<alpha> \<alpha>1. uu = \<alpha> \<and> \<alpha>1 \<in> S - (it - {x}) \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<alpha> = \<alpha>1 \<inter> \<alpha>'} \<union>
    {uu.
     \<exists>\<alpha> \<alpha>1. uu = \<alpha> \<and> \<alpha>1 \<in> S - (it - {x}) \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and>  \<not> (\<alpha>1 \<subseteq> \<alpha>') \<and> \<alpha> = \<alpha>1 - \<alpha>1 \<inter> \<alpha>'}
    \<subseteq> \<sigma> \<union> {x}"
     proof 
       fix xa
       assume xa_ct: "xa \<in> {\<alpha>. \<alpha> \<inter> \<alpha>' = {} \<and> \<alpha> \<in> S - (it - {x})} \<union>
               {uu.
                \<exists>\<alpha> \<alpha>1. uu = \<alpha> \<and> \<alpha>1 \<in> S - (it - {x}) \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> 
                  \<alpha> = \<alpha>1 \<inter> \<alpha>'} \<union>
               {uu.
                \<exists>\<alpha> \<alpha>1.
                   uu = \<alpha> \<and>
                   \<alpha>1 \<in> S - (it - {x}) \<and>
                   \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<not> (\<alpha>1 \<subseteq> \<alpha>') \<and> \<alpha> = \<alpha>1 - \<alpha>1 \<inter> \<alpha>'}"

       have branch1: "xa \<in> {uu.
                    \<exists>\<alpha> \<alpha>1. uu = \<alpha> \<and> \<alpha>1 \<in> S - (it - {x}) \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> 
                  \<alpha> = \<alpha>1 \<inter> \<alpha>'} \<Longrightarrow> 
            xa \<in> \<sigma> \<union> {x}"
       proof (cases "xa = x")
       case True
        then show ?thesis by simp
      next
        case False
        assume xa_def: "xa \<in> {uu. \<exists>\<alpha> \<alpha>1. uu = \<alpha> \<and> 
                        \<alpha>1 \<in> S - (it - {x}) \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<alpha> = \<alpha>1 \<inter> \<alpha>'} "
        from this False x\<alpha>' x\<alpha>''
        obtain \<alpha>1 where
        \<alpha>1_def: "\<alpha>1 \<in> S - (it - {x}) \<and>
                      \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> xa = \<alpha>1 \<inter> \<alpha>'"
          by auto
        from this x\<alpha>' x\<alpha>'' False
        have "\<alpha>1 \<noteq> x"
          by auto
        from this \<alpha>1_def
        have "\<exists>\<alpha>1. \<alpha>1 \<in> S - it \<and>
                      \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> xa = \<alpha>1 \<inter> \<alpha>'"
          by auto
        from this \<sigma>_def
        show "xa \<in> \<sigma> \<union> {x}"
          by auto
      qed

       have branch3: "xa \<in> {uu.
                \<exists>\<alpha> \<alpha>1.
                   uu = \<alpha> \<and>
                   \<alpha>1 \<in> S - (it - {x}) \<and>
                   \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<not> (\<alpha>1 \<subseteq> \<alpha>') \<and> \<alpha> = \<alpha>1 - \<alpha>1 \<inter> \<alpha>'}
             \<Longrightarrow> xa \<in> \<sigma> \<union> {x}"
       proof (cases "xa = x")
      case True
      then show ?thesis by simp
      next
        case False
        assume xa_cons: "xa \<in> {uu. \<exists>\<alpha> \<alpha>1. uu = \<alpha> \<and>
                      \<alpha>1 \<in> S - (it - {x}) \<and>
                      \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<not> (\<alpha>1 \<subseteq> \<alpha>') \<and> \<alpha> = \<alpha>1 - \<alpha>1 \<inter> \<alpha>'}"
        from this
        obtain \<alpha>1 where
        \<alpha>1_def: "\<alpha>1 \<in> S - (it - {x}) \<and>
                       \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<not> (\<alpha>1 \<subseteq> \<alpha>') \<and> xa = \<alpha>1 - \<alpha>1 \<inter> \<alpha>'" 
          by auto
        from this x\<alpha>' x\<alpha>''
        have "\<alpha>1 \<noteq> x"
          by auto
        from this \<sigma>_def \<alpha>1_def
        have "\<alpha>1 \<in> S - it \<and>
                       \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<not> (\<alpha>1 \<subseteq> \<alpha>') \<and> xa = \<alpha>1 - \<alpha>1 \<inter> \<alpha>'"
          by auto
        from this \<sigma>_def xa_cons
        show ?thesis 
          by blast
      qed
      

       have branch2: "xa \<in> {\<alpha>. \<alpha> \<inter> \<alpha>' = {} \<and> \<alpha> \<in> S - (it - {x})} \<Longrightarrow> xa \<in> \<sigma> \<union> {x}"
       proof (cases "xa = x")
         case True
         then show ?thesis 
          by auto
       next
         case False
         assume xa_def': "xa \<in> {\<alpha>. \<alpha> \<inter> \<alpha>' = {} \<and> \<alpha> \<in> S - (it - {x})}"
         from this False
         have "xa \<in> S - (it) \<and> xa \<inter> \<alpha>' = {}"
           by auto
         from this \<sigma>_def
         show ?thesis 
           by simp
       qed
       from xa_ct branch1 branch2 branch3
       show "xa \<in> \<sigma> \<union> {x}"
         by auto
     qed 
   }
 qed
}
  {
    fix x it \<sigma>
    assume x_in_it: "x \<in> it"
       and it_subset_S: "it \<subseteq> S"
       and \<sigma>_def: "\<sigma> =
       {\<alpha>. \<alpha> \<inter> \<alpha>' = {} \<and> \<alpha> \<in> S - it} \<union>
       {uu. \<exists>\<alpha> \<alpha>1. uu = \<alpha> \<and> \<alpha>1 \<in> S - it \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<alpha> = \<alpha>1 \<inter> \<alpha>'} \<union>
       {uu.
        \<exists>\<alpha> \<alpha>1.
           uu = \<alpha> \<and> \<alpha>1 \<in> S - it \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<not> \<alpha>1 \<subseteq> \<alpha>' \<and> \<alpha> = \<alpha>1 - \<alpha>1 \<inter> \<alpha>'}"
       and x\<alpha>': "x \<inter> \<alpha>' \<noteq> {}"
       and x\<alpha>'': "x \<noteq> x \<inter> \<alpha>'"
    show "\<sigma> \<union> {x \<inter> \<alpha>', x - x \<inter> \<alpha>'} =
       {\<alpha>. \<alpha> \<inter> \<alpha>' = {} \<and> \<alpha> \<in> S - (it - {x})} \<union>
       {uu. \<exists>\<alpha> \<alpha>1. uu = \<alpha> \<and> \<alpha>1 \<in> S - (it - {x}) \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<alpha> = \<alpha>1 \<inter> \<alpha>'} \<union>
       {uu.
        \<exists>\<alpha> \<alpha>1.
           uu = \<alpha> \<and>
           \<alpha>1 \<in> S - (it - {x}) \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<not> \<alpha>1 \<subseteq> \<alpha>' \<and> \<alpha> = \<alpha>1 - \<alpha>1 \<inter> \<alpha>'}"
    proof
      {
        show "\<sigma> \<union> {x \<inter> \<alpha>', x - x \<inter> \<alpha>'}
              \<subseteq> {\<alpha>. \<alpha> \<inter> \<alpha>' = {} \<and> \<alpha> \<in> S - (it - {x})} \<union>
              {uu. \<exists>\<alpha> \<alpha>1. uu = \<alpha> \<and> \<alpha>1 \<in> S - (it - {x}) \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> 
                   \<alpha> = \<alpha>1 \<inter> \<alpha>'} \<union>
       {uu.
        \<exists>\<alpha> \<alpha>1.
           uu = \<alpha> \<and>
           \<alpha>1 \<in> S - (it - {x}) \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<not> \<alpha>1 \<subseteq> \<alpha>' \<and> \<alpha> = \<alpha>1 - \<alpha>1 \<inter> \<alpha>'}"
        proof
          fix xa
          assume xa_in: "xa \<in> \<sigma> \<union> {x \<inter> \<alpha>', x - x \<inter> \<alpha>'}"
          show "xa \<in> {\<alpha>. \<alpha> \<inter> \<alpha>' = {} \<and> \<alpha> \<in> S - (it - {x})} \<union>
                {uu.
                 \<exists>\<alpha> \<alpha>1. uu = \<alpha> \<and> \<alpha>1 \<in> S - (it - {x}) \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<alpha> = \<alpha>1 \<inter> \<alpha>'} \<union>
                {uu.
                 \<exists>\<alpha> \<alpha>1.
                    uu = \<alpha> \<and>
                    \<alpha>1 \<in> S - (it - {x}) \<and>
                    \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<not> \<alpha>1 \<subseteq> \<alpha>' \<and> \<alpha> = \<alpha>1 - \<alpha>1 \<inter> \<alpha>'}"
          proof (cases "xa \<in> \<sigma>")
            case True
            from this \<sigma>_def show ?thesis by auto
          next                        
            case False
            from this xa_in
            have xa_in': "xa = x \<inter> \<alpha>' \<or> xa = x - x \<inter> \<alpha>'"
              by auto
            let ?thesis' = "xa \<in> {\<alpha>. \<alpha> \<inter> \<alpha>' = {} \<and> \<alpha> \<in> S - (it - {x})} \<union>
          {uu. \<exists>\<alpha> \<alpha>1. uu = \<alpha> \<and> \<alpha>1 \<in> S - (it - {x}) \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<alpha> = \<alpha>1 \<inter> \<alpha>'} \<union>
          {uu.
           \<exists>\<alpha> \<alpha>1.
              uu = \<alpha> \<and>
              \<alpha>1 \<in> S - (it - {x}) \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<not> \<alpha>1 \<subseteq> \<alpha>' \<and> \<alpha> = \<alpha>1 - \<alpha>1 \<inter> \<alpha>'}"
            from x\<alpha>' x\<alpha>'' xa_in' x_in_it it_subset_S
            have x_cons: "x \<in> S - (it - {x}) \<and> x \<inter> \<alpha>' \<noteq> {}"
              by auto
            from this
            have thesis1: "xa = x \<inter> \<alpha>' \<Longrightarrow> ?thesis'" 
              by auto
            from x\<alpha>' x\<alpha>'' xa_in' x_in_it it_subset_S
            have x_cons: "x \<in> S - (it - {x}) \<and> x \<inter> \<alpha>' \<noteq> {} \<and> \<not> x \<subseteq> \<alpha>'"
              by auto
            from this
            have thesis2: "xa = x - x \<inter> \<alpha>' \<Longrightarrow> ?thesis"
              by auto
            from thesis2 thesis1 False xa_in
            show ?thesis'
              by blast
          qed qed
        }
        {
          show "{\<alpha>. \<alpha> \<inter> \<alpha>' = {} \<and> \<alpha> \<in> S - (it - {x})} \<union>
    {uu. \<exists>\<alpha> \<alpha>1. uu = \<alpha> \<and> \<alpha>1 \<in> S - (it - {x}) \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<alpha> = \<alpha>1 \<inter> \<alpha>'} \<union>
    {uu.
     \<exists>\<alpha> \<alpha>1.
        uu = \<alpha> \<and> \<alpha>1 \<in> S - (it - {x}) \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<not> \<alpha>1 \<subseteq> \<alpha>' \<and> \<alpha> = \<alpha>1 - \<alpha>1 \<inter> \<alpha>'}
    \<subseteq> \<sigma> \<union> {x \<inter> \<alpha>', x - x \<inter> \<alpha>'}"
          proof 
            fix xa
            assume xa_in: "xa \<in> {\<alpha>. \<alpha> \<inter> \<alpha>' = {} \<and> \<alpha> \<in> S - (it - {x})} \<union>
               {uu.
                \<exists>\<alpha> \<alpha>1. uu = \<alpha> \<and> \<alpha>1 \<in> S - (it - {x}) \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<alpha> = \<alpha>1 \<inter> \<alpha>'} \<union>
               {uu.
                \<exists>\<alpha> \<alpha>1.
                   uu = \<alpha> \<and>
                   \<alpha>1 \<in> S - (it - {x}) \<and>
                   \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<not> \<alpha>1 \<subseteq> \<alpha>' \<and> \<alpha> = \<alpha>1 - \<alpha>1 \<inter> \<alpha>'}"
            
            have case1: "xa \<in> {\<alpha>. \<alpha> \<inter> \<alpha>' = {} \<and> \<alpha> \<in> S - (it - {x})} \<Longrightarrow> 
                         xa \<in> \<sigma> \<union> {x \<inter> \<alpha>', x - x \<inter> \<alpha>'}"
            proof (cases "xa = x")
              case True
              assume xa_in1: "xa \<in> {\<alpha>. \<alpha> \<inter> \<alpha>' = {} \<and> \<alpha> \<in> S - (it - {x})}"
              from this have "xa \<inter> \<alpha>' = {} \<and> xa \<in> S - (it - {x})"
                by auto
            from this x\<alpha>' True
            show ?thesis 
              by auto
            next
              case False
              assume xa_in1: "xa \<in> {\<alpha>. \<alpha> \<inter> \<alpha>' = {} \<and> \<alpha> \<in> S - (it - {x})}"
              from this False 
              have "xa \<inter> \<alpha>' = {} \<and> xa \<in> S - it"
                by auto
              from this \<sigma>_def 
              show ?thesis by auto
            qed   
            have case2: "xa \<in> {uu.
                \<exists>\<alpha> \<alpha>1. uu = \<alpha> \<and> \<alpha>1 \<in> S - (it - {x}) \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<alpha> = \<alpha>1 \<inter> \<alpha>'} \<Longrightarrow>
              xa \<in> \<sigma> \<union> {x \<inter> \<alpha>', x - x \<inter> \<alpha>'}"
            proof (cases "xa = x")
              case True
              assume xa_cons1: "xa \<in> {uu. \<exists>\<alpha> \<alpha>1. uu = \<alpha> \<and> \<alpha>1 \<in> S - (it - {x}) \<and> 
                                        \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<alpha> = \<alpha>1 \<inter> \<alpha>'}"
              from this obtain \<alpha>1 where 
              \<alpha>1_def : "\<alpha>1 \<in> S - (it - {x}) \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> xa = \<alpha>1 \<inter> \<alpha>'"
                by auto
              show ?thesis 
              proof (cases "x = \<alpha>1")
                case True
                from this \<alpha>1_def show ?thesis by simp
              next
                case False 
                from this \<alpha>1_def
                have "\<alpha>1 \<in> S - it \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> xa = \<alpha>1 \<inter> \<alpha>'"
                  by auto
                from this \<sigma>_def
                show ?thesis by auto
              qed
            next
              case False
              note xa_neq_x = False
              assume xa_cons1: "xa \<in> {uu. \<exists>\<alpha> \<alpha>1. uu = \<alpha> \<and> \<alpha>1 \<in> S - (it - {x}) \<and> 
                                        \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<alpha> = \<alpha>1 \<inter> \<alpha>'}"
              from this False 
              obtain \<alpha>1 where
              \<alpha>1_def: "\<alpha>1 \<in> S - (it - {x}) \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> xa = \<alpha>1 \<inter> \<alpha>'"
                by auto
              show ?thesis
              proof (cases "\<alpha>1 = x")
                case True
                from this \<alpha>1_def 
                show ?thesis by simp
                next
                  case False
                  from this \<alpha>1_def
                  have "\<alpha>1 \<in> S - it \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> xa = \<alpha>1 \<inter> \<alpha>'"
                    by auto
                  from this xa_neq_x \<sigma>_def
                  show ?thesis by auto
                qed
              qed

        have case3: "xa \<in> {uu.
                \<exists>\<alpha> \<alpha>1.
                   uu = \<alpha> \<and>
                   \<alpha>1 \<in> S - (it - {x}) \<and>
                   \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<not> \<alpha>1 \<subseteq> \<alpha>' \<and> \<alpha> = \<alpha>1 - \<alpha>1 \<inter> \<alpha>'} \<Longrightarrow> 
                xa \<in> \<sigma> \<union> {x \<inter> \<alpha>', x - x \<inter> \<alpha>'}"
        proof -
          assume xa_in1: "xa \<in> {uu.
                \<exists>\<alpha> \<alpha>1.
                   uu = \<alpha> \<and>
                   \<alpha>1 \<in> S - (it - {x}) \<and>
                   \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<not> \<alpha>1 \<subseteq> \<alpha>' \<and> \<alpha> = \<alpha>1 - \<alpha>1 \<inter> \<alpha>'}"
          from this 
          obtain \<alpha>1 where 
           \<alpha>1_def : "\<alpha>1 \<in> S - (it - {x}) \<and>
                     \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<not> \<alpha>1 \<subseteq> \<alpha>' \<and> xa = \<alpha>1 - \<alpha>1 \<inter> \<alpha>'"
            by auto
          show "xa \<in> \<sigma> \<union> {x \<inter> \<alpha>', x - x \<inter> \<alpha>'}"
          proof (cases "\<alpha>1 = x")
            case True
            from this \<alpha>1_def 
            have "x \<in> S - (it - {x}) \<and>
                     x \<inter> \<alpha>' \<noteq> {} \<and> \<not> x \<subseteq> \<alpha>' \<and> xa = x - x \<inter> \<alpha>'"
              by simp
            from this 
            show ?thesis 
              by simp
          next
            case False
            from this \<alpha>1_def 
            have "\<alpha>1 \<in> S - it \<and>
                     \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<not> \<alpha>1 \<subseteq> \<alpha>' \<and> xa = \<alpha>1 - \<alpha>1 \<inter> \<alpha>'"
              by simp
            from this \<sigma>_def
            show ?thesis by auto
          qed
        qed
       
            from case1 case2 case3 xa_in
            show "xa \<in> \<sigma> \<union> {x \<inter> \<alpha>', x - x \<inter> \<alpha>'}"
              by force
          qed
        }
      qed
    }
    {
       fix x it \<sigma>
    assume x_in_it: "x \<in> it"
       and it_subset_S: "it \<subseteq> S"
       and \<sigma>_def: "\<sigma> =
       {\<alpha>. \<alpha> \<inter> \<alpha>' = {} \<and> \<alpha> \<in> S - it} \<union>
       {uu. \<exists>\<alpha> \<alpha>1. uu = \<alpha> \<and> \<alpha>1 \<in> S - it \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<alpha> = \<alpha>1 \<inter> \<alpha>'} \<union>
       {uu.
        \<exists>\<alpha> \<alpha>1.
           uu = \<alpha> \<and> \<alpha>1 \<in> S - it \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<not> \<alpha>1 \<subseteq> \<alpha>' \<and> \<alpha> = \<alpha>1 - \<alpha>1 \<inter> \<alpha>'}"
       and x\<alpha>': "\<not> x \<inter> \<alpha>' \<noteq> {}"


    show "\<sigma> \<union> {x} =
       {\<alpha>. \<alpha> \<inter> \<alpha>' = {} \<and> \<alpha> \<in> S - (it - {x})} \<union>
       {uu. \<exists>\<alpha> \<alpha>1. uu = \<alpha> \<and> \<alpha>1 \<in> S - (it - {x}) \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<alpha> = \<alpha>1 \<inter> \<alpha>'} \<union>
       {uu.
        \<exists>\<alpha> \<alpha>1.
           uu = \<alpha> \<and>
           \<alpha>1 \<in> S - (it - {x}) \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<not> \<alpha>1 \<subseteq> \<alpha>' \<and> \<alpha> = \<alpha>1 - \<alpha>1 \<inter> \<alpha>'}"
    proof
      {
        show "\<sigma> \<union> {x}
    \<subseteq> {\<alpha>. \<alpha> \<inter> \<alpha>' = {} \<and> \<alpha> \<in> S - (it - {x})} \<union>
       {uu. \<exists>\<alpha> \<alpha>1. uu = \<alpha> \<and> \<alpha>1 \<in> S - (it - {x}) \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<alpha> = \<alpha>1 \<inter> \<alpha>'} \<union>
       {uu.
        \<exists>\<alpha> \<alpha>1.
           uu = \<alpha> \<and>
           \<alpha>1 \<in> S - (it - {x}) \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<not> \<alpha>1 \<subseteq> \<alpha>' \<and> \<alpha> = \<alpha>1 - \<alpha>1 \<inter> \<alpha>'}"
        proof
          fix xa
          assume xa_cons: "xa \<in> \<sigma> \<union> {x}"
          let ?thesis' = "xa \<in> {\<alpha>. \<alpha> \<inter> \<alpha>' = {} \<and> \<alpha> \<in> S - (it - {x})} \<union>
                {uu.
                 \<exists>\<alpha> \<alpha>1. uu = \<alpha> \<and> \<alpha>1 \<in> S - (it - {x}) \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<alpha> = \<alpha>1 \<inter> \<alpha>'} \<union>
                {uu.
                 \<exists>\<alpha> \<alpha>1.
                    uu = \<alpha> \<and>
                    \<alpha>1 \<in> S - (it - {x}) \<and>
                    \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<not> \<alpha>1 \<subseteq> \<alpha>' \<and> \<alpha> = \<alpha>1 - \<alpha>1 \<inter> \<alpha>'}"
          show ?thesis'
          proof (cases "xa = x")
          case True
          from xa_cons \<sigma>_def x\<alpha>' x_in_it it_subset_S
          show ?thesis 
            using True by auto
          next
            case False
            from this xa_cons
            have xa_cons': "xa \<in> \<sigma>"
              by auto
            from x\<alpha>' x_in_it it_subset_S
            have case1: "xa \<in> {\<alpha>. \<alpha> \<inter> \<alpha>' = {} \<and> \<alpha> \<in> S - it} \<Longrightarrow> 
                  xa \<in> {\<alpha>. \<alpha> \<inter> \<alpha>' = {} \<and> \<alpha> \<in> S - (it - {x})}"
              by blast

            from x\<alpha>' x_in_it it_subset_S
            have case2: "xa \<in> {uu. \<exists>\<alpha> \<alpha>1. uu = \<alpha> \<and> \<alpha>1 \<in> S - it \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<alpha> = \<alpha>1 \<inter> \<alpha>'} 
                    \<Longrightarrow>
                  xa \<in> {uu. \<exists>\<alpha> \<alpha>1. uu = \<alpha> \<and> \<alpha>1 \<in> S - (it - {x}) \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} 
                            \<and> \<alpha> = \<alpha>1 \<inter> \<alpha>'}"
              by blast      

            from x\<alpha>' x_in_it it_subset_S
            have case3: "xa \<in> {uu.
           \<exists>\<alpha> \<alpha>1.
              uu = \<alpha> \<and>
              \<alpha>1 \<in> S - (it - {x}) \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<not> \<alpha>1 \<subseteq> \<alpha>' \<and> \<alpha> = \<alpha>1 - \<alpha>1 \<inter> \<alpha>'} \<Longrightarrow>
            xa \<in>  {uu.
           \<exists>\<alpha> \<alpha>1.
              uu = \<alpha> \<and>
              \<alpha>1 \<in> S - (it - {x}) \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<not> \<alpha>1 \<subseteq> \<alpha>' \<and> \<alpha> = \<alpha>1 - \<alpha>1 \<inter> \<alpha>'}"
              by blast
            
            from case1 case2 case3 xa_cons' \<sigma>_def
            show ?thesis 
              by blast
          qed
        qed
      }

      {
        show "{\<alpha>. \<alpha> \<inter> \<alpha>' = {} \<and> \<alpha> \<in> S - (it - {x})} \<union>
    {uu. \<exists>\<alpha> \<alpha>1. uu = \<alpha> \<and> \<alpha>1 \<in> S - (it - {x}) \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<alpha> = \<alpha>1 \<inter> \<alpha>'} \<union>
    {uu.
     \<exists>\<alpha> \<alpha>1.
        uu = \<alpha> \<and> \<alpha>1 \<in> S - (it - {x}) \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<not> \<alpha>1 \<subseteq> \<alpha>' \<and> \<alpha> = \<alpha>1 - \<alpha>1 \<inter> \<alpha>'}
    \<subseteq> \<sigma> \<union> {x}"
        proof
          fix xa
          assume xa_cons: "xa \<in> {\<alpha>. \<alpha> \<inter> \<alpha>' = {} \<and> \<alpha> \<in> S - (it - {x})} \<union>
               {uu.
                \<exists>\<alpha> \<alpha>1. uu = \<alpha> \<and> \<alpha>1 \<in> S - (it - {x}) \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<alpha> = \<alpha>1 \<inter> \<alpha>'} \<union>
               {uu.
                \<exists>\<alpha> \<alpha>1.
                   uu = \<alpha> \<and>
                   \<alpha>1 \<in> S - (it - {x}) \<and>
                   \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<not> \<alpha>1 \<subseteq> \<alpha>' \<and> \<alpha> = \<alpha>1 - \<alpha>1 \<inter> \<alpha>'}"
          show "xa \<in> \<sigma> \<union> {x}"
          proof (cases "xa = x")
            case True
            then show ?thesis by auto
          next
            case False
            from x\<alpha>' x_in_it it_subset_S False
            have case1: "xa \<in> {\<alpha>. \<alpha> \<inter> \<alpha>' = {} \<and> \<alpha> \<in> S - (it - {x})} \<Longrightarrow>
                         xa \<in> {\<alpha>. \<alpha> \<inter> \<alpha>' = {} \<and> \<alpha> \<in> S - it}"
              by blast

            from x\<alpha>' x_in_it it_subset_S
            have case2: 
                "xa \<in> {uu. \<exists>\<alpha> \<alpha>1. uu = \<alpha> \<and> \<alpha>1 \<in> S - (it - {x}) \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} 
                            \<and> \<alpha> = \<alpha>1 \<inter> \<alpha>'} \<Longrightarrow>
                xa \<in> {uu. \<exists>\<alpha> \<alpha>1. uu = \<alpha> \<and> \<alpha>1 \<in> S - it \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<alpha> = \<alpha>1 \<inter> \<alpha>'}"
              by blast      

            from x\<alpha>' x_in_it it_subset_S
            have case3: "xa \<in>  {uu.
           \<exists>\<alpha> \<alpha>1.
              uu = \<alpha> \<and>
              \<alpha>1 \<in> S - (it - {x}) \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<not> \<alpha>1 \<subseteq> \<alpha>' \<and> \<alpha> = \<alpha>1 - \<alpha>1 \<inter> \<alpha>'}
              \<Longrightarrow>
            xa \<in> {uu.
           \<exists>\<alpha> \<alpha>1.
              uu = \<alpha> \<and>
              \<alpha>1 \<in> S - it \<and> \<alpha>1 \<inter> \<alpha>' \<noteq> {} \<and> \<not> \<alpha>1 \<subseteq> \<alpha>' \<and> \<alpha> = \<alpha>1 - \<alpha>1 \<inter> \<alpha>'}"
              by blast
            from case1 case2 case3 False \<sigma>_def xa_cons
            show ?thesis 
              by auto
          qed
        qed
      }
    qed
  }
qed 

definition split_mult :: "'a set set \<Rightarrow> 'a set  \<Rightarrow> 'a set set nres"
  where 
  "split_mult lbs \<alpha> = 
        (FOREACHi 
             (\<lambda> lbs' s_lbs'. 
                 (\<Union> s_lbs' = \<alpha> \<and> finite s_lbs') \<and>
                 (\<forall> \<alpha>1 \<alpha>2. \<alpha>1 \<in> s_lbs' \<and> \<alpha>2 \<in> s_lbs' \<longrightarrow> 
                            \<alpha>1 = \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {}) \<and>
                 (\<forall> \<alpha>3 \<alpha>4. \<alpha>3 \<in> s_lbs' \<and> 
                            \<alpha>4 \<in> lbs - lbs' \<longrightarrow> \<alpha>3 \<subseteq> \<alpha>4 \<or> \<alpha>3 \<inter> \<alpha>4 = {}) \<and> 
                 (\<forall> \<alpha>5 \<in> s_lbs'. 
                    \<exists> s \<subseteq> lbs - lbs'. (\<alpha>5 \<subseteq> \<Inter> s \<inter> \<alpha> \<and> 
                                       (\<forall> \<alpha>6 \<in> lbs - lbs' - (s \<union> {\<alpha>}). \<alpha>5 \<inter> \<alpha>6 = {})) \<and>
                          (\<forall> \<alpha>7. \<alpha>7 \<subseteq> \<Inter> s \<inter> \<alpha> \<and> (\<forall> \<alpha>8 \<in> lbs - lbs' - (s \<union> {\<alpha>}). 
                                              \<alpha>7 \<inter> \<alpha>8 = {}) \<longrightarrow> 
                                 \<alpha>7 \<subseteq> \<alpha>5))
              ) 
             lbs
             (\<lambda> \<alpha>' s_lbs. 
                split_sing \<alpha>' s_lbs
              ) {\<alpha>}
            )"


definition split_tran :: "'q \<Rightarrow> 'a set \<Rightarrow> 'q \<Rightarrow> 'a set set \<Rightarrow> ('q, 'a) LTS nres" 
  where "split_tran q \<alpha> q' lbs = do {
           s_lbs \<leftarrow> split_mult lbs \<alpha>;
         FOREACHi
             (\<lambda> s_lbs' trans'.
               (\<forall> (q1, \<alpha>1', q1') \<in> trans'. q = q1 \<and> q' = q1') \<and> 
               \<Union> {\<alpha>1. (q, \<alpha>1, q') \<in> trans'} = \<Union> (s_lbs - s_lbs') \<and>
               {\<alpha>1. (q, \<alpha>1, q') \<in> trans'} = s_lbs - s_lbs' \<and>
               (\<forall> (q, \<alpha>1, q') \<in> trans'. 
                    \<exists> s \<subseteq> lbs. (\<alpha>1 \<subseteq> \<Inter> s \<and> (\<forall> \<alpha>2 \<in> lbs - s. \<alpha>1 \<inter> \<alpha>2 = {})) \<and>
                          (\<forall> \<alpha>3. \<alpha>3 \<subseteq> \<Inter> s \<and> (\<forall> \<alpha>4 \<in> lbs - s. \<alpha>3 \<inter> \<alpha>4 = {}) \<longrightarrow> 
                                 \<alpha>3 \<subseteq> \<alpha>1))  \<and>
               (\<forall> \<alpha>1 \<alpha>2. {\<alpha>1, \<alpha>2} \<subseteq> {\<alpha>1. (q, \<alpha>1, q') \<in> trans'} \<longrightarrow> 
                        \<alpha>1 = \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {})\<and>
               (\<forall> \<alpha>1 \<alpha>2. \<alpha>1 \<in> {\<alpha>1. (q, \<alpha>1, q') \<in> trans'} \<and>
                          \<alpha>2 \<in> lbs \<longrightarrow> 
                          \<alpha>1 \<subseteq> \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {}))
             s_lbs
             (\<lambda> \<alpha>' new_trans'. 
               RETURN (new_trans' \<union> {(q, \<alpha>', q')}))
          {}
        }"

lemma split_tran_correct:
  fixes q \<alpha> q' lbs 
  assumes finite_lbs: "finite lbs \<and> \<alpha> \<in> lbs"
  shows "split_tran q \<alpha> q' lbs \<le> 
         SPEC (\<lambda> trans.
               (\<forall> (q1, \<alpha>1', q1') \<in> trans. q = q1 \<and> q' = q1') \<and> 
               \<Union> {\<alpha>1. (q, \<alpha>1, q') \<in> trans} = \<alpha> \<and> 
               (\<forall> \<alpha>1 \<alpha>2. {\<alpha>1, \<alpha>2} \<subseteq> {\<alpha>1. (q, \<alpha>1, q') \<in> trans} \<longrightarrow> 
                        \<alpha>1 = \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {}) \<and>
               (\<forall> (q, \<alpha>1, q') \<in> trans. 
                    \<exists> s \<subseteq> lbs. (\<alpha>1 \<subseteq> \<Inter> s \<and> (\<forall> \<alpha>2 \<in> lbs - s. \<alpha>1 \<inter> \<alpha>2 = {})) \<and>
                          (\<forall> \<alpha>3. \<alpha>3 \<subseteq> \<Inter> s \<and> (\<forall> \<alpha>4 \<in> lbs - s. \<alpha>3 \<inter> \<alpha>4 = {}) \<longrightarrow> 
                                 \<alpha>3 \<subseteq> \<alpha>1))  \<and>
               (\<forall> \<alpha>1 \<alpha>2. \<alpha>1 \<in> {\<alpha>1. (q, \<alpha>1, q') \<in> trans} \<and>
                          \<alpha>2 \<in> lbs \<longrightarrow> 
                          \<alpha>1 \<subseteq> \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {}))"
  unfolding split_tran_def split_mult_def
  apply (intro refine_vcg)
  using finite_lbs apply simp
  apply simp
  defer
  apply simp
proof -
  {
    fix x it \<sigma>
    assume x_in_it: "x \<in> it"  
       and it_sub_lbs: "it \<subseteq> lbs"
       and \<sigma>_def: "(\<Union> \<sigma> = \<alpha> \<and> finite \<sigma>) \<and>
                   (\<forall>\<alpha>1 \<alpha>2. \<alpha>1 \<in> \<sigma> \<and> \<alpha>2 \<in> \<sigma> \<longrightarrow> 
                                \<alpha>1 = \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {}) \<and>
                   (\<forall>\<alpha>3 \<alpha>4. \<alpha>3 \<in> \<sigma> \<and> \<alpha>4 \<in> lbs - it \<longrightarrow> 
                                \<alpha>3 \<subseteq> \<alpha>4 \<or> \<alpha>3 \<inter> \<alpha>4 = {}) \<and>
                   (\<forall>\<alpha>5\<in>\<sigma>. \<exists>s\<subseteq>lbs - it.
                        (\<alpha>5 \<subseteq> \<Inter> s \<inter> \<alpha> \<and> (\<forall>\<alpha>6\<in>lbs - it - (s \<union> {\<alpha>}). \<alpha>5 \<inter> \<alpha>6 = {})) \<and>
                   (\<forall>\<alpha>7. \<alpha>7 \<subseteq> \<Inter> s \<inter> \<alpha> \<and> (\<forall>\<alpha>8\<in>lbs - it - (s \<union> {\<alpha>}). \<alpha>7 \<inter> \<alpha>8 = {}) 
                        \<longrightarrow> \<alpha>7 \<subseteq> \<alpha>5))"
    from \<sigma>_def finite_lbs 
    have finite_\<sigma>: "finite \<sigma>"
    by force

    thm split_sing_correct[OF finite_\<sigma>, of x]
    have "SPEC (\<lambda>S'. S' =
              {\<alpha>. \<alpha> \<inter> x = {} \<and> \<alpha> \<in> \<sigma>} \<union>
              {uu. \<exists>\<alpha> \<alpha>1. uu = \<alpha> \<and> \<alpha>1 \<in> \<sigma> \<and> \<alpha>1 \<inter> x \<noteq> {} \<and> \<alpha> = \<alpha>1 \<inter> x} \<union>
              {uu.
               \<exists>\<alpha> \<alpha>1. uu = \<alpha> \<and> \<alpha>1 \<in> \<sigma> \<and> \<alpha>1 \<inter> x \<noteq> {} \<and> \<not> \<alpha>1 \<subseteq> x \<and> \<alpha> = \<alpha>1 - \<alpha>1 \<inter> x}) \<le>
         SPEC (\<lambda>s_lbs'.
                   (\<Union> s_lbs' = \<alpha> \<and> finite s_lbs') \<and>
                   (\<forall>\<alpha>1 \<alpha>2. \<alpha>1 \<in> s_lbs' \<and> \<alpha>2 \<in> s_lbs' \<longrightarrow> \<alpha>1 = \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {}) \<and>
                   (\<forall>\<alpha>3 \<alpha>4.
                       \<alpha>3 \<in> s_lbs' \<and> \<alpha>4 \<in> lbs - (it - {x}) \<longrightarrow>
                       \<alpha>3 \<subseteq> \<alpha>4 \<or> \<alpha>3 \<inter> \<alpha>4 = {}) \<and>
                   (\<forall>\<alpha>5\<in>s_lbs'.
                       \<exists>s\<subseteq>lbs - (it - {x}).
                          (\<alpha>5 \<subseteq> \<Inter> s \<inter> \<alpha> \<and>
                           (\<forall>\<alpha>6\<in>lbs - (it - {x}) - (s \<union> {\<alpha>}). \<alpha>5 \<inter> \<alpha>6 = {})) \<and>
                          (\<forall>\<alpha>7. \<alpha>7 \<subseteq> \<Inter> s \<inter> \<alpha> \<and>
                                 (\<forall>\<alpha>8\<in>lbs - (it - {x}) - (s \<union> {\<alpha>}). \<alpha>7 \<inter> \<alpha>8 = {}) \<longrightarrow>
                                 \<alpha>7 \<subseteq> \<alpha>5)))"
      apply simp
    proof 
      {
        show "\<Union> {\<alpha>. \<alpha> \<inter> x = {} \<and> \<alpha> \<in> \<sigma>} \<union> 
              \<Union> {uu. \<exists>\<alpha>1. \<alpha>1 \<in> \<sigma> \<and> \<alpha>1 \<inter> x \<noteq> {} \<and> uu = \<alpha>1 \<inter> x} \<union>
              \<Union> {uu. \<exists>\<alpha>1. \<alpha>1 \<in> \<sigma> \<and> \<alpha>1 \<inter> x \<noteq> {} \<and> \<not> \<alpha>1 \<subseteq> x \<and> uu = \<alpha>1 - \<alpha>1 \<inter> x} =
              \<alpha>"
        proof 
          { 
            from \<sigma>_def
            show "\<Union> {\<alpha>. \<alpha> \<inter> x = {} \<and> \<alpha> \<in> \<sigma>} \<union> 
                  \<Union> {uu. \<exists>\<alpha>1. \<alpha>1 \<in> \<sigma> \<and> \<alpha>1 \<inter> x \<noteq> {} \<and> uu = \<alpha>1 \<inter> x} \<union>
                  \<Union> {uu. \<exists>\<alpha>1. \<alpha>1 \<in> \<sigma> \<and> \<alpha>1 \<inter> x \<noteq> {} \<and> \<not> \<alpha>1 \<subseteq> x \<and> uu = \<alpha>1 - \<alpha>1 \<inter> x}
                 \<subseteq> \<alpha>"
              by blast
          }
          {
            show "\<alpha> \<subseteq> \<Union> {\<alpha>. \<alpha> \<inter> x = {} \<and> \<alpha> \<in> \<sigma>} \<union>
                  \<Union> {uu. \<exists>\<alpha>1. \<alpha>1 \<in> \<sigma> \<and> \<alpha>1 \<inter> x \<noteq> {} \<and> uu = \<alpha>1 \<inter> x} \<union>
                  \<Union> {uu. \<exists>\<alpha>1. \<alpha>1 \<in> \<sigma> \<and> \<alpha>1 \<inter> x \<noteq> {} \<and> \<not> \<alpha>1 \<subseteq> x \<and> uu = \<alpha>1 - \<alpha>1 \<inter> x}"
            proof
              fix xa
              assume xa_in_\<alpha>: "xa \<in> \<alpha>"
              thm \<sigma>_def
              show "xa \<in> \<Union> {\<alpha>. \<alpha> \<inter> x = {} \<and> \<alpha> \<in> \<sigma>} \<union>
                \<Union> {uu. \<exists>\<alpha>1. \<alpha>1 \<in> \<sigma> \<and> \<alpha>1 \<inter> x \<noteq> {} \<and> uu = \<alpha>1 \<inter> x} \<union>
                \<Union> {uu. \<exists>\<alpha>1. \<alpha>1 \<in> \<sigma> \<and> \<alpha>1 \<inter> x \<noteq> {} \<and> \<not> \<alpha>1 \<subseteq> x \<and> uu = \<alpha>1 - \<alpha>1 \<inter> x}"
              proof (cases "\<exists> \<alpha>. xa \<in> \<alpha> \<and> \<alpha> \<inter> x = {} \<and> \<alpha> \<in> \<sigma>")
              case True
                then show ?thesis by blast
              next
                case False
                from xa_in_\<alpha> \<sigma>_def
                obtain \<alpha>1 where
                \<alpha>1_def: "xa \<in> \<alpha>1 \<and> \<alpha>1 \<in> \<sigma>"
                  by force
                from this False
                have "\<alpha>1 \<inter> x \<noteq> {}"
                  by auto
                from this \<alpha>1_def
                show ?thesis
                  by blast
              qed
            qed
          }
        qed
      }

      {
        show "finite {\<alpha>. \<alpha> \<inter> x = {} \<and> \<alpha> \<in> \<sigma>} \<and>
    finite {uu. \<exists>\<alpha>1. \<alpha>1 \<in> \<sigma> \<and> \<alpha>1 \<inter> x \<noteq> {} \<and> uu = \<alpha>1 \<inter> x} \<and>
    finite {uu. \<exists>\<alpha>1. \<alpha>1 \<in> \<sigma> \<and> \<alpha>1 \<inter> x \<noteq> {} \<and> \<not> \<alpha>1 \<subseteq> x \<and> uu = \<alpha>1 - \<alpha>1 \<inter> x} \<and>
    (\<forall>\<alpha>1 \<alpha>2.
        (\<alpha>1 \<inter> x = {} \<and> \<alpha>1 \<in> \<sigma> \<or>
         (\<exists>\<alpha>1a. \<alpha>1a \<in> \<sigma> \<and> \<alpha>1a \<inter> x \<noteq> {} \<and> \<alpha>1 = \<alpha>1a \<inter> x) \<or>
         (\<exists>\<alpha>1a. \<alpha>1a \<in> \<sigma> \<and> \<alpha>1a \<inter> x \<noteq> {} \<and> \<not> \<alpha>1a \<subseteq> x \<and> \<alpha>1 = \<alpha>1a - \<alpha>1a \<inter> x)) \<and>
        (\<alpha>2 \<inter> x = {} \<and> \<alpha>2 \<in> \<sigma> \<or>
         (\<exists>\<alpha>1. \<alpha>1 \<in> \<sigma> \<and> \<alpha>1 \<inter> x \<noteq> {} \<and> \<alpha>2 = \<alpha>1 \<inter> x) \<or>
         (\<exists>\<alpha>1. \<alpha>1 \<in> \<sigma> \<and> \<alpha>1 \<inter> x \<noteq> {} \<and> \<not> \<alpha>1 \<subseteq> x \<and> \<alpha>2 = \<alpha>1 - \<alpha>1 \<inter> x)) \<longrightarrow>
        \<alpha>1 = \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {}) \<and>
    (\<forall>\<alpha>3 \<alpha>4.
        (\<alpha>3 \<inter> x = {} \<and> \<alpha>3 \<in> \<sigma> \<or>
         (\<exists>\<alpha>1. \<alpha>1 \<in> \<sigma> \<and> \<alpha>1 \<inter> x \<noteq> {} \<and> \<alpha>3 = \<alpha>1 \<inter> x) \<or>
         (\<exists>\<alpha>1. \<alpha>1 \<in> \<sigma> \<and> \<alpha>1 \<inter> x \<noteq> {} \<and> \<not> \<alpha>1 \<subseteq> x \<and> \<alpha>3 = \<alpha>1 - \<alpha>1 \<inter> x)) \<and>
        \<alpha>4 \<in> lbs \<and> (\<alpha>4 \<in> it \<longrightarrow> \<alpha>4 = x) \<longrightarrow>
        \<alpha>3 \<subseteq> \<alpha>4 \<or> \<alpha>3 \<inter> \<alpha>4 = {}) \<and>
    (\<forall>\<alpha>5\<in>{\<alpha>. \<alpha> \<inter> x = {} \<and> \<alpha> \<in> \<sigma>} \<union> {uu. \<exists>\<alpha>1. \<alpha>1 \<in> \<sigma> \<and> \<alpha>1 \<inter> x \<noteq> {} \<and> uu = \<alpha>1 \<inter> x} \<union>
          {uu. \<exists>\<alpha>1. \<alpha>1 \<in> \<sigma> \<and> \<alpha>1 \<inter> x \<noteq> {} \<and> \<not> \<alpha>1 \<subseteq> x \<and> uu = \<alpha>1 - \<alpha>1 \<inter> x}.
        \<exists>s\<subseteq>lbs - (it - {x}).
           \<alpha>5 \<subseteq> \<Inter> s \<and>
           \<alpha>5 \<subseteq> \<alpha> \<and>
           (\<forall>\<alpha>6\<in>lbs - (it - {x}) - insert \<alpha> s. \<alpha>5 \<inter> \<alpha>6 = {}) \<and>
           (\<forall>\<alpha>7. \<alpha>7 \<subseteq> \<Inter> s \<and>
                  \<alpha>7 \<subseteq> \<alpha> \<and> (\<forall>\<alpha>8\<in>lbs - (it - {x}) - insert \<alpha> s. \<alpha>7 \<inter> \<alpha>8 = {}) \<longrightarrow>
                  \<alpha>7 \<subseteq> \<alpha>5))"
          apply (rule conjI)
          using \<sigma>_def 
           apply auto[1]
          apply (rule conjI)
          using \<sigma>_def apply force
          apply (rule conjI)
          using \<sigma>_def apply force
          apply (rule_tac conjI)
          apply (rule allI impI)+
          using \<sigma>_def
          apply auto[1]
        proof
          {
            show " \<forall>\<alpha>3 \<alpha>4.
              (\<alpha>3 \<inter> x = {} \<and> \<alpha>3 \<in> \<sigma> \<or>
              (\<exists>\<alpha>1. \<alpha>1 \<in> \<sigma> \<and> \<alpha>1 \<inter> x \<noteq> {} \<and> \<alpha>3 = \<alpha>1 \<inter> x) \<or>
              (\<exists>\<alpha>1. \<alpha>1 \<in> \<sigma> \<and> \<alpha>1 \<inter> x \<noteq> {} \<and> \<not> \<alpha>1 \<subseteq> x \<and> \<alpha>3 = \<alpha>1 - \<alpha>1 \<inter> x)) \<and>
                \<alpha>4 \<in> lbs \<and> (\<alpha>4 \<in> it \<longrightarrow> \<alpha>4 = x) \<longrightarrow>
                \<alpha>3 \<subseteq> \<alpha>4 \<or> \<alpha>3 \<inter> \<alpha>4 = {}"
              apply (rule allI impI)+
            proof -
              fix \<alpha>3 \<alpha>4
              assume cons: "(\<alpha>3 \<inter> x = {} \<and> \<alpha>3 \<in> \<sigma> \<or>
                             (\<exists>\<alpha>1. \<alpha>1 \<in> \<sigma> \<and> \<alpha>1 \<inter> x \<noteq> {} \<and> \<alpha>3 = \<alpha>1 \<inter> x) \<or>
                             (\<exists>\<alpha>1. \<alpha>1 \<in> \<sigma> \<and> \<alpha>1 \<inter> x \<noteq> {} \<and> 
                              \<not> \<alpha>1 \<subseteq> x \<and> \<alpha>3 = \<alpha>1 - \<alpha>1 \<inter> x)) \<and>
                              \<alpha>4 \<in> lbs \<and> (\<alpha>4 \<in> it \<longrightarrow> \<alpha>4 = x)"

              have case1: "(\<alpha>3 \<inter> x = {} \<and> \<alpha>3 \<in> \<sigma>) \<and> 
                           \<alpha>4 \<in> lbs \<and> (\<alpha>4 \<in> it \<longrightarrow> \<alpha>4 = x) \<Longrightarrow>
                           \<alpha>3 \<subseteq> \<alpha>4 \<or> \<alpha>3 \<inter> \<alpha>4 = {}"
                using \<sigma>_def
                by (meson DiffI)
              have case2: "(\<exists>\<alpha>1. \<alpha>1 \<in> \<sigma> \<and> \<alpha>1 \<inter> x \<noteq> {} \<and> 
                              \<not> \<alpha>1 \<subseteq> x \<and> \<alpha>3 = \<alpha>1 - \<alpha>1 \<inter> x) \<and> 
                           \<alpha>4 \<in> lbs \<and> (\<alpha>4 \<in> it \<longrightarrow> \<alpha>4 = x) \<Longrightarrow>
                           \<alpha>3 \<subseteq> \<alpha>4 \<or> \<alpha>3 \<inter> \<alpha>4 = {}"
                using \<sigma>_def
                by blast

              have case3: "(\<exists>\<alpha>1. \<alpha>1 \<in> \<sigma> \<and> \<alpha>1 \<inter> x \<noteq> {} \<and> \<alpha>3 = \<alpha>1 \<inter> x)\<and> 
                           \<alpha>4 \<in> lbs \<and> (\<alpha>4 \<in> it \<longrightarrow> \<alpha>4 = x) \<Longrightarrow>
                           \<alpha>3 \<subseteq> \<alpha>4 \<or> \<alpha>3 \<inter> \<alpha>4 = {}"
                using \<sigma>_def
                by blast
              from cons case1 case2 case3
              show "\<alpha>3 \<subseteq> \<alpha>4 \<or> \<alpha>3 \<inter> \<alpha>4 = {}"
                by blast
            qed
          }
          {
            show "\<forall>\<alpha>5\<in>{\<alpha>. \<alpha> \<inter> x = {} \<and> \<alpha> \<in> \<sigma>} \<union> {uu. \<exists>\<alpha>1. \<alpha>1 \<in> \<sigma> \<and> \<alpha>1 \<inter> x \<noteq> {} \<and> uu = \<alpha>1 \<inter> x} \<union>
         {uu. \<exists>\<alpha>1. \<alpha>1 \<in> \<sigma> \<and> \<alpha>1 \<inter> x \<noteq> {} \<and> \<not> \<alpha>1 \<subseteq> x \<and> uu = \<alpha>1 - \<alpha>1 \<inter> x}.
       \<exists>s\<subseteq>lbs - (it - {x}).
          \<alpha>5 \<subseteq> \<Inter> s \<and>
          \<alpha>5 \<subseteq> \<alpha> \<and>
          (\<forall>\<alpha>6\<in>lbs - (it - {x}) - insert \<alpha> s. \<alpha>5 \<inter> \<alpha>6 = {}) \<and>
          (\<forall>\<alpha>7. \<alpha>7 \<subseteq> \<Inter> s \<and>
                 \<alpha>7 \<subseteq> \<alpha> \<and> (\<forall>\<alpha>8\<in>lbs - (it - {x}) - insert \<alpha> s. \<alpha>7 \<inter> \<alpha>8 = {}) \<longrightarrow>
                 \<alpha>7 \<subseteq> \<alpha>5)"
              
            proof 
              fix \<alpha>5
              assume a5_in: "\<alpha>5 \<in> {\<alpha>. \<alpha> \<inter> x = {} \<and> \<alpha> \<in> \<sigma>} \<union>
               {uu. \<exists>\<alpha>1. \<alpha>1 \<in> \<sigma> \<and> \<alpha>1 \<inter> x \<noteq> {} \<and> uu = \<alpha>1 \<inter> x} \<union>
               {uu. \<exists>\<alpha>1. \<alpha>1 \<in> \<sigma> \<and> \<alpha>1 \<inter> x \<noteq> {} \<and> \<not> \<alpha>1 \<subseteq> x \<and> uu = \<alpha>1 - \<alpha>1 \<inter> x}"
              let ?res = "\<exists>s\<subseteq>lbs - (it - {x}).
             \<alpha>5 \<subseteq> \<Inter> s \<and>
             \<alpha>5 \<subseteq> \<alpha> \<and>
             (\<forall>\<alpha>6\<in>lbs - (it - {x}) - (s \<union> {\<alpha>}). \<alpha>5 \<inter> \<alpha>6 = {}) \<and>
             (\<forall>\<alpha>7. \<alpha>7 \<subseteq> \<Inter> s \<and>
                    \<alpha>7 \<subseteq> \<alpha> \<and> (\<forall>\<alpha>8\<in>lbs - (it - {x}) - (s \<union> {\<alpha>}). \<alpha>7 \<inter> \<alpha>8 = {}) \<longrightarrow>
                    \<alpha>7 \<subseteq> \<alpha>5)"
          
              have case1: "\<alpha>5 \<in> {\<alpha>. \<alpha> \<inter> x = {} \<and> \<alpha> \<in> \<sigma>} \<Longrightarrow> ?res"
              proof -
                assume \<alpha>5_in': "\<alpha>5 \<in> {\<alpha>. \<alpha> \<inter> x = {} \<and> \<alpha> \<in> \<sigma>}"
                from this
                have \<alpha>5_cons: "\<alpha>5 \<inter> x = {} \<and> \<alpha>5 \<in> \<sigma>"
                  by blast
                from \<sigma>_def this
                obtain s where
                s_def: "s \<subseteq> lbs - it \<and>
                       (\<alpha>5 \<subseteq> \<Inter> s \<inter> \<alpha> \<and> (\<forall>\<alpha>6\<in>lbs - it - (s \<union> {\<alpha>}). \<alpha>5 \<inter> \<alpha>6 = {})) \<and>
                       (\<forall>\<alpha>7. \<alpha>7 \<subseteq> \<Inter> s \<inter> \<alpha> \<and> 
                       (\<forall>\<alpha>8\<in>lbs - it - (s \<union> {\<alpha>}). \<alpha>7 \<inter> \<alpha>8 = {}) \<longrightarrow> \<alpha>7 \<subseteq> \<alpha>5)"
                  by force

                 
                 
                from s_def \<alpha>5_cons x_in_it it_sub_lbs
                have "s \<subseteq> lbs - (it - {x}) \<and>
                        \<alpha>5 \<subseteq> \<Inter> s \<and> \<alpha>5 \<subseteq> \<alpha> \<and>
                        (\<forall>\<alpha>6\<in>lbs - (it - {x}) - (s \<union> {\<alpha>}). \<alpha>5 \<inter> \<alpha>6 = {}) \<and>
                        (\<forall>\<alpha>7. \<alpha>7 \<subseteq> \<Inter> s \<and> \<alpha>7 \<subseteq> \<alpha> \<and> 
                        (\<forall>\<alpha>8\<in>lbs - (it - {x}) - (s \<union> {\<alpha>}). \<alpha>7 \<inter> \<alpha>8 = {}) \<longrightarrow>
                        \<alpha>7 \<subseteq> \<alpha>5)"
                  apply (rule_tac conjI)
                  apply blast
                  apply (rule_tac conjI)
                  apply blast
                  apply (rule_tac conjI)
                  apply blast
                  apply (rule_tac conjI)
                   apply blast
                  by auto
                  
                from this show ?res
                  by auto
              qed
              have case2: "\<alpha>5 \<in> {uu. \<exists>\<alpha>1. \<alpha>1 \<in> \<sigma> \<and> \<alpha>1 \<inter> x \<noteq> {} \<and> uu = \<alpha>1 \<inter> x} \<Longrightarrow>
                          ?res"
              proof -
                assume \<alpha>5_in: "\<alpha>5 \<in> {uu. \<exists>\<alpha>1. \<alpha>1 \<in> \<sigma> \<and> \<alpha>1 \<inter> x \<noteq> {} \<and> uu = \<alpha>1 \<inter> x}"
                from this
                have \<alpha>5_cons: "\<exists> \<alpha>1. \<alpha>1 \<in> \<sigma> \<and> \<alpha>1 \<inter> x \<noteq> {} \<and> \<alpha>5 = \<alpha>1 \<inter> x"
                  by auto
                from this obtain \<alpha>1 where
                \<alpha>1_def: "\<alpha>1 \<in> \<sigma> \<and> \<alpha>1 \<inter> x \<noteq> {} \<and> \<alpha>5 = \<alpha>1 \<inter> x"
                  by auto
                from \<sigma>_def this
                obtain s where
                s_def :"s \<subseteq> lbs - it \<and>
                       (\<alpha>1 \<subseteq> \<Inter> s \<inter> \<alpha> \<and> (\<forall>\<alpha>6\<in>lbs - it - (s \<union> {\<alpha>}). \<alpha>1 \<inter> \<alpha>6 = {})) \<and>
                       (\<forall>\<alpha>7. \<alpha>7 \<subseteq> \<Inter> s \<inter> \<alpha> \<and> 
                       (\<forall>\<alpha>8\<in>lbs - it - (s \<union> {\<alpha>}). \<alpha>7 \<inter> \<alpha>8 = {}) \<longrightarrow> \<alpha>7 \<subseteq> \<alpha>1)"
                  by meson
                
                have inst: "\<alpha>5 \<subseteq> \<Inter> (s \<union> {x}) \<and>
                      \<alpha>5 \<subseteq> \<alpha> \<and>
                     (\<forall>\<alpha>6 \<in> lbs - (it - {x}) - (s \<union> {x} \<union> {\<alpha>}). \<alpha>5 \<inter> \<alpha>6 = {}) \<and>
                     (\<forall>\<alpha>7. \<alpha>7 \<subseteq> \<Inter> (s \<union> {x}) \<and> \<alpha>7 \<subseteq> \<alpha> \<and> 
                     (\<forall>\<alpha>8\<in>lbs - (it - {x}) - (s \<union> {x} \<union> {\<alpha>}). \<alpha>7 \<inter> \<alpha>8 = {}) \<longrightarrow> \<alpha>7 \<subseteq> \<alpha>5)"
                  apply (rule_tac conjI)
                  using s_def \<alpha>1_def
                  apply blast
                  apply (rule_tac conjI)
                  using s_def \<alpha>1_def
                  apply blast
                  apply (rule_tac conjI)
                  using s_def \<alpha>1_def
                  apply blast
                  thm s_def \<alpha>1_def
                  apply (rule allI impI)+
                proof -
                  fix \<alpha>7
                  assume \<alpha>7_cons: "\<alpha>7 \<subseteq> \<Inter> (s \<union> {x}) \<and>
                                  \<alpha>7 \<subseteq> \<alpha> \<and> 
                      (\<forall>\<alpha>8\<in>lbs - (it - {x}) - (s \<union> {x} \<union> {\<alpha>}). \<alpha>7 \<inter> \<alpha>8 = {})"
                  from s_def
                  have a7_cons': "\<alpha>7 \<subseteq> \<Inter> s \<inter> \<alpha> \<and> 
                          (\<forall>\<alpha>8\<in>lbs - it - (s \<union> {\<alpha>}). \<alpha>7 \<inter> \<alpha>8 = {}) \<longrightarrow> \<alpha>7 \<subseteq> \<alpha>1"
                    by auto
                  from x_in_it it_sub_lbs
                  have "lbs - (it - {x}) - (s \<union> {x} \<union> {\<alpha>}) = lbs - it - (s \<union> {\<alpha>})"
                    by auto
                  from this \<alpha>7_cons a7_cons' \<alpha>1_def
                  show "\<alpha>7 \<subseteq> \<alpha>5"
                    by auto
                qed

                from s_def x_in_it it_sub_lbs
                have "(s \<union> {x}) \<subseteq> lbs - (it - {x})"
                  by auto
                from this inst
                show "?res"
                  by meson
              qed
              have case3: "\<alpha>5 \<in> {uu. \<exists>\<alpha>1. \<alpha>1 \<in> \<sigma> \<and> \<alpha>1 \<inter> x \<noteq> {} \<and> 
                           \<not> \<alpha>1 \<subseteq> x \<and> uu = \<alpha>1 - \<alpha>1 \<inter> x} \<Longrightarrow> ?res"
              proof -
                assume \<alpha>5_cons: "\<alpha>5 \<in> {uu. \<exists>\<alpha>1. \<alpha>1 \<in> \<sigma> \<and> \<alpha>1 \<inter> x \<noteq> {} \<and> 
                                         \<not> \<alpha>1 \<subseteq> x \<and> uu = \<alpha>1 - \<alpha>1 \<inter> x}"
                from this 
                obtain \<alpha>1 where
                \<alpha>1_def: "\<alpha>1 \<in> \<sigma> \<and> \<alpha>1 \<inter> x \<noteq> {} \<and> \<not> \<alpha>1 \<subseteq> x \<and> \<alpha>5 = \<alpha>1 - \<alpha>1 \<inter> x"
                  by force
                from \<sigma>_def this
                obtain s where
                s_def: "s \<subseteq> lbs - it \<and>
                       (\<alpha>1 \<subseteq> \<Inter> s \<inter> \<alpha> \<and> 
                       (\<forall>\<alpha>6 \<in> lbs - it - (s \<union> {\<alpha>}). \<alpha>1 \<inter> \<alpha>6 = {})) \<and>
                       (\<forall>\<alpha>7. \<alpha>7 \<subseteq> \<Inter> s \<inter> \<alpha> \<and> 
                       (\<forall>\<alpha>8 \<in> lbs - it - (s \<union> {\<alpha>}). \<alpha>7 \<inter> \<alpha>8 = {}) \<longrightarrow> \<alpha>7 \<subseteq> \<alpha>1)"
                  by meson
                from \<alpha>1_def
                have \<alpha>5x_empty: "\<alpha>5 \<inter> x = {}"
                  by auto
              have inst: "\<alpha>5 \<subseteq> \<Inter> s \<and>
                      \<alpha>5 \<subseteq> \<alpha> \<and>
                     (\<forall>\<alpha>6 \<in> lbs - (it - {x}) - (s \<union> {\<alpha>}). \<alpha>5 \<inter> \<alpha>6 = {}) \<and>
                     (\<forall>\<alpha>7. \<alpha>7 \<subseteq> \<Inter> s \<and> \<alpha>7 \<subseteq> \<alpha> \<and> 
                     (\<forall>\<alpha>8\<in>lbs - (it - {x}) - (s \<union> {\<alpha>}). \<alpha>7 \<inter> \<alpha>8 = {}) \<longrightarrow> \<alpha>7 \<subseteq> \<alpha>5)"
                apply (rule conjI)
                using s_def \<alpha>1_def
                 apply blast
                apply (rule conjI)
                using s_def \<alpha>1_def
                 apply blast
                apply (rule conjI)
                using s_def \<alpha>1_def
                apply blast
                thm s_def \<alpha>5x_empty
                apply (rule allI impI)+
              proof -
                fix \<alpha>7
                assume \<alpha>7_cons: "\<alpha>7 \<subseteq> \<Inter> s \<and> \<alpha>7 \<subseteq> \<alpha> \<and> 
                        (\<forall>\<alpha>8\<in>lbs - (it - {x}) - (s \<union> {\<alpha>}). \<alpha>7 \<inter> \<alpha>8 = {})"
                from s_def this
                have s_def_sub': 
                     "(\<forall>\<alpha>8 \<in> lbs - it - (s \<union> {\<alpha>}). \<alpha>7 \<inter> \<alpha>8 = {}) \<longrightarrow> \<alpha>7 \<subseteq> \<alpha>1"
                  by auto

                from this \<alpha>7_cons x_in_it it_sub_lbs
                have \<alpha>7_sub_\<alpha>1: "\<alpha>7 \<subseteq> \<alpha>1"
                  by auto

                have x_notin_s: "x \<notin> s"
                  using \<alpha>1_def s_def by blast
                
                
                thm this \<alpha>1_def x_in_it it_sub_lbs
                show "\<alpha>7 \<subseteq> \<alpha>5"
                proof (cases "x = \<alpha>")
                  case True
                  from True \<alpha>1_def \<sigma>_def
                  show ?thesis by force 
                next
                  case False
                  from False  x_notin_s  x_in_it it_sub_lbs
                  have "x \<in> lbs - (it - {x}) - (s \<union> {\<alpha>})"
                    by force
                  from this \<alpha>7_cons
                  have "\<alpha>7 \<inter> x = {}" 
                    by auto
                  from this \<alpha>1_def \<alpha>7_sub_\<alpha>1
                  show ?thesis by auto
                qed
              qed
              from s_def
              have "s \<subseteq> lbs - (it - {x})"        
                by blast
              from this inst
              show "\<exists> s \<subseteq> lbs - (it - {x}).
                       \<alpha>5 \<subseteq> \<Inter> s \<and>
                       \<alpha>5 \<subseteq> \<alpha> \<and>
                       (\<forall>\<alpha>6\<in>lbs - (it - {x}) - (s \<union> {\<alpha>}). \<alpha>5 \<inter> \<alpha>6 = {}) \<and>
                       (\<forall>\<alpha>7. \<alpha>7 \<subseteq> \<Inter> s \<and> \<alpha>7 \<subseteq> \<alpha> \<and> (\<forall>\<alpha>8\<in>lbs - (it - {x}) - (s \<union> {\<alpha>}). \<alpha>7 \<inter> \<alpha>8 = {}) \<longrightarrow>
                              \<alpha>7 \<subseteq> \<alpha>5)"
                by auto
            qed
            from case1 case2 case3 a5_in
            show "\<exists>s\<subseteq>lbs - (it - {x}).
             \<alpha>5 \<subseteq> \<Inter> s \<and>
             \<alpha>5 \<subseteq> \<alpha> \<and>
             (\<forall>\<alpha>6\<in>lbs - (it - {x}) - insert \<alpha> s. \<alpha>5 \<inter> \<alpha>6 = {}) \<and>
             (\<forall>\<alpha>7. \<alpha>7 \<subseteq> \<Inter> s \<and>
                    \<alpha>7 \<subseteq> \<alpha> \<and> (\<forall>\<alpha>8\<in>lbs - (it - {x}) - insert \<alpha> s. \<alpha>7 \<inter> \<alpha>8 = {}) \<longrightarrow>
                    \<alpha>7 \<subseteq> \<alpha>5)"
              by force
          qed 
        }
      qed
    }
    qed
    from this split_sing_correct[OF finite_\<sigma>, of x]
    show "split_sing x \<sigma>
       \<le> SPEC (\<lambda>s_lbs'.
                (\<Union> s_lbs' = \<alpha> \<and> finite s_lbs') \<and>
                (\<forall>\<alpha>1 \<alpha>2. \<alpha>1 \<in> s_lbs' \<and> \<alpha>2 \<in> s_lbs' \<longrightarrow> \<alpha>1 = \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {}) \<and>
                (\<forall>\<alpha>3 \<alpha>4.
                    \<alpha>3 \<in> s_lbs' \<and> \<alpha>4 \<in> lbs - (it - {x}) \<longrightarrow> \<alpha>3 \<subseteq> \<alpha>4 \<or> \<alpha>3 \<inter> \<alpha>4 = {}) \<and>
                (\<forall>\<alpha>5\<in>s_lbs'.
                    \<exists>s\<subseteq>lbs - (it - {x}).
                       (\<alpha>5 \<subseteq> \<Inter> s \<inter> \<alpha> \<and>
                        (\<forall>\<alpha>6\<in>lbs - (it - {x}) - (s \<union> {\<alpha>}). \<alpha>5 \<inter> \<alpha>6 = {})) \<and>
                       (\<forall>\<alpha>7. \<alpha>7 \<subseteq> \<Inter> s \<inter> \<alpha> \<and>
                              (\<forall>\<alpha>8\<in>lbs - (it - {x}) - (s \<union> {\<alpha>}). \<alpha>7 \<inter> \<alpha>8 = {}) \<longrightarrow>
                              \<alpha>7 \<subseteq> \<alpha>5)))"
      using SPEC_trans
      by blast
  }
  {
    fix \<sigma>
    assume left: "(\<Union> \<sigma> = \<alpha> \<and> finite \<sigma>) \<and>
         (\<forall>\<alpha>1 \<alpha>2. \<alpha>1 \<in> \<sigma> \<and> \<alpha>2 \<in> \<sigma> \<longrightarrow> \<alpha>1 = \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {}) \<and>
         (\<forall>\<alpha>3 \<alpha>4. \<alpha>3 \<in> \<sigma> \<and> \<alpha>4 \<in> lbs - {} \<longrightarrow> \<alpha>3 \<subseteq> \<alpha>4 \<or> \<alpha>3 \<inter> \<alpha>4 = {}) \<and>
         (\<forall>\<alpha>5\<in>\<sigma>.
             \<exists>s\<subseteq>lbs - {}.
                (\<alpha>5 \<subseteq> \<Inter> s \<inter> \<alpha> \<and> (\<forall>\<alpha>6\<in>lbs - {} - (s \<union> {\<alpha>}). \<alpha>5 \<inter> \<alpha>6 = {})) \<and>
                (\<forall>\<alpha>7. \<alpha>7 \<subseteq> \<Inter> s \<inter> \<alpha> \<and> (\<forall>\<alpha>8\<in>lbs - {} - (s \<union> {\<alpha>}). \<alpha>7 \<inter> \<alpha>8 = {}) \<longrightarrow>
                       \<alpha>7 \<subseteq> \<alpha>5))"
    show "(\<forall>(q1, \<alpha>1', q1')\<in>{}. q = q1 \<and> q' = q1') \<and>
         \<Union> {\<alpha>1. (q, \<alpha>1, q') \<in> {}} = \<Union> (\<sigma> - \<sigma>) \<and>
         {\<alpha>1. (q, \<alpha>1, q') \<in> {}} = \<sigma> - \<sigma> \<and>
         (\<forall>(q, \<alpha>1, q')\<in>{}.
             \<exists>s\<subseteq>lbs.
                (\<alpha>1 \<subseteq> \<Inter> s \<and> (\<forall>\<alpha>2\<in>lbs - s. \<alpha>1 \<inter> \<alpha>2 = {})) \<and>
                (\<forall>\<alpha>3. \<alpha>3 \<subseteq> \<Inter> s \<and> (\<forall>\<alpha>4\<in>lbs - s. \<alpha>3 \<inter> \<alpha>4 = {}) \<longrightarrow> \<alpha>3 \<subseteq> \<alpha>1)) \<and>
         (\<forall>\<alpha>1 \<alpha>2. {\<alpha>1, \<alpha>2} \<subseteq> {\<alpha>1. (q, \<alpha>1, q') \<in> {}} \<longrightarrow> \<alpha>1 = \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {}) \<and>
         (\<forall>\<alpha>1 \<alpha>2. \<alpha>1 \<in> {\<alpha>1. (q, \<alpha>1, q') \<in> {}} \<and> \<alpha>2 \<in> lbs \<longrightarrow> \<alpha>1 \<subseteq> \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {})"
      apply (rule conjI)
       apply simp
      apply (rule conjI)
       apply simp
      apply (rule conjI)
       apply simp
      by simp
  }
  {
    fix \<sigma> x it \<sigma>'
    assume pre1: "(\<Union> \<sigma> = \<alpha> \<and> finite \<sigma>) \<and>
       (\<forall>\<alpha>1 \<alpha>2. \<alpha>1 \<in> \<sigma> \<and> \<alpha>2 \<in> \<sigma> \<longrightarrow> \<alpha>1 = \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {}) \<and>
       (\<forall>\<alpha>3 \<alpha>4. \<alpha>3 \<in> \<sigma> \<and> \<alpha>4 \<in> lbs - {} \<longrightarrow> \<alpha>3 \<subseteq> \<alpha>4 \<or> \<alpha>3 \<inter> \<alpha>4 = {}) \<and>
       (\<forall>\<alpha>5\<in>\<sigma>.
           \<exists>s\<subseteq>lbs - {}.
              (\<alpha>5 \<subseteq> \<Inter> s \<inter> \<alpha> \<and> (\<forall>\<alpha>6\<in>lbs - {} - (s \<union> {\<alpha>}). \<alpha>5 \<inter> \<alpha>6 = {})) \<and>
              (\<forall>\<alpha>7. \<alpha>7 \<subseteq> \<Inter> s \<inter> \<alpha> \<and> (\<forall>\<alpha>8\<in>lbs - {} - (s \<union> {\<alpha>}). \<alpha>7 \<inter> \<alpha>8 = {}) \<longrightarrow>
                     \<alpha>7 \<subseteq> \<alpha>5))"
       and x_in_it: "x \<in> it"
       and it_sub_\<sigma>: "it \<subseteq> \<sigma>"
       and pre2: "(\<forall>(q1, \<alpha>1', q1')\<in>\<sigma>'. q = q1 \<and> q' = q1') \<and>
       \<Union> {\<alpha>1. (q, \<alpha>1, q') \<in> \<sigma>'} = \<Union> (\<sigma> - it) \<and>
       {\<alpha>1. (q, \<alpha>1, q') \<in> \<sigma>'} = \<sigma> - it \<and>
       (\<forall>(q, \<alpha>1, q')\<in>\<sigma>'.
           \<exists>s\<subseteq>lbs.
              (\<alpha>1 \<subseteq> \<Inter> s \<and> (\<forall>\<alpha>2\<in>lbs - s. \<alpha>1 \<inter> \<alpha>2 = {})) \<and>
              (\<forall>\<alpha>3. \<alpha>3 \<subseteq> \<Inter> s \<and> (\<forall>\<alpha>4\<in>lbs - s. \<alpha>3 \<inter> \<alpha>4 = {}) \<longrightarrow> \<alpha>3 \<subseteq> \<alpha>1)) \<and>
       (\<forall>\<alpha>1 \<alpha>2. {\<alpha>1, \<alpha>2} \<subseteq> {\<alpha>1. (q, \<alpha>1, q') \<in> \<sigma>'} \<longrightarrow> \<alpha>1 = \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {}) \<and>
       (\<forall>\<alpha>1 \<alpha>2. \<alpha>1 \<in> {\<alpha>1. (q, \<alpha>1, q') \<in> \<sigma>'} \<and> \<alpha>2 \<in> lbs \<longrightarrow> \<alpha>1 \<subseteq> \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {})"
    show "(\<forall>(q1, \<alpha>1', q1')\<in>\<sigma>' \<union> {(q, x, q')}. q = q1 \<and> q' = q1') \<and>
       \<Union> {\<alpha>1. (q, \<alpha>1, q') \<in> \<sigma>' \<union> {(q, x, q')}} = \<Union> (\<sigma> - (it - {x})) \<and>
       {\<alpha>1. (q, \<alpha>1, q') \<in> \<sigma>' \<union> {(q, x, q')}} = \<sigma> - (it - {x}) \<and>
       (\<forall>(q, \<alpha>1, q')\<in>\<sigma>' \<union> {(q, x, q')}.
           \<exists>s\<subseteq>lbs.
              (\<alpha>1 \<subseteq> \<Inter> s \<and> (\<forall>\<alpha>2\<in>lbs - s. \<alpha>1 \<inter> \<alpha>2 = {})) \<and>
              (\<forall>\<alpha>3. \<alpha>3 \<subseteq> \<Inter> s \<and> (\<forall>\<alpha>4\<in>lbs - s. \<alpha>3 \<inter> \<alpha>4 = {}) \<longrightarrow> \<alpha>3 \<subseteq> \<alpha>1)) \<and>
       (\<forall>\<alpha>1 \<alpha>2.
           {\<alpha>1, \<alpha>2} \<subseteq> {\<alpha>1. (q, \<alpha>1, q') \<in> \<sigma>' \<union> {(q, x, q')}} \<longrightarrow>
           \<alpha>1 = \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {}) \<and>
       (\<forall>\<alpha>1 \<alpha>2.
           \<alpha>1 \<in> {\<alpha>1. (q, \<alpha>1, q') \<in> \<sigma>' \<union> {(q, x, q')}} \<and> \<alpha>2 \<in> lbs \<longrightarrow>
           \<alpha>1 \<subseteq> \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {})"
      apply (rule conjI)
      using pre2 apply simp
      apply (rule conjI)
    proof -
      {
        show "\<Union> {\<alpha>1. (q, \<alpha>1, q') \<in> \<sigma>' \<union> {(q, x, q')}} = \<Union> (\<sigma> - (it - {x}))"
        proof
          {
            show "\<Union> {\<alpha>1. (q, \<alpha>1, q') \<in> \<sigma>' \<union> {(q, x, q')}} \<subseteq> \<Union> (\<sigma> - (it - {x}))"
            proof
              fix xa
              assume xa_in: "xa \<in> \<Union> {\<alpha>1. (q, \<alpha>1, q') \<in> \<sigma>' \<union> {(q, x, q')}}"
              from pre2
              have pre2': "\<Union> {\<alpha>1. (q, \<alpha>1, q') \<in> \<sigma>'} = \<Union> (\<sigma> - it)"
                by simp
              from pre2' xa_in
              show "xa \<in> \<Union> (\<sigma> - (it - {x}))"
              proof (cases "xa \<in> x")
              case True
              from it_sub_\<sigma> x_in_it True
              show ?thesis 
                by blast
              next
                case False
                from this xa_in pre2'
                have "xa \<in> \<Union> (\<sigma> - it)"
                  by auto
                from this it_sub_\<sigma> x_in_it 
                show ?thesis 
                  by auto
              qed
             qed
           }
           {
             show "\<Union> (\<sigma> - (it - {x})) \<subseteq> \<Union> {\<alpha>1. (q, \<alpha>1, q') \<in> \<sigma>' \<union> {(q, x, q')}}"
             proof
               fix xa
               assume xa_in: "xa \<in> \<Union> (\<sigma> - (it - {x}))"
               from pre2
              have pre2': "\<Union> {\<alpha>1. (q, \<alpha>1, q') \<in> \<sigma>'} = \<Union> (\<sigma> - it)"
                by simp
               show "xa \<in> \<Union> {\<alpha>1. (q, \<alpha>1, q') \<in> \<sigma>' \<union> {(q, x, q')}}"
               proof (cases "xa \<in> x")
                 case True
                 then show ?thesis by auto
                next
                  case False
                  from this pre2' xa_in it_sub_\<sigma> x_in_it
                  have "xa \<in> \<Union> {\<alpha>1. (q, \<alpha>1, q') \<in> \<sigma>'}" 
                    by auto
                  from this
                 show ?thesis by auto
               qed
             qed
           }
         qed
       }
       {
     show "{\<alpha>1. (q, \<alpha>1, q') \<in> \<sigma>' \<union> {(q, x, q')}} = \<sigma> - (it - {x}) \<and>
          (\<forall>(q, \<alpha>1, q')\<in>\<sigma>' \<union> {(q, x, q')}.
           \<exists>s\<subseteq>lbs.
             (\<alpha>1 \<subseteq> \<Inter> s \<and> (\<forall>\<alpha>2\<in>lbs - s. \<alpha>1 \<inter> \<alpha>2 = {})) \<and>
             (\<forall>\<alpha>3. \<alpha>3 \<subseteq> \<Inter> s \<and> (\<forall>\<alpha>4\<in>lbs - s. \<alpha>3 \<inter> \<alpha>4 = {}) \<longrightarrow> \<alpha>3 \<subseteq> \<alpha>1)) \<and>
          (\<forall>\<alpha>1 \<alpha>2.
              {\<alpha>1, \<alpha>2} \<subseteq> {\<alpha>1. (q, \<alpha>1, q') \<in> \<sigma>' \<union> {(q, x, q')}} \<longrightarrow> \<alpha>1 = \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {}) \<and>
          (\<forall>\<alpha>1 \<alpha>2.
        \<alpha>1 \<in> {\<alpha>1. (q, \<alpha>1, q') \<in> \<sigma>' \<union> {(q, x, q')}} \<and> \<alpha>2 \<in> lbs \<longrightarrow>
        \<alpha>1 \<subseteq> \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {})"
       apply (rule_tac conjI allI impI)+
       using pre2 x_in_it it_sub_\<sigma>
       apply auto[1]
       apply (rule_tac conjI allI impI)+
        defer
        apply (rule_tac conjI allI impI)+
       defer
       apply (rule_tac allI impI)+
       proof - {
             fix \<alpha>1 \<alpha>2
             assume \<alpha>1_cons: 
                      "\<alpha>1 \<in> {\<alpha>1. (q, \<alpha>1, q') \<in> \<sigma>' \<union> {(q, x, q')}} \<and> \<alpha>2 \<in> lbs"
             from this pre1 pre2
             have "\<Union> {\<alpha>1. (q, \<alpha>1, q') \<in> \<sigma>'} = \<Union> (\<sigma> - it)"
               by auto
             from this it_sub_\<sigma> x_in_it
             have "\<Union> {\<alpha>1. (q, \<alpha>1, q') \<in> \<sigma>'} \<subseteq> \<Union> \<sigma>"
               by auto
             from this pre1
             have "(\<forall>\<alpha>1 \<alpha>2. \<alpha>1 \<in> \<sigma> \<and> \<alpha>2 \<in> \<sigma> \<longrightarrow> \<alpha>1 = \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {})"
               by auto
             from pre1 pre2 it_sub_\<sigma> x_in_it
             have "{\<alpha>1. (q, \<alpha>1, q') \<in> \<sigma>'} \<union> {x} \<subseteq> \<sigma>"
               by auto
             from this pre1 \<alpha>1_cons
             show "\<alpha>1 \<subseteq> \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {}"
               by blast
           }
           {
             fix \<alpha>1 \<alpha>2
             assume \<alpha>1\<alpha>2: "{\<alpha>1, \<alpha>2} \<subseteq> {\<alpha>1. (q, \<alpha>1, q') \<in> \<sigma>' \<union> {(q, x, q')}}"
             from pre1 pre2 it_sub_\<sigma> x_in_it
             have "{\<alpha>1. (q, \<alpha>1, q') \<in> \<sigma>'} \<union> {x} \<subseteq> \<sigma>"
               by auto
             from this  \<alpha>1\<alpha>2
             have "\<alpha>1 \<in> \<sigma> \<and> \<alpha>2 \<in> \<sigma>"
               by auto
             from this pre1
             show "\<alpha>1 = \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {}" 
               by auto
           }
           {
             show "\<forall>(q, \<alpha>1, q')\<in>\<sigma>' \<union> {(q, x, q')}.
                   \<exists>s\<subseteq>lbs.
                       (\<alpha>1 \<subseteq> \<Inter> s \<and> (\<forall>\<alpha>2\<in>lbs - s. \<alpha>1 \<inter> \<alpha>2 = {})) \<and>
                       (\<forall>\<alpha>3. \<alpha>3 \<subseteq> \<Inter> s \<and> (\<forall>\<alpha>4\<in>lbs - s. \<alpha>3 \<inter> \<alpha>4 = {}) \<longrightarrow> \<alpha>3 \<subseteq> \<alpha>1)"
             proof 
               fix xa
               assume xa_cons: "xa \<in> \<sigma>' \<union> {(q, x, q')}"

               from pre2 
               have case1: "xa \<in> \<sigma>' \<Longrightarrow> case xa of (q, \<alpha>1, q') \<Rightarrow>
                      \<exists>s\<subseteq>lbs.
                      (\<alpha>1 \<subseteq> \<Inter> s \<and> (\<forall>\<alpha>2\<in>lbs - s. \<alpha>1 \<inter> \<alpha>2 = {})) \<and>
                      (\<forall>\<alpha>3. \<alpha>3 \<subseteq> \<Inter> s \<and> (\<forall>\<alpha>4\<in>lbs - s. \<alpha>3 \<inter> \<alpha>4 = {}) \<longrightarrow> \<alpha>3 \<subseteq> \<alpha>1)"
                 by simp

               from it_sub_\<sigma> x_in_it
               have x_in_\<sigma>: "x \<in> \<sigma>" by auto
               from pre1 this
               obtain s where
               s_def: "s \<subseteq> lbs - {} \<and>
           (x \<subseteq> \<Inter> s \<inter> \<alpha> \<and> (\<forall>\<alpha>6\<in>lbs - {} - (s \<union> {\<alpha>}). x \<inter> \<alpha>6 = {})) \<and>
           (\<forall>\<alpha>7. \<alpha>7 \<subseteq> \<Inter> s \<inter> \<alpha> \<and> (\<forall>\<alpha>8\<in>lbs - {} - (s \<union> {\<alpha>}). \<alpha>7 \<inter> \<alpha>8 = {}) \<longrightarrow>
                  \<alpha>7 \<subseteq> x)"
                 by force
  
         from this finite_lbs
         have inst: "(s \<union> {\<alpha>}) \<subseteq> lbs  \<and>
                (x \<subseteq> \<Inter> (s \<union> {\<alpha>}) \<and> (\<forall>\<alpha>2\<in>lbs - (s \<union> {\<alpha>}). x \<inter> \<alpha>2 = {})) \<and>
                (\<forall>\<alpha>3. \<alpha>3 \<subseteq> \<Inter> (s \<union> {\<alpha>}) \<and> (\<forall>\<alpha>4\<in>lbs - (s \<union> {\<alpha>}). \<alpha>3 \<inter> \<alpha>4 = {})
                     \<longrightarrow> \<alpha>3 \<subseteq> x)"
           by force
         from this
         have case2: "xa \<in> {(q, x, q')} \<Longrightarrow> 
                     case xa of (q, \<alpha>1, q') \<Rightarrow>
                            \<exists>s\<subseteq>lbs.
                      (\<alpha>1 \<subseteq> \<Inter> s \<and> (\<forall>\<alpha>2\<in>lbs - s. \<alpha>1 \<inter> \<alpha>2 = {})) \<and>
                      (\<forall>\<alpha>3. \<alpha>3 \<subseteq> \<Inter> s \<and> (\<forall>\<alpha>4\<in>lbs - s. \<alpha>3 \<inter> \<alpha>4 = {}) \<longrightarrow> \<alpha>3 \<subseteq> \<alpha>1)"
         proof -
           assume xa_v: "xa \<in> {(q, x, q')}"
           from this have "xa = (q, x, q')" by auto
           from this
           show " case xa of (q, \<alpha>1, q') \<Rightarrow>
                            \<exists>s\<subseteq>lbs.
                      (\<alpha>1 \<subseteq> \<Inter> s \<and> (\<forall>\<alpha>2\<in>lbs - s. \<alpha>1 \<inter> \<alpha>2 = {})) \<and>
                      (\<forall>\<alpha>3. \<alpha>3 \<subseteq> \<Inter> s \<and> (\<forall>\<alpha>4\<in>lbs - s. \<alpha>3 \<inter> \<alpha>4 = {}) \<longrightarrow> \<alpha>3 \<subseteq> \<alpha>1)"
             apply simp     
             using inst
             by meson
         qed
         from this xa_cons case1
          show "case xa of (q, \<alpha>1, q') \<Rightarrow>
                    \<exists>s\<subseteq>lbs.
                      (\<alpha>1 \<subseteq> \<Inter> s \<and> (\<forall>\<alpha>2\<in>lbs - s. \<alpha>1 \<inter> \<alpha>2 = {})) \<and>
                      (\<forall>\<alpha>3. \<alpha>3 \<subseteq> \<Inter> s \<and> (\<forall>\<alpha>4\<in>lbs - s. \<alpha>3 \<inter> \<alpha>4 = {}) \<longrightarrow> \<alpha>3 \<subseteq> \<alpha>1)"
            by auto
        qed
         }
         qed
       }
     qed
   }
   {
     fix \<sigma> \<sigma>'
     assume pre1: "(\<Union> \<sigma> = \<alpha> \<and> finite \<sigma>) \<and>
       (\<forall>\<alpha>1 \<alpha>2. \<alpha>1 \<in> \<sigma> \<and> \<alpha>2 \<in> \<sigma> \<longrightarrow> \<alpha>1 = \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {}) \<and>
       (\<forall>\<alpha>3 \<alpha>4. \<alpha>3 \<in> \<sigma> \<and> \<alpha>4 \<in> lbs - {} \<longrightarrow> \<alpha>3 \<subseteq> \<alpha>4 \<or> \<alpha>3 \<inter> \<alpha>4 = {}) \<and>
       (\<forall>\<alpha>5\<in>\<sigma>.
           \<exists>s\<subseteq>lbs - {}.
              (\<alpha>5 \<subseteq> \<Inter> s \<inter> \<alpha> \<and> (\<forall>\<alpha>6\<in>lbs - {} - (s \<union> {\<alpha>}). \<alpha>5 \<inter> \<alpha>6 = {})) \<and>
              (\<forall>\<alpha>7. \<alpha>7 \<subseteq> \<Inter> s \<inter> \<alpha> \<and> (\<forall>\<alpha>8\<in>lbs - {} - (s \<union> {\<alpha>}). \<alpha>7 \<inter> \<alpha>8 = {}) \<longrightarrow>
                     \<alpha>7 \<subseteq> \<alpha>5))"
        and pre2: "(\<forall>(q1, \<alpha>1', q1')\<in>\<sigma>'. q = q1 \<and> q' = q1') \<and>
       \<Union> {\<alpha>1. (q, \<alpha>1, q') \<in> \<sigma>'} = \<Union> (\<sigma> - {}) \<and>
       {\<alpha>1. (q, \<alpha>1, q') \<in> \<sigma>'} = \<sigma> - {} \<and>
       (\<forall>(q, \<alpha>1, q')\<in>\<sigma>'.
           \<exists>s\<subseteq>lbs.
              (\<alpha>1 \<subseteq> \<Inter> s \<and> (\<forall>\<alpha>2\<in>lbs - s. \<alpha>1 \<inter> \<alpha>2 = {})) \<and>
              (\<forall>\<alpha>3. \<alpha>3 \<subseteq> \<Inter> s \<and> (\<forall>\<alpha>4\<in>lbs - s. \<alpha>3 \<inter> \<alpha>4 = {}) \<longrightarrow> \<alpha>3 \<subseteq> \<alpha>1)) \<and>
       (\<forall>\<alpha>1 \<alpha>2. {\<alpha>1, \<alpha>2} \<subseteq> {\<alpha>1. (q, \<alpha>1, q') \<in> \<sigma>'} \<longrightarrow> \<alpha>1 = \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {}) \<and>
       (\<forall>\<alpha>1 \<alpha>2. \<alpha>1 \<in> {\<alpha>1. (q, \<alpha>1, q') \<in> \<sigma>'} \<and> \<alpha>2 \<in> lbs \<longrightarrow> \<alpha>1 \<subseteq> \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {})"
     show "(\<forall>(q1, \<alpha>1', q1')\<in>\<sigma>'. q = q1 \<and> q' = q1') \<and>
       \<Union> {\<alpha>1. (q, \<alpha>1, q') \<in> \<sigma>'} = \<alpha> \<and>
       (\<forall>\<alpha>1 \<alpha>2. {\<alpha>1, \<alpha>2} \<subseteq> {\<alpha>1. (q, \<alpha>1, q') \<in> \<sigma>'} \<longrightarrow> \<alpha>1 = \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {}) \<and>
       (\<forall>(q, \<alpha>1, q')\<in>\<sigma>'.
           \<exists>s\<subseteq>lbs.
              (\<alpha>1 \<subseteq> \<Inter> s \<and> (\<forall>\<alpha>2\<in>lbs - s. \<alpha>1 \<inter> \<alpha>2 = {})) \<and>
              (\<forall>\<alpha>3. \<alpha>3 \<subseteq> \<Inter> s \<and> (\<forall>\<alpha>4\<in>lbs - s. \<alpha>3 \<inter> \<alpha>4 = {}) \<longrightarrow> \<alpha>3 \<subseteq> \<alpha>1)) \<and>
       (\<forall>\<alpha>1 \<alpha>2. \<alpha>1 \<in> {\<alpha>1. (q, \<alpha>1, q') \<in> \<sigma>'} \<and> \<alpha>2 \<in> lbs \<longrightarrow> \<alpha>1 \<subseteq> \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {})"
       apply (rule conjI)
       using pre2 apply simp
       apply (rule conjI)
       using pre2 pre1 apply simp
       apply (rule conjI)
       using pre1 pre2 apply blast
       apply (rule conjI)
       defer
       using pre2 pre1 
       apply auto[1]
       using pre2 pre1 by fast 
   }
 qed

definition split_trans :: "('q, 'a) LTS \<Rightarrow> ('q, 'a) LTS nres" 
 where
  "split_trans TS = do {
    lbs \<leftarrow> labels TS; 
    (FOREACHi
        (\<lambda> TS' Trans'. {(q,q') | q q' \<alpha>. (q, \<alpha>, q') \<in> Trans'} = 
                       {(q,q') | q q' \<alpha>. (q, \<alpha>, q') \<in> TS - TS'} \<and> 
                       (\<forall> q q'. \<Union> {\<alpha>. (q, \<alpha>, q') \<in> Trans'} = 
                                \<Union> {\<alpha>. (q, \<alpha>, q') \<in> TS - TS'}) \<and>
                       (\<forall> (q, \<alpha>1, q') \<in> Trans'. 
                         \<exists> s \<subseteq> lbs. (\<alpha>1 \<subseteq> \<Inter> s \<and> (\<forall> \<alpha>2 \<in> lbs - s. \<alpha>1 \<inter> \<alpha>2 = {})) \<and>
                          (\<forall> \<alpha>3. \<alpha>3 \<subseteq> \<Inter> s \<and> (\<forall> \<alpha>4 \<in> lbs - s. \<alpha>3 \<inter> \<alpha>4 = {}) \<longrightarrow> 
                                 \<alpha>3 \<subseteq> \<alpha>1)) \<and>
                       (\<forall> q1 \<alpha>1 q1' q2 \<alpha>2 q2'. (q1, \<alpha>1, q1') \<in> Trans' \<and>
                         (q2, \<alpha>2, q2') \<in> Trans' \<longrightarrow> \<alpha>1 = \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {}) \<and>
                       (\<forall> (q, \<alpha>, q') \<in> Trans'. (\<forall> \<alpha>' \<in> lbs. \<alpha> \<subseteq> \<alpha>' \<or> \<alpha> \<inter> \<alpha>' = {})))
        TS 
        (\<lambda> (q, \<alpha>, q') Trans. 
         do {
           Tran  \<leftarrow> (split_tran q \<alpha> q' lbs);
           RETURN (Trans \<union> Tran)
         })
         {}
      )
    }"



lemma split_trans_correct:
  fixes TS
  assumes finite_TS: "finite TS"
    and TS_cons1: "\<forall> (q, \<alpha>, q') \<in> TS. \<alpha> \<noteq> {}"
  shows "split_trans TS \<le> 
         SPEC (\<lambda> Trans. {(q,q') | q q' \<alpha>. (q, \<alpha>, q') \<in> Trans} = 
                        {(q,q') | q q' \<alpha>. (q, \<alpha>, q') \<in> TS} \<and> 
                        (\<forall> q q'. \<Union> {\<alpha>. (q, \<alpha>, q') \<in> Trans} = 
                                 \<Union> {\<alpha>. (q, \<alpha>, q') \<in> TS}) \<and>
                        (\<forall> q1 \<alpha>1 q1' q2 \<alpha>2 q2'. (q1, \<alpha>1, q1') \<in> Trans \<and>
                         (q2, \<alpha>2, q2') \<in> Trans \<longrightarrow> \<alpha>1 = \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {}))"
  unfolding split_trans_def labels_def
  apply (intro refine_vcg)
  using finite_TS 
  apply simp
  apply auto[1]
  apply (auto simp add: case_split)[1]
  apply (rename_tac q \<alpha> q' it \<sigma>)  
  defer  
proof -
  define lbs where "lbs = {\<alpha> | q \<alpha> q'. (q, \<alpha>, q') \<in> TS}"
  {
    fix \<sigma>
    assume last_iter: "
         {uu. \<exists>q q' \<alpha>. uu = (q, q') \<and> (q, \<alpha>, q') \<in> \<sigma>} =
         {uu. \<exists>q q' \<alpha>. uu = (q, q') \<and> (q, \<alpha>, q') \<in> TS - {}} \<and>
         (\<forall>q q'. \<Union> {\<alpha>. (q, \<alpha>, q') \<in> \<sigma>} = \<Union> {\<alpha>. (q, \<alpha>, q') \<in> TS - {}}) \<and>
         (\<forall>(q, \<alpha>1, q')\<in>\<sigma>.
             \<exists>s\<subseteq>{uu. \<exists>q \<alpha> q'. uu = \<alpha> \<and> (q, \<alpha>, q') \<in> TS}.
                (\<alpha>1 \<subseteq> \<Inter> s \<and>
                 (\<forall>\<alpha>2\<in>{uu. \<exists>q \<alpha> q'. uu = \<alpha> \<and> (q, \<alpha>, q') \<in> TS} - s. \<alpha>1 \<inter> \<alpha>2 = {})) \<and>
                (\<forall>\<alpha>3. \<alpha>3 \<subseteq> \<Inter> s \<and>
                       (\<forall>\<alpha>4\<in>{uu. \<exists>q \<alpha> q'. uu = \<alpha> \<and> (q, \<alpha>, q') \<in> TS} - s.
                           \<alpha>3 \<inter> \<alpha>4 = {}) \<longrightarrow>
                       \<alpha>3 \<subseteq> \<alpha>1)) \<and>
         (\<forall>q1 \<alpha>1 q1' q2 \<alpha>2 q2'.
             (q1, \<alpha>1, q1') \<in> \<sigma> \<and> (q2, \<alpha>2, q2') \<in> \<sigma> \<longrightarrow> \<alpha>1 = \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {})\<and>
         (\<forall>(q, \<alpha>, q')\<in>\<sigma>.
             \<forall>\<alpha>'\<in>{uu. \<exists>q \<alpha> q'. uu = \<alpha> \<and> (q, \<alpha>, q') \<in> TS}. \<alpha> \<subseteq> \<alpha>' \<or> \<alpha> \<inter> \<alpha>' = {})"
    show "{uu. \<exists>q q' \<alpha>. uu = (q, q') \<and> (q, \<alpha>, q') \<in> \<sigma>} =
          {uu. \<exists>q q' \<alpha>. uu = (q, q') \<and> (q, \<alpha>, q') \<in> TS} \<and>
          (\<forall>q q'. \<Union> {\<alpha>. (q, \<alpha>, q') \<in> \<sigma>} = \<Union> {\<alpha>. (q, \<alpha>, q') \<in> TS}) \<and>
          (\<forall>q1 \<alpha>1 q1' q2 \<alpha>2 q2'.
             (q1, \<alpha>1, q1') \<in> \<sigma> \<and> (q2, \<alpha>2, q2') \<in> \<sigma> \<longrightarrow> \<alpha>1 = \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {})"
      apply (rule conjI)
      using last_iter apply simp
      apply (rule conjI)
      using last_iter apply simp
      using last_iter lbs_def by simp
  }
  {
    fix q \<alpha> q' it \<sigma>
    assume
        it_in: "(q, \<alpha>, q') \<in> it"
    and it_TS: "it \<subseteq> TS"
    and prem1: "{(q, q'). \<exists>\<alpha>. (q, \<alpha>, q') \<in> \<sigma>} =
                 {(q, q'). \<exists>\<alpha>. (q, \<alpha>, q') \<in> TS \<and> (q, \<alpha>, q') \<notin> it}"
    and prem2: "\<forall>q q'. \<Union> {\<alpha>. (q, \<alpha>, q') \<in> \<sigma>} = 
                       \<Union> {\<alpha>. (q, \<alpha>, q') \<in> TS \<and> (q, \<alpha>, q') \<notin> it}"
    and prem3: "\<forall>q1 \<alpha>1 q1' q2 \<alpha>2.
          (q1, \<alpha>1, q1') \<in> \<sigma> \<and> (\<exists>q2'. (q2, \<alpha>2, q2') \<in> \<sigma>) \<longrightarrow> \<alpha>1 = \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {}"
    and prem4: "\<forall>x\<in>\<sigma>. case x of
              (q, \<alpha>, q') \<Rightarrow> \<forall>\<alpha>'. (\<exists>q q'. (q, \<alpha>', q') \<in> TS) \<longrightarrow> \<alpha> \<subseteq> \<alpha>' \<or> \<alpha> \<inter> \<alpha>' = {}"
    and prem5: "\<forall>x\<in>\<sigma>. case x of
              (q, \<alpha>1, q') \<Rightarrow>
                \<exists>s\<subseteq>{uu. \<exists>q q'. (q, uu, q') \<in> TS}.
                   \<alpha>1 \<subseteq> \<Inter> s \<and>
                   (\<forall>\<alpha>2\<in>{uu. \<exists>q q'. (q, uu, q') \<in> TS} - s. \<alpha>1 \<inter> \<alpha>2 = {}) \<and>
                   (\<forall>\<alpha>3. \<alpha>3 \<subseteq> \<Inter> s \<and>
                          (\<forall>\<alpha>4\<in>{uu. \<exists>q q'. (q, uu, q') \<in> TS} - s. \<alpha>3 \<inter> \<alpha>4 = {}) \<longrightarrow>
                          \<alpha>3 \<subseteq> \<alpha>1)"
    define lbs where "lbs = {\<alpha> | q \<alpha> q'. (q, \<alpha>, q') \<in> TS}"
    from lbs_def finite_imageI[of TS "\<lambda>(q,\<alpha>,q'). \<alpha>"]
    have "lbs = (\<lambda>(q,\<alpha>,q'). \<alpha>) ` TS"
      by auto
    from finite_imageI[of TS "\<lambda>(q,\<alpha>,q'). \<alpha>"] this finite_TS
    have finite_lbs: "finite lbs \<and> \<alpha> \<in> lbs"     
      using it_TS it_in lbs_def by force
    from this lbs_def
    have finite_lbs': "finite {uu. \<exists>q q'. (q, uu, q') \<in> TS}"
      by simp

    have SPEC1: "SPEC (\<lambda>trans.
            (\<forall>(q1, \<alpha>1', q1')\<in>trans. q = q1 \<and> q' = q1') \<and>
            \<Union> {\<alpha>1. (q, \<alpha>1, q') \<in> trans} = \<alpha> \<and>
            (\<forall>\<alpha>1 \<alpha>2.
                {\<alpha>1, \<alpha>2} \<subseteq> {\<alpha>1. (q, \<alpha>1, q') \<in> trans} \<longrightarrow> \<alpha>1 = \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {}) \<and>
            (\<forall>(q, \<alpha>1, q')\<in>trans.
                \<exists>s\<subseteq>lbs.
                   (\<alpha>1 \<subseteq> \<Inter> s \<and> (\<forall>\<alpha>2\<in>lbs - s. \<alpha>1 \<inter> \<alpha>2 = {})) \<and>
                   (\<forall>\<alpha>3. \<alpha>3 \<subseteq> \<Inter> s \<and> (\<forall>\<alpha>4\<in>lbs - s. \<alpha>3 \<inter> \<alpha>4 = {}) \<longrightarrow> \<alpha>3 \<subseteq> \<alpha>1)) \<and>
            (\<forall>\<alpha>1 \<alpha>2.
                \<alpha>1 \<in> {\<alpha>1. (q, \<alpha>1, q') \<in> trans} \<and> \<alpha>2 \<in> lbs \<longrightarrow> \<alpha>1 \<subseteq> \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {})) 
          \<le>
        SPEC (\<lambda>Tran. RETURN (\<sigma> \<union> Tran)
                    \<le> SPEC (\<lambda>Trans'.
                                {(q, q'). \<exists>\<alpha>. (q, \<alpha>, q') \<in> Trans'} =
                                {(qa, q'a).
                                 \<exists>\<alpha>'. (qa, \<alpha>', q'a) \<in> TS \<and>
                                       ((qa, \<alpha>', q'a) \<in> it \<longrightarrow>
                                        qa = q \<and> \<alpha>' = \<alpha> \<and> q'a = q')} \<and>
                                (\<forall>qa q'a.
                                    \<Union> {\<alpha>. (qa, \<alpha>, q'a) \<in> Trans'} =
                                    \<Union> {\<alpha>'. (qa, \<alpha>', q'a) \<in> TS \<and>
((qa, \<alpha>', q'a) \<in> it \<longrightarrow> qa = q \<and> \<alpha>' = \<alpha> \<and> q'a = q')}) \<and>
                                (\<forall>x\<in>Trans'.
                                    case x of
                                    (q, \<alpha>1, q') \<Rightarrow>
                                      \<exists>s\<subseteq>{uu. \<exists>q q'. (q, uu, q') \<in> TS}.
                                         \<alpha>1 \<subseteq> \<Inter> s \<and>
                                         (\<forall>\<alpha>2\<in>{uu. \<exists>q q'. (q, uu, q') \<in> TS} - s.
 \<alpha>1 \<inter> \<alpha>2 = {}) \<and>
                                         (\<forall>\<alpha>3.
 \<alpha>3 \<subseteq> \<Inter> s \<and> (\<forall>\<alpha>4\<in>{uu. \<exists>q q'. (q, uu, q') \<in> TS} - s. \<alpha>3 \<inter> \<alpha>4 = {}) \<longrightarrow> \<alpha>3 \<subseteq> \<alpha>1)) \<and>
                                (\<forall>q1 \<alpha>1 q1' q2 \<alpha>2.
                                    (q1, \<alpha>1, q1') \<in> Trans' \<and>
                                    (\<exists>q2'. (q2, \<alpha>2, q2') \<in> Trans') \<longrightarrow>
                                    \<alpha>1 = \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {}) \<and>
                                (\<forall>x\<in>Trans'.
                                    case x of
                                    (q, \<alpha>, q') \<Rightarrow>
                                      \<forall>\<alpha>'. (\<exists>q q'. (q, \<alpha>', q') \<in> TS) \<longrightarrow>
\<alpha> \<subseteq> \<alpha>' \<or> \<alpha> \<inter> \<alpha>' = {})))
        "
      apply simp
      proof
      {
        fix x
        assume x_in_trans: "x \<in> {trans.
              (\<forall>(q1, ab)\<in>trans. q = q1 \<and> (case ab of (\<alpha>1', x) \<Rightarrow> q' = x)) \<and>
              \<Union> {\<alpha>1. (q, \<alpha>1, q') \<in> trans} = \<alpha> \<and>
              (\<forall>\<alpha>1 \<alpha>2.
                  (q, \<alpha>1, q') \<in> trans \<and> (q, \<alpha>2, q') \<in> trans \<longrightarrow>
                  \<alpha>1 = \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {}) \<and>
              (\<forall>(q, \<alpha>1, q')\<in>trans.
                  \<exists>s\<subseteq>lbs.
                     \<alpha>1 \<subseteq> \<Inter> s \<and>
                     (\<forall>\<alpha>2\<in>lbs - s. \<alpha>1 \<inter> \<alpha>2 = {}) \<and>
                     (\<forall>\<alpha>3. \<alpha>3 \<subseteq> \<Inter> s \<and> (\<forall>\<alpha>4\<in>lbs - s. \<alpha>3 \<inter> \<alpha>4 = {}) \<longrightarrow> \<alpha>3 \<subseteq> \<alpha>1)) \<and>
              (\<forall>\<alpha>1 \<alpha>2. (q, \<alpha>1, q') \<in> trans \<and> \<alpha>2 \<in> lbs \<longrightarrow> \<alpha>1 \<subseteq> \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {})}"
        from this
        show "x \<in> {Tran.
               {(q, q'). \<exists>\<alpha>. (q, \<alpha>, q') \<in> \<sigma> \<or> (q, \<alpha>, q') \<in> Tran} =
               {(qa, q'a).
                \<exists>\<alpha>'. (qa, \<alpha>', q'a) \<in> TS \<and>
                      ((qa, \<alpha>', q'a) \<in> it \<longrightarrow> qa = q \<and> \<alpha>' = \<alpha> \<and> q'a = q')} \<and>
               (\<forall>qa q'a.
                   \<Union> {\<alpha>. (qa, \<alpha>, q'a) \<in> \<sigma> \<or> (qa, \<alpha>, q'a) \<in> Tran} =
                   \<Union> {\<alpha>'. (qa, \<alpha>', q'a) \<in> TS \<and>
                           ((qa, \<alpha>', q'a) \<in> it \<longrightarrow> qa = q \<and> \<alpha>' = \<alpha> \<and> q'a = q')}) \<and>
               (\<forall>(q, \<alpha>1, q')\<in>\<sigma> \<union> Tran.
                   \<exists>s\<subseteq>{uu. \<exists>q q'. (q, uu, q') \<in> TS}.
                      \<alpha>1 \<subseteq> \<Inter> s \<and>
                      (\<forall>\<alpha>2\<in>{uu. \<exists>q q'. (q, uu, q') \<in> TS} - s. \<alpha>1 \<inter> \<alpha>2 = {}) \<and>
                      (\<forall>\<alpha>3. \<alpha>3 \<subseteq> \<Inter> s \<and>
                             (\<forall>\<alpha>4\<in>{uu. \<exists>q q'. (q, uu, q') \<in> TS} - s. \<alpha>3 \<inter> \<alpha>4 = {}) \<longrightarrow>
                             \<alpha>3 \<subseteq> \<alpha>1)) \<and>
               (\<forall>q1 \<alpha>1 q1' q2 \<alpha>2.
                   ((q1, \<alpha>1, q1') \<in> \<sigma> \<or> (q1, \<alpha>1, q1') \<in> Tran) \<and>
                   (\<exists>q2'. (q2, \<alpha>2, q2') \<in> \<sigma> \<or> (q2, \<alpha>2, q2') \<in> Tran) \<longrightarrow>
                   \<alpha>1 = \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {}) \<and>
               (\<forall>(q, \<alpha>, q')\<in>\<sigma> \<union> Tran.
                   \<forall>\<alpha>'. (\<exists>q q'. (q, \<alpha>', q') \<in> TS) \<longrightarrow> \<alpha> \<subseteq> \<alpha>' \<or> \<alpha> \<inter> \<alpha>' = {})}"
        proof
          assume x_in_trans': "
         (\<forall>(q1, ab)\<in>x. q = q1 \<and> (case ab of (\<alpha>1', x) \<Rightarrow> q' = x)) \<and>
    \<Union> {\<alpha>1. (q, \<alpha>1, q') \<in> x} = \<alpha> \<and>
    (\<forall>\<alpha>1 \<alpha>2. (q, \<alpha>1, q') \<in> x \<and> (q, \<alpha>2, q') \<in> x \<longrightarrow> \<alpha>1 = \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {}) \<and>
    (\<forall>(q, \<alpha>1, q')\<in>x.
        \<exists>s\<subseteq>lbs.
           \<alpha>1 \<subseteq> \<Inter> s \<and>
           (\<forall>\<alpha>2\<in>lbs - s. \<alpha>1 \<inter> \<alpha>2 = {}) \<and>
           (\<forall>\<alpha>3. \<alpha>3 \<subseteq> \<Inter> s \<and> (\<forall>\<alpha>4\<in>lbs - s. \<alpha>3 \<inter> \<alpha>4 = {}) \<longrightarrow> \<alpha>3 \<subseteq> \<alpha>1)) \<and>
    (\<forall>\<alpha>1 \<alpha>2. (q, \<alpha>1, q') \<in> x \<and> \<alpha>2 \<in> lbs \<longrightarrow> \<alpha>1 \<subseteq> \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {})"
          show "x \<in> {Tran.
          {(q, q'). \<exists>\<alpha>. (q, \<alpha>, q') \<in> \<sigma> \<or> (q, \<alpha>, q') \<in> Tran} =
          {(qa, q'a).
           \<exists>\<alpha>'. (qa, \<alpha>', q'a) \<in> TS \<and>
                 ((qa, \<alpha>', q'a) \<in> it \<longrightarrow> qa = q \<and> \<alpha>' = \<alpha> \<and> q'a = q')} \<and>
          (\<forall>qa q'a.
              \<Union> {\<alpha>. (qa, \<alpha>, q'a) \<in> \<sigma> \<or> (qa, \<alpha>, q'a) \<in> Tran} =
              \<Union> {\<alpha>'. (qa, \<alpha>', q'a) \<in> TS \<and>
                      ((qa, \<alpha>', q'a) \<in> it \<longrightarrow> qa = q \<and> \<alpha>' = \<alpha> \<and> q'a = q')}) \<and>
          (\<forall>(q, \<alpha>1, q')\<in>\<sigma> \<union> Tran.
              \<exists>s\<subseteq>{uu. \<exists>q q'. (q, uu, q') \<in> TS}.
                 \<alpha>1 \<subseteq> \<Inter> s \<and>
                 (\<forall>\<alpha>2\<in>{uu. \<exists>q q'. (q, uu, q') \<in> TS} - s. \<alpha>1 \<inter> \<alpha>2 = {}) \<and>
                 (\<forall>\<alpha>3. \<alpha>3 \<subseteq> \<Inter> s \<and>
                        (\<forall>\<alpha>4\<in>{uu. \<exists>q q'. (q, uu, q') \<in> TS} - s. \<alpha>3 \<inter> \<alpha>4 = {}) \<longrightarrow>
                        \<alpha>3 \<subseteq> \<alpha>1)) \<and>
          (\<forall>q1 \<alpha>1 q1' q2 \<alpha>2.
              ((q1, \<alpha>1, q1') \<in> \<sigma> \<or> (q1, \<alpha>1, q1') \<in> Tran) \<and>
              (\<exists>q2'. (q2, \<alpha>2, q2') \<in> \<sigma> \<or> (q2, \<alpha>2, q2') \<in> Tran) \<longrightarrow>
              \<alpha>1 = \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {}) \<and>
          (\<forall>(q, \<alpha>, q')\<in>\<sigma> \<union> Tran.
              \<forall>\<alpha>'. (\<exists>q q'. (q, \<alpha>', q') \<in> TS) \<longrightarrow> \<alpha> \<subseteq> \<alpha>' \<or> \<alpha> \<inter> \<alpha>' = {})}"
   proof
  show "{(q, q'). \<exists>\<alpha>. (q, \<alpha>, q') \<in> \<sigma> \<or> (q, \<alpha>, q') \<in> x} =
    {(qa, q'a).
     \<exists>\<alpha>'. (qa, \<alpha>', q'a) \<in> TS \<and> ((qa, \<alpha>', q'a) \<in> it \<longrightarrow> qa = q \<and> \<alpha>' = \<alpha> \<and> q'a = q')} \<and>
    (\<forall>qa q'a.
        \<Union> {\<alpha>. (qa, \<alpha>, q'a) \<in> \<sigma> \<or> (qa, \<alpha>, q'a) \<in> x} =
        \<Union> {\<alpha>'. (qa, \<alpha>', q'a) \<in> TS \<and>
                ((qa, \<alpha>', q'a) \<in> it \<longrightarrow> qa = q \<and> \<alpha>' = \<alpha> \<and> q'a = q')}) \<and>
    (\<forall>(q, \<alpha>1, q')\<in>\<sigma> \<union> x.
        \<exists>s\<subseteq>{uu. \<exists>q q'. (q, uu, q') \<in> TS}.
           \<alpha>1 \<subseteq> \<Inter> s \<and>
           (\<forall>\<alpha>2\<in>{uu. \<exists>q q'. (q, uu, q') \<in> TS} - s. \<alpha>1 \<inter> \<alpha>2 = {}) \<and>
           (\<forall>\<alpha>3. \<alpha>3 \<subseteq> \<Inter> s \<and> (\<forall>\<alpha>4\<in>{uu. \<exists>q q'. (q, uu, q') \<in> TS} - s. \<alpha>3 \<inter> \<alpha>4 = {}) \<longrightarrow>
                  \<alpha>3 \<subseteq> \<alpha>1)) \<and>
    (\<forall>q1 \<alpha>1 q1' q2 \<alpha>2.
        ((q1, \<alpha>1, q1') \<in> \<sigma> \<or> (q1, \<alpha>1, q1') \<in> x) \<and>
        (\<exists>q2'. (q2, \<alpha>2, q2') \<in> \<sigma> \<or> (q2, \<alpha>2, q2') \<in> x) \<longrightarrow>
        \<alpha>1 = \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {}) \<and>
    (\<forall>(q, \<alpha>, q')\<in>\<sigma> \<union> x. \<forall>\<alpha>'. (\<exists>q q'. (q, \<alpha>', q') \<in> TS) \<longrightarrow> \<alpha> \<subseteq> \<alpha>' \<or> \<alpha> \<inter> \<alpha>' = {})"
    apply (rule conjI)+
    defer
     apply (rule conjI)+
    defer
      apply (rule conjI)+  
       defer
    apply (rule conjI)+ 
  proof -
    {
    show "{(q, q'). \<exists>\<alpha>. (q, \<alpha>, q') \<in> \<sigma> \<or> (q, \<alpha>, q') \<in> x} =
          {(qa, q'a). \<exists>\<alpha>'. (qa, \<alpha>', q'a) \<in> TS \<and> 
                           ((qa, \<alpha>', q'a) \<in> it \<longrightarrow> qa = q \<and> \<alpha>' = \<alpha> \<and> q'a = q')}"
    proof -
      from x_in_trans' TS_cons1 it_in it_TS
      have x_nempty: "x \<noteq> {}"
        using Sup_empty by auto

      from x_in_trans'
      have "\<forall>(q1, \<alpha>, q2) \<in> x. q = q1 \<and> q' = q2"
        by auto
      from this x_nempty
      have x_capacity: "{(q, q')| q q' \<alpha>. (q, \<alpha>, q') \<in> x} = {(q,q')}"
        by auto
      thm this prem1
      show "{(q, q'). \<exists>\<alpha>. (q, \<alpha>, q') \<in> \<sigma> \<or> (q, \<alpha>, q') \<in> x} =
            {(qa, q'a). \<exists>\<alpha>'. (qa, \<alpha>', q'a) \<in> TS \<and> 
             ((qa, \<alpha>', q'a) \<in> it \<longrightarrow> qa = q \<and> \<alpha>' = \<alpha> \<and> q'a = q')}"
        using  set_eq_iff
        apply auto
        using x_capacity prem1
        apply fastforce
        using x_capacity prem1
        apply (metis (mono_tags, lifting) 
        case_prodD it_TS it_in subset_iff x_in_trans')
        using x_capacity prem1
        apply fastforce
        using x_capacity prem1
        by fastforce
    qed
  }
   {
    from prem4 
    have case1: "\<forall>(q, \<alpha>, q') \<in> \<sigma>. \<forall>\<alpha>'. 
              (\<exists>q q'. (q, \<alpha>', q') \<in> TS) \<longrightarrow> \<alpha> \<subseteq> \<alpha>' \<or> \<alpha> \<inter> \<alpha>' = {}"
      by simp

    from x_in_trans'
    have image: "(\<forall>\<alpha>1 \<alpha>2. (q, \<alpha>1, q') \<in> x \<and> \<alpha>2 \<in> lbs \<longrightarrow> \<alpha>1 \<subseteq> \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {})"
      by auto

    from  x_in_trans' 
    have "\<forall> (q1, \<alpha>, q1') \<in> x. q1 = q \<and> q1' = q'"
      by auto
    from  this image lbs_def
    have case2: "\<forall> (q, \<alpha>, q') \<in> x . \<forall> \<alpha>'. (\<exists>q q'. (q, \<alpha>', q') \<in> TS) 
              \<longrightarrow> \<alpha> \<subseteq> \<alpha>' \<or> \<alpha> \<inter> \<alpha>' = {}"
      by force

    from case1 case2
    show "\<forall>(q, \<alpha>, q')\<in>\<sigma> \<union> x. \<forall>\<alpha>'. 
              (\<exists>q q'. (q, \<alpha>', q') \<in> TS) \<longrightarrow> \<alpha> \<subseteq> \<alpha>' \<or> \<alpha> \<inter> \<alpha>' = {}"
      by blast
  }
  {
    thm prem2 x_in_trans'
    show "\<forall>qa q'a.
       \<Union> {\<alpha>. (qa, \<alpha>, q'a) \<in> \<sigma> \<or> (qa, \<alpha>, q'a) \<in> x} =
       \<Union> {\<alpha>'. (qa, \<alpha>', q'a) \<in> TS \<and>
               ((qa, \<alpha>', q'a) \<in> it \<longrightarrow> qa = q \<and> \<alpha>' = \<alpha> \<and> q'a = q')}"
      apply (rule allI)+
      apply (rename_tac q1 q1')
    proof
      {
        fix q1 q1'
        show "\<Union> {\<alpha>. (q1, \<alpha>, q1') \<in> \<sigma> \<or> (q1, \<alpha>, q1') \<in> x}
            \<subseteq> \<Union> {\<alpha>'. (q1, \<alpha>', q1') \<in> TS \<and> ((q1, \<alpha>', q1') \<in> it \<longrightarrow> 
                q1 = q \<and> \<alpha>' = \<alpha> \<and> q1' = q')}"
        proof
          fix xa
          assume xa_in : "xa \<in> \<Union> {\<alpha>. (q1, \<alpha>, q1') \<in> \<sigma> \<or> (q1, \<alpha>, q1') \<in> x}"
          from this have inx: "(\<exists> \<alpha>1. (q1, \<alpha>1, q1') \<in> \<sigma> \<and> xa \<in> \<alpha>1) \<or> 
                          (\<exists> \<alpha>1. (q1, \<alpha>1, q1') \<in> x \<and> xa \<in> \<alpha>1)"
            by auto
          show "xa \<in> \<Union> {\<alpha>'. (q1, \<alpha>', q1') \<in> TS \<and>
                       ((q1, \<alpha>', q1') \<in> it \<longrightarrow> q1 = q \<and> \<alpha>' = \<alpha> \<and> q1' = q')}"
          proof (cases "\<exists> \<alpha>1. (q1, \<alpha>1, q1') \<in> \<sigma> \<and> xa \<in> \<alpha>1")
            case True
            from this prem2
            show ?thesis by blast
            next
              case False
              from this inx
              obtain \<alpha>1 where 
              \<alpha>1_def:"(q1, \<alpha>1, q1') \<in> x \<and> xa \<in> \<alpha>1"
                by auto
              from this x_in_trans'
              have "q1 = q \<and> q1' = q' \<and> \<alpha>1 \<subseteq> \<alpha>"
                by auto
              from this it_in \<alpha>1_def
              show ?thesis 
                using it_TS by auto
            qed
          qed
        }
        {
          fix q1 q1'
          show "\<Union> {\<alpha>'. (q1, \<alpha>', q1') \<in> TS \<and>
               ((q1, \<alpha>', q1') \<in> it \<longrightarrow> q1 = q \<and> \<alpha>' = \<alpha> \<and> q1' = q')}
           \<subseteq> \<Union> {\<alpha>. (q1, \<alpha>, q1') \<in> \<sigma> \<or> (q1, \<alpha>, q1') \<in> x}"
          proof
            fix xa
            assume xa_in: "xa \<in> \<Union> {\<alpha>'. (q1, \<alpha>', q1') \<in> TS \<and>
                           ((q1, \<alpha>', q1') \<in> it \<longrightarrow> q1 = q \<and> \<alpha>' = \<alpha> \<and> q1' = q')}"
            from this 
            have xa_div: "xa \<in> \<Union> {\<alpha>'. (q1, \<alpha>', q1') \<in> TS - it} \<or>
                  xa \<in> \<Union> {\<alpha>'. ((q1, \<alpha>', q1') \<in> it \<longrightarrow> q1 = q \<and> \<alpha>' = \<alpha> \<and> q1' = q')}"
              by auto
            show "xa \<in> \<Union> {\<alpha>. (q1, \<alpha>, q1') \<in> \<sigma> \<or> (q1, \<alpha>, q1') \<in> x}"
            proof (cases "xa \<in> \<Union> {\<alpha>'. (q1, \<alpha>', q1') \<in> TS - it}")
              case True
                 
              from True prem2 
              show ?thesis by force 
              next
                case False
                from this xa_div
                have "xa \<in> \<Union> {\<alpha>'. (q1, \<alpha>', q1') \<in> it \<longrightarrow> 
                              q1 = q \<and> \<alpha>' = \<alpha> \<and> q1' = q'}" by blast
                from this it_in 
                have "xa \<in> \<alpha>" 
                  using False xa_in by auto
                from this x_in_trans'
                show ?thesis 
                  using False xa_in by auto
              qed
            qed
          }
        qed

      } 
      
  {
    show "\<forall>q1 \<alpha>1 q1' q2 \<alpha>2.
       ((q1, \<alpha>1, q1') \<in> \<sigma> \<or> (q1, \<alpha>1, q1') \<in> x) \<and>
       (\<exists>q2'. (q2, \<alpha>2, q2') \<in> \<sigma> \<or> (q2, \<alpha>2, q2') \<in> x) \<longrightarrow>
       \<alpha>1 = \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {}"
      apply (rule allI impI)+
    proof -
      fix q1 \<alpha>1 q1' q2 \<alpha>2
      assume in_x: "((q1, \<alpha>1, q1') \<in> \<sigma> \<or> (q1, \<alpha>1, q1') \<in> x) \<and>
                    (\<exists>q2'. (q2, \<alpha>2, q2') \<in> \<sigma> \<or> (q2, \<alpha>2, q2') \<in> x)"
      from prem3
      have case1: "((q1, \<alpha>1, q1') \<in> \<sigma> \<and> (\<exists>q2'. (q2, \<alpha>2, q2') \<in> \<sigma>)) \<Longrightarrow> 
           \<alpha>1 = \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {}"
        by auto

      from x_in_trans'
      have "(\<forall>\<alpha>1 \<alpha>2. (q, \<alpha>1, q') \<in> x \<and> (q, \<alpha>2, q') \<in> x \<longrightarrow> 
                    \<alpha>1 = \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {}) \<and> 
            (\<forall> (q1, \<alpha>1, q1') \<in> x. q1 = q \<and> q1' = q' ) "
        by auto
      from this
      have case2: "(q1, \<alpha>1, q1') \<in> x \<and> (\<exists>q2'. (q2, \<alpha>2, q2') \<in> x) \<Longrightarrow> 
           \<alpha>1 = \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {}"
        by fastforce

      have case3: "(q1, \<alpha>1, q1') \<in> \<sigma> \<and> (\<exists>q2'. (q2, \<alpha>2, q2') \<in> x) \<Longrightarrow>
           \<alpha>1 = \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {}"
      proof -
        assume \<sigma>x_in: "(q1, \<alpha>1, q1') \<in> \<sigma> \<and> (\<exists>q2'. (q2, \<alpha>2, q2') \<in> x)"
        from this obtain q2'
          where q2'_def: "(q1, \<alpha>1, q1') \<in> \<sigma> \<and> (q2, \<alpha>2, q2') \<in> x"
          by auto

        from q2'_def prem4 lbs_def
        have \<alpha>1_info : "\<forall> \<alpha>'. \<alpha>' \<in> lbs \<longrightarrow> \<alpha>1 \<subseteq> \<alpha>' \<or> \<alpha>1 \<inter> \<alpha>' = {}"
          by blast

        from q2'_def x_in_trans'
        have "q2 = q \<and> q2' = q'"
          by auto
        
        from this q2'_def lbs_def x_in_trans' lbs_def
        have \<alpha>2_info: "\<forall> \<alpha>'. \<alpha>' \<in> lbs \<longrightarrow> \<alpha>2 \<subseteq> \<alpha>' \<or> \<alpha>2 \<inter> \<alpha>' = {}"
          by simp

      from prem5 lbs_def
          have "(\<forall>(q, \<alpha>1, q')\<in>\<sigma>.
           \<exists>s\<subseteq>lbs.
           \<alpha>1 \<subseteq> \<Inter> s \<and>
           (\<forall>\<alpha>2\<in>lbs - s. \<alpha>1 \<inter> \<alpha>2 = {}) \<and>
           (\<forall>\<alpha>3. \<alpha>3 \<subseteq> \<Inter> s \<and> (\<forall>\<alpha>4\<in>lbs - s. \<alpha>3 \<inter> \<alpha>4 = {}) \<longrightarrow> \<alpha>3 \<subseteq> \<alpha>1))"
            by simp

    from this q2'_def
    have "\<exists>s\<subseteq>lbs.
      \<alpha>1 \<subseteq> \<Inter> s \<and>
      (\<forall>\<alpha>'\<in>lbs - s. \<alpha>1 \<inter> \<alpha>' = {}) \<and>
      (\<forall>\<alpha>3. \<alpha>3 \<subseteq> \<Inter> s \<and> (\<forall>\<alpha>4\<in>lbs - s. \<alpha>3 \<inter> \<alpha>4 = {}) \<longrightarrow> \<alpha>3 \<subseteq> \<alpha>1)"
      by fastforce


  from this 
        obtain s1 where
        s1_def: "s1 \<subseteq>lbs \<and> \<alpha>1 \<subseteq> \<Inter> s1 \<and> (\<forall>\<alpha>'\<in>lbs - s1. \<alpha>1 \<inter> \<alpha>' = {})
                \<and> (\<forall>\<alpha>3. \<alpha>3 \<subseteq> \<Inter> s1 \<and> (\<forall>\<alpha>4\<in>lbs - s1. \<alpha>3 \<inter> \<alpha>4 = {}) \<longrightarrow> \<alpha>3 \<subseteq> \<alpha>1)"
          by auto
        from this have 
       s1_def': "s1 \<subseteq>lbs \<and> \<alpha>1 \<subseteq> \<Inter> s1 \<and> (\<forall>\<alpha>'\<in>lbs - s1. \<alpha>1 \<inter> \<alpha>' = {})" 
          by auto

      from x_in_trans'
          have "(\<forall>(q, \<alpha>1, q')\<in>x.
         \<exists>s\<subseteq>lbs.
         \<alpha>1 \<subseteq> \<Inter> s \<and>
         (\<forall>\<alpha>2\<in>lbs - s. \<alpha>1 \<inter> \<alpha>2 = {}) \<and>
         (\<forall>\<alpha>3. \<alpha>3 \<subseteq> \<Inter> s \<and> (\<forall>\<alpha>4\<in>lbs - s. \<alpha>3 \<inter> \<alpha>4 = {}) \<longrightarrow> \<alpha>3 \<subseteq> \<alpha>1))"
            by auto


      from this q2'_def 
      have "\<exists>s\<subseteq>lbs.
      \<alpha>2 \<subseteq> \<Inter> s \<and>
      (\<forall>\<alpha>'\<in>lbs - s. \<alpha>2 \<inter> \<alpha>' = {}) \<and>
      (\<forall>\<alpha>3. \<alpha>3 \<subseteq> \<Inter> s \<and> (\<forall>\<alpha>4\<in>lbs - s. \<alpha>3 \<inter> \<alpha>4 = {}) \<longrightarrow> \<alpha>3 \<subseteq> \<alpha>2)"
        by fastforce
        
      from this 
        obtain s2 where
        s2_def: "s2 \<subseteq>lbs \<and> \<alpha>2 \<subseteq> \<Inter> s2 \<and> (\<forall>\<alpha>'\<in>lbs - s2. \<alpha>2 \<inter> \<alpha>' = {})
                \<and> (\<forall>\<alpha>3. \<alpha>3 \<subseteq> \<Inter> s2 \<and> (\<forall>\<alpha>4\<in>lbs - s2. \<alpha>3 \<inter> \<alpha>4 = {}) \<longrightarrow> \<alpha>3 \<subseteq> \<alpha>2)"
          by auto
        from this have 
       s2_def': "s2 \<subseteq>lbs \<and> \<alpha>2 \<subseteq> \<Inter> s2 \<and> (\<forall>\<alpha>'\<in>lbs - s2. \<alpha>2 \<inter> \<alpha>' = {})" 
          by auto
      show "\<alpha>1 = \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {}" 
        proof (rule ccontr)
          assume p1: "\<not> (\<alpha>1 = \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {})"
          from this have \<alpha>1neq\<alpha>2: "\<alpha>1 \<noteq> \<alpha>2 \<and> \<alpha>1 \<inter> \<alpha>2 \<noteq> {}"
            by auto
          from this obtain e
            where e_def: "e \<in> \<alpha>1 \<inter> \<alpha>2" by auto
          from this s1_def'
          have e_s1: "e \<in> \<Inter> s1 \<and> (\<forall>\<alpha>'\<in>lbs - s1. {e} \<inter> \<alpha>' = {}) \<and> s1 \<subseteq>lbs"
            by auto
          from e_def s2_def'
          have e_s2: "e \<in> \<Inter> s2 \<and> (\<forall>\<alpha>'\<in>lbs - s2. {e} \<inter> \<alpha>' = {}) \<and> s2 \<subseteq>lbs"
            by auto
          from e_s1 e_s2
          have s1_eq_s2: "s1 = s2"
            by fastforce

          from s2_def
          have s2_def': 
           "\<forall>\<alpha>3. \<alpha>3 \<subseteq> \<Inter> s2 \<and> (\<forall>\<alpha>4\<in>lbs - s2. \<alpha>3 \<inter> \<alpha>4 = {}) \<longrightarrow> \<alpha>3 \<subseteq> \<alpha>2"
            by auto
          from s1_def s1_eq_s2
          have left1:"\<alpha>1 \<subseteq> \<Inter> s2 \<and> (\<forall>\<alpha>4\<in>lbs - s2. \<alpha>1 \<inter> \<alpha>4 = {})"
            by blast
          from s2_def' left1
          have sub_left: "\<alpha>1 \<subseteq> \<alpha>2"
            by blast


        from s1_def
          have s1_def': 
           "\<forall>\<alpha>3. \<alpha>3 \<subseteq> \<Inter> s1 \<and> (\<forall>\<alpha>4\<in>lbs - s1. \<alpha>3 \<inter> \<alpha>4 = {}) \<longrightarrow> \<alpha>3 \<subseteq> \<alpha>1"
            by auto
          from s2_def s1_eq_s2
          have left1:"\<alpha>2 \<subseteq> \<Inter> s1 \<and> (\<forall>\<alpha>4\<in>lbs - s1. \<alpha>2 \<inter> \<alpha>4 = {})"
            by blast
          from s1_def' left1
          have sub_right: "\<alpha>2 \<subseteq> \<alpha>1"
            by blast
        
          from \<alpha>1neq\<alpha>2 sub_right sub_left
          show "False"
            by blast
        qed
      qed
     have case4: "(q1, \<alpha>1, q1') \<in> x \<and> (\<exists>q2'. (q2, \<alpha>2, q2') \<in> \<sigma>) \<Longrightarrow>
           \<alpha>1 = \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {}"
      proof -
        assume \<sigma>x_in: "(q1, \<alpha>1, q1') \<in> x \<and> (\<exists>q2'. (q2, \<alpha>2, q2') \<in> \<sigma>)"
        from this obtain q2'
          where q2'_def: "(q1, \<alpha>1, q1') \<in> x \<and> (q2, \<alpha>2, q2') \<in> \<sigma>"
          by auto

        from q2'_def prem4 lbs_def
        have \<alpha>2_info : "\<forall> \<alpha>'. \<alpha>' \<in> lbs \<longrightarrow> \<alpha>2 \<subseteq> \<alpha>' \<or> \<alpha>2 \<inter> \<alpha>' = {}"
          by blast

        from q2'_def x_in_trans'
        have "q1 = q \<and> q1' = q'"
          by auto
        
        from this q2'_def lbs_def x_in_trans' lbs_def
        have \<alpha>2_info: "\<forall> \<alpha>'. \<alpha>' \<in> lbs \<longrightarrow> \<alpha>1 \<subseteq> \<alpha>' \<or> \<alpha>1 \<inter> \<alpha>' = {}"
          by simp

       

      from prem5 lbs_def
          have "(\<forall>(q, \<alpha>1, q')\<in>\<sigma>.
           \<exists>s\<subseteq>lbs.
           \<alpha>1 \<subseteq> \<Inter> s \<and>
           (\<forall>\<alpha>2\<in>lbs - s. \<alpha>1 \<inter> \<alpha>2 = {}) \<and>
           (\<forall>\<alpha>3. \<alpha>3 \<subseteq> \<Inter> s \<and> (\<forall>\<alpha>4\<in>lbs - s. \<alpha>3 \<inter> \<alpha>4 = {}) \<longrightarrow> \<alpha>3 \<subseteq> \<alpha>1))"
            by simp

    from this q2'_def
    have "\<exists>s\<subseteq>lbs.
      \<alpha>2 \<subseteq> \<Inter> s \<and>
      (\<forall>\<alpha>'\<in>lbs - s. \<alpha>2 \<inter> \<alpha>' = {}) \<and>
      (\<forall>\<alpha>3. \<alpha>3 \<subseteq> \<Inter> s \<and> (\<forall>\<alpha>4\<in>lbs - s. \<alpha>3 \<inter> \<alpha>4 = {}) \<longrightarrow> \<alpha>3 \<subseteq> \<alpha>2)"
      by fastforce


  from this 
        obtain s2 where
        s2_def: "s2 \<subseteq>lbs \<and> \<alpha>2 \<subseteq> \<Inter> s2 \<and> (\<forall>\<alpha>'\<in>lbs - s2. \<alpha>2 \<inter> \<alpha>' = {})
                \<and> (\<forall>\<alpha>3. \<alpha>3 \<subseteq> \<Inter> s2 \<and> (\<forall>\<alpha>4\<in>lbs - s2. \<alpha>3 \<inter> \<alpha>4 = {}) \<longrightarrow> \<alpha>3 \<subseteq> \<alpha>2)"
          by auto
        from this have 
       s2_def': "s2 \<subseteq>lbs \<and> \<alpha>2 \<subseteq> \<Inter> s2 \<and> (\<forall>\<alpha>'\<in>lbs - s2. \<alpha>2 \<inter> \<alpha>' = {})" 
          by auto

      from x_in_trans'
          have "(\<forall>(q, \<alpha>1, q')\<in>x.
         \<exists>s\<subseteq>lbs.
         \<alpha>1 \<subseteq> \<Inter> s \<and>
         (\<forall>\<alpha>2\<in>lbs - s. \<alpha>1 \<inter> \<alpha>2 = {}) \<and>
         (\<forall>\<alpha>3. \<alpha>3 \<subseteq> \<Inter> s \<and> (\<forall>\<alpha>4\<in>lbs - s. \<alpha>3 \<inter> \<alpha>4 = {}) \<longrightarrow> \<alpha>3 \<subseteq> \<alpha>1))"
            by auto


      from this q2'_def 
      have "\<exists>s\<subseteq>lbs.
      \<alpha>1 \<subseteq> \<Inter> s \<and>
      (\<forall>\<alpha>'\<in>lbs - s. \<alpha>1 \<inter> \<alpha>' = {}) \<and>
      (\<forall>\<alpha>3. \<alpha>3 \<subseteq> \<Inter> s \<and> (\<forall>\<alpha>4\<in>lbs - s. \<alpha>3 \<inter> \<alpha>4 = {}) \<longrightarrow> \<alpha>3 \<subseteq> \<alpha>1)"
        by fastforce
        
      from this 
        obtain s1 where
        s1_def: "s1 \<subseteq>lbs \<and> \<alpha>1 \<subseteq> \<Inter> s1 \<and> (\<forall>\<alpha>'\<in>lbs - s1. \<alpha>1 \<inter> \<alpha>' = {})
                \<and> (\<forall>\<alpha>3. \<alpha>3 \<subseteq> \<Inter> s1 \<and> (\<forall>\<alpha>4\<in>lbs - s1. \<alpha>3 \<inter> \<alpha>4 = {}) \<longrightarrow> \<alpha>3 \<subseteq> \<alpha>1)"
          by auto
        from this have 
       s1_def': "s1 \<subseteq>lbs \<and> \<alpha>1 \<subseteq> \<Inter> s1 \<and> (\<forall>\<alpha>'\<in>lbs - s1. \<alpha>1 \<inter> \<alpha>' = {})" 
          by auto
      show "\<alpha>1 = \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {}" 
        proof (rule ccontr)
          assume p1: "\<not> (\<alpha>1 = \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {})"
          from this have \<alpha>1neq\<alpha>2: "\<alpha>1 \<noteq> \<alpha>2 \<and> \<alpha>1 \<inter> \<alpha>2 \<noteq> {}"
            by auto
          from this obtain e
            where e_def: "e \<in> \<alpha>1 \<inter> \<alpha>2" by auto
          from this s1_def'
          have e_s1: "e \<in> \<Inter> s1 \<and> (\<forall>\<alpha>'\<in>lbs - s1. {e} \<inter> \<alpha>' = {}) \<and> s1 \<subseteq>lbs"
            by auto
          from e_def s2_def'
          have e_s2: "e \<in> \<Inter> s2 \<and> (\<forall>\<alpha>'\<in>lbs - s2. {e} \<inter> \<alpha>' = {}) \<and> s2 \<subseteq>lbs"
            by auto
          from e_s1 e_s2
          have s1_eq_s2: "s1 = s2"
            by fastforce

          from s2_def
          have s2_def': 
           "\<forall>\<alpha>3. \<alpha>3 \<subseteq> \<Inter> s2 \<and> (\<forall>\<alpha>4\<in>lbs - s2. \<alpha>3 \<inter> \<alpha>4 = {}) \<longrightarrow> \<alpha>3 \<subseteq> \<alpha>2"
            by auto
          from s1_def s1_eq_s2
          have left1:"\<alpha>1 \<subseteq> \<Inter> s2 \<and> (\<forall>\<alpha>4\<in>lbs - s2. \<alpha>1 \<inter> \<alpha>4 = {})"
            by blast
          from s2_def' left1
          have sub_left: "\<alpha>1 \<subseteq> \<alpha>2"
            by blast


        from s1_def
          have s1_def': 
           "\<forall>\<alpha>3. \<alpha>3 \<subseteq> \<Inter> s1 \<and> (\<forall>\<alpha>4\<in>lbs - s1. \<alpha>3 \<inter> \<alpha>4 = {}) \<longrightarrow> \<alpha>3 \<subseteq> \<alpha>1"
            by auto
          from s2_def s1_eq_s2
          have left1:"\<alpha>2 \<subseteq> \<Inter> s1 \<and> (\<forall>\<alpha>4\<in>lbs - s1. \<alpha>2 \<inter> \<alpha>4 = {})"
            by blast
          from s1_def' left1
          have sub_right: "\<alpha>2 \<subseteq> \<alpha>1"
            by blast
        
          from \<alpha>1neq\<alpha>2 sub_right sub_left
          show "False"
            by blast
        qed
      qed
      from case1 case2 case3 case4 in_x
      show "\<alpha>1 = \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {}"
        by auto
    qed
    {
      from x_in_trans' lbs_def prem5
      show "\<forall>(q, \<alpha>1, q')\<in>\<sigma> \<union> x.
       \<exists>s\<subseteq>{uu. \<exists>q q'. (q, uu, q') \<in> TS}.
          \<alpha>1 \<subseteq> \<Inter> s \<and>
          (\<forall>\<alpha>2\<in>{uu. \<exists>q q'. (q, uu, q') \<in> TS} - s. \<alpha>1 \<inter> \<alpha>2 = {}) \<and>
          (\<forall>\<alpha>3. \<alpha>3 \<subseteq> \<Inter> s \<and> (\<forall>\<alpha>4\<in>{uu. \<exists>q q'. (q, uu, q') \<in> TS} - s. \<alpha>3 \<inter> \<alpha>4 = {}) \<longrightarrow>
                 \<alpha>3 \<subseteq> \<alpha>1)"
        by force  
    
    }
  }
qed
qed
qed
}
qed
  
  
    show "split_tran q \<alpha> q' {uu. \<exists>q q'. (q, uu, q') \<in> TS} \<bind> (\<lambda>Tran. RETURN (\<sigma> \<union> Tran))
       \<le> SPEC (\<lambda>Trans'.
                   {(q, q'). \<exists>\<alpha>. (q, \<alpha>, q') \<in> Trans'} =
                   {(qa, q'a).
                    \<exists>\<alpha>'. (qa, \<alpha>', q'a) \<in> TS \<and>
                          ((qa, \<alpha>', q'a) \<in> it \<longrightarrow> qa = q \<and> \<alpha>' = \<alpha> \<and> q'a = q')} \<and>
                   (\<forall>qa q'a.
                       \<Union> {\<alpha>. (qa, \<alpha>, q'a) \<in> Trans'} =
                       \<Union> {\<alpha>'. (qa, \<alpha>', q'a) \<in> TS \<and>
                               ((qa, \<alpha>', q'a) \<in> it \<longrightarrow> qa = q \<and> \<alpha>' = \<alpha> \<and> q'a = q')}) \<and>
                   (\<forall>x\<in>Trans'.
                       case x of
                       (q, \<alpha>1, q') \<Rightarrow>
                         \<exists>s\<subseteq>{uu. \<exists>q q'. (q, uu, q') \<in> TS}.
                            \<alpha>1 \<subseteq> \<Inter> s \<and>
                            (\<forall>\<alpha>2\<in>{uu. \<exists>q q'. (q, uu, q') \<in> TS} - s. \<alpha>1 \<inter> \<alpha>2 = {}) \<and>
                            (\<forall>\<alpha>3. \<alpha>3 \<subseteq> \<Inter> s \<and>
                                   (\<forall>\<alpha>4\<in>{uu. \<exists>q q'. (q, uu, q') \<in> TS} - s.
                                       \<alpha>3 \<inter> \<alpha>4 = {}) \<longrightarrow>
                                   \<alpha>3 \<subseteq> \<alpha>1)) \<and>
                   (\<forall>q1 \<alpha>1 q1' q2 \<alpha>2.
                       (q1, \<alpha>1, q1') \<in> Trans' \<and> (\<exists>q2'. (q2, \<alpha>2, q2') \<in> Trans') \<longrightarrow>
                       \<alpha>1 = \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {}) \<and>
                   (\<forall>x\<in>Trans'.
                       case x of
                       (q, \<alpha>, q') \<Rightarrow>
                         \<forall>\<alpha>'. (\<exists>q q'. (q, \<alpha>', q') \<in> TS) \<longrightarrow> \<alpha> \<subseteq> \<alpha>' \<or> \<alpha> \<inter> \<alpha>' = {}))"
      apply (intro refine_vcg)
      using split_tran_correct[of lbs \<alpha> q q', OF finite_lbs] SPEC1 lbs_def
            SPEC_trans
      by fastforce
  }
qed

definition NFA_uniq_trans :: "('a, 'b) NFA_rec \<Rightarrow> ('a, 'b) NFA_rec nres" 
where
  "NFA_uniq_trans \<A> = do {
   \<Delta>' \<leftarrow> split_trans (\<Delta> \<A>);
   RETURN \<lparr>
           \<Q> = \<Q> \<A>,
           \<Sigma> = \<Sigma> \<A>,
           \<Delta> = \<Delta>',
           \<I> = \<I> \<A>,
           \<F> = \<F> \<A> 
          \<rparr>
}"


lemma NFA_uniq_trans_correct:
  fixes \<A>
  assumes wf_\<A>: "NFA \<A>"
      and \<Delta>_cons: "(\<forall>(q, \<alpha>, q')\<in>\<Delta> \<A>. \<alpha> \<noteq> {}) \<and> finite (\<Delta> \<A>)"
  shows "NFA_uniq_trans \<A> \<le> 
         SPEC (\<lambda> \<A>'. NFA \<A>' \<and> uniq_label_NFA \<A>' \<and> \<L> \<A>' = \<L> \<A>
                     \<and> {(q,q')| q \<alpha> q'. (q, \<alpha>, q') \<in> \<Delta> \<A>} = 
                       {(q,q')| q \<alpha> q'. (q, \<alpha>, q') \<in> \<Delta> \<A>'}
                     \<and> (\<forall> q q'. \<Union> {\<alpha>. (q, \<alpha>, q') \<in> \<Delta> \<A>} = 
                                \<Union> {\<alpha>. (q, \<alpha>, q') \<in> \<Delta> \<A>'})
                     \<and> \<Sigma> \<A>' = \<Sigma> \<A> \<and> \<Q> \<A>' = \<Q> \<A>)"
  unfolding NFA_uniq_trans_def
  apply (intro refine_vcg)
proof -
  from \<Delta>_cons
  have finite_\<Delta>: "finite (\<Delta> \<A>)"
    by auto
  from \<Delta>_cons
  have noempty_labels: "(\<forall>(q, \<alpha>, q')\<in>\<Delta> \<A>. \<alpha> \<noteq> {})"
    by auto
  
  have SPEC_cons: 
  "SPEC (\<lambda>Trans.
            {uu. \<exists>q q' \<alpha>. uu = (q, q') \<and> (q, \<alpha>, q') \<in> Trans} =
            {uu. \<exists>q q' \<alpha>. uu = (q, q') \<and> (q, \<alpha>, q') \<in> \<Delta> \<A>} \<and>
            (\<forall>q q'. \<Union> {\<alpha>. (q, \<alpha>, q') \<in> Trans} = \<Union> {\<alpha>. (q, \<alpha>, q') \<in> \<Delta> \<A>}) \<and>
            (\<forall>q1 \<alpha>1 q1' q2 \<alpha>2 q2'.
                (q1, \<alpha>1, q1') \<in> Trans \<and> (q2, \<alpha>2, q2') \<in> Trans \<longrightarrow>
                \<alpha>1 = \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {})) \<le> 
  SPEC (\<lambda>\<Delta>'. RETURN \<lparr>\<Q> = \<Q> \<A>, \<Sigma> = \<Sigma> \<A>, \<Delta> = \<Delta>', \<I> = \<I> \<A>, \<F> = \<F> \<A>\<rparr>
                  \<le> SPEC (\<lambda>\<A>'. NFA \<A>' \<and>
                                uniq_label_NFA \<A>' \<and>
                                \<L> \<A>' = \<L> \<A> \<and>
                                {uu. \<exists>q \<alpha> q'. uu = (q, q') \<and> (q, \<alpha>, q') \<in> \<Delta> \<A>} =
                                {uu. \<exists>q \<alpha> q'. uu = (q, q') \<and> (q, \<alpha>, q') \<in> \<Delta> \<A>'} \<and>
                                (\<forall>q q'.
                                    \<Union> {\<alpha>. (q, \<alpha>, q') \<in> \<Delta> \<A>} =
                                    \<Union> {\<alpha>. (q, \<alpha>, q') \<in> \<Delta> \<A>'})\<and>
                                \<Sigma> \<A>' = \<Sigma> \<A> \<and> \<Q> \<A>' = \<Q> \<A>))"
    apply simp
    apply (rule subsetI)
    apply simp
  proof -
    fix x
    assume split_trans_cons: 
           "{(q, q'). \<exists>\<alpha>. (q, \<alpha>, q') \<in> x} = {(q, q'). \<exists>\<alpha>. (q, \<alpha>, q') \<in> \<Delta> \<A>} \<and>
            (\<forall>q q'. \<Union> {\<alpha>. (q, \<alpha>, q') \<in> x} = \<Union> {\<alpha>. (q, \<alpha>, q') \<in> \<Delta> \<A>}) \<and>
            (\<forall>q1 \<alpha>1 q1' q2 \<alpha>2.
            (q1, \<alpha>1, q1') \<in> x \<and> (\<exists>q2'. (q2, \<alpha>2, q2') \<in> x) \<longrightarrow>
            \<alpha>1 = \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {})"
    show "NFA \<lparr>\<Q> = \<Q> \<A>, \<Sigma> = \<Sigma> \<A>, \<Delta> = x, \<I> = \<I> \<A>, \<F> = \<F> \<A>\<rparr> \<and>
         uniq_label_NFA \<lparr>\<Q> = \<Q> \<A>, \<Sigma> = \<Sigma> \<A>, \<Delta> = x, \<I> = \<I> \<A>, \<F> = \<F> \<A>\<rparr> \<and>
         \<L> \<lparr>\<Q> = \<Q> \<A>, \<Sigma> = \<Sigma> \<A>, \<Delta> = x, \<I> = \<I> \<A>, \<F> = \<F> \<A>\<rparr> = \<L> \<A> \<and>
         {uu. \<exists>q \<alpha> q'. uu = (q, q') \<and> (q, \<alpha>, q') \<in> \<Delta> \<A>} =
         {uu. \<exists>q \<alpha> q'. uu = (q, q') \<and> (q, \<alpha>, q') \<in> x}"
      apply (rule conjI)
      unfolding NFA_def
      apply simp
      using split_trans_cons wf_\<A> NFA_def
       apply simp
       apply (rule_tac conjI)
      defer
      apply (rule_tac conjI)
      apply fastforce
        apply blast
       apply (rule_tac conjI)
        defer
        apply (rule_tac conjI)
      defer
      using split_trans_cons  
         apply fastforce
        defer
      defer
    proof -
      {
        show "\<forall>q \<sigma> q'. (q, \<sigma>, q') \<in> x \<longrightarrow> q \<in> \<Q> \<A> \<and> \<sigma> \<subseteq> \<Sigma> \<A> \<and> q' \<in> \<Q> \<A>"
          apply (rule allI impI)+
        proof -
          fix q \<sigma> q'
          assume in_x: "(q, \<sigma>, q') \<in> x"
          from wf_\<A> NFA_def
          have sub_\<Sigma>: "\<Union> {\<alpha>. (q, \<alpha>, q') \<in> \<Delta> \<A>} \<subseteq> \<Sigma> \<A>"
            by force
          from split_trans_cons
          have 
          \<Delta>_in_\<Q>: "{(q, q'). \<exists>\<alpha>. (q, \<alpha>, q') \<in> x} = {(q, q'). \<exists>\<alpha>. (q, \<alpha>, q') \<in> \<Delta> \<A>}" and
         label_in_\<Sigma>: "(\<forall>q q'. \<Union> {\<alpha>. (q, \<alpha>, q') \<in> x} = \<Union> {\<alpha>. (q, \<alpha>, q') \<in> \<Delta> \<A>})"
            by auto

          thm this sub_\<Sigma> in_x wf_\<A> NFA_def
          show "q \<in> \<Q> \<A> \<and> \<sigma> \<subseteq> \<Sigma> \<A> \<and> q' \<in> \<Q> \<A>"
            apply (rule conjI)
            using in_x \<Delta>_in_\<Q> wf_\<A> NFA_def[of \<A>]
            apply blast
            apply (rule conjI)
            using label_in_\<Sigma> in_x sub_\<Sigma>
            apply blast
            using in_x \<Delta>_in_\<Q> wf_\<A> NFA_def[of \<A>]
            by blast
        qed
      }
      {
        show "uniq_label_NFA \<lparr>\<Q> = \<Q> \<A>, \<Sigma> = \<Sigma> \<A>, \<Delta> = x, \<I> = \<I> \<A>, \<F> = \<F> \<A>\<rparr>"
          unfolding uniq_label_NFA_def
          apply simp
          using split_trans_cons
          by simp
      }
      {
        show "\<L> \<lparr>\<Q> = \<Q> \<A>, \<Sigma> = \<Sigma> \<A>, \<Delta> = x, \<I> = \<I> \<A>, \<F> = \<F> \<A>\<rparr> = \<L> \<A>"
          apply (simp add: set_eq_iff)
          apply (rule allI)
          apply (auto)
          using \<L>_def[of \<A>]
                \<L>_def[of "\<lparr>\<Q> = \<Q> \<A>, \<Sigma> = \<Sigma> \<A>, \<Delta> = x, \<I> = \<I> \<A>, \<F> = \<F> \<A>\<rparr>"]
          apply simp
        proof -
          {
            fix xa
            assume 
            xa_in: "NFA_accept \<lparr>\<Q> = \<Q> \<A>, \<Sigma> = \<Sigma> \<A>, \<Delta> = x, \<I> = \<I> \<A>, \<F> = \<F> \<A>\<rparr> xa"
            from this 
                 NFA_accept_def
                 [of "\<lparr>\<Q> = \<Q> \<A>, \<Sigma> = \<Sigma> \<A>, \<Delta> = x, \<I> = \<I> \<A>, \<F> = \<F> \<A>\<rparr>" xa]
            obtain q q'
            where q_q'_def: "LTS_is_reachable x q xa q' \<and> q \<in> \<I> \<A> \<and> q' \<in> \<F> \<A>"
              by auto
            from this 
            have extract_reachable: "LTS_is_reachable x q xa q'"
              by auto
            from this
            have "LTS_is_reachable (\<Delta> \<A>) q xa q'"
              apply (induction xa arbitrary: q)
              apply simp
            proof -
              {
                fix a xa q
                assume ind_hyp: "(\<And>q. LTS_is_reachable x q xa q' \<Longrightarrow> 
                                          LTS_is_reachable (\<Delta> \<A>) q xa q')"
                   and left: "LTS_is_reachable x q (a # xa) q'"
                from left LTS_is_reachable.simps(2)[of x q a xa q']
                obtain q'' \<sigma>
                  where q''_\<sigma>_def: 
                  "a \<in> \<sigma> \<and> (q, \<sigma>, q'') \<in> x \<and> LTS_is_reachable x q'' xa q'"
                  by auto

                from this ind_hyp
                have conclusion1: "LTS_is_reachable (\<Delta> \<A>) q'' xa q'"
                  by auto

                from q''_\<sigma>_def split_trans_cons
                have "\<exists> \<alpha>'. (q, \<alpha>', q'') \<in> (\<Delta> \<A>) \<and> a \<in> \<alpha>'"
                  by blast
                from this conclusion1 LTS_is_reachable.simps(2)
                show "LTS_is_reachable (\<Delta> \<A>) q (a # xa) q'"
                  by auto
              }
            qed
            from this q_q'_def NFA_accept_def
            show "NFA_accept \<A> xa"
              by auto
          }
          {
            show "\<And>xa. xa \<in> \<L> \<A> \<Longrightarrow> 
                      xa \<in> \<L> \<lparr>\<Q> = \<Q> \<A>, \<Sigma> = \<Sigma> \<A>, \<Delta> = x, \<I> = \<I> \<A>, \<F> = \<F> \<A>\<rparr>"
            proof -
              fix xa
              assume xa_in : "xa \<in> \<L> \<A>"
              from this \<L>_def[of \<A>] NFA_accept_def[of \<A> xa]
              obtain q q' where
              q_q'_def: "q \<in> \<I> \<A> \<and> q'\<in>\<F> \<A> \<and> LTS_is_reachable (\<Delta> \<A>) q xa q'"
                by blast
              from this 
              have reachable': "LTS_is_reachable (\<Delta> \<A>) q xa q'" by simp
              from this
              have "LTS_is_reachable x q xa q'"
                apply (induction xa arbitrary: q)
                apply simp
              proof -
                {
                  fix a xa q
                  assume ind_hyp: 
                          "(\<And>q. LTS_is_reachable (\<Delta> \<A>) q xa q' \<Longrightarrow> 
                                  LTS_is_reachable x q xa q')"
                     and right: "LTS_is_reachable (\<Delta> \<A>) q (a # xa) q'"
                  from right LTS_is_reachable.simps(2)
                  obtain q'' \<alpha>
                    where q''_\<alpha>_def: "a \<in> \<alpha> \<and> 
                           (q, \<alpha>, q'') \<in> (\<Delta> \<A>) \<and> 
                            LTS_is_reachable (\<Delta> \<A>)  q'' xa q'"
                    by force
                  from this split_trans_cons
                  have conclusion1: "\<exists> \<alpha>'. a \<in> \<alpha>' \<and> (q, \<alpha>', q'') \<in> x"
                    by blast
                  from q''_\<alpha>_def ind_hyp[of q'']
                  have "LTS_is_reachable x q'' xa q'"
                    by auto
                  from this conclusion1 LTS_is_reachable.simps(2)
                  show "LTS_is_reachable x q (a # xa) q'"
                    by auto
                }
              qed
              from this \<L>_def[of "\<lparr>\<Q> = \<Q> \<A>, \<Sigma> = \<Sigma> \<A>, \<Delta> = x, \<I> = \<I> \<A>, \<F> = \<F> \<A>\<rparr>"] 
                   NFA_accept_def[of "\<lparr>\<Q> = \<Q> \<A>, \<Sigma> = \<Sigma> \<A>, \<Delta> = x, \<I> = \<I> \<A>, \<F> = \<F> \<A>\<rparr>"] 
                   q_q'_def
              show "xa \<in> \<L> \<lparr>\<Q> = \<Q> \<A>, \<Sigma> = \<Sigma> \<A>, \<Delta> = x, \<I> = \<I> \<A>, \<F> = \<F> \<A>\<rparr>"
                by auto
            qed
          }
        qed
      }
    qed
  qed
  from this split_trans_correct[OF finite_\<Delta> noempty_labels]
  show "split_trans (\<Delta> \<A>)
        \<le> SPEC (\<lambda>\<Delta>'. RETURN \<lparr>\<Q> = \<Q> \<A>, \<Sigma> = \<Sigma> \<A>, \<Delta> = \<Delta>', \<I> = \<I> \<A>, \<F> = \<F> \<A>\<rparr>
                  \<le> SPEC (\<lambda>\<A>'. NFA \<A>' \<and>
                                uniq_label_NFA \<A>' \<and>
                                \<L> \<A>' = \<L> \<A> \<and>
                                {uu. \<exists>q \<alpha> q'. uu = (q, q') \<and> (q, \<alpha>, q') \<in> \<Delta> \<A>} =
                                {uu. \<exists>q \<alpha> q'. uu = (q, q') \<and> (q, \<alpha>, q') \<in> \<Delta> \<A>'} \<and>
                                (\<forall>q q'.
                                    \<Union> {\<alpha>. (q, \<alpha>, q') \<in> \<Delta> \<A>} =
                                    \<Union> {\<alpha>. (q, \<alpha>, q') \<in> \<Delta> \<A>'})\<and>
                                \<Sigma> \<A>' = \<Sigma> \<A>\<and> \<Q> \<A>' = \<Q> \<A>))"
    using SPEC_trans
    by fastforce
qed

definition label_addup :: "'q \<Rightarrow>  ('q, 'a) LTS \<Rightarrow> 'a set nres" where
  "label_addup q TS = 
   FOREACHi (\<lambda> TS' \<alpha>'. \<alpha>' = \<Union> {\<alpha>1 | \<alpha>1 q'. (q, \<alpha>1, q') \<in> TS - TS'})
   TS (\<lambda> (q1, \<alpha>, q2) S. 
            if (q = q1) then RETURN (S \<union> \<alpha>) 
                        else RETURN S) {}"

definition label_addup_gen :: "'q \<Rightarrow>  ('q, 'a) LTS \<Rightarrow> 'a set list nres" where
  "label_addup_gen q TS = 
   FOREACHi (\<lambda> TS' \<alpha>'. set \<alpha>' = {\<alpha>1 | \<alpha>1 q'. (q, \<alpha>1, q') \<in> TS - TS'})
   TS (\<lambda> (q1, \<alpha>, q2) S. 
            if (q = q1) then RETURN (\<alpha> # S) 
                        else RETURN S) []"



definition complete_trans :: "'q set \<Rightarrow> 'a set \<Rightarrow> 'q \<Rightarrow> ('q, 'a) LTS \<Rightarrow> ('q, 'a) LTS nres"  where
  "complete_trans Q L q_dead ST =
    FOREACHi
    (\<lambda> Q' NST. NST = ST \<union> 
                     {(q, \<alpha>, q_dead) | q \<alpha>.  q \<in> Q - Q' \<and> \<alpha> \<noteq> {} \<and>
                                    \<alpha> = L - \<Union> {\<alpha>' | \<alpha>' q'. (q, \<alpha>', q') \<in> ST}})
    Q
    (\<lambda> q ST'. do {
      L' \<leftarrow> label_addup q ST;
      if (L' = L) then RETURN ST' 
      else RETURN (ST' \<union> {(q, L - L', q_dead)})})
    ST"

definition complete_trans_gen :: "('a set \<Rightarrow> 'a set list \<Rightarrow> 'a set) \<Rightarrow> 
  'q set \<Rightarrow> 'a set \<Rightarrow> 'q \<Rightarrow> ('q, 'a) LTS \<Rightarrow> ('q, 'a) LTS nres"  where
  "complete_trans_gen diff Q L q_dead ST =
    FOREACHi
    (\<lambda> Q' NST. NST = ST \<union> 
                     {(q, L - \<Union> {\<alpha>' | \<alpha>' q'. (q, \<alpha>', q') \<in> ST}, q_dead) | 
                         q.  q \<in> Q - Q' \<and> L - 
                         \<Union> {\<alpha>' | \<alpha>' q'. (q, \<alpha>', q') \<in> ST} \<noteq> {}})
    Q
    (\<lambda> q ST'. do {
      L' \<leftarrow> label_addup_gen q ST;
      if ((diff L L') = {}) then RETURN ST' 
      else RETURN (ST' \<union> {(q, diff L L', q_dead)})})
    ST"

lemma complete_trans_correct:
  fixes Q L q_head ST
  assumes finite_Q: "finite Q"
      and finite_ST: "finite ST"
      and wf_L_ST: "\<forall> (q,\<alpha>,q') \<in> ST. \<alpha> \<subseteq> L"
  shows "complete_trans Q L q_dead ST \<le>
         SPEC (\<lambda> ST'. ST' = ST \<union> 
                     {(q, \<alpha>, q_dead) | q \<alpha>.  q \<in> Q \<and> \<alpha> \<noteq> {} \<and>
                       \<alpha> = L - \<Union> {\<alpha>' | \<alpha>' q'. (q, \<alpha>', q') \<in> ST}})"
  unfolding complete_trans_def label_addup_def
  apply (intro refine_vcg)
  using finite_Q apply simp
  apply simp
  using finite_ST apply simp
  apply force
  apply (rename_tac q it \<sigma> xa ita \<sigma>')
  defer
  apply blast
  defer
  apply blast  
  defer  
proof -
  {
    fix q it \<sigma> xa ita \<sigma>'
    assume xa_in_ita: "xa \<in> ita"
       and ita_sub_ST: "ita \<subseteq> ST"
       and \<sigma>'_def: "\<sigma>' = \<Union> {uu. \<exists>\<alpha>1 q'. uu = \<alpha>1 \<and> (q, \<alpha>1, q') \<in> ST - ita}"
    from this obtain q1 \<alpha> q2 where q12_\<alpha>_def: "xa = (q1, \<alpha>, q2)"
      by (meson prod_cases3)
    from this
    show "(case xa of (q1, \<alpha>, q2) \<Rightarrow> 
              \<lambda>S. if q = q1 then RETURN (S \<union> \<alpha>) else RETURN S) \<sigma>'
           \<le> 
          SPEC (\<lambda>\<alpha>'. \<alpha>' = \<Union> {uu. \<exists>\<alpha>1 q'. uu = \<alpha>1 \<and> 
                   (q, \<alpha>1, q') \<in> ST - (ita - {xa})})"
      apply simp
      apply (rule_tac conjI impI)+
       defer
      using \<sigma>'_def
      apply force
      using \<sigma>'_def xa_in_ita ita_sub_ST
      by fastforce
  }
  {
    fix x it \<sigma> \<sigma>'
    assume x_in_it: "x \<in> it"
       and it_subQ: "it \<subseteq> Q"
       and \<sigma>_def: "\<sigma> = ST \<union> {(q, \<alpha>, q_dead) |q \<alpha>.
        q \<in> Q - it \<and>
        \<alpha> \<noteq> {} \<and> \<alpha> = L - \<Union> {uu. \<exists>\<alpha>' q'. uu = \<alpha>' \<and> (q, \<alpha>', q') \<in> ST}}"
       and \<sigma>'_def: "\<sigma>' = \<Union> {uu. \<exists>\<alpha>1 q'. uu = \<alpha>1 \<and> (x, \<alpha>1, q') \<in> ST - {}}"
       and \<sigma>'neqL: "\<sigma>' \<noteq> L"

    from x_in_it it_subQ
    have set_cons: "(Q - it) \<union> {x} = Q - (it - {x})"
      by auto

    from \<sigma>'_def \<sigma>'neqL wf_L_ST
    have "L - \<sigma>' \<noteq> {}"
      by auto

    from set_cons \<sigma>_def this \<sigma>'_def
    show "\<sigma> \<union> {(x, L - \<sigma>', q_dead)} =
       ST \<union>
       {(q, \<alpha>, q_dead) |q \<alpha>.
        q \<in> Q - (it - {x}) \<and>
        \<alpha> \<noteq> {} \<and> \<alpha> = L - \<Union> {uu. \<exists>\<alpha>' q'. uu = \<alpha>' \<and> (q, \<alpha>', q') \<in> ST}}"
      by auto
  }
qed

lemma complete_trans_gen_correct:
  fixes Q L q_head ST diff
  assumes finite_Q: "finite Q"
      and finite_ST: "finite ST"
      and wf_L_ST: "\<forall> (q,\<alpha>,q') \<in> ST. \<alpha> \<subseteq> L"
      and diff_OK: "\<And> L L'. diff L L' = L - \<Union> (set L')"
  shows "complete_trans_gen diff Q L q_dead ST \<le>
         SPEC (\<lambda> ST'. ST' = ST \<union> {(q, L - \<Union> {\<alpha>' | \<alpha>' q'. (q, \<alpha>', q') \<in> ST}, 
                            q_dead) | q. q \<in> Q \<and> 
                            L - \<Union> {\<alpha>' | \<alpha>' q'. (q, \<alpha>', q') \<in> ST} \<noteq> {}})"
  unfolding complete_trans_gen_def label_addup_gen_def
  apply (intro refine_vcg)
  using finite_Q apply simp
  apply simp
  using finite_ST apply simp
  apply force
  apply (rename_tac q it \<sigma> xa ita \<sigma>')
  defer  
  using diff_OK apply force
  defer
  apply blast
proof -
  {
    fix q it \<sigma> xa ita \<sigma>'
    assume xa_in_ita: "xa \<in> ita"
       and ita_sub_ST: "ita \<subseteq> ST"
       and \<sigma>'_def: "set \<sigma>' = {uu. \<exists>\<alpha>1 q'. uu = \<alpha>1 \<and> (q, \<alpha>1, q') \<in> ST - ita}"
    from this obtain q1 \<alpha> q2 where q12_\<alpha>_def: "xa = (q1, \<alpha>, q2)"
      by (meson prod_cases3)
    from this
    show "(case xa of (q1, \<alpha>, q2) \<Rightarrow> \<lambda>S. if q = q1 then RETURN (\<alpha> # S) else RETURN S) \<sigma>'
       \<le> SPEC (\<lambda>\<alpha>'. set \<alpha>' = {uu. \<exists>\<alpha>1 q'. uu = \<alpha>1 \<and> (q, \<alpha>1, q') \<in> ST - (ita - {xa})})"
      apply simp
      apply (rule_tac conjI impI)+
       defer
      using \<sigma>'_def
      apply force
      using \<sigma>'_def xa_in_ita ita_sub_ST
      by fastforce
  }
  {
    fix x it \<sigma> \<sigma>'
    assume x_in_it: "x \<in> it"
       and it_subQ: "it \<subseteq> Q"
       and \<sigma>_def: "\<sigma> =
       ST \<union>
       {(q, L - \<Union> {uu. \<exists>\<alpha>' q'. uu = \<alpha>' \<and> (q, \<alpha>', q') \<in> ST}, q_dead) |q.
        q \<in> Q - it \<and> L - \<Union> {uu. \<exists>\<alpha>' q'. uu = \<alpha>' \<and> (q, \<alpha>', q') \<in> ST} \<noteq> {}}"
       and \<sigma>'_def: "set \<sigma>' = {uu. \<exists>\<alpha>1 q'. uu = \<alpha>1 \<and> (x, \<alpha>1, q') \<in> ST - {}}"
       and \<sigma>'neqL: "diff L \<sigma>' \<noteq> {}"

    from x_in_it it_subQ
    have set_cons: "(Q - it) \<union> {x} = Q - (it - {x})"
      by auto

    from \<sigma>'_def \<sigma>'neqL wf_L_ST
    have nempty: "diff L \<sigma>' \<noteq> {}"
      by auto
  
    from nempty set_cons \<sigma>_def this \<sigma>'_def nempty diff_OK[of L \<sigma>']
    show " \<sigma> \<union> {(x, diff L \<sigma>', q_dead)} =
       ST \<union>
       {(q, L - \<Union> {uu. \<exists>\<alpha>' q'. uu = \<alpha>' \<and> (q, \<alpha>', q') \<in> ST}, q_dead) |q.
        q \<in> Q - (it - {x}) \<and> L - \<Union> {uu. \<exists>\<alpha>' q'. uu = \<alpha>' \<and> (q, \<alpha>', q') \<in> ST} \<noteq> {}}"
      by auto
  }
qed

definition NFA_tran_complete where
    "NFA_tran_complete \<A> q = do { 
     \<Delta>' \<leftarrow> complete_trans (\<Q> \<A>) (\<Sigma> \<A>) q (\<Delta> \<A>);
     RETURN \<lparr> 
       \<Q> = \<Q> \<A> \<union> {q},
       \<Sigma> = \<Sigma> \<A>,
       \<Delta> = \<Delta>' \<union> {(q, (\<Sigma> \<A>), q)},
       \<I> = \<I> \<A>,
       \<F> = \<F> \<A>
     \<rparr>}"

lemma NFA_tran_complete_correct:
  fixes \<A> q
  assumes wf_\<A>: "NFA \<A>"
      and wf_q: "q \<notin> \<Q> \<A>"
      and finite_\<Delta>: "finite (\<Delta> \<A>)"
  shows "NFA_tran_complete \<A> q \<le>
         SPEC (\<lambda> \<A>'. NFA \<A>' \<and> \<L> \<A> = \<L> \<A>' \<and> 
                     (\<forall> q \<in> \<Q> \<A>'. \<forall> a \<in> (\<Sigma> \<A>'). \<exists> \<alpha> q'. a \<in> \<alpha> \<and> 
                      (q, \<alpha>, q') \<in> (\<Delta> \<A>')) \<and>
                      finite (\<Delta> \<A>') \<and> \<Sigma> \<A> = \<Sigma> \<A>' \<and>
                     ((\<Sigma> \<A> \<noteq> {} \<and> (\<forall> \<alpha> q q'. (q, \<alpha>, q') \<in> (\<Delta> \<A>) \<longrightarrow> \<alpha> \<noteq> {})) \<longrightarrow>
                      (\<forall> \<alpha> q q'. (q, \<alpha>, q') \<in> (\<Delta> \<A>') \<longrightarrow> \<alpha> \<noteq> {})))"
  unfolding NFA_tran_complete_def
  apply (intro refine_vcg)
  thm complete_trans_correct[of "\<Q> \<A>" "\<Delta> \<A>" "\<Sigma> \<A>" q]
proof -
  from wf_\<A> NFA_def
  have finite_\<Q>\<A>: "finite (\<Q> \<A>)"
    by auto

  from wf_\<A> NFA_def
  have label_in_\<Sigma>: "\<forall>(q, \<alpha>, q')\<in>\<Delta> \<A>. \<alpha> \<subseteq> \<Sigma> \<A> "
    by force

  

  have SPEC_sub: "SPEC (\<lambda>ST'. ST' =
               \<Delta> \<A> \<union>
               {(qa, \<alpha>, q) |qa \<alpha>.
                qa \<in> \<Q> \<A> \<and>
                \<alpha> \<noteq> {} \<and> \<alpha> = \<Sigma> \<A> - \<Union> {uu. \<exists>\<alpha>' q'. uu = \<alpha>' \<and> (qa, \<alpha>', q') \<in> \<Delta> \<A>}})
       \<le> 
         SPEC (\<lambda>\<Delta>'. RETURN
                   \<lparr>\<Q> = \<Q> \<A> \<union> {q}, \<Sigma> = \<Sigma> \<A>, \<Delta> = \<Delta>' \<union> {(q, \<Sigma> \<A>, q)}, \<I> = \<I> \<A>,
                      \<F> = \<F> \<A>\<rparr>
                  \<le> SPEC (\<lambda>\<A>'. NFA \<A>' \<and>
                                \<L> \<A> = \<L> \<A>' \<and>
                                (\<forall>q\<in>\<Q> \<A>'.
                                    \<forall>a\<in>\<Sigma> \<A>'. \<exists>\<alpha> q'. a \<in> \<alpha> \<and> (q, \<alpha>, q') \<in> \<Delta> \<A>') \<and>
                                finite (\<Delta> \<A>') \<and>
                                \<Sigma> \<A> = \<Sigma> \<A>' \<and>
                                (\<Sigma> \<A> \<noteq> {} \<and>
                                 (\<forall>\<alpha> q q'. (q, \<alpha>, q') \<in> \<Delta> \<A> \<longrightarrow> \<alpha> \<noteq> {}) \<longrightarrow>
                                 (\<forall>\<alpha> q q'. (q, \<alpha>, q') \<in> \<Delta> \<A>' \<longrightarrow> \<alpha> \<noteq> {}))))"
    apply simp
    apply (rule impI conjI)+ 
    defer
    apply (rule impI conjI)+ 
    defer 
      apply (rule_tac impI conjI)+ 
       defer
       apply (rule_tac impI conjI)+
defer
        apply (rule_tac impI conjI)+
defer
  apply (rule_tac impI conjI)+
  proof -
    {
      from wf_\<A> NFA_def[of \<A>]
      have wf1: "\<I> \<A> \<subseteq> \<Q> \<A>"
       and wf2: "\<F> \<A> \<subseteq> \<Q> \<A>"
       and wf3: "finite (\<Q> \<A>)"
       and wf4: "(\<forall>q \<sigma> q'. (q, \<sigma>, q') \<in> \<Delta> \<A> \<longrightarrow> q \<in> \<Q> \<A> \<and> \<sigma> \<subseteq> \<Sigma> \<A> \<and> q' \<in> \<Q> \<A>)"
        by auto

      
      show "NFA \<lparr>\<Q> = insert q (\<Q> \<A>), \<Sigma> = \<Sigma> \<A>,
           \<Delta> = insert (q, \<Sigma> \<A>, q)
                 (\<Delta> \<A> \<union>
                  {(qa, \<Sigma> \<A> - \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>}, q) |qa.
                   qa \<in> \<Q> \<A> \<and> \<not> \<Sigma> \<A> \<subseteq> \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>}}),
           \<I> = \<I> \<A>, \<F> = \<F> \<A>\<rparr>"
        using NFA_def[of "\<lparr>\<Q> = insert q (\<Q> \<A>), \<Sigma> = \<Sigma> \<A>,
           \<Delta> = insert (q, \<Sigma> \<A>, q)
                 (\<Delta> \<A> \<union>
                  {(qa, \<Sigma> \<A> - \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>}, q) |qa.
                   qa \<in> \<Q> \<A> \<and> \<not> \<Sigma> \<A> \<subseteq> \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>}}),
           \<I> = \<I> \<A>, \<F> = \<F> \<A>\<rparr>"]
        apply simp
      proof -
        show "(\<forall>qa \<sigma> q'.
        (qa, \<sigma>, q') \<in> \<Delta> \<A> \<longrightarrow>
        (qa = q \<or> qa \<in> \<Q> \<A>) \<and> \<sigma> \<subseteq> \<Sigma> \<A> \<and> (q' = q \<or> q' \<in> \<Q> \<A>)) \<and>
         \<I> \<A> \<subseteq> insert q (\<Q> \<A>) \<and> \<F> \<A> \<subseteq> insert q (\<Q> \<A>) \<and> finite (\<Q> \<A>)"
          apply (rule conjI)+
          defer
          apply (rule conjI)
          using wf1 apply blast
          using wf2 wf3 apply blast
          using wf4
          by force
      qed
    }
    {
      show " \<forall>a\<in>\<Sigma> \<A>.
       \<exists>\<alpha>. a \<in> \<alpha> \<and>
            (\<exists>q'. \<alpha> = \<Sigma> \<A> \<and> q' = q \<or>
                  (q, \<alpha>, q') \<in> \<Delta> \<A> \<or>
                  \<alpha> = \<Sigma> \<A> - \<Union> {uu. \<exists>q'. (q, uu, q') \<in> \<Delta> \<A>} \<and>
                  q' = q \<and> q \<in> \<Q> \<A> \<and> \<not> \<Sigma> \<A> \<subseteq> \<Union> {uu. \<exists>q'. (q, uu, q') \<in> \<Delta> \<A>})"
        by blast
    }
    {
      show "\<forall>qa\<in>\<Q> \<A>.
       \<forall>a\<in>\<Sigma> \<A>.
          \<exists>\<alpha>. a \<in> \<alpha> \<and>
               (\<exists>q'. qa = q \<and> \<alpha> = \<Sigma> \<A> \<and> q' = q \<or>
                     (qa, \<alpha>, q') \<in> \<Delta> \<A> \<or>
                     \<alpha> = \<Sigma> \<A> - \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>} \<and>
                     q' = q \<and> \<not> \<Sigma> \<A> \<subseteq> \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>})"
      proof 
        fix qa
        assume qa_\<Q>\<A>: "qa \<in> \<Q> \<A>"
        show "\<forall>a\<in>\<Sigma> \<A>.
             \<exists>\<alpha>. a \<in> \<alpha> \<and>
                  (\<exists>q'. qa = q \<and> \<alpha> = \<Sigma> \<A> \<and> q' = q \<or>
                        (qa, \<alpha>, q') \<in> \<Delta> \<A> \<or>
                        \<alpha> = \<Sigma> \<A> - \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>} \<and>
                        q' = q \<and> \<not> \<Sigma> \<A> \<subseteq> \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>})"  
        proof
          fix a
          assume a_in_\<Sigma>: "a \<in> \<Sigma> \<A>"
          from qa_\<Q>\<A> wf_q
          have "qa \<noteq> q" by auto
          from this
          show "\<exists>\<alpha>. a \<in> \<alpha> \<and>
                  (\<exists>q'. qa = q \<and> \<alpha> = \<Sigma> \<A> \<and> q' = q \<or>
                    (qa, \<alpha>, q') \<in> \<Delta> \<A> \<or>
                    \<alpha> = \<Sigma> \<A> - \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>} \<and>
                    q' = q \<and> \<not> \<Sigma> \<A> \<subseteq> \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>})"
            apply simp
          proof (cases "\<exists>q' \<alpha>. a \<in> \<alpha> \<and> (qa, \<alpha>, q') \<in> \<Delta> \<A>")
            case True
            then show "\<exists>\<alpha>. a \<in> \<alpha> \<and>
               (\<exists>q'. (qa, \<alpha>, q') \<in> \<Delta> \<A> \<or>
               \<alpha> = \<Sigma> \<A> - \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>} \<and>
               q' = q \<and> \<not> \<Sigma> \<A> \<subseteq> \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>})" 
              by auto
          next
            case False
            from this 
            have "a \<notin> \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>}"
              by blast
            from this False 
            show "\<exists>\<alpha>. a \<in> \<alpha> \<and>
               (\<exists>q'. (qa, \<alpha>, q') \<in> \<Delta> \<A> \<or>
               \<alpha> = \<Sigma> \<A> - \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>} \<and>
               q' = q \<and> \<not> \<Sigma> \<A> \<subseteq> \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>})"  
              apply simp 

              using \<open>a \<notin> \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>}\<close> a_in_\<Sigma> by blast
          qed
        qed
      qed
    }
    {
      show "\<L> \<A> =
            \<L> \<lparr>\<Q> = insert q (\<Q> \<A>), \<Sigma> = \<Sigma> \<A>,
              \<Delta> = insert (q, \<Sigma> \<A>, q)
                (\<Delta> \<A> \<union>
                 {(qa, \<Sigma> \<A> - \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>}, q) |qa.
                  qa \<in> \<Q> \<A> \<and> \<not> \<Sigma> \<A> \<subseteq> \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>}}),
            \<I> = \<I> \<A>, \<F> = \<F> \<A>\<rparr>"
        apply (rule set_eqI)
      proof
        {
          fix x 
          assume x_in_\<L>A:  "x \<in> \<L> \<A>"
          from this \<L>_def[of \<A>] NFA_accept_def[of \<A> x]
          obtain q1 q1' where
          q_q'_def: "q1 \<in> \<I> \<A> \<and> q1' \<in> \<F> \<A> \<and> LTS_is_reachable (\<Delta> \<A>) q1 x q1'"
            by auto
          let ?\<A> = "\<lparr>\<Q> = insert q (\<Q> \<A>), \<Sigma> = \<Sigma> \<A>,
                   \<Delta> = insert (q, \<Sigma> \<A>, q)
                         (\<Delta> \<A> \<union>
                          {(qa, \<Sigma> \<A> - \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>}, q) |qa.
                           qa \<in> \<Q> \<A> \<and> \<not> \<Sigma> \<A> \<subseteq> \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>}}),
                   \<I> = \<I> \<A>, \<F> = \<F> \<A>\<rparr>"
          from q_q'_def
          have "LTS_is_reachable (\<Delta> \<A>) q1 x q1'"
            by auto
          from this
          have "LTS_is_reachable (\<Delta> ?\<A>) q1 x q1'"
            apply simp
            by (meson LTS_is_reachable_subset subset_insertI sup.boundedE)
          from this q_q'_def \<L>_def[of ?\<A>] NFA_accept_def[of ?\<A> x]
          show "x \<in> \<L> ?\<A>"
            by auto
        }
        {
          let ?\<A> = "\<lparr>\<Q> = insert q (\<Q> \<A>), \<Sigma> = \<Sigma> \<A>,
                  \<Delta> = insert (q, \<Sigma> \<A>, q)
                        (\<Delta> \<A> \<union>
                         {(qa, \<Sigma> \<A> - \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>}, q) |qa.
                          qa \<in> \<Q> \<A> \<and> \<not> \<Sigma> \<A> \<subseteq> \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>}}),
                  \<I> = \<I> \<A>, \<F> = \<F> \<A>\<rparr> "
          fix x
          assume x_in_\<L>\<A>: "x \<in> \<L> ?\<A>"
          from this \<L>_def[of ?\<A>] NFA_accept_def[of ?\<A> x]
          obtain q1 q1' where
          q1_q1'_def: "q1 \<in> \<I> \<A> \<and> q1' \<in> \<F> \<A> \<and> LTS_is_reachable (\<Delta> ?\<A>) q1 x q1'"
            by auto
          from wf_q wf_\<A> NFA_def
          have "q \<notin> \<I> \<A> \<and> q \<notin> \<F> \<A>"
            by force
          thm this

          from wf_\<A> NFA_def[of \<A>]
          have q_in_QA: "\<forall> (q, \<alpha>, q') \<in> \<Delta> \<A>. q \<in> \<Q> \<A>"
            by auto

          have loop_q: "\<forall> w q'. LTS_is_reachable (\<Delta> ?\<A>) q w q' \<longrightarrow> q' = q"
            apply (rule allI impI)+
          proof -
            fix w q'
            assume reachable: "LTS_is_reachable (\<Delta> ?\<A>) q w q'"
            from this
            show "q' = q"
              apply (induction w)
               apply simp
            proof -
              fix a w
              assume ind_hyp: "(LTS_is_reachable (\<Delta> ?\<A>) q w q' \<Longrightarrow> q' = q)"
                 and   left: "LTS_is_reachable (\<Delta> ?\<A>) q (a # w) q'"
              from left LTS_is_reachable.simps(2)[of "\<Delta> ?\<A>" q a w q']
              obtain q'' \<alpha>'' where
              q\<alpha>''_def: "(q, \<alpha>'', q'') \<in> \<Delta> ?\<A> \<and> 
                          LTS_is_reachable (\<Delta> ?\<A>) q''  w q'"
                by force    

              from q\<alpha>''_def q_in_QA wf_q
              have "q'' = q"
                using Pair_inject by auto
  
              from ind_hyp this  q\<alpha>''_def
              show "q' = q"
                by auto
            qed
          qed
          from  q1_q1'_def
          have "LTS_is_reachable (\<Delta> ?\<A>) q1 x q1'"
            by simp
          from this
          have "LTS_is_reachable (\<Delta> \<A>) q1 x q1'"
            apply (induction x arbitrary: q1)
            apply simp
          proof -
            fix a x q1      
            assume ind_hyp: "\<And>q1. (LTS_is_reachable (\<Delta> ?\<A>) q1 x q1' \<Longrightarrow>
                             LTS_is_reachable (\<Delta> \<A>) q1 x q1')"
                   and right: "LTS_is_reachable (\<Delta> ?\<A>) q1 (a # x) q1'"
            from right LTS_is_reachable.simps(2)[of "\<Delta> ?\<A>"]
            obtain \<alpha>2 q2 where
            q2_\<alpha>2_def: "(q1, \<alpha>2, q2) \<in> \<Delta> (?\<A>) \<and> a \<in> \<alpha>2" and
           reachable': "LTS_is_reachable (\<Delta> ?\<A>) q2 x q1'"
              by blast

            from this loop_q q1_q1'_def
            have "q2 \<noteq> q"
              using \<open>q \<notin> \<I> \<A> \<and> q \<notin> \<F> \<A>\<close> by blast

            from this  q2_\<alpha>2_def
            have conc1: "(q1, \<alpha>2, q2) \<in> \<Delta> \<A> \<and> a \<in> \<alpha>2"
              by simp

            from reachable' ind_hyp
            have "LTS_is_reachable (\<Delta> \<A>) q2 x q1'"
              by auto
            from this conc1 LTS_is_reachable.simps(2)
            show "LTS_is_reachable (\<Delta> \<A>) q1 (a # x) q1'"
              by auto
          qed
          from this \<L>_def[of \<A>] NFA_accept_def[of \<A> x] q1_q1'_def
          show "x \<in> \<L> \<A>" by auto
        }
      qed
    }
    {
      show "\<Sigma> \<A> \<noteq> {} \<and> (\<forall>\<alpha>. (\<exists>q q'. (q, \<alpha>, q') \<in> \<Delta> \<A>) \<longrightarrow> \<alpha> \<noteq> {}) \<longrightarrow>
             (\<forall>\<alpha>. (\<exists>qa q'.
              qa = q \<and> \<alpha> = \<Sigma> \<A> \<and> q' = q \<or>
              (qa, \<alpha>, q') \<in> \<Delta> \<A> \<or>
              \<alpha> = \<Sigma> \<A> - \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>} \<and>
              q' = q \<and> qa \<in> \<Q> \<A> \<and> \<not> \<Sigma> \<A> \<subseteq> \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>}) \<longrightarrow>
          \<alpha> \<noteq> {})"
        by blast
    }{
      show "finite (\<Delta> \<A>)"
        using finite_\<Delta> by simp
    }{
      from finite_\<Delta> wf_\<A> NFA_def[of \<A>]
      show "finite
     {(qa, \<Sigma> \<A> - \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>}, q) |qa.
      qa \<in> \<Q> \<A> \<and> \<not> \<Sigma> \<A> \<subseteq> \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>}}"
        by auto
    }
  qed

  from this complete_trans_correct[of "\<Q> \<A>" "\<Delta> \<A>" "\<Sigma> \<A>" q, 
                             OF finite_\<Q>\<A> finite_\<Delta> label_in_\<Sigma>]
  show "complete_trans (\<Q> \<A>) (\<Sigma> \<A>) q (\<Delta> \<A>)
    \<le>  SPEC (\<lambda>\<Delta>'. RETURN
                   \<lparr>\<Q> = \<Q> \<A> \<union> {q}, \<Sigma> = \<Sigma> \<A>, \<Delta> = \<Delta>' \<union> {(q, \<Sigma> \<A>, q)}, \<I> = \<I> \<A>,
                      \<F> = \<F> \<A>\<rparr>
                  \<le> SPEC (\<lambda>\<A>'. NFA \<A>' \<and>
                                \<L> \<A> = \<L> \<A>' \<and>
                                (\<forall>q\<in>\<Q> \<A>'.
                                    \<forall>a\<in>\<Sigma> \<A>'. \<exists>\<alpha> q'. a \<in> \<alpha> \<and> (q, \<alpha>, q') \<in> \<Delta> \<A>') \<and>
                                finite (\<Delta> \<A>') \<and>
                                \<Sigma> \<A> = \<Sigma> \<A>' \<and>
                                (\<Sigma> \<A> \<noteq> {} \<and>
                                 (\<forall>\<alpha> q q'. (q, \<alpha>, q') \<in> \<Delta> \<A> \<longrightarrow> \<alpha> \<noteq> {}) \<longrightarrow>
                                 (\<forall>\<alpha> q q'. (q, \<alpha>, q') \<in> \<Delta> \<A>' \<longrightarrow> \<alpha> \<noteq> {}))))"
    using SPEC_trans by blast
qed

definition NFA_tran_complete_gen where
    "NFA_tran_complete_gen diff \<A> q = do { 
     \<Delta>' \<leftarrow> complete_trans_gen diff (\<Q> \<A>) (\<Sigma> \<A>) q (\<Delta> \<A>);
     RETURN \<lparr> 
       \<Q> = \<Q> \<A> \<union> {q},
       \<Sigma> = \<Sigma> \<A>,
       \<Delta> = \<Delta>' \<union> {(q, (\<Sigma> \<A>), q)},
       \<I> = \<I> \<A>,
       \<F> = \<F> \<A>
     \<rparr>}"

lemma NFA_tran_complete_gen_correct:
  fixes \<A> q diff
  assumes wf_\<A>: "NFA \<A>"
      and wf_q: "q \<notin> \<Q> \<A>"
      and finite_\<Delta>: "finite (\<Delta> \<A>)"
      and diff_cons2: "\<forall>S1 R a. diff S1 R \<subseteq> S1" 
      and diff_cons3: "\<forall>S1 R. (diff S1 R) = S1 - \<Union> (set R)"
      and diff_cons4: "\<forall>S1 R. finite (diff S1 R)"
  shows "NFA_tran_complete_gen diff \<A> q \<le>
         SPEC (\<lambda> \<A>'. NFA \<A>' \<and> \<L> \<A> = \<L> \<A>' \<and> 
                     (\<forall> q \<in> \<Q> \<A>'. \<forall> a \<in> (\<Sigma> \<A>'). \<exists> \<alpha> q'. a \<in> \<alpha> \<and> 
                      (q, \<alpha>, q') \<in> (\<Delta> \<A>')) \<and>
                      finite (\<Delta> \<A>') \<and> \<Sigma> \<A> = \<Sigma> \<A>' \<and>
                     ((\<Sigma> \<A> \<noteq> {} \<and> (\<forall> \<alpha> q q'. (q, \<alpha>, q') \<in> (\<Delta> \<A>) \<longrightarrow> \<alpha> \<noteq> {})) \<longrightarrow>
                      (\<forall> \<alpha> q q'. (q, \<alpha>, q') \<in> (\<Delta> \<A>') \<longrightarrow> \<alpha> \<noteq> {})))"
  unfolding NFA_tran_complete_gen_def
  apply (intro refine_vcg)
  thm complete_trans_gen_correct[of "\<Q> \<A>" "\<Delta> \<A>" "\<Sigma> \<A>" diff q]
proof -
  from wf_\<A> NFA_def
  have finite_\<Q>\<A>: "finite (\<Q> \<A>)"
    by auto

  from wf_\<A> NFA_def
  have label_in_\<Sigma>: "\<forall>(q, \<alpha>, q')\<in>\<Delta> \<A>. \<alpha> \<subseteq> \<Sigma> \<A> "
    by force

  have SPEC_sub: "SPEC (\<lambda>ST'. ST' =
               \<Delta> \<A> \<union>
               {(qa, \<Sigma> \<A> - \<Union> {uu. \<exists>\<alpha>' q'. uu = \<alpha>' \<and> (qa, \<alpha>', q') \<in> \<Delta> \<A>}, q) |qa.
                qa \<in> \<Q> \<A> \<and> 
                \<Sigma> \<A> - \<Union> {uu. \<exists>\<alpha>' q'. uu = \<alpha>' \<and> (qa, \<alpha>', q') \<in> \<Delta> \<A>} \<noteq> {}})
       \<le> 
         SPEC (\<lambda>\<Delta>'. RETURN
                   \<lparr>\<Q> = \<Q> \<A> \<union> {q}, \<Sigma> = \<Sigma> \<A>, \<Delta> = \<Delta>' \<union> {(q, \<Sigma> \<A>, q)}, \<I> = \<I> \<A>,
                      \<F> = \<F> \<A>\<rparr>
                  \<le> SPEC (\<lambda>\<A>'. NFA \<A>' \<and>
                                \<L> \<A> = \<L> \<A>' \<and>
                                (\<forall>q\<in>\<Q> \<A>'.
                                    \<forall>a\<in>\<Sigma> \<A>'. \<exists>\<alpha> q'. a \<in> \<alpha> \<and> (q, \<alpha>, q') \<in> \<Delta> \<A>') \<and>
                                finite (\<Delta> \<A>') \<and>
                                \<Sigma> \<A> = \<Sigma> \<A>' \<and>
                                (\<Sigma> \<A> \<noteq> {} \<and>
                                 (\<forall>\<alpha> q q'. (q, \<alpha>, q') \<in> \<Delta> \<A> \<longrightarrow> \<alpha> \<noteq> {}) \<longrightarrow>
                                 (\<forall>\<alpha> q q'. (q, \<alpha>, q') \<in> \<Delta> \<A>' \<longrightarrow> \<alpha> \<noteq> {}))))"
    apply simp
    apply (rule impI conjI)+ 
    defer
    apply (rule impI conjI)+ 
    defer 
    apply (rule_tac impI conjI)+ 
    defer
    apply (rule_tac impI conjI)+
    defer
    apply (rule_tac impI conjI)+
    defer
    apply (rule_tac impI conjI)+
  proof -
    {
      from wf_\<A> NFA_def[of \<A>]
      have wf1: "\<I> \<A> \<subseteq> \<Q> \<A>"
       and wf2: "\<F> \<A> \<subseteq> \<Q> \<A>"
       and wf3: "finite (\<Q> \<A>)"
       and wf4: "(\<forall>q \<sigma> q'. (q, \<sigma>, q') \<in> \<Delta> \<A> \<longrightarrow> q \<in> \<Q> \<A> \<and> \<sigma> \<subseteq> \<Sigma> \<A> \<and> q' \<in> \<Q> \<A>)"
        by auto

      
      show "NFA \<lparr>\<Q> = insert q (\<Q> \<A>), \<Sigma> = \<Sigma> \<A>,
           \<Delta> = insert (q, \<Sigma> \<A>, q)
                 (\<Delta> \<A> \<union>
                  {(qa, \<Sigma> \<A> - \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>}, q) |qa.
                   qa \<in> \<Q> \<A> \<and> \<not> \<Sigma> \<A> \<subseteq> \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>}}),
           \<I> = \<I> \<A>, \<F> = \<F> \<A>\<rparr>"
        using NFA_def[of "\<lparr>\<Q> = insert q (\<Q> \<A>), \<Sigma> = \<Sigma> \<A>,
           \<Delta> = insert (q, \<Sigma> \<A>, q)
                 (\<Delta> \<A> \<union>
                  {(qa, \<alpha>, q) | qa \<alpha>. qa \<in> \<Q> \<A> \<and> \<alpha> \<noteq> {} \<and>
                   \<alpha> = (\<Sigma> \<A>) - \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>}}),
           \<I> = \<I> \<A>, \<F> = \<F> \<A>\<rparr>"]
        apply simp
      proof -
        show "(\<forall>qa \<sigma> q'.
        (qa, \<sigma>, q') \<in> \<Delta> \<A> \<longrightarrow> (qa = q \<or> qa \<in> \<Q> \<A>) \<and> \<sigma> \<subseteq> \<Sigma> \<A> \<and> (q' = q \<or> q' \<in> \<Q> \<A>)) \<and>
    \<I> \<A> \<subseteq> insert q (\<Q> \<A>) \<and> \<F> \<A> \<subseteq> insert q (\<Q> \<A>) \<and> finite (\<Q> \<A>)"
          apply (rule conjI)+
          defer
          apply (rule conjI)
          using wf1 apply blast
          using wf2 wf3 apply blast
          using wf4 diff_cons2
          by force
      qed
    }
    {
      show "\<forall>a\<in>\<Sigma> \<A>.
       \<exists>\<alpha>. a \<in> \<alpha> \<and>
            (\<exists>q'. \<alpha> = \<Sigma> \<A> \<and> q' = q \<or>
                  (q, \<alpha>, q') \<in> \<Delta> \<A> \<or>
                  \<alpha> = \<Sigma> \<A> - \<Union> {uu. \<exists>q'. (q, uu, q') \<in> \<Delta> \<A>} \<and>
                  q' = q \<and> q \<in> \<Q> \<A> \<and> \<not> \<Sigma> \<A> \<subseteq> \<Union> {uu. \<exists>q'. (q, uu, q') \<in> \<Delta> \<A>})"
        by blast
    }
    {
      show "\<forall>qa\<in>\<Q> \<A>.
       \<forall>a\<in>\<Sigma> \<A>.
          \<exists>\<alpha>. a \<in> \<alpha> \<and>
               (\<exists>q'. qa = q \<and> \<alpha> = \<Sigma> \<A> \<and> q' = q \<or>
                     (qa, \<alpha>, q') \<in> \<Delta> \<A> \<or>
                     \<alpha> = \<Sigma> \<A> - \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>} \<and>
                     q' = q \<and> \<not> \<Sigma> \<A> \<subseteq> \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>})"
      proof 
        fix qa
        assume qa_\<Q>\<A>: "qa \<in> \<Q> \<A>"
        show "\<forall>a\<in>\<Sigma> \<A>.
             \<exists>\<alpha>. a \<in> \<alpha> \<and>
                  (\<exists>q'. qa = q \<and> \<alpha> = \<Sigma> \<A> \<and> q' = q \<or>
                        (qa, \<alpha>, q') \<in> \<Delta> \<A> \<or>
                        \<alpha> = \<Sigma> \<A> - \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>} \<and>
                        q' = q \<and> \<not> \<Sigma> \<A> \<subseteq> \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>})"  
        proof
          fix a
          assume a_in_\<Sigma>: "a \<in> \<Sigma> \<A>"
          from qa_\<Q>\<A> wf_q
          have "qa \<noteq> q" by auto
          from this
          show "\<exists>\<alpha>. a \<in> \<alpha> \<and>
              (\<exists>q'. qa = q \<and> \<alpha> = \<Sigma> \<A> \<and> q' = q \<or>
                    (qa, \<alpha>, q') \<in> \<Delta> \<A> \<or>
                    \<alpha> = \<Sigma> \<A> - \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>} \<and>
                    q' = q \<and> \<not> \<Sigma> \<A> \<subseteq> \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>})"
            apply simp
          proof (cases "\<exists>q' \<alpha>. a \<in> \<alpha> \<and> (qa, \<alpha>, q') \<in> \<Delta> \<A>")
            case True
            then show "\<exists>\<alpha>. a \<in> \<alpha> \<and>
         (\<exists>q'. (qa, \<alpha>, q') \<in> \<Delta> \<A> \<or>
               \<alpha> = \<Sigma> \<A> - \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>} \<and>
               q' = q \<and> \<not> \<Sigma> \<A> \<subseteq> \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>})" 
              by auto
          next
            case False
            from this 
            have "a \<notin> \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>}"
              by blast
            from this diff_cons3 a_in_\<Sigma>
            have "a \<in> (\<Sigma> \<A>) - \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>}" by auto
            from this diff_cons3
            have "\<exists> \<alpha>. a \<in> \<alpha> \<and> \<alpha> = (\<Sigma> \<A>) - \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>}"
              by (metis (no_types, lifting) Union_iff)
            from this False a_in_\<Sigma> diff_cons3
            show "\<exists>\<alpha>. a \<in> \<alpha> \<and>
         (\<exists>q'. (qa, \<alpha>, q') \<in> \<Delta> \<A> \<or>
               \<alpha> = \<Sigma> \<A> - \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>} \<and>
               q' = q \<and> \<not> \<Sigma> \<A> \<subseteq> \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>}) "  
              apply simp 
              using a_in_\<Sigma> 
              using \<open>a \<in> \<Sigma> \<A> - \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>}\<close> by blast
          qed
        qed
      qed
    }
    {
      show "\<L> \<A> =
    \<L> \<lparr>\<Q> = insert q (\<Q> \<A>), \<Sigma> = \<Sigma> \<A>,
          \<Delta> = insert (q, \<Sigma> \<A>, q)
                (\<Delta> \<A> \<union>
                 {(qa, \<Sigma> \<A> - \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>}, q) |qa.
                  qa \<in> \<Q> \<A> \<and> \<not> \<Sigma> \<A> \<subseteq> \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>}}),
          \<I> = \<I> \<A>, \<F> = \<F> \<A>\<rparr>"
        apply (rule set_eqI)
      proof
        {
          fix x 
          assume x_in_\<L>A:  "x \<in> \<L> \<A>"
          from this \<L>_def[of \<A>] NFA_accept_def[of \<A> x]
          obtain q1 q1' where
          q_q'_def: "q1 \<in> \<I> \<A> \<and> q1' \<in> \<F> \<A> \<and> LTS_is_reachable (\<Delta> \<A>) q1 x q1'"
            by auto
          let ?\<A> = "\<lparr>\<Q> = insert q (\<Q> \<A>), \<Sigma> = \<Sigma> \<A>,
                  \<Delta> = insert (q, \<Sigma> \<A>, q)
                        (\<Delta> \<A> \<union>
                         {(qa, (\<Sigma> \<A>) - \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>}, q) |qa.
                          qa \<in> \<Q> \<A> \<and> 
          \<not> \<Sigma> \<A> \<subseteq> \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>}}),
                  \<I> = \<I> \<A>, \<F> = \<F> \<A>\<rparr>"
          from q_q'_def
          have "LTS_is_reachable (\<Delta> \<A>) q1 x q1'"
            by auto
          from this
          have "LTS_is_reachable (\<Delta> ?\<A>) q1 x q1'"
            apply simp
            by (meson LTS_is_reachable_subset subset_insertI sup.boundedE)
          from this q_q'_def \<L>_def[of ?\<A>] NFA_accept_def[of ?\<A> x]
          show "x \<in> \<L> ?\<A>"
            by auto
        }
        {
          let ?\<A> = "\<lparr>\<Q> = insert q (\<Q> \<A>), \<Sigma> = \<Sigma> \<A>,
                  \<Delta> = insert (q, \<Sigma> \<A>, q)
                        (\<Delta> \<A> \<union>
                         {(qa, (\<Sigma> \<A>) - \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>}, q) |qa.
                          qa \<in> \<Q> \<A> \<and> \<not> \<Sigma> \<A> \<subseteq> \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>}}),
                  \<I> = \<I> \<A>, \<F> = \<F> \<A>\<rparr>"
          fix x
          assume x_in_\<L>\<A>: "x \<in> \<L> ?\<A>"
          from this \<L>_def[of ?\<A>] NFA_accept_def[of ?\<A> x]
          obtain q1 q1' where
          q1_q1'_def: "q1 \<in> \<I> \<A> \<and> q1' \<in> \<F> \<A> \<and> LTS_is_reachable (\<Delta> ?\<A>) q1 x q1'"
            by auto
          from wf_q wf_\<A> NFA_def
          have "q \<notin> \<I> \<A> \<and> q \<notin> \<F> \<A>"
            by force
          thm this

          from wf_\<A> NFA_def[of \<A>]
          have q_in_QA: "\<forall> (q, \<alpha>, q') \<in> \<Delta> \<A>. q \<in> \<Q> \<A>"
            by auto

          have loop_q: "\<forall> w q'. LTS_is_reachable (\<Delta> ?\<A>) q w q' \<longrightarrow> q' = q"
            apply (rule allI impI)+
          proof -
            fix w q'
            assume reachable: "LTS_is_reachable (\<Delta> ?\<A>) q w q'"
            from this
            show "q' = q"
              apply (induction w)
               apply simp
            proof -
              fix a w
              assume ind_hyp: "(LTS_is_reachable (\<Delta> ?\<A>) q w q' \<Longrightarrow> q' = q)"
                 and   left: "LTS_is_reachable (\<Delta> ?\<A>) q (a # w) q'"
              from left LTS_is_reachable.simps(2)[of "\<Delta> ?\<A>" q a w q']
              obtain q'' \<alpha>'' where
              q\<alpha>''_def: "(q, \<alpha>'', q'') \<in> \<Delta> ?\<A> \<and> 
                          LTS_is_reachable (\<Delta> ?\<A>) q''  w q'"
                by force    

              from q\<alpha>''_def q_in_QA wf_q
              have "q'' = q"
                using Pair_inject by auto
  
              from ind_hyp this  q\<alpha>''_def
              show "q' = q"
                by auto
            qed
          qed
          from  q1_q1'_def
          have "LTS_is_reachable (\<Delta> ?\<A>) q1 x q1'"
            by simp
          from this
          have "LTS_is_reachable (\<Delta> \<A>) q1 x q1'"
            apply (induction x arbitrary: q1)
            apply simp
          proof -
            fix a x q1      
            assume ind_hyp: "\<And>q1. (LTS_is_reachable (\<Delta> ?\<A>) q1 x q1' \<Longrightarrow>
                             LTS_is_reachable (\<Delta> \<A>) q1 x q1')"
                   and right: "LTS_is_reachable (\<Delta> ?\<A>) q1 (a # x) q1'"
            from right LTS_is_reachable.simps(2)[of "\<Delta> ?\<A>"]
            obtain \<alpha>2 q2 where
            q2_\<alpha>2_def: "(q1, \<alpha>2, q2) \<in> \<Delta> (?\<A>) \<and> a \<in> \<alpha>2" and
           reachable': "LTS_is_reachable (\<Delta> ?\<A>) q2 x q1'"
              by blast

            from this loop_q q1_q1'_def
            have "q2 \<noteq> q"
              using \<open>q \<notin> \<I> \<A> \<and> q \<notin> \<F> \<A>\<close> by blast

            from this  q2_\<alpha>2_def
            have conc1: "(q1, \<alpha>2, q2) \<in> \<Delta> \<A> \<and> a \<in> \<alpha>2"
              by simp

            from reachable' ind_hyp
            have "LTS_is_reachable (\<Delta> \<A>) q2 x q1'"
              by auto
            from this conc1 LTS_is_reachable.simps(2)
            show "LTS_is_reachable (\<Delta> \<A>) q1 (a # x) q1'"
              by auto
          qed
          from this \<L>_def[of \<A>] NFA_accept_def[of \<A> x] q1_q1'_def
          show "x \<in> \<L> \<A>" by auto
        }
      qed
    }
    {
      show "\<Sigma> \<A> \<noteq> {} \<and> (\<forall>\<alpha>. (\<exists>q q'. (q, \<alpha>, q') \<in> \<Delta> \<A>) \<longrightarrow> \<alpha> \<noteq> {}) \<longrightarrow>
    (\<forall>\<alpha>. (\<exists>qa q'.
              qa = q \<and> \<alpha> = \<Sigma> \<A> \<and> q' = q \<or>
              (qa, \<alpha>, q') \<in> \<Delta> \<A> \<or>
              \<alpha> = \<Sigma> \<A> - \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>} \<and>
              q' = q \<and> qa \<in> \<Q> \<A> \<and> \<not> \<Sigma> \<A> \<subseteq> \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>}) \<longrightarrow>
          \<alpha> \<noteq> {})"
        by blast
    }{
      show "finite (\<Delta> \<A>)"
        using finite_\<Delta> by simp
    }{
      from diff_cons4 diff_cons3
      have finite0: "\<forall> qa \<in> \<Q> \<A>. finite ((\<Sigma> \<A>) - \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>})"
        by (metis (no_types, lifting) Diff_empty Union_empty finite.emptyI finite_list)

      have C1: "{(qa, \<alpha>, q) |qa \<alpha>. qa \<in> \<Q> \<A> \<and> \<alpha> \<noteq> {} \<and> 
            \<alpha> = (\<Sigma> \<A>) - \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>}} = 
            \<Union> {{(qa, \<alpha>, q)| \<alpha>. \<alpha> \<noteq> {} \<and> 
            \<alpha> = (\<Sigma> \<A>) - \<Union>  {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>}} | qa. qa \<in> \<Q> \<A>}"
        by auto

      from wf_\<A> NFA_def[of \<A>] 
      have finite1: "finite {{(qa, \<alpha>, q)| \<alpha>. \<alpha> \<noteq> {} \<and> 
            \<alpha> = (\<Sigma> \<A>) - \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>}} | qa. qa \<in> \<Q> \<A>}"
        by auto

      from finite0
      have C2: "\<And> M. M \<in> {{(qa, \<alpha>, q)| \<alpha>. \<alpha> \<noteq> {} \<and> 
            \<alpha> = (\<Sigma> \<A>) - \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>}} | qa. qa \<in> \<Q> \<A>} \<Longrightarrow> 
            finite M"
        by auto

      
      from C1 C2 finite_Union[OF finite1 C2]
      show "finite
     {(qa, (\<Sigma> \<A>) - \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>}, q) |qa.
      qa \<in> \<Q> \<A> \<and> \<not> \<Sigma> \<A> \<subseteq> \<Union> {uu. \<exists>q'. (qa, uu, q') \<in> \<Delta> \<A>}}"
        by auto
    }
  qed

  from this complete_trans_gen_correct[of "\<Q> \<A>" "\<Delta> \<A>" "\<Sigma> \<A>" diff q, 
                             OF finite_\<Q>\<A> finite_\<Delta> label_in_\<Sigma> ]
       diff_cons3
  show "complete_trans_gen diff (\<Q> \<A>) (\<Sigma> \<A>) q (\<Delta> \<A>)
    \<le>  SPEC (\<lambda>\<Delta>'. RETURN
                   \<lparr>\<Q> = \<Q> \<A> \<union> {q}, \<Sigma> = \<Sigma> \<A>, \<Delta> = \<Delta>' \<union> {(q, \<Sigma> \<A>, q)}, \<I> = \<I> \<A>,
                      \<F> = \<F> \<A>\<rparr>
                  \<le> SPEC (\<lambda>\<A>'. NFA \<A>' \<and>
                                \<L> \<A> = \<L> \<A>' \<and>
                                (\<forall>q\<in>\<Q> \<A>'.
                                    \<forall>a\<in>\<Sigma> \<A>'. \<exists>\<alpha> q'. a \<in> \<alpha> \<and> (q, \<alpha>, q') \<in> \<Delta> \<A>') \<and>
                                finite (\<Delta> \<A>') \<and>
                                \<Sigma> \<A> = \<Sigma> \<A>' \<and>
                                (\<Sigma> \<A> \<noteq> {} \<and>
                                 (\<forall>\<alpha> q q'. (q, \<alpha>, q') \<in> \<Delta> \<A> \<longrightarrow> \<alpha> \<noteq> {}) \<longrightarrow>
                                 (\<forall>\<alpha> q q'. (q, \<alpha>, q') \<in> \<Delta> \<A>' \<longrightarrow> \<alpha> \<noteq> {}))))"
    using SPEC_trans by blast
qed

definition NFA_uniq_complete_trans :: 
     "('a, 'b) NFA_rec \<Rightarrow> 'a \<Rightarrow> ('a, 'b) NFA_rec nres" where
    "NFA_uniq_complete_trans \<A> q = do {
      \<A>1 \<leftarrow> NFA_tran_complete \<A> q;
      \<A>2 \<leftarrow> NFA_uniq_trans \<A>1;
      RETURN \<A>2
    }"

thm determinise_NFA_is_DFA

lemma NFA_uniq_complete_trans_correct:
   fixes \<A> q
 assumes wf_\<A>: "NFA \<A>"
     and wf_q: "q \<notin> \<Q> \<A>"
     and finite_\<Delta>: "finite (\<Delta> \<A>)" 
     and tran_nempty: "(\<forall>(q, \<alpha>, q') \<in> \<Delta> \<A>. \<alpha> \<noteq> {}) \<and> \<Sigma> \<A> \<noteq> {}"
  shows "NFA_uniq_complete_trans \<A> q \<le>
        SPEC (\<lambda> \<A>'.
                uniq_label_NFA \<A>' \<and> NFA \<A>' \<and> \<L> \<A> = \<L> \<A>' \<and>
                (\<forall>q\<in>\<Q> \<A>'. \<forall>a \<in> \<Sigma> \<A>'. \<exists>\<alpha> q'. a \<in> \<alpha> \<and> (q, \<alpha>, q') \<in> \<Delta> \<A>')
        )"
  unfolding NFA_uniq_complete_trans_def
  apply (intro refine_vcg)
proof -
  
  have "SPEC (\<lambda>\<A>'. NFA \<A>' \<and>
              \<L> \<A> = \<L> \<A>' \<and>
              (\<forall>q\<in>\<Q> \<A>'. \<forall>a\<in>\<Sigma> \<A>'. \<exists>\<alpha> q'. a \<in> \<alpha> \<and> (q, \<alpha>, q') \<in> \<Delta> \<A>') \<and>
              finite (\<Delta> \<A>') \<and>
              \<Sigma> \<A> = \<Sigma> \<A>' \<and>
              (\<Sigma> \<A> \<noteq> {} \<and> (\<forall>\<alpha> q q'. (q, \<alpha>, q') \<in> \<Delta> \<A> \<longrightarrow> \<alpha> \<noteq> {}) \<longrightarrow>
               (\<forall>\<alpha> q q'. (q, \<alpha>, q') \<in> \<Delta> \<A>' \<longrightarrow> \<alpha> \<noteq> {})))
       \<le>
       SPEC (\<lambda>\<A>1. NFA_uniq_trans \<A>1 \<bind> RETURN
                  \<le> SPEC (\<lambda>\<A>'. uniq_label_NFA \<A>' \<and>
                                NFA \<A>' \<and>
                                \<L> \<A> = \<L> \<A>' \<and>
                                (\<forall>q\<in>\<Q> \<A>'.
                                    \<forall>a\<in>\<Sigma> \<A>'. \<exists>\<alpha> q'. a \<in> \<alpha> \<and> (q, \<alpha>, q') \<in> \<Delta> \<A>')))"
    apply (intro refine_vcg)
  proof -
    fix x
    assume wf: "NFA x \<and>
         \<L> \<A> = \<L> x \<and>
         (\<forall>q\<in>\<Q> x. \<forall>a\<in>\<Sigma> x. \<exists>\<alpha> q'. a \<in> \<alpha> \<and> (q, \<alpha>, q') \<in> \<Delta> x) \<and>
         finite (\<Delta> x) \<and>
         \<Sigma> \<A> = \<Sigma> x \<and>
         (\<Sigma> \<A> \<noteq> {} \<and> (\<forall>\<alpha> q q'. (q, \<alpha>, q') \<in> \<Delta> \<A> \<longrightarrow> \<alpha> \<noteq> {}) \<longrightarrow>
          (\<forall>\<alpha> q q'. (q, \<alpha>, q') \<in> \<Delta> x \<longrightarrow> \<alpha> \<noteq> {}))"
    from wf
    have "(\<forall>q\<in>\<Q> x. \<forall>a\<in>\<Sigma> x. \<exists>\<alpha> q'. a \<in> \<alpha> \<and> (q, \<alpha>, q') \<in> \<Delta> x)" by simp
  
    from wf have wf_x: "NFA x" by simp
    from wf tran_nempty
    have \<alpha>_nempty: "(\<forall>(q, \<alpha>, q')\<in>\<Delta> x. \<alpha> \<noteq> {}) \<and> finite (\<Delta> x)" by blast
    have "SPEC (\<lambda>\<A>'. NFA \<A>' \<and>
              uniq_label_NFA \<A>' \<and>
              \<L> \<A>' = \<L> x \<and>
              {uu. \<exists>q \<alpha> q'. uu = (q, q') \<and> (q, \<alpha>, q') \<in> \<Delta> x} =
              {uu. \<exists>q \<alpha> q'. uu = (q, q') \<and> (q, \<alpha>, q') \<in> \<Delta> \<A>'} \<and>
              (\<forall>q q'. \<Union> {\<alpha>. (q, \<alpha>, q') \<in> \<Delta> x} = \<Union> {\<alpha>. (q, \<alpha>, q') \<in> \<Delta> \<A>'}) \<and>
              \<Sigma> \<A>' = \<Sigma> x \<and> \<Q> \<A>' = \<Q> x) \<le>
           SPEC (\<lambda>x. RETURN x
                      \<le> SPEC (\<lambda>\<A>'. uniq_label_NFA \<A>' \<and>
                                    NFA \<A>' \<and>
                                    \<L> \<A> = \<L> \<A>' \<and>
                                    (\<forall>q\<in>\<Q> \<A>'.
                                        \<forall>a\<in>\<Sigma> \<A>'. \<exists>\<alpha> q'. a \<in> \<alpha> \<and> (q, \<alpha>, q') \<in> \<Delta> \<A>')))"
      apply (intro refine_vcg)
      apply simp
      apply (rule_tac conjI)
      using wf apply blast
      using wf by blast
    from this NFA_uniq_trans_correct[of x, OF wf_x \<alpha>_nempty]
    show "NFA_uniq_trans x
         \<le> SPEC (\<lambda>x. RETURN x
                      \<le> SPEC (\<lambda>\<A>'. uniq_label_NFA \<A>' \<and>
                                    NFA \<A>' \<and>
                                    \<L> \<A> = \<L> \<A>' \<and>
                                    (\<forall>q\<in>\<Q> \<A>'.
                                    \<forall>a\<in>\<Sigma> \<A>'. \<exists>\<alpha> q'. a \<in> \<alpha> \<and> (q, \<alpha>, q') \<in> \<Delta> \<A>')))"
      using SPEC_trans by blast
  qed
  from this NFA_tran_complete_correct[of \<A>, OF wf_\<A> wf_q finite_\<Delta>]
  show "NFA_tran_complete \<A> q
    \<le> SPEC (\<lambda>\<A>1. NFA_uniq_trans \<A>1 \<bind> RETURN
                  \<le> SPEC (\<lambda>\<A>'. uniq_label_NFA \<A>' \<and>
                                NFA \<A>' \<and>
                                \<L> \<A> = \<L> \<A>' \<and>
                                (\<forall>q\<in>\<Q> \<A>'.
                                    \<forall>a\<in>\<Sigma> \<A>'. \<exists>\<alpha> q'. a \<in> \<alpha> \<and> (q, \<alpha>, q') \<in> \<Delta> \<A>')))"
    using SPEC_trans by blast
qed
end


