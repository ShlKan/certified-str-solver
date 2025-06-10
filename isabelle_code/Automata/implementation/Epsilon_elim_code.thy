
theory Epsilon_elim_code

imports Epsilon_Elim_Imp LTSSpec NFA_interval_Spec NFAByLTS
        RBT_LTSImpl RBT_NFAImpl Interval_imp

begin



locale epsilon_elim_interval_code = automaton_by_lts_bool_algebra_syntax
  s_ops l_ops lt_ops d_ops +
  s: StdSet s_ops (* Set operations on states *) +
  l: StdSet l_ops (* Set operations on labels *) +
  lt: StdSet lt_ops   (* Set operations on labels *) +
  d: StdLTS d_ops elem_op (* An LTS *) +
  ss: StdSet ss_ops (* Set operations on states *)  +
  ssm: StdMap m_ops 
  for s_ops::"('q::{NFA_states},'q_set,_) set_ops_scheme"
  and ss_ops::"('q \<times> 'q,'qq_set,_) set_ops_scheme"
  and l_ops::"('a ::linorder, 'a_set ,_) set_ops_scheme"
  and lt_ops::"('b, 'ai_set ,_) set_ops_scheme"
  and m_ops :: "('q, 'q_set, 'qqset_m, 'more) map_ops_scheme"
  and d_ops::"('q,'b,'a,'d,_) lts_ops_scheme"

begin

definition init_state_imp :: "'q \<Rightarrow> 'qq_set \<Rightarrow> 'q_set nres"  where
    "init_state_imp q t \<equiv>  
     FOREACH
      {p . p \<in> ss.\<alpha> t} 
      (\<lambda> (x, y) S. (if x = q then RETURN (s.ins y S) else RETURN S)) 
          (s.ins q (s.empty ()))"

lemma init_state_imp_correct:
  fixes q t' t
  assumes tt'_ok: "t = ss.\<alpha> t' \<and> ss.invar t'"
  shows "init_state_imp q t' \<le> \<Down> (br s.\<alpha> s.invar) (init_state q t)"
  unfolding init_state_imp_def
            init_state_def
  apply (refine_rcg)
  apply (subgoal_tac "inj_on id {p. p \<in> ss.\<alpha> t'}")
  apply assumption  
  apply force
  using tt'_ok
  apply force
  unfolding br_def
  apply simp
  using tt'_ok 
  apply (simp add: s.empty_correct(1) s.empty_correct(2) 
                s.ins_correct(1) s.ins_correct(2))
  apply simp  
  using s.ins_correct(1) s.ins_correct(2) by auto


definition init_closure_impl  where
    "init_closure_impl S T \<equiv> do {
       FOREACH
        {q. q \<in> s.\<alpha> S} 
        (\<lambda> q P. do { 
            onestep \<leftarrow> init_state_imp q T;
            RETURN (ssm.update q onestep P)}) (ssm.empty ())
      }"

definition map_\<alpha> where
  "map_\<alpha> = (\<lambda> m k. if ssm.\<alpha> m k = None then None 
                    else Some (s.\<alpha> (the (ssm.\<alpha> m k))))"


definition map_invar where
  "map_invar = (\<lambda> m. ssm.invar m \<and> (\<forall> k. (if ssm.\<alpha> m k = None then True 
                           else (s.invar (the (ssm.\<alpha> m k))))))"

definition map_invar_uniq where
  "map_invar_uniq q = (\<lambda> m. map_invar m \<and> dom (ssm.\<alpha> m) = {q})"

lemma init_closure_impl_correct:
  fixes S T S' T'
  assumes SS'_ok: " {q. q \<in> S'} = {q. q \<in> s.\<alpha> S}"
      and TT'_ok: "T' = ss.\<alpha> T \<and> ss.invar T"
  shows "init_closure_impl S T \<le> \<Down> (br (map_\<alpha>) (map_invar)) (init_closure S' T')"
  unfolding init_closure_impl_def init_closure_def
  apply (refine_rcg)
  apply (subgoal_tac "inj_on id {q. q \<in> s.\<alpha> S}")
  apply assumption
  apply force
  using SS'_ok apply force
  unfolding br_def map_\<alpha>_def map_invar_def
  apply simp
  using ssm.empty_correct(1) ssm.empty_correct(2) apply auto[1]
  apply (subgoal_tac "init_state_imp x T \<le> \<Down> (br s.\<alpha> s.invar) 
                            (init_state x' T')")
  apply assumption
  using init_state_imp_correct TT'_ok
  apply force
  apply simp
proof -
  fix x it \<sigma> x' it' \<sigma>' onestep onestepa
  assume p1: "ssm.invar \<sigma> \<and>
       (\<forall>k. if ssm.\<alpha> \<sigma> k = None then True else s.invar (the (ssm.\<alpha> \<sigma> k)))"
     and p2: "(onestep, onestepa) \<in> br s.\<alpha> s.invar"
  from p2 
  have onestep_eq: "onestepa = s.\<alpha> onestep \<and> s.invar onestep"
    unfolding br_def
    by auto
  from this
  show "(\<lambda>k. if ssm.\<alpha> \<sigma> k = None then None else Some (s.\<alpha> (the (ssm.\<alpha> \<sigma> k))))(x \<mapsto>
       onestepa) =
       (\<lambda>k. if ssm.\<alpha> (ssm.update x onestep \<sigma>) k = None then None
            else Some (s.\<alpha> (the (ssm.\<alpha> (ssm.update x onestep \<sigma>) k)))) \<and>
       ssm.invar (ssm.update x onestep \<sigma>) \<and>
       (\<forall>k. (\<exists>y. ssm.\<alpha> (ssm.update x onestep \<sigma>) k = Some y) \<longrightarrow>
            s.invar (the (ssm.\<alpha> (ssm.update x onestep \<sigma>) k)))"
    apply simp
    apply (rule_tac conjI)
     defer
    apply (rule_tac conjI)
    using p1 
    apply (simp add: ssm.update_correct(2))
    using p1  
    using onestep_eq ssm.correct
    using p1 by auto
qed


definition one_step_state_impl :: "'q \<Rightarrow> 'qqset_m \<Rightarrow> 'qqset_m nres" where
    "one_step_state_impl q P \<equiv> do {
       newset \<leftarrow> 
        (FOREACH {q'. q'\<in> s.\<alpha> (the (ssm.lookup q P))}
          (\<lambda> q RS. do { 
              RETURN (s.union RS (the (ssm.lookup q P)))}) 
                (the (ssm.lookup q P)));
       RETURN (ssm.sng q newset)
      }"


lemma one_step_state_impl_correct:
  fixes q P P'
  assumes PP'_ok1: "ssm.invar P \<and> dom P' = dom (ssm.\<alpha> P)"
      and PP'_ok2: "\<forall> q \<in> dom P'. s.invar (the (ssm.lookup q P)) \<and> 
                       {q'. q' \<in> the (P' q)} = {q'. q' \<in> s.\<alpha> (the (ssm.lookup q P))}"
      and qP_ok: "q \<in> dom P'"
      and dom_ok: "s.\<alpha> (the (ssm.lookup q P)) \<subseteq> dom P'"
  shows "one_step_state_impl q P \<le> \<Down> (br map_\<alpha> (map_invar_uniq q)) (one_step_state q P')"
  unfolding one_step_state_impl_def one_step_state_def
  apply (refine_rcg)
  apply (subgoal_tac "inj_on id {q'. q' \<in> s.\<alpha> (the (ssm.lookup q P))}")
  apply assumption
  apply force
  using PP'_ok2 qP_ok apply auto[1]
  apply (subgoal_tac "(the (ssm.lookup q P), the (P' q)) \<in> (br s.\<alpha> s.invar)")
  apply assumption
  unfolding br_def
  apply simp
  using PP'_ok2 qP_ok apply auto[1]
  defer
  apply simp
  unfolding map_\<alpha>_def 
  apply (rule_tac conjI)
  using map_upd_Some_unfold ssm.sng_correct(1) apply auto[1]
  unfolding map_invar_uniq_def map_invar_def
   apply simp
  using ssm.correct(3) ssm.correct(4)
  apply force
  apply simp
proof - 
  fix x it \<sigma> x' it' \<sigma>'
  assume xeq: "x' = x"
     and xin: "x \<in> it"
     and iteq: "it' = it"
     and itin: "it \<subseteq> s.\<alpha> (the (ssm.lookup q P))"
     and itin': "it \<subseteq> the (P' q)"
     and \<sigma>\<sigma>': " \<sigma>' = s.\<alpha> \<sigma>"
     and p1: "\<Union> {the (P' q') |q'. q' \<in> the (P' q) \<and> q' \<notin> it} \<union> the (P' q) = s.\<alpha> \<sigma> \<and>
       s.invar \<sigma>"
  from PP'_ok1 PP'_ok2 dom_ok
  have "the (P' x) = s.\<alpha> (the (ssm.lookup x P))"
    by (metis Collect_mem_eq insert_subset itin' 
        qP_ok subsetI subset_antisym xin)
  from this
  show "s.\<alpha> \<sigma> \<union> the (P' x) = s.\<alpha> (s.union \<sigma> (the (ssm.lookup x P))) \<and>
        s.invar (s.union \<sigma> (the (ssm.lookup x P)))"
    apply (rule_tac conjI)
    using s.correct(18)[of "\<sigma>" "the (ssm.lookup x P)"] p1 
    apply (metis PP'_ok2 dom_ok in_mono itin xin)
    by (meson PP'_ok2 dom_ok in_mono itin p1 s.union_correct(2) xin)
qed


term ssm.update
definition one_step_impl where
    "one_step_impl S P \<equiv> do {
       FOREACH {q'. q'\<in> s.\<alpha> S}
          (\<lambda> q P'. do {
              qM \<leftarrow> (one_step_state_impl q P);
              RETURN (ssm.update q (the (ssm.lookup q qM)) P')}) (ssm.empty ())
      }"

lemma one_step_impl_correct:
  fixes S S' P P'
  assumes S_ok: "{q'. q' \<in> S'} = {q'. q' \<in> s.\<alpha> S}"
      and PP'_ok1: "ssm.invar P \<and> dom P' = dom (ssm.\<alpha> P)"
      and PP'_ok2: "\<forall> q \<in> dom P'. s.invar (the (ssm.lookup q P)) \<and> 
                       {q'. q' \<in> the (P' q)} = {q'. q' \<in> s.\<alpha> (the (ssm.lookup q P))}"
      and qP_ok: "S' \<subseteq> dom P'"
      and dom_ok: "\<forall> q \<in> S'. s.\<alpha> (the (ssm.lookup q P)) \<subseteq> dom P'"
  shows "one_step_impl S P \<le> \<Down> (br map_\<alpha> map_invar) (one_step S' P')"
  unfolding one_step_impl_def one_step_def
  apply (refine_rcg)
  apply (subgoal_tac "inj_on id {q'. q' \<in> s.\<alpha> S}")
  apply assumption
  apply force
  using S_ok apply force
  using br_def map_\<alpha>_def map_invar_def
  apply simp
  apply (simp add: ssm.empty_correct(1) ssm.empty_correct(2) br_def map_\<alpha>_def map_invar_def)
   apply (subgoal_tac "one_step_state_impl x P \<le> \<Down> 
                        (br map_\<alpha> (map_invar_uniq x)) (one_step_state x' P')")
    apply assumption
  using one_step_state_impl_correct
  apply simp defer apply simp defer
proof -
  {
    fix x it \<sigma> x' it' \<sigma>'
    assume xeq: "x' = x"
       and xin: "x \<in> it"
       and iteq: "it' = it" 
       and itin: "it \<subseteq> s.\<alpha> S"
       and itin': "it \<subseteq> S'"
       and p1: "dom \<sigma>' = S' - it \<and>
       \<Union> (ran \<sigma>') \<subseteq> S' \<and>
       (\<forall>q\<in>S' - it.
           the (\<sigma>' q) = \<Union> {the (P' q') |q'. q' \<in> the (P' q)} \<union> the (P' q))"
       and p2: "(\<sigma>, \<sigma>') \<in> br map_\<alpha> map_invar"


    have c1: "x \<in> dom P'"
      using itin' qP_ok xin by blast
    have c2: "s.\<alpha> (the (ssm.lookup x P)) \<subseteq> dom P'"
        using dom_ok itin' xin by blast
    from one_step_state_impl_correct[of P P' x, OF PP'_ok1 PP'_ok2 c1 c2]
    show "one_step_state_impl x P \<le> \<Down> (br map_\<alpha> (map_invar_uniq x)) (one_step_state x P')"
      by auto
  }{
    fix x it \<sigma> x' it' \<sigma>' qM qMa
    assume xeq: "x' = x"
       and xin: "x \<in> it"
       and iteq: "it' = it"
       and itin: "it \<subseteq> s.\<alpha> S"
       and itin': "it \<subseteq> S'"
       and p1: "dom \<sigma>' = S' - it \<and>
                \<Union> (ran \<sigma>') \<subseteq> S' \<and>
                (\<forall>q\<in>S' - it.
                the (\<sigma>' q) = \<Union> {the (P' q') |q'. q' \<in> the (P' q)} \<union> the (P' q))"
       and p2: "(\<sigma>, \<sigma>') \<in> br map_\<alpha> map_invar"
       and p3: "(qM, qMa) \<in> br map_\<alpha> (map_invar_uniq x)"
    from p3
    have c1: "dom qMa = {x} \<and> ssm.invar qM"  
      unfolding br_def map_\<alpha>_def map_invar_uniq_def map_invar_def
      apply simp
      by force
    from this p3
    have c3: "s.invar (the (ssm.\<alpha> qM x)) \<and> 
              (\<forall>k. if ssm.\<alpha> qM k = None then True else s.invar (the (ssm.\<alpha> qM k)))"
      unfolding br_def map_\<alpha>_def map_invar_uniq_def map_invar_def
      apply simp
      using PP'_ok1
      by (metis domIff insertI1)
    from p3 this c1
    have c2: "the (qMa x) = s.\<alpha> (the (ssm.lookup x qM))"
      unfolding br_def map_\<alpha>_def map_invar_uniq_def
      apply simp
      by (metis domIff insertI1 ssm.lookup_correct)

    from p2
    have c4: "ssm.invar \<sigma> \<and> 
              (\<forall>k. if ssm.\<alpha> \<sigma> k = None then True else s.invar (the (ssm.\<alpha> \<sigma> k)))"
      unfolding br_def map_\<alpha>_def map_invar_def
      by simp

    from c1 c2 c3 c4
    show "(ssm.update x (the (ssm.lookup x qM)) \<sigma>, \<sigma>' ++ qMa) 
                \<in> br map_\<alpha> map_invar"
      unfolding br_def map_\<alpha>_def map_invar_def
      apply simp
      apply (rule_tac conjI)
      defer
      apply (rule_tac conjI)
      using ssm.update_correct(2) apply blast  
    proof -
      {
        assume domqMa: "dom qMa = {x} \<and> ssm.invar qM"
           and qMqMaeq: "the (qMa x) = s.\<alpha> (the (ssm.lookup x qM))"
           and invars: "s.invar (the (ssm.\<alpha> qM x)) \<and>
                        (\<forall>k. if ssm.\<alpha> qM k = None then True else 
                          s.invar (the (ssm.\<alpha> qM k)))"
           and invar\<sigma>: "ssm.invar \<sigma> \<and> 
                    (\<forall>k. if ssm.\<alpha> \<sigma> k = None then True else s.invar (the (ssm.\<alpha> \<sigma> k)))"
        show "\<forall>k. (\<exists>y. ssm.\<alpha> (ssm.update x (the (ssm.lookup x qM)) \<sigma>) k = Some y) \<longrightarrow>
                   s.invar (the (ssm.\<alpha> (ssm.update x (the (ssm.lookup x qM)) \<sigma>) k))"
          apply rule apply rule
        proof -
          fix k
          assume p1: "\<exists>y. ssm.\<alpha> (ssm.update x (the (ssm.lookup x qM)) \<sigma>) k = Some y"
          from this   
          obtain y where 
          y_def: "ssm.\<alpha> (ssm.update x (the (ssm.lookup x qM)) \<sigma>) k = Some y"
            by auto
          show "s.invar (the (ssm.\<alpha> (ssm.update x (the (ssm.lookup x qM)) \<sigma>) k))"
          proof (cases "x = k")
            case True
            then show ?thesis 
              apply simp
              using domqMa invar\<sigma> invars ssm.lookup_correct 
                    ssm.update_correct(1) by auto
            next
              case False
              from this
              have "ssm.lookup k (ssm.update x (the (ssm.lookup x qM)) \<sigma>) = 
                    ssm.lookup k \<sigma>"
                using StdMap.correct(5) invar\<sigma> ssm.StdMap_axioms 
                      ssm.update_correct(1) ssm.update_correct(2) by fastforce
              from this
              have c1: "ssm.lookup k (ssm.update x (the (ssm.lookup x qM)) \<sigma>) = 
                    (ssm.\<alpha> \<sigma>) k"
                by (simp add: invar\<sigma> ssm.lookup_correct)
              have c2: "ssm.lookup k (ssm.update x (the (ssm.lookup x qM)) \<sigma>) = 
                    (ssm.\<alpha> (ssm.update x (the (ssm.lookup x qM)) \<sigma>)) k"
                using invar\<sigma> ssm.lookup_correct ssm.update_correct(2) by blast

              

              from c1 c2 invar\<sigma>
              show ?thesis 
                apply simp
                using p1 by auto  
            qed
          qed
        }

        {
           assume domqMa: "dom qMa = {x} \<and> ssm.invar qM"
           and qMqMaeq: "the (qMa x) = s.\<alpha> (the (ssm.lookup x qM))"
           and invars: "s.invar (the (ssm.\<alpha> qM x)) \<and>
                        (\<forall>k. if ssm.\<alpha> qM k = None then True else 
                          s.invar (the (ssm.\<alpha> qM k)))"
           and invar\<sigma>: "ssm.invar \<sigma> \<and> 
                    (\<forall>k. if ssm.\<alpha> \<sigma> k = None then True else s.invar (the (ssm.\<alpha> \<sigma> k)))"
           show "\<sigma>' ++ qMa =
              (\<lambda>k. if ssm.\<alpha> (ssm.update x (the (ssm.lookup x qM)) \<sigma>) k = None then None
                else Some (s.\<alpha> (the (ssm.\<alpha> (ssm.update x (the (ssm.lookup x qM)) \<sigma>) k))))"
             apply rule
           proof -
             fix k
             from domqMa
             obtain v where v_def: "qMa x = Some v"
               by auto

             show "(\<sigma>' ++ qMa) k =
         (if ssm.\<alpha> (ssm.update x (the (ssm.lookup x qM)) \<sigma>) k = None then None
          else Some (s.\<alpha> (the (ssm.\<alpha> (ssm.update x (the (ssm.lookup x qM)) \<sigma>) k))))"
             proof (cases "x = k")
               case True
               from this v_def
               show ?thesis 
                 apply simp
                 using invar\<sigma> qMqMaeq ssm.update_correct(1) by auto
             next
               case False
               from False
               have c1: "ssm.\<alpha> (ssm.update x (the (ssm.lookup x qM)) \<sigma>) k = 
                     ssm.\<alpha> \<sigma> k"
                 using invar\<sigma> ssm.update_correct(1) by auto

               from False
               have c2: "(the (ssm.\<alpha> (ssm.update x
                           (the (ssm.lookup x qM)) \<sigma>) k)) = 
                         the (ssm.\<alpha> \<sigma> k)"
                 using c1 by auto
               from False
               have c3: "ssm.\<alpha> (ssm.update x (the (ssm.lookup x qM)) \<sigma>) k = 
                         ssm.\<alpha> \<sigma> k"
                 using c1 by blast
               from False domqMa
               have "(\<sigma>' ++ qMa) k = \<sigma>' k"
                 by auto
               from this 
               show ?thesis
                 apply simp
                 apply (rule conjI)
                 using c1
                  apply simp
                 using p2 br_def map_\<alpha>_def map_invar_def
                  apply (simp add: in_br_conv)
                 using c2 c3 
                 apply simp
                 using p2 br_def map_\<alpha>_def map_invar_def
                 by (simp add: in_br_conv)
             qed
           qed
            }
          qed
  }
qed

definition reach_closed_impl where
  "reach_closed_impl S R \<equiv> 
      s.ball S
        (\<lambda> x. s.ball (the (ssm.lookup x R)) 
                       (\<lambda> q. s.subset (the (ssm.lookup q R)) 
                            (the ((ssm.lookup x R)))))"

lemma reach_closed_impl_correct:
  fixes S S' R
  assumes SS'_OK: "S = s.\<alpha> S' \<and> s.invar S'"
      and R_OK: "dom R = S \<and> \<Union> (ran R) \<subseteq> S \<and> ssm.invar R'"
      and R'_OK: "ssm.invar R' \<and> (\<forall> q \<in> S. s.invar (the (ssm.lookup q R')))"
      and RR'_OK: "dom (ssm.\<alpha> R') = dom R \<and>
                   (\<forall>q \<in> S. s.\<alpha> (the (ssm.lookup q R')) = the (R q))" 
  shows "reach_closed_impl S' R' = (reach_closed S R)"
  unfolding reach_closed_impl_def reach_closed_def
proof 
  {
    assume p1: "s.ball S'
     (\<lambda>x. s.ball (the (ssm.lookup x R'))
           (\<lambda>q. s.subset (the (ssm.lookup q R')) (the (ssm.lookup x R'))))"
    from s.ball_correct[of S' "(\<lambda>x. s.ball (the (ssm.lookup x R'))
           (\<lambda>q. s.subset (the (ssm.lookup q R')) (the (ssm.lookup x R'))))"]
         SS'_OK p1
    have c1: "(\<forall>x\<in>S.
        s.ball (the (ssm.lookup x R'))
         (\<lambda>q. s.subset (the (ssm.lookup q R')) (the (ssm.lookup x R'))))"
      by auto
    
    show "\<forall>q\<in>S. \<forall>q'\<in>the (R q). the (R q') \<subseteq> the (R q)"
      apply auto
    proof -
      fix q q' x
      assume qin: "q \<in> S"
         and q'in: "q' \<in> the (R q)"
         and xin: "x \<in> the (R q')"

      from c1 s.ball_correct[of "the (ssm.lookup q R')"
           "(\<lambda>q1. s.subset (the (ssm.lookup q1 R')) (the (ssm.lookup q R')))"]
      have c2: "\<forall>x\<in>s.\<alpha> (the (ssm.lookup q R')).
                s.subset (the (ssm.lookup x R')) (the (ssm.lookup q R'))"
        using R'_OK qin by blast
      
      have c3: "s.\<alpha> (the (ssm.lookup q R')) = the (R q)"
        by (simp add: RR'_OK qin)

      from q'in R_OK
      obtain qr where
      qr_def: "R q = Some qr"
        using qin by blast
      from this ranI[of R q qr] R_OK
      have "q' \<in> S"
        using q'in by auto
      from this
      have c4: "s.\<alpha> (the (ssm.lookup q' R')) = the (R q')"
        by (simp add: RR'_OK)

      from c3 q'in c2
      have "s.subset (the (ssm.lookup q' R')) (the (ssm.lookup q R'))"
        by auto
      from this
      have "the (R q') \<subseteq>  the (R q)"
        using R'_OK \<open>q' \<in> S\<close> c3 c4 qin s.subset_correct by blast
      from this xin
      show "x \<in> the (R q)"
        by auto
    qed
  }
  {
    assume pre: "\<forall>q\<in>S. \<forall>q'\<in>the (R q). the (R q') \<subseteq> the (R q)"

    have "(\<forall>x\<in>s.\<alpha> S'.
    s.ball (the (ssm.lookup x R'))
     (\<lambda>q. s.subset (the (ssm.lookup q R')) (the (ssm.lookup x R'))))"
    proof
      fix x
      assume xin: "x \<in> s.\<alpha> S'"
      from this SS'_OK
      have xin': "x \<in> S" by auto

      

      have "(\<forall>xa\<in>s.\<alpha> (the (ssm.lookup x R')).
        s.subset (the (ssm.lookup xa R')) (the (ssm.lookup x R')))"
      proof 
        fix xa
        assume p1: "xa \<in> s.\<alpha> (the (ssm.lookup x R'))"

        have c3: "s.\<alpha> (the (ssm.lookup x R')) = the (R x)"
          by (simp add: RR'_OK \<open>x \<in> S\<close>)

      from xin' R_OK
      obtain qr where
      qr_def: "R x = Some qr"
        using xin' by blast
      from this ranI[of R x qr] R_OK
      have "xa \<in> S"
        using xin' 
        using c3 p1 by auto
      from this
      have c4: "s.\<alpha> (the (ssm.lookup xa R')) = the (R xa)"
        by (simp add: RR'_OK)
      from c3 c4 pre
      show "s.subset (the (ssm.lookup xa R')) (the (ssm.lookup x R'))"
        using R'_OK \<open>xa \<in> S\<close> p1 s.subset_correct xin' by auto
    qed

      from this s.ball_correct[of "the (ssm.lookup x R')" 
              "(\<lambda>q. s.subset (the (ssm.lookup q R')) (the (ssm.lookup x R')))"]
      show "s.ball (the (ssm.lookup x R'))
          (\<lambda>q. s.subset (the (ssm.lookup q R')) (the (ssm.lookup x R')))"
        using R'_OK xin' by blast
    qed
    from this s.ball_correct[of S' "(\<lambda>x. s.ball (the (ssm.lookup x R'))
           (\<lambda>q. s.subset (the (ssm.lookup q R')) (the (ssm.lookup x R'))))"]
    show "s.ball S'
     (\<lambda>x. s.ball (the (ssm.lookup x R'))
           (\<lambda>q. s.subset (the (ssm.lookup q R')) (the (ssm.lookup x R'))))"
      using SS'_OK by blast
  }
qed



definition reach_closure_impl  where
 "reach_closure_impl S T \<equiv> do {
  R \<leftarrow> init_closure_impl S T;
  WHILET 
  (\<lambda> R. \<not> (reach_closed_impl S R)) 
    (\<lambda> R. one_step_impl S R) R}"

lemma reach_closure_impl_correct:
  fixes S S' R R'
  assumes SS'_OK: "S = s.\<alpha> S' \<and> s.invar S'" 
      and RR'_OK: "R = ss.\<alpha> R' \<and> ss.invar R'"
  shows "reach_closure_impl S' R' \<le> \<Down> (br map_\<alpha> map_invar) (reach_closure_imp S R)"
  unfolding reach_closure_impl_def reach_closure_imp_def
  apply (refine_rcg)
  apply (subgoal_tac "init_closure_impl S' R' \<le> \<Down> (br map_\<alpha> map_invar) (init_closure S R)")
  apply assumption
  using init_closure_impl_correct[of S S' R R'] RR'_OK SS'_OK
  apply force
  unfolding br_def map_\<alpha>_def map_invar_def
  apply simp
proof -
  {
    fix x x'
    assume p1: "dom x' = S \<and>
       \<Union> (ran x') \<subseteq> S \<and>
       (\<forall>q\<in>S. q \<in> the (x' q) \<and>
               (\<forall>q'. (q, q') \<in> R \<longrightarrow> q' \<in> the (x' q)) \<and>
               (\<forall>q'\<in>the (x' q). epsilon_reachable q q' R))"
       and p2: "(x, x')
       \<in> {(c, a).
           a = (\<lambda>k. if ssm.\<alpha> c k = None then None else Some (s.\<alpha> (the (ssm.\<alpha> c k)))) \<and>
           ssm.invar c \<and>
           (\<forall>k. if ssm.\<alpha> c k = None then True else s.invar (the (ssm.\<alpha> c k)))}"
    from p2
    have c1: "ssm.invar x \<and> (\<forall>q\<in>S. s.invar (the (ssm.lookup q x)))" 
      apply simp
      using p1
      by (metis domIff ssm.lookup_correct)

    from p2
    have c2: "dom (ssm.\<alpha> x) = dom x' \<and> (
                  \<forall>q\<in>S. s.\<alpha> (the (ssm.lookup q x)) = the (x' q))"
      apply simp
      apply (rule_tac conjI)
      using p1
proof -
  assume a1: "x' = (\<lambda>k. if ssm.\<alpha> x k = None then None else Some (s.\<alpha> (the (ssm.\<alpha> x k)))) \<and> ssm.invar x \<and> (\<forall>k. if ssm.\<alpha> x k = None then True else s.invar (the (ssm.\<alpha> x k)))"
  have f2: "{q. x' q \<noteq> None} = S"
    using p1 by fastforce
then have "{q. ssm.\<alpha> x q \<noteq> None} = S"
  using a1 by force
then show "dom (ssm.\<alpha> x) = dom (\<lambda>q. if ssm.\<alpha> x q = None then None else Some (s.\<alpha> (the (ssm.\<alpha> x q))))"
using f2 a1 by blast
next
  assume p1': "x' = (\<lambda>k. if ssm.\<alpha> x k = None then None else Some (s.\<alpha> (the (ssm.\<alpha> x k)))) \<and>
    ssm.invar x \<and>
    (\<forall>k. if ssm.\<alpha> x k = None then True else s.invar (the (ssm.\<alpha> x k)))"
  show "\<forall>q\<in>S. (ssm.\<alpha> x q = None \<longrightarrow> s.\<alpha> (the (ssm.lookup q x)) = the None) \<and>
           ((\<exists>y. ssm.\<alpha> x q = Some y) \<longrightarrow>
            s.\<alpha> (the (ssm.lookup q x)) = s.\<alpha> (the (ssm.\<alpha> x q)))"
  proof
    fix q
    assume qin: "q \<in> S"
    from p1 p1' 
    have dom_neq: "dom x' = dom (ssm.\<alpha> x)"
      unfolding dom_def
      by force

    from this qin p1 ssm.correct
    have "ssm.\<alpha> x q \<noteq> None"
      by auto
    from this
    show "(ssm.\<alpha> x q = None \<longrightarrow> s.\<alpha> (the (ssm.lookup q x)) = the None) \<and>
         ((\<exists>y. ssm.\<alpha> x q = Some y) \<longrightarrow>
          s.\<alpha> (the (ssm.lookup q x)) = s.\<alpha> (the (ssm.\<alpha> x q)))"
      apply (rule_tac conjI)
      apply force
      using p1 p1' 
      by (simp add: ssm.lookup_correct)
  qed
qed
  from  c1 c2 reach_closed_impl_correct[of S S' x' x ] p1
    show "(\<not> reach_closed_impl S' x) = (\<not> reach_closed S x')"
      using SS'_OK by linarith
  }

  {
    fix x x'
    assume p1: "(x, x')
       \<in> {(c, a).
           a = (\<lambda>k. if ssm.\<alpha> c k = None then None else Some (s.\<alpha> (the (ssm.\<alpha> c k)))) \<and>
           ssm.invar c \<and>
           (\<forall>k. if ssm.\<alpha> c k = None then True else s.invar (the (ssm.\<alpha> c k)))}"
       and p2: "dom x' = S \<and>
       \<Union> (ran x') \<subseteq> S \<and>
       (\<forall>q\<in>S. q \<in> the (x' q) \<and>
               (\<forall>q'. (q, q') \<in> R \<longrightarrow> q' \<in> the (x' q)) \<and>
               (\<forall>q'\<in>the (x' q). epsilon_reachable q q' R))"
    from p1
    have c1: "ssm.invar x \<and> dom x' = dom (ssm.\<alpha> x)"
      apply simp
      using domIff by fastforce

    from p1 this
    have c2: "\<forall>q\<in>dom x'.
   s.invar (the (ssm.lookup q x)) \<and>
   {q'. q' \<in> the (x' q)} = {q'. q' \<in> s.\<alpha> (the (ssm.lookup q x))}"
      apply simp
      using ssm.lookup_correct by auto

    from p2
    have c3: "S \<subseteq> dom x'" by auto

    from p2 p1
    have c4: "\<forall>q\<in>S. s.\<alpha> (the (ssm.lookup q x)) \<subseteq> dom x'"
      apply simp
      by (metis (no_types, lifting) Sup_upper domIff 
                dual_order.trans ranI ssm.lookup_correct)
    from c1 c2 c3 c4 one_step_impl_correct[of S S' x x']
    show "one_step_impl S' x
       \<le> \<Down> {(c, a).
             a =
             (\<lambda>k. if ssm.\<alpha> c k = None then None else Some (s.\<alpha> (the (ssm.\<alpha> c k)))) \<and>
             ssm.invar c \<and>
             (\<forall>k. if ssm.\<alpha> c k = None then True else s.invar (the (ssm.\<alpha> c k)))}
           (one_step S x')"
      unfolding br_def map_\<alpha>_def map_invar_def
      using SS'_OK by blast
  }
qed

definition compute_ep_I_imp where 
     "compute_ep_I_imp I P = 
      FOREACH {q. q \<in> s.\<alpha> I} 
           (\<lambda> q NI. if ssm.lookup q P = None then RETURN NI else
                    RETURN (s.union NI (the (ssm.lookup q P)))
      ) (s.empty ())"

lemma compute_eq_I_imp_correct:
  fixes I P I' P'
  assumes II'_ok: "I' = s.\<alpha> I \<and> s.invar I"
      and P_ok: "ssm.invar P \<and> (\<forall> q \<in> dom P'. s.invar (the (ssm.lookup q P)))"
      and PP'_ok: "dom P' = dom (ssm.\<alpha> P) \<and> 
                          (\<forall> q \<in> dom P'. s.\<alpha> (the (ssm.lookup q P)) = the (P' q))"
  shows "compute_ep_I_imp I P \<le> \<Down> (br s.\<alpha> s.invar)(compute_ep_I I' P')"
  unfolding compute_ep_I_imp_def compute_ep_I_def
  apply (refine_rcg)
  apply (subgoal_tac "inj_on id {q. q \<in> s.\<alpha> I}")
  apply assumption
  apply force
  using II'_ok
  apply force
  unfolding br_def
  apply simp
  using s.empty_correct(1) s.empty_correct(2) apply blast
  apply simp
  using P_ok PP'_ok ssm.correct
  apply (metis domIff)
  apply simp
  using P_ok PP'_ok ssm.correct
  by (metis (no_types, lifting) domI s.union_correct(1) s.union_correct(2))


definition compute_ep_F_imp where 
     "compute_ep_F_imp F Q P = 
      FOREACH {q. q \<in> s.\<alpha> F} (\<lambda> q NI. do {
            TI \<leftarrow> (FOREACH
                    {q. q \<in> s.\<alpha> Q} (\<lambda> q' NII. 
                        if s.memb q (the (ssm.lookup q' P)) 
                        then RETURN (s.ins q' NII) 
                        else RETURN NII) (s.empty ()));
            RETURN (s.union TI NI)
          }
      ) (s.empty ())"


lemma compute_eq_F_imp_correct:
  fixes Q P Q' P' F F'
  assumes QQ'_ok: "Q' = s.\<alpha> Q \<and> s.invar Q"
      and FF'_ok: "F' = s.\<alpha> F \<and> s.invar F"
      and P_ok: "ssm.invar P \<and> (\<forall> q \<in> dom P'. s.invar (the (ssm.lookup q P)))"
      and PP'_ok: "dom P' = dom (ssm.\<alpha> P) \<and> Q' \<subseteq> dom P' \<and>
                          (\<forall> q \<in> dom P'. s.\<alpha> (the (ssm.lookup q P)) = the (P' q))"
  shows "compute_ep_F_imp F Q P \<le> \<Down> (br s.\<alpha> s.invar)(compute_ep_F F' Q' P')"
  unfolding compute_ep_F_imp_def compute_ep_F_def
  apply (refine_rcg)
  apply (subgoal_tac "inj_on id {q. q \<in> s.\<alpha> F}")
  apply assumption
  apply force
  using FF'_ok apply force
  unfolding br_def
  apply simp
  using s.empty_correct(1) s.empty_correct(2) apply blast
  apply (subgoal_tac "inj_on id {q. q \<in> s.\<alpha> Q}")
  apply assumption
  apply force
  using QQ'_ok apply force
  apply (subgoal_tac "(s.empty (), {}) \<in> (br s.\<alpha> s.invar)")
  apply assumption
  unfolding br_def
  apply simp
  apply (simp add: s.empty_correct(1) s.empty_correct(2))
    apply simp 
  
  apply (metis (no_types, lifting) PP'_ok P_ok in_mono s.memb_correct)
  apply simp
  apply (simp add: s.ins_correct(1) s.ins_correct(2))
  apply simp
  by (simp add: s.union_correct(1) s.union_correct(2))



definition compute_ep_Trans_imp where 
     "compute_ep_Trans_imp Tran Q P = 
      FOREACH
         {t. t \<in> d.\<alpha> Tran} (\<lambda> (q, \<alpha>, q') NI. do {
            TI \<leftarrow> (FOREACH 
                  {q. q \<in> s.\<alpha> Q} (\<lambda> q'' NII. 
                        if s.memb q (the (ssm.lookup q'' P)) then 
                               RETURN (d.add q'' \<alpha> q' NII) 
                        else RETURN NII) (d.empty));
            RETURN (d.union TI NI)
          }
      ) d.empty"


lemma compute_ep_Trans_imp_correct:
  assumes Tran_ok: "Tran' =  ba_to_set ` {t. t \<in> d.\<alpha> Tran}"
      and Tran_ok': "\<forall> (q, \<alpha>, q') \<in> {t. t \<in> d.\<alpha> Tran}. canonical_op \<alpha>"
      and QQ'_ok: "Q' = s.\<alpha> Q"
      and P_ok: "ssm.invar P \<and> (\<forall> q \<in> dom P'. s.invar (the (ssm.lookup q P)))"
      and PP'_ok: "dom P' = dom (ssm.\<alpha> P) \<and> Q' \<subseteq> dom P' \<and>
                          (\<forall> q \<in> dom P'. s.\<alpha> (the (ssm.lookup q P)) = the (P' q))"
    shows "compute_ep_Trans_imp Tran Q P \<le> \<Down> (br (\<lambda> d. ba_to_set ` (d.\<alpha> d)) 
            d.invar)
         (compute_ep_Trans Tran' Q' P')"
  unfolding compute_ep_Trans_imp_def compute_ep_Trans_def
  apply (refine_rcg)
  apply (subgoal_tac "inj_on ba_to_set {t. t \<in> d.\<alpha> Tran}")
  apply assumption
  using inj_on_def ba_to_set.simps
  apply (smt Pair_inject Tran_ok' case_prodE iv.inj_semIs_aux ba_to_set.simps)
  using Tran_ok apply force
  apply (simp add: br_def d.lts_empty_correct(1) d.lts_empty_correct(2))
  apply (subgoal_tac "inj_on id {q. q \<in> s.\<alpha> Q}")
  apply assumption
  apply force
  using QQ'_ok apply force
  apply (subgoal_tac "(d.empty, {}) \<in> (br (\<lambda> d. ba_to_set ` (d.\<alpha> d)) d.invar)")
  apply assumption
  apply simp
  apply (simp add: br_def d.lts_empty_correct(1) d.lts_empty_correct(2))
  using PP'_ok P_ok br_def 
  apply (simp add: PP'_ok s.memb_correct subsetD)
  apply simp
  apply (simp add: br_def d.lts_add_correct(1) d.lts_add_correct(2))
  apply simp
  unfolding br_def
  apply simp
  by (simp add: d.lts_union_correct(1) d.lts_union_correct(2) image_Un)
 



definition nfae_states :: "'q_set \<times>  'd \<times> 'qq_set\<times> 'q_set \<times> 'q_set \<Rightarrow> 'q_set" where
  "nfae_states A = fst A"
lemma [simp]: "nfae_states (Q,  D, D', I, F) = Q" by (simp add: nfae_states_def)


definition nfae_trans :: 
        "'q_set \<times> 'd \<times> 'qq_set \<times> 'q_set \<times> 'q_set \<Rightarrow> 'd" where
  "nfae_trans A = (fst (snd A))"
lemma [simp]: "nfae_trans (Q, D, D', I, F) = D" by (simp add: nfae_trans_def)

definition nfae_trans_ep :: 
        "'q_set \<times> 'd \<times> 'qq_set \<times> 'q_set \<times> 'q_set \<Rightarrow> 'qq_set" where
  "nfae_trans_ep A = (fst(snd (snd A)))"
lemma [simp]: "nfae_trans_ep (Q, D, D', I, F) = D'" by (simp add: nfae_trans_ep_def)

definition nfae_initial :: "'q_set \<times> 'd \<times> 'qq_set \<times> 'q_set \<times> 'q_set \<Rightarrow> 'q_set" where
  "nfae_initial A = fst (snd (snd  (snd A)))"
lemma [simp]: "nfae_initial (Q, D, D', I, F) = I" by (simp add: nfae_initial_def)

definition nfae_accepting :: "'q_set \<times>  'd \<times> 'qq_set \<times> 'q_set \<times> 'q_set \<Rightarrow> 'q_set" where
  "nfae_accepting A = snd (snd (snd (snd A)))"
lemma [simp]: "nfae_accepting (Q, D, D', I, F) = F" by (simp add: nfae_accepting_def)


definition nfae_invar :: "'q_set \<times> 'd \<times> 'qq_set \<times> 'q_set \<times> 'q_set \<Rightarrow> bool" where
  "nfae_invar A =
   (s.invar (nfae_states A) \<and> 
    d.invar (nfae_trans A) \<and>
    ss.invar (nfae_trans_ep A) \<and>
    s.invar (nfae_initial A) \<and> 
    s.invar (nfae_accepting A))"


definition nfae_\<alpha> :: "'q_set \<times>  'd \<times> 'qq_set \<times> 'q_set \<times> 'q_set
                           \<Rightarrow> ('q, 'a) NFAe_rec" 
  where
  "nfae_\<alpha> A =
   \<lparr> \<Q>e = s.\<alpha> (nfae_states A),   
     \<Delta>e = ba_to_set ` (d.\<alpha> (nfae_trans A)),
     \<Delta>e' = ss.\<alpha> (nfae_trans_ep A),
     \<I>e = s.\<alpha> (nfae_initial A), 
     \<F>e = s.\<alpha> (nfae_accepting A) \<rparr>"

definition NFA_elim_imp  where 
     "NFA_elim_imp A = do {
       P \<leftarrow> reach_closure_impl (nfae_states A) (nfae_trans_ep A);
       N\<Delta> \<leftarrow> (compute_ep_Trans_imp (nfae_trans A) (nfae_states A) P);
       N\<I> \<leftarrow>  compute_ep_I_imp (nfae_initial A) P;
       N\<F> \<leftarrow>  compute_ep_F_imp (nfae_accepting A) (nfae_states A) P;
       RETURN (nfae_states A, 
               d.union (nfae_trans A)  N\<Delta>, 
               s.union (nfae_initial A) N\<I>, 
               s.union (nfae_accepting A) N\<F>)
     }"

lemma NFA_elim_imp_correct:
  fixes \<A> \<A>'
  assumes state_ok: "\<Q>e \<A>' = s.\<alpha> (nfae_states \<A>) \<and> s.invar (nfae_states \<A>)" 
      and trans_ok: "\<Delta>e' \<A>' = ss.\<alpha> (nfae_trans_ep \<A>) \<and> ss.invar (nfae_trans_ep \<A>)"
      and trans_ok': "\<Delta>e \<A>' = ba_to_set ` {t. t \<in> d.\<alpha> (nfae_trans \<A>)} \<and>
                      d.invar (nfae_trans \<A>) \<and> 
                      (\<forall>(q, \<alpha>, q')\<in>{t. t \<in> d.\<alpha> (nfae_trans \<A>)}. canonical_op \<alpha>)"
      and initial_ok: "\<I>e \<A>' = s.\<alpha> (nfae_initial \<A>) \<and> s.invar (nfae_initial \<A>)"
      and accepting_ok: "\<F>e \<A>' = s.\<alpha> (nfae_accepting \<A>) \<and> s.invar (nfae_accepting \<A>)"
      and wf_\<A>': "NFAe \<A>' \<and> finite (\<Delta>e' \<A>')"
  shows "NFA_elim_imp \<A> \<le> \<Down> (br nfa_\<alpha> nfa_invar) (NFA_elim_Impl \<A>')"
  unfolding NFA_elim_imp_def NFA_elim_Impl_def
  apply refine_rcg
  apply (subgoal_tac "reach_closure_impl (nfae_states \<A>) (nfae_trans_ep \<A>)
              \<le> \<Down> (br map_\<alpha> (\<lambda> m. map_invar m \<and> dom (ssm.\<alpha> m) = (\<Q>e \<A>'))) 
                            (reach_closure_imp (\<Q>e \<A>') (\<Delta>e' \<A>'))")
       apply assumption 
      defer
  apply (subgoal_tac "compute_ep_Trans_imp (nfae_trans \<A>) (nfae_states \<A>) P
                        \<le> \<Down> ((br (\<lambda>d. ba_to_set ` d.\<alpha> d) d.invar)) 
                     (compute_ep_Trans (\<Delta>e \<A>') (\<Q>e \<A>') Pa)")
       apply assumption
  defer
  apply (subgoal_tac "compute_ep_I_imp (nfae_initial \<A>) P
       \<le> \<Down> (br s.\<alpha> s.invar) (compute_ep_I (\<I>e \<A>') Pa)")
  apply assumption
  defer
  apply (subgoal_tac "compute_ep_F_imp (nfae_accepting \<A>) (nfae_states \<A>) P
       \<le> \<Down> (br s.\<alpha> s.invar) (compute_ep_F (\<F>e \<A>') (\<Q>e \<A>') Pa)")
  apply assumption
  
proof -
  {
    fix P Pa
    assume p1: "(P, Pa) \<in> br map_\<alpha> (\<lambda>m. map_invar m \<and> dom (ssm.\<alpha> m) = \<Q>e \<A>')"
    show "compute_ep_F_imp (nfae_accepting \<A>) (nfae_states \<A>) P
       \<le> \<Down> (br s.\<alpha> s.invar) (compute_ep_F (\<F>e \<A>') (\<Q>e \<A>') Pa)"
      apply (rule compute_eq_F_imp_correct)
      using state_ok apply force
      using accepting_ok apply force
      using p1 unfolding br_def
      apply simp
      apply (metis domIff map_\<alpha>_def map_invar_def ssm.lookup_correct)
      using p1 unfolding br_def
      apply simp
      apply (rule conjI)
      defer
      unfolding map_\<alpha>_def map_invar_def
      apply (metis (no_types, lifting) domI domIff option.sel 
      ssm.lookup_correct subsetI)
      unfolding map_\<alpha>_def dom_def
      by auto
  }
  {
    fix P Pa N\<Delta> N\<Delta>'
    assume p1: "(P, Pa) \<in> br map_\<alpha> (\<lambda>m. map_invar m \<and> dom (ssm.\<alpha> m) = \<Q>e \<A>')"
    show "compute_ep_I_imp (nfae_initial \<A>) P
         \<le> \<Down> (br s.\<alpha> s.invar) (compute_ep_I (\<I>e \<A>') Pa)"
      apply (rule compute_eq_I_imp_correct[of "\<I>e \<A>'" "nfae_initial \<A>" P Pa])
      using initial_ok apply simp
      using p1 unfolding br_def
      apply simp
      unfolding map_\<alpha>_def map_invar_def
      apply (metis domIff ssm.lookup_correct)
      using p1 unfolding br_def
      apply simp
      unfolding map_\<alpha>_def 
      apply (rule_tac conjI)
       defer
      using map_invar_def ssm.lookup_correct apply auto[1]
      apply (subgoal_tac "dom (\<lambda>k. if ssm.\<alpha> P k = None then None else 
                           Some (s.\<alpha> (the (ssm.\<alpha> P k)))) = dom (ssm.\<alpha> P)")
      apply force
      unfolding dom_def
      by simp
  }
  {
    show "reach_closure_impl (nfae_states \<A>) (nfae_trans_ep \<A>)
    \<le> \<Down> (br map_\<alpha> (\<lambda>m. map_invar m \<and> dom (ssm.\<alpha> m) = \<Q>e \<A>'))
        (reach_closure_imp (\<Q>e \<A>') (\<Delta>e' \<A>'))"
      unfolding br_def
    proof -
      from reach_closure_impl_correct[of "\<Q>e \<A>'" "nfae_states \<A>" "\<Delta>e' \<A>'" 
                                       "nfae_trans_ep \<A>"] state_ok trans_ok
      have rc_correct: "reach_closure_impl (nfae_states \<A>) (nfae_trans_ep \<A>)
                        \<le> \<Down> (br map_\<alpha> map_invar) (reach_closure_imp (\<Q>e \<A>') (\<Delta>e' \<A>'))"
        by auto
      from this
      show "reach_closure_impl (nfae_states \<A>) (nfae_trans_ep \<A>)
              \<le> \<Down> {(c, a). a = map_\<alpha> c \<and> map_invar c \<and> dom (ssm.\<alpha> c) = \<Q>e \<A>'}
                  (reach_closure_imp (\<Q>e \<A>') (\<Delta>e' \<A>'))"
      proof (cases "reach_closure_impl (nfae_states \<A>) (nfae_trans_ep \<A>) = FAILi")
        case True
        then show ?thesis 
            apply simp 
          using rc_correct by auto
      next
        case False
        from this obtain rci where
        rci_def: "reach_closure_impl (nfae_states \<A>) (nfae_trans_ep \<A>) = RES rci"
          using nres.exhaust by auto
        from this 
        show ?thesis 
        proof (cases "reach_closure_imp (\<Q>e \<A>') (\<Delta>e' \<A>') = FAILi")
          case True
          from this rci_def rc_correct
          have "(RES rci) \<le> \<Down> (br map_\<alpha> map_invar) FAILi"
            by simp
          from rci_def True
          show ?thesis 
            by simp
        next
          case False
          from this
          obtain rc where 
          rc_def: "reach_closure_imp (\<Q>e \<A>') (\<Delta>e' \<A>') = RES rc"
            using nres.exhaust by auto
          from rc_def rci_def rc_correct
          have c1: "RES rci \<le> \<Down> (br map_\<alpha> map_invar) (RES rc)"
            by simp

          from this 
          have c2: "rci \<subseteq> {c. map_\<alpha> c \<in> rc \<and> map_invar c}"
            unfolding conc_fun_def br_def
            by simp
          
          show ?thesis
            apply (simp add: c1 rc_def rci_def)
            unfolding conc_fun_def
            apply simp
          proof
            fix x
            assume xin: "x \<in> rci"
            from c2 this
            have c2': "map_\<alpha> x \<in> rc \<and> map_invar x" by auto
            from reach_closure_imp_correct[of "\<Q>e \<A>'" "\<Delta>e' \<A>'"] 
                wf_\<A>'
            have "reach_closure_imp (\<Q>e \<A>') (\<Delta>e' \<A>')
                    \<le> SPEC (\<lambda>P. \<forall>q q'. dom P = \<Q>e \<A>' \<and>
                        \<Union> (ran P) \<subseteq> \<Q>e \<A>' \<and>
                        (q \<in> \<Q>e \<A>' \<longrightarrow>
                         epsilon_reachable q q' (\<Delta>e' \<A>') = (q' \<in> the (P q))))"
              unfolding NFAe_def 
              by force

            from this rc_def
            have c3: "dom (map_\<alpha> x) = \<Q>e \<A>'"
              by (simp add: c2' subset_Collect_conv)

            have c4: "dom (map_\<alpha> x) = dom (ssm.\<alpha> x)"
              unfolding map_\<alpha>_def
              apply auto
              using option.collapse by fastforce

            from c2'
            show "x \<in> {c. map_\<alpha> c \<in> rc \<and> map_invar c \<and> dom (ssm.\<alpha> c) = \<Q>e \<A>'}"
              apply simp
              using c3 c4
              by auto
        qed
      qed
    qed
  qed
  }
  {
    fix P Pa
    assume PPa: "(P, Pa) \<in> br map_\<alpha> (\<lambda>m. map_invar m \<and> dom (ssm.\<alpha> m) = \<Q>e \<A>')"
    thm init_closure_correct
    from PPa
    have s1: "ssm.invar P \<and> (\<forall>q\<in>dom Pa. s.invar (the (ssm.lookup q P)))"
      unfolding br_def map_\<alpha>_def map_invar_def
      apply simp
      by (metis domIff ssm.lookup_correct)
    from PPa
    have s2: "dom Pa = dom (ssm.\<alpha> P) \<and>
    \<Q>e \<A>' \<subseteq> dom Pa \<and> (\<forall>q\<in>dom Pa. s.\<alpha> (the (ssm.lookup q P)) = the (Pa q))"
      unfolding br_def map_\<alpha>_def map_invar_def
      apply simp
      by (smt Collect_cong domI domIff dom_def map_lookup_def 
              ssm.map_lookup_axioms subset_eq)
    
    show "compute_ep_Trans_imp (nfae_trans \<A>) (nfae_states \<A>) P
       \<le> \<Down> (br (\<lambda>d. ba_to_set ` d.\<alpha> d) d.invar)
           (compute_ep_Trans (\<Delta>e \<A>') (\<Q>e \<A>') Pa)"
      apply (rule compute_ep_Trans_imp_correct[of "\<Delta>e \<A>'" "nfae_trans \<A>" "\<Q>e \<A>'"
                                      "nfae_states \<A>"])
      using trans_ok' state_ok
      apply auto[3]
      using s1 s2 by auto    
  }
  {
    fix P Pa N\<Delta> N\<Delta>' N\<I> N\<I>' N\<F> N\<F>' 
    assume trans_pre: "(N\<Delta>, N\<Delta>') \<in> br (\<lambda>d. ba_to_set ` d.\<alpha> d) d.invar"
       and init_pre: "(N\<I>, N\<I>') \<in> br s.\<alpha> s.invar"
       and accept_pre: "(N\<F>, N\<F>') \<in> br s.\<alpha> s.invar"
    show "((nfae_states \<A>,  d.union (nfae_trans \<A>) N\<Delta>,
         s.union (nfae_initial \<A>) N\<I>, s.union (nfae_accepting \<A>) N\<F>),
        \<lparr>\<Q> = \<Q>e \<A>',  \<Delta> = \<Delta>e \<A>' \<union> N\<Delta>', \<I> = \<I>e \<A>' \<union> N\<I>',
           \<F> = \<F>e \<A>' \<union> N\<F>'\<rparr>)
       \<in> br nfa_\<alpha> nfa_invar"
      unfolding br_def nfa_\<alpha>_def nfa_invar_def
      apply simp
      apply (rule conjI)
      using state_ok apply force
      apply (rule conjI)
      using trans_pre unfolding br_def
      apply simp
      using trans_ok' d.correct(8)
      apply simp
      apply blast
      apply (rule conjI)
      using initial_ok s.correct(18) init_pre 
      unfolding br_def
      apply simp
      apply (rule conjI)
      using accepting_ok accept_pre s.correct(18)
      unfolding br_def
      apply simp
      apply (rule conjI)
      using state_ok apply simp
      apply (rule conjI)
      using trans_ok' trans_pre d.correct(8) d.correct(7)
      unfolding br_def
      apply simp
      apply (rule conjI)
      using initial_ok init_pre s.correct(18) s.correct(19)
      unfolding br_def
      apply simp
      using accepting_ok accept_pre s.correct(18) s.correct(19)
      unfolding br_def
      by simp
  }
qed

term nfae_trans

schematic_goal NFA_elim_imp_code:
  fixes D_it1 :: "'q_set \<Rightarrow> ('q, 'qqset_m) set_iterator"
  fixes D_it2 :: "'qq_set \<Rightarrow> ('q \<times> 'q, 'q_set) set_iterator"
  fixes D_it3 :: "'q \<Rightarrow> 'qqset_m \<Rightarrow> ('q, 'q_set) set_iterator"
  fixes D_it4 :: "'d \<Rightarrow> ('q \<times> 'b \<times> 'q, 'd) set_iterator"
  fixes D_it5 :: "'q_set \<Rightarrow> ('q, 'd) set_iterator"
  fixes D_it6 :: "'q_set \<Rightarrow> ('q, 'q_set) set_iterator"
  fixes D_it7 :: "'q_set \<Rightarrow> ('q, 'q_set) set_iterator"
  fixes D_it8 :: "'q_set \<Rightarrow> ('q, 'q_set) set_iterator"
  assumes D_it1_OK [rule_format, refine_transfer]: 
         "set_iterator (D_it1 (fst A)) {e. e \<in> s.\<alpha> (fst A)}"
      and D_it2_OK [rule_format, refine_transfer]: 
         "set_iterator (D_it2 (fst (snd (snd A)))) 
                          {e. e \<in> ss.\<alpha> (fst (snd (snd A)))}"
      and D_it3_OK [rule_format, refine_transfer]: 
         "\<And> q ssm. set_iterator (D_it3 q ssm) 
                          {e. e \<in> s.\<alpha> (the (ssm.lookup q ssm))}"
      and D_it4_OK [rule_format, refine_transfer]: 
         "set_iterator (D_it4 (fst (snd A))) 
                          {t. t \<in> d.\<alpha> (fst (snd A))}"
      and D_it5_OK [rule_format, refine_transfer]: 
         "set_iterator (D_it5 (fst A)) 
                          {e. e \<in> s.\<alpha> (fst A)}"
      and D_it6_OK [rule_format, refine_transfer]: 
         "set_iterator (D_it6 (fst (snd (snd (snd A))))) 
                          {e. e \<in> s.\<alpha> (fst (snd (snd (snd A))))}"
      and D_it7_OK [rule_format, refine_transfer]: 
         "set_iterator (D_it7 (snd (snd (snd (snd A)))))
                          {e. e \<in> s.\<alpha> (snd (snd (snd (snd A))))}"
      and D_it8_OK [rule_format, refine_transfer]: 
         "set_iterator (D_it8 (fst A)) 
                          {e. e \<in> s.\<alpha> (fst A)}"
  shows "RETURN ?f \<le> NFA_elim_imp A"
  unfolding NFA_elim_imp_def
            reach_closure_impl_def
            init_closure_impl_def
            init_state_imp_def
            reach_closed_impl_def
            nfae_states_def
            nfae_trans_ep_def
            one_step_impl_def
            one_step_state_impl_def
            compute_ep_Trans_imp_def
            nfae_trans_def
            nfae_initial_def
            compute_ep_I_imp_def
            compute_ep_F_imp_def
            nfae_accepting_def
  apply (unfold split_def snd_conv fst_conv prod.collapse)
  apply (rule refine_transfer | assumption | erule conjE)+
  done


definition NFA_elim_code where
    "NFA_elim_code D_it1 D_it2 D_it3 D_it4 D_it5 D_it6 D_it7 D_it8 A
              = (let x = Let (D_it1 (fst A) (\<lambda>_. True)
                 (\<lambda>x \<sigma>. let xa = D_it2 (fst (snd (snd A))) (\<lambda>_. True)
                                  (\<lambda>xa \<sigma>'.
                                      if fst xa = x then s.ins (snd xa) \<sigma>' else \<sigma>')
                                  (s.ins x (s.empty ()))
                        in ssm.update x xa \<sigma>)
                 (ssm.empty ()))
            (while
              (\<lambda>R. \<not> s.ball (fst A)
                       (\<lambda>x. s.ball (the (ssm.lookup x R))
                             (\<lambda>q. s.subset (the (ssm.lookup q R))
                                   (the (ssm.lookup x R)))))
              (\<lambda>xa. D_it1 (fst A) (\<lambda>_. True)
                     (\<lambda>xb \<sigma>.
                         let xc = Let (D_it3 xb xa (\<lambda>_. True)
                                        (\<lambda>xc \<sigma>'.
  s.union \<sigma>' (the (ssm.lookup xc xa)))
                                        (the (ssm.lookup xb xa)))
                                   (ssm.sng xb)
                         in ssm.update xb (the (ssm.lookup xb xc)) \<sigma>)
                     (ssm.empty ())));
       xa = D_it4 (fst (snd A)) (\<lambda>_. True)
             (\<lambda>xa \<sigma>.
                 let xb = D_it5 (fst A) (\<lambda>_. True)
                           (\<lambda>xb \<sigma>'.
                               if s.memb (fst xa) (the (ssm.lookup xb x))
                               then d.add xb (fst (snd xa)) (snd (snd xa)) \<sigma>'
                               else \<sigma>')
                           d.empty
                 in d.union xb \<sigma>)
             d.empty;
       xb = D_it6 (fst (snd (snd (snd A)))) (\<lambda>_. True)
             (\<lambda>xb \<sigma>.
                 if ssm.lookup xb x = None then \<sigma>
                 else s.union \<sigma> (the (ssm.lookup xb x)))
             (s.empty ());
       xc = D_it7 (snd (snd (snd (snd A)))) (\<lambda>_. True)
             (\<lambda>xc \<sigma>.
                 let xd = D_it8 (fst A) (\<lambda>_. True)
                           (\<lambda>xd \<sigma>'.
                               if s.memb xc (the (ssm.lookup xd x))
                               then s.ins xd \<sigma>' else \<sigma>')
                           (s.empty ())
                 in s.union xd \<sigma>)
             (s.empty ())
   in (fst A, d.union (fst (snd A)) xa, s.union (fst (snd (snd (snd A)))) xb,
       s.union (snd (snd (snd (snd A)))) xc))"

schematic_goal NFA_elim_impl_code :
    "NFA_elim_code D_it1 D_it2 D_it3 D_it4 D_it5 D_it6 D_it7 D_it8 A  = ?XXX1"
  unfolding NFA_elim_code_def
  by (rule refl)+

definition lookup_aux where
    "lookup_aux v rc = ssm.lookup v rc"

schematic_goal lookup_aux_code :
    "lookup_aux v rc = ?XXX1"
  unfolding lookup_aux_def
  by (rule refl)+

end

interpretation epsilon_elim_interval_defs: 
        epsilon_elim_interval_code semIs emptyIs nemptyIs 
                   intersectIs diffIs elemIs canonicalIs
                   rs_ops rs_ops rs_ops 
                   rs_ops rm_ops rs_lts_ops                             
  by intro_locales
  

definition lookup_aux where
      "lookup_aux = epsilon_elim_interval_defs.lookup_aux"



definition rs_nfa_elim where
      "rs_nfa_elim = epsilon_elim_interval_defs.NFA_elim_code
                     (\<lambda> x. rs_iteratei x)
                     (\<lambda> x. rs_iteratei x)
                     (\<lambda> q ssm. rs_iteratei (the (lookup_aux q ssm)))
                     rs_lts_it
                     (\<lambda> x. rs_iteratei x)
                     (\<lambda> x. rs_iteratei x)
                     (\<lambda> x. rs_iteratei x)
                     (\<lambda> x. rs_iteratei x)"

lemmas epsilon_elim_defs =
  lookup_aux_def
  rs_nfa_elim_def

lemmas lookup_code [code] = 
    epsilon_elim_interval_defs.lookup_aux_code[folded epsilon_elim_defs]

lemmas rs_nfa_elim_code [code] = 
    epsilon_elim_interval_defs.NFA_elim_impl_code[of 
                     "\<lambda> x. rs_iteratei x"
                     "\<lambda> x. rs_iteratei x"
                     "\<lambda> q ssm. rs_iteratei (the (lookup_aux q ssm))"
                     rs_lts_it
                     "\<lambda> x. rs_iteratei x"
                     "\<lambda> x. rs_iteratei x"
                     "\<lambda> x. rs_iteratei x"
                     "\<lambda> x. rs_iteratei x",
                    folded epsilon_elim_defs]
                  
end


