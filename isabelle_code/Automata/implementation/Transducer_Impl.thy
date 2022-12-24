
theory Transducer_Impl

imports "../Transducer" DFAByLTS 
        RBT_LTSImpl RBT_NFAImpl interval

begin

type_synonym 'a TlabelI = "('a \<times> 'a) list option \<times>  
                                ('a option \<Rightarrow> ('a \<times> 'a) list option)"



locale transducer_code = automaton_by_lts_interval_syntax
  s_ops l_ops lt_ops d_ops +
  s: StdSet s_ops (* Set operations on states *) +
  l: StdSet l_ops (* Set operations on labels *) +
  lt: StdSet lt_ops   (* Set operations on labels *) +
  d: StdLTS d_ops elemIs (* An LTS *) +
  dt: StdLTS dt_ops "\<lambda> _ _. True" (* An LTS *) +
  ddt: StdLTS ddt_ops "\<lambda> _ _. True" (* An LTS *) +
  ss: StdSet ss_ops (* Set operations on states *)  +
  ssd: StdSet ssd_ops (* Set operations on states *)  +
  ssm: StdMap m_ops 
  for s_ops::"('q::{NFA_states},'q_set,_) set_ops_scheme"
  and ss_ops::"('q \<times> 'q,'qq_set,_) set_ops_scheme"
  and ssd_ops::"(('q \<times> 'q) \<times> ('q \<times> 'q),'qqqq_set,_) set_ops_scheme"
  and l_ops::"('a ::linorder, 'a_set ,_) set_ops_scheme"
  and lt_ops::"(('a \<times> 'a) list, 'ai_set ,_) set_ops_scheme"
  and m_ops :: "('q, 'q_set, 'qqset_m, 'more) map_ops_scheme"
  and ddt_ops::"('q \<times> 'q,('a \<times> 'a) list,'a,'ddt,_) lts_ops_scheme"
  and d_ops::"('q,('a \<times> 'a) list,'a,'d,_) lts_ops_scheme"
  and dt_ops::"('q, 'a TlabelI,'a,'dt,_) lts_ops_scheme"

begin




definition prods_imp where
  "prods_imp Q1 Q2 = 
   FOREACH 
     {q. q \<in> s.\<alpha> Q1} (\<lambda> q Q. do { 
        S \<leftarrow>  FOREACH {q. q \<in> s.\<alpha> Q2} 
                        (\<lambda> q' Q'. RETURN (ss.ins (q,q') Q')) (ss.empty ());
        RETURN (ss.union Q S)
    }) (ss.empty ())"

lemma prods_imp_correct:
  fixes Q1 Q2 Q1' Q2'
  assumes Q1_ok: "Q1' = s.\<alpha> Q1 \<and> s.invar Q1"
      and Q2_ok: "Q2' = s.\<alpha> Q2 \<and> s.invar Q2"
  shows  "prods_imp Q1 Q2 \<le> \<Down> (br ss.\<alpha> ss.invar) (prods Q1' Q2')"
  unfolding prods_imp_def prods_def
  apply refine_rcg
  apply (subgoal_tac "inj_on id {q. q \<in> s.\<alpha> Q1}")
  apply assumption
  apply force
  using Q1_ok apply force
  unfolding br_def
  apply simp
  apply (simp add: ss.empty_correct(1) ss.empty_correct(2))
  apply (subgoal_tac "inj_on id {q. q \<in> s.\<alpha> Q2}")
  apply assumption
  apply force
  using Q2_ok apply force
  apply (subgoal_tac "(ss.empty (), {}) \<in> (br ss.\<alpha> ss.invar)")
  apply assumption
  unfolding br_def
  apply simp
  apply (simp add: ss.empty_correct(1) ss.empty_correct(2))
  apply simp
  apply (simp add: ss.ins_correct(1) ss.ins_correct(2))
  apply simp
  by (simp add: ss.union_correct(1) ss.union_correct(2))


definition copy_tran_imp where
   "copy_tran_imp q q' S = 
    FOREACH {q. q \<in> s.\<alpha> S} 
              (\<lambda> s T. RETURN (ssd.ins ((q,s), (q',s)) T)) (ssd.empty ())"

lemma copy_tran_imp_correct:
  fixes q q' S S'
  assumes S_ok: "S' = s.\<alpha> S \<and> s.invar S"
  shows "copy_tran_imp q q' S \<le> \<Down> (br ssd.\<alpha> ssd.invar) (copy_tran q q' S')"
  unfolding copy_tran_imp_def copy_tran_def
  apply refine_rcg
  apply (subgoal_tac "inj_on id {q. q \<in> s.\<alpha> S}")
  apply assumption
  apply force
  using S_ok apply force
  unfolding br_def apply simp
  using ssd.empty_correct(1) ssd.empty_correct(2) apply blast
  apply simp
  by (simp add: ssd.ins_correct(1) ssd.ins_correct(2))


definition copy_tran'_imp where
   "copy_tran'_imp q \<alpha> q' S = 
    FOREACH {q. q \<in> s.\<alpha> S} 
              (\<lambda> s T. RETURN (ddt.add (q,s) \<alpha> (q',s) T)) (ddt.empty)"

fun interval_to_set_prod :: "('q \<times>'q) \<times> ('a \<times> 'a) list \<times> ('q \<times> 'q) \<Rightarrow> 
                        ('q \<times> 'q) \<times> 'a set \<times> ('q \<times> 'q)"  where
    "interval_to_set_prod (q, s, q') = (q, semIs s, q')"

definition ddt\<alpha> where
   "ddt\<alpha> = (\<lambda> S. interval_to_set_prod ` (ddt.\<alpha> S))"

definition ddtinvar where
   "ddtinvar = (\<lambda> S. ddt.invar S \<and> (\<forall> (q, \<alpha>, q') \<in> (ddt.\<alpha> S). canonicalIs \<alpha>))"

lemma copy_tran'_imp:
  assumes S_ok: "S' = s.\<alpha> S \<and> s.invar S"
      and \<alpha>_ok: "\<alpha>' = semIs \<alpha> \<and> canonicalIs \<alpha>"
  shows "copy_tran'_imp q \<alpha> q' S \<le> \<Down> (br ddt\<alpha> ddtinvar) 
   (copy_tran' q \<alpha>' q' S')"
  unfolding copy_tran'_imp_def copy_tran'_def
  apply refine_rcg
  apply (subgoal_tac "inj_on id {q. q \<in> s.\<alpha> S}")
  apply assumption
  apply force
  using S_ok apply force
  unfolding br_def ddt\<alpha>_def ddtinvar_def
  apply simp
  using ddt.correct
  apply force
  apply simp
  apply (rule conjI)
proof -
  {
    fix x it \<sigma> x' it' \<sigma>'
    assume xin: "x \<in> it"
       and itin: "it \<subseteq> S'"
       and pre1: "{((q, s), \<alpha>', q', s) |s. s \<in> S' \<and> s \<notin> it} = interval_to_set_prod ` ddt.\<alpha> \<sigma> \<and>
       ddt.invar \<sigma> \<and> (\<forall>x\<in>ddt.\<alpha> \<sigma>. case x of (q, \<alpha>, q') \<Rightarrow> canonicalIs \<alpha>)"
       and pre2: "\<sigma>' = interval_to_set_prod ` ddt.\<alpha> \<sigma>"
    from pre1
    have "ddt.\<alpha> (ddt.add (q, x) \<alpha> (q', x) \<sigma>) = 
                {((q, x), \<alpha>, (q', x))} \<union> ddt.\<alpha> \<sigma>"
      using ddt.lts_add_correct(2) by auto
     
    from this
    show "insert ((q, x), \<alpha>', q', x) (interval_to_set_prod ` ddt.\<alpha> \<sigma>) =
          interval_to_set_prod ` ddt.\<alpha> (ddt.add (q, x) \<alpha> (q', x) \<sigma>)"
      apply simp
      using \<alpha>_ok
      by force  
    }
    {
      fix x it \<sigma> x' it' \<sigma>'
      assume xin: "x \<in> it"
         and itin: "it \<subseteq> S'"
         and pre: "{((q, s), \<alpha>', q', s) |s. s \<in> S' \<and> s \<notin> it} = interval_to_set_prod ` ddt.\<alpha> \<sigma> \<and>
                  ddt.invar \<sigma> \<and> (\<forall>x\<in>ddt.\<alpha> \<sigma>. case x of (q, \<alpha>, q') \<Rightarrow> canonicalIs \<alpha>)"

      show "ddt.invar (ddt.add (q, x) \<alpha> (q', x) \<sigma>) \<and>
               (\<forall>x\<in>ddt.\<alpha> (ddt.add (q, x) \<alpha> (q', x) \<sigma>).
                     case x of (q, \<alpha>, q') \<Rightarrow> canonicalIs \<alpha>)"
        apply (rule conjI)
        using pre 
        apply (simp add: pre ddt.lts_add_correct(1))
        using \<alpha>_ok
        by (simp add: ddt.lts_add_correct(2) pre)
    }
  qed


definition subtrans_comp_imp where
    "subtrans_comp_imp q \<alpha> f q' F fe T D1 D2 =
     FOREACH
      {t. t \<in> d.\<alpha> T} (\<lambda> (q1, \<alpha>', q1') (D1, D2).
      (if (nemptyIs (intersectIs \<alpha> \<alpha>')) then do {
       D1 \<leftarrow> (if (F f (intersectIs \<alpha> \<alpha>') \<noteq> None) 
                  then RETURN (ddt.add (q,q1)
                       (the (F f (intersectIs \<alpha> \<alpha>'))) (q',q1') D1)
               else RETURN D1);
       D2 \<leftarrow> (if fe f (intersectIs \<alpha> \<alpha>') then 
                    RETURN (ssd.ins ((q,q1), (q',q1'))  D2) else RETURN D2);
       RETURN (D1, D2)
      }
      else (RETURN (D1, D2)))) (D1, D2)"

definition Dddt\<alpha> where
   "Dddt\<alpha> = (\<lambda> (D1,D2). (interval_to_set_prod ` (ddt.\<alpha> D1), ssd.\<alpha> D2))"

definition Dddtinvar where
   "Dddtinvar = (\<lambda> (D1, D2). ddt.invar D1 \<and> 
                             (\<forall> (q, \<alpha>, q') \<in> (ddt.\<alpha> D1). canonicalIs \<alpha>) \<and>
                             ssd.invar D2)"

lemma subtrans_comp_correct:
  assumes T'_ok: "T' = interval_to_set ` (d.\<alpha> T)"
      and T_ok: "\<forall> (q, \<alpha>, q') \<in> (d.\<alpha> T). canonicalIs \<alpha>"
      and DD_ok: "((D1, D2), D1', D2') \<in> br Dddt\<alpha> Dddtinvar"
      and \<alpha>_ok: "canonicalIs \<alpha> \<and> \<alpha>' = semIs \<alpha>"
      and F_ok: "\<forall> \<alpha> \<alpha>'. \<alpha>' = semIs \<alpha> \<longrightarrow> (F f \<alpha> = None) \<longleftrightarrow> (F' f' \<alpha>' = None)"
      and F_ok'': "\<forall> \<alpha>. canonicalIs \<alpha> \<and> (F f \<alpha> \<noteq> None) \<longrightarrow> 
                                        canonicalIs (the (F f \<alpha>))"
      and F_ok': "\<forall> \<alpha> \<alpha>'. (\<alpha>' = semIs \<alpha> \<and> F f \<alpha> \<noteq> None \<longrightarrow> semIs (the (F f \<alpha>)) = the (F' f' \<alpha>'))"
      and fe_ok: "\<forall> \<alpha> \<alpha>'. \<alpha>' = semIs \<alpha> \<longrightarrow> fe f \<alpha>  = fe' f' \<alpha>'"
  shows "subtrans_comp_imp q \<alpha> f q' F fe T D1 D2 \<le> \<Down> (br Dddt\<alpha> Dddtinvar)
         (subtrans_comp q \<alpha>' f' q' F' fe' T' D1' D2')"
  unfolding subtrans_comp_imp_def subtrans_comp_def
  apply (refine_rcg)
  apply (subgoal_tac "inj_on interval_to_set {t. t \<in> d.\<alpha> T}")
  apply assumption
  using T_ok inj_semIs
  unfolding inj_on_def 
  apply simp
  apply fastforce
  using T'_ok apply force
  using DD_ok
  apply simp
  using \<alpha>_ok intersectIs_correct nemptyIs_correct
  apply (smt Pair_inject T_ok interval_to_set.simps mem_Collect_eq old.prod.case subset_eq)
  using \<alpha>_ok intersectIs_correct nemptyIs_correct F_ok
  apply (smt Pair_inject T_ok interval_to_set.simps mem_Collect_eq old.prod.case subset_eq)
  apply (subgoal_tac "(ddt.add (q, x1c) (the (F f (intersectIs \<alpha> x1d))) (q', x2d) x1e,
        {((q, x1), the (F' f' (\<alpha>' \<inter> x1a)), q', x2a)} \<union> x1b)
       \<in> (br ddt\<alpha> ddtinvar)")
  apply assumption  
  defer
  unfolding Dddt\<alpha>_def Dddtinvar_def br_def
  apply simp
  unfolding ddt\<alpha>_def ddtinvar_def
  apply simp
  using fe_ok \<alpha>_ok intersectIs_correct nemptyIs_correct
  defer
  apply (subgoal_tac "(ssd.ins ((q, x1c), q', x2d) x2e, {((q, x1), q', x2a)} \<union> x2b)
                       \<in> (br ssd.\<alpha> ssd.invar)")
  apply assumption
  unfolding br_def
  apply simp
  using ssd.ins_correct(1) ssd.ins_correct(2) apply auto[1]
  apply simp
  apply simp
  apply simp
  apply simp defer apply simp
proof - 
  {
    fix x1c x1d x2d x1e it x2e
    assume p1: "D1' \<union>
       {((q, q1), the (F' f' (\<alpha>' \<inter> \<alpha>'')), q', q1') |q1 q1' \<alpha>''.
        (q1, \<alpha>'', q1') \<in> T' \<and>
        (q1, \<alpha>'', q1') \<notin> interval_to_set ` it \<and>
        \<alpha>' \<inter> \<alpha>'' \<noteq> {} \<and> (\<exists>y. F' f' (\<alpha>' \<inter> \<alpha>'') = Some y)} =
       interval_to_set_prod ` ddt.\<alpha> x1e \<and>
       D2' \<union>
       {((q, q1), q', q1') |q1 q1'.
        \<exists>\<alpha>''. (q1, \<alpha>'', q1') \<in> T' \<and>
               (q1, \<alpha>'', q1') \<notin> interval_to_set ` it \<and>
               \<alpha>' \<inter> \<alpha>'' \<noteq> {} \<and> fe' f' (\<alpha>' \<inter> \<alpha>'')} =
       ssd.\<alpha> x2e \<and>
       ddt.invar x1e \<and>
       (\<forall>x\<in>ddt.\<alpha> x1e. case x of (q, \<alpha>, q') \<Rightarrow> canonicalIs \<alpha>) \<and> ssd.invar x2e"
      and p2: "(x1c, x1d, x2d) \<in> it"
      and p3: "it \<subseteq> d.\<alpha> T"
      and p4: "\<exists>y. F f (intersectIs \<alpha> x1d) = Some y"
      and p5: "\<exists>y. F' f' (\<alpha>' \<inter> semIs x1d) = Some y"

    from p2 p3 T_ok p1
    have canox1d: "canonicalIs x1d"
      by force
    from this \<alpha>_ok p3 T_ok p2 intersectIs_correct F_ok F_ok' p4 p5
    have c1: "the (F' f' (\<alpha>' \<inter> semIs x1d)) = semIs (the (F f (intersectIs \<alpha> x1d)))"
      by (metis option.distinct(1))

    show "insert ((q, x1c), the (F' f' (\<alpha>' \<inter> semIs x1d)), q', x2d)
        (interval_to_set_prod ` ddt.\<alpha> x1e) =
       interval_to_set_prod `
       ddt.\<alpha> (ddt.add (q, x1c) (the (F f (intersectIs \<alpha> x1d))) (q', x2d) x1e) \<and>
       ddt.invar (ddt.add (q, x1c) (the (F f (intersectIs \<alpha> x1d))) (q', x2d) x1e) \<and>
       (\<forall>x\<in>ddt.\<alpha> (ddt.add (q, x1c) (the (F f (intersectIs \<alpha> x1d))) (q', x2d) x1e).
           case x of (q, \<alpha>, q') \<Rightarrow> canonicalIs \<alpha>)"
      apply (rule conjI)
      using c1 p1 
      apply (simp add: ddt.lts_add_correct(2))
      apply (rule_tac conjI)
      using p1
      apply (simp add: ddt.lts_add_correct(1))
      apply (subgoal_tac 
             "ddt.\<alpha> (ddt.add (q, x1c) (the (F f (intersectIs \<alpha> x1d))) (q', x2d) x1e) = 
              {((q, x1c), (the (F f (intersectIs \<alpha> x1d))), (q', x2d))} \<union> (ddt.\<alpha> x1e)")
       apply simp
      apply (rule_tac conjI)
      using F_ok'' p1 canox1d
      apply (simp add: \<alpha>_ok intersectIs_correct p4)
      using p1 apply simp
      using p1
      using ddt.lts_add_correct(2) by auto
  }
  {
    fix x1c x1d x2d x1e it x2e
    assume p1: "D1' \<union>
       {((q, q1), the (F' f' (\<alpha>' \<inter> \<alpha>'')), q', q1') |q1 q1' \<alpha>''.
        (q1, \<alpha>'', q1') \<in> T' \<and>
        (q1, \<alpha>'', q1') \<notin> interval_to_set ` it \<and>
        \<alpha>' \<inter> \<alpha>'' \<noteq> {} \<and> (\<exists>y. F' f' (\<alpha>' \<inter> \<alpha>'') = Some y)} =
       interval_to_set_prod ` ddt.\<alpha> x1e \<and>
       D2' \<union>
       {((q, q1), q', q1') |q1 q1'.
        \<exists>\<alpha>''. (q1, \<alpha>'', q1') \<in> T' \<and>
               (q1, \<alpha>'', q1') \<notin> interval_to_set ` it \<and>
               \<alpha>' \<inter> \<alpha>'' \<noteq> {} \<and> fe' f' (\<alpha>' \<inter> \<alpha>'')} =
       ssd.\<alpha> x2e \<and>
       ddt.invar x1e \<and>
       (\<forall>x\<in>ddt.\<alpha> x1e. case x of (q, \<alpha>, q') \<Rightarrow> canonicalIs \<alpha>) \<and> ssd.invar x2e"
      and p2: "(x1c, x1d, x2d) \<in> it"
      and p3: "it \<subseteq> d.\<alpha> T"
      and p4: "intersectIs \<alpha> x1d \<noteq> []"
      and p5: "\<alpha>' \<inter> semIs x1d \<noteq> {}"

    from p2 p3 p1 T_ok
    have x1dcan: "canonicalIs x1d"
      by auto

    from fe_ok x1dcan \<alpha>_ok
    show "fe f (intersectIs \<alpha> x1d) = fe' f' (\<alpha>' \<inter> semIs x1d)"
      by (simp add: intersectIs_correct)
  }
qed


term dt.\<alpha>



definition trans_comp_imp where
    "trans_comp_imp F fe T1 T2 Q = 
     FOREACH
     {t. t \<in> dt.\<alpha> T1}
     (\<lambda> (q, (\<alpha>, f), q') (D1, D2). 
       (
          if (\<alpha> = None) then 
              (if (f None = None) then 
                  do {
                      D2' \<leftarrow> copy_tran_imp q q' Q;
                      RETURN (D1, ssd.union D2 D2')
                  }
               else do {
                  D1' \<leftarrow> copy_tran'_imp q (the (f None)) q' Q;
                  RETURN (ddt.union D1 D1', D2)
               })
          else (subtrans_comp_imp q (the \<alpha>) f q' F fe T2 D1 D2)
        )) (ddt.empty, ssd.empty ())"

lemma inj_aux: 
  fixes ft T
  assumes ft_ok: "inj_on ft {f | q \<alpha> f q'. (q, (\<alpha>, f), q') \<in> dt.\<alpha> T}"
      and T_ok: "(\<forall> (q, (\<alpha>, f), q') \<in> dt.\<alpha> T. 
                                    \<alpha> \<noteq> None \<longrightarrow> canonicalIs (the \<alpha>))"
  shows "inj_on (\<lambda> (q, (\<alpha>, f), q'). (q, (if \<alpha> = None then None else
                                  Some (semIs (the \<alpha>)), ft f), q'))  (dt.\<alpha> T)"
  unfolding inj_on_def
  apply rule
  apply rule
  apply rule
proof   -
  fix x y
  assume xin: "x \<in> dt.\<alpha> T"
     and yin: "y \<in> dt.\<alpha> T"
     and pre: "(case x of
            (q, xa, xb) \<Rightarrow>
              (case xa of
               (\<alpha>, f) \<Rightarrow>
                 \<lambda>q'. (q, (if \<alpha> = None then None else Some (semIs (the \<alpha>)), ft f), q'))
               xb) =
           (case y of
            (q, xa, xb) \<Rightarrow>
              (case xa of
               (\<alpha>, f) \<Rightarrow>
                 \<lambda>q'. (q, (if \<alpha> = None then None else Some (semIs (the \<alpha>)), ft f), q'))
               xb)"
      from xin 
      obtain qx \<alpha>x fx qx' where
       x_def: "x = (qx, (\<alpha>x, fx), qx')"
        by (metis old.prod.exhaust)

      from xin this
      have fxin: "fx \<in> {f | q \<alpha> f q'. (q, (\<alpha>, f), q') \<in> dt.\<alpha> T}"
        by auto

      from yin 
      obtain qy \<alpha>y fy qy' where
       y_def: "y = (qy, (\<alpha>y, fy), qy')"
        by (metis old.prod.exhaust)

      from yin this
      have fyin: "fy \<in> {f | q \<alpha> f q'. (q, (\<alpha>, f), q') \<in> dt.\<alpha> T}"
        by auto

      from x_def y_def pre
      show "x = y"
        apply simp
        using T_ok ft_ok
      proof -
        assume pre1: "qx = qy \<and>
            (if \<alpha>x = None then None else Some (semIs (the \<alpha>x))) =
            (if \<alpha>y = None then None else Some (semIs (the \<alpha>y))) \<and>
              ft fx = ft fy \<and> qx' = qy'"
        show "\<alpha>x = \<alpha>y \<and> fx = fy"
        proof (cases "\<alpha>x = None")
          case True
          from this pre1
          have "\<alpha>y = None"
            by (meson option.distinct(1))
          from this True
          show ?thesis 
            apply simp
            using pre1 ft_ok fxin fyin
            unfolding inj_on_def
            by fastforce
          next
            case False
            from this pre1
            have eq1: "semIs (the \<alpha>x) = semIs (the \<alpha>y)"
              by (metis option.distinct(1) option.sel)
            from this obtain axs ays
              where as_def: "\<alpha>x = Some axs \<and> \<alpha>y = Some ays"
              using False pre1 by force
            from this T_ok fyin fxin
            have "canonicalIs axs \<and> canonicalIs ays"
              using x_def xin y_def yin by auto
            from eq1 this
            show ?thesis 
              apply (rule_tac conjI)
              using fxin fyin T_ok as_def
              apply (simp add: inj_semIs)
              using fxin fyin ft_ok pre1
              unfolding inj_on_def
              by simp
          qed
        qed
      qed
         


lemma trans_comp_imp_correct:
  assumes T_ok: "T1' = (\<lambda> (q, (\<alpha>, f), q'). (q, (if \<alpha> = None then None else
                                  Some (semIs (the \<alpha>)), ft f), q')) ` (dt.\<alpha> T1) \<and> 
                        (\<forall> (q, (\<alpha>, f), q') \<in> dt.\<alpha> T1. 
                                    \<alpha> \<noteq> None \<longrightarrow> canonicalIs (the \<alpha>))"
      and ft_ok: "inj_on ft {f | q \<alpha> f q'. (q, (\<alpha>, f), q') \<in> dt.\<alpha> T1}"
      and ft_ok': "\<forall> f \<in> {f | q \<alpha> f q'. (q, (\<alpha>, f), q') \<in> dt.\<alpha> T1}. 
                  ((f None = None) = ((ft f None) = None)) \<and>
                  ((f None \<noteq> None) \<longrightarrow> canonicalIs (the (f None)) \<and> 
                                      semIs (the (f None)) = the (ft f None)) \<and>
                  (\<forall> \<alpha>. ((f (Some \<alpha>)) = None \<longleftrightarrow> (ft f (Some \<alpha>)) = None) \<and>
                  (f (Some \<alpha>) \<noteq> None \<longrightarrow> canonicalIs (the (f (Some \<alpha>))) \<and> 
                                      semIs (the (f (Some \<alpha>))) = the (ft f (Some \<alpha>))))"
      and Q_ok: "Q' = s.\<alpha> Q \<and> s.invar Q"
      and T2_ok: "T2' = interval_to_set ` d.\<alpha> T2 \<and> 
                  (\<forall>(q, \<alpha>, q')\<in>d.\<alpha> T2. canonicalIs \<alpha>)"
      and F_ok: "\<forall>\<alpha> \<alpha>' f f'. \<alpha>' = semIs \<alpha> \<and> 
                      (f' = ft f)\<longrightarrow> 
                ((F f \<alpha> = None) = (F' f' \<alpha>' = None) \<and> 
                 (F f \<alpha> \<noteq> None \<longrightarrow> canonicalIs (the (F f \<alpha>)) \<and> 
                                    semIs (the (F f \<alpha>)) = (the (F' f' \<alpha>'))))"
      and fe_ok: "\<forall>\<alpha> \<alpha>' f f'. \<alpha>' = semIs \<alpha> \<and> 
                      (f' = ft f)\<longrightarrow> 
                ((fe f \<alpha>) = (fe' f' \<alpha>'))"
  shows "trans_comp_imp F fe T1 T2 Q  \<le> \<Down> (br Dddt\<alpha> Dddtinvar)
         (Transducer.trans_comp F' fe' T1' T2' Q')"
  unfolding trans_comp_imp_def Transducer.trans_comp_def
  apply refine_rcg
  apply (subgoal_tac "inj_on (\<lambda> (q, (\<alpha>, f), q'). (q, (if \<alpha> = None then None else
                                  Some (semIs (the \<alpha>)), ft f), q')) {t. t \<in> dt.\<alpha> T1}")
  apply assumption
  using inj_aux[of ft T1] T_ok ft_ok
  apply force
  using T_ok apply simp
  unfolding br_def Dddt\<alpha>_def Dddtinvar_def
  apply simp
  apply (simp add: ddt.lts_empty_correct(1) 
            ddt.lts_empty_correct(2) ssd.empty_correct(1) ssd.empty_correct(2))
  apply fastforce
  defer
  apply (subgoal_tac "copy_tran_imp x1d x2f Q
       \<le> \<Down> (br ssd.\<alpha> ssd.invar)
           (copy_tran x1 x2b Q')")
  apply assumption
  defer  
  defer
  apply (subgoal_tac "copy_tran'_imp x1d (the (x2e None)) x2f Q
       \<le> \<Down> (br ddt\<alpha> ddtinvar)
           (copy_tran' x1 (the (x2a None)) x2b Q')")  
        apply assumption  
proof -
  {
    fix x x' it it' x1d x2d  x2f x1e x1f x2e x1 x2 x1a x2b x1b x2a
    assume xin: "x \<in> it"
       and xin': "x' \<in> it'"
       and itin: "it \<subseteq> {t. t \<in> dt.\<alpha> T1}"
       and it'in: "it' \<subseteq> T1'"
       and x_def: "x = (x1d, x2d)"
       and x2d_def : "x2d = (x1e, x2f)"
       and x1e_def: "x1e = (x1f, x2e)"
       and x'_def: "x' = (x1, x2)"
       and x2_def: "x2 = (x1a, x2b)"
       and x1a_def: "x1a = (x1b, x2a)"
       and x1f_def: "x1f = None"
       and x1b_def: "x1b = None"
       and pre: "x' =
       (case x of
        (q, xa, xb) \<Rightarrow>
          (case xa of
           (\<alpha>, f) \<Rightarrow>
             \<lambda>q'. (q, (if \<alpha> = None then None else Some (semIs (the \<alpha>)), ft f), q'))
           xb)"

    from x_def x2d_def x1e_def xin itin
    have x2ein: "x2e \<in> {f | q a f q'. (q, (a, f), q') \<in> dt.\<alpha> T1}"
      by blast


    from pre x_def x2d_def x1e_def x'_def x2_def x1a_def 
    show "(x2e None = None) = (x2a None = None)"
      apply simp
      using ft_ok' x2ein
      by fastforce
  }
  {
    fix x1d::'q 
    fix x2f::'q 
    fix x2e x1 x2a x2b x x2d x1e x1f x' x2 x1a x1b it
    assume x2e_def: "x2e None \<noteq> None"
       and x2a_def: "x2a None \<noteq> None"
       and x_def: "x = (x1d, x2d)"
       and x2d_def: "x2d = (x1e, x2f)"
       and x1e_def: "x1e = (x1f, x2e)"
       and x'_def: "x' = (x1, x2)"
       and x2_def: "x2 = (x1a, x2b)"
       and x1a_def: "x1a = (x1b, x2a)"
       and xin: "x \<in> it"
       and itin: "it \<subseteq> {t. t \<in> dt.\<alpha> T1}"
       and xx': "x' =
       (case x of
        (q, xa, xb) \<Rightarrow>
          (case xa of
           (\<alpha>, f) \<Rightarrow>
             \<lambda>q'. (q, (if \<alpha> = None then None else Some (semIs (the \<alpha>)), ft f), q'))
           xb)"
    from xx' x_def x'_def x2d_def x2_def
    have eqx1: "x1d = x1 \<and> x2f = x2b"
      apply auto
      apply (simp add: x1e_def)
      by (simp add: x1e_def)


    from x2e_def xin itin ft_ok x_def x2d_def x1e_def ft_ok'
    have "canonicalIs (the (x2e (None))) \<and>
              semIs (the (x2e (None))) = the (ft x2e (None))"
      by fastforce
    from this xx' x_def x'_def x2_def x2d_def x1e_def x1a_def
    have "semIs (the (x2e None)) = (the (x2a None)) \<and> canonicalIs (the (x2e None))"
      by simp

    from this Q_ok copy_tran'_imp[of Q' Q "the (x2a None)" "the (x2e None)" x1d x2f]
         eqx1
    show "copy_tran'_imp x1d (the (x2e None)) x2f Q
       \<le> \<Down> (br ddt\<alpha> ddtinvar) (copy_tran' x1 (the (x2a None)) x2b Q')"
      by auto
  }
  {
    fix x1g D1' x2g x1c D1'a x2c \<sigma> \<sigma>'
    
    assume D1_ok: "(D1', D1'a) \<in> br ddt\<alpha> ddtinvar"
       and \<sigma>_def: "\<sigma> = (x1g, x2g)"
       and \<sigma>'_def: "\<sigma>' = (x1c, x2c)"
       and \<sigma>_ok: "(\<sigma>, \<sigma>')
       \<in> {(c, a).
           a = (case c of (D1, D2) \<Rightarrow> (interval_to_set_prod ` ddt.\<alpha> D1, ssd.\<alpha> D2)) \<and>
           (case c of
            (D1, D2) \<Rightarrow>
              ddt.invar D1 \<and>
              (\<forall>(q, \<alpha>, q')\<in>ddt.\<alpha> D1. canonicalIs \<alpha>) \<and> ssd.invar D2)}"
    
    from \<sigma>_ok \<sigma>'_def \<sigma>_def
    have pre1: "x1c = interval_to_set_prod ` ddt.\<alpha> x1g \<and>
    x2c = ssd.\<alpha> x2g \<and>
    ddt.invar x1g \<and>
    (\<forall>x\<in>ddt.\<alpha> x1g. case x of (q, \<alpha>, q') \<Rightarrow> canonicalIs \<alpha>) \<and> ssd.invar x2g"
      by simp

    from D1_ok
    have pre2: "D1'a = interval_to_set_prod ` ddt.\<alpha> D1' \<and>
          ddt.invar D1' \<and> (\<forall>x\<in>ddt.\<alpha> D1'. case x of (q, \<alpha>, q') \<Rightarrow> canonicalIs \<alpha>)"
      unfolding br_def ddt\<alpha>_def ddtinvar_def
      by simp
    show "((ddt.union x1g D1', x2g), x1c \<union> D1'a, x2c)
       \<in> {(c, a).
           a = (case c of (D1, D2) \<Rightarrow> (interval_to_set_prod ` ddt.\<alpha> D1, ssd.\<alpha> D2)) \<and>
           (case c of
            (D1, D2) \<Rightarrow>
              ddt.invar D1 \<and> (\<forall>(q, \<alpha>, q')\<in>ddt.\<alpha> D1. canonicalIs \<alpha>) \<and> ssd.invar D2)}"
      apply simp
      apply (rule conjI)
      using pre1 pre2
      apply (simp add: ddt.lts_union_correct(2) image_Un)
      apply (rule conjI)
      using pre1 apply simp
      apply (rule conjI)
      using pre1 pre2
      apply (simp add: ddt.lts_union_correct(1))
      apply (rule conjI)
      using pre1 pre2
      using ddt.lts_union_correct(2) apply fastforce
      using pre1 by simp
  }
  {
    fix x1g x2g x2b x2c \<sigma> \<sigma>'
        x1a x2 x' x1e x2d x x1c it
    fix x2e :: "'a option \<Rightarrow> ('a \<times> 'a) list option"
    fix x2a :: "'a option \<Rightarrow> 'a set option"
    fix x1f :: "(('a \<times> 'a) list) option"
    fix x1b :: "'a set option"
    fix x1d :: "'q"
    fix x2f :: "'q"
    fix x1 :: "'q"
    fix x2b :: "'q" 
    assume x1a_def: "x1a = (x1b, x2a)"
       and \<sigma>_def: "\<sigma>' = (x1c, x2c)"
       and x2_def: "x2 = (x1a, x2b)"
       and x'_def: "x' = (x1, x2)"
       and x1e_def: "x1e = (x1f, x2e)"
       and x2d_def: "x2d = (x1e, x2f)"
       and x_def: "x = (x1d, x2d)"
       and x1f_nNone: "x1f \<noteq> None"
       and x1b_nNone: "x1b \<noteq> None"
       and \<sigma>\<sigma>': "(\<sigma>, \<sigma>')
       \<in> {(c, a).
           a = (case c of (D1, D2) \<Rightarrow> (interval_to_set_prod ` ddt.\<alpha> D1, ssd.\<alpha> D2)) \<and>
           (case c of
            (D1, D2) \<Rightarrow>
              ddt.invar D1 \<and>
              (\<forall>(q, \<alpha>, q')\<in>ddt.\<alpha> D1. canonicalIs \<alpha>) \<and> ssd.invar D2)}"
      and \<sigma>_def: "\<sigma> = (x1g, x2g)"
      and \<sigma>'_def: "\<sigma>' = (x1c, x2c)"
      and xx': "x' =
       (case x of
        (q, xa, xb) \<Rightarrow>
          (case xa of
           (\<alpha>, f) \<Rightarrow>
             \<lambda>q'. (q, (if \<alpha> = None then None else Some (semIs (the \<alpha>)), ft f), q'))
           xb)"
      and xin: "x \<in> it"
      and itin: "it \<subseteq> {t. t \<in> dt.\<alpha> T1}"
    from xx' x_def x'_def x2d_def x2_def x1a_def x1e_def
    have x2aeqx2e: "x2a = ft x2e"
      by simp
    from \<sigma>\<sigma>' \<sigma>_def \<sigma>'_def
    have c1: "((x1g, x2g), x1c, x2c) \<in> br Dddt\<alpha> Dddtinvar"
      unfolding br_def Dddt\<alpha>_def Dddtinvar_def
      by simp

    from x2aeqx2e F_ok
    have c2: "\<forall>\<alpha> \<alpha>'. \<alpha>' = semIs \<alpha> \<longrightarrow> (F x2e \<alpha> = None) = (F' x2a \<alpha>' = None)"
      by auto
    from x_def x2d_def x1e_def x'_def x2_def x1a_def xx' x1f_nNone x1b_nNone
    have c3: "canonicalIs (the x1f) \<and> the x1b = semIs (the x1f)"
      apply simp
      using itin xin T_ok
      by force

    from F_ok xx' x_def x'_def x2d_def x2_def x1a_def x1e_def
    have c4: "\<forall>\<alpha>. canonicalIs \<alpha> \<and> F x2e \<alpha> \<noteq> None \<longrightarrow> canonicalIs (the (F x2e \<alpha>))"
      by (simp add: F_ok)

    from ft_ok ft_ok' x2aeqx2e F_ok
    have c5: "\<forall>\<alpha> \<alpha>'. \<alpha>' = semIs \<alpha> \<and> F x2e \<alpha> \<noteq> None \<longrightarrow> 
                    semIs (the (F x2e \<alpha>)) = the (F' x2a \<alpha>')"
      by force

    from fe_ok x2aeqx2e
    have c6: "\<forall>\<alpha> \<alpha>'. \<alpha>' = semIs \<alpha> \<longrightarrow> fe x2e \<alpha> = fe' x2a \<alpha>'"
      by auto

    from xx' x_def x2d_def x'_def x2_def x1e_def
    have "x1 = x1d \<and> x2b = x2f"
      by simp

    from T2_ok c1 c2 c3 c4 c5 c6 this
        subtrans_comp_correct[of T2' T2 x1g x2g x1c x2c 
                                  "the x1f" "the x1b" F x2e F' x2a fe fe' x1d x2f]
    have "subtrans_comp_imp x1d (the x1f) x2e x2f F fe T2 x1g x2g
  \<le> \<Down> (br Dddt\<alpha> Dddtinvar) (subtrans_comp x1 (the x1b) x2a x2b F' fe' T2' x1c x2c)"
      by auto
    from this
    show "subtrans_comp_imp x1d (the x1f) x2e x2f F fe T2 x1g x2g
       \<le> \<Down> {(c, a).
             a = (case c of (D1, D2) \<Rightarrow> (interval_to_set_prod ` ddt.\<alpha> D1, ssd.\<alpha> D2)) \<and>
             (case c of
              (D1, D2) \<Rightarrow>
                ddt.invar D1 \<and> (\<forall>(q, \<alpha>, q')\<in>ddt.\<alpha> D1. canonicalIs \<alpha>) \<and> ssd.invar D2)}
           (subtrans_comp x1 (the x1b) x2a x2b F' fe' T2' x1c x2c)"
      unfolding br_def Dddt\<alpha>_def Dddtinvar_def
      by simp
  }
  { 
    fix x1d :: 'q
    fix x2f :: 'q
    fix x1 x2b x x' x1a x1b x2a x2 x1e x1f x2e x2d 
    assume xx': "x' =
       (case x of
        (q, xa, xb) \<Rightarrow>
          (case xa of
           (\<alpha>, f) \<Rightarrow>
             \<lambda>q'. (q, (if \<alpha> = None then None else Some (semIs (the \<alpha>)), ft f), q'))
           xb)"
        and x1a_def: "x1a = (x1b, x2a)"
        and x2_def: "x2 = (x1a, x2b)"
        and x'_def: "x' = (x1, x2)"
        and x1e_def: "x1e = (x1f, x2e)"
        and x2d_def: "x2d = (x1e, x2f)"
        and x_def: "x = (x1d, x2d)"

    from xx' x'_def x2_def x1a_def x_def x2d_def 
    have xxeq: "x1d = x1 \<and> x2f = x2b"
      apply simp
      by (simp add: x1e_def)


    from Q_ok copy_tran_imp_correct[of Q' Q x1d x2f] xxeq
    show "copy_tran_imp x1d x2f Q \<le> \<Down> (br ssd.\<alpha> ssd.invar) (copy_tran x1 x2b Q')"
      by auto
  }
  {
    fix x1g x2g D2' x1c x2c D2'a \<sigma> \<sigma>'
    assume DD: "(D2', D2'a) \<in> br ssd.\<alpha> ssd.invar"
       and \<sigma>\<sigma>': "(\<sigma>, \<sigma>')
       \<in> {(c, a).
           a = (case c of (D1, D2) \<Rightarrow> (interval_to_set_prod ` ddt.\<alpha> D1, ssd.\<alpha> D2)) \<and>
           (case c of
            (D1, D2) \<Rightarrow>
              ddt.invar D1 \<and>
              (\<forall>(q, \<alpha>, q')\<in>ddt.\<alpha> D1. canonicalIs \<alpha>) \<and> ssd.invar D2)}"
       and \<sigma>'_def: "\<sigma>' = (x1c, x2c)"
       and \<sigma>_def: "\<sigma> = (x1g, x2g)"

    from \<sigma>\<sigma>' \<sigma>_def \<sigma>'_def
    have pre1: "x1c = interval_to_set_prod ` ddt.\<alpha> x1g \<and>
    x2c = ssd.\<alpha> x2g \<and>
    ddt.invar x1g \<and>
    (\<forall>x\<in>ddt.\<alpha> x1g. case x of (q, \<alpha>, q') \<Rightarrow> canonicalIs \<alpha>) \<and> ssd.invar x2g"
      by simp

    from DD
    have pre2: "D2'a = ssd.\<alpha> D2' \<and> ssd.invar D2'"
      unfolding br_def
      by simp
  
    show "((x1g, ssd.union x2g D2'), x1c, x2c \<union> D2'a)
       \<in> {(c, a).
           a = (case c of (D1, D2) \<Rightarrow> (interval_to_set_prod ` ddt.\<alpha> D1, ssd.\<alpha> D2)) \<and>
           (case c of
            (D1, D2) \<Rightarrow>
              ddt.invar D1 \<and> (\<forall>(q, \<alpha>, q')\<in>ddt.\<alpha> D1. canonicalIs \<alpha>) \<and> ssd.invar D2)}"
      apply simp
      apply (rule conjI)
      using pre1 apply simp
      apply (rule conjI)
      using pre1 pre2
       apply (simp add: ssd.union_correct(1))
      apply (rule conjI)
      using pre1 apply simp
      using pre1 pre2
      using ssd.union_correct(2) by auto
  }
qed

definition nft_states :: "'q_set \<times> ('a \<times> 'a) list \<times> 'dt \<times> 'q_set \<times> 'q_set \<Rightarrow> 'q_set" where
  "nft_states A = fst A"
lemma [simp]: "nft_states (Q, Sig, D, I, F) = Q" by (simp add: nft_states_def)

definition nft_alphabet :: "'q_set \<times> ('a \<times> 'a) list \<times> 'dt \<times> 'q_set \<times> 'q_set \<Rightarrow> ('a \<times> 'a) list" where
  "nft_alphabet A = fst (snd A)"
lemma [simp]: "nft_alphabet (Q, Sig, D, I, F) = Sig" by (simp add: nft_alphabet_def)

definition nft_trans :: "'q_set \<times> ('a \<times> 'a) list \<times> 'dt \<times> 'q_set \<times> 'q_set \<Rightarrow> 'dt" where
  "nft_trans A = (fst (snd (snd A)))"
lemma [simp]: "nft_trans (Q, Sig, D, I, F) = D" by (simp add: nft_trans_def)

definition nft_initial :: "'q_set \<times> ('a \<times> 'a) list \<times> 'dt \<times> 'q_set \<times> 'q_set \<Rightarrow> 'q_set" where
  "nft_initial A = fst (snd (snd (snd  A)))"
lemma [simp]: "nft_initial (Q, Sig, D, I, F) = I" by (simp add: nft_initial_def)

definition nft_accepting :: "'q_set \<times> ('a \<times> 'a) list \<times> 'dt \<times> 'q_set \<times> 'q_set \<Rightarrow> 'q_set" where
  "nft_accepting A = snd (snd (snd (snd  A)))"
lemma [simp]: "nft_accepting (Q, Sig, D, I, F) = F" by (simp add: nft_accepting_def)


definition productT_impl where
  "productT_impl \<T> \<A> F fe = do {
    Q \<leftarrow> prods_imp (nft_states \<T>) (nfa_states \<A>);
    S \<leftarrow> RETURN (nft_alphabet \<T>);
    (D1, D2) \<leftarrow> trans_comp_imp F fe (nft_trans \<T>) (nfa_trans \<A>) (nfa_states \<A>);
    I \<leftarrow> prods_imp (nft_initial \<T>) (nfa_initial \<A>);
    F \<leftarrow> prods_imp (nft_accepting \<T>) (nfa_accepting \<A>);
    RETURN (Q,S,D1,D2,I, F)
  }"


definition nfae_states :: "'qq_set \<times> ('a \<times> 'a) list \<times> 'ddt \<times> 'qqqq_set\<times> 'qq_set \<times> 'qq_set \<Rightarrow> 'qq_set" where
  "nfae_states A = fst A"
lemma [simp]: "nfae_states (Q, Sig, D, D', I, F) = Q" by (simp add: nfae_states_def)

definition nfae_alphabet :: "'qq_set \<times> ('a \<times> 'a) list \<times> 'ddt \<times> 'qqqq_set\<times> 'qq_set \<times> 'qq_set
                               \<Rightarrow> ('a \<times> 'a) list" where
  "nfae_alphabet A = fst (snd A)"
lemma [simp]: "nfae_alphabet (Q, Sig, D, D', I, F) = Sig" by (simp add: nfae_alphabet_def)


definition nfae_trans :: 
        "'qq_set \<times> ('a \<times> 'a) list \<times> 'ddt \<times> 'qqqq_set\<times> 'qq_set \<times> 'qq_set \<Rightarrow> 'ddt" where
  "nfae_trans A = (fst (snd (snd A)))"
lemma [simp]: "nfae_trans (Q, Sig, D, D', I, F) = D" by (simp add: nfae_trans_def)

definition nfae_trans_ep :: 
        "'qq_set \<times> ('a \<times> 'a) list \<times> 'ddt \<times> 'qqqq_set\<times> 'qq_set \<times> 'qq_set \<Rightarrow> 'qqqq_set" where
  "nfae_trans_ep A = (fst (snd (snd (snd A))))"
lemma [simp]: "nfae_trans_ep (Q, Sig, D, D', I, F) = D'" by (simp add: nfae_trans_ep_def)

definition nfae_initial :: 
    "'qq_set \<times> ('a \<times> 'a) list \<times> 'ddt \<times> 'qqqq_set\<times> 'qq_set \<times> 'qq_set \<Rightarrow> 'qq_set" where
  "nfae_initial A = fst (snd (snd (snd  (snd A))))"
lemma [simp]: "nfae_initial (Q, Sig, D, D', I, F) = I" by (simp add: nfae_initial_def)

definition nfae_accepting :: "'qq_set \<times> ('a \<times> 'a) list \<times> 'ddt \<times> 'qqqq_set\<times> 'qq_set \<times> 'qq_set 
              \<Rightarrow> 'qq_set" where
  "nfae_accepting A = snd (snd (snd (snd (snd A))))"
lemma [simp]: "nfae_accepting (Q, Sig, D, D', I, F) = F" by (simp add: nfae_accepting_def)


definition nfae_invar :: "'qq_set \<times> ('a \<times> 'a) list \<times> 'ddt \<times> 'qqqq_set\<times> 'qq_set \<times> 'qq_set \<Rightarrow> bool" where
  "nfae_invar A =
   (ss.invar (nfae_states A) \<and> 
    ddt.invar (nfae_trans A) \<and>
    ssd.invar (nfae_trans_ep A) \<and>
    ss.invar (nfae_initial A) \<and> 
    ss.invar (nfae_accepting A))"

fun interval_to_setq :: "('q \<times> 'q) \<times> ('a \<times> 'a) list \<times> ('q \<times> 'q) \<Rightarrow> 
                        ('q \<times> 'q) \<times> 'a set \<times> ('q \<times> 'q)"  where
    "interval_to_setq (q, s, q') = (q, semIs s, q')"

definition nfae_\<alpha> :: "'qq_set \<times> ('a \<times> 'a) list \<times> 'ddt \<times> 'qqqq_set\<times> 'qq_set \<times> 'qq_set
                           \<Rightarrow> ('q \<times> 'q, 'a) NFAe_rec" 
  where
  "nfae_\<alpha> A =
   \<lparr> \<Q>e = ss.\<alpha> (nfae_states A),   
     \<Sigma>e = semIs (nfae_alphabet A),
     \<Delta>e = interval_to_setq ` (ddt.\<alpha> (nfae_trans A)),
     \<Delta>e' = ssd.\<alpha> (nfae_trans_ep A),
     \<I>e = ss.\<alpha> (nfae_initial A), 
     \<F>e = ss.\<alpha> (nfae_accepting A) \<rparr>"

lemma productT_impl_correct:
  fixes ft :: "('a option \<Rightarrow> ('a \<times> 'a) list option) \<Rightarrow> 'a option \<Rightarrow> 'a set option"
  assumes Tstate_ok: "\<Q>T \<T>' = s.\<alpha> (nft_states \<T>) \<and> s.invar (nft_states \<T>)"
      and Astate_ok: "\<Q> \<A>' = s.\<alpha> (nfa_states \<A>) \<and> s.invar (nfa_states \<A>)"
      and alphabet_ok: "\<Sigma>T \<T>' = semIs (nft_alphabet \<T>) \<and> canonicalIs (nft_alphabet \<T>)"
      and tran_ok: "\<Delta>T \<T>' =
       (\<lambda>(q, (\<alpha>, f), q').
           (q, (if \<alpha> = None then None else Some (semIs (the \<alpha>)), ft f), q')) `
       dt.\<alpha> (nft_trans \<T>) \<and>
       (\<forall>(q, (\<alpha>, f), q')\<in>dt.\<alpha> (nft_trans \<T>). \<alpha> \<noteq> None \<longrightarrow> canonicalIs (the \<alpha>))"
      and ft_ok: "inj_on ft {f| q \<alpha>' f q'. (q, (\<alpha>', f), q') \<in> dt.\<alpha> (nft_trans \<T>)}"
      and ft_ok': "\<forall>f\<in>{f| q \<alpha>' f q'. (q, (\<alpha>', f), q') \<in> dt.\<alpha> (nft_trans \<T>)}.
          (f None = None) = (ft f None = None) \<and>
          (f None \<noteq> None \<longrightarrow>
           canonicalIs (the (f None)) \<and> semIs (the (f None)) = the (ft f None)) \<and>
          (\<forall>\<alpha>. (f (Some \<alpha>) = None) = (ft f (Some \<alpha>) = None) \<and>
                (f (Some \<alpha>) \<noteq> None \<longrightarrow>
                 canonicalIs (the (f (Some \<alpha>))) \<and>
                 semIs (the (f (Some \<alpha>))) = the (ft f (Some \<alpha>))))"
      and tranA_ok: "\<Delta> \<A>' = interval_to_set ` d.\<alpha> (nfa_trans \<A>) \<and>
       (\<forall>(q, \<alpha>, q')\<in>d.\<alpha> (nfa_trans \<A>). canonicalIs \<alpha>)"
      and F_ok: "\<forall>\<alpha> \<alpha>' f f'.
          \<alpha>' = semIs \<alpha> \<and> f' = ft f \<longrightarrow>
          (F f \<alpha> = None) = (F' f' \<alpha>' = None) \<and>
          (F f \<alpha> \<noteq> None \<longrightarrow>
           canonicalIs (the (F f \<alpha>)) \<and> semIs (the (F f \<alpha>)) = the (F' f' \<alpha>'))"
      and fe_ok: "\<forall>\<alpha> \<alpha>' f f'. \<alpha>' = semIs \<alpha> \<and> f' = ft f \<longrightarrow> fe f \<alpha> = fe' f' \<alpha>'"
      and IT_ok: "\<I>T \<T>' = s.\<alpha> (nft_initial \<T>) \<and> s.invar (nft_initial \<T>)"
      and IA_ok: "\<I> \<A>' = s.\<alpha> (nfa_initial \<A>) \<and> s.invar (nfa_initial \<A>)"
      and FT_ok: "\<F>T \<T>' = s.\<alpha> (nft_accepting \<T>) \<and> s.invar (nft_accepting \<T>)"
      and FA_ok: "\<F> \<A>' = s.\<alpha> (nfa_accepting \<A>) \<and> s.invar (nfa_accepting \<A>)"
  shows "productT_impl \<T> \<A> F fe \<le> \<Down> (br nfae_\<alpha> nfae_invar) 
         (productT_imp \<T>' \<A>' F' fe')"
  unfolding productT_impl_def productT_imp_def
  apply (refine_rcg)
  apply (subgoal_tac "prods_imp (nft_states \<T>) (nfa_states \<A>)
    \<le> \<Down> (br ss.\<alpha> ss.invar) (prods (\<Q>T \<T>') (NFA_set_interval.NFA_rec.\<Q> \<A>'))")
  apply assumption
  using Tstate_ok Astate_ok prods_imp_correct
  apply fastforce  
  apply (subgoal_tac "(nft_alphabet \<T>, \<Sigma>T \<T>') \<in> (br semIs (\<lambda> x. canonicalIs x))")
  apply assumption
  unfolding br_def
  apply simp
  using alphabet_ok apply simp
  apply (subgoal_tac "trans_comp_imp F fe (nft_trans \<T>) (nfa_trans \<A>) (nfa_states \<A>)
       \<le> \<Down> (br Dddt\<alpha> Dddtinvar)
           (Transducer.trans_comp F' fe' (\<Delta>T \<T>') (NFA_set_interval.NFA_rec.\<Delta> \<A>') 
              (NFA_set_interval.NFA_rec.\<Q> \<A>'))")
  apply assumption
  apply (rule trans_comp_imp_correct[of "\<Delta>T \<T>'" ft "nft_trans \<T>" "\<Q> \<A>'" "nfa_states \<A>"
                                "\<Delta> \<A>'" "nfa_trans \<A>" F F' fe fe'])
  using tran_ok 
  apply force
  using ft_ok apply force
  using ft_ok' apply force
  using Astate_ok apply force
  using tranA_ok apply force
  using F_ok apply force
  using fe_ok apply force
  apply (subgoal_tac "prods_imp (nft_initial \<T>) (nfa_initial \<A>)
       \<le> \<Down> (br ss.\<alpha> ss.invar)
           (prods (\<I>T \<T>') (NFA_set_interval.NFA_rec.\<I> \<A>'))")
  apply assumption
  using prods_imp_correct[of "\<I>T \<T>'" "nft_initial \<T>" "\<I> \<A>'" "nfa_initial \<A>"]
        IT_ok IA_ok
  apply force
  apply (subgoal_tac "prods_imp (nft_accepting \<T>) (nfa_accepting \<A>)
       \<le> \<Down> (br ss.\<alpha> ss.invar)
           (prods (\<F>T \<T>') (NFA_set_interval.NFA_rec.\<F> \<A>'))")
  apply assumption
  using prods_imp_correct[of "\<F>T \<T>'" "nft_accepting \<T>" "\<F> \<A>'" "nfa_accepting \<A>"]
        FT_ok FA_ok
  apply force
  unfolding br_def Dddt\<alpha>_def Dddtinvar_def
  apply simp
  unfolding nfae_\<alpha>_def nfae_invar_def
  apply simp
  by force

schematic_goal productT_impl_code:
  fixes D_it1 :: "('q, 'qq_set) set_iterator"
    and D_it2 :: "('q, 'qq_set) set_iterator"
    and D_it3 :: "('q \<times> 'a TlabelI \<times> 'q, 'ddt \<times> 'qqqq_set) set_iterator"
    and D_it4 :: "('q, 'qqqq_set) set_iterator"
    and D_it5 :: "('q, 'ddt) set_iterator"
    and D_it6 :: "('q \<times> ('a \<times> 'a) list \<times> 'q, 'ddt \<times> 'qqqq_set) set_iterator"
    and D_it7 :: "('q, 'qq_set) set_iterator"
    and D_it8 :: "('q, 'qq_set) set_iterator"
    and D_it9 :: "('q, 'qq_set) set_iterator"
    and D_it10 :: "('q, 'qq_set) set_iterator"
assumes D_it1_OK [rule_format, refine_transfer]: 
         "set_iterator D_it1 {e. e \<in> s.\<alpha> (nft_states \<T>)}"
    and D_it2_OK [rule_format, refine_transfer]: 
         "set_iterator D_it2 {e. e \<in> s.\<alpha> (nfa_states \<A>)}"
    and D_it3_OK [rule_format, refine_transfer]: 
         "set_iterator D_it3 {t. t \<in> dt.\<alpha> (nft_trans \<T>)}"
    and D_it4_OK [rule_format, refine_transfer]: 
         "set_iterator D_it4 {e. e \<in> s.\<alpha> (nfa_states \<A>)}"
    and D_it5_OK [rule_format, refine_transfer]: 
         "set_iterator D_it5 {e. e \<in> s.\<alpha> (nfa_states \<A>)}"
    and D_it6_OK [rule_format, refine_transfer]: 
         "set_iterator D_it6 {t. t \<in> d.\<alpha> (nfa_trans \<A>)}"
    and D_it7_OK [rule_format, refine_transfer]: 
         "set_iterator D_it7 {e. e \<in> s.\<alpha> (nft_initial \<T>)}"
    and D_it8_OK [rule_format, refine_transfer]: 
         "set_iterator D_it8 {e. e \<in> s.\<alpha> (nfa_initial \<A>)}"
    and D_it9_OK [rule_format, refine_transfer]: 
         "set_iterator D_it9 {e. e \<in> s.\<alpha> (nft_accepting \<T>)}"
    and D_it10_OK [rule_format, refine_transfer]: 
         "set_iterator D_it10 {e. e \<in> s.\<alpha> (nfa_accepting \<A>)}"
  shows "RETURN ?f \<le> productT_impl \<T> \<A> F fe"
  unfolding productT_impl_def
            prods_imp_def
            trans_comp_imp_def
            copy_tran_imp_def
            copy_tran'_imp_def
            subtrans_comp_imp_def
  apply (unfold split_def snd_conv fst_conv prod.collapse)
  apply (rule refine_transfer | assumption | erule conjE)+
  done


definition productT_impl_code where 
    "productT_impl_code
                D_it1 D_it2 D_it3 D_it4 D_it5 D_it6 
                D_it7 D_it8 D_it9 D_it10 \<T> \<A> F fe = 
       (let x = D_it1 (\<lambda>_. True)
            (\<lambda>x \<sigma>. Let (D_it2 (\<lambda>_. True) (\<lambda>xa. ss.ins (x, xa)) (ss.empty ()))
                    (ss.union \<sigma>))
            (ss.empty ());
       xa = nft_alphabet \<T>;
       xb = D_it3 (\<lambda>_. True)
             (\<lambda>xb \<sigma>.
                 if fst (fst (snd xb)) = None
                 then if snd (fst (snd xb)) None = None
                      then let xc = D_it4 (\<lambda>_. True)
                                     (\<lambda>xc. ssd.ins ((fst xb, xc), snd (snd xb), xc))
                                     (ssd.empty ())
                           in (fst \<sigma>, ssd.union (snd \<sigma>) xc)
                      else let xc = D_it5 (\<lambda>_. True)
                                     (\<lambda>xc. ddt.add (fst xb, xc)
(the (snd (fst (snd xb)) None)) (snd (snd xb), xc))
                                     ddt.empty
                           in (ddt.union (fst \<sigma>) xc, snd \<sigma>)
                 else D_it6 (\<lambda>_. True)
                       (\<lambda>xc \<sigma>'.
                           if nemptyIs
                               (intersectIs (the (fst (fst (snd xb)))) (fst (snd xc)))
                           then let xd = if F (snd (fst (snd xb)))
 (intersectIs (the (fst (fst (snd xb)))) (fst (snd xc))) \<noteq>
None
                                         then ddt.add (fst xb, fst xc)
   (the (F (snd (fst (snd xb)))
          (intersectIs (the (fst (fst (snd xb)))) (fst (snd xc)))))
   (snd (snd xb), snd (snd xc)) (fst \<sigma>')
                                         else fst \<sigma>'
                                in Let (if fe (snd (fst (snd xb)))
(intersectIs (the (fst (fst (snd xb)))) (fst (snd xc)))
                                        then ssd.ins
  ((fst xb, fst xc), snd (snd xb), snd (snd xc)) (snd \<sigma>')
                                        else snd \<sigma>')
                                    (Pair xd)
                           else \<sigma>')
                       \<sigma>)
             (ddt.empty, ssd.empty ());
       xc = D_it7 (\<lambda>_. True)
             (\<lambda>xc \<sigma>.
                 Let (D_it8 (\<lambda>_. True) (\<lambda>xd. ss.ins (xc, xd)) (ss.empty ()))
                  (ss.union \<sigma>))
             (ss.empty ());
       xd = D_it9 (\<lambda>_. True)
             (\<lambda>xd \<sigma>.
                 Let (D_it10 (\<lambda>_. True) (\<lambda>xe. ss.ins (xd, xe)) (ss.empty ()))
                  (ss.union \<sigma>))
             (ss.empty ())
   in (x, xa, fst xb, snd xb, xc, xd))"

definition nfa_construct_interval_aux ::
  "'q_set \<times> ('a \<times> 'a) list \<times> 'dt \<times> 'q_set \<times> 'q_set \<Rightarrow> 
   'q \<times> (('a \<times> 'a) list option \<times> ('a option \<Rightarrow> ('a \<times> 'a) list option)) \<times> 'q \<Rightarrow> 
   'q_set \<times> ('a \<times> 'a) list \<times> 'dt \<times> 'q_set \<times> 'q_set" where 
   "nfa_construct_interval_aux = (\<lambda>(Q, Sig, D, I, F) (q1, (l, f), q2).
    (s.ins q1 (s.ins q2 Q), Sig, 
     dt.add q1 (l, f) q2 D,
     I, F))"

fun nft_construct_interval  where
   "nft_construct_interval (QL, SigL, DL, IL, FL) =
    foldl nfa_construct_interval_aux 
     (s.from_list (QL @ IL @ FL),
      SigL,
      dt.empty,
      s.from_list IL,
      s.from_list FL) DL"

end

 


end 












