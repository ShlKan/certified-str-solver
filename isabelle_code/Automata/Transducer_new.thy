
theory Transducer_new

imports Main Epsilon_elim

begin



type_synonym ('a, 'b) Tlabel = "('a option \<Rightarrow> 'b set option)"
 

type_synonym ('q, 'a, 'c) LTTS = 
            "('q \<times> ('a set option \<times> 'c) \<times> 'q) set"

record ('q, 'a, 'b, 'c) NFT =
  \<Q>T :: "'q set"           (* "The set of states" *)
  \<Delta>T :: " ('q, 'a, 'c) LTTS"   (* "The transition relation" *)
  \<I>T :: "'q set"            (* "The set of initial states *)
  \<F>T :: "'q set"           (* "The set of final states *)
  \<M> :: "'c \<Rightarrow> ('a, 'b)  Tlabel"

locale NFT_wf =  
  fixes \<T> :: "('q, 'a, 'b, 'c) NFT" 
  assumes \<Delta>_consistent: "\<And>q \<sigma> q' f. (q, (\<sigma>, f), q') \<in> \<Delta>T \<T> 
                \<Longrightarrow> (q \<in> \<Q>T \<T>) \<and> (q' \<in> \<Q>T \<T>)"
      and \<I>_consistent: "\<I>T \<T> \<subseteq> \<Q>T \<T>"
      and \<F>_consistent: "\<F>T \<T> \<subseteq> \<Q>T \<T>"
      and finite_\<Q>: "finite (\<Q>T \<T>)"



fun Edge_path :: "('q, 'a, 'b) LTTS \<Rightarrow> 'q \<Rightarrow> (('a set option \<times> 'b) \<times> 'q) list \<Rightarrow> bool" where
    "Edge_path Trans q [] = True" |
    "Edge_path Trans q ((\<alpha>, q') # pl) = (((q, \<alpha>, q') \<in> Trans) 
                                          \<and> Edge_path Trans q' pl)"



fun inputE :: "('a option \<times> 'b option) list \<Rightarrow> 'a list" where
  "inputE [] = []" |
  "inputE ((Some a, _) # l) = a # (inputE l)" |
  "inputE ((None, _) # l) = (inputE l)" 

lemma inputE_concat: "inputE (\<pi> @ \<pi>') = inputE \<pi> @ inputE \<pi>'"
  apply (induction \<pi> rule: inputE.induct)
  apply simp
  by auto

fun outputE :: "('a option \<times> 'b option) list \<Rightarrow> 'b list" where
  "outputE [] = []" |
  "outputE ((_, Some a) # l) = a # (outputE l)" |
  "outputE ((_, None) # l) = (outputE l)" 

lemma outputE_concat: "outputE (\<pi> @ \<pi>') = outputE \<pi> @ outputE \<pi>'"
  apply (induction \<pi> rule: outputE.induct)
  apply simp
  by auto

fun matche where
  "matche None None = True" |
  "matche (Some s) (Some e) = (e \<in> s)" |
  "matche _ _ = False"

fun matcht where
  "matcht (s,i) (a, b) M = ((matche s a) \<and> (matche ((M i) a) b))"


fun LTTS_reachable :: "('q, 'a, 'c) LTTS \<Rightarrow> ('c \<Rightarrow> ('a, 'b) Tlabel) 
                        \<Rightarrow> 'q \<Rightarrow> ('a option \<times> 'b option) list \<Rightarrow> 'q \<Rightarrow> bool" where
  "LTTS_reachable Trans M q [] q'= (q = q')" |
  "LTTS_reachable Trans M q (s # w) q' = 
      (\<exists> q'' \<alpha>. (q, \<alpha>, q'') \<in> Trans \<and> matcht \<alpha> s M \<and> 
                LTTS_reachable Trans M q'' w q')"

lemma LTTS_reachable_concat:
    fixes q \<pi> q' \<pi>'' q''
  assumes fst_part: "LTTS_reachable Trans M q \<pi> q'"
      and snd_part: "LTTS_reachable Trans M q' \<pi>' q''"
    shows "LTTS_reachable Trans M q (\<pi> @ \<pi>') q''"
  using fst_part snd_part
  apply (induction \<pi> arbitrary: q)
  apply simp
  by auto

  
definition domainT where
  "domainT \<T> M = {inputE \<pi> | q \<pi> q'. q \<in> \<I>T \<T> \<and> 
                           q' \<in> \<F>T \<T> \<and> LTTS_reachable (\<Delta>T \<T>) M q \<pi> q'}"

definition codomainT  :: "('q, 'a, 'b, 'c) NFT \<Rightarrow> ('c \<Rightarrow> ('a, 'b) Tlabel) \<Rightarrow> 'b list set" where
  "codomainT \<T> M = {outputE \<pi> | q \<pi> q'. q \<in> \<I>T \<T> \<and> 
                           q' \<in> \<F>T \<T> \<and> LTTS_reachable (\<Delta>T \<T>) M q \<pi> q'}"

definition outputL :: "('q, 'a, 'b, 'c) NFT \<Rightarrow> ('c \<Rightarrow> ('a, 'b) Tlabel) \<Rightarrow> 
                               ('q, 'a) NFA_rec \<Rightarrow> 'b list set" where
  "outputL \<T> M \<A> = {outputE \<pi> | \<pi> q q'. q \<in> \<I>T \<T> \<and> q' \<in> \<F>T \<T> \<and> 
                                LTTS_reachable (\<Delta>T \<T>) M q \<pi> q' \<and>
                                inputE \<pi> \<in> \<L> \<A>}" 

definition productT :: "('q, 'a, 'b, 'c) NFT \<Rightarrow> ('q, 'a) NFA_rec \<Rightarrow> 
                        (('a option \<Rightarrow> 'b set option) \<Rightarrow> 'a set \<Rightarrow> 'b set option) \<Rightarrow> 
                         ('q \<times> 'q, 'b) NFAe_rec" where
  "productT \<T> \<A> F = \<lparr> 
      \<Q>e = \<Q>T \<T> \<times> \<Q> \<A>,
      \<Delta>e = {((p,p'), the (((\<M> \<T>) f) None), (q,p')) 
              | p p' q f. p' \<in> \<Q> \<A> \<and>
                   ((p, (None, f), q) \<in> \<Delta>T \<T> \<and> (\<exists> So. ((\<M> \<T>) f) None = Some So))}
            \<union>
            { ((p,p'), the (F ((\<M> \<T>) f) (\<sigma>1 \<inter> \<sigma>2)), (q,q')) 
                  | p p' \<sigma>1 \<sigma>2 q q' f.
               (p, (Some \<sigma>1, f), q) \<in> \<Delta>T \<T> \<and> (p', \<sigma>2, q') \<in> \<Delta> \<A> \<and>
                     \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists> So. F ((\<M> \<T>) f) (\<sigma>1 \<inter> \<sigma>2) = Some So)},
      \<Delta>e' = {((p,p'), (q,p')) 
              | p p' q f. p' \<in> \<Q> \<A> \<and>
                   ((p, (None, f), q) \<in> \<Delta>T \<T> \<and> (((\<M> \<T>) f) None = None))}
            \<union>
            { ((p,p'), (q,q')) 
                  | p p' \<sigma>1 \<sigma>2 q q' f.
               (p, (Some \<sigma>1, f), q) \<in> \<Delta>T \<T> \<and> (p', \<sigma>2, q') \<in> \<Delta> \<A> \<and>
                     \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists> x \<in> (\<sigma>1 \<inter> \<sigma>2). ((\<M> \<T>) f) (Some x) = None)},
      \<I>e = \<I>T \<T> \<times> \<I> \<A>,
      \<F>e = \<F>T \<T> \<times> \<F> \<A> 
  \<rparr>"

lemma productT_wf:
  fixes \<T> \<A> F
  assumes wfTA: "NFT_wf \<T> \<and> NFA \<A>"
  shows "NFAe (productT \<T> \<A> F)"
  unfolding productT_def NFAe_def
  apply simp
  using wfTA
  unfolding NFT_wf_def NFA_def
  apply simp
  by (meson Sigma_mono)

lemma productT_correct:
  fixes \<T> \<A> F
  assumes F_ok1: "\<forall> f s. (\<forall> e \<in> s. f (Some e) = None) \<longleftrightarrow> F f s = None"
      and F_ok2: "\<forall> f s. F f s \<noteq> None \<longrightarrow> 
                      F f s = Some (\<Union> {S| e S. e \<in> s \<and> 
                                                   f (Some e) = Some S})"
      and wfTA: "NFT_wf \<T> \<and> NFA \<A>"
    shows "\<L>e (productT \<T> \<A> F) = outputL \<T> (\<M> \<T>) \<A>"
  unfolding \<L>e_def outputL_def NFAe_accept_def
  apply simp
  apply rule
  apply rule 
proof 
  {
    fix x
    assume xin:"x \<in> {w. \<exists>q\<in>\<I>e (productT \<T> \<A> F).
                        \<exists>x\<in>\<F>e (productT \<T> \<A> F).
                          LTS_is_reachable_epsilon (\<Delta>e (productT \<T> \<A> F))
                            (\<Delta>e' (productT \<T> \<A> F)) q w x}"
    from this obtain q q'
      where w_def: "q \<in> \<I>e (productT \<T> \<A> F) \<and> q' \<in>\<F>e (productT \<T> \<A> F) \<and>
                    LTS_is_reachable_epsilon (\<Delta>e (productT \<T> \<A> F)) 
                    (\<Delta>e' (productT \<T> \<A> F)) q x q'"
      by auto
    from this 
    have w_def': "q \<in> \<Q>e  (productT \<T> \<A> F) \<and> q' \<in> \<Q>e  (productT \<T> \<A> F) \<and>
                  LTS_is_reachable_epsilon (\<Delta>e (productT \<T> \<A> F)) 
                              (\<Delta>e' (productT \<T> \<A> F)) q x q'"
      unfolding productT_def
      apply simp
      using wfTA 
      unfolding NFT_wf_def NFA_def
      by force

    from w_def 
    have fstqI: "fst q \<in> \<I>T \<T> \<and> fst q' \<in> \<F>T \<T>"
      unfolding productT_def
      apply simp
      by fastforce
    from w_def' 
    have "\<exists> \<pi>. x = outputE \<pi> \<and> LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) (fst q) \<pi> (fst q') 
                \<and> LTS_is_reachable (\<Delta> \<A>) (snd q) (inputE \<pi>) (snd q')"
      apply (induction x arbitrary: q)
      apply simp
    proof -
      {
        fix q
        assume qin: "q \<in> \<Q>e (productT \<T> \<A> F) \<and>
         q' \<in> \<Q>e (productT \<T> \<A> F) \<and>
         (\<exists>l. l \<noteq> [] \<and>
              epsilon_reach l (\<Delta>e' (productT \<T> \<A> F)) \<and> hd l = q \<and> last l = q')"

        from this obtain q1 q1' q2 q2' where
        q12_def: "q = (q1, q1') \<and> q' = (q2, q2')"
          by fastforce

        from qin obtain l
          where l_def: "l \<noteq> [] \<and> epsilon_reach l (\<Delta>e' (productT \<T> \<A> F)) \<and> 
                     hd l = q \<and> last l = q'" by auto
       from this q12_def
       have "\<exists>\<pi>. [] = outputE \<pi> \<and>
                LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) q1 \<pi> q2 \<and> 
                    LTS_is_reachable (\<Delta> \<A>) q1' (inputE \<pi>) q2'"
          apply (induction l arbitrary: q q1 q1')
          apply simp
        proof -
          fix a l q q1 q1'
          assume ind_hyp: "\<And>q q1 q1'.
           l \<noteq> [] \<and>
           epsilon_reach l (\<Delta>e' (productT \<T> \<A> F)) \<and> hd l = q \<and> last l = q' \<Longrightarrow>
           q = (q1, q1') \<and> q' = (q2, q2') \<Longrightarrow>
           \<exists>\<pi>. [] = outputE \<pi> \<and>
               LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) q1 \<pi> q2 \<and>
               LTS_is_reachable (NFA_rec.\<Delta> \<A>) q1' (inputE \<pi>)
                q2'"
             and p1: " a # l \<noteq> [] \<and>
       epsilon_reach (a # l) (\<Delta>e' (productT \<T> \<A> F)) \<and>
       hd (a # l) = q \<and> last (a # l) = q'"
             and p2: "q = (q1, q1') \<and> q' = (q2, q2')"
          show "\<exists>\<pi>. [] = outputE \<pi> \<and> LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) q1 \<pi> q2 \<and> 
                    LTS_is_reachable (\<Delta> \<A>) q1' (inputE \<pi>) q2'"
          proof (cases "l = []")
            case True
            from this p1 p2
            have eq_qq': "(q1, q1') = (q2, q2')" by auto
            from this
            have "[] = outputE [] \<and> LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) q1 [] q2 \<and> 
                    LTS_is_reachable (\<Delta> \<A>) q1' (inputE []) q2'"
              by auto 
            then show ?thesis by fastforce
          next
            case False
            from False obtain q3 l' where
            q3l'_def: "l = q3 # l'" 
              using list.exhaust by blast
            from p1 this p2
            have qq3in: "(q, q3) \<in> (\<Delta>e' (productT \<T> \<A> F)) \<and> 
                        epsilon_reach (q3#l') (\<Delta>e' (productT \<T> \<A> F))"
              apply (simp add: p1 p2) by auto
              
            from ind_hyp[of q3 "fst q3" "snd q3"]
            have "\<exists>\<pi>. [] = outputE \<pi> \<and>
                     LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) (fst q3) \<pi> q2 \<and>
                      LTS_is_reachable (\<Delta> \<A>) (snd q3) (inputE \<pi>) q2'"
              using p1 p2 q3l'_def by auto
            from this obtain \<pi> where
            \<pi>_def: "[] = outputE \<pi> \<and>
               LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) (fst q3) \<pi> q2 \<and>
                  LTS_is_reachable (\<Delta> \<A>) (snd q3) (inputE \<pi>) q2'"
              by auto
           
            from qq3in 
            have "(q, q3) \<in> \<Delta>e' (productT \<T> \<A> F)" by auto
            from this
            have "(\<exists> f. (fst q, (None, f), fst q3) \<in> \<Delta>T \<T> \<and> ((\<M> \<T>) f) None = None \<and>
                        snd q = snd q3)\<or>
                  (\<exists> \<sigma>1 f \<sigma>2. (fst q, (Some \<sigma>1, f), fst q3) \<in> \<Delta>T \<T> \<and>
                        (snd q, \<sigma>2, snd q3) \<in> \<Delta> \<A> \<and>
                               \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> 
                                  (\<exists>x\<in>\<sigma>1 \<inter> \<sigma>2. ((\<M> \<T>) f) (Some x) = None))"
              unfolding productT_def
              apply simp 
              by (metis fst_conv snd_conv)
            
            from this obtain f1 f2 \<sigma>1 \<sigma>2 
              where f12\<sigma>12_def: 
                  "((fst q, (None, f1), fst q3) \<in> \<Delta>T \<T> \<and> 
                                ((\<M> \<T>) f1) None = None \<and> snd q = snd q3) \<or>
                   ((fst q, (Some \<sigma>1, f2), fst q3) \<in> \<Delta>T \<T> \<and> 
                        (snd q, \<sigma>2, snd q3) \<in> \<Delta> \<A> \<and>
                               \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> 
                                (\<exists> x \<in> (\<sigma>1 \<inter> \<sigma>2). ((\<M> \<T>) f2) (Some x) = None))"
              by blast
           
            show ?thesis
            proof (cases "(fst q, (None, f1), fst q3) \<in> \<Delta>T \<T> \<and> ((\<M> \<T>) f1) None = None 
                          \<and> snd q = snd q3")
              case True
              from \<pi>_def
              have s1: "[] = outputE ((None, None) # \<pi>)" by auto
              from True p2 LTTS_reachable.simps(2) 
                    [of "\<Delta>T \<T>" "\<M> \<T>" "fst q" "(None,None)" \<pi> q2] \<pi>_def
              have s2: "LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) q1 ((None, None) # \<pi>) q2"
                apply simp
                by force
              from True p2 \<pi>_def
              have s3: "LTS_is_reachable (\<Delta> \<A>) q1' 
                              (inputE ((None, None) # \<pi>)) q2'"
                by simp
              from s1 s2 s3
              show ?thesis by fastforce
            next
              case False
              from this f12\<sigma>12_def
              have False': "(fst q, (Some \<sigma>1, f2), fst q3) \<in> \<Delta>T \<T> 
                    \<and> (snd q, \<sigma>2, snd q3) \<in> \<Delta> \<A> \<and>
                     \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists> x \<in> (\<sigma>1 \<inter> \<sigma>2). (\<M> \<T>) f2 (Some x) = None)" by auto
              from this obtain a1  where
                a1a2_def: "a1 \<in> \<sigma>1 \<inter> \<sigma>2 \<and> (\<M> \<T>) f2 (Some a1) = None" by force
              from \<pi>_def
              have s1: "[] = outputE ((Some a1, None) # \<pi>)"
                by auto
              from False' p2 \<pi>_def f12\<sigma>12_def LTTS_reachable.simps(2)
                        [of "(\<Delta>T \<T>)" "(\<M> \<T>)" q1 
                        "(Some a1, None)" \<pi> q2] F_ok1
              have s2: "LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) q1 ((Some a1, None) # \<pi>) q2"
                apply simp               
                using IntD1 a1a2_def by fastforce
              from False' p2 \<pi>_def
              have s3: "LTS_is_reachable (\<Delta> \<A>) q1' 
                              (inputE ((Some a1, None) # \<pi>)) q2'"
                using a1a2_def by auto
              from s1 s2 s3
              show ?thesis by fastforce
            qed
          qed
        qed
        from this q12_def
        show "\<exists>\<pi>. [] = outputE \<pi> \<and>
             LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) (fst q) \<pi> (fst q') \<and>
             LTS_is_reachable (\<Delta> \<A>) (snd q) (inputE \<pi>) (snd q')"
          by auto
      }
      {
        fix a x q
        assume ind_hyp: "(\<And>q. q \<in> \<Q>e (productT \<T> \<A> F) \<and>
             q' \<in> \<Q>e (productT \<T> \<A> F) \<and>
             LTS_is_reachable_epsilon (\<Delta>e (productT \<T> \<A> F)) (\<Delta>e' (productT \<T> \<A> F)) q
              x q' \<Longrightarrow>
             \<exists>\<pi>. x = outputE \<pi> \<and>
                 LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) (fst q) \<pi> (fst q') \<and>
                 LTS_is_reachable (\<Delta> \<A>) (snd q) (inputE \<pi>) (snd q'))"
           and p1: "q \<in> \<Q>e (productT \<T> \<A> F) \<and>
                    q' \<in> \<Q>e (productT \<T> \<A> F) \<and>
                    LTS_is_reachable_epsilon (\<Delta>e (productT \<T> \<A> F)) 
                                      (\<Delta>e' (productT \<T> \<A> F)) q (a # x) q'"   

        from p1
        have "(\<exists> qi qj \<sigma>. epsilon_reachable q qi (\<Delta>e' (productT \<T> \<A> F)) \<and> 
              a \<in> \<sigma> \<and> (qi, \<sigma>, qj) \<in> (\<Delta>e (productT \<T> \<A> F)) \<and> 
              LTS_is_reachable_epsilon (\<Delta>e (productT \<T> \<A> F))
                                       (\<Delta>e' (productT \<T> \<A> F)) qj x q')"
          by auto
        from this obtain qi qj \<sigma> where
        qij\<sigma>_def: "epsilon_reachable q qi (\<Delta>e' (productT \<T> \<A> F)) \<and> 
              a \<in> \<sigma> \<and> (qi, \<sigma>, qj) \<in> (\<Delta>e (productT \<T> \<A> F)) \<and> 
              LTS_is_reachable_epsilon (\<Delta>e (productT \<T> \<A> F))
                                       (\<Delta>e' (productT \<T> \<A> F)) qj x q'"
          by auto
        from qij\<sigma>_def 
        have "epsilon_reachable q qi (\<Delta>e' (productT \<T> \<A> F))" by auto
        from this p1 obtain l where
        l_def: "l \<noteq> [] \<and> epsilon_reach l (\<Delta>e' (productT \<T> \<A> F)) \<and> 
                hd l = q \<and> last l = qi \<and> q \<in> \<Q>e (productT \<T> \<A> F)" 
                      unfolding epsilon_reachable_def by auto

        from this 
        have qiin:  "qi \<in> \<Q>e (productT \<T> \<A> F)"
          apply (induction l arbitrary: q)  
          apply simp
        proof -
          fix a l q
          assume ind_hyp: "(\<And>q. l \<noteq> [] \<and>
            epsilon_reach l (\<Delta>e' (productT \<T> \<A> F)) \<and>
            hd l = q \<and> last l = qi \<and> q \<in> \<Q>e (productT \<T> \<A> F) \<Longrightarrow>
            qi \<in> \<Q>e (productT \<T> \<A> F))"
             and p1: "a # l \<noteq> [] \<and>
           epsilon_reach (a # l) (\<Delta>e' (productT \<T> \<A> F)) \<and>
           hd (a # l) = q \<and> last (a # l) = qi \<and> q \<in> \<Q>e (productT \<T> \<A> F)"
          from p1 have qaeq: "a = q" by auto
          show "qi \<in> \<Q>e (productT \<T> \<A> F)"
          proof (cases "l = []")
          case True
            then show ?thesis 
              using p1 by auto
          next
            case False
            from this obtain l' q1 where
            lq1_def: "l = q1 # l'" 
              using clearjunk.cases by blast
            from p1 
            have e_reach1: "epsilon_reach l (\<Delta>e' (productT \<T> \<A> F))"
              by (metis epsilon_reach.elims(3) epsilon_reach.simps(3))
            from lq1_def p1 epsilon_reach.simps(3)
                      [of a q1 l' "\<Delta>e' (productT \<T> \<A> F)"]
            have cc1: "((a, q1) \<in> (\<Delta>e' (productT \<T> \<A> F)) 
                        \<and> epsilon_reach (q1 # l') (\<Delta>e' (productT \<T> \<A> F)))"
              by auto
            have cc0: "hd l = q1 \<and> last l = qi"
              using lq1_def p1 by auto
            from cc1 qaeq p1 productT_wf[OF wfTA, of F]
            have "q1 \<in> \<Q>e (productT \<T> \<A> F)"
              unfolding NFAe_def
              apply simp
              by (meson NFAe.\<Delta>'_consistent \<open>NFAe (productT \<T> \<A> F)\<close>)
            from this cc1 cc0 False ind_hyp[of q1] lq1_def qaeq
            show ?thesis  
              by auto
          qed
        qed

        from this qij\<sigma>_def
        have qjin: "qj \<in> \<Q>e (productT \<T> \<A> F)" 
          by (meson NFAe.\<Delta>_consistent productT_wf wfTA)

        from this ind_hyp[of qj]  qij\<sigma>_def
        have c1: "\<exists>\<pi>. x = outputE \<pi> \<and>
                  LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) (fst qj) \<pi> (fst q') \<and>
                  LTS_is_reachable (\<Delta> \<A>) (snd qj) (inputE \<pi>) (snd q')"
          using p1 by blast

        obtain l' where
        l'_def:  "l' \<noteq> [] \<and> epsilon_reach l' (\<Delta>e' (productT \<T> \<A> F))
                \<and> hd l' = q \<and> last l' = qi"
          using \<open>epsilon_reachable q qi (\<Delta>e' (productT \<T> \<A> F))\<close>
          using \<open>\<And>thesis. (\<And>l. l \<noteq> [] \<and> epsilon_reach l 
                (\<Delta>e' (productT \<T> \<A> F)) \<and> hd l = q \<and> 
                last l = qi \<and> q \<in> \<Q>e (productT \<T> \<A> F) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> 
          by blast
        from this
        have fst_half: "\<exists> \<pi>. [] = outputE \<pi> \<and>
           LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) (fst q) \<pi> (fst qi) \<and>
           LTS_is_reachable (\<Delta> \<A>) (snd q) (inputE \<pi>) (snd qi)"
           apply (induction l' arbitrary: q)
           apply simp
        proof -
          fix a l' q
          assume ind_hyp: "(\<And>q. l' \<noteq> [] \<and>
             epsilon_reach l' (\<Delta>e' (productT \<T> \<A> F)) \<and> hd l' = q \<and> last l' = qi \<Longrightarrow>
             \<exists>\<pi>. [] = outputE \<pi> \<and>
                 LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) (fst q) \<pi> (fst qi) \<and>
                 LTS_is_reachable (\<Delta> \<A>) (snd q) (inputE \<pi>) (snd qi))"
             and p1: "a # l' \<noteq> [] \<and>
                      epsilon_reach (a # l') (\<Delta>e' (productT \<T> \<A> F)) \<and>
                      hd (a # l') = q \<and> last (a # l') = qi"

          show "\<exists>\<pi>. [] = outputE \<pi> \<and>
                    LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>)  (fst q) \<pi> (fst qi) \<and>
                    LTS_is_reachable (\<Delta> \<A>) (snd q) (inputE \<pi>) (snd qi)"
          proof (cases "l' = []")
            case True
              then show ?thesis 
                by (metis LTS_is_reachable.simps(1) LTTS_reachable.simps(1) 
                          inputE.simps(1) last_ConsL list.sel(1)
                          outputE.simps(1) p1)
            next
              case False
              from this obtain a' l'' where 
              al'_def: "l' = a' # l''" 
                using clearjunk.cases by blast
              from p1
              have s1: "epsilon_reach l' (\<Delta>e' (productT \<T> \<A> F)) \<and> 
                        hd l' = a' \<and> last l' = qi " 
                by (simp add: al'_def)
              from s1 False ind_hyp[of a']
              have "\<exists>\<pi>. [] = outputE \<pi> \<and>
                    LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) (fst a') \<pi> (fst qi) \<and>
                    LTS_is_reachable (\<Delta> \<A>) (snd a') (inputE \<pi>) (snd qi)"
                by force
              from this
              obtain \<pi> where
              \<pi>_def: "[] = outputE \<pi> \<and>
                      LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) (fst a') \<pi> (fst qi) \<and>
                      LTS_is_reachable (\<Delta> \<A>) (snd a') (inputE \<pi>) (snd qi)"
                by auto
              from p1 al'_def
              have s2: "((a,a') \<in> (\<Delta>e' (productT \<T> \<A> F))
                         \<and> epsilon_reach (a' # l'') (\<Delta>e' (productT \<T> \<A> F)))"
                by auto

              from s2 
              have "(a, a') \<in> \<Delta>e' (productT \<T> \<A> F)" by auto
              from this
          have branch: "(\<exists> f. snd a' \<in> \<Q> \<A> \<and> (fst a, (None, f), fst a') \<in> \<Delta>T \<T> 
                 \<and> (\<M> \<T>) f None = None \<and> snd a = snd a') \<or> 
                (\<exists> \<sigma>1 \<sigma>2 f. (fst a, (Some \<sigma>1, f), fst a') \<in> \<Delta>T \<T> \<and>
                (snd a, \<sigma>2, snd a') \<in> \<Delta> \<A> \<and> \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> 
                          (\<exists> x \<in> \<sigma>1 \<inter> \<sigma>2. (\<M> \<T>) f (Some x) = None))"
            unfolding productT_def
            apply simp
            by (metis fst_conv snd_conv)
         
          show ?thesis
          proof (cases "(\<exists> f. snd a' \<in> \<Q> \<A> \<and> (fst a, (None, f), fst a') \<in> \<Delta>T \<T> 
                        \<and> (\<M> \<T>) f None = None \<and> snd a = snd a')")
            case True
            from this
            obtain f where
            f_def: "snd a' \<in> \<Q> \<A> \<and>
             (fst a, (None, f), fst a') \<in> \<Delta>T \<T> \<and> 
                  (\<M> \<T>) f None = None \<and> snd a = snd a'" by auto
            have "a = q" 
              using p1 by auto
            from this f_def \<pi>_def LTTS_reachable.simps(2)
                 [of "\<Delta>T \<T>" "(\<M> \<T>)" "fst a" "(None, None)" \<pi> "fst qi"]
            have c1: "LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) (fst q) ((None, None) # \<pi>) (fst qi)"
              apply simp 
              by force

            from True
            have c2: "LTS_is_reachable (\<Delta> \<A>) (snd q) 
                                     (inputE ((None, None) # \<pi>)) (snd qi)"
              apply simp
              using \<open>a = q\<close> \<pi>_def by auto
            from c1 c2
            show ?thesis 
              by (metis \<pi>_def outputE.simps(3))
            next
              case False
              from this branch
              have "(\<exists> \<sigma>1 \<sigma>2 f. (fst a, (Some \<sigma>1, f), fst a') \<in> \<Delta>T \<T> \<and>
                (snd a, \<sigma>2, snd a') \<in> \<Delta> \<A> \<and> \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> 
                  (\<exists> x \<in> \<sigma>1 \<inter> \<sigma>2. (\<M> \<T>) f (Some x) = None))"
                by auto
              from this 
              obtain \<sigma>1 \<sigma>2 f where
              \<sigma>12f_def: "(fst a, (Some \<sigma>1, f), fst a') \<in> \<Delta>T \<T> \<and>
                         (snd a, \<sigma>2, snd a') \<in> \<Delta> \<A> \<and> 
                          \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists> x \<in> \<sigma>1 \<inter> \<sigma>2. (\<M> \<T>) f (Some x) = None)"
                by auto
              from this obtain e where
              e_def: "e \<in> \<sigma>1 \<inter> \<sigma>2 \<and> (\<M> \<T>) f (Some e) = None" by force
              from p1
              have qa_eq: "q = a" by force
              from this e_def \<pi>_def LTTS_reachable.simps(2)
                      [of "(\<Delta>T \<T>)" "(\<M> \<T>)" "fst q" "(Some e, None)" \<pi> "fst qi"]
                    \<sigma>12f_def F_ok1
              have s1: "LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) (fst q) 
                                ((Some e, None) # \<pi>) (fst qi)"
                apply simp
                by (metis e_def matche.simps(1) matche.simps(2))

              from \<sigma>12f_def \<pi>_def
              have s2: "LTS_is_reachable (\<Delta> \<A>) (snd q) 
                              (inputE ((Some e, None) # \<pi>)) (snd qi)"
                apply simp
                using e_def qa_eq by blast
              from s1 s2
              show ?thesis 
                by (metis \<pi>_def outputE.simps(3))
            qed
          qed
        qed

        define sl where "sl = a # x"

        from qij\<sigma>_def 
        have "a \<in> \<sigma> \<and> (qi, \<sigma>, qj) \<in> \<Delta>e (productT \<T> \<A> F) \<and>
               LTS_is_reachable_epsilon (\<Delta>e (productT \<T> \<A> F)) 
                        (\<Delta>e' (productT \<T> \<A> F)) qj x q'"
          by auto

        from this
        have snd_half: 
            "\<exists>\<pi>. a # x = outputE \<pi> \<and>
                   LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) (fst qi) \<pi> (fst q') \<and>
                   LTS_is_reachable (\<Delta> \<A>) (snd qi) (inputE \<pi>) (snd q')"
          apply (induction x arbitrary: qi a qj \<sigma>)
        proof -
          {
            fix qi a qj \<sigma>
            assume p1: "a \<in> \<sigma> \<and> (qi, \<sigma>, qj) \<in> \<Delta>e (productT \<T> \<A> F) \<and>
                        LTS_is_reachable_epsilon (\<Delta>e (productT \<T> \<A> F)) 
                                        (\<Delta>e' (productT \<T> \<A> F)) qj []  q'"
            from this productT_def
            have branch: "(\<exists> \<sigma>1 \<sigma>2 f.
            (fst qi, (Some \<sigma>1, f), fst qj) \<in> \<Delta>T \<T> \<and>
            (snd qi, \<sigma>2, snd qj) \<in> \<Delta> \<A> \<and> \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (F ((\<M> \<T>) f) (\<sigma>1 \<inter> \<sigma>2) = Some \<sigma>)) \<or>
             (\<exists> f. snd qi \<in> \<Q> \<A> \<and> (fst qi, (None, f), fst qj) \<in> \<Delta>T \<T> \<and> 
                    ((\<M> \<T>) f None = Some \<sigma>) \<and> snd qj = snd qi)"
              unfolding productT_def
              apply simp
              by fastforce
            from p1 LTS_is_reachable_epsilon.simps(1)
            obtain l where 
            l_def: "l \<noteq> [] \<and> epsilon_reach l (\<Delta>e' (productT \<T> \<A> F))
                           \<and> hd l = qj \<and> last l = q'"
              by auto
            from this
            have "\<exists>\<pi>. [] = outputE \<pi> \<and> 
                       LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) (fst qj) \<pi> (fst q') \<and>
                       LTS_is_reachable (\<Delta> \<A>) (snd qj) (inputE \<pi>) (snd q')"
              apply (induction l arbitrary: qj)
              apply simp
            proof -
              fix a l qj
              assume ind_hyp: "(\<And>qj. l \<noteq> [] \<and>
              epsilon_reach l (\<Delta>e' (productT \<T> \<A> F)) \<and> hd l = qj \<and> last l = q' \<Longrightarrow>
              \<exists>\<pi>. [] = outputE \<pi> \<and>
                  LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) (fst qj) \<pi> (fst q') \<and>
                  LTS_is_reachable (\<Delta> \<A>) (snd qj) (inputE \<pi>) (snd q'))"
                 and p1: "a # l \<noteq> [] \<and> 
                          epsilon_reach (a # l) (\<Delta>e' (productT \<T> \<A> F)) \<and>
                          hd (a # l) = qj \<and> last (a # l) = q'"

              show "\<exists>\<pi>. [] = outputE \<pi> \<and>
                    LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) (fst qj) \<pi> (fst q') \<and>
                    LTS_is_reachable (\<Delta> \<A>) (snd qj) (inputE \<pi>) (snd q')"
              proof (cases "l = []")
                case True
                from this p1
                have "qj = q'" 
                  by auto
                from this
                show ?thesis 
                  apply simp 
                  by (metis LTS_is_reachable.simps(1) LTTS_reachable.simps(1) 
                            inputE.simps(1) outputE.simps(1))
              next
                case False
                from this
                obtain a1 l' where
                a1l'_def: "l = a1 # l'" 
                  using clearjunk.cases by blast
                from this p1
                have "epsilon_reach l (\<Delta>e' (productT \<T> \<A> F)) \<and> 
                        hd l = a1 \<and> last l = q'"
                  by simp
                from this ind_hyp[of a1] False
                have "\<exists>\<pi>. [] = outputE \<pi> \<and> 
                           LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) (fst a1) \<pi> (fst q') \<and>
                            LTS_is_reachable (\<Delta> \<A>) (snd a1) (inputE \<pi>) (snd q')"
                  by auto
                from this obtain \<pi> where
                \<pi>_def: "[] = outputE \<pi> \<and> 
                           LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) (fst a1) \<pi> (fst q') \<and>
                            LTS_is_reachable (\<Delta> \<A>) (snd a1) (inputE \<pi>) (snd q')"
                  by auto
                from p1 a1l'_def
                have "(qj, a1) \<in> (\<Delta>e' (productT \<T> \<A> F))"
                  by auto
                from this  
                have branch1: "(\<exists> f. snd qj \<in> \<Q> \<A> \<and> (fst qj, (None, f), fst a1) \<in> \<Delta>T \<T> \<and> 
                            (\<M> \<T>) f None = None \<and> snd qj = snd a1) \<or> 
                      (\<exists> \<sigma>1 \<sigma>2 f.
             (fst qj, (Some \<sigma>1, f), fst a1) \<in> \<Delta>T \<T> \<and>
             (snd qj, \<sigma>2, snd a1) \<in> \<Delta> \<A> \<and> \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> 
                          (\<exists> x \<in> \<sigma>1 \<inter> \<sigma>2. (\<M> \<T>) f (Some x) = None))"  
                  unfolding productT_def
                  apply simp
                  by (metis fst_conv snd_conv)
                
                show ?thesis 
                proof (cases "(\<exists> f. snd qj \<in> \<Q> \<A> \<and> (fst qj, (None, f), fst a1) \<in> \<Delta>T \<T> \<and> 
                            (\<M> \<T>) f None = None \<and> snd qj = snd a1)")
                  case True
                  from this obtain f where
                  f_def: "snd qj \<in> \<Q> \<A> \<and>
      (fst qj, (None, f), fst a1) \<in> \<Delta>T \<T> \<and> (\<M> \<T>) f None = None \<and> snd qj = snd a1"
                    by auto
                  have s1: "LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>)
                              (fst qj) ((None,None) # \<pi>) (fst q')"
                    using True \<pi>_def by fastforce
                  have s2: "LTS_is_reachable (\<Delta> \<A>) (snd qj)
                                 (inputE ((None,None) # \<pi>)) (snd q')"
                    using True \<pi>_def by auto
                  from s1 s2
                  show ?thesis 
                    by (metis \<pi>_def outputE.simps(3))
                next
                  case False
                  from this branch1
                  obtain \<sigma>1 \<sigma>2 f where
                  \<sigma>12f_def: "(fst qj, (Some \<sigma>1, f), fst a1) \<in> \<Delta>T \<T> \<and>
                             (snd qj, \<sigma>2, snd a1) \<in> \<Delta> \<A> \<and> \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> 
                             (\<exists> x \<in> \<sigma>1 \<inter> \<sigma>2. (\<M> \<T>) f (Some x) = None)" by auto
                  from this 
                  obtain e where e_def: "e \<in> \<sigma>1 \<inter> \<sigma>2 \<and> (\<M> \<T>) f (Some e) = None" by auto
                  have s1: "LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) (fst qj) 
                                  ((Some e, None) # \<pi>) (fst q')"
                    by (metis F_ok1 IntD1 LTTS_reachable.simps(2) 
                              \<pi>_def \<sigma>12f_def e_def matche.simps(1) 
                              matche.simps(2) matcht.simps)
                  have s2: "LTS_is_reachable (\<Delta> \<A>) (snd qj) 
                            (inputE ((Some e, None) # \<pi>)) (snd q')"
                    using \<pi>_def \<sigma>12f_def e_def by auto
                  from s1 s2
                  show ?thesis
                    by (metis \<pi>_def outputE.simps(3))
                qed
              qed
            qed
            from this
            obtain \<pi> where
            \<pi>_def: "[] = outputE \<pi> \<and>
                     LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) (fst qj) \<pi> (fst q') \<and>
                      LTS_is_reachable (\<Delta> \<A>) (snd qj) (inputE \<pi>) (snd q')"
              by auto
            from p1 this branch LTTS_reachable.simps(2)[of "(\<Delta>T \<T>)"]
            show "\<exists>\<pi>. [a] = outputE \<pi> \<and>
              LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) (fst qi) \<pi> (fst q') \<and>
              LTS_is_reachable (\<Delta> \<A>) (snd qi) (inputE \<pi>) (snd q')"
            proof (cases "(\<exists> f. snd qi \<in> \<Q> \<A> \<and> (fst qi, (None, f), fst qj) \<in> \<Delta>T \<T> \<and> 
                    ((\<M> \<T>) f None = Some \<sigma>) \<and> snd qj = snd qi)")
              case True
              from this obtain f where
              f_def: "snd qi \<in> \<Q> \<A> \<and> (fst qi, (None, f), fst qj) \<in> \<Delta>T \<T> \<and> 
                       ((\<M> \<T>) f None = Some \<sigma>) \<and> snd qj = snd qi"
                by auto
              from \<pi>_def f_def p1
                   LTTS_reachable.simps(2)[of "(\<Delta>T \<T>)" "(\<M> \<T>)" "fst qi" 
                                              "(None, Some a)" \<pi> "fst q'"]
              have s1: "LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) (fst qi) ((None, Some a)#\<pi>) (fst q')"
                by fastforce
              from \<pi>_def f_def p1 
              have s2: "LTS_is_reachable (\<Delta> \<A>) (snd qi) 
                            (inputE ((None, Some a)#\<pi>)) (snd q')"
                by simp
              from s1 s2
              show ?thesis 
                by (metis \<pi>_def outputE.simps(2))
            next
              case False
              from this branch
              obtain \<sigma>1 \<sigma>2 f where
            \<sigma>12f_def:"(fst qi, (Some \<sigma>1, f), fst qj) \<in> \<Delta>T \<T> \<and>
                      (snd qi, \<sigma>2, snd qj) \<in> \<Delta> \<A> \<and> \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> 
                       F ((\<M> \<T>) f) (\<sigma>1 \<inter> \<sigma>2) = Some \<sigma>"
                by auto
              from F_ok2 this
              have \<sigma>11: "F ((\<M> \<T>) f) (\<sigma>1 \<inter> \<sigma>2) = 
                      Some (\<Union> {S |e S. e \<in> \<sigma>1 \<inter> \<sigma>2 \<and> 
                    (\<M> \<T>) f (Some e) = Some S})"
                by blast        
              from this p1 
              obtain b S where
              b_def: "b \<in> \<sigma>1 \<inter> \<sigma>2 \<and> a \<in> S \<and> (\<M> \<T>) f (Some b) = Some S" 
                using F_ok1 F_ok2
                using \<sigma>12f_def by auto
              from this b_def \<sigma>11
              have "matcht (Some \<sigma>1, f) (Some b, Some a) (\<M> \<T>)"
                by simp
              from \<pi>_def \<sigma>12f_def b_def this
                   LTTS_reachable.simps(2)
                   [of "\<Delta>T \<T>" "(\<M> \<T>)" "fst qi" "(Some b, Some a)" \<pi> "fst q'"]
              have s1: "LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) (fst qi) 
                                      ((Some b, Some a) # \<pi>) (fst q')"
                by fastforce
              have s2: "LTS_is_reachable (\<Delta> \<A>) (snd qi) 
                              (inputE ((Some b, Some a) # \<pi>)) (snd q')" 
                using \<pi>_def \<sigma>12f_def b_def by auto
              from s1 s2
              show ?thesis 
                by (metis \<pi>_def outputE.simps(2))
            qed
          }
          {
            fix a x qi aa qj \<sigma>
            assume ind_hyp: 
                    "\<And>qi a qj \<sigma>. a \<in> \<sigma> \<and>
                            (qi, \<sigma>, qj) \<in> \<Delta>e (productT \<T> \<A> F) \<and>
                            LTS_is_reachable_epsilon (\<Delta>e (productT \<T> \<A> F))
                            (\<Delta>e' (productT \<T> \<A> F)) qj x q' \<Longrightarrow>
                            \<exists>\<pi>. a # x = outputE \<pi> \<and>
               LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) (fst qi) \<pi> (fst q') \<and>
               LTS_is_reachable (\<Delta> \<A>) (snd qi) (inputE \<pi>) (snd q')"
               and p1: "aa \<in> \<sigma> \<and>
       (qi, \<sigma>, qj) \<in> \<Delta>e (productT \<T> \<A> F) \<and>
       LTS_is_reachable_epsilon (\<Delta>e (productT \<T> \<A> F)) (\<Delta>e' (productT \<T> \<A> F)) qj
        (a # x) q'"

            from p1 LTS_is_reachable_epsilon.simps(2)
                          [of "\<Delta>e (productT \<T> \<A> F)" 
                              "\<Delta>e' (productT \<T> \<A> F)" qj a x q']
            obtain qk ql \<sigma>' where qiqj\<sigma>_def: "
        epsilon_reachable qj qk (\<Delta>e' (productT \<T> \<A> F)) \<and>
        a \<in> \<sigma>' \<and>
        (qk, \<sigma>', ql) \<in> \<Delta>e (productT \<T> \<A> F) \<and>
        LTS_is_reachable_epsilon (\<Delta>e (productT \<T> \<A> F)) (\<Delta>e' (productT \<T> \<A> F)) ql x
         q'"
              by auto
            from this ind_hyp[of a \<sigma>' qk ql]
            obtain \<pi> where
          \<pi>_def: "a # x = outputE \<pi> \<and>
        LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) (fst qk) \<pi> (fst q') \<and>
        LTS_is_reachable (\<Delta> \<A>) (snd qk) (inputE \<pi>) (snd q')"
              by auto

            from qiqj\<sigma>_def epsilon_reachable_def[of qj qk]
            obtain l where
            l_def: "l \<noteq> [] \<and> epsilon_reach l (\<Delta>e' (productT \<T> \<A> F)) \<and> 
            hd l = qj \<and> last l = qk"  by force
        from this
        have "\<exists> \<pi>. a # x = outputE \<pi> \<and>
        LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) (fst qj) \<pi> (fst q') \<and>
        LTS_is_reachable (\<Delta> \<A>) (snd qj) (inputE \<pi>) (snd q')"  
          apply (induction l arbitrary: qj)
           apply simp
          apply (rename_tac a' l qj)
        proof -
          fix a' l qj
          assume ind_hyp: "\<And>qj. l \<noteq> [] \<and>
              epsilon_reach l (\<Delta>e' (productT \<T> \<A> F)) \<and> hd l = qj \<and> last l = qk \<Longrightarrow>
              \<exists>\<pi>. a # x = outputE \<pi> \<and>
                  LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) (fst qj) \<pi> (fst q') \<and>
                  LTS_is_reachable (\<Delta> \<A>) (snd qj) (inputE \<pi>) (snd q')"
             and p1: "a' # l \<noteq> [] \<and>
       epsilon_reach (a' # l) (\<Delta>e' (productT \<T> \<A> F)) \<and>
       hd (a' # l) = qj \<and> last (a' # l) = qk"
          show "\<exists>\<pi>. a # x = outputE \<pi> \<and>
           LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) (fst qj) \<pi> (fst q') \<and>
           LTS_is_reachable (\<Delta> \<A>) (snd qj) (inputE \<pi>) (snd q')"
          proof (cases "l = []")
          case True
          then show ?thesis 
            using \<pi>_def p1 by auto
          next
            case False
            from False obtain b l' where
            bl'_def: "l = b # l'" 
              using list.exhaust by blast
            have "epsilon_reach (l) (\<Delta>e' (productT \<T> \<A> F)) \<and>
                    hd l = b \<and> last l = qk"
              using bl'_def p1 by auto
            from ind_hyp[of b] this
            have "\<exists>\<pi>. a # x = outputE \<pi> \<and>
        LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) (fst b) \<pi> (fst q') \<and>
        LTS_is_reachable (\<Delta> \<A>) (snd b) (inputE \<pi>) (snd q')"
              using False by blast
            from this obtain \<pi> where
          \<pi>_def: "a # x = outputE \<pi> \<and>
                  LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) (fst b) \<pi> (fst q') \<and>
                  LTS_is_reachable (\<Delta> \<A>) (snd b) (inputE \<pi>) (snd q')"
              by auto
            from p1 bl'_def productT_def
            have branch: 
                  "(\<exists> f. snd qj \<in> \<Q> \<A> \<and> (fst qj, (None, f), fst b) \<in> \<Delta>T \<T> \<and> 
                          (\<M> \<T>) f None = None \<and> snd qj = snd b) \<or>
                   (\<exists> \<sigma>1 \<sigma>2 f.
             (fst qj, (Some \<sigma>1, f), fst b) \<in> \<Delta>T \<T> \<and>
             (snd qj, \<sigma>2, snd b) \<in> \<Delta> \<A> \<and> \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> 
                    (\<exists> x \<in> \<sigma>1 \<inter> \<sigma>2. (\<M> \<T>) f (Some x) = None))"
              unfolding productT_def
              apply simp
            proof -
              assume p1: "((\<exists>p p'.
         a' = (p, p') \<and>
         (\<exists>q. b = (q, p') \<and>
              p' \<in> \<Q> \<A> \<and> (\<exists>f. (p, (None, f), q) \<in> \<Delta>T \<T> \<and> (\<M> \<T>) f None = None))) \<or>
     (\<exists>p p'.
         a' = (p, p') \<and>
         (\<exists>\<sigma>1 \<sigma>2 q q'.
             b = (q, q') \<and>
             (\<exists>f. (p, (Some \<sigma>1, f), q) \<in> \<Delta>T \<T> \<and>
                  (p', \<sigma>2, q') \<in> \<Delta> \<A> \<and>
                  \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>x\<in>\<sigma>1 \<inter> \<sigma>2. (\<M> \<T>) f (Some x) = None))))) \<and>
    epsilon_reach (b # l')
     ({((p, p'), q, p') |p p' q.
       p' \<in> \<Q> \<A> \<and> (\<exists>f. (p, (None, f), q) \<in> \<Delta>T \<T> \<and> (\<M> \<T>) f None = None)} \<union>
      {uu.
       \<exists>p p' \<sigma>1 \<sigma>2 q q'.
          uu = ((p, p'), q, q') \<and>
          (\<exists>f. (p, (Some \<sigma>1, f), q) \<in> \<Delta>T \<T> \<and>
               (p', \<sigma>2, q') \<in> \<Delta> \<A> \<and>
               \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>x\<in>\<sigma>1 \<inter> \<sigma>2. (\<M> \<T>) f (Some x) = None))}) \<and>
    a' = qj \<and> (if l' = [] then b else last l') = qk"
        and p2: "l = b # l'"
              from this have p3: "((\<exists>p p'.
         a' = (p, p') \<and>
         (\<exists>q. b = (q, p') \<and>
              p' \<in> \<Q> \<A> \<and> (\<exists>f. (p, (None, f), q) \<in> \<Delta>T \<T> \<and> (\<M> \<T>) f None = None))) \<or>
     (\<exists>p p'.
         a' = (p, p') \<and>
         (\<exists>\<sigma>1 \<sigma>2 q q'.
             b = (q, q') \<and>
             (\<exists>f. (p, (Some \<sigma>1, f), q) \<in> \<Delta>T \<T> \<and>
                  (p', \<sigma>2, q') \<in> \<Delta> \<A> \<and>
                  \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>x\<in>\<sigma>1 \<inter> \<sigma>2. (\<M> \<T>) f (Some x) = None))))) \<and> 
          a' = qj \<and> (if l' = [] then b else last l') = qk"
                by auto
              from this p2 wfTA NFA_def
              have s1: "snd qj \<in> \<Q> \<A>"
              by (metis sndI)
               from p1
              have qja'eq: "qj = a'" by simp
              from p3 
              have "((\<exists>p p'.
         a' = (p, p') \<and>
         (\<exists>q. b = (q, p') \<and>
              p' \<in> \<Q> \<A> \<and> (\<exists>f. (p, (None, f), q) \<in> \<Delta>T \<T> \<and> (\<M> \<T>) f None = None))) \<or>
     (\<exists>p p'.
         a' = (p, p') \<and>
         (\<exists>\<sigma>1 \<sigma>2 q q'.
             b = (q, q') \<and>
             (\<exists>f. (p, (Some \<sigma>1, f), q) \<in> \<Delta>T \<T> \<and>
                  (p', \<sigma>2, q') \<in> \<Delta> \<A> \<and>
                  \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>x\<in>\<sigma>1 \<inter> \<sigma>2. (\<M> \<T>) f (Some x) = None)))))" by auto
              from this qja'eq
              have s2: "
    (\<exists>f. (fst qj, (None, f), fst b) \<in> \<Delta>T \<T> \<and> (\<M> \<T>) f None = None \<and> snd qj = snd b) \<or>
    (\<exists>\<sigma>1 \<sigma>2 f.
        (fst qj, (Some \<sigma>1, f), fst b) \<in> \<Delta>T \<T> \<and>
        (snd qj, \<sigma>2, snd b) \<in> \<Delta> \<A> \<and> \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>x\<in>\<sigma>1 \<inter> \<sigma>2. (\<M> \<T>) f (Some x) = None))"
                apply simp
                by (metis fst_conv snd_conv)
              from s1 s2
              show "snd qj \<in> \<Q> \<A> \<and>
    (\<exists>f. (fst qj, (None, f), fst b) \<in> \<Delta>T \<T> \<and> (\<M> \<T>) f None = None \<and> snd qj = snd b) \<or>
    (\<exists>\<sigma>1 \<sigma>2 f.
        (fst qj, (Some \<sigma>1, f), fst b) \<in> \<Delta>T \<T> \<and>
        (snd qj, \<sigma>2, snd b) \<in> \<Delta> \<A> \<and> \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>x\<in>\<sigma>1 \<inter> \<sigma>2. (\<M> \<T>) f (Some x) = None))"
                by auto
            qed
            show ?thesis 
           proof (cases "(\<exists> f. snd qj \<in> \<Q> \<A> \<and> (fst qj, (None, f), fst b) \<in> \<Delta>T \<T> \<and> 
                          (\<M> \<T>) f None = None \<and> snd qj = snd b)")
             case True  
             from this obtain f where
             f_def: "snd qj \<in> \<Q> \<A> \<and>
      (fst qj, (None, f), fst b) \<in> \<Delta>T \<T> \<and> (\<M> \<T>) f None = None \<and> snd qj = snd b" by auto
             have s1: "LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) (fst qj) ((None, None) # \<pi>) (fst q')"
               using \<pi>_def f_def by force
             have s2: "LTS_is_reachable (\<Delta> \<A>) (snd qj) 
                              (inputE ((None, None) # \<pi>)) (snd q')"
               using True \<pi>_def by auto
             from s1 s2 show ?thesis 
               by (metis \<pi>_def outputE.simps(3))
              next
                case False
                from this branch
                obtain \<sigma>1 \<sigma>2 f where
              \<sigma>12f_def: 
        "(fst qj, (Some \<sigma>1, f), fst b) \<in> \<Delta>T \<T> \<and>
         (snd qj, \<sigma>2, snd b) \<in> \<Delta> \<A> \<and> \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>x\<in>\<sigma>1 \<inter> \<sigma>2. (\<M> \<T>) f (Some x) = None)"
                  by auto
                from this
                obtain c where c_def: "c \<in> \<sigma>1 \<inter> \<sigma>2 \<and> (\<M> \<T>) f (Some c) = None" by force
                from this
                have s1: "LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) (fst qj) ((Some c, None) # \<pi>) (fst q')"
                  by (metis F_ok1 IntD1 LTTS_reachable.simps(2) 
                          \<pi>_def \<sigma>12f_def matche.simps(1) matche.simps(2) matcht.simps)
                have s2: "LTS_is_reachable (\<Delta> \<A>) (snd qj) 
                            (inputE ((Some c, None) # \<pi>)) (snd q')" 
                  using \<pi>_def \<sigma>12f_def c_def by auto
                from s1 s2
                show ?thesis 
                  by (metis \<pi>_def outputE.simps(3))
              qed
            qed qed

            from this obtain \<pi> where
          \<pi>_def: "a # x = outputE \<pi> \<and>
      LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) (fst qj) \<pi> (fst q') \<and>
      LTS_is_reachable (\<Delta> \<A>) (snd qj) (inputE \<pi>) (snd q')" by auto

          from p1 
          have branch: "(\<exists> f. snd qi \<in> \<Q> \<A> \<and> 
                        (fst qi, (None, f), fst qj) \<in> \<Delta>T \<T> \<and> 
                         ((\<M> \<T>) f None = Some \<sigma>) \<and> snd qi = snd qj) \<or> 
                (\<exists> \<sigma>1 \<sigma>2 f.
              (fst qi, (Some \<sigma>1, f), fst qj) \<in> \<Delta>T \<T> \<and>
              (snd qi, \<sigma>2, snd qj) \<in> \<Delta> \<A> \<and> \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> 
                  (F ((\<M> \<T>) f) (\<sigma>1 \<inter> \<sigma>2) = Some \<sigma>))"
            unfolding productT_def
            by fastforce

         from this p1
         show "\<exists>\<pi>. aa # a # x = outputE \<pi> \<and>
           LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) (fst qi) \<pi> (fst q') \<and>
           LTS_is_reachable (\<Delta> \<A>) (snd qi) (inputE \<pi>) (snd q')"
         proof (cases "(\<exists> f. snd qi \<in> \<Q> \<A> \<and> 
                        (fst qi, (None, f), fst qj) \<in> \<Delta>T \<T> \<and> 
                         ((\<M> \<T>) f None = Some \<sigma>) \<and> snd qi = snd qj)")
           case True
           from True
           obtain f where 
           f_def: "snd qi \<in> \<Q> \<A> \<and> 
                        (fst qi, (None, f), fst qj) \<in> \<Delta>T \<T> \<and> 
                         ((\<M> \<T>) f None = Some \<sigma>) \<and> snd qi = snd qj" by auto
           from this \<pi>_def p1 LTTS_reachable.simps(2)
                              [of "\<Delta>T \<T>" "(\<M> \<T>)" "fst qi" "(None, Some aa)" \<pi> "fst q'"]
           have s1: "LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>)
                    (fst qi) ((None, Some aa) # \<pi>) (fst q')"
             by fastforce
          
           have s2: "LTS_is_reachable (\<Delta> \<A>) (snd qi) 
                            (inputE ((None, Some aa) # \<pi>)) (snd q')"
             using True \<pi>_def by auto
           from s1 s2
            show ?thesis 
              by (metis \<pi>_def outputE.simps(2))
         next
           case False
           from False branch
           obtain \<sigma>1 \<sigma>2 f where \<sigma>12f_def:
        "(fst qi, (Some \<sigma>1, f), fst qj) \<in> \<Delta>T \<T> \<and>
         (snd qi, \<sigma>2, snd qj) \<in> \<Delta> \<A> \<and> \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> 
            F ((\<M> \<T>) f) (\<sigma>1 \<inter> \<sigma>2) = Some \<sigma>"
             by auto 
           from this F_ok2 
           have goal_1: "\<sigma> = (\<Union> {uu. \<exists>e S. uu = S \<and> e \<in> \<sigma>1 \<inter> \<sigma>2 \<and> 
                          ((\<M> \<T>) f) (Some e) = Some S})"
             by fastforce
           from p1
           have "aa \<in> \<sigma>"
             by simp
           from this \<sigma>12f_def p1 F_ok2 F_ok1 goal_1
           obtain c S where c_def: "c \<in> \<sigma>1 \<inter> \<sigma>2 \<and> 
                    (\<M> \<T>) f (Some c) = Some S \<and> aa \<in> S"
             using disjoint_iff_not_equal inf.idem 
             by blast
           from this \<sigma>12f_def F_ok2
           have "matcht (Some \<sigma>1, f) (Some c, Some aa) (\<M> \<T>)"
             using F_ok1 F_ok2 by auto
           from this \<sigma>12f_def \<pi>_def c_def LTTS_reachable.simps(2)
                              [of "\<Delta>T \<T>" "(\<M> \<T>)""fst qi" "(Some c, Some aa)" \<pi> "fst q'"]
           have s1: "LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) (fst qi) ((Some c, Some aa) # \<pi>) (fst q')"
             by fastforce
           have s2: "LTS_is_reachable (\<Delta> \<A>) (snd qi) 
                          (inputE ((Some c, Some aa) # \<pi>)) (snd q')"
             using \<pi>_def \<sigma>12f_def c_def by auto
           from s1 s2 show ?thesis 
             by (metis \<pi>_def outputE.simps(2))
         qed
       }
     qed
     from fst_half
     obtain \<pi> where \<pi>_def: "[] = outputE \<pi> \<and>
      LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) (fst q) \<pi> (fst qi) \<and>
      LTS_is_reachable (\<Delta> \<A>) (snd q) (inputE \<pi>) (snd qi)"
       by auto
     from snd_half
     obtain \<pi>' where \<pi>'_def: "a # x = outputE \<pi>' \<and>
      LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) (fst qi) \<pi>' (fst q') \<and>
      LTS_is_reachable (\<Delta> \<A>) (snd qi) (inputE \<pi>') (snd q')"
       by auto

     from outputE_concat[of \<pi> \<pi>'] \<pi>_def \<pi>'_def
     have s1: "a # x = outputE (\<pi> @ \<pi>')"  by auto

     from inputE_concat[of \<pi> \<pi>'] \<pi>_def \<pi>'_def
     have s2: "inputE \<pi> @ inputE \<pi>' = inputE (\<pi> @ \<pi>')"  by auto

     from \<pi>_def \<pi>'_def
          LTTS_reachable_concat[of "\<Delta>T \<T>" "\<M> \<T>" "fst q" \<pi> "fst qi" \<pi>' "fst q'"]
     have s3: "LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) (fst q) (\<pi> @ \<pi>') (fst q')"
       by auto

    from \<pi>_def \<pi>'_def s2
          LTS_is_reachable_concat' 
           [of "\<Delta> \<A>" "snd q" "inputE \<pi>" "snd qi" "inputE \<pi>'" "snd q'"]
     have s4: "LTS_is_reachable (\<Delta> \<A>) (snd q) (inputE \<pi> @ inputE \<pi>') (snd q')"
       by auto

     from s3 s4 s1
        show "\<exists>\<pi>. a # x = outputE \<pi> \<and>
           LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) (fst q) \<pi> (fst q') \<and>
           LTS_is_reachable (\<Delta> \<A>) (snd q) (inputE \<pi>) (snd q')"
          using s2 by auto
      }
    qed

    from this obtain \<pi> where
    \<pi>_def: "x = outputE \<pi> \<and> LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) (fst q) \<pi> (fst q') 
                \<and> LTS_is_reachable (\<Delta> \<A>) (snd q) (inputE \<pi>) (snd q')"
      by auto
    from this w_def 
    have "(inputE \<pi>) \<in> \<L> \<A>"
      unfolding \<L>_def NFA_accept_def productT_def
      apply simp
      by fastforce
    from this fstqI \<pi>_def
    show "\<exists>\<pi>. x = outputE \<pi> \<and>
             (\<exists>q. q \<in> \<I>T \<T> \<and>
                  (\<exists>q'. q' \<in> \<F>T \<T> \<and>
                        LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) q \<pi> q' \<and> inputE \<pi> \<in> \<L> \<A>))"
      by force
    }
    {
      show "{outputE \<pi> |\<pi>.
     \<exists>q. q \<in> \<I>T \<T> \<and>
         (\<exists>q'. q' \<in> \<F>T \<T> \<and> LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) q \<pi> q' \<and> inputE \<pi> \<in> \<L> \<A>)}
    \<subseteq> {w. \<exists>q\<in>\<I>e (productT \<T> \<A> F).
              \<exists>x\<in>\<F>e (productT \<T> \<A> F).
                 LTS_is_reachable_epsilon (\<Delta>e (productT \<T> \<A> F))
                  (\<Delta>e' (productT \<T> \<A> F)) q w x}"
        apply rule
        apply rule
      proof -
        fix x
        assume xin: "x \<in> {outputE \<pi> |\<pi>.
              \<exists>q. q \<in> \<I>T \<T> \<and>
                  (\<exists>q'. q' \<in> \<F>T \<T> \<and>
                        LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) q \<pi> q' \<and> inputE \<pi> \<in> \<L> \<A>)}"
        from this obtain \<pi> q q' where
        \<pi>qq'_def: "x = outputE \<pi> \<and> q \<in> \<I>T \<T> \<and> q' \<in> \<F>T \<T> \<and>
                   LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) q \<pi> q' \<and> inputE \<pi> \<in> \<L> \<A>"
          by auto

        from this 
        obtain q1 q1' where
        q1_def': "x = outputE \<pi> \<and> q \<in> \<I>T \<T> \<and> q' \<in> \<F>T \<T> \<and>
                         LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) q \<pi> q' \<and> 
                         (q1 \<in> \<I> \<A> \<and> q1' \<in> \<F> \<A> \<and> 
                             LTS_is_reachable (\<Delta> \<A>) q1 (inputE \<pi>) q1')"
          unfolding \<L>_def NFA_accept_def
          by auto

        from this wfTA NFA_def
        have "x = outputE \<pi> \<and> LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) q \<pi> q' \<and> 
              LTS_is_reachable (\<Delta> \<A>) q1 (inputE \<pi>) q1' \<and> q1 \<in> \<Q> \<A>" 
          by fastforce
        from this
        have ep_reach: "LTS_is_reachable_epsilon (\<Delta>e (productT \<T> \<A> F)) 
                                       (\<Delta>e' (productT \<T> \<A> F))
                     (q,q1) x (q', q1')"
          apply (induction \<pi> arbitrary: q q1 x)
          apply force
        proof -
          fix a \<pi> q q1 x
          assume ind_hyp: "(\<And>q q1 x. x = outputE \<pi> \<and>
            LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) q \<pi> q' \<and>
            LTS_is_reachable (\<Delta> \<A>) q1 (inputE \<pi>) q1' \<and> q1 \<in> \<Q> \<A> \<Longrightarrow>
            LTS_is_reachable_epsilon (\<Delta>e (productT \<T> \<A> F)) (\<Delta>e' (productT \<T> \<A> F))
             (q, q1) x (q', q1'))"
             and p1: "x = outputE (a # \<pi>) \<and>
           LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) q (a # \<pi>) q' \<and>
           LTS_is_reachable (\<Delta> \<A>) q1 (inputE (a # \<pi>)) q1' \<and> q1 \<in> \<Q> \<A>"

          from p1 have "\<exists> q'' \<alpha>. (q, \<alpha>, q'') \<in> \<Delta>T \<T> \<and> matcht \<alpha> a (\<M> \<T>) \<and> 
                          LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) q'' \<pi> q'"
            by auto
          from this obtain q'' \<alpha> where
          q''_def: "(q, \<alpha>, q'') \<in> \<Delta>T \<T> \<and> matcht \<alpha> a (\<M> \<T>) \<and> 
                          LTTS_reachable (\<Delta>T \<T>) (\<M> \<T>) q'' \<pi> q'" by auto
          from this
          have
          \<alpha>_branch: "(\<exists> f. \<alpha> = (None, f)) \<or> (\<exists> k f. \<alpha> = (Some k, f))"
            by (metis not_None_eq surj_pair)

          show "LTS_is_reachable_epsilon (\<Delta>e (productT \<T> \<A> F)) 
                                         (\<Delta>e' (productT \<T> \<A> F))
                                         (q, q1) x (q', q1')"
          proof (cases "\<exists> f. \<alpha> = (None, f)")
            case True 
            from this obtain f where f_def: "\<alpha> = (None, f)" by auto
            from this q''_def
            have c1: "((\<M> \<T>) f None = None \<longrightarrow> (a = (None, None))) \<and> 
                  ((\<exists> p. (\<M> \<T>) f None = Some p) \<longrightarrow> (\<exists> c. a = (None, Some c) \<and>  
                                              c \<in> (the ((\<M> \<T>) f None))))"
              by (metis Pair_inject matche.elims(2) matcht.elims(2) 
                        option.distinct(1) option.sel)
            show ?thesis 
            proof (cases "(\<M> \<T>) f None = None")
              case True
              from this c1 
              have a_def: "a = (None, None)"
                by auto
              from p1 a_def 
              have reachq1q1': "LTS_is_reachable (\<Delta> \<A>) q1 (inputE \<pi>) q1' \<and> q1 \<in> \<Q> \<A>"
                by simp
              
              from reachq1q1' ind_hyp[of x q'' q1] q''_def
              have s1: "LTS_is_reachable_epsilon (\<Delta>e (productT \<T> \<A> F)) 
                            (\<Delta>e' (productT \<T> \<A> F)) (q'', q1) x (q', q1')"
                using a_def outputE.simps(3) p1 by blast
              from reachq1q1'
              have s2: "((q,q1), (q'', q1)) \<in> (\<Delta>e' (productT \<T> \<A> F))"
                unfolding productT_def
                apply simp
                using f_def q''_def 
                using True by blast
              from this epsilon_reachable_def
                   [of "(q,q1)" "(q'', q1)" "\<Delta>e' (productT \<T> \<A> F)"]
                   epsilon_reach.simps(3)[of "(q,q1)" "(q'', q1)" "[]"
                                             "(\<Delta>e' (productT \<T> \<A> F))"]
              have "epsilon_reachable (q, q1) (q'', q1) (\<Delta>e' (productT \<T> \<A> F))"
                by fastforce
              from s1 this
                   LTS_is_reachable_epsilon_add_empty_head
                   [of "(q,q1)" "(q'', q1)" "\<Delta>e' (productT \<T> \<A> F)"
                       "\<Delta>e (productT \<T> \<A> F)" x "(q', q1')"]
              show ?thesis by simp 
            next
              case False
              from this
              have "\<exists> p. (\<M> \<T>) f None = Some p"
                by blast
              from this obtain \<sigma> where
              \<sigma>_def: "(\<M> \<T>) f None = Some \<sigma>" by auto
              from q''_def f_def matcht.simps[of None f "fst a" "snd a"]
              have "\<exists> c. a = (None, Some c) \<and> c \<in> \<sigma>"
                using \<sigma>_def c1 by auto
              from this obtain c where 
              c_def: "a = (None, Some c) \<and> c \<in> \<sigma>" by auto
              from this inputE_concat[of "[a]" \<pi>]
              have "outputE (a # \<pi>) = c # (outputE \<pi>)" 
                by simp 
              have reachq1q1': "LTS_is_reachable (\<Delta> \<A>) q1 (inputE \<pi>) q1' \<and> q1 \<in> \<Q> \<A>"
                using c_def p1 by auto
              
              from p1 c_def outputE_concat[of "[a]" \<pi>]
              have xeq: "x = c # outputE \<pi>"
                using \<open>outputE (a # \<pi>) = c # outputE \<pi>\<close> by blast
  
              from reachq1q1' ind_hyp[of "outputE \<pi>" q'' q1] q''_def
              have s1: "LTS_is_reachable_epsilon (\<Delta>e (productT \<T> \<A> F)) 
                            (\<Delta>e' (productT \<T> \<A> F)) (q'', q1) 
                                (outputE \<pi>) (q', q1')"
                by auto
              have ep_reach_qq1: "epsilon_reachable (q, q1) (q, q1)
                     (\<Delta>e' (productT \<T> \<A> F))"
                unfolding epsilon_reachable_def epsilon_reach.simps
                by force
              from q''_def 
              have "((q, q1), the ((\<M> \<T>) f None), (q'', q1)) \<in> \<Delta>e (productT \<T> \<A> F)"
                unfolding productT_def
                apply simp
                using \<sigma>_def f_def p1 by blast

              from this ep_reach_qq1 LTS_is_reachable_epsilon.simps(2)
                        [of "\<Delta>e (productT \<T> \<A> F)" 
                            "\<Delta>e' (productT \<T> \<A> F)" "(q, q1)"
                            c "outputE \<pi>" "(q', q1')"] xeq s1
             show ?thesis 
               using \<sigma>_def c_def by force
            qed
          next
            case False
            from this 
            obtain \<sigma> f where \<sigma>_def: "\<alpha> = (Some \<sigma>, f)"
              using \<alpha>_branch by blast

            from q''_def
            obtain si where 
            si_def: "fst a = Some si \<and> si \<in> \<sigma>" 
              using F_ok1 F_ok2 
              by (metis (no_types, opaque_lifting) \<sigma>_def fst_eqD matche.elims(2) 
                        matche.simps(2) matcht.elims(2) not_Some_eq)
            from p1 LTS_is_reachable.simps(2)[of "\<Delta> \<A>" q1 si "inputE \<pi>" q1']
              obtain q2 \<sigma>' where 
              q2\<sigma>_def: "si \<in> \<sigma>' \<and> (q1, \<sigma>', q2) \<in> \<Delta> \<A> \<and> 
                          LTS_is_reachable (\<Delta> \<A>) q2 (inputE \<pi>) q1'"
                by (metis fst_conv inputE.simps(2) old.prod.exhaust si_def)                
              from this wfTA NFA_def
              have q2in: "q2 \<in> \<Q> \<A>"
               by fast
              from q2\<sigma>_def 
              have \<sigma>\<sigma>'neq: "\<sigma> \<inter> \<sigma>' \<noteq> {}" 
                using si_def by blast

            show ?thesis 
            proof (cases "(\<M> \<T>) f (Some si) = None")
              case True
              from this si_def q''_def
              have snda_none: "snd a = None" 
                by (metis \<sigma>_def matche.elims(2) matcht.simps 
                    option.distinct(1) surjective_pairing)
              from this p1
              have "inputE (a # \<pi>) = si # (inputE \<pi>)"
                by (metis inputE.simps(2) prod.collapse si_def)
              
              from this q''_def q2\<sigma>_def \<sigma>_def True
              have head_reach: "((q,q1), (q'',q2)) \<in> \<Delta>e' (productT \<T> \<A> F)"
                unfolding productT_def
                apply simp
                using si_def by blast
              
              have "x = outputE \<pi>" 
                by (metis outputE.simps(3) p1 prod.collapse snda_none)
              from this ind_hyp[of x q'' q2] q''_def q2\<sigma>_def q2in
              have tail_reach: "LTS_is_reachable_epsilon (\<Delta>e (productT \<T> \<A> F)) 
                                             (\<Delta>e' (productT \<T> \<A> F)) 
                          (q'', q2) x  (q', q1')"
                by auto
              from head_reach epsilon_reachable_def
              have s1: "epsilon_reachable (q, q1) (q'', q2) (\<Delta>e' (productT \<T> \<A> F))"
                by (metis epsilon_reach.simps(2) epsilon_reach.simps(3) 
                          last_ConsL last_ConsR list.distinct(1) list.sel(1))
      
              from s1 tail_reach LTS_is_reachable_epsilon_add_empty_head
                   [of "(q,q1)" "(q'',q2)" "\<Delta>e' (productT \<T> \<A> F)"
                       "\<Delta>e (productT \<T> \<A> F)" x "(q', q1')"]
              show ?thesis by simp
            next
              case False
              from this q''_def
              obtain d so where
              so_def: "(\<M> \<T>) f (Some si) = Some d \<and> so \<in> d \<and> snd a = Some so"
                by (metis \<sigma>_def fst_conv matche.elims(2) matcht.elims(2) si_def snd_conv) 

              from q2\<sigma>_def si_def
              have "si \<in> \<sigma> \<inter> \<sigma>'" 
                by auto
              from this F_ok2 so_def
              have so_in: "\<exists> S. so \<in> S \<and> (F ((\<M> \<T>) f) (\<sigma> \<inter> \<sigma>')) = Some S"
                using F_ok1 all_not_in_conv 
                by (smt (verit) UnionI mem_Collect_eq)

              from q2\<sigma>_def q''_def
              have head_reach: "((q,q1), the (F ((\<M> \<T>) f) (\<sigma> \<inter> \<sigma>')), (q'', q2)) \<in> \<Delta>e (productT \<T> \<A> F)"
                unfolding productT_def
                apply simp
                by (metis F_ok1 False \<open>si \<in> \<sigma> \<inter> \<sigma>'\<close> \<sigma>\<sigma>'neq \<sigma>_def option.exhaust)

              from p1 so_def
              have s1: "x = so # (outputE \<pi>)"
                by (metis outputE.simps(2) prod.collapse)
              have s2: "epsilon_reachable (q, q1) (q, q1)
                        (\<Delta>e' (productT \<T> \<A> F))"
                unfolding epsilon_reachable_def
                by force
              have s3: "so \<in> the (F ((\<M> \<T>) f) (\<sigma> \<inter> \<sigma>')) \<and>
                        ((q,q1), the (F ((\<M> \<T>) f) (\<sigma> \<inter> \<sigma>')), (q'', q2)) 
                            \<in> \<Delta>e (productT \<T> \<A> F)"
                using head_reach so_in 
                by force

              from ind_hyp[of "outputE \<pi>" q'' q2]
              have s4: "LTS_is_reachable_epsilon (\<Delta>e (productT \<T> \<A> F)) 
                                       (\<Delta>e' (productT \<T> \<A> F)) (q'', q2)
                                        (outputE \<pi>) (q', q1')"
                using q''_def q2\<sigma>_def q2in by blast

              from s1 s2 s3 LTS_is_reachable_epsilon.simps(2)[
                   of "\<Delta>e (productT \<T> \<A> F)" "\<Delta>e' (productT \<T> \<A> F)" 
                      "(q,q1)" so "outputE \<pi>" "(q', q1')"] s4
              show ?thesis by force
            qed
          qed
        qed

        from this
        have s1: "(q,q1) \<in> \<I>e (productT \<T> \<A> F)"
          unfolding productT_def
          apply simp        
          using q1_def' by linarith
        have s2: "(q', q1') \<in> \<F>e (productT \<T> \<A> F)"
          unfolding productT_def
          apply simp
          using q1_def' by linarith
        from s1 s2 ep_reach
        show "\<exists>q\<in>\<I>e (productT \<T> \<A> F).
            \<exists>xa\<in>\<F>e (productT \<T> \<A> F).
               LTS_is_reachable_epsilon (\<Delta>e (productT \<T> \<A> F)) (\<Delta>e' (productT \<T> \<A> F))
                q x xa"
          by auto
      qed
    }
  qed


definition copy_tran where
   "copy_tran q q' S = 
    FOREACHi (\<lambda> Sr Tn. Tn = {((q,s), (q',s))| s. s \<in> S - Sr}) 
               S (\<lambda> s T. RETURN ({((q,s), (q',s))} \<union> T)) {}"

lemma copy_tran_correct: 
  fixes q q' S
  assumes finiteS: "finite S"
  shows "copy_tran q q' S \<le> SPEC (\<lambda> T. T = {((q,s), (q',s))| s. s \<in> S})"
  unfolding copy_tran_def
  apply (refine_vcg)
  using finiteS apply force
  apply force
  apply force
  apply force
  done
  




definition copy_tran' where
   "copy_tran' q \<alpha> q' S = 
    FOREACHi (\<lambda> Sr Tn. Tn = {((q,s), \<alpha>, (q',s))| s. s \<in> S - Sr}) 
        S (\<lambda> s T. RETURN ({((q,s), \<alpha>, (q',s))} \<union> T)) {}"

lemma copy_tran'_correct: 
  fixes q \<alpha> q' S
  assumes finiteS: "finite S"
  shows "copy_tran' q \<alpha> q' S \<le> SPEC (\<lambda> T. T = {((q,s), \<alpha>, (q',s))| s. s \<in> S})"
  unfolding copy_tran'_def
  apply (refine_vcg)
  using finiteS apply force
  apply force
  apply force
  apply force
  done


definition subtrans_comp where
    "subtrans_comp M q \<alpha> f q' F fe T D1 D2 =
     FOREACHi
      (\<lambda> Tr (Dn1, Dn2). 
          Dn1 = D1 \<union> {((q,q1), (the (F (M f) (\<alpha> \<inter> \<alpha>'))), (q',q1')) | 
                      q1 q1' \<alpha>'. (q1, \<alpha>', q1') \<in> T - Tr \<and> \<alpha> \<inter> \<alpha>' \<noteq> {} \<and> F (M f) (\<alpha> \<inter> \<alpha>') \<noteq> None} \<and> 
          Dn2 = D2 \<union> {((q,q1), (q',q1')) | 
                      q1 q1' \<alpha>'. (q1, \<alpha>', q1') \<in> T - Tr \<and> \<alpha> \<inter> \<alpha>' \<noteq> {} \<and> fe (M f) (\<alpha> \<inter> \<alpha>')})
      T (\<lambda> (q1, \<alpha>', q1') (D1, D2).
      (if (\<alpha> \<inter> \<alpha>' \<noteq> {}) then do {
       D1 \<leftarrow> (if (F (M f) (\<alpha> \<inter> \<alpha>') \<noteq> None) 
                  then RETURN ({((q,q1), (the (F (M f) (\<alpha> \<inter> \<alpha>'))), (q',q1'))} \<union> D1)
               else RETURN D1);
       D2 \<leftarrow> (if fe (M f) (\<alpha> \<inter> \<alpha>') then 
                    RETURN ({((q,q1), (q',q1'))} \<union> D2) else RETURN D2);
       RETURN (D1, D2)
      }
      else (RETURN (D1, D2)))) (D1, D2)"

lemma subtrans_comp_correct: 
  fixes q \<alpha> f q' F fe T D1 D2 M
  assumes finiteT: "finite T"
  shows "subtrans_comp M q \<alpha> f q' F fe T D1 D2 \<le> 
          SPEC (\<lambda> (Dn1, Dn2).
              Dn1 = D1 \<union> {((q,q1), (the (F (M f) (\<alpha> \<inter> \<alpha>'))), (q',q1')) | 
                      q1 q1' \<alpha>'. (q1, \<alpha>', q1') \<in> T \<and> \<alpha> \<inter> \<alpha>' \<noteq> {} \<and> F (M f) (\<alpha> \<inter> \<alpha>') \<noteq> None} \<and> 
              Dn2 = D2 \<union> {((q,q1), (q',q1')) | 
                      q1 q1' \<alpha>'. (q1, \<alpha>', q1') \<in> T \<and> \<alpha> \<inter> \<alpha>' \<noteq> {} \<and> fe (M f) (\<alpha> \<inter> \<alpha>')})"
  unfolding subtrans_comp_def
  apply (refine_vcg)
  using finiteT apply force
  apply force
  apply force
  apply blast
  apply simp 
  defer
  apply blast
  apply simp
  apply fastforce
  apply simp
  apply fastforce
  apply simp
  apply fastforce
  apply blast
  apply simp
  defer
  apply blast
  apply simp
  apply fastforce
  apply simp
    apply fastforce
   apply fastforce
  by fastforce

    


definition trans_comp where
    "trans_comp M F fe T1 T2 Q = 
     FOREACHi (\<lambda> T1r (Dn1, Dn2). Dn1 = {((p,p'), the ((M f) None), (q,p')) 
              | p p' q f. p' \<in> Q \<and>
                   ((p, (None, f), q) \<in> T1 - T1r \<and> (\<exists> So. (M f) None = Some So))}
            \<union>
            { ((p,p'), the (F (M f) (\<sigma>1 \<inter> \<sigma>2)), (q,q')) 
                  | p p' \<sigma>1 \<sigma>2 q q' f.
               (p, (Some \<sigma>1, f), q) \<in> T1 - T1r \<and> (p', \<sigma>2, q') \<in> T2 \<and>
                     \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists> So. F (M f) (\<sigma>1 \<inter> \<sigma>2) = Some So)} \<and>
      Dn2 = {((p,p'), (q,p')) 
              | p p' q f. p' \<in> Q \<and>
                   ((p, (None, f), q) \<in> T1 - T1r \<and> ((M f) None = None))}
            \<union>
            { ((p,p'), (q,q')) 
                  | p p' \<sigma>1 \<sigma>2 q q' f.
               (p, (Some \<sigma>1, f), q) \<in> T1 - T1r \<and> (p', \<sigma>2, q') \<in> T2 \<and>
                     \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists> x \<in> (\<sigma>1 \<inter> \<sigma>2). (M f) (Some x) = None)})
     T1
     (\<lambda> (q, (\<alpha>, f), q') (D1, D2). 
       (
          if (\<alpha> = None) then 
              (if ((M f) None = None) then 
                  do {
                      D2' \<leftarrow> copy_tran q q' Q;
                      RETURN (D1, D2 \<union> D2')
                  }
               else do {
                  D1' \<leftarrow> copy_tran' q (the ((M f) None)) q' Q;
                  RETURN (D1 \<union> D1', D2)
               })
          else (subtrans_comp M q (the \<alpha>) f q' F fe T2 D1 D2)
        )) ({}, {})"

lemma trans_comp_correct:
  fixes F fe T1 T2 Q M
  assumes finiteT: "finite T1"
      and finiteT2: "finite T2"
      and finiteQ: "finite Q"
      and fe_ok: "\<forall> f \<alpha>. fe f \<alpha> \<longleftrightarrow> (\<exists> x \<in> \<alpha>. f (Some x) = None)"
  shows "trans_comp M F fe T1 T2 Q \<le> 
          SPEC (\<lambda> (Dn1, Dn2). Dn1 = {((p,p'), the ((M f) None), (q,p')) 
              | p p' q f. p' \<in> Q \<and>
                   ((p, (None, f), q) \<in> T1 \<and> (\<exists> So. (M f) None = Some So))}
            \<union>
            { ((p,p'), the (F (M f) (\<sigma>1 \<inter> \<sigma>2)), (q,q')) 
                  | p p' \<sigma>1 \<sigma>2 q q' f.
               (p, (Some \<sigma>1, f), q) \<in> T1 \<and> (p', \<sigma>2, q') \<in> T2 \<and>
                     \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists> So. F (M f) (\<sigma>1 \<inter> \<sigma>2) = Some So)} \<and>
      Dn2 = {((p,p'), (q,p')) 
              | p p' q f. p' \<in> Q \<and>
                   ((p, (None, f), q) \<in> T1 \<and> ((M f) None = None))}
            \<union>
            { ((p,p'), (q,q')) 
                  | p p' \<sigma>1 \<sigma>2 q q' f.
               (p, (Some \<sigma>1, f), q) \<in> T1 \<and> (p', \<sigma>2, q') \<in> T2 \<and>
                     \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists> x \<in> (\<sigma>1 \<inter> \<sigma>2). (M f) (Some x) = None)})"
  unfolding trans_comp_def
  apply (refine_vcg)
  using finiteT apply force
  apply simp
  apply simp
  apply simp
  using copy_tran_correct[OF finiteQ]
  defer defer defer
  apply auto[1]
  apply auto[1]
  defer apply simp
  defer apply (simp)
proof -
  {
    fix x it \<sigma> x1 x2 x1a x1b x2a x2b x1c x2c
    assume xin: "(x1, (None, x2a), x2b) \<in> it"
       and itin: "it \<subseteq> T1"
       and x2a_def: "M x2a None = None"
    
    from x2a_def
    have eq1: "{((p, p'), the ((M f) None), q, p') |p p' q f.
                       p' \<in> Q \<and>
                       (p, (None, f), q) \<in> T1 \<and>
                       (p, (None, f), q) \<notin> it \<and> (\<exists>So. (M f) None = Some So)} = 
               {((p, p'), the ((M f) None), q, p') |p p' q f.
                       p' \<in> Q \<and>
                       (p, (None, f), q) \<in> T1 \<and>
                       ((p, (None, f), q) \<in> it \<longrightarrow> f = x2a \<and> p = x1 \<and> q = x2b) \<and>
                       (\<exists>So. (M f) None = Some So)}"
      by force

    from copy_tran_correct[OF finiteQ, of x1 x2b]
    have c1: "copy_tran x1 x2b Q \<le> SPEC (\<lambda>T. T = {((x1, s), x2b, s) |s. s \<in> Q})"  
      by auto

    have c2: "SPEC (\<lambda>T. T = {((x1, s), x2b, s) |s. s \<in> Q}) \<le>
             SPEC (\<lambda>D2'. {((p, p'), q, p') |p p' q.
                    p' \<in> Q \<and>
                    (\<exists>f. (p, (None, f), q) \<in> T1 \<and>
                         (p, (None, f), q) \<notin> it \<and> M f None = None)} \<union>
                   {uu.
                    \<exists>p p' \<sigma>1 \<sigma>2 q q'.
                       uu = ((p, p'), q, q') \<and>
                       (\<exists>f. (p, (Some \<sigma>1, f), q) \<in> T1 \<and>
                            (p, (Some \<sigma>1, f), q) \<notin> it \<and>
                            (p', \<sigma>2, q') \<in> T2 \<and>
                            \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>x\<in>\<sigma>1 \<inter> \<sigma>2. M f (Some x) = None))} \<union>
                   D2' =
                   {((p, p'), q, p') |p p' q.
                    p' \<in> Q \<and>
                    (\<exists>f. (p, (None, f), q) \<in> T1 \<and>
                         ((p, (None, f), q) \<in> it \<longrightarrow> f = x2a \<and> p = x1 \<and> q = x2b) \<and>
                        M f None = None)} \<union>
                   {uu.
                    \<exists>p p' \<sigma>1 \<sigma>2 q q'.
                       uu = ((p, p'), q, q') \<and>
                       (\<exists>f. (p, (Some \<sigma>1, f), q) \<in> T1 \<and>
                            (p, (Some \<sigma>1, f), q) \<notin> it \<and>
                            (p', \<sigma>2, q') \<in> T2 \<and>
                            \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>x\<in>\<sigma>1 \<inter> \<sigma>2. (M f) (Some x) = None))})"
      apply simp
      apply auto
      using itin x2a_def xin by blast
      
    show "copy_tran x1 x2b Q
       \<le> SPEC (\<lambda>D2'. {((p, p'), the ((M f) None), q, p') |p p' q f.
                       p' \<in> Q \<and>
                       (p, (None, f), q) \<in> T1 \<and>
                       (p, (None, f), q) \<notin> it \<and> (\<exists>So. M f None = Some So)} \<union>
                      {((p, p'), the (F (M f) (\<sigma>1 \<inter> \<sigma>2)), q, q') |p p' \<sigma>1 \<sigma>2 q q' f.
                       (p, (Some \<sigma>1, f), q) \<in> T1 \<and>
                       (p, (Some \<sigma>1, f), q) \<notin> it \<and>
                       (p', \<sigma>2, q') \<in> T2 \<and>
                       \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>So. F (M f) (\<sigma>1 \<inter> \<sigma>2) = Some So)} =
                      {((p, p'), the ((M f) None), q, p') |p p' q f.
                       p' \<in> Q \<and>
                       (p, (None, f), q) \<in> T1 \<and>
                       ((p, (None, f), q) \<in> it \<longrightarrow> f = x2a \<and> p = x1 \<and> q = x2b) \<and>
                       (\<exists>So. M f None = Some So)} \<union>
                      {((p, p'), the (F (M f) (\<sigma>1 \<inter> \<sigma>2)), q, q') |p p' \<sigma>1 \<sigma>2 q q' f.
                       (p, (Some \<sigma>1, f), q) \<in> T1 \<and>
                       (p, (Some \<sigma>1, f), q) \<notin> it \<and>
                       (p', \<sigma>2, q') \<in> T2 \<and>
                       \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>So. F (M f) (\<sigma>1 \<inter> \<sigma>2) = Some So)} \<and>
                      {((p, p'), q, p') |p p' q.
                       p' \<in> Q \<and>
                       (\<exists>f. (p, (None, f), q) \<in> T1 \<and>
                            (p, (None, f), q) \<notin> it \<and> (M f) None = None)} \<union>
                      {uu.
                       \<exists>p p' \<sigma>1 \<sigma>2 q q'.
                          uu = ((p, p'), q, q') \<and>
                          (\<exists>f. (p, (Some \<sigma>1, f), q) \<in> T1 \<and>
                               (p, (Some \<sigma>1, f), q) \<notin> it \<and>
                               (p', \<sigma>2, q') \<in> T2 \<and>
                               \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>x\<in>\<sigma>1 \<inter> \<sigma>2. (M f) (Some x) = None))} \<union>
                      D2' =
                      {((p, p'), q, p') |p p' q.
                       p' \<in> Q \<and>
                       (\<exists>f. (p, (None, f), q) \<in> T1 \<and>
                            ((p, (None, f), q) \<in> it \<longrightarrow> f = x2a \<and> p = x1 \<and> q = x2b) \<and>
                            (M f)  None = None)} \<union>
                      {uu.
                       \<exists>p p' \<sigma>1 \<sigma>2 q q'.
                          uu = ((p, p'), q, q') \<and>
                          (\<exists>f. (p, (Some \<sigma>1, f), q) \<in> T1 \<and>
                               (p, (Some \<sigma>1, f), q) \<notin> it \<and>
                               (p', \<sigma>2, q') \<in> T2 \<and>
                               \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>x\<in>\<sigma>1 \<inter> \<sigma>2. (M f) (Some x) = None))})"
      using eq1 apply simp
      using c2 c1
      by (simp add: SPEC_trans)
  }{
    fix x it \<sigma> x1 x2 x1a x1b x2a x2b x1c x2c
    assume xin: "(x1, (None, x2a), x2b) \<in> it"
       and itin: "it \<subseteq> T1"
       and x2a_def: "\<exists>y. M x2a None = Some y"
    from x2a_def
    have eq1: "{((p, p'), q, p') |p p' q.
                       p' \<in> Q \<and>
                       (\<exists>f. (p, (None, f), q) \<in> T1 \<and>
                            (p, (None, f), q) \<notin> it \<and> M f None = None)} = 
              {((p, p'), q, p') |p p' q.
                       p' \<in> Q \<and>
                       (\<exists>f. (p, (None, f), q) \<in> T1 \<and>
                            ((p, (None, f), q) \<in> it \<longrightarrow> f = x2a \<and> p = x1 \<and> q = x2b) \<and>
                            M f None = None)}"
      by auto

    from copy_tran'_correct[OF finiteQ, of x1 "the (M x2a None)" x2b]
    have c1: "copy_tran' x1 (the (M x2a None)) x2b Q
  \<le> SPEC (\<lambda>T. T = {((x1, s), the (M x2a None), x2b, s) |s. s \<in> Q})"
      by auto

    have c2: "SPEC (\<lambda>T. T = {((x1, s), the (M x2a None), x2b, s) |s. s \<in> Q}) \<le> 
        SPEC (\<lambda>D1'. {((p, p'), the (M f None), q, p') |p p' q f.
                    p' \<in> Q \<and>
                    (p, (None, f), q) \<in> T1 \<and>
                    (p, (None, f), q) \<notin> it \<and> (\<exists>So. M f None = Some So)} \<union>
                   {((p, p'), the (F (M f) (\<sigma>1 \<inter> \<sigma>2)), q, q') |p p' \<sigma>1 \<sigma>2 q q' f.
                    (p, (Some \<sigma>1, f), q) \<in> T1 \<and>
                    (p, (Some \<sigma>1, f), q) \<notin> it \<and>
                    (p', \<sigma>2, q') \<in> T2 \<and>
                    \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>So. F (M f) (\<sigma>1 \<inter> \<sigma>2) = Some So)} \<union>
                   D1' =
                   {((p, p'), the ((M f) None), q, p') |p p' q f.
                    p' \<in> Q \<and>
                    (p, (None, f), q) \<in> T1 \<and>
                    ((p, (None, f), q) \<in> it \<longrightarrow> f = x2a \<and> p = x1 \<and> q = x2b) \<and>
                    (\<exists>So. (M f) None = Some So)} \<union>
                   {((p, p'), the (F (M f) (\<sigma>1 \<inter> \<sigma>2)), q, q') |p p' \<sigma>1 \<sigma>2 q q' f.
                    (p, (Some \<sigma>1, f), q) \<in> T1 \<and>
                    (p, (Some \<sigma>1, f), q) \<notin> it \<and>
                    (p', \<sigma>2, q') \<in> T2 \<and>
                    \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>So. F (M f) (\<sigma>1 \<inter> \<sigma>2) = Some So)})"
      apply simp 
      apply auto
      apply (metis option.sel)
      using itin x2a_def xin apply blast
      apply (metis option.sel)
      apply (metis option.sel)
      by (metis option.sel)

    show "copy_tran' x1 (the (M x2a None)) x2b Q
       \<le> SPEC (\<lambda>D1'. {((p, p'), the (M f None), q, p') |p p' q f.
                       p' \<in> Q \<and>
                       (p, (None, f), q) \<in> T1 \<and>
                       (p, (None, f), q) \<notin> it \<and> (\<exists>So. M f None = Some So)} \<union>
                      {((p, p'), the (F (M f) (\<sigma>1 \<inter> \<sigma>2)), q, q') |p p' \<sigma>1 \<sigma>2 q q' f.
                       (p, (Some \<sigma>1, f), q) \<in> T1 \<and>
                       (p, (Some \<sigma>1, f), q) \<notin> it \<and>
                       (p', \<sigma>2, q') \<in> T2 \<and>
                       \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>So. F (M f) (\<sigma>1 \<inter> \<sigma>2) = Some So)} \<union>
                      D1' =
                      {((p, p'), the ((M f) None), q, p') |p p' q f.
                       p' \<in> Q \<and>
                       (p, (None, f), q) \<in> T1 \<and>
                       ((p, (None, f), q) \<in> it \<longrightarrow> f = x2a \<and> p = x1 \<and> q = x2b) \<and>
                       (\<exists>So. (M f) None = Some So)} \<union>
                      {((p, p'), the (F (M f) (\<sigma>1 \<inter> \<sigma>2)), q, q') |p p' \<sigma>1 \<sigma>2 q q' f.
                       (p, (Some \<sigma>1, f), q) \<in> T1 \<and>
                       (p, (Some \<sigma>1, f), q) \<notin> it \<and>
                       (p', \<sigma>2, q') \<in> T2 \<and>
                       \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>So. F (M f) (\<sigma>1 \<inter> \<sigma>2) = Some So)} \<and>
                      {((p, p'), q, p') |p p' q.
                       p' \<in> Q \<and>
                       (\<exists>f. (p, (None, f), q) \<in> T1 \<and>
                            (p, (None, f), q) \<notin> it \<and> (M f) None = None)} \<union>
                      {uu.
                       \<exists>p p' \<sigma>1 \<sigma>2 q q'.
                          uu = ((p, p'), q, q') \<and>
                          (\<exists>f. (p, (Some \<sigma>1, f), q) \<in> T1 \<and>
                               (p, (Some \<sigma>1, f), q) \<notin> it \<and>
                               (p', \<sigma>2, q') \<in> T2 \<and>
                               \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>x\<in>\<sigma>1 \<inter> \<sigma>2. (M f) (Some x) = None))} =
                      {((p, p'), q, p') |p p' q.
                       p' \<in> Q \<and>
                       (\<exists>f. (p, (None, f), q) \<in> T1 \<and>
                            ((p, (None, f), q) \<in> it \<longrightarrow> f = x2a \<and> p = x1 \<and> q = x2b) \<and>
                            (M f) None = None)} \<union>
                      {uu.
                       \<exists>p p' \<sigma>1 \<sigma>2 q q'.
                          uu = ((p, p'), q, q') \<and>
                          (\<exists>f. (p, (Some \<sigma>1, f), q) \<in> T1 \<and>
                               (p, (Some \<sigma>1, f), q) \<notin> it \<and>
                               (p', \<sigma>2, q') \<in> T2 \<and>
                               \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>x\<in>\<sigma>1 \<inter> \<sigma>2. (M f) (Some x) = None))})"
      using eq1 apply simp
      using c1 c2 by (simp add: SPEC_trans)
  }
  {
    fix x it \<sigma> x1 x2 x1a x1b x2a x2b x1c x2c
    assume xinit: "(x1, (x1b, x2a), x2b) \<in> it"
       and itin: "it \<subseteq> T1"
       and x1b_def: "\<exists>y. x1b = Some y"
    
    have eq1: "{((p, p'), the (M f None), q, p') |p p' q f.
     p' \<in> Q \<and>
     (p, (None, f), q) \<in> T1 \<and> (p, (None, f), q) \<notin> it \<and> (\<exists>So. M f None = Some So)} = 
    {((p, p'), the (M f None), q, p') |p p' q f.
     p' \<in> Q \<and>
     (p, (None, f), q) \<in> T1 \<and>
     ((p, (None, f), q) \<in> it \<longrightarrow> f = x2a \<and> None = x1b \<and> p = x1 \<and> q = x2b) \<and>
     (\<exists>So. M f None = Some So)}"
      using xinit itin x1b_def by force


    have eq2: "{((p, p'), the (M f None), q, p') |p p' q f.
     p' \<in> Q \<and>
     (p, (None, f), q) \<in> T1 \<and>
     ((p, (None, f), q) \<in> it \<longrightarrow> f = x2a \<and> None = x1b \<and> p = x1 \<and> q = x2b) \<and>
     (\<exists>So. M f None = Some So)} = 
    {((p, p'), the (M f None), q, p') |p p' q f.
     p' \<in> Q \<and>
     (p, (None, f), q) \<in> T1 \<and>
     ((p, (None, f), q) \<in> it \<longrightarrow> f = x2a \<and> None = x1b \<and> p = x1 \<and> q = x2b) \<and>
     (\<exists>So. M f None = Some So)}"
      by force

    

    
    have c1: "SPEC (\<lambda>(Dn1, Dn2).
              Dn1 =
              {((p, p'), the (M f None), q, p') |p p' q f.
               p' \<in> Q \<and>
               (p, (None, f), q) \<in> T1 \<and>
               (p, (None, f), q) \<notin> it \<and> (\<exists>So. M f None = Some So)} \<union>
              {((p, p'), the (F (M f) (\<sigma>1 \<inter> \<sigma>2)), q, q') |p p' \<sigma>1 \<sigma>2 q q' f.
               (p, (Some \<sigma>1, f), q) \<in> T1 \<and>
               (p, (Some \<sigma>1, f), q) \<notin> it \<and>
               (p', \<sigma>2, q') \<in> T2 \<and> \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>So. F (M f) (\<sigma>1 \<inter> \<sigma>2) = Some So)} \<union>
              {((x1, q1), the (F (M x2a) (the x1b \<inter> \<alpha>')), x2b, q1') |q1 q1' \<alpha>'.
               (q1, \<alpha>', q1') \<in> T2 \<and>
               the x1b \<inter> \<alpha>' \<noteq> {} \<and> F (M x2a) (the x1b \<inter> \<alpha>') \<noteq> None} \<and>
              Dn2 =
              {((p, p'), q, p') |p p' q.
               p' \<in> Q \<and>
               (\<exists>f. (p, (None, f), q) \<in> T1 \<and>
                    (p, (None, f), q) \<notin> it \<and> M f None = None)} \<union>
              {uu.
               \<exists>p p' \<sigma>1 \<sigma>2 q q'.
                  uu = ((p, p'), q, q') \<and>
                  (\<exists>f. (p, (Some \<sigma>1, f), q) \<in> T1 \<and>
                       (p, (Some \<sigma>1, f), q) \<notin> it \<and>
                       (p', \<sigma>2, q') \<in> T2 \<and>
                       \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>x\<in>\<sigma>1 \<inter> \<sigma>2. M f (Some x) = None))} \<union>
              {uu.
               \<exists>q1 q1' \<alpha>'.
                  uu = ((x1, q1), x2b, q1') \<and>
                  (q1, \<alpha>', q1') \<in> T2 \<and> the x1b \<inter> \<alpha>' \<noteq> {} \<and> fe (M x2a) (the x1b \<inter> \<alpha>')}) \<le> 
    RES {({((p, p'), the (M f None), q, p') |p p' q f.
                 p' \<in> Q \<and>
                 (p, (None, f), q) \<in> T1 \<and>
                 ((p, (None, f), q) \<in> it \<longrightarrow>
                  f = x2a \<and> None = x1b \<and> p = x1 \<and> q = x2b) \<and>
                 (\<exists>So. M f None = Some So)} \<union>
                {((p, p'), the (F (M f) (\<sigma>1 \<inter> \<sigma>2)), q, q') |p p' \<sigma>1 \<sigma>2 q q' f.
                 (p, (Some \<sigma>1, f), q) \<in> T1 \<and>
                 ((p, (Some \<sigma>1, f), q) \<in> it \<longrightarrow>
                  f = x2a \<and> Some \<sigma>1 = x1b \<and> p = x1 \<and> q = x2b) \<and>
                 (p', \<sigma>2, q') \<in> T2 \<and> \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>So. F (M f) (\<sigma>1 \<inter> \<sigma>2) = Some So)},
                {((p, p'), q, p') |p p' q.
                 p' \<in> Q \<and>
                 (\<exists>f. (p, (None, f), q) \<in> T1 \<and>
                      ((p, (None, f), q) \<in> it \<longrightarrow>
                       f = x2a \<and> None = x1b \<and> p = x1 \<and> q = x2b) \<and>
                      (M f) None = None)} \<union>
                {uu.
                 \<exists>p p' \<sigma>1 \<sigma>2 q q'.
                    uu = ((p, p'), q, q') \<and>
                    (\<exists>f. (p, (Some \<sigma>1, f), q) \<in> T1 \<and>
                         ((p, (Some \<sigma>1, f), q) \<in> it \<longrightarrow>
                          f = x2a \<and> Some \<sigma>1 = x1b \<and> p = x1 \<and> q = x2b) \<and>
                         (p', \<sigma>2, q') \<in> T2 \<and>
                         \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>x\<in>\<sigma>1 \<inter> \<sigma>2. M f (Some x) = None))})}"
      apply simp
      apply (rule_tac conjI)
      apply (simp add:eq1)
      apply rule
      apply rule
        defer apply rule
      defer apply rule apply rule
         defer apply rule defer
    proof -
      {
        fix x
        assume xin: "x \<in> {((p, p'), the (M f None), q, p') |p p' q f.
              p' \<in> Q \<and>
              (p, (None, f), q) \<in> T1 \<and>
              ((p, (None, f), q) \<in> it \<longrightarrow> f = x2a \<and> None = x1b \<and> p = x1 \<and> q = x2b) \<and>
              (\<exists>So. M f None = Some So)} \<union>
             {((p, p'), the (F (M f) (\<sigma>1 \<inter> \<sigma>2)), q, q') |p p' \<sigma>1 \<sigma>2 q q' f.
              (p, (Some \<sigma>1, f), q) \<in> T1 \<and>
              (p, (Some \<sigma>1, f), q) \<notin> it \<and>
              (p', \<sigma>2, q') \<in> T2 \<and>
              \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>So. F (M f) (\<sigma>1 \<inter> \<sigma>2) = Some So)} \<union>
             {((x1, q1), the (F (M x2a) (the x1b \<inter> \<alpha>')), x2b, q1') |q1 q1' \<alpha>'.
              (q1, \<alpha>', q1') \<in> T2 \<and>
              the x1b \<inter> \<alpha>' \<noteq> {} \<and> (\<exists>y. F (M x2a) (the x1b \<inter> \<alpha>') = Some y)}"
        show "x \<in> {((p, p'), the (M f None), q, p') |p p' q f.
               p' \<in> Q \<and>
               (p, (None, f), q) \<in> T1 \<and>
               ((p, (None, f), q) \<in> it \<longrightarrow> f = x2a \<and> None = x1b \<and> p = x1 \<and> q = x2b) \<and>
               (\<exists>So. M f None = Some So)} \<union>
              {((p, p'), the (F (M f) (\<sigma>1 \<inter> \<sigma>2)), q, q') |p p' \<sigma>1 \<sigma>2 q q' f.
               (p, (Some \<sigma>1, f), q) \<in> T1 \<and>
               ((p, (Some \<sigma>1, f), q) \<in> it \<longrightarrow>
                f = x2a \<and> Some \<sigma>1 = x1b \<and> p = x1 \<and> q = x2b) \<and>
               (p', \<sigma>2, q') \<in> T2 \<and> \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>So. F (M f) (\<sigma>1 \<inter> \<sigma>2) = Some So)}"
        proof (cases "x \<in> {((p, p'), the (M f None), q, p') |p p' q f.
              p' \<in> Q \<and>
              (p, (None, f), q) \<in> T1 \<and>
              ((p, (None, f), q) \<in> it \<longrightarrow> f = x2a \<and> None = x1b \<and> p = x1 \<and> q = x2b) \<and>
              (\<exists>So. M f None = Some So)}")
          case True
          then show ?thesis by auto
          next
            case False
            from this xin
            have xin': "x \<in> {((p, p'), the (F (M f) (\<sigma>1 \<inter> \<sigma>2)), q, q') |p p' \<sigma>1 \<sigma>2 q q' f.
          (p, (Some \<sigma>1, f), q) \<in> T1 \<and>
          (p, (Some \<sigma>1, f), q) \<notin> it \<and>
          (p', \<sigma>2, q') \<in> T2 \<and> \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>So. F (M f) (\<sigma>1 \<inter> \<sigma>2) = Some So)} \<union>
         {((x1, q1), the (F (M x2a) (the x1b \<inter> \<alpha>')), x2b, q1') |q1 q1' \<alpha>'.
          (q1, \<alpha>', q1') \<in> T2 \<and>
          the x1b \<inter> \<alpha>' \<noteq> {} \<and> (\<exists>y. F (M x2a) (the x1b \<inter> \<alpha>') = Some y)}" by force
            then show ?thesis 
            proof (cases "x \<in> {((p, p'), the (F (M f) (\<sigma>1 \<inter> \<sigma>2)), q, q') |p p' \<sigma>1 \<sigma>2 q q' f.
          (p, (Some \<sigma>1, f), q) \<in> T1 \<and>
          (p, (Some \<sigma>1, f), q) \<notin> it \<and>
          (p', \<sigma>2, q') \<in> T2 \<and> \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>So. F (M f) (\<sigma>1 \<inter> \<sigma>2) = Some So)}")
              case True
              then show ?thesis by force
            next
              case False
              from this xin'
              have xin'': "x \<in> {((x1, q1), the (F (M x2a) (the x1b \<inter> \<alpha>')), x2b, q1') |q1 q1' \<alpha>'.
          (q1, \<alpha>', q1') \<in> T2 \<and>
          the x1b \<inter> \<alpha>' \<noteq> {} \<and> (\<exists>y. F (M x2a) (the x1b \<inter> \<alpha>') = Some y)}"
                by force
              from x1b_def
              obtain y where y_def: "x1b = Some y" by auto
                
              from xin'' this xinit itin x1b_def 
              show ?thesis
                by fastforce
            qed
          qed
        }
        {
          fix x
          assume xin: "x \<in> {((p, p'), the (M f None), q, p') |p p' q f.
              p' \<in> Q \<and>
              (p, (None, f), q) \<in> T1 \<and>
              ((p, (None, f), q) \<in> it \<longrightarrow> f = x2a \<and> None = x1b \<and> p = x1 \<and> q = x2b) \<and>
              (\<exists>So. M f None = Some So)} \<union>
             {((p, p'), the (F (M f) (\<sigma>1 \<inter> \<sigma>2)), q, q') |p p' \<sigma>1 \<sigma>2 q q' f.
              (p, (Some \<sigma>1, f), q) \<in> T1 \<and>
              ((p, (Some \<sigma>1, f), q) \<in> it \<longrightarrow>
               f = x2a \<and> Some \<sigma>1 = x1b \<and> p = x1 \<and> q = x2b) \<and>
              (p', \<sigma>2, q') \<in> T2 \<and> \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>So. F (M f) (\<sigma>1 \<inter> \<sigma>2) = Some So)}"
          show "x \<in> {((p, p'), the (M f None), q, p') |p p' q f.
               p' \<in> Q \<and>
               (p, (None, f), q) \<in> T1 \<and>
               ((p, (None, f), q) \<in> it \<longrightarrow> f = x2a \<and> None = x1b \<and> p = x1 \<and> q = x2b) \<and>
               (\<exists>So. M f None = Some So)} \<union>
              {((p, p'), the (F (M f) (\<sigma>1 \<inter> \<sigma>2)), q, q') |p p' \<sigma>1 \<sigma>2 q q' f.
               (p, (Some \<sigma>1, f), q) \<in> T1 \<and>
               (p, (Some \<sigma>1, f), q) \<notin> it \<and>
               (p', \<sigma>2, q') \<in> T2 \<and>
               \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>So. F (M f) (\<sigma>1 \<inter> \<sigma>2) = Some So)} \<union>
              {((x1, q1), the (F (M x2a) (the x1b \<inter> \<alpha>')), x2b, q1') |q1 q1' \<alpha>'.
               (q1, \<alpha>', q1') \<in> T2 \<and>
               the x1b \<inter> \<alpha>' \<noteq> {} \<and> (\<exists>y. F (M x2a) (the x1b \<inter> \<alpha>') = Some y)}"
          proof (cases "x \<in> {((p, p'), the (M f None), q, p') |p p' q f.
              p' \<in> Q \<and>
              (p, (None, f), q) \<in> T1 \<and>
              ((p, (None, f), q) \<in> it \<longrightarrow> f = x2a \<and> None = x1b \<and> p = x1 \<and> q = x2b) \<and>
              (\<exists>So. M f None = Some So)}")
          case True
          then show ?thesis by auto
          next
            case False
            from this xin
            have xin': "x \<in> {((p, p'), the (F (M f) (\<sigma>1 \<inter> \<sigma>2)), q, q') |p p' \<sigma>1 \<sigma>2 q q' f.
          (p, (Some \<sigma>1, f), q) \<in> T1 \<and>
          ((p, (Some \<sigma>1, f), q) \<in> it \<longrightarrow> f = x2a \<and> Some \<sigma>1 = x1b \<and> p = x1 \<and> q = x2b) \<and>
          (p', \<sigma>2, q') \<in> T2 \<and> \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>So. F (M f) (\<sigma>1 \<inter> \<sigma>2) = Some So)}"
              by force
            from this show ?thesis by fastforce
          qed
        }
        {
          fix x
          assume xin: "x \<in> {((p, p'), q, p') |p p' q.
              p' \<in> Q \<and>
              (\<exists>f. (p, (None, f), q) \<in> T1 \<and>
                   (p, (None, f), q) \<notin> it \<and> M f None = None)} \<union>
             {uu.
              \<exists>p p' \<sigma>1 \<sigma>2 q q'.
                 uu = ((p, p'), q, q') \<and>
                 (\<exists>f. (p, (Some \<sigma>1, f), q) \<in> T1 \<and>
                      (p, (Some \<sigma>1, f), q) \<notin> it \<and>
                      (p', \<sigma>2, q') \<in> T2 \<and>
                      \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>x\<in>\<sigma>1 \<inter> \<sigma>2. M f (Some x) = None))} \<union>
             {((x1, q1), x2b, q1') |q1 q1'.
              \<exists>\<alpha>'. (q1, \<alpha>', q1') \<in> T2 \<and>
                    the x1b \<inter> \<alpha>' \<noteq> {} \<and> fe (M x2a) (the x1b \<inter> \<alpha>')}"
          show "x \<in> {((p, p'), q, p') |p p' q.
               p' \<in> Q \<and>
               (\<exists>f. (p, (None, f), q) \<in> T1 \<and>
                    ((p, (None, f), q) \<in> it \<longrightarrow>
                     f = x2a \<and> None = x1b \<and> p = x1 \<and> q = x2b) \<and>
                    M f None = None)} \<union>
              {uu.
               \<exists>p p' \<sigma>1 \<sigma>2 q q'.
                  uu = ((p, p'), q, q') \<and>
                  (\<exists>f. (p, (Some \<sigma>1, f), q) \<in> T1 \<and>
                       ((p, (Some \<sigma>1, f), q) \<in> it \<longrightarrow>
                        f = x2a \<and> Some \<sigma>1 = x1b \<and> p = x1 \<and> q = x2b) \<and>
                       (p', \<sigma>2, q') \<in> T2 \<and>
                       \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>x\<in>\<sigma>1 \<inter> \<sigma>2. M f (Some x) = None))}"
          proof (cases "x \<in> {((p, p'), q, p') |p p' q.
              p' \<in> Q \<and>
              (\<exists>f. (p, (None, f), q) \<in> T1 \<and> (p, (None, f), q) \<notin> it \<and> M f None = None)}")
            case True
              then show ?thesis by auto
            next
              case False
              from this xin
              have xin': "x \<in> {uu.
          \<exists>p p' \<sigma>1 \<sigma>2 q q'.
             uu = ((p, p'), q, q') \<and>
             (\<exists>f. (p, (Some \<sigma>1, f), q) \<in> T1 \<and>
                  (p, (Some \<sigma>1, f), q) \<notin> it \<and>
                  (p', \<sigma>2, q') \<in> T2 \<and>
                  \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>x\<in>\<sigma>1 \<inter> \<sigma>2. M f (Some x) = None))} \<union>
         {((x1, q1), x2b, q1') |q1 q1'.
          \<exists>\<alpha>'. (q1, \<alpha>', q1') \<in> T2 \<and> the x1b \<inter> \<alpha>' \<noteq> {} \<and> fe (M x2a) (the x1b \<inter> \<alpha>')}"
                by force
              then show ?thesis 
              proof (cases "x \<in> {uu.
          \<exists>p p' \<sigma>1 \<sigma>2 q q'.
             uu = ((p, p'), q, q') \<and>
             (\<exists>f. (p, (Some \<sigma>1, f), q) \<in> T1 \<and>
                  (p, (Some \<sigma>1, f), q) \<notin> it \<and>
                  (p', \<sigma>2, q') \<in> T2 \<and>
                  \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>x\<in>\<sigma>1 \<inter> \<sigma>2. M f (Some x) = None))}")
              case True
                then show ?thesis by fastforce
              next
                case False
                from this xin'
                have xin'': "x \<in> {((x1, q1), x2b, q1') |q1 q1'.
          \<exists>\<alpha>'. (q1, \<alpha>', q1') \<in> T2 \<and> the x1b \<inter> \<alpha>' \<noteq> {} \<and> fe (M x2a) (the x1b \<inter> \<alpha>')}"
                  by force
            from x1b_def
              obtain y where y_def: "x1b = Some y" by auto
                
              from xin'' 
              obtain q1 q1' \<alpha>' where
              q1q1'\<alpha>_def: "x = ((x1, q1), x2b, q1') \<and> 
              (q1, \<alpha>', q1') \<in> T2 \<and> the x1b \<inter> \<alpha>' \<noteq> {} \<and> fe (M x2a) (the x1b \<inter> \<alpha>')" 
                by force
              from this fe_ok
              have q1q1'\<alpha>_def': "x = ((x1, q1), x2b, q1') \<and> 
              (q1, \<alpha>', q1') \<in> T2 \<and> the x1b \<inter> \<alpha>' \<noteq> {} \<and> 
                  (\<exists>x\<in>the x1b \<inter> \<alpha>'. (M x2a) (Some x) = None)"
                by auto

from this xinit itin x1b_def y_def
              have "x \<in> {uu.
          \<exists>p p' \<sigma>1 \<sigma>2 q q'.
             uu = ((p, p'), q, q') \<and>
             (\<exists>f. (p, (Some \<sigma>1, f), q) \<in> T1 \<and>
                  ((p, (Some \<sigma>1, f), q) \<in> it \<longrightarrow>
                   f = x2a \<and> Some \<sigma>1 = x1b \<and> p = x1 \<and> q = x2b) \<and>
                  (p', \<sigma>2, q') \<in> T2 \<and>
                  \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>x\<in>\<sigma>1 \<inter> \<sigma>2. M f (Some x) = None))}"
                by force
              from this
              show ?thesis 
                by auto
              qed
              
            qed
          }
          {
            fix x
            assume xin: " x \<in> {((p, p'), q, p') |p p' q.
              p' \<in> Q \<and>
              (\<exists>f. (p, (None, f), q) \<in> T1 \<and>
                   ((p, (None, f), q) \<in> it \<longrightarrow>
                    f = x2a \<and> None = x1b \<and> p = x1 \<and> q = x2b) \<and>
                   M f None = None)} \<union>
             {uu.
              \<exists>p p' \<sigma>1 \<sigma>2 q q'.
                 uu = ((p, p'), q, q') \<and>
                 (\<exists>f. (p, (Some \<sigma>1, f), q) \<in> T1 \<and>
                      ((p, (Some \<sigma>1, f), q) \<in> it \<longrightarrow>
                       f = x2a \<and> Some \<sigma>1 = x1b \<and> p = x1 \<and> q = x2b) \<and>
                      (p', \<sigma>2, q') \<in> T2 \<and>
                      \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>x\<in>\<sigma>1 \<inter> \<sigma>2. M f (Some x) = None))}"
            show "x \<in> {((p, p'), q, p') |p p' q.
               p' \<in> Q \<and>
               (\<exists>f. (p, (None, f), q) \<in> T1 \<and>
                    (p, (None, f), q) \<notin> it \<and> M f None = None)} \<union>
              {uu.
               \<exists>p p' \<sigma>1 \<sigma>2 q q'.
                  uu = ((p, p'), q, q') \<and>
                  (\<exists>f. (p, (Some \<sigma>1, f), q) \<in> T1 \<and>
                       (p, (Some \<sigma>1, f), q) \<notin> it \<and>
                       (p', \<sigma>2, q') \<in> T2 \<and>
                       \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>x\<in>\<sigma>1 \<inter> \<sigma>2. M f (Some x) = None))} \<union>
              {((x1, q1), x2b, q1') |q1 q1'.
               \<exists>\<alpha>'. (q1, \<alpha>', q1') \<in> T2 \<and> the x1b \<inter> \<alpha>' \<noteq> {} \<and> fe (M x2a) (the x1b \<inter> \<alpha>')}"
              proof (cases "x \<in> {uu.
              \<exists>p p' \<sigma>1 \<sigma>2 q q'.
                 uu = ((p, p'), q, q') \<and>
                 (\<exists>f. (p, (Some \<sigma>1, f), q) \<in> T1 \<and>
                      ((p, (Some \<sigma>1, f), q) \<in> it \<longrightarrow>
                       f = x2a \<and> Some \<sigma>1 = x1b \<and> p = x1 \<and> q = x2b) \<and>
                      (p', \<sigma>2, q') \<in> T2 \<and>
                      \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>x\<in>\<sigma>1 \<inter> \<sigma>2. M f (Some x) = None))}")
                case True
                from this
                obtain p p' \<sigma>1 \<sigma>2 q q' f
                  where inc_def: "x = ((p, p'), q, q') \<and> ((p, (Some \<sigma>1, f), q) \<in> T1 \<and>
                    ((p, (Some \<sigma>1, f), q) \<in> it \<longrightarrow>
                     f = x2a \<and> Some \<sigma>1 = x1b \<and> p = x1 \<and> q = x2b) \<and>
                    (p', \<sigma>2, q') \<in> T2 \<and>
                    \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>x\<in>\<sigma>1 \<inter> \<sigma>2. M f (Some x) = None))"
                  by fastforce
                from this fe_ok
                have fe_ok': "fe (M f) (\<sigma>1 \<inter> \<sigma>2)" by auto 
                show ?thesis 
                proof (cases "(p, (Some \<sigma>1, f), q) \<in> it")
                  case True
                  from this inc_def fe_ok'                  
                  have "x \<in> {((x1, q1), x2b, q1') |q1 q1'.
                          \<exists>\<alpha>'. (q1, \<alpha>', q1') \<in> T2 \<and> the x1b \<inter> \<alpha>' \<noteq> {} \<and> 
                            fe (M x2a) (the x1b \<inter> \<alpha>')}" 
                    apply simp
                    by force
                  then show ?thesis by auto 
                next
                  case False
                  from this inc_def
                  have " x = ((p, p'), q, q') \<and>
                          (p, (Some \<sigma>1, f), q) \<in> T1 \<and> (p', \<sigma>2, q') \<in> T2 \<and> \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> 
                            (\<exists>x\<in>\<sigma>1 \<inter> \<sigma>2. M f (Some x) = None)"
                    by force
                  from this False
                  show ?thesis 
                    by fastforce
                qed 
              next
                case False
                from this xin
                have xin': "x \<in> {((p, p'), q, p') |p p' q.
          p' \<in> Q \<and>
          (\<exists>f. (p, (None, f), q) \<in> T1 \<and>
               ((p, (None, f), q) \<in> it \<longrightarrow> f = x2a \<and> None = x1b \<and> p = x1 \<and> q = x2b) \<and>
              M f None = None)}" by force
                from this obtain p p' q f
                  where pp'q_def: "x = ((p, p'), q, p') \<and> p' \<in> Q \<and> (p, (None, f), q) \<in> T1 \<and>
               ((p, (None, f), q) \<in> it \<longrightarrow> f = x2a \<and> None = x1b \<and> p = x1 \<and> q = x2b) \<and>
               M f None = None"
                  by force
                from this show ?thesis 
                proof (cases "(p, (None, f), q) \<in> it")
                  case True 
                  from this pp'q_def
                  show ?thesis apply simp 
                    using x1b_def by blast
                next
                  case False
                  from this pp'q_def
                  have "x = ((p, p'), q, p') \<and> p' \<in> Q \<and>
                          (p, (None, f), q) \<in> T1 \<and> M f None = None"
                    by auto
                  from this False
                  show ?thesis by auto
                  qed
              qed
          }
        qed

        thm subtrans_comp_correct
        from c1 subtrans_comp_correct[OF finiteT2, of M x1 "the x1b" x2a x2b F fe 
                    "({((p, p'), the (M f None), q, p') |p p' q f.
          p' \<in> Q \<and>
          (p, (None, f), q) \<in> T1 \<and> (p, (None, f), q) \<notin> it \<and> (\<exists>So. M f None = Some So)} \<union>
         {((p, p'), the (F (M f) (\<sigma>1 \<inter> \<sigma>2)), q, q') |p p' \<sigma>1 \<sigma>2 q q' f.
          (p, (Some \<sigma>1, f), q) \<in> T1 \<and>
          (p, (Some \<sigma>1, f), q) \<notin> it \<and>
          (p', \<sigma>2, q') \<in> T2 \<and> \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>So. F (M f) (\<sigma>1 \<inter> \<sigma>2) = Some So)})" 
                      
          "({((p, p'), q, p') |p p' q.
          p' \<in> Q \<and>
          (\<exists>f. (p, (None, f), q) \<in> T1 \<and> (p, (None, f), q) \<notin> it \<and> (M f) None = None)} \<union>
         {uu.
          \<exists>p p' \<sigma>1 \<sigma>2 q q'.
             uu = ((p, p'), q, q') \<and>
             (\<exists>f. (p, (Some \<sigma>1, f), q) \<in> T1 \<and>
                  (p, (Some \<sigma>1, f), q) \<notin> it \<and>
                  (p', \<sigma>2, q') \<in> T2 \<and>
                  \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>x\<in>\<sigma>1 \<inter> \<sigma>2. (M f) (Some x) = None))})"]
    show "subtrans_comp M x1 (the x1b) x2a x2b F fe T2
        ({((p, p'), the (M f None), q, p') |p p' q f.
          p' \<in> Q \<and>
          (p, (None, f), q) \<in> T1 \<and> (p, (None, f), q) \<notin> it \<and> (\<exists>So. (M f) None = Some So)} \<union>
         {((p, p'), the (F (M f) (\<sigma>1 \<inter> \<sigma>2)), q, q') |p p' \<sigma>1 \<sigma>2 q q' f.
          (p, (Some \<sigma>1, f), q) \<in> T1 \<and>
          (p, (Some \<sigma>1, f), q) \<notin> it \<and>
          (p', \<sigma>2, q') \<in> T2 \<and> \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>So. F (M f) (\<sigma>1 \<inter> \<sigma>2) = Some So)})
        ({((p, p'), q, p') |p p' q.
          p' \<in> Q \<and>
          (\<exists>f. (p, (None, f), q) \<in> T1 \<and> (p, (None, f), q) \<notin> it \<and> (M f) None = None)} \<union>
         {uu.
          \<exists>p p' \<sigma>1 \<sigma>2 q q'.
             uu = ((p, p'), q, q') \<and>
             (\<exists>f. (p, (Some \<sigma>1, f), q) \<in> T1 \<and>
                  (p, (Some \<sigma>1, f), q) \<notin> it \<and>
                  (p', \<sigma>2, q') \<in> T2 \<and>
                  \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>x\<in>\<sigma>1 \<inter> \<sigma>2. (M f) (Some x) = None))})
       \<le> RES {({((p, p'), the ((M f) None), q, p') |p p' q f.
                 p' \<in> Q \<and>
                 (p, (None, f), q) \<in> T1 \<and>
                 ((p, (None, f), q) \<in> it \<longrightarrow>
                  f = x2a \<and> None = x1b \<and> p = x1 \<and> q = x2b) \<and>
                 (\<exists>So. (M f) None = Some So)} \<union>
                {((p, p'), the (F (M f) (\<sigma>1 \<inter> \<sigma>2)), q, q') |p p' \<sigma>1 \<sigma>2 q q' f.
                 (p, (Some \<sigma>1, f), q) \<in> T1 \<and>
                 ((p, (Some \<sigma>1, f), q) \<in> it \<longrightarrow>
                  f = x2a \<and> Some \<sigma>1 = x1b \<and> p = x1 \<and> q = x2b) \<and>
                 (p', \<sigma>2, q') \<in> T2 \<and> \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>So. F (M f) (\<sigma>1 \<inter> \<sigma>2) = Some So)},
                {((p, p'), q, p') |p p' q.
                 p' \<in> Q \<and>
                 (\<exists>f. (p, (None, f), q) \<in> T1 \<and>
                      ((p, (None, f), q) \<in> it \<longrightarrow>
                       f = x2a \<and> None = x1b \<and> p = x1 \<and> q = x2b) \<and>
                      (M f) None = None)} \<union>
                {uu.
                 \<exists>p p' \<sigma>1 \<sigma>2 q q'.
                    uu = ((p, p'), q, q') \<and>
                    (\<exists>f. (p, (Some \<sigma>1, f), q) \<in> T1 \<and>
                         ((p, (Some \<sigma>1, f), q) \<in> it \<longrightarrow>
                          f = x2a \<and> Some \<sigma>1 = x1b \<and> p = x1 \<and> q = x2b) \<and>
                         (p', \<sigma>2, q') \<in> T2 \<and>
                         \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>x\<in>\<sigma>1 \<inter> \<sigma>2. (M f) (Some x) = None))})}"
      by (simp add: SPEC_trans)
      
  }
qed

definition prods where
  "prods Q1 Q2 = 
   FOREACHi (\<lambda> Q1r Qn. Qn = (Q1 - Q1r) \<times> Q2) 
     Q1 (\<lambda> q Q. do { 
        S \<leftarrow>  FOREACHi (\<lambda> Q2r Qn'. Qn' = {q} \<times> (Q2 - Q2r)) 
          Q2 (\<lambda> q' Q'. RETURN (Q' \<union> {(q,q')})) {};
        RETURN (Q \<union> S)
    }) {}"

lemma prods_correct:
  fixes Q1 Q2
  assumes Q1_finite: "finite Q1"
      and Q2_finite: "finite Q2"
  shows "prods Q1 Q2 \<le> SPEC (\<lambda> Q. Q = (Q1 \<times> Q2))"
  unfolding prods_def
  apply (refine_vcg)
  using Q1_finite apply force
  apply force
  using Q2_finite apply force
  apply force
  apply force
  apply force
  apply force
  done

definition productT_imp where
  "productT_imp \<T> \<A> F fe = do {
    Q \<leftarrow> prods (\<Q>T \<T>) (\<Q> \<A>);
    (D1, D2) \<leftarrow> trans_comp (\<M> \<T>) F fe  (\<Delta>T \<T>) (\<Delta> \<A>) (\<Q> \<A>);
    I \<leftarrow> prods (\<I>T \<T>) (\<I> \<A>);
    F \<leftarrow> prods (\<F>T \<T>) (\<F> \<A>);
    RETURN \<lparr> \<Q>e = Q, \<Delta>e = D1, \<Delta>e' = D2, \<I>e = I, \<F>e = F\<rparr>
  }"


lemma productT_imp_correct:
  assumes finite_TT: "finite (\<Delta>T \<T>)"    
      and finite_TA: "finite (\<Delta> \<A>)"
      and finite_Q: "finite (\<Q> \<A>)"
      and finite_TQ: "finite (\<Q>T \<T>)"
      and finite_I: "finite (\<I> \<A>)"
      and finite_TI: "finite (\<I>T \<T>)"
      and finite_F: "finite (\<F> \<A>)"
      and finite_TF: "finite (\<F>T \<T>)"
      and fe_ok: "\<forall>f \<alpha>. fe f \<alpha> = (\<exists>x\<in>\<alpha>. f (Some x) = None)"
  shows "productT_imp \<T> \<A> F fe \<le> SPEC (\<lambda> A. A = productT \<T> \<A> F)"
  unfolding productT_imp_def
  apply (refine_vcg)
proof -
  thm prods_correct[OF finite_TQ finite_Q]

  have c1: "SPEC (\<lambda>Q. Q = \<Q>T \<T> \<times> NFA_rec.\<Q> \<A>) \<le>
            SPEC (\<lambda>Q. trans_comp (\<M> \<T>) F fe (\<Delta>T \<T>) (NFA_rec.\<Delta> \<A>)
                       (NFA_rec.\<Q> \<A>) \<bind>
                      (\<lambda>(D1, D2).
                          prods (\<I>T \<T>) (NFA_rec.\<I> \<A>) \<bind>
                          (\<lambda>I. prods (\<F>T \<T>) (NFA_rec.\<F> \<A>) \<bind>
                               (\<lambda>F. RETURN
                                     \<lparr>\<Q>e = Q, \<Delta>e = D1, \<Delta>e' = D2, \<I>e = I,
                                        \<F>e = F\<rparr>)))
                 \<le> SPEC (\<lambda>A. A = productT \<T> \<A> F))"
    apply simp
  proof -
    have "trans_comp (\<M> \<T>) F fe (\<Delta>T \<T>) (NFA_rec.\<Delta> \<A>)
     (NFA_rec.\<Q> \<A>) \<bind>
    (\<lambda>(D1, D2).
        prods (\<I>T \<T>) (NFA_rec.\<I> \<A>) \<bind>
        (\<lambda>I. prods (\<F>T \<T>) (NFA_rec.\<F> \<A>) \<bind>
             (\<lambda>F. RETURN
                   \<lparr>\<Q>e = \<Q>T \<T> \<times> NFA_rec.\<Q> \<A>, \<Delta>e = D1,
                      \<Delta>e' = D2, \<I>e = I, \<F>e = F\<rparr>)))
    \<le> SPEC (\<lambda> A. A = productT \<T> \<A> F)"
      apply refine_vcg
    proof -

      have "SPEC (\<lambda>(Dn1, Dn2).
            Dn1 =
            {((p, p'), the ((\<M> \<T>) f None), q, p') |p p' q f.
             p' \<in> NFA_rec.\<Q> \<A> \<and>
             (p, (None, f), q) \<in> \<Delta>T \<T> \<and> (\<exists>So. (\<M> \<T>) f None = Some So)} \<union>
            {((p, p'), the (F ((\<M> \<T>) f) (\<sigma>1 \<inter> \<sigma>2)), q, q') |p p' \<sigma>1 \<sigma>2 q q' f.
             (p, (Some \<sigma>1, f), q) \<in> \<Delta>T \<T> \<and>
             (p', \<sigma>2, q') \<in> NFA_rec.\<Delta> \<A> \<and>
             \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>So. F ((\<M> \<T>) f) (\<sigma>1 \<inter> \<sigma>2) = Some So)} \<and>
            Dn2 =
            {uu.
             \<exists>p p' q f.
                uu = ((p, p'), q, p') \<and>
                p' \<in> NFA_rec.\<Q> \<A> \<and>
                (p, (None, f), q) \<in> \<Delta>T \<T> \<and> (\<M> \<T>) f None = None} \<union>
            {uu.
             \<exists>p p' \<sigma>1 \<sigma>2 q q' f.
                uu = ((p, p'), q, q') \<and>
                (p, (Some \<sigma>1, f), q) \<in> \<Delta>T \<T> \<and>
                (p', \<sigma>2, q') \<in> NFA_rec.\<Delta> \<A> \<and>
                \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>x\<in>\<sigma>1 \<inter> \<sigma>2. (\<M> \<T>) f (Some x) = None)}) \<le> 
            SPEC (\<lambda>x. (case x of
                  (D1, D2) \<Rightarrow>
                    prods (\<I>T \<T>) (NFA_rec.\<I> \<A>) \<bind>
                    (\<lambda>I. prods (\<F>T \<T>) (NFA_rec.\<F> \<A>) \<bind>
                         (\<lambda>F. RETURN
                               \<lparr>\<Q>e = \<Q>T \<T> \<times> NFA_rec.\<Q> \<A>,
                                  \<Delta>e = D1, \<Delta>e' = D2, \<I>e = I, \<F>e = F\<rparr>)))
                 \<le> SPEC (\<lambda>A. A = productT \<T> \<A> F))"
        apply simp
        unfolding productT_def
        apply simp
      proof -
        have "prods (\<I>T \<T>) (NFA_rec.\<I> \<A>) \<bind>
    (\<lambda>I. prods (\<F>T \<T>) (NFA_rec.\<F> \<A>) \<bind>
         (\<lambda>Fa. RETURN
                \<lparr>\<Q>e = \<Q>T \<T> \<times> NFA_rec.\<Q> \<A>, 
                   \<Delta>e = {((p, p'), the (\<M> \<T> f None), q, p') |p p' q f.
                          p' \<in> NFA_rec.\<Q> \<A> \<and>
                          (p, (None, f), q) \<in> \<Delta>T \<T> \<and> (\<exists>So. \<M> \<T> f None = Some So)} \<union>
                         {((p, p'), the (F (\<M> \<T> f) (\<sigma>1 \<inter> \<sigma>2)), q, q') |p p' \<sigma>1 \<sigma>2 q
                          q' f.
                          (p, (Some \<sigma>1, f), q) \<in> \<Delta>T \<T> \<and>
                          (p', \<sigma>2, q') \<in> NFA_rec.\<Delta> \<A> \<and>
                          \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>So. F (\<M> \<T> f) (\<sigma>1 \<inter> \<sigma>2) = Some So)},
                   \<Delta>e' =
                     {((p, p'), q, p') |p p' q.
                      p' \<in> NFA_rec.\<Q> \<A> \<and>
                      (\<exists>f. (p, (None, f), q) \<in> \<Delta>T \<T> \<and> \<M> \<T> f None = None)} \<union>
                     {uu.
                      \<exists>p p' \<sigma>1 \<sigma>2 q q'.
                         uu = ((p, p'), q, q') \<and>
                         (\<exists>f. (p, (Some \<sigma>1, f), q) \<in> \<Delta>T \<T> \<and>
                              (p', \<sigma>2, q') \<in> NFA_rec.\<Delta> \<A> \<and>
                              \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>x\<in>\<sigma>1 \<inter> \<sigma>2. \<M> \<T> f (Some x) = None))},
                   \<I>e = I, \<F>e = Fa\<rparr>))
    \<le> SPEC (\<lambda> A. A = \<lparr>\<Q>e = \<Q>T \<T> \<times> NFA_rec.\<Q> \<A>, 
               \<Delta>e = {((p, p'), the (\<M> \<T> f None), q, p') |p p' q f.
                      p' \<in> NFA_rec.\<Q> \<A> \<and>
                      (p, (None, f), q) \<in> \<Delta>T \<T> \<and> (\<exists>So. \<M> \<T> f None = Some So)} \<union>
                     {((p, p'), the (F (\<M> \<T> f) (\<sigma>1 \<inter> \<sigma>2)), q, q') |p p' \<sigma>1 \<sigma>2 q q' f.
                      (p, (Some \<sigma>1, f), q) \<in> \<Delta>T \<T> \<and>
                      (p', \<sigma>2, q') \<in> NFA_rec.\<Delta> \<A> \<and>
                      \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>So. F (\<M> \<T> f) (\<sigma>1 \<inter> \<sigma>2) = Some So)},
               \<Delta>e' =
                 {((p, p'), q, p') |p p' q.
                  p' \<in> NFA_rec.\<Q> \<A> \<and>
                  (\<exists>f. (p, (None, f), q) \<in> \<Delta>T \<T> \<and> \<M> \<T> f None = None)} \<union>
                 {uu.
                  \<exists>p p' \<sigma>1 \<sigma>2 q q'.
                     uu = ((p, p'), q, q') \<and>
                     (\<exists>f. (p, (Some \<sigma>1, f), q) \<in> \<Delta>T \<T> \<and>
                          (p', \<sigma>2, q') \<in> NFA_rec.\<Delta> \<A> \<and>
                          \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>x\<in>\<sigma>1 \<inter> \<sigma>2. \<M> \<T> f (Some x) = None))},
               \<I>e = \<I>T \<T> \<times> NFA_rec.\<I> \<A>,
               \<F>e = \<F>T \<T> \<times> NFA_rec.\<F> \<A>\<rparr>)"
          apply (refine_vcg)
        proof -
          have "SPEC (\<lambda>Q. Q = \<I>T \<T> \<times> NFA_rec.\<I> \<A>) \<le>
                SPEC (\<lambda>I. prods (\<F>T \<T>) (NFA_rec.\<F> \<A>) \<bind>
                 (\<lambda>Fa. RETURN
                        \<lparr>\<Q>e = \<Q>T \<T> \<times> NFA_rec.\<Q> \<A>, 
                           \<Delta>e = {((p, p'), the (\<M> \<T> f None), q, p') |p p' q f.
                                  p' \<in> NFA_rec.\<Q> \<A> \<and>
                                  (p, (None, f), q) \<in> \<Delta>T \<T> \<and>
                                  (\<exists>So. \<M> \<T> f None = Some So)} \<union>
                                 {((p, p'), the (F (\<M> \<T> f) (\<sigma>1 \<inter> \<sigma>2)), q, q') |p p'
                                  \<sigma>1 \<sigma>2 q q' f.
                                  (p, (Some \<sigma>1, f), q) \<in> \<Delta>T \<T> \<and>
                                  (p', \<sigma>2, q') \<in> NFA_rec.\<Delta> \<A> \<and>
                                  \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and>
                                  (\<exists>So. F (\<M> \<T> f) (\<sigma>1 \<inter> \<sigma>2) = Some So)},
                           \<Delta>e' =
                             {((p, p'), q, p') |p p' q.
                              p' \<in> NFA_rec.\<Q> \<A> \<and>
                              (\<exists>f. (p, (None, f), q) \<in> \<Delta>T \<T> \<and> \<M> \<T> f None = None)} \<union>
                             {uu.
                              \<exists>p p' \<sigma>1 \<sigma>2 q q'.
                                 uu = ((p, p'), q, q') \<and>
                                 (\<exists>f. (p, (Some \<sigma>1, f), q) \<in> \<Delta>T \<T> \<and>
                                      (p', \<sigma>2, q') \<in> NFA_rec.\<Delta> \<A> \<and>
                                      \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and>
                                      (\<exists>x\<in>\<sigma>1 \<inter> \<sigma>2. \<M> \<T> f (Some x) = None))},
                           \<I>e = I, \<F>e = Fa\<rparr>)
                 \<le> SPEC (\<lambda>A. A = \<lparr>\<Q>e = \<Q>T \<T> \<times> NFA_rec.\<Q> \<A>,
                                    
                                     \<Delta>e = {((p, p'), the (\<M> \<T> f None), q, p') |p p' q
f. p' \<in> NFA_rec.\<Q> \<A> \<and>
   (p, (None, f), q) \<in> \<Delta>T \<T> \<and> (\<exists>So. \<M> \<T> f None = Some So)} \<union>
                                           {((p, p'), the (F (\<M> \<T> f) (\<sigma>1 \<inter> \<sigma>2)), q,
 q') |
p p' \<sigma>1 \<sigma>2 q q' f.
(p, (Some \<sigma>1, f), q) \<in> \<Delta>T \<T> \<and>
(p', \<sigma>2, q') \<in> NFA_rec.\<Delta> \<A> \<and>
\<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>So. F (\<M> \<T> f) (\<sigma>1 \<inter> \<sigma>2) = Some So)},
                                     \<Delta>e' =
                                       {((p, p'), q, p') |p p' q.
                                        p' \<in> NFA_rec.\<Q> \<A> \<and>
                                        (\<exists>f.
(p, (None, f), q) \<in> \<Delta>T \<T> \<and> \<M> \<T> f None = None)} \<union>
                                       {uu.
                                        \<exists>p p' \<sigma>1 \<sigma>2 q q'.
                                           uu = ((p, p'), q, q') \<and>
                                           (\<exists>f.
   (p, (Some \<sigma>1, f), q) \<in> \<Delta>T \<T> \<and>
   (p', \<sigma>2, q') \<in> NFA_rec.\<Delta> \<A> \<and>
   \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>x\<in>\<sigma>1 \<inter> \<sigma>2. \<M> \<T> f (Some x) = None))},
                                     \<I>e = \<I>T \<T> \<times> NFA_rec.\<I> \<A>,
                                     \<F>e = \<F>T \<T> \<times> NFA_rec.\<F> \<A>\<rparr>))"
            apply simp
          proof -
            have "prods (\<F>T \<T>) (NFA_rec.\<F> \<A>) \<bind>
    (\<lambda>Fa. RETURN
           \<lparr>\<Q>e = \<Q>T \<T> \<times> NFA_rec.\<Q> \<A>, 
              \<Delta>e = {((p, p'), the (\<M> \<T> f None), q, p') |p p' q f.
                     p' \<in> NFA_rec.\<Q> \<A> \<and>
                     (p, (None, f), q) \<in> \<Delta>T \<T> \<and> (\<exists>So. \<M> \<T> f None = Some So)} \<union>
                    {((p, p'), the (F (\<M> \<T> f) (\<sigma>1 \<inter> \<sigma>2)), q, q') |p p' \<sigma>1 \<sigma>2 q q' f.
                     (p, (Some \<sigma>1, f), q) \<in> \<Delta>T \<T> \<and>
                     (p', \<sigma>2, q') \<in> NFA_rec.\<Delta> \<A> \<and>
                     \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>So. F (\<M> \<T> f) (\<sigma>1 \<inter> \<sigma>2) = Some So)},
              \<Delta>e' =
                {((p, p'), q, p') |p p' q.
                 p' \<in> NFA_rec.\<Q> \<A> \<and>
                 (\<exists>f. (p, (None, f), q) \<in> \<Delta>T \<T> \<and> \<M> \<T> f None = None)} \<union>
                {uu.
                 \<exists>p p' \<sigma>1 \<sigma>2 q q'.
                    uu = ((p, p'), q, q') \<and>
                    (\<exists>f. (p, (Some \<sigma>1, f), q) \<in> \<Delta>T \<T> \<and>
                         (p', \<sigma>2, q') \<in> NFA_rec.\<Delta> \<A> \<and>
                         \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>x\<in>\<sigma>1 \<inter> \<sigma>2. \<M> \<T> f (Some x) = None))},
              \<I>e = \<I>T \<T> \<times> NFA_rec.\<I> \<A>, \<F>e = Fa\<rparr>)
    \<le> SPEC (\<lambda> A. A = \<lparr>\<Q>e = \<Q>T \<T> \<times> NFA_rec.\<Q> \<A>, 
               \<Delta>e = {((p, p'), the (\<M> \<T> f None), q, p') |p p' q f.
                      p' \<in> NFA_rec.\<Q> \<A> \<and>
                      (p, (None, f), q) \<in> \<Delta>T \<T> \<and> (\<exists>So. \<M> \<T> f None = Some So)} \<union>
                     {((p, p'), the (F (\<M> \<T> f) (\<sigma>1 \<inter> \<sigma>2)), q, q') |p p' \<sigma>1 \<sigma>2 q q' f.
                      (p, (Some \<sigma>1, f), q) \<in> \<Delta>T \<T> \<and>
                      (p', \<sigma>2, q') \<in> NFA_rec.\<Delta> \<A> \<and>
                      \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>So. F (\<M> \<T> f) (\<sigma>1 \<inter> \<sigma>2) = Some So)},
               \<Delta>e' =
                 {((p, p'), q, p') |p p' q.
                  p' \<in> NFA_rec.\<Q> \<A> \<and>
                  (\<exists>f. (p, (None, f), q) \<in> \<Delta>T \<T> \<and> \<M> \<T> f None = None)} \<union>
                 {uu.
                  \<exists>p p' \<sigma>1 \<sigma>2 q q'.
                     uu = ((p, p'), q, q') \<and>
                     (\<exists>f. (p, (Some \<sigma>1, f), q) \<in> \<Delta>T \<T> \<and>
                          (p', \<sigma>2, q') \<in> NFA_rec.\<Delta> \<A> \<and>
                          \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>x\<in>\<sigma>1 \<inter> \<sigma>2. \<M> \<T> f (Some x) = None))},
               \<I>e = \<I>T \<T> \<times> NFA_rec.\<I> \<A>,
               \<F>e = \<F>T \<T> \<times> NFA_rec.\<F> \<A>\<rparr>)"
              apply refine_vcg
            proof -
              have "SPEC (\<lambda>Q. Q = \<F>T \<T> \<times> NFA_rec.\<F> \<A>) \<le> 
                    SPEC (\<lambda>Fa. RETURN
                   \<lparr>\<Q>e = \<Q>T \<T> \<times> NFA_rec.\<Q> \<A>,
                      \<Delta>e = {((p, p'), the (\<M> \<T> f None), q, p') |p p' q f.
                             p' \<in> NFA_rec.\<Q> \<A> \<and>
                             (p, (None, f), q) \<in> \<Delta>T \<T> \<and>
                             (\<exists>So. \<M> \<T> f None = Some So)} \<union>
                            {((p, p'), the (F (\<M> \<T> f) (\<sigma>1 \<inter> \<sigma>2)), q, q') |p p' \<sigma>1 \<sigma>2
                             q q' f.
                             (p, (Some \<sigma>1, f), q) \<in> \<Delta>T \<T> \<and>
                             (p', \<sigma>2, q') \<in> NFA_rec.\<Delta> \<A> \<and>
                             \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>So. F (\<M> \<T> f) (\<sigma>1 \<inter> \<sigma>2) = Some So)},
                      \<Delta>e' =
                        {((p, p'), q, p') |p p' q.
                         p' \<in> NFA_rec.\<Q> \<A> \<and>
                         (\<exists>f. (p, (None, f), q) \<in> \<Delta>T \<T> \<and> \<M> \<T> f None = None)} \<union>
                        {uu.
                         \<exists>p p' \<sigma>1 \<sigma>2 q q'.
                            uu = ((p, p'), q, q') \<and>
                            (\<exists>f. (p, (Some \<sigma>1, f), q) \<in> \<Delta>T \<T> \<and>
                                 (p', \<sigma>2, q') \<in> NFA_rec.\<Delta> \<A> \<and>
                                 \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and>
                                 (\<exists>x\<in>\<sigma>1 \<inter> \<sigma>2. \<M> \<T> f (Some x) = None))},
                      \<I>e = \<I>T \<T> \<times> NFA_rec.\<I> \<A>, \<F>e = Fa\<rparr>
                  \<le> SPEC (\<lambda>A. A = \<lparr>\<Q>e = \<Q>T \<T> \<times> NFA_rec.\<Q> \<A>,
                                     
                                      \<Delta>e = {((p, p'), the (\<M> \<T> f None), q, p') |p p'
 q f.
 p' \<in> NFA_rec.\<Q> \<A> \<and>
 (p, (None, f), q) \<in> \<Delta>T \<T> \<and> (\<exists>So. \<M> \<T> f None = Some So)} \<union>
{((p, p'), the (F (\<M> \<T> f) (\<sigma>1 \<inter> \<sigma>2)), q, q') |p p' \<sigma>1 \<sigma>2 q q' f.
 (p, (Some \<sigma>1, f), q) \<in> \<Delta>T \<T> \<and>
 (p', \<sigma>2, q') \<in> NFA_rec.\<Delta> \<A> \<and>
 \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>So. F (\<M> \<T> f) (\<sigma>1 \<inter> \<sigma>2) = Some So)},
                                      \<Delta>e' =
                                        {((p, p'), q, p') |p p' q.
                                         p' \<in> NFA_rec.\<Q> \<A> \<and>
                                         (\<exists>f.
 (p, (None, f), q) \<in> \<Delta>T \<T> \<and> \<M> \<T> f None = None)} \<union>
                                        {uu.
                                         \<exists>p p' \<sigma>1 \<sigma>2 q q'.
uu = ((p, p'), q, q') \<and>
(\<exists>f. (p, (Some \<sigma>1, f), q) \<in> \<Delta>T \<T> \<and>
     (p', \<sigma>2, q') \<in> NFA_rec.\<Delta> \<A> \<and>
     \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>x\<in>\<sigma>1 \<inter> \<sigma>2. \<M> \<T> f (Some x) = None))},
                                      \<I>e = \<I>T \<T> \<times> NFA_rec.\<I> \<A>,
                                      \<F>e = \<F>T \<T> \<times> NFA_rec.\<F> \<A>\<rparr>))"
                by simp
              from this
              show "prods (\<F>T \<T>) (NFA_rec.\<F> \<A>)
    \<le> SPEC (\<lambda>Fa. RETURN
                   \<lparr>\<Q>e = \<Q>T \<T> \<times> NFA_rec.\<Q> \<A>,
                      \<Delta>e = {((p, p'), the (\<M> \<T> f None), q, p') |p p' q f.
                             p' \<in> NFA_rec.\<Q> \<A> \<and>
                             (p, (None, f), q) \<in> \<Delta>T \<T> \<and>
                             (\<exists>So. \<M> \<T> f None = Some So)} \<union>
                            {((p, p'), the (F (\<M> \<T> f) (\<sigma>1 \<inter> \<sigma>2)), q, q') |p p' \<sigma>1 \<sigma>2
                             q q' f.
                             (p, (Some \<sigma>1, f), q) \<in> \<Delta>T \<T> \<and>
                             (p', \<sigma>2, q') \<in> NFA_rec.\<Delta> \<A> \<and>
                             \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>So. F (\<M> \<T> f) (\<sigma>1 \<inter> \<sigma>2) = Some So)},
                      \<Delta>e' =
                        {((p, p'), q, p') |p p' q.
                         p' \<in> NFA_rec.\<Q> \<A> \<and>
                         (\<exists>f. (p, (None, f), q) \<in> \<Delta>T \<T> \<and> \<M> \<T> f None = None)} \<union>
                        {uu.
                         \<exists>p p' \<sigma>1 \<sigma>2 q q'.
                            uu = ((p, p'), q, q') \<and>
                            (\<exists>f. (p, (Some \<sigma>1, f), q) \<in> \<Delta>T \<T> \<and>
                                 (p', \<sigma>2, q') \<in> NFA_rec.\<Delta> \<A> \<and>
                                 \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and>
                                 (\<exists>x\<in>\<sigma>1 \<inter> \<sigma>2. \<M> \<T> f (Some x) = None))},
                      \<I>e = \<I>T \<T> \<times> NFA_rec.\<I> \<A>, \<F>e = Fa\<rparr>
                  \<le> SPEC (\<lambda>A. A = \<lparr>\<Q>e = \<Q>T \<T> \<times> NFA_rec.\<Q> \<A>,
                                     
                                      \<Delta>e = {((p, p'), the (\<M> \<T> f None), q, p') |p p'
 q f.
 p' \<in> NFA_rec.\<Q> \<A> \<and>
 (p, (None, f), q) \<in> \<Delta>T \<T> \<and> (\<exists>So. \<M> \<T> f None = Some So)} \<union>
{((p, p'), the (F (\<M> \<T> f) (\<sigma>1 \<inter> \<sigma>2)), q, q') |p p' \<sigma>1 \<sigma>2 q q' f.
 (p, (Some \<sigma>1, f), q) \<in> \<Delta>T \<T> \<and>
 (p', \<sigma>2, q') \<in> NFA_rec.\<Delta> \<A> \<and>
 \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>So. F (\<M> \<T> f) (\<sigma>1 \<inter> \<sigma>2) = Some So)},
                                      \<Delta>e' =
                                        {((p, p'), q, p') |p p' q.
                                         p' \<in> NFA_rec.\<Q> \<A> \<and>
                                         (\<exists>f.
 (p, (None, f), q) \<in> \<Delta>T \<T> \<and> \<M> \<T> f None = None)} \<union>
                                        {uu.
                                         \<exists>p p' \<sigma>1 \<sigma>2 q q'.
uu = ((p, p'), q, q') \<and>
(\<exists>f. (p, (Some \<sigma>1, f), q) \<in> \<Delta>T \<T> \<and>
     (p', \<sigma>2, q') \<in> NFA_rec.\<Delta> \<A> \<and>
     \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>x\<in>\<sigma>1 \<inter> \<sigma>2. \<M> \<T> f (Some x) = None))},
                                      \<I>e = \<I>T \<T> \<times> NFA_rec.\<I> \<A>,
                                      \<F>e = \<F>T \<T> \<times> NFA_rec.\<F> \<A>\<rparr>))"
                apply (simp)
                using prods_correct[OF finite_TF finite_F]
                by force
            qed

            from this
            show "prods (\<F>T \<T>) (NFA_rec.\<F> \<A>) \<bind>
    (\<lambda>Fa. RETURN
           \<lparr>\<Q>e = \<Q>T \<T> \<times> NFA_rec.\<Q> \<A>,
              \<Delta>e = {((p, p'), the (\<M> \<T> f None), q, p') |p p' q f.
                     p' \<in> NFA_rec.\<Q> \<A> \<and>
                     (p, (None, f), q) \<in> \<Delta>T \<T> \<and> (\<exists>So. \<M> \<T> f None = Some So)} \<union>
                    {((p, p'), the (F (\<M> \<T> f) (\<sigma>1 \<inter> \<sigma>2)), q, q') |p p' \<sigma>1 \<sigma>2 q q' f.
                     (p, (Some \<sigma>1, f), q) \<in> \<Delta>T \<T> \<and>
                     (p', \<sigma>2, q') \<in> NFA_rec.\<Delta> \<A> \<and>
                     \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>So. F (\<M> \<T> f) (\<sigma>1 \<inter> \<sigma>2) = Some So)},
              \<Delta>e' =
                {((p, p'), q, p') |p p' q.
                 p' \<in> NFA_rec.\<Q> \<A> \<and>
                 (\<exists>f. (p, (None, f), q) \<in> \<Delta>T \<T> \<and> \<M> \<T> f None = None)} \<union>
                {uu.
                 \<exists>p p' \<sigma>1 \<sigma>2 q q'.
                    uu = ((p, p'), q, q') \<and>
                    (\<exists>f. (p, (Some \<sigma>1, f), q) \<in> \<Delta>T \<T> \<and>
                         (p', \<sigma>2, q') \<in> NFA_rec.\<Delta> \<A> \<and>
                         \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>x\<in>\<sigma>1 \<inter> \<sigma>2. \<M> \<T> f (Some x) = None))},
              \<I>e = \<I>T \<T> \<times> NFA_rec.\<I> \<A>, \<F>e = Fa\<rparr>)
    \<le> RES {\<lparr>\<Q>e = \<Q>T \<T> \<times> NFA_rec.\<Q> \<A>,
               \<Delta>e = {((p, p'), the (\<M> \<T> f None), q, p') |p p' q f.
                      p' \<in> NFA_rec.\<Q> \<A> \<and>
                      (p, (None, f), q) \<in> \<Delta>T \<T> \<and> (\<exists>So. \<M> \<T> f None = Some So)} \<union>
                     {((p, p'), the (F (\<M> \<T> f) (\<sigma>1 \<inter> \<sigma>2)), q, q') |p p' \<sigma>1 \<sigma>2 q q' f.
                      (p, (Some \<sigma>1, f), q) \<in> \<Delta>T \<T> \<and>
                      (p', \<sigma>2, q') \<in> NFA_rec.\<Delta> \<A> \<and>
                      \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>So. F (\<M> \<T> f) (\<sigma>1 \<inter> \<sigma>2) = Some So)},
               \<Delta>e' =
                 {((p, p'), q, p') |p p' q.
                  p' \<in> NFA_rec.\<Q> \<A> \<and>
                  (\<exists>f. (p, (None, f), q) \<in> \<Delta>T \<T> \<and> \<M> \<T> f None = None)} \<union>
                 {uu.
                  \<exists>p p' \<sigma>1 \<sigma>2 q q'.
                     uu = ((p, p'), q, q') \<and>
                     (\<exists>f. (p, (Some \<sigma>1, f), q) \<in> \<Delta>T \<T> \<and>
                          (p', \<sigma>2, q') \<in> NFA_rec.\<Delta> \<A> \<and>
                          \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>x\<in>\<sigma>1 \<inter> \<sigma>2. \<M> \<T> f (Some x) = None))},
               \<I>e = \<I>T \<T> \<times> NFA_rec.\<I> \<A>,
               \<F>e = \<F>T \<T> \<times> NFA_rec.\<F> \<A>\<rparr>}"
              by auto
          qed
          from this prods_correct[OF finite_TI finite_I]
          show "prods (\<I>T \<T>) (NFA_rec.\<I> \<A>)
    \<le> SPEC (\<lambda>I. prods (\<F>T \<T>) (NFA_rec.\<F> \<A>) \<bind>
                 (\<lambda>Fa. RETURN
                        \<lparr>\<Q>e = \<Q>T \<T> \<times> NFA_rec.\<Q> \<A>,
                           \<Delta>e = {((p, p'), the (\<M> \<T> f None), q, p') |p p' q f.
                                  p' \<in> NFA_rec.\<Q> \<A> \<and>
                                  (p, (None, f), q) \<in> \<Delta>T \<T> \<and>
                                  (\<exists>So. \<M> \<T> f None = Some So)} \<union>
                                 {((p, p'), the (F (\<M> \<T> f) (\<sigma>1 \<inter> \<sigma>2)), q, q') |p p'
                                  \<sigma>1 \<sigma>2 q q' f.
                                  (p, (Some \<sigma>1, f), q) \<in> \<Delta>T \<T> \<and>
                                  (p', \<sigma>2, q') \<in> NFA_rec.\<Delta> \<A> \<and>
                                  \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and>
                                  (\<exists>So. F (\<M> \<T> f) (\<sigma>1 \<inter> \<sigma>2) = Some So)},
                           \<Delta>e' =
                             {((p, p'), q, p') |p p' q.
                              p' \<in> NFA_rec.\<Q> \<A> \<and>
                              (\<exists>f. (p, (None, f), q) \<in> \<Delta>T \<T> \<and> \<M> \<T> f None = None)} \<union>
                             {uu.
                              \<exists>p p' \<sigma>1 \<sigma>2 q q'.
                                 uu = ((p, p'), q, q') \<and>
                                 (\<exists>f. (p, (Some \<sigma>1, f), q) \<in> \<Delta>T \<T> \<and>
                                      (p', \<sigma>2, q') \<in> NFA_rec.\<Delta> \<A> \<and>
                                      \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and>
                                      (\<exists>x\<in>\<sigma>1 \<inter> \<sigma>2. \<M> \<T> f (Some x) = None))},
                           \<I>e = I, \<F>e = Fa\<rparr>)
                 \<le> SPEC (\<lambda>A. A = \<lparr>\<Q>e = \<Q>T \<T> \<times> NFA_rec.\<Q> \<A>,
                                    
                                     \<Delta>e = {((p, p'), the (\<M> \<T> f None), q, p') |p p' q
f. p' \<in> NFA_rec.\<Q> \<A> \<and>
   (p, (None, f), q) \<in> \<Delta>T \<T> \<and> (\<exists>So. \<M> \<T> f None = Some So)} \<union>
                                           {((p, p'), the (F (\<M> \<T> f) (\<sigma>1 \<inter> \<sigma>2)), q,
 q') |
p p' \<sigma>1 \<sigma>2 q q' f.
(p, (Some \<sigma>1, f), q) \<in> \<Delta>T \<T> \<and>
(p', \<sigma>2, q') \<in> NFA_rec.\<Delta> \<A> \<and>
\<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>So. F (\<M> \<T> f) (\<sigma>1 \<inter> \<sigma>2) = Some So)},
                                     \<Delta>e' =
                                       {((p, p'), q, p') |p p' q.
                                        p' \<in> NFA_rec.\<Q> \<A> \<and>
                                        (\<exists>f.
(p, (None, f), q) \<in> \<Delta>T \<T> \<and> \<M> \<T> f None = None)} \<union>
                                       {uu.
                                        \<exists>p p' \<sigma>1 \<sigma>2 q q'.
                                           uu = ((p, p'), q, q') \<and>
                                           (\<exists>f.
   (p, (Some \<sigma>1, f), q) \<in> \<Delta>T \<T> \<and>
   (p', \<sigma>2, q') \<in> NFA_rec.\<Delta> \<A> \<and>
   \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>x\<in>\<sigma>1 \<inter> \<sigma>2. \<M> \<T> f (Some x) = None))},
                                     \<I>e = \<I>T \<T> \<times> NFA_rec.\<I> \<A>,
                                     \<F>e = \<F>T \<T> \<times> NFA_rec.\<F> \<A>\<rparr>))"
            using SPEC_trans by force
        qed
        from this
        have "prods (\<I>T \<T>) (NFA_rec.\<I> \<A>) \<bind>
    (\<lambda>I. prods (\<F>T \<T>) (NFA_rec.\<F> \<A>) \<bind>
         (\<lambda>Fa. RETURN
                \<lparr>\<Q>e = \<Q>T \<T> \<times> NFA_rec.\<Q> \<A>,
                   \<Delta>e = {((p, p'), the (\<M> \<T> f None), q, p') |p p' q f.
                          p' \<in> NFA_rec.\<Q> \<A> \<and>
                          (p, (None, f), q) \<in> \<Delta>T \<T> \<and> (\<exists>So. \<M> \<T> f None = Some So)} \<union>
                         {((p, p'), the (F (\<M> \<T> f) (\<sigma>1 \<inter> \<sigma>2)), q, q') |p p' \<sigma>1 \<sigma>2 q
                          q' f.
                          (p, (Some \<sigma>1, f), q) \<in> \<Delta>T \<T> \<and>
                          (p', \<sigma>2, q') \<in> NFA_rec.\<Delta> \<A> \<and>
                          \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>So. F (\<M> \<T> f) (\<sigma>1 \<inter> \<sigma>2) = Some So)},
                   \<Delta>e' =
                     {((p, p'), q, p') |p p' q.
                      p' \<in> NFA_rec.\<Q> \<A> \<and>
                      (\<exists>f. (p, (None, f), q) \<in> \<Delta>T \<T> \<and> \<M> \<T> f None = None)} \<union>
                     {uu.
                      \<exists>p p' \<sigma>1 \<sigma>2 q q'.
                         uu = ((p, p'), q, q') \<and>
                         (\<exists>f. (p, (Some \<sigma>1, f), q) \<in> \<Delta>T \<T> \<and>
                              (p', \<sigma>2, q') \<in> NFA_rec.\<Delta> \<A> \<and>
                              \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>x\<in>\<sigma>1 \<inter> \<sigma>2. \<M> \<T> f (Some x) = None))},
                   \<I>e = I, \<F>e = Fa\<rparr>))
    \<le> RES {\<lparr>\<Q>e = \<Q>T \<T> \<times> NFA_rec.\<Q> \<A>,
               \<Delta>e = {((p, p'), the (\<M> \<T> f None), q, p') |p p' q f.
                      p' \<in> NFA_rec.\<Q> \<A> \<and>
                      (p, (None, f), q) \<in> \<Delta>T \<T> \<and> (\<exists>So. \<M> \<T> f None = Some So)} \<union>
                     {((p, p'), the (F (\<M> \<T> f) (\<sigma>1 \<inter> \<sigma>2)), q, q') |p p' \<sigma>1 \<sigma>2 q q' f.
                      (p, (Some \<sigma>1, f), q) \<in> \<Delta>T \<T> \<and>
                      (p', \<sigma>2, q') \<in> NFA_rec.\<Delta> \<A> \<and>
                      \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>So. F (\<M> \<T> f) (\<sigma>1 \<inter> \<sigma>2) = Some So)},
               \<Delta>e' =
                 {((p, p'), q, p') |p p' q.
                  p' \<in> NFA_rec.\<Q> \<A> \<and>
                  (\<exists>f. (p, (None, f), q) \<in> \<Delta>T \<T> \<and> \<M> \<T> f None = None)} \<union>
                 {uu.
                  \<exists>p p' \<sigma>1 \<sigma>2 q q'.
                     uu = ((p, p'), q, q') \<and>
                     (\<exists>f. (p, (Some \<sigma>1, f), q) \<in> \<Delta>T \<T> \<and>
                          (p', \<sigma>2, q') \<in> NFA_rec.\<Delta> \<A> \<and>
                          \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>x\<in>\<sigma>1 \<inter> \<sigma>2. \<M> \<T> f (Some x) = None))},
               \<I>e = \<I>T \<T> \<times> NFA_rec.\<I> \<A>,
               \<F>e = \<F>T \<T> \<times> NFA_rec.\<F> \<A>\<rparr>}"
          by auto
        from this
        show "prods (\<I>T \<T>) (NFA_rec.\<I> \<A>) \<bind>
    (\<lambda>I. prods (\<F>T \<T>) (NFA_rec.\<F> \<A>) \<bind>
         (\<lambda>Fa. RETURN
                \<lparr>\<Q>e = \<Q>T \<T> \<times> NFA_rec.\<Q> \<A>,
                   \<Delta>e = {((p, p'), the (\<M> \<T> f None), q, p') |p p' q f.
                          p' \<in> NFA_rec.\<Q> \<A> \<and>
                          (p, (None, f), q) \<in> \<Delta>T \<T> \<and> (\<exists>So. \<M> \<T> f None = Some So)} \<union>
                         {((p, p'), the (F (\<M> \<T> f) (\<sigma>1 \<inter> \<sigma>2)), q, q') |p p' \<sigma>1 \<sigma>2 q
                          q' f.
                          (p, (Some \<sigma>1, f), q) \<in> \<Delta>T \<T> \<and>
                          (p', \<sigma>2, q') \<in> NFA_rec.\<Delta> \<A> \<and>
                          \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>So. F (\<M> \<T> f) (\<sigma>1 \<inter> \<sigma>2) = Some So)},
                   \<Delta>e' =
                     {((p, p'), q, p') |p p' q.
                      p' \<in> NFA_rec.\<Q> \<A> \<and>
                      (\<exists>f. (p, (None, f), q) \<in> \<Delta>T \<T> \<and> \<M> \<T> f None = None)} \<union>
                     {uu.
                      \<exists>p p' \<sigma>1 \<sigma>2 q q'.
                         uu = ((p, p'), q, q') \<and>
                         (\<exists>f. (p, (Some \<sigma>1, f), q) \<in> \<Delta>T \<T> \<and>
                              (p', \<sigma>2, q') \<in> NFA_rec.\<Delta> \<A> \<and>
                              \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>x\<in>\<sigma>1 \<inter> \<sigma>2. \<M> \<T> f (Some x) = None))},
                   \<I>e = I, \<F>e = Fa\<rparr>))
    \<le> RES {\<lparr>\<Q>e = \<Q>T \<T> \<times> NFA_rec.\<Q> \<A>,
               \<Delta>e = {((p, p'), the (\<M> \<T> f None), q, p') |p p' q f.
                      p' \<in> NFA_rec.\<Q> \<A> \<and>
                      (p, (None, f), q) \<in> \<Delta>T \<T> \<and> (\<exists>So. \<M> \<T> f None = Some So)} \<union>
                     {((p, p'), the (F (\<M> \<T> f) (\<sigma>1 \<inter> \<sigma>2)), q, q') |p p' \<sigma>1 \<sigma>2 q q' f.
                      (p, (Some \<sigma>1, f), q) \<in> \<Delta>T \<T> \<and>
                      (p', \<sigma>2, q') \<in> NFA_rec.\<Delta> \<A> \<and>
                      \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>So. F (\<M> \<T> f) (\<sigma>1 \<inter> \<sigma>2) = Some So)},
               \<Delta>e' =
                 {((p, p'), q, p') |p p' q.
                  p' \<in> NFA_rec.\<Q> \<A> \<and>
                  (\<exists>f. (p, (None, f), q) \<in> \<Delta>T \<T> \<and> \<M> \<T> f None = None)} \<union>
                 {uu.
                  \<exists>p p' \<sigma>1 \<sigma>2 q q'.
                     uu = ((p, p'), q, q') \<and>
                     (\<exists>f. (p, (Some \<sigma>1, f), q) \<in> \<Delta>T \<T> \<and>
                          (p', \<sigma>2, q') \<in> NFA_rec.\<Delta> \<A> \<and>
                          \<sigma>1 \<inter> \<sigma>2 \<noteq> {} \<and> (\<exists>x\<in>\<sigma>1 \<inter> \<sigma>2. \<M> \<T> f (Some x) = None))},
               \<I>e = \<I>T \<T> \<times> NFA_rec.\<I> \<A>,
               \<F>e = \<F>T \<T> \<times> NFA_rec.\<F> \<A>\<rparr>}"
          by auto
      qed

      from this trans_comp_correct[of  "\<Delta>T \<T>" "\<Delta> \<A>" "\<Q> \<A>" fe "\<M> \<T>" F, 
                         OF finite_TT finite_TA finite_Q fe_ok]
      show "trans_comp (\<M> \<T>) F fe (\<Delta>T \<T>) (NFA_rec.\<Delta> \<A>)
     (NFA_rec.\<Q> \<A>)
    \<le> SPEC (\<lambda>x. (case x of
                  (D1, D2) \<Rightarrow>
                    prods (\<I>T \<T>) (NFA_rec.\<I> \<A>) \<bind>
                    (\<lambda>I. prods (\<F>T \<T>) (NFA_rec.\<F> \<A>) \<bind>
                         (\<lambda>F. RETURN
                               \<lparr>\<Q>e = \<Q>T \<T> \<times> NFA_rec.\<Q> \<A>, 
                                  \<Delta>e = D1, \<Delta>e' = D2, \<I>e = I, \<F>e = F\<rparr>)))
                 \<le> SPEC (\<lambda>A. A = productT \<T> \<A> F))"
        using SPEC_trans 
        by force
    qed
    from this
    show "trans_comp (\<M> \<T>) F fe (\<Delta>T \<T>) (NFA_rec.\<Delta> \<A>)
     (NFA_rec.\<Q> \<A>) \<bind>
    (\<lambda>(D1, D2).
        prods (\<I>T \<T>) (NFA_rec.\<I> \<A>) \<bind>
        (\<lambda>I. prods (\<F>T \<T>) (NFA_rec.\<F> \<A>) \<bind>
             (\<lambda>F. RETURN
                   \<lparr>\<Q>e = \<Q>T \<T> \<times> NFA_rec.\<Q> \<A>, \<Delta>e = D1,
                      \<Delta>e' = D2, \<I>e = I, \<F>e = F\<rparr>)))
    \<le> RES {productT \<T> \<A> F}"
      by auto
  qed
  from this prods_correct[OF finite_TQ finite_Q]
  have "prods (\<Q>T \<T>) (NFA_rec.\<Q> \<A>)
    \<le> SPEC (\<lambda>Q.  trans_comp (\<M> \<T>) F fe (\<Delta>T \<T>) (NFA_rec.\<Delta> \<A>)
                       (NFA_rec.\<Q> \<A>) \<bind>
                      (\<lambda>(D1, D2).
                          prods (\<I>T \<T>) (NFA_rec.\<I> \<A>) \<bind>
                          (\<lambda>I. prods (\<F>T \<T>) (NFA_rec.\<F> \<A>) \<bind>
                               (\<lambda>F. RETURN
                                     \<lparr>\<Q>e = Q, \<Delta>e = D1, \<Delta>e' = D2, \<I>e = I,
                                        \<F>e = F\<rparr>)))
                 \<le> SPEC (\<lambda>A. A = productT \<T> \<A> F))"
    using SPEC_trans by force
  from this
  show "prods (\<Q>T \<T>) (NFA_rec.\<Q> \<A>)
    \<le> SPEC (\<lambda>Q. trans_comp (\<M> \<T>) F fe (\<Delta>T \<T>) (NFA_rec.\<Delta> \<A>)
                       (NFA_rec.\<Q> \<A>) \<bind>
                      (\<lambda>(D1, D2).
                          prods (\<I>T \<T>) (NFA_rec.\<I> \<A>) \<bind>
                          (\<lambda>I. prods (\<F>T \<T>) (NFA_rec.\<F> \<A>) \<bind>
                               (\<lambda>F. RETURN
                                     \<lparr>\<Q>e = Q,\<Delta>e = D1, \<Delta>e' = D2, \<I>e = I,
                                        \<F>e = F\<rparr>)))
                 \<le> SPEC (\<lambda>A. A = productT \<T> \<A> F))"
    by auto
qed
  
end
















