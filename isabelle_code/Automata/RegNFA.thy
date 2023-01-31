
theory RegNFA

imports Main NFA_set_interval NFA_epsilon

begin

datatype 'a RegEx = Ep | Atom 'a | IVL 'a 'a | Star "'a RegEx" 
                  | Concat "'a RegEx" "'a RegEx" | Alt "'a RegEx" "'a RegEx" 


inductive_set 
    star_sem :: "'a list set \<Rightarrow> 'a list set" 
    for reg:: "'a list set"  where
  base: "x \<in> reg \<Longrightarrow> x \<in> star_sem reg" |
  step: "\<lbrakk>x \<in> reg; y \<in> star_sem reg\<rbrakk> \<Longrightarrow> x @ y \<in> star_sem reg"


fun semRegEx where
      "semRegEx Ep = {[]}"
    | "semRegEx (Atom a) = {[a]}"
    | "semRegEx (IVL l r) = {[e] | e. l \<le> e \<and> e \<le> r}"
    | "semRegEx (Star e) = star_sem (semRegEx e)"
    | "semRegEx (Concat e1 e2) = {x @ y | x y. x \<in> semRegEx e1 \<and> y \<in> semRegEx e2}"
    | "semRegEx (Alt e1 e2) = (semRegEx e1) \<union> (semRegEx e2)"

fun renameQ :: "'a RegEx set \<Rightarrow> 'a RegEx \<Rightarrow> 'a RegEx set" where 
     "renameQ Q reg = {Concat q reg | q. q \<in> Q}"


fun renameT :: "('a RegEx \<times> 'a set \<times> 'a RegEx) set \<Rightarrow> 'a RegEx \<Rightarrow> 
                ('a RegEx \<times> 'a set \<times> 'a RegEx) set" where 
     "renameT T reg = {(Concat q reg, \<alpha> , Concat q' reg) | q \<alpha> q'.  (q, \<alpha>, q') \<in> T}"

fun renameT' :: "('a RegEx \<times> 'a RegEx) set \<Rightarrow> 'a RegEx \<Rightarrow> 
                 ('a RegEx \<times> 'a RegEx) set" where 
     "renameT' T reg = {(Concat q reg, Concat q' reg) | q q'.  (q, q') \<in> T}"

fun renameNFA where
    "renameNFA \<A> reg = \<lparr> \<Q>e = renameQ (\<Q>e \<A>) reg, \<Sigma>e = \<Sigma>e \<A>, \<Delta>e = renameT (\<Delta>e \<A>) reg, 
                         \<Delta>e' = renameT' (\<Delta>e' \<A>) reg, \<I>e = renameQ (\<I>e \<A>) reg, 
                         \<F>e = renameQ (\<F>e \<A>) reg\<rparr>"



fun RegToNFA :: "('a::ord) set \<Rightarrow> 'a RegEx \<Rightarrow> ('a RegEx,'a) NFAe_rec" where
  "RegToNFA E Ep = \<lparr>\<Q>e = {Ep}, \<Sigma>e = E, \<Delta>e = {}, 
                          \<Delta>e' = {}, \<I>e = {Ep}, \<F>e = {Ep}\<rparr>" |
  "RegToNFA E (Atom a) = \<lparr>\<Q>e = {Atom a}, \<Sigma>e = E, \<Delta>e = {(Atom a, {a}, Ep)}, 
                          \<Delta>e' = {}, \<I>e = {Atom a}, \<F>e = {Ep}\<rparr>" |
  "RegToNFA E (IVL l r) =  \<lparr>\<Q>e = {IVL l r}, \<Sigma>e = E, 
                            \<Delta>e = {(IVL l r, {e. l \<le> e \<and> e \<le> r}, Ep)}, 
                            \<Delta>e' = {}, \<I>e = {IVL l r}, \<F>e = {Ep}\<rparr>" |
  "RegToNFA E (Concat e1 e2) = (let (\<A>1, \<A>2) = (renameNFA (RegToNFA E e1) e2, 
                                                            RegToNFA E e2) in 
                                \<lparr>\<Q>e = {Concat e1 e2} \<union> \<Q>e \<A>1 \<union> \<Q>e \<A>2, \<Sigma>e = E, 
                                \<Delta>e = \<Delta>e \<A>1 \<union> \<Delta>e \<A>2, 
                                \<Delta>e' = {(Concat Ep e2, e2)} \<union> \<Delta>e' \<A>1 \<union> \<Delta>e' \<A>2, 
                                \<I>e = {Concat e1 e2}, \<F>e = {Ep} \<rparr>)" |
  "RegToNFA E (Star e) = (let \<A> = (renameNFA (RegToNFA E e) (Star e)) in 
                           \<lparr>\<Q>e = {Star e}, \<Sigma>e = E, 
                            \<Delta>e = \<Delta>e \<A>, 
                            \<Delta>e' = {(Star e, Concat e (Star e)), 
                                    (Concat Ep (Star e), Star e),
                                     (Star e, Ep)} \<union> (\<Delta>e' \<A>), 
                            \<I>e = {Star e}, \<F>e = {Ep}\<rparr>)" |
  "RegToNFA E (Alt e1 e2) = (let (\<A>1, \<A>2) = (RegToNFA E e1, RegToNFA E e2) in
                             \<lparr> \<Q>e = {Alt e1 e2} \<union> \<Q>e \<A>1 \<union> \<Q>e \<A>2, 
                               \<Sigma>e = E, 
                               \<Delta>e = \<Delta>e \<A>1 \<union> \<Delta>e \<A>2,
                               \<Delta>e' = {(Alt e1 e2, e1), (Alt e1 e2, e2)} \<union> \<Delta>e' \<A>1 \<union> \<Delta>e' \<A>2,
                               \<I>e = {Alt e1 e2},
                               \<F>e = {Ep}
                              \<rparr>)"
 
definition state\<L> where 
   "state\<L> q \<A> = {w | w q'. q' \<in> \<F>e \<A> \<and> LTS_is_reachable_epsilon (\<Delta>e \<A>) (\<Delta>e' \<A>) q w q'}"

definition invar_state\<L>_NFA where
   "invar_state\<L>_NFA \<A> = (\<forall> q \<in> \<Q>e \<A>. state\<L> q \<A> = semRegEx q)"

lemma Union_invar_state\<L>:
  fixes \<A>1 \<A>2
  assumes invarA1: "invar_state\<L>_NFA \<A>1"
      and invarA2: "invar_state\<L>_NFA \<A>2"
      and \<Sigma>_eq: "\<Sigma>e \<A>1 = \<Sigma>e \<A>2"
    shows "invar_state\<L>_NFA 
            \<lparr>\<Q>e = \<Q>e \<A>1 \<union> \<Q>e \<A>2,
             \<Sigma>e = \<Sigma>e \<A>1,
             \<Delta>e = \<Delta>e \<A>1 \<union> \<Delta>e \<A>2,
             \<Delta>e' = \<Delta>e' \<A>1 \<union> \<Delta>e' \<A>2,
             \<I>e = \<I>e \<A>1 \<union> \<I>e \<A>2,
             \<F>e = \<F>e \<A>1 \<union> \<F>e \<A>2\<rparr>"
  unfolding invar_state\<L>_NFA_def
  apply simp
  unfolding state\<L>_def
  apply simp
  apply (rule)
  apply (rule)
  apply (rule)
  defer
  apply rule
proof 
  {
    fix q x
    assume qin: "q \<in> \<Q>e \<A>1 \<union> \<Q>e \<A>2"
       and xin: "x \<in> semRegEx q"
    show "\<exists>q'. (q' \<in> \<F>e \<A>1 \<or> q' \<in> \<F>e \<A>2) \<and>
                LTS_is_reachable_epsilon (\<Delta>e \<A>1 \<union> \<Delta>e \<A>2) (\<Delta>e' \<A>1 \<union> \<Delta>e' \<A>2) q x q'"
    proof (cases "q \<in> \<Q>e \<A>1")
      case True
      from this xin invarA1
      obtain q' where q'_def:"q' \<in> \<F>e \<A>1 \<and> LTS_is_reachable_epsilon (\<Delta>e \<A>1) (\<Delta>e' \<A>1) q x q'"
        unfolding invar_state\<L>_NFA_def state\<L>_def
        by force
      from this
      have "LTS_is_reachable_epsilon (\<Delta>e \<A>1 \<union> \<Delta>e \<A>2) (\<Delta>e' \<A>1 \<union> \<Delta>e' \<A>2) q x q'"
        apply (induction x arbitrary: q)
      proof -
        {
          fix q
        assume reach_ind: "q' \<in> \<F>e \<A>1 \<and> LTS_is_reachable_epsilon (\<Delta>e \<A>1) (\<Delta>e' \<A>1) q [] q'"
        from LTS_is_reachable_epsilon.simps(1)
            [of "\<Delta>e \<A>1" 
                "\<Delta>e' \<A>1" q q'] this
        obtain l where
        l_def: "(l \<noteq> [] \<and> epsilon_reach l (\<Delta>e' \<A>1) \<and> hd l = q \<and> last l = q')"
          by auto
        from this
        have "epsilon_reach l (\<Delta>e' \<A>1)" by auto
        from this
        have "epsilon_reach l (\<Delta>e' \<A>1 \<union> \<Delta>e' \<A>2)"
          apply (induction l)
          apply simp
          using epsilon_reach.elims(3) by fastforce  
        from this 
        show "LTS_is_reachable_epsilon (\<Delta>e \<A>1 \<union> \<Delta>e \<A>2) (\<Delta>e' \<A>1 \<union> \<Delta>e' \<A>2) q [] q'"
          using l_def by auto
      }
      {
        fix a x q
        assume ind_hyp: "(\<And>q. q' \<in> \<F>e \<A>1 \<and> LTS_is_reachable_epsilon (\<Delta>e \<A>1) (\<Delta>e' \<A>1) q x q' \<Longrightarrow>
            LTS_is_reachable_epsilon (\<Delta>e \<A>1 \<union> \<Delta>e \<A>2) (\<Delta>e' \<A>1 \<union> \<Delta>e' \<A>2) q x q')"
           and reach: "q' \<in> \<F>e \<A>1 \<and> LTS_is_reachable_epsilon (\<Delta>e \<A>1) (\<Delta>e' \<A>1) q (a # x) q'"
        from reach LTS_is_reachable_epsilon.simps(2)[of "\<Delta>e \<A>1" "\<Delta>e' \<A>1" q a x q']
        obtain qi qj \<sigma>
          where qiqj\<sigma>_def: "epsilon_reachable q qi (\<Delta>e' \<A>1) \<and>
        a \<in> \<sigma> \<and> (qi, \<sigma>, qj) \<in> \<Delta>e \<A>1 \<and> LTS_is_reachable_epsilon (\<Delta>e \<A>1) (\<Delta>e' \<A>1) qj x q'"
          by force
        from this ind_hyp
        have c1:"LTS_is_reachable_epsilon (\<Delta>e \<A>1 \<union> \<Delta>e \<A>2) (\<Delta>e' \<A>1 \<union> \<Delta>e' \<A>2) qj x q'"
          using q'_def by blast
        from qiqj\<sigma>_def
        obtain l where
        l_def: "l \<noteq> [] \<and> epsilon_reach l (\<Delta>e' \<A>1) \<and> hd l = q \<and> last l = qi"
          unfolding epsilon_reachable_def
          by fastforce
        from this
        have "epsilon_reach l (\<Delta>e' \<A>1)" by auto
        from this
        have "epsilon_reach l (\<Delta>e' \<A>1 \<union> \<Delta>e' \<A>2)"
          apply (induction l)
          apply simp
          using epsilon_reach.elims(3) by fastforce  
        from this l_def
        have c2: "epsilon_reachable q qi (\<Delta>e' \<A>1 \<union> \<Delta>e' \<A>2)"
          unfolding epsilon_reachable_def
          by auto
        from c1 c2 LTS_is_reachable_epsilon.simps(2)[of "\<Delta>e \<A>1 \<union> \<Delta>e \<A>2" 
                                                    "\<Delta>e' \<A>1 \<union> \<Delta>e' \<A>2" q a x q'] qiqj\<sigma>_def
        show "LTS_is_reachable_epsilon (\<Delta>e \<A>1 \<union> \<Delta>e \<A>2) (\<Delta>e' \<A>1 \<union> \<Delta>e' \<A>2) q (a # x) q'"      
          by blast
      }
    qed
    then show ?thesis 
      using q'_def by blast
    next
      case False
      from this
      have "q \<in> \<Q>e \<A>2"
        using qin by auto
      from this xin invarA2
      obtain q' where q'_def:"q' \<in> \<F>e \<A>2 \<and> LTS_is_reachable_epsilon (\<Delta>e \<A>2) (\<Delta>e' \<A>2) q x q'"
        unfolding invar_state\<L>_NFA_def state\<L>_def
        by force
      from this
      have "LTS_is_reachable_epsilon (\<Delta>e \<A>1 \<union> \<Delta>e \<A>2) (\<Delta>e' \<A>1 \<union> \<Delta>e' \<A>2) q x q'"
        apply (induction x arbitrary: q)
      proof -
        {
          fix q
        assume reach_ind: "q' \<in> \<F>e \<A>2 \<and> LTS_is_reachable_epsilon (\<Delta>e \<A>2) (\<Delta>e' \<A>2) q [] q'"
        from LTS_is_reachable_epsilon.simps(1)
            [of "\<Delta>e \<A>2" 
                "\<Delta>e' \<A>2" q q'] this
        obtain l where
        l_def: "(l \<noteq> [] \<and> epsilon_reach l (\<Delta>e' \<A>2) \<and> hd l = q \<and> last l = q')"
          by auto
        from this
        have "epsilon_reach l (\<Delta>e' \<A>2)" by auto
        from this
        have "epsilon_reach l (\<Delta>e' \<A>1 \<union> \<Delta>e' \<A>2)"
          apply (induction l)
          apply simp
          using epsilon_reach.elims(3) by fastforce  
        from this 
        show "LTS_is_reachable_epsilon (\<Delta>e \<A>1 \<union> \<Delta>e \<A>2) (\<Delta>e' \<A>1 \<union> \<Delta>e' \<A>2) q [] q'"
          using l_def by auto
      }
      {
        fix a x q
        assume ind_hyp: "(\<And>q. q' \<in> \<F>e \<A>2 \<and> LTS_is_reachable_epsilon (\<Delta>e \<A>2) (\<Delta>e' \<A>2) q x q' \<Longrightarrow>
            LTS_is_reachable_epsilon (\<Delta>e \<A>1 \<union> \<Delta>e \<A>2) (\<Delta>e' \<A>1 \<union> \<Delta>e' \<A>2) q x q')"
           and reach: "q' \<in> \<F>e \<A>2 \<and> LTS_is_reachable_epsilon (\<Delta>e \<A>2) (\<Delta>e' \<A>2) q (a # x) q'"
        from reach LTS_is_reachable_epsilon.simps(2)[of "\<Delta>e \<A>2" "\<Delta>e' \<A>2" q a x q']
        obtain qi qj \<sigma>
          where qiqj\<sigma>_def: "epsilon_reachable q qi (\<Delta>e' \<A>2) \<and>
        a \<in> \<sigma> \<and> (qi, \<sigma>, qj) \<in> \<Delta>e \<A>2 \<and> LTS_is_reachable_epsilon (\<Delta>e \<A>2) (\<Delta>e' \<A>2) qj x q'"
          by force
        from this ind_hyp
        have c1:"LTS_is_reachable_epsilon (\<Delta>e \<A>1 \<union> \<Delta>e \<A>2) (\<Delta>e' \<A>1 \<union> \<Delta>e' \<A>2) qj x q'"
          using q'_def by blast
        from qiqj\<sigma>_def
        obtain l where
        l_def: "l \<noteq> [] \<and> epsilon_reach l (\<Delta>e' \<A>2) \<and> hd l = q \<and> last l = qi"
          unfolding epsilon_reachable_def
          by fastforce
        from this
        have "epsilon_reach l (\<Delta>e' \<A>2)" by auto
        from this
        have "epsilon_reach l (\<Delta>e' \<A>1 \<union> \<Delta>e' \<A>2)"
          apply (induction l)
          apply simp
          using epsilon_reach.elims(3) by fastforce  
        from this l_def
        have c2: "epsilon_reachable q qi (\<Delta>e' \<A>1 \<union> \<Delta>e' \<A>2)"
          unfolding epsilon_reachable_def
          by auto
        from c1 c2 LTS_is_reachable_epsilon.simps(2)[of "\<Delta>e \<A>1 \<union> \<Delta>e \<A>2" 
                                                    "\<Delta>e' \<A>1 \<union> \<Delta>e' \<A>2" q a x q'] qiqj\<sigma>_def
        show "LTS_is_reachable_epsilon (\<Delta>e \<A>1 \<union> \<Delta>e \<A>2) (\<Delta>e' \<A>1 \<union> \<Delta>e' \<A>2) q (a # x) q'"      
          by blast
      }
    qed
      then show ?thesis 
        using q'_def by blast
    qed
  } 
  {
    fix q x
    assume qin: "q \<in> \<Q>e \<A>1 \<union> \<Q>e \<A>2"
       and xin: "x \<in> {uu.
                 \<exists>q'. (q' \<in> \<F>e \<A>1 \<or> q' \<in> \<F>e \<A>2) \<and>
                      LTS_is_reachable_epsilon (\<Delta>e \<A>1 \<union> \<Delta>e \<A>2) (\<Delta>e' \<A>1 \<union> \<Delta>e' \<A>2) q uu q'}"
    from xin
    obtain q' where
    q'_def: "(q' \<in> \<F>e \<A>1 \<or> q' \<in> \<F>e \<A>2) \<and>
                      LTS_is_reachable_epsilon (\<Delta>e \<A>1 \<union> \<Delta>e \<A>2) (\<Delta>e' \<A>1 \<union> \<Delta>e' \<A>2) q x q'"
      by auto
    thm LTS_is_reachable_epsilon.simps(2)
    from this
    show "x \<in> semRegEx q"
      apply (induction x)

  }



lemma RegToNFA_state\<L>_correct:
     "\<forall> q \<in> \<Q>e (RegToNFA E reg). state\<L> q (RegToNFA E reg) = semRegEx q"
    apply (induction reg)
    apply simp
    apply (simp add: state\<L>_def)
    apply auto[1]
    using neq_NilE apply fastforce
    apply force
    apply (simp add: state\<L>_def)
    apply auto[1]
    defer
    unfolding epsilon_reachable_def
    apply force
    apply force
    apply (simp add: state\<L>_def)
    apply auto[1]
    defer
    unfolding epsilon_reachable_def
    apply force
    apply force
  proof - 
    {
      fix x xa
      assume reach: " LTS_is_reachable_epsilon {(Atom x, {x}, Ep)} {} (Atom x) xa Ep"
      show "xa = [x]"
      proof (cases "xa = []")
        case True
        from reach True
             LTS_is_reachable_epsilon.simps(1)[of "{(Atom x, {x}, Ep)}" "{}" "(Atom x)" Ep]
        show ?thesis 
          by (metis RegEx.distinct(1) empty_iff epsilon_reach.elims(2) last_ConsL list.sel(1))
      next
        case False
        from this obtain h xa' where
        hxa'_def: "xa = h # xa'" 
          by (meson list.exhaust)
        from this reach LTS_is_reachable_epsilon.simps(2)
                        [of "{(Atom x, {x}, Ep)}" "{}" "Atom x" h xa' Ep]
        have
        qi\<sigma>_def: "epsilon_reachable (Atom x) (Atom x) {} \<and>
        h = x \<and>
        LTS_is_reachable_epsilon {(Atom x, {x}, Ep)} {} Ep xa' Ep"
          by force
        show ?thesis 
        proof (cases "xa' = []")
          case True
          then show ?thesis 
            using hxa'_def qi\<sigma>_def by fastforce
        next
          case False
          from this 
          obtain h' xa'' where
          h'xa''_def: "xa' = h' # xa''"
            by (meson list.exhaust)
          from this qi\<sigma>_def 
               LTS_is_reachable_epsilon.simps(2)
                    [of "{(Atom x, {x}, Ep)}" "{}" Ep h' xa' Ep]
          obtain qi' where
          qi'_def: "epsilon_reachable Ep qi' {} \<and> h' \<in> {x} \<and>
                    (qi', {x}, Ep) \<in> {(Atom x, {x}, Ep)}"
            by auto
          from this
          have "qi' = Ep"
            unfolding epsilon_reachable_def
            by (metis empty_iff epsilon_reach.elims(2) last_ConsL list.sel(1))
          from this qi'_def
          have "(Ep, {x}, Ep) \<in> {(Atom x, {x}, Ep)}"
            by auto
          then show ?thesis 
            by auto
        qed
      qed
    } {
      fix x1 x2a x
      assume reach: "LTS_is_reachable_epsilon 
                      {(IVL x1 x2a, {e. x1 \<le> e \<and> e \<le> x2a}, Ep)} {} (IVL x1 x2a) x
        Ep"
      
      show "\<exists>e. x = [e] \<and> x1 \<le> e \<and> e \<le> x2a"
      proof (cases "x = []")
        case True
        from LTS_is_reachable_epsilon.simps(1)[of 
             "{(IVL x1 x2a, {e. x1 \<le> e \<and> e \<le> x2a}, Ep)}" 
             "{}" "IVL x1 x2a" Ep] reach True
        show ?thesis 
          by (metis RegEx.simps(8) empty_iff epsilon_reach.elims(2) last_ConsL list.sel(1))
      next
        case False
        from this obtain h x' where
        hx'_def: "x = h # x'" 
          by (meson list.exhaust)
        from LTS_is_reachable_epsilon.simps(2)
             [of "{(IVL x1 x2a, {e. x1 \<le> e \<and> e \<le> x2a}, Ep)}" "{}" "IVL x1 x2a" h x' Ep]
             reach
        obtain qi where
        qi_def: "epsilon_reachable (IVL x1 x2a) qi {} \<and>
        h \<in> {e. x1 \<le> e \<and> e \<le> x2a} \<and> 
        (qi, {e. x1 \<le> e \<and> e \<le> x2a}, Ep) \<in> {(IVL x1 x2a, {e. x1 \<le> e \<and> e \<le> x2a}, Ep)} \<and>
        LTS_is_reachable_epsilon {(IVL x1 x2a, {e. x1 \<le> e \<and> e \<le> x2a}, Ep)} {} Ep x' Ep"
          using hx'_def by blast
        show ?thesis 
        proof (cases "x' = []")
          case True
          then show ?thesis 
            using hx'_def qi_def by blast
        next
          case False
          from this obtain h' x'' where
          h'x''_def: "x' = h' # x''" 
            by (meson list.exhaust)
          from LTS_is_reachable_epsilon.simps(2)
              [of "{(IVL x1 x2a, {e. x1 \<le> e \<and> e \<le> x2a}, Ep)}" "{}"
                  Ep h' x'' Ep] qi_def
          obtain qi where
          qi_def: "epsilon_reachable Ep qi {} \<and>
                   (qi, {e. x1 \<le> e \<and> e \<le> x2a}, Ep) \<in> 
                      {(IVL x1 x2a, {e. x1 \<le> e \<and> e \<le> x2a}, Ep)}"
            using h'x''_def by blast
          from this 
          have "qi = Ep"
            unfolding epsilon_reachable_def
            apply simp
            using epsilon_reach.elims(2) by fastforce
          from this qi_def
          show ?thesis by force
        qed
      qed
    }
    {
      fix reg1 reg2
      assume reg1inv: "\<forall>q\<in>\<Q>e (RegToNFA E reg1). state\<L> q (RegToNFA E reg1) = semRegEx q"
         and reg2inv: "\<forall>q\<in>\<Q>e (RegToNFA E reg2). state\<L> q (RegToNFA E reg2) = semRegEx q"
      show " \<forall>q\<in>\<Q>e (RegToNFA E (Alt reg1 reg2)). 
                  state\<L> q (RegToNFA E (Alt reg1 reg2)) = semRegEx q"
        apply (rule)
      proof 
        
    }



lemma RegToNFA_correct:
      "\<L>e (RegToNFA E reg) = semRegEx reg"
      unfolding \<L>e_def NFAe_accept_def
      apply (induction reg)
      apply simp
      apply auto[1]
  apply (metis LTS_is_reachable_epsilon.simps(2) empty_iff min_list.cases)
  apply force
  apply simp
  apply auto[1]
  defer
  unfolding epsilon_reachable_def 
       apply force
  unfolding epsilon_reachable_def 
      apply force
     apply simp
     apply auto[1]
       defer
    unfolding epsilon_reachable_def 
         apply force
unfolding epsilon_reachable_def 
      apply force
proof - 
  {
    fix x xa
    assume reach: "LTS_is_reachable_epsilon {(Atom x, {x}, Ep)} {} (Atom x) xa Ep" 
    show "xa = [x]"
    proof (cases "xa = []")
      case True
      from LTS_is_reachable_epsilon.simps(1)[of "{(Atom x, {x}, Ep)}" "{}" "Atom x" Ep]
      obtain l where 
      l_def: "l \<noteq> [] \<and> epsilon_reach l {} \<and> hd l = Atom x \<and> last l = Ep"
        using True reach by presburger
      from True this
      show ?thesis 
        by (metis RegEx.distinct(1) epsilon_reach.elims(2) 
                  last_ConsL list.sel(1) memb_imp_not_empty)
    next
      case False
      from this obtain a xa' where
      axa'_def: "xa = a # xa'" 
        by (meson list.exhaust)
      note epreach = LTS_is_reachable_epsilon.simps(2)
                [of "{(Atom x, {x}, Ep)}" "{}" "Atom x" a "xa'" Ep]
      from reach epreach
      obtain qi qj \<sigma> where
      qiqj\<sigma>_def: "epsilon_reachable (Atom x) qi {} \<and>
        a \<in> \<sigma> \<and>
        (qi, \<sigma>, qj) \<in> {(Atom x, {x}, Ep)} \<and>
        LTS_is_reachable_epsilon {(Atom x, {x}, Ep)} {} qj xa' Ep"
        using axa'_def by blast
      from this have
      qiqj\<sigma>'_prop: "qi = Atom x \<and> a = x \<and> qj = Ep"
        by blast
      show ?thesis 
      proof (cases "xa' = []")
        case True
        from this qiqj\<sigma>'_prop axa'_def
        show ?thesis by force
      next
        case False
        from this obtain b xa'' where
        bxa''_def: "xa' = b # xa''" 
          by (meson list.exhaust)
        from LTS_is_reachable_epsilon.simps(2)[of "{(Atom x, {x}, Ep)}" "{}" Ep b xa'' Ep]
             qiqj\<sigma>'_prop
        obtain qi' \<alpha>' where
        qi'qj'\<alpha>'_def: "epsilon_reachable Ep qi' {} \<and>
        b \<in> \<alpha>' \<and>
        (qi', \<alpha>', Ep) \<in> {(Atom x, {x}, Ep)}"
          using bxa''_def qiqj\<sigma>_def by blast

        from this epsilon_reachable_def[of Ep qi' "{}"]
        obtain l where
        l_def: "l \<noteq> [] \<and> epsilon_reach l {} \<and> hd l = Ep \<and> last l = qi'"
          by auto
        from this
        have "qi' = Ep"
          apply (induction l)
          apply simp
          by (metis empty_iff epsilon_reach.elims(1) last_ConsL list.sel(1))
        from this qi'qj'\<alpha>'_def
        show ?thesis 
          by force
      qed
    qed
  }



end























