
section \<open> Interface for NFAs and DFAs \<close>

theory NFA_set_spec
 
imports Main 
  "../DFA" 
  "Collections.Collections"

begin
type_synonym ('q,'a,'nfa) nfa_\<alpha> = "'nfa \<Rightarrow> ('q, 'a) NFA_rec"

  locale nfa =
    fixes \<alpha> :: "('q,'a,'nfa) nfa_\<alpha>"
    fixes invar :: "'nfa \<Rightarrow> bool"
    assumes nfa_is_wellformed: "invar n \<Longrightarrow> NFA (\<alpha> n)"

type_synonym ('q2,'i,'b,'\<sigma>,'nfa) nfa_construct = 
    "('q2 \<Rightarrow> 'i) \<Rightarrow> 'b \<Rightarrow> 'q2 list \<Rightarrow>  ('q2 \<Rightarrow> bool) \<Rightarrow> 
     ('q2 \<Rightarrow> ('b \<times>'q2,'\<sigma>) set_iterator) \<Rightarrow> 'nfa"

locale dfa_construct = nfa \<alpha> invar + set s_\<alpha> s_invar 
    for \<alpha> invar 
    and s_\<alpha> :: "'a_set \<Rightarrow> 'a::linorder set" and s_invar + 
    constrains \<alpha> :: "('q,'a,'nfa) nfa_\<alpha>" 
    fixes q2_\<alpha> :: "'q2_rep \<Rightarrow> 'q2" 
      and q2_invar :: "'q2_rep \<Rightarrow> bool" 
      and construct :: "('q2_rep,'i,'b,'\<sigma>,'nfa) nfa_construct"
      and sem :: "'b \<Rightarrow> 'a set" 
      and canonical_op :: "'b \<Rightarrow> bool"
    assumes dfa_construct_correct:
       "\<lbrakk>weak_DFA (\<A>::('q2, 'a) NFA_rec); inj_on f (\<Q> \<A>);
         \<And>q. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> \<Q> \<A> \<Longrightarrow> ff q = (f (q2_\<alpha> q));
         distinct (map q2_\<alpha> I); \<And>q. q \<in> set I \<Longrightarrow> q2_invar q; q2_\<alpha> ` (set I) = \<I> \<A>;
         canonical_op Sig; 
         finite (\<Delta> \<A>);
         \<And> q. \<forall> (a, q') \<in> (DS q). canonical_op a ; 
         \<And> q. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> \<Q> \<A> \<Longrightarrow> inj_on q2_\<alpha> {q'. \<exists>a. (a, q') \<in> DS q};
         sem Sig = \<Sigma> \<A>; \<And>q. \<lbrakk>q2_invar q; q2_\<alpha> q \<in> \<Q> \<A>\<rbrakk> \<Longrightarrow> FP q \<longleftrightarrow> q2_\<alpha> q \<in> \<F> \<A>;
         \<And>q. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> \<Q> \<A> \<Longrightarrow> set_iterator (D_it q) (DS q) \<and>
               {(a, q'). (q2_\<alpha> q, a, q') \<in> \<Delta> \<A>} = (\<lambda>(a, q'). (sem a, q2_\<alpha> q')) ` (DS q) \<and>
               (\<forall>a q'. (a, q') \<in> (DS q) \<longrightarrow> q2_invar q') \<and>
               (\<forall>a q'. (a, q') \<in> (DS q) \<longrightarrow> (\<forall>q''. (a, q'') \<in> (DS q) \<longrightarrow> (q2_\<alpha> q' = q2_\<alpha> q'') = (q' = q''))) 
            \<rbrakk> \<Longrightarrow> 
         (invar (construct ff Sig I FP D_it) \<and>
          NFA_isomorphic_wf (\<alpha> (construct ff Sig I FP D_it)) (NFA_remove_unreachable_states \<A>))"

locale nfa_rename_states = nfa \<alpha>1 invar1 + nfa \<alpha>2 invar2  
    for \<alpha>1 :: "('q1,'a,'nfa1) nfa_\<alpha>" and invar1 and
        \<alpha>2 :: "('q2,'a,'nfa2) nfa_\<alpha>" and invar2 +
    fixes rename_states :: "'nfa1 \<Rightarrow> ('q1 \<Rightarrow> 'q2) \<Rightarrow> 'nfa2"
    assumes nfa_rename_states_correct:
      "invar1 n \<Longrightarrow> (invar2 (rename_states n f))"
      "invar1 n \<Longrightarrow> (\<alpha>2 (rename_states n f) = NFA_rename_states (\<alpha>1 n) f)"

  type_synonym ('a1,'a2,'nfa1,'nfa2) nfa_rename_labels = "'nfa1 \<Rightarrow> ('a1 \<Rightarrow> 'a2) \<Rightarrow> 'nfa2"
  locale nfa_rename_labels = n1:nfa \<alpha>1 invar1 + n2:nfa \<alpha>2 invar2  
    for \<alpha>1 :: "('q,'a1,'nfa1) nfa_\<alpha>" and invar1 and
        \<alpha>2 :: "('q,'a2,'nfa2) nfa_\<alpha>" and invar2 +
    fixes rename_labels :: "('a1,'a2,'nfa1,'nfa2) nfa_rename_labels"
    assumes rename_labels_correct:
      "invar1 n \<Longrightarrow> (invar2 (rename_labels n f))"
      "invar1 n \<Longrightarrow> (\<alpha>2 (rename_labels n f) = NFA_rename_labels (\<alpha>1 n) f)"
  begin
    lemma rename_labels_correct___isomorphic :
      "invar1 n \<Longrightarrow> (invar2 (rename_labels n f))"
      "invar1 n \<Longrightarrow> NFA_isomorphic_wf (\<alpha>1 n) \<A> \<Longrightarrow> 
                    NFA_isomorphic_wf (\<alpha>2 (rename_labels n f)) (NFA_rename_labels \<A> f)"
    using rename_labels_correct[of n f] n2.nfa_is_wellformed
          NFA_isomorphic_wf___NFA_rename_labels_cong [of "\<alpha>1 n" \<A> f]

    by simp_all
end

type_synonym ('q,'b,'nfa) nfa_from_list_ba = 
    "('q list \<times> 'b \<times> ('q \<times> 'b \<times> 'q) list 
      \<times> 'q list \<times> 'q list) \<Rightarrow> 'nfa"

  thm NFA_construct_interval___is_well_formed

  locale nfa_from_list_ba = nfa +
    constrains \<alpha> :: "('q,'a::linorder,'nfa) nfa_\<alpha>"
    fixes wf :: "('q list \<times> 'b \<times> ('q \<times> 'b \<times> 'q) list 
      \<times> 'q list \<times> 'q list) \<Rightarrow> bool"
    fixes from_interval :: "('q,'b,'nfa) nfa_from_list_ba" and
         sem :: "'b \<Rightarrow> 'a set" and
        canonical_op :: "'b \<Rightarrow> bool" and
        intersect_op :: "'b \<Rightarrow> 'b \<Rightarrow> 'b" and
        empty_op :: "'b \<Rightarrow> bool" 
    assumes nfa_from_list_interval_correct:
      "wf l \<Longrightarrow> invar (from_interval l)"  
      "wf l \<Longrightarrow> \<alpha> (from_interval l) = NFA_construct_ba sem l"
  begin
    lemma nfa_from_list_interval_correct___isomorphic :
      "wf l \<Longrightarrow> invar (from_interval l)"
      "wf l \<Longrightarrow> (\<forall> (q,d,q') \<in> set (fst (snd (snd l))). finite (sem d)) \<longrightarrow>
       (\<forall> (q, \<sigma>, q') \<in> set (fst (snd (snd l))). sem \<sigma> \<subseteq> sem (fst (snd l))) \<longrightarrow>
         NFA_isomorphic_wf (\<alpha> (from_interval l)) (NFA_construct_ba sem l)"
      apply auto
      by (simp_all add: nfa_from_list_interval_correct 
                        NFA_isomorphic_wf_def NFA_isomorphic_refl
                        NFA_construct_interval___is_well_formed)
      
  end

locale nfa_determinise = n1: nfa \<alpha>1 invar1 + n2: nfa \<alpha>2 invar2    
    for \<alpha>1 :: "('q1::{NFA_states},'a::linorder,'nfa1) nfa_\<alpha>" and invar1 and
        \<alpha>2 :: "('q2,'a,'nfa2) nfa_\<alpha>" and invar2  and
        T  :: "'nfa1 \<Rightarrow> (('q \<times> 'b \<times> 'q) set)" and
        sem :: "'b \<Rightarrow> 'a set" and
        canonical_op :: "'b \<Rightarrow> bool" and
        intersect_op :: "'b \<Rightarrow> 'b \<Rightarrow> 'b" and
        empty_op :: "'b \<Rightarrow> bool" 
        +
    fixes determinise :: "'nfa1 \<Rightarrow> 'nfa2"
    assumes determinise_correct_aux:
      "invar1 n \<Longrightarrow> (\<forall> (q, a, q') \<in> (T n). canonical_op a) \<Longrightarrow>
        (\<forall> (q, a, q') \<in> (T n). sem a \<noteq> {}) \<Longrightarrow>
      (\<forall> (q1, a1, q1') \<in> (T n). \<forall> (q2, a2, q2') \<in> (T n).
                   a1 \<noteq> a2 \<longrightarrow> empty_op (intersect_op a1 a2))
       \<Longrightarrow> invar2 (determinise n) \<and> 
       NFA_isomorphic_wf (\<alpha>2 (determinise n)) (efficient_determinise_NFA (\<alpha>1 n))"
  begin
    lemma determinise_correct:
      "invar1 n \<Longrightarrow> (\<forall> (q, a, q') \<in> (T n). canonical_op a)
       \<Longrightarrow> (\<forall> (q, a, q') \<in> (T n). sem a \<noteq> {}) \<Longrightarrow>
       (\<forall> (q1, a1, q1') \<in> (T n). \<forall> (q2, a2, q2') \<in> (T n).
                   a1 \<noteq> a2 \<longrightarrow> empty_op (intersect_op a1 a2)) \<Longrightarrow> invar2 (determinise n)"
      "invar1 n \<Longrightarrow> (\<forall> (q, a, q') \<in> (T n). canonical_op a)
       \<Longrightarrow> (\<forall> (q, a, q') \<in> (T n). sem a \<noteq> {}) \<Longrightarrow>
      (\<forall> (q1, a1, q1') \<in> (T n). \<forall> (q2, a2, q2') \<in> (T n).
                   a1 \<noteq> a2 \<longrightarrow> empty_op (intersect_op a1 a2)) \<Longrightarrow> 
      NFA_isomorphic_wf (\<alpha>2 (determinise n)) (efficient_determinise_NFA (\<alpha>1 n))"
      using determinise_correct_aux by (simp_all)

    lemma determinise_correct___isomorphic:
      "invar1 n \<Longrightarrow> (\<forall> (q, a, q') \<in> (T n). canonical_op a)
       \<Longrightarrow> (\<forall> (q, a, q') \<in> (T n). sem a \<noteq> {}) \<Longrightarrow> 
          (\<forall> (q1, a1, q1') \<in> (T n). \<forall> (q2, a2, q2') \<in> (T n).
                   a1 \<noteq> a2 \<longrightarrow> empty_op (intersect_op a1 a2)) \<Longrightarrow> invar2 (determinise n)"
      "invar1 n \<Longrightarrow> (\<forall> (q, a, q') \<in> (T n). canonical_op a)
       \<Longrightarrow> (\<forall> (q, a, q') \<in> (T n). sem a \<noteq> {}) \<Longrightarrow> 
        (\<forall> (q1, a1, q1') \<in> (T n). \<forall> (q2, a2, q2') \<in> (T n).
                   a1 \<noteq> a2 \<longrightarrow> empty_op (intersect_op a1 a2)) \<Longrightarrow> 
            NFA_isomorphic_wf (\<alpha>1 n) \<A> \<and> (\<I> (\<alpha>1 n) \<noteq> {})\<Longrightarrow> 
       NFA_isomorphic_wf (\<alpha>2 (determinise n)) (efficient_determinise_NFA \<A>)"
      apply (simp add: determinise_correct)
      apply (insert determinise_correct(2)[of n]
                    NFA_isomorphic_efficient_determinise [of "\<alpha>1 n" \<A>])
      using NFA_set.NFA_isomorphic_wf_trans apply blast
    done

    lemma determinise_correct___same:
      "invar1 n \<Longrightarrow> (\<forall> (q, a, q') \<in> (T n). canonical_op a)
       \<Longrightarrow> (\<forall> (q, a, q') \<in> (T n). sem a \<noteq> {}) \<Longrightarrow> 
        (\<forall> (q1, a1, q1') \<in> (T n). \<forall> (q2, a2, q2') \<in> (T n).
                   a1 \<noteq> a2 \<longrightarrow> empty_op (intersect_op a1 a2)) \<Longrightarrow> invar2 (determinise n)"
      "invar1 n \<Longrightarrow> (\<forall> (q, a, q') \<in> (T n). canonical_op a)
       \<Longrightarrow> (\<forall> (q, a, q') \<in> (T n). sem a \<noteq> {}) \<Longrightarrow> 
        uniq_label_NFA (\<alpha>1 n) \<and> \<I> (\<alpha>1 n) \<noteq> {} \<Longrightarrow> (\<forall> (q1, a1, q1') \<in> (T n). \<forall> (q2, a2, q2') \<in> (T n).
                   a1 \<noteq> a2 \<longrightarrow> empty_op (intersect_op a1 a2)) \<Longrightarrow>
                    NFA_isomorphic_wf (\<alpha>2 (determinise n)) (NFA_determinise (\<alpha>1 n))"
       using determinise_correct [of n] n1.nfa_axioms[unfolded nfa_def]
             NFA_determinise_isomorphic_wf [of "\<alpha>1 n"]
       by (simp_all, metis NFA_isomorphic_wf_trans)

    lemma determinise_correct___same_isomorphic:
      "invar1 n \<Longrightarrow> (\<forall> (q, a, q') \<in> (T n). canonical_op a)
       \<Longrightarrow>(\<forall> (q, a, q') \<in> (T n). sem a \<noteq> {}) \<Longrightarrow> (\<forall> (q1, a1, q1') \<in> (T n). \<forall> (q2, a2, q2') \<in> (T n).
                   a1 \<noteq> a2 \<longrightarrow> empty_op (intersect_op a1 a2)) \<Longrightarrow> invar2 (determinise n)"
      "invar1 n \<Longrightarrow> (\<forall> (q, a, q') \<in> (T n). canonical_op a)
       \<Longrightarrow> (\<forall> (q, a, q') \<in> (T n). sem a \<noteq> {}) \<Longrightarrow> (\<forall> (q1, a1, q1') \<in> (T n). \<forall> (q2, a2, q2') \<in> (T n).
                   a1 \<noteq> a2 \<longrightarrow> empty_op (intersect_op a1 a2)) \<Longrightarrow> NFA_isomorphic_wf (\<alpha>1 n) \<A> \<Longrightarrow> 
       uniq_label_NFA \<A> \<and> \<I> \<A> \<noteq> {} \<Longrightarrow>
       NFA_isomorphic_wf (\<alpha>2 (determinise n)) (NFA_determinise \<A>)"
      apply (simp add: determinise_correct)
      apply (insert determinise_correct___isomorphic(2)[of n \<A>]
                    NFA_determinise_isomorphic_wf [of \<A>])
      apply (simp)
      apply (subgoal_tac "\<I> (\<alpha>1 n) \<noteq> {}")
      apply (metis NFA_isomorphic_wf_trans NFA_isomorphic_wf_alt_def)
      unfolding NFA_isomorphic_wf_def NFA_isomorphic_def
      apply fastforce
    done
  end


locale nfa_complement = nfa \<alpha> invar   
    for \<alpha> :: "('q,'a,'nfa) nfa_\<alpha>" and invar +
    fixes complement :: "'nfa \<Rightarrow> 'nfa"
    assumes complement_correct:
      "invar n \<Longrightarrow> invar (complement n)"
      "invar n \<Longrightarrow> (\<alpha> (complement n) = DFA_complement (\<alpha> n))"
  begin
    lemma complement_correct___isomorphic :
      "invar n \<Longrightarrow> invar (complement n)"
      "invar n \<Longrightarrow> NFA_isomorphic_wf (\<alpha> n) (\<A> :: ('q2, 'a) NFA_rec) \<Longrightarrow>
                    NFA_isomorphic_wf (\<alpha> (complement n)) (DFA_complement \<A>)"
      apply (simp add: complement_correct)
      apply (insert complement_correct(2)[of n] 
                  NFA_isomorphic_wf___DFA_complement_cong [of "\<alpha> n" \<A>])
      apply (simp)
    done
end


  subsection \<open>  Record Based Interface \<close>

  record ('q,'a, 'b, 'nfa) nfa_ops =
    nfa_op_\<alpha> :: "('q::{NFA_states},'a,'nfa) nfa_\<alpha>"
    nfa_op_invar :: "'nfa \<Rightarrow> bool"
    nfa_op_ba_wf :: "('q list \<times> ('q \<times> 'b \<times> 'q) list 
      \<times> 'q list \<times> 'q list) \<Rightarrow> bool"
    nfa_op_bool_comb :: "(bool \<Rightarrow> bool \<Rightarrow> bool) \<Rightarrow> 'nfa \<Rightarrow> 'nfa \<Rightarrow> 'nfa"
    nfa_op_concate :: "'nfa \<Rightarrow> 'nfa \<Rightarrow> 'nfa"
 

  locale StdNFADefs =
    fixes ops :: "('q::{NFA_states},'a ::linorder, 'b, 'nfa) nfa_ops"
  begin
    abbreviation \<alpha> where "\<alpha> \<equiv> nfa_op_\<alpha> ops"
    abbreviation invar where "invar \<equiv> nfa_op_invar ops"
    abbreviation nfa_ba_wf where "nfa_ba_wf \<equiv> nfa_op_ba_wf ops"
(*  abbreviation nfa_from_list where "nfa_from_list \<equiv> nfa_op_nfa_from_list ops" *)
(*    abbreviation dfa_from_list where "dfa_from_list \<equiv> nfa_op_dfa_from_list ops"
    abbreviation to_list where "to_list \<equiv> nfa_op_to_list ops"
    abbreviation accept where "accept \<equiv> nfa_op_accept ops"
    abbreviation is_deterministic where "is_deterministic \<equiv> nfa_op_is_deterministic ops"
    abbreviation rename_labels where "rename_labels \<equiv> nfa_op_rename_labels ops"
    abbreviation normalise where "normalise \<equiv> nfa_op_normalise ops"
    abbreviation reverse where "reverse \<equiv> nfa_op_reverse ops"
    abbreviation complement where "complement \<equiv> nfa_op_complement ops"
    abbreviation bool_comb where "bool_comb \<equiv> nfa_op_bool_comb ops"
    abbreviation product where "product \<equiv> bool_comb (\<and>)"
    abbreviation determinise where "determinise \<equiv> nfa_op_determinise ops"
    abbreviation minimise_Brzozowski where "minimise_Brzozowski \<equiv> nfa_op_minimise_Brzozowski ops"
    abbreviation minimise_Hopcroft where "minimise_Hopcroft \<equiv> nfa_op_minimise_Hopcroft ops"
    abbreviation minimise_Hopcroft_NFA where "minimise_Hopcroft_NFA \<equiv> nfa_op_minimise_Hopcroft_NFA ops"
    abbreviation right_quotient_lists where "right_quotient_lists \<equiv> nfa_op_right_quotient_lists ops"
    abbreviation states_no where "states_no \<equiv> nfa_op_states_no ops"
    abbreviation labels_no where "labels_no \<equiv> nfa_op_labels_no ops"
    abbreviation trans_no where "trans_no \<equiv> nfa_op_trans_no ops"
    abbreviation initial_no where "initial_no \<equiv> nfa_op_initial_no ops"
    abbreviation final_no where "final_no \<equiv> nfa_op_final_no ops" *)
end



  locale StdNFA = StdNFADefs +
    nfa \<alpha> invar 
    (* nfa_from_list \<alpha> invar nfa_from_list + *)

(*
    nfa_to_list \<alpha> invar to_list +
    nfa_stats \<alpha> invar states_no trans_no initial_no final_no +
    nfa_accept \<alpha> invar accept +
    nfa_rename_labels \<alpha> invar \<alpha> invar rename_labels +
    nfa_normalise \<alpha> invar normalise +
    nfa_reverse \<alpha> invar \<alpha> invar reverse +
    nfa_bool_comb_same \<alpha> invar bool_comb *)
  begin
  
 
  end
end
