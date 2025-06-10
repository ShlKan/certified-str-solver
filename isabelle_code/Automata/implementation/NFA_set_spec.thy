
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
