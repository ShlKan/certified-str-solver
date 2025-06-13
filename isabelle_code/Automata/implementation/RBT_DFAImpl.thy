
section \<open> DFA \<close>

theory RBT_DFAImpl 

imports  
      "Collections.Collections" 
      RBT_LTSImpl Interval_imp 
      DFAByLTS
begin


interpretation rs_nfa_defs: nfa_dfa_by_lts_bool_algebra_defs rs_ops
                            rs_ops rs_ops rs_ops rs_lts_ops rs_lts_ops
                            semIs emptyIs nemptyIs intersectIs diffIs elemIs canonicalIs
  apply intro_locales
  using interval_bool_algebra
  by simp


type_synonym ('a,'b) rs_nfa = 
   "('a, unit) RBT.rbt \<times> 
    ('a, (('b \<times> 'b) list, ('a, unit) RBT.rbt) RBT.rbt) RBT.rbt \<times>
    ('a, unit) RBT.rbt \<times> ('a, unit) RBT.rbt"



definition "rs_nfa_determinise \<equiv> rs_nfa_defs.determinise_impl rm_ops rm_ops  
   rs_iteratei rs_iteratei rs_iteratei rs_iteratei rs_lts_succq_it" 

definition "rs_nfa_complement \<equiv> rs_nfa_defs.complement_impl"


lemmas rs_nfa_defs =
  rs_nfa_determinise_def
  rs_nfa_complement_def 



lemmas rs_nfa_determinise_code [code] = rs_nfa_defs.determinise_impl_code 
  [of rm_ops rm_ops rs_iteratei rs_iteratei rs_iteratei rs_iteratei rs_lts_succq_it, folded rs_nfa_defs]

lemmas rs_nfa_complement_code [code] = rs_nfa_defs.complement_impl_code[folded rs_nfa_defs]


end
