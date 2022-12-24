(*  
    Authors:     Shuanglong Kan <shuanglong@uni-kl.de>
                 Thomas Tuerk <tuerk@in.tum.de>             
*)

section \<open> Export Code with RBTs \<close>

theory RBT_CodeExport
imports Main 
        RBT_NFAImpl 
        NFA_Split_Impl
        Transducer_Impl_new
        Epsilon_elim_code
begin

export_code
  prod_encode
  rs_nfa_construct_interval
  rs_nfa_bool_comb
  rs_nfa_determinise
  rs_nfa_destruct  
  rs_nfa_complement
  rs_nfa_concate 
  rs_nfa_concate_rename 
  rs_nfa_construct_reachable 
  rs_split_trans_code
  rs_nfa_uniq
  rs_nfa_tran_complement
  rs_nfa_union
  rs_nfa_rename
  rs_nfa_qsize
  rs_product_transducer
  rs_nft_construct_interval
  rs_nft_destruct
  rs_nfae_destruct
  rs_nfa_elim
  rs_nfa_normal

in OCaml module_name "Automata_lib"



end
