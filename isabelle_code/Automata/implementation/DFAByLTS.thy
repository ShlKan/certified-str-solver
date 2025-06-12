
theory DFAByLTS
                                      
imports "Collections.Collections" "HOL.Enum"
      "../../General/Accessible_Impl" "../DFA"
  LTSSpec LTSGA NFA_set_spec LTS_Impl Bool_Algebra
  

begin


subsection \<open> Locales for NFAs and a common locale \<close>

locale automaton_by_lts_bool_algebra_syntax = 
  s: StdSetDefs s_ops   (* Set operations on states *) +
  l: StdSetDefs l_ops   (* Set operations on labels *) +
  lt: StdSetDefs lt_ops   (* Set operations on labels *) +
  d: StdCommonLTSDefs d_ops elem_op  (* An LTS *) +
  iv: bool_algebra sem empty_op noempty_op 
                   intersect_op diff_op elem_op canonical_op
  for s_ops::"('q::{NFA_states},'q_set,_) set_ops_scheme"
  and l_ops::"('a:: linorder,'a_set ,_) set_ops_scheme"
  and lt_ops::"('b, 'ai_set ,_) set_ops_scheme"
  and d_ops::"('q, 'b,'a,'d,_) common_lts_ops_scheme" 
  and sem :: "'b \<Rightarrow> 'a set"
  and empty_op :: "'b \<Rightarrow> bool"
  and noempty_op :: "'b \<Rightarrow> bool"
  and intersect_op :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"
  and diff_op :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b"
  and elem_op :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  and canonical_op :: "'b \<Rightarrow> bool"


locale automaton_by_lts_bool_algebra_defs = automaton_by_lts_bool_algebra_syntax
      s_ops l_ops lt_ops d_ops sem empty_op noempty_op 
                   intersect_op diff_op elem_op canonical_op + 
  s: StdSet s_ops (* Set operations on states *) +
  l: StdSet l_ops (* Set operations on labels *) +
  lt: StdSet lt_ops   (* Set operations on labels *) +
  d: StdCommonLTS d_ops elem_op (* An LTS *) + 
  iv: bool_algebra sem empty_op noempty_op 
                   intersect_op diff_op elem_op canonical_op
  for s_ops::"('q::{NFA_states},'q_set,_) set_ops_scheme"
  and l_ops::"('a :: linorder,'a_set ,_) set_ops_scheme"
  and lt_ops::"('b, 'ai_set ,_) set_ops_scheme"
  and d_ops::"('q, 'b,'a,'d,_) common_lts_ops_scheme" 
  and sem :: "'b \<Rightarrow> 'a set"
  and empty_op :: "'b \<Rightarrow> bool"
  and noempty_op :: "'b \<Rightarrow> bool"
  and intersect_op :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"
  and diff_op :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b"
  and elem_op :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  and canonical_op :: "'b \<Rightarrow> bool"


locale nfa_by_lts_bool_algebra_defs = automaton_by_lts_bool_algebra_defs 
  s_ops l_ops lt_ops d_ops sem empty_op noempty_op 
                   intersect_op diff_op elem_op canonical_op + 
  s: StdSet s_ops (* Set operations on states *) +
  l: StdSet l_ops (* Set operations on labels *) +
  lt: StdSet lt_ops   (* Set operations on labels *) +
  d: StdLTS d_ops elem_op (* An LTS *) +
  iv: bool_algebra sem empty_op noempty_op 
                   intersect_op diff_op elem_op canonical_op
  for s_ops::"('q :: {NFA_states},'q_set,_) set_ops_scheme"
  and l_ops::"('a ::linorder,'a_set,_) set_ops_scheme"
  and lt_ops::"('b, 'ai_set ,_) set_ops_scheme"
  and d_ops::"('q, 'b,'a,'d,_) lts_ops_scheme"
  and sem :: "'b \<Rightarrow> 'a set"
  and empty_op :: "'b \<Rightarrow> bool"
  and noempty_op :: "'b \<Rightarrow> bool"
  and intersect_op :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"
  and diff_op :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b"
  and elem_op :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  and canonical_op :: "'b \<Rightarrow> bool"


lemma nfa_by_lts_bool_algebra_defs___sublocale :
  "nfa_by_lts_bool_algebra_defs s_ops l_ops lt_ops d_ops sem empty_op noempty_op 
                   intersect_op diff_op elem_op canonical_op \<Longrightarrow>
   automaton_by_lts_bool_algebra_defs s_ops l_ops lt_ops d_ops sem empty_op noempty_op 
                   intersect_op diff_op elem_op canonical_op"
  unfolding nfa_by_lts_bool_algebra_defs_def automaton_by_lts_bool_algebra_defs_def
  by (simp add: StdLTS_sublocale)

lemma nfa_by_lts_defs___sublocale :
  "nfa_by_lts_bool_algebra_defs s_ops l_ops lt_ops d_ops sem empty_op noempty_op 
                   intersect_op diff_op elem_op canonical_op  \<Longrightarrow>
   automaton_by_lts_bool_algebra_defs s_ops l_ops lt_ops d_ops sem empty_op noempty_op 
                   intersect_op diff_op elem_op canonical_op"
  unfolding nfa_by_lts_bool_algebra_defs_def automaton_by_lts_bool_algebra_defs_def
  by (simp add: StdLTS_sublocale)

locale nfa_dfa_by_lts_bool_algebra_defs = 
  s: StdSet s_ops (* Set operations on states *) +
  ss: StdSet ss_ops (* Set operations on states *) +
  l: StdSet l_ops (* Set operations on labels *) +
  lt: StdSet lt_ops   (* Set operations on labels *) +
  d_nfa: StdLTS d_nfa_ops elem_op (* An LTS *) +
  dd_nfa: StdLTS dd_nfa_ops elem_op (* An LTS *) +
  iv: bool_algebra sem empty_op noempty_op 
                   intersect_op diff_op elem_op canonical_op
  for s_ops::"('q::{NFA_states},'q_set,_) set_ops_scheme"
  and ss_ops::"('q \<times> 'q,'qq_set,_) set_ops_scheme"
  and l_ops::"('a::linorder, 'a_set ,_) set_ops_scheme"
  and lt_ops::"('b, 'ai_set ,_) set_ops_scheme"
  and d_nfa_ops::"('q, 'b,'a,'d_nfa,_) lts_ops_scheme"
  and dd_nfa_ops::"('q \<times> 'q,'b, 'a,'dd_nfa,_) lts_ops_scheme"
   and sem :: "'b \<Rightarrow> 'a set"
  and empty_op :: "'b \<Rightarrow> bool"
  and noempty_op :: "'b \<Rightarrow> bool"
  and intersect_op :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"
  and diff_op :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b"
  and elem_op :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  and canonical_op :: "'b \<Rightarrow> bool"

sublocale nfa_dfa_by_lts_bool_algebra_defs < 
          nfa: nfa_by_lts_bool_algebra_defs 
          s_ops l_ops lt_ops d_nfa_ops by unfold_locales



context automaton_by_lts_bool_algebra_syntax
begin

definition nfa_states :: "'q_set \<times> 'b \<times> 'd \<times> 'q_set \<times> 'q_set \<Rightarrow> 'q_set" where
  "nfa_states A = fst A"
lemma [simp]: "nfa_states (Q, E, D, I, F) = Q" by (simp add: nfa_states_def)


fun ba_to_set :: "'q \<times> 'b \<times> 'q \<Rightarrow> 'q \<times> 'a set \<times> 'q"  where
    "ba_to_set (q, s, q') = (q, sem s, q')"

definition nfa_trans :: 
        "'q_set \<times> 'b \<times> 'd \<times> 'q_set \<times> 'q_set \<Rightarrow> 'd" where
  "nfa_trans A = (fst (snd (snd A)))"
lemma [simp]: "nfa_trans (Q, E, D, I, F) = D" by (simp add: nfa_trans_def)

fun nfa_tranlabel :: "('q \<times> 'b \<times> 'q) list \<Rightarrow> 'ai_set" where
    "nfa_tranlabel [] = lt.empty ()"
  | "nfa_tranlabel (a # l) = lt.ins (fst (snd a)) (nfa_tranlabel l)"

definition nfa_labels:: "'q_set \<times> 'b \<times> 'd \<times> 'q_set \<times> 'q_set \<Rightarrow> 'ai_set" where
    "nfa_labels A = nfa_tranlabel (d.to_list (nfa_trans A))"

definition nfa_alphabet :: 
        "'q_set \<times> 'b \<times> 'd \<times> 'q_set \<times> 'q_set \<Rightarrow> 'b" where
  "nfa_alphabet A = (fst (snd A))"
lemma [simp]: "nfa_alphabet (Q, E, D, I, F) = E" by (simp add: nfa_alphabet_def)

    


definition nfa_initial :: "'q_set \<times> 'b \<times> 'd \<times> 'q_set \<times> 'q_set \<Rightarrow> 'q_set" where
  "nfa_initial A = fst (snd (snd (snd  A)))"
lemma [simp]: "nfa_initial (Q, E, D, I, F) = I" by (simp add: nfa_initial_def)

definition nfa_accepting :: "'q_set \<times> 'b \<times> 'd \<times> 'q_set \<times> 'q_set \<Rightarrow> 'q_set" where
  "nfa_accepting A = snd (snd (snd (snd  A)))"
lemma [simp]: "nfa_accepting (Q, E, D, I, F) = F" by (simp add: nfa_accepting_def)


(***********)

definition nfa_statep :: "'qq_set \<times> 'dd_nfa \<times> 'qq_set \<times> 'qq_set \<Rightarrow> 'qq_set" where
  "nfa_statep A = fst A"
lemma [simp]: "nfa_statep (Q, D, I, F) = Q" by (simp add: nfa_statep_def)

definition nfa_transp :: 
        "'qq_set \<times> 'dd_nfa \<times> 'qq_set \<times> 'qq_set \<Rightarrow> 'dd_nfa" where
  "nfa_transp A = (fst (snd A))"
lemma [simp]: "nfa_transp (Q, D, I, F) = D" by (simp add: nfa_transp_def)

definition nfa_initialp :: "'qq_set \<times> 'dd_nfa \<times> 'qq_set \<times> 'qq_set \<Rightarrow> 'qq_set" where
  "nfa_initialp A = fst (snd (snd  A))"
lemma [simp]: "nfa_initialp (Q, D, I, F) = I" by (simp add: nfa_initialp_def)

definition nfa_acceptingp :: "'qq_set \<times> 'dd_nfa \<times> 'qq_set \<times> 'qq_set \<Rightarrow> 'qq_set" where
  "nfa_acceptingp A = snd (snd (snd  A))"
lemma [simp]: "nfa_acceptingp (Q, D, I, F) = F" by (simp add: nfa_acceptingp_def)

lemmas nfa_selectors_def = nfa_accepting_def nfa_states_def 
       nfa_trans_def nfa_initial_def


definition nfa_invar :: "'q_set \<times> 'b \<times> 'd \<times> 'q_set \<times> 'q_set \<Rightarrow> bool" where
  "nfa_invar A =
   (s.invar (nfa_states A) \<and> 
    d.invar (nfa_trans A) \<and>
    s.invar (nfa_initial A) \<and> 
    s.invar (nfa_accepting A))"


definition nfa_\<alpha> :: "'q_set \<times> 'b \<times> 'd \<times> 'q_set \<times> 'q_set \<Rightarrow> ('q, 'a) NFA_rec" 
  where
  "nfa_\<alpha> A =
   \<lparr> \<Q> = s.\<alpha> (nfa_states A), 
     \<Sigma> = sem (nfa_alphabet A),
     \<Delta> = ba_to_set ` (d.\<alpha> (nfa_trans A)),
     \<I> = s.\<alpha> (nfa_initial A), 
     \<F> = s.\<alpha> (nfa_accepting A) \<rparr>"

definition nfa_to_set :: "'q_set \<Rightarrow> 'q set" where
   "nfa_to_set s = s.\<alpha> s"

definition nfa_invar_NFA :: "'q_set \<times> 'b \<times> 'd \<times> 'q_set \<times> 'q_set \<Rightarrow> bool" where
  "nfa_invar_NFA A \<equiv> (nfa_invar A \<and> NFA (nfa_\<alpha> A))"

definition nfa_invar_NFA' :: "'q_set \<times> 'b \<times> 'd \<times> 'q_set \<times> 'q_set \<Rightarrow> bool" where
  "nfa_invar_NFA' A \<equiv> (nfa_invar A \<and> NFA (nfa_\<alpha> A))"

definition nfa_invar_DFA :: "'q_set \<times> 'b \<times> 'd \<times> 'q_set \<times> 'q_set \<Rightarrow> bool" where
  "nfa_invar_DFA A \<equiv> (nfa_invar A \<and> weak_DFA (nfa_\<alpha> A))"

end

context automaton_by_lts_bool_algebra_defs
begin

lemma nfa_by_map_correct [simp]:
    "nfa nfa_\<alpha> nfa_invar_NFA"
    unfolding nfa_def nfa_invar_NFA_def
    by simp


lemma nfa_by_map_correct' [simp]:
    "nfa nfa_\<alpha> nfa_invar_NFA'"
    unfolding nfa_def nfa_invar_NFA'_def
    by simp




end



context automaton_by_lts_bool_algebra_defs
begin



end

context automaton_by_lts_bool_algebra_defs
begin

fun rename_states_gen_impl where
  "rename_states_gen_impl im im2 (Q, Sig, D, I, F) = (\<lambda> f.
   (im f Q, Sig, im2 (\<lambda>qaq. (f (fst qaq), fst (snd qaq), f (snd (snd qaq)))) D,
    im f I, im f F))"



lemma rename_states_impl_correct :
assumes wf_target: "nfa_by_lts_bool_algebra_defs 
               s_ops' l_ops lt_ops d_ops' sem empty_op noempty_op 
                   intersect_op diff_op elem_op canonical_op "
assumes im_OK: "set_image s.\<alpha> s.invar (set_op_\<alpha> s_ops') (set_op_invar s_ops') im"
assumes im2_OK: "lts_image d.\<alpha> d.invar (clts_op_\<alpha> d_ops') (clts_op_invar d_ops') im2"
shows "nfa_rename_states nfa_\<alpha> nfa_invar_NFA
           (automaton_by_lts_bool_algebra_syntax.nfa_\<alpha> s_ops' d_ops' sem)
           (automaton_by_lts_bool_algebra_syntax.nfa_invar_NFA s_ops' d_ops' sem)
           (rename_states_gen_impl im im2)"
proof (intro nfa_rename_states.intro 
             nfa_rename_states_axioms.intro
             automaton_by_lts_bool_algebra_defs.nfa_by_map_correct)
  show "automaton_by_lts_bool_algebra_defs s_ops l_ops lt_ops d_ops
        sem empty_op noempty_op 
                   intersect_op diff_op elem_op canonical_op " 
  by (fact automaton_by_lts_bool_algebra_defs_axioms)
  show "automaton_by_lts_bool_algebra_defs s_ops' l_ops lt_ops d_ops'
        sem empty_op noempty_op 
                   intersect_op diff_op elem_op canonical_op " 
    by (intro nfa_by_lts_defs___sublocale wf_target)
  fix n f
  assume invar: "nfa_invar_NFA n"
  obtain QL SigL DL IL FL where n_eq[simp]: "n = (QL, SigL, DL, IL, FL)" 
        by (cases n, blast)

  interpret s': StdSet s_ops' using wf_target 
        unfolding nfa_by_lts_bool_algebra_defs_def by simp
  interpret d': StdLTS d_ops' elem_op using wf_target 
        unfolding nfa_by_lts_bool_algebra_defs_def by simp
  interpret im: set_image s.\<alpha> s.invar s'.\<alpha> s'.invar im by fact
  interpret im2: lts_image d.\<alpha> d.invar d'.\<alpha> d'.invar im2 by fact

  from invar have invar_weak: "nfa_invar n" and wf: "NFA (nfa_\<alpha> n)"
    unfolding nfa_invar_NFA_def by simp_all

 have pre:"automaton_by_lts_bool_algebra_syntax sem empty_op noempty_op intersect_op
   diff_op elem_op canonical_op"
    by (simp add: automaton_by_lts_bool_algebra_syntax_axioms)

  note nfa_var = automaton_by_lts_bool_algebra_syntax.nfa_invar_def
      [of sem empty_op noempty_op intersect_op diff_op elem_op 
          canonical_op s_ops' d_ops', OF pre]

  let ?nfa_\<alpha>' = "automaton_by_lts_bool_algebra_syntax.nfa_\<alpha> s_ops' d_ops' sem"
  let ?nfa_invar' = "automaton_by_lts_bool_algebra_syntax.nfa_invar s_ops' d_ops'"
  let ?nfa_invar_NFA' = "automaton_by_lts_bool_algebra_syntax.nfa_invar_NFA s_ops' d_ops'"
  thm im.image_correct
  from invar_weak pre
  have "?nfa_invar' (rename_states_gen_impl im im2 n f) \<and>
        ?nfa_\<alpha>' (rename_states_gen_impl im im2 n f) = 
         NFA_rename_states (nfa_\<alpha> n) f"
    
    apply (simp add: nfa_var 
                     automaton_by_lts_bool_algebra_syntax.nfa_invar_def 
                     automaton_by_lts_bool_algebra_syntax.nfa_\<alpha>_def
                     automaton_by_lts_bool_algebra_syntax.nfa_selectors_def
                     NFA_rename_states_def 
                     im.image_correct im2.lts_image_correct)
    apply (subgoal_tac "automaton_by_lts_bool_algebra_syntax.nfa_alphabet
              (im f QL, SigL, im2 (\<lambda>qaq. (f (fst qaq), fst (snd qaq), f (snd (snd qaq)))) DL,
               im f IL, im f FL) = SigL")
     defer
    using automaton_by_lts_bool_algebra_syntax.nfa_alphabet_def
          [of sem empty_op noempty_op intersect_op diff_op elem_op 
          canonical_op  
          "(im f QL, SigL, im2 (\<lambda>qaq. (f (fst qaq), fst (snd qaq), f (snd (snd qaq)))) DL, im f IL,
      im f FL)", OF pre]
    apply fastforce
    apply (simp add: image_iff)
    apply (simp add: set_eq_iff)
    apply auto
    apply (metis (no_types, lifting) Pair_inject 
           automaton_by_lts_bool_algebra_syntax.ba_to_set.simps)
  proof -
    fix aa a ac b 
    assume p1: "\<forall>x. (x \<in> aa) = (x \<in> sem ac)" and
           p2: "(a, ac, b) \<in> d.\<alpha> DL" 
    from p2 have c1: "automaton_by_lts_bool_algebra_syntax.ba_to_set sem
       (f a, ac, f b)
       \<in> automaton_by_lts_bool_algebra_syntax.ba_to_set sem `
          (\<lambda>qaq. (f (fst qaq), fst (snd qaq), f (snd (snd qaq)))) ` d.\<alpha> DL"
      by force
    from p1 have "aa = sem ac" by auto
    from this p1 have "automaton_by_lts_bool_algebra_syntax.ba_to_set sem 
       (f a, ac, f b) = (f a, aa ,f b)"
      by (meson automaton_by_lts_bool_algebra_syntax.ba_to_set.simps pre)
    from this c1 show "(f a, aa, f b)
       \<in> automaton_by_lts_bool_algebra_syntax.ba_to_set sem `
          (\<lambda>qaq. (f (fst qaq), fst (snd qaq), f (snd (snd qaq)))) ` d.\<alpha> DL"
      by auto
  qed
  thus "?nfa_\<alpha>' (rename_states_gen_impl im im2 n f) = 
        NFA_rename_states (nfa_\<alpha> n) f"
       "?nfa_invar_NFA' sem (rename_states_gen_impl im im2 n f)"
    unfolding automaton_by_lts_bool_algebra_syntax.nfa_invar_NFA_def
    using NFA_rename_states___is_well_formed[OF wf, of f]
    apply (simp_all add: NFA_remove_states___is_well_formed)
    using nfa_alphabet_def[of n]  pre
          automaton_by_lts_bool_algebra_syntax.nfa_alphabet_def 
         [of sem empty_op noempty_op intersect_op diff_op elem_op 
          canonical_op "(im f QL, SigL, im2 (\<lambda>qaq. (f (fst qaq), fst (snd qaq), f (snd (snd qaq)))) DL,
          im f IL, im f FL)"]
          invar n_eq nfa_invar_NFA_def[of n]
    apply simp
    by (simp add: automaton_by_lts_bool_algebra_syntax.nfa_invar_NFA_def)
qed



subsection \<open> Constructing Automata \<close>

definition nfa_construct_ba_aux ::
  "'q_set \<times> 'b \<times> 'd \<times> 'q_set \<times> 'q_set \<Rightarrow> 'q \<times> 'b \<times> 'q \<Rightarrow> 
   'q_set \<times> 'b \<times> 'd \<times> 'q_set \<times> 'q_set" where 
   "nfa_construct_ba_aux = (\<lambda>(Q, Sig, D, I, F) (q1, l, q2).
    (s.ins q1 (s.ins q2 Q), Sig, 
     d.add q1 (intersect_op l Sig) q2 D,
     I, F))"


definition wf_IA :: "'q list \<times> 'b \<times>
                     ('q \<times> 'b \<times> 'q) list \<times> 'q list \<times> 'q list \<Rightarrow> bool" where
  "wf_IA ll = (canonical_op (fst (snd ll)) \<and>
              (\<forall> (q, l , q') \<in> set (fst (snd (snd ll))). canonical_op l))"

definition wf_\<Sigma>  where
   "wf_\<Sigma> ll = (canonical_op (fst (snd ll)))"

lemma nfa_construct_ba_aux_correct :
fixes q1 q2
assumes invar: "nfa_invar A \<and> wf_\<Sigma> A"
    and d_add_OK: 
        "lts_add d.\<alpha> d.invar d.add"
    and l_cano: "canonical_op l"
shows "nfa_invar (nfa_construct_ba_aux A (q1, l, q2))"
      "nfa_\<alpha> (nfa_construct_ba_aux A (q1, l, q2)) =
              construct_NFA_ba_aux sem (nfa_\<alpha> A) (q1, l, q2)"
proof -
  obtain QL SigL DL IL FL 
    where A_eq[simp]: "A = (QL, SigL, DL, IL, FL)" by (cases A, blast)

  from this invar nfa_invar_NFA_def nfa_invar_def
  have invarDL: "d.invar DL"
    by auto
  
  have DL_OK : "d.invar DL \<Longrightarrow> 
     (lts_add d.\<alpha> d.invar d.add) \<Longrightarrow>
                d.invar (d.add q1 l q2 DL) \<and>
                d.\<alpha> (d.add q1 l q2 DL) =
                d.\<alpha> DL \<union> {(q1, l, q2)}"
    proof -
      assume add_OK: "lts_add d.\<alpha> d.invar d.add" 
      assume invard: "d.invar DL" 
      then show ?thesis
        by (auto simp add: lts_add.lts_add_correct[OF add_OK invard] invar)
    qed

    from  invar A_eq wf_\<Sigma>_def[of A]
         nfa_invar_NFA_def[of A] nfa_alphabet_def[of A]
    have "canonical_op SigL"
      by auto

    from this l_cano
    have lsiglinter: "sem (intersect_op l SigL) = sem l \<inter> sem SigL" 
      using iv.intersect_intervals_sem by auto
      
      

    from DL_OK invar d_add_OK
    show "nfa_\<alpha> (nfa_construct_ba_aux A (q1, l, q2)) = 
                construct_NFA_ba_aux sem (nfa_\<alpha> A) (q1, l, q2)"
       "nfa_invar (nfa_construct_ba_aux A (q1, l, q2))"
      apply (simp_all add: nfa_construct_ba_aux_def 
                        nfa_\<alpha>_def s.correct nfa_invar_NFA_def nfa_invar_def)
      apply (simp add: \<open>canonical_op SigL\<close> iv.intersect_intervals_sem l_cano
          lts_add_def)
      by (simp add: lts_add.lts_add_correct(1))
qed


fun nfa_construct_ba  where
   "nfa_construct_ba (QL, SigL, DL, IL, FL) =
    foldl nfa_construct_ba_aux 
     (s.from_list (QL @ IL @ FL),
      SigL,
      d.empty,
      s.from_list IL,
      s.from_list FL) DL"
declare nfa_construct_ba.simps [simp del]


lemma nfa_construct_ba_aux_\<Sigma>: 
    "nfa_alphabet (nfa_construct_ba_aux (QL, SigL, DL, IL, FL) qlq) = SigL"
  unfolding nfa_construct_ba_aux_def nfa_alphabet_def
  using split
  apply simp
proof -
  obtain q l q' where qlq'_def: "qlq = (q, l, q')"  
    using ba_to_set.cases by blast
  from this
  show "fst (snd (case qlq of
              (q1, l, q2) \<Rightarrow>
                (s.ins q1 (s.ins q2 QL), SigL, d.add q1 
                (intersect_op l SigL) q2 DL, IL,
                 FL))) =
    SigL"
    using split by simp
qed

lemma nfa_construct_interval_\<Sigma>: 
    "nfa_alphabet (nfa_construct_ba (QL, SigL, DL, IL, FL)) = SigL"
  unfolding nfa_construct_ba.simps
  apply (induction DL)
  apply simp
  using foldl_Cons
proof -
  fix a DL
  have c1: "\<And> A D. nfa_alphabet
        (foldl nfa_construct_ba_aux
          A
          D) =
        (fst (snd A))"
  proof -
    fix A D
    show "nfa_alphabet (foldl nfa_construct_ba_aux A D) = fst (snd A)"
      apply (induction D arbitrary: A)
      using nfa_alphabet_def
      apply simp
      using foldl_Cons
      apply simp
      using nfa_alphabet_def nfa_construct_ba_aux_\<Sigma> by auto
  qed
  from this [of 
        "(s.from_list (QL @ IL @ FL), SigL, d.empty, 
         s.from_list IL, s.from_list FL)" "a # DL"]
  show "nfa_alphabet
        (foldl nfa_construct_ba_aux
          (s.from_list (QL @ IL @ FL), SigL, d.empty, s.from_list IL, s.from_list FL)
          (a # DL)) =
       SigL"
    by simp
qed

lemma nfa_construct_correct_gen :
  fixes ll :: "'q list \<times> 'b \<times>
                 ('q \<times> 'b \<times> 'q) list \<times> 'q list \<times> 'q list"
  assumes d_add_OK: "lts_add d.\<alpha> d.invar d.add"
      and wf_ll: "wf_IA ll"
  shows "nfa_invar (nfa_construct_ba ll)"
      "nfa_\<alpha> (nfa_construct_ba ll) = NFA_construct_ba sem ll" 
proof -
  obtain QL SigL DL IL FL where l_eq[simp]: 
      "ll = (QL, SigL, DL, IL, FL)" by (cases ll, blast)
  let ?A = 
      "(s.from_list (QL @ IL @ FL), SigL, d.empty, s.from_list IL, 
        s.from_list FL)"

  have A_invar: "nfa_invar ?A \<and> wf_\<Sigma> ?A" 
    unfolding nfa_invar_NFA_def nfa_invar_def
    using wf_ll wf_IA_def[of ll] l_eq
    by (simp add: s.correct l.correct d.correct_common wf_\<Sigma>_def)

  from wf_ll wf_IA_def[of ll] l_eq
  have wf_DL: "\<forall> (q, i, q') \<in> set DL.  canonical_op i"
    by auto
  
   have A_\<alpha>: "nfa_\<alpha> ?A = \<lparr>\<Q> = set (QL @ IL @ FL), \<Sigma> = sem SigL, 
                          \<Delta> = {}, \<I> = set IL, \<F> = set FL\<rparr>"
    by (simp add: nfa_\<alpha>_def s.correct d.correct_common l.correct)
  { fix A DL'
    have " nfa_invar A \<and> wf_\<Sigma> A \<Longrightarrow> set DL' \<subseteq> set DL \<Longrightarrow>
        (lts_add d.\<alpha> d.invar d.add) \<Longrightarrow>
        nfa_invar (foldl (nfa_construct_ba_aux) A DL') \<and>
        nfa_\<alpha> (foldl (nfa_construct_ba_aux) A DL') =
        foldl (construct_NFA_ba_aux sem) (nfa_\<alpha> A) DL'"
    proof (induct DL' arbitrary: A)
      case Nil thus ?case by simp
    next
      case (Cons qlq DL')
      note ind_hyp = Cons(1)
      note invar_A = Cons(2)
      note set_DL'_subset = Cons(3)
      note d_add_OK' = Cons(4)


      let ?A' = "nfa_construct_ba_aux A qlq"
      obtain q1 l q2 where qlq_eq[simp]: "qlq = (q1,  l, q2)" by (metis prod.exhaust)
      from set_DL'_subset wf_DL qlq_eq
      have canonical_l: "canonical_op l"
        by auto
      obtain QA \<Sigma>A IA FA \<Delta>A where
      A_eq: "A = (QA, \<Sigma>A, IA, FA, \<Delta>A)"
        using prod_cases5 by blast
      from invar_A nfa_construct_ba_aux_def wf_\<Sigma>_def[of A]
           wf_\<Sigma>_def[of "nfa_construct_ba_aux A qlq"] A_eq
      have wf\<Sigma>': "wf_\<Sigma> (nfa_construct_ba_aux A qlq)"
        by simp
        

        note aux_correct = nfa_construct_ba_aux_correct
          [of  A  l q1  q2, OF invar_A d_add_OK canonical_l] 
   
      from this ind_hyp [of ?A'] set_DL'_subset aux_correct d_add_OK wf\<Sigma>'
      show ?case
        by auto
       
    qed
  } note step = this [of ?A DL]

  with A_\<alpha> A_invar show \<alpha>_OK: "nfa_\<alpha> (nfa_construct_ba ll) = 
                               NFA_construct_ba sem ll" 
                    and weak_invar: "nfa_invar (nfa_construct_ba ll)" 
    by (simp_all add: nfa_construct_ba.simps NFA_construct_ba.simps 
          Ball_def d.correct_common d_add_OK)
qed




lemma (in nfa_by_lts_bool_algebra_defs) nfa_construct_ba_correct :
  "nfa_from_list_ba nfa_\<alpha> nfa_invar_NFA wf_IA nfa_construct_ba sem"
proof -
   from nfa_by_lts_bool_algebra_defs_axioms have "lts_add d.\<alpha> d.invar d.add" 
     unfolding nfa_by_lts_bool_algebra_defs_def StdLTS_def by simp
   with nfa_construct_correct_gen
   show ?thesis
     apply (intro nfa_from_list_ba.intro nfa_by_map_correct 
                  nfa_from_list_ba_axioms.intro)
      apply (simp_all add: nfa_invar_NFA_def nfa_construct_interval_\<Sigma>
                           NFA_construct_interval___is_well_formed)
   done
qed

lemma (in nfa_by_lts_bool_algebra_defs) nfa_construct_ba_correct' :
  "nfa_from_list_ba nfa_\<alpha> nfa_invar_NFA' wf_IA nfa_construct_ba sem"
proof -
   from nfa_by_lts_bool_algebra_defs_axioms have "lts_add d.\<alpha> d.invar d.add" 
     unfolding nfa_by_lts_bool_algebra_defs_def StdLTS_def by simp
   with nfa_construct_correct_gen
   show ?thesis
     apply (intro nfa_from_list_ba.intro nfa_by_map_correct 
                  nfa_from_list_ba_axioms.intro)
      apply (simp_all add: nfa_invar_NFA'_def nfa_construct_interval_\<Sigma>
                           NFA_construct_interval___is_well_formed)
     using nfa_construct_interval_\<Sigma> wf_IA_def
   done
qed



end

context nfa_dfa_by_lts_bool_algebra_defs 
begin

lemma (in automaton_by_lts_bool_algebra_syntax) automaton_by_lts_correct :
  "nfa nfa_\<alpha> nfa_invar_NFA"
  unfolding nfa_\<alpha>_def nfa_invar_NFA_def nfa_def nfa_invar_def
  by simp

end

locale NFA_construct_reachable_locale = 
  automaton_by_lts_bool_algebra_defs s_ops l_ops lt_ops d_ops 
      sem empty_op noempty_op 
                   intersect_op diff_op elem_op canonical_op +
  qm: StdMap qm_ops (* The index max *)
  for s_ops::"('q::{NFA_states},'q_set,_) set_ops_scheme"
  and l_ops::"('a::linorder,'a_set,_) set_ops_scheme"
  and lt_ops::"('b, 'ai_set,_) set_ops_scheme"
  and d_ops::"('q, 'b, 'a, 'd,_) common_lts_ops_scheme"
  and qm_ops :: "('i, 'q::{NFA_states}, 'm, _) map_ops_scheme" 
  and sem :: "'b \<Rightarrow> 'a set"
  and empty_op :: "'b \<Rightarrow> bool"
  and noempty_op :: "'b \<Rightarrow> bool"
  and intersect_op :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"
  and diff_op :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b"
  and elem_op :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  and canonical_op :: "'b \<Rightarrow> bool" +
  fixes f :: "'q2 \<Rightarrow> 'i"
    and ff :: "'q2_rep \<Rightarrow> 'i"
    and q2_\<alpha> :: "'q2_rep \<Rightarrow> 'q2"  
    and q2_invar :: "'q2_rep \<Rightarrow> bool" 
begin

text \<open> the pair (qm,n) denotes a map qm and the keys are the range 
       0 ... n - 1.
       state_map_\<alpha> is map from a state q to another state q'.
       firstly, the function f maps q to i and then qm maps i to another state q'.
  \<close>

definition state_map_\<alpha> where "state_map_\<alpha> \<equiv> (\<lambda>(qm, n::nat). qm.\<alpha> qm \<circ> f)"
definition state_map_invar where "state_map_invar \<equiv> (\<lambda>(qm, n). qm.invar qm \<and> 
         (\<forall>i q. qm.\<alpha> qm i = Some q \<longrightarrow> (\<exists>n' < n. q = states_enumerate n')))"


lemma state_map_extend_thm:
fixes n qm q
defines "qm'' \<equiv> qm.update_dj (f q) (states_enumerate n) qm"
assumes f_inj_on: "inj_on f S"
    and invar_qm_n: "state_map_invar (qm, n)"
    and q_in_S: "q \<in> S"
    and q_nin_dom: "q \<notin> dom (state_map_\<alpha> (qm, n))"
    and map_OK : "NFA_construct_reachable_map_OK 
                  S Map.empty {} 
                  (state_map_\<alpha> (qm, n))"
shows "state_map_invar (qm'', Suc n)"
      "qm.\<alpha> qm'' = (qm.\<alpha> qm) ((f q) \<mapsto> states_enumerate n)"
      "NFA_construct_reachable_map_OK S 
          (state_map_\<alpha> (qm, n)) 
          {q} (state_map_\<alpha> (qm'', Suc n))"
      "S \<inter> dom (state_map_\<alpha> (qm'', Suc n)) = 
         insert q ((dom (state_map_\<alpha> (qm, n))) \<inter> S)"
proof -
  from invar_qm_n have invar_qm: "qm.invar qm" unfolding state_map_invar_def by simp

  from q_nin_dom have fq_nin_dom_rm: "f q \<notin> dom (qm.\<alpha> qm)"
    unfolding state_map_\<alpha>_def by (simp add: dom_def)

  have qm''_props: "qm.invar qm''" 
                   "qm.\<alpha> qm'' = (qm.\<alpha> qm) (f q \<mapsto> states_enumerate n)"
    using qm.update_dj_correct [OF invar_qm fq_nin_dom_rm]
    by (simp_all add: qm''_def)  
  show "qm.\<alpha> qm'' = (qm.\<alpha> qm) (f q \<mapsto> states_enumerate n)" by (fact qm''_props(2))

  show invar_qm''_n: "state_map_invar (qm'', Suc n)"
    using invar_qm_n
    by (simp add: state_map_invar_def qm''_props) (metis less_Suc_eq)

  have rm''_q: "state_map_\<alpha> (qm'', Suc n) q = Some (states_enumerate n)"
    unfolding state_map_\<alpha>_def by (simp add: qm''_props)

  have dom_sub: "insert q (dom (state_map_\<alpha> (qm, n))) \<subseteq> dom (state_map_\<alpha> (qm'', Suc n))"
    unfolding state_map_\<alpha>_def 
    by (simp add: subset_iff dom_def qm''_props o_def)

  show dom_eq: "S \<inter> dom (state_map_\<alpha> (qm'', Suc n)) = insert q ((dom (state_map_\<alpha> (qm, n))) \<inter> S)"
      (is "?ls = ?rs")
  proof (intro set_eqI iffI)
    fix q'
    assume "q' \<in> ?rs" 
    with q_in_S dom_sub show "q' \<in> ?ls" by auto
  next
    fix q'
    assume "q' \<in> ?ls"
    hence q'_in_S: "q' \<in> S" and q'_in_dom: "q' \<in> dom (state_map_\<alpha> (qm'', Suc n))" by simp_all

    from f_inj_on q_in_S q'_in_S have fqq'[simp]: "f q' = f q \<longleftrightarrow> q' = q"
      unfolding inj_on_def by auto

    from q'_in_dom have "q' = q \<or> q' \<in> (dom (state_map_\<alpha> (qm, n)))" unfolding state_map_\<alpha>_def
      by (auto simp add: qm''_props o_def dom_def)
    with q'_in_S show "q' \<in> ?rs" by auto
  qed

  have qm''_inj_on: "inj_on (state_map_\<alpha> (qm'', Suc n)) (S \<inter> dom (state_map_\<alpha> (qm'', Suc n)))"
  proof (rule inj_onI)
    fix q' q''
    assume q'_in: "q' \<in> S \<inter> dom (state_map_\<alpha> (qm'', Suc n))"
    assume q''_in: "q'' \<in> S \<inter> dom (state_map_\<alpha> (qm'', Suc n))"
    assume state_map_\<alpha>_eq: "state_map_\<alpha> (qm'', Suc n) q' = state_map_\<alpha> (qm'', Suc n) q''"
 
    { fix q'''
      assume in_dom: "q''' \<in> S \<inter> dom (state_map_\<alpha> (qm, n))"

      from in_dom q_nin_dom have "q''' \<noteq> q" by auto
      with f_inj_on q_in_S in_dom have f_q'''_neq: "f q''' \<noteq> f q"
        unfolding inj_on_def by auto
            
      have prop1: "state_map_\<alpha> (qm'', Suc n) q''' = state_map_\<alpha> (qm, n) q'''" 
        unfolding state_map_\<alpha>_def
        by (simp add: o_def qm''_props f_q'''_neq)

      from invar_qm_n in_dom obtain n' where "n' < n" and 
           "state_map_\<alpha> (qm, n) q''' = Some (states_enumerate n')" 
        unfolding state_map_invar_def dom_def state_map_\<alpha>_def by auto

      with prop1 have prop2: "state_map_\<alpha> (qm'', Suc n) q''' \<noteq> state_map_\<alpha> (qm'', Suc n) q"
        by (simp add: rm''_q states_enumerate_eq)

      note prop1 prop2
    } note qm''_\<alpha>_props = this

    show "q' = q''"
    proof (cases "q' = q")
      case True note q'_eq[simp] = this
      show ?thesis
      proof (cases "q'' = q")
        case True thus ?thesis by simp
      next
        case False with q''_in dom_eq 
        have "q'' \<in> S \<inter> (dom (state_map_\<alpha> (qm, n)))" by simp
        with qm''_\<alpha>_props(2) [of q''] state_map_\<alpha>_eq have "False" by simp
        thus ?thesis ..
      qed
    next
      case False with q'_in dom_eq 
      have q'_in_dom_qm: "q' \<in> (S \<inter> dom (state_map_\<alpha> (qm, n)))" by simp
      show ?thesis
      proof (cases "q'' = q")
        case True 
        with qm''_\<alpha>_props(2) [of q'] state_map_\<alpha>_eq q'_in_dom_qm have "False" by simp
        thus ?thesis ..
      next
        case False with q''_in dom_eq 
        have q''_in_dom_qm: "q'' \<in> (S \<inter> dom (state_map_\<alpha> (qm, n)))" by simp

        from map_OK have "inj_on (state_map_\<alpha> (qm, n)) (S \<inter> dom (state_map_\<alpha> (qm, n)))"
          unfolding NFA_construct_reachable_map_OK_def by simp
        with q''_in_dom_qm q'_in_dom_qm state_map_\<alpha>_eq qm''_\<alpha>_props(1) show ?thesis
          unfolding inj_on_def by auto
      qed
    qed
  qed          

  show map_OK': "NFA_construct_reachable_map_OK S (state_map_\<alpha> (qm, n)) {q} (state_map_\<alpha> (qm'', Suc n))"
  proof
    show "{q} \<subseteq> dom (state_map_\<alpha> (qm'', Suc n))"
      by (simp add: rm''_q dom_def)
  next
    fix q' r'
    assume "state_map_\<alpha> (qm, n) q' = Some r'"
    with fq_nin_dom_rm show "state_map_\<alpha> (qm'', Suc n) q' = Some r'"
      unfolding state_map_\<alpha>_def by (auto simp add: qm''_props dom_def)
  next
    show "inj_on (state_map_\<alpha> (qm'', Suc n)) (S \<inter> dom (state_map_\<alpha> (qm'', Suc n)))"
      by (fact qm''_inj_on)
  qed
qed


text \<open> qm is a map from indexes to state names \<close>

definition NFA_construct_reachable_init_ba_impl where
  "NFA_construct_reachable_init_ba_impl I =
   foldl (\<lambda> ((qm, n), Is) q. 
          ((qm.update_dj (ff q) (states_enumerate n) qm, Suc n),
                             s.ins_dj (states_enumerate n) Is))
          ((qm.empty (), 0), s.empty ()) I"

lemma NFA_construct_reachable_init_ba_impl_correct :
fixes II D
defines "I \<equiv> map q2_\<alpha> II"
defines "S \<equiv> accessible (LTS_forget_labels D) (set I)"
assumes f_inj_on: "inj_on f S"
    and dist_I: "distinct I"
    and invar_I: "\<And>q. q \<in> set II \<Longrightarrow> q2_invar q"
    and ff_OK: "\<And>q. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> S \<Longrightarrow> ff q = f (q2_\<alpha> q)" 
shows
   "RETURN (NFA_construct_reachable_init_ba_impl II) \<le> \<Down> 
       (rprod (build_rel state_map_\<alpha> state_map_invar) 
              (build_rel s.\<alpha> s.invar)) 
     (SPEC (\<lambda>(rm, I'). 
        NFA_construct_reachable_map_OK 
          (accessible (LTS_forget_labels D) (set I)) Map.empty (set I) rm \<and>
        I' = (the \<circ> rm) ` (set I)))"
proof -
  let ?step = "(\<lambda>((qm, n), Is) q. 
           ((qm.update_dj (ff q) (states_enumerate n) qm, Suc n),
               s.ins_dj (states_enumerate n) Is))"
  { fix II
    have invar_OK : "\<And>qm n Is qm' n' Is'.
           set (map q2_\<alpha> II) \<subseteq> S \<Longrightarrow>
           distinct (map q2_\<alpha> II) \<Longrightarrow>
            \<forall>q\<in>set II. q2_invar q \<Longrightarrow>      
            dom (state_map_\<alpha> (qm, n)) \<inter> (set (map q2_\<alpha> II)) = {} \<Longrightarrow>
            state_map_invar (qm, n) \<Longrightarrow>
            s.invar Is \<Longrightarrow> 
            (\<And>q. q \<in> s.\<alpha> Is \<Longrightarrow> (\<exists>n' < n. q = states_enumerate n')) \<Longrightarrow>
            NFA_construct_reachable_map_OK S Map.empty {} (state_map_\<alpha> (qm, n)) \<Longrightarrow>
            ((qm', n'), Is') = foldl ?step ((qm, n),Is) II \<Longrightarrow>

              s.invar Is' \<and>
              s.\<alpha> Is' = ((the \<circ> (state_map_\<alpha> (qm', n'))) ` (set (map q2_\<alpha> II))) \<union> s.\<alpha> Is \<and>
              state_map_invar (qm', n') \<and>
           NFA_construct_reachable_map_OK S (state_map_\<alpha> (qm, n)) (set (map q2_\<alpha> II)) (state_map_\<alpha> (qm', n'))" 
    proof (induct II)
      case Nil thus ?case by (simp add: NFA_construct_reachable_map_OK_def)
    next
      case (Cons q II' qm n Is qm' n' Is')
      from Cons(2) have q_in_S: "q2_\<alpha> q \<in> S" and II'_subset: "set (map q2_\<alpha> II') \<subseteq> S" by simp_all
      from Cons(3) have q_nin_I': "q2_\<alpha> q \<notin> set (map q2_\<alpha> II')" and "distinct (map q2_\<alpha> II')" by simp_all
      from Cons(4) have invar_q: "q2_invar q" and invar_II': "\<forall>q\<in>set II'. q2_invar q" by simp_all
      note dom_qII'_dist = Cons(5)
      note invar_qm_n = Cons(6) 
      note invar_Is = Cons(7) 
      note memb_Is = Cons(8) 
      note map_OK = Cons(9)
      note fold_eq = Cons(10)

      let ?I' = "map q2_\<alpha> II'"
      define qm'' where "qm'' = qm.update_dj (ff q) (states_enumerate n) qm"
      define Is'' where "Is'' = s.ins_dj (states_enumerate n) Is"

      note ind_hyp = Cons(1) [OF II'_subset `distinct ?I'` invar_II', 
                              of qm'' "Suc n" Is'' qm' n' Is']

      from dom_qII'_dist have q_nin_dom: "q2_\<alpha> q \<notin> dom (state_map_\<alpha> (qm, n))" by auto

      from state_map_extend_thm [OF f_inj_on invar_qm_n q_in_S q_nin_dom map_OK]
      have invar_qm''_n: "state_map_invar (qm'', Suc n)" and
           qm''_alpha: "map_op_\<alpha> qm_ops qm'' = 
                        (map_op_\<alpha> qm_ops qm) (ff q \<mapsto> states_enumerate n)" and
           map_OK': "NFA_construct_reachable_map_OK S (state_map_\<alpha> (qm, n)) {q2_\<alpha> q} (state_map_\<alpha> (qm'', Suc n))" and
           dom_eq: "S \<inter> dom (state_map_\<alpha> (qm'', Suc n)) = insert (q2_\<alpha> q) ((dom (state_map_\<alpha> (qm, n))) \<inter> S)"
        using qm''_def[symmetric] ff_OK [OF invar_q q_in_S, symmetric]
        by simp_all

      have dom_II'_dist: "dom (state_map_\<alpha> (qm'', Suc n)) \<inter> set ?I' = {}" 
      proof -
        from II'_subset have "dom (state_map_\<alpha> (qm'', Suc n)) \<inter> set (map q2_\<alpha> II') =
             (S \<inter> dom (state_map_\<alpha> (qm'', Suc n))) \<inter> set (map q2_\<alpha> II')" by auto
        hence step: "dom (state_map_\<alpha> (qm'', Suc n)) \<inter> set (map q2_\<alpha> II') = 
                    insert (q2_\<alpha> q) ((dom (state_map_\<alpha> (qm, n))) \<inter> S) \<inter> set (map q2_\<alpha> II')"
          unfolding dom_eq by simp

        from dom_qII'_dist q_nin_I' show ?thesis unfolding step
           by (auto simp add: set_eq_iff) 
      qed

      have state_n_nin_Is: "states_enumerate n \<notin> s.\<alpha> Is"
      proof (rule notI)
        assume "states_enumerate n \<in> s.\<alpha> Is"
        from memb_Is[OF this] show False
          by (simp add: states_enumerate_eq)
      qed

      from state_n_nin_Is invar_Is 
      have Is''_props: "s.invar Is''" "s.\<alpha> Is'' = insert (states_enumerate n) (s.\<alpha> Is)"
        by (simp_all add: Is''_def s.correct)

      have state_n_nin_Is: "states_enumerate n \<notin> s.\<alpha> Is"
      proof (rule notI)
        assume "states_enumerate n \<in> s.\<alpha> Is"
        from memb_Is[OF this] show False
          by (simp add: states_enumerate_eq)
      qed

      from state_n_nin_Is invar_Is 
      have Is''_props: "s.invar Is''" "s.\<alpha> Is'' = insert (states_enumerate n) (s.\<alpha> Is)"
        by (simp_all add: Is''_def s.correct)

      have ind_hyp': "
        s.invar Is' \<and>
        s.\<alpha> Is' = (the \<circ> state_map_\<alpha> (qm', n')) ` set ?I' \<union> s.\<alpha> Is'' \<and>
        state_map_invar (qm', n') \<and>
        NFA_construct_reachable_map_OK S (state_map_\<alpha> (qm'', Suc n)) (set ?I') (state_map_\<alpha> (qm', n'))"
      proof (rule ind_hyp [OF dom_II'_dist invar_qm''_n Is''_props(1)])
        fix q
        assume "q \<in> s.\<alpha> Is''"
        with Is''_props(2) memb_Is show "\<exists>n'<Suc n. q = states_enumerate n'"
          by auto (metis less_Suc_eq)
      next
        from map_OK' 
        show "NFA_construct_reachable_map_OK S Map.empty {} (state_map_\<alpha> (qm'', Suc n))"
          unfolding NFA_construct_reachable_map_OK_def by simp
      next
        from fold_eq show "((qm', n'), Is') = foldl ?step ((qm'', Suc n), Is'') II'" 
          by (simp add: qm''_def Is''_def)
      qed

      show ?case proof (intro conjI)
        show "s.invar Is'" "state_map_invar (qm', n')" by (simp_all add: ind_hyp')
      next
        from ind_hyp' qm''_alpha have "state_map_\<alpha> (qm', n') (q2_\<alpha> q) = Some (states_enumerate n)" 
          unfolding NFA_construct_reachable_map_OK_def state_map_\<alpha>_def 
          by (simp add: ff_OK[OF invar_q q_in_S])
        thus "s.\<alpha> Is' = (the \<circ> state_map_\<alpha> (qm', n')) ` set (map q2_\<alpha> (q # II')) \<union> s.\<alpha> Is"
          by (simp add: ind_hyp' Is''_props)
      next
        show "NFA_construct_reachable_map_OK S (state_map_\<alpha> (qm, n)) (set (map q2_\<alpha> (q # II')))
              (state_map_\<alpha> (qm', n'))"
        proof (rule NFA_construct_reachable_map_OK_trans [of _ _ "{q2_\<alpha> q}"
               "state_map_\<alpha> (qm'', Suc n)" "set ?I'"]) 
          show "set (map q2_\<alpha> (q # II')) \<subseteq> {q2_\<alpha> q} \<union> set ?I'" by auto
        next
          show "NFA_construct_reachable_map_OK S (state_map_\<alpha> (qm'', Suc n)) (set ?I') 
                  (state_map_\<alpha> (qm', n'))"
            using ind_hyp' by simp
        next
          show "NFA_construct_reachable_map_OK S (state_map_\<alpha> (qm, n)) {q2_\<alpha> q} (state_map_\<alpha> (qm'', Suc n))" 
            by (simp add: map_OK')
        qed
      qed
    qed
  } note ind_proof = this

  have pre1 : "set (map q2_\<alpha> II) \<subseteq> S" unfolding S_def I_def by (rule accessible_subset_ws)
  have pre2 : "distinct (map q2_\<alpha> II)" using dist_I[unfolded I_def] by simp
  have pre3 : "\<forall>q\<in>set II. q2_invar q" using invar_I by simp

  have pre4 : "dom (state_map_\<alpha> (qm.empty (), 0)) \<inter> set (map q2_\<alpha> II) = {}"
    unfolding state_map_\<alpha>_def by (simp add: qm.correct o_def)

  have pre5 : "state_map_invar (qm.empty (), 0)"
    unfolding state_map_invar_def by (simp add: qm.correct)

  have pre6 : "NFA_construct_reachable_map_OK S Map.empty {} 
               (state_map_\<alpha> (qm.empty(), 0))"
    unfolding NFA_construct_reachable_map_OK_def state_map_\<alpha>_def by (simp add: qm.correct o_def)

  note ind_proof' = ind_proof [OF ]
  obtain qm' n' Is' where 
  res_eq: "NFA_construct_reachable_init_ba_impl II = ((qm', n'), Is')" by (metis prod.exhaust)
  
  define tmpsempty where "tmpsempty = s.empty ()"
  note ind_proof' = ind_proof [OF pre1 pre2 pre3 pre4 pre5 _ _ pre6, 
          of tmpsempty qm' n' Is',
    folded NFA_construct_reachable_init_ba_impl_def]

  from ind_proof' show ?thesis 
   apply (rule_tac SPEC_refine)+
    apply (simp add: s.correct 
     I_def tmpsempty_def br_def
     state_map_\<alpha>_def state_map_invar_def single_valued_def
    res_eq S_def NFA_construct_reachable_map_OK_def f_inj_on)
    using NFA_construct_reachable_init_ba_impl_def res_eq 
    by (auto simp add: tmpsempty_def br_def single_valued_def)
qed


definition NFA_construct_reachable_impl_step_rel where
  "NFA_construct_reachable_impl_step_rel =
    build_rel (\<lambda>DS. (\<lambda>(a, q'). (sem a, q2_\<alpha> q')) ` DS)
              (\<lambda>DS. (\<forall>a q'. (a, q') \<in> DS \<longrightarrow> q2_invar q') \<and>
                    (\<forall>a q' q''. (a, q') \<in> DS \<longrightarrow> (a, q'') \<in> DS \<longrightarrow> 
                       ((q2_\<alpha> q' = q2_\<alpha> q'') \<longleftrightarrow> q' = q'')))"

definition NFA_construct_reachable_impl_step_ba where
"NFA_construct_reachable_impl_step_ba DS qm0 n D0 q =
  FOREACH {(a,q').(a,q') \<in> (DS q)} 
  (\<lambda>(a, q') ((qm, n), DD', N). 
   if (noempty_op a) then do {
   let ((qm', n'), r') =
    (let r'_opt = qm.lookup (ff q') qm in
      if (r'_opt = None) then
         ((qm.update_dj (ff q') (states_enumerate n) qm, Suc n), states_enumerate n)
      else
         ((qm, n), the r'_opt)
    );
  RETURN ((qm', n'), 
    (d.add (the (qm.lookup (ff q) qm0)) a r' DD'), q' # N)
} else RETURN ((qm, n), DD', N)) ((qm0, n), D0, [])"

lemma inj_DSq: 
  fixes D
  assumes DS_OK1: "\<forall> (a, q') \<in> D. canonical_op a"
      and DS_OK2: "inj_on q2_\<alpha> {q| a q. (a, q) \<in> D}"
    shows "inj_on (\<lambda>(a, q'). (sem a, q2_\<alpha> q')) 
                  ({(a, q'). (a, q') \<in> D})"
  unfolding inj_on_def
proof 
  fix x
  assume x_in: "x \<in> {(a, q'). (a, q') \<in> D}"
  show "\<forall>y\<in>{(a, q'). (a, q') \<in> D}.
            (case x of (a, q') \<Rightarrow> (sem a, q2_\<alpha> q')) =
            (case y of (a, q') \<Rightarrow> (sem a, q2_\<alpha> q')) \<longrightarrow>
            x = y"
  proof 
    fix y
    assume y_in: "y \<in> {(a, q'). (a, q') \<in> D}"
    from x_in obtain x1 x2 where x12_def: "x = (x1, x2)" 
      by blast

    from y_in obtain y1 y2 where y12_def: "y = (y1, y2)" 
      by blast

   have bool_algebra_pre: "bool_algebra sem empty_op noempty_op intersect_op diff_op elem_op
   canonical_op"
      using iv.bool_algebra_axioms by blast
    note inj_sem = bool_algebra.inj_semIs_aux 
                   [of sem empty_op noempty_op intersect_op 
                       diff_op elem_op  canonical_op, OF bool_algebra_pre ]
    from x_in y_in inj_sem  DS_OK1 DS_OK2
    show "(case x of (a, q') \<Rightarrow> (sem a, q2_\<alpha> q')) =
         (case y of (a, q') \<Rightarrow> (sem a, q2_\<alpha> q')) \<longrightarrow>
         x = y"
      by (metis (mono_tags, lifting) Pair_inject 
              inj_onD mem_Collect_eq old.prod.case x12_def y12_def)
  qed
qed


lemma bool_algebra_pre : "bool_algebra sem empty_op noempty_op intersect_op 
                       diff_op elem_op  canonical_op"
  using iv.bool_algebra_axioms by blast

lemma NFA_construct_reachable_impl_step_correct :
fixes D II
fixes q :: "'q2_rep"
defines "I \<equiv> map q2_\<alpha> II"
defines "S \<equiv> accessible (LTS_forget_labels D) (set I)"
assumes f_inj_on: "inj_on f S"
    and ff_OK: "\<And>q. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> S \<Longrightarrow> ff q = f (q2_\<alpha> q)" 
    and d_add_OK: "lts_add d.\<alpha> d.invar d.add" 
    (* \<forall>q a q' q''. (q, a, q') \<in> D \<and> (q, a, q'') \<in> D \<and> q'' \<noteq> q' \<longrightarrow> *)     
    and rm_eq: "rm = state_map_\<alpha> (qm0, n)"
    and invar_qm0_n: "state_map_invar (qm0, n)"
    and D0'_eq: "D0' = d.\<alpha> D0" "ba_to_set ` D0' = \<Delta> \<A>"
    and invar_D0: "d.invar D0"
    and rm_q:  "rm (q2_\<alpha> q) = Some r"
    and r_nin: "r \<notin> \<Q> \<A>"
    and invar_q: "q2_invar q"
    and q_in_S: "q2_\<alpha> q \<in> S"
    and DS_OK0: "\<forall> (a, q') \<in> (DS q). canonical_op a"
    and DS_OK1: "inj_on q2_\<alpha> {q'| a q'. (a, q') \<in> (DS q)}"
    and DS_OK: "(DS q, {(a, q'). (q2_\<alpha> q, a, q') \<in> D}) \<in> 
          NFA_construct_reachable_impl_step_rel"
    and weak_invar: "NFA_construct_reachable_abstract_impl_weak_invar 
                     Sig I FP D (rm, \<A>)"
shows "NFA_construct_reachable_impl_step_ba DS qm0 n D0 q \<le> 
  \<Down> (rprod (build_rel state_map_\<alpha> state_map_invar) (rprod (build_rel 
           (\<lambda> d. ba_to_set ` d.\<alpha> d) d.invar) 
           (map_list_rel (build_rel q2_\<alpha> q2_invar))))
     (NFA_construct_reachable_abstract_impl_step S D rm (\<Delta> \<A>) 
                                                        (q2_\<alpha> q))"

  apply (subgoal_tac "NFA_construct_reachable_impl_step_ba DS qm0 n D0 q \<le> 
  \<Down> (rprod (build_rel state_map_\<alpha> state_map_invar) (rprod (build_rel 
           (\<lambda> d. ba_to_set ` d.\<alpha> d) d.invar) 
           (map_list_rel (build_rel q2_\<alpha> q2_invar))))
     (NFA_construct_reachable_abstract_impl_step S D rm (ba_to_set ` D0') 
                                                        (q2_\<alpha> q))")
  apply (simp add: assms(9))
  unfolding NFA_construct_reachable_impl_step_ba_def
            NFA_construct_reachable_abstract_impl_step_def
            nempI_correct
  using [[goals_limit = 10]]
  apply (refine_rcg)
  (* "preprocess goals" *)
  apply (subgoal_tac "inj_on (\<lambda>(a, q'). (sem a, q2_\<alpha> q')) 
                ({(a, q'). (a, q') \<in> DS q})")
  apply assumption
  using inj_DSq[OF DS_OK0 DS_OK1]
  apply force
  (* "goal solved" *)
  apply (insert DS_OK inj_semIs) []
  apply (simp add: NFA_construct_reachable_impl_step_rel_def)
  apply (simp add: in_br_conv br_def)
  (* "goal solved" *)
  apply (simp add: rm_eq D0'_eq invar_qm0_n invar_D0)
  apply (simp add: in_br_conv)
  apply (simp add: invar_D0 invar_qm0_n)
  using assms(8) invar_D0 iv.noempty_intervals_sem 
  iv.empty_interval_sem DS_OK0
  apply fastforce
  (* "goal solved" *)
  apply (simp add: br_def in_br_conv invar_D0)
  apply (clarify, simp)+
   
  apply (rename_tac it N D' q'' qm n NN a b q')
  apply (subgoal_tac "
    (qm.lookup (ff q'') qm = None \<longrightarrow>
        RETURN
         ((qm.update_dj (ff q'') (states_enumerate n) qm, Suc n), states_enumerate n)
        \<le> \<Down> (rprod (build_rel state_map_\<alpha> state_map_invar) Id)
            (SPEC
              (\<lambda>(rm', r').
                  NFA_construct_reachable_map_OK S (state_map_\<alpha> (qm, n)) {q2_\<alpha> q'}
                   rm' \<and>
                  rm' (q2_\<alpha> q') = Some r'))) \<and>
       ((\<exists>y. qm.lookup (ff q'') qm = Some y) \<longrightarrow>
        RETURN ((qm, n), the (qm.lookup (ff q'') qm))
        \<le> \<Down> (rprod (build_rel state_map_\<alpha> state_map_invar) Id)
            (SPEC
              (\<lambda>(rm', r').
                  NFA_construct_reachable_map_OK S (state_map_\<alpha> (qm, n)) {q2_\<alpha> q'}
                   rm' \<and>
                  rm' (q2_\<alpha> q') = Some r')))")
  apply assumption
  apply (simp del: br_def rprod_def 
  add: Let_def ff_OK pw_le_iff refine_pw_simps rprod_sv) 
  apply (rule conjI)
  apply (rule impI)
  defer
  apply (rule impI)
  apply (erule exE)
  apply (rename_tac r)
  defer
  apply (clarify, simp add: br_def)+
  apply (rename_tac it N i1 q'' qm n D' NN r' qm' n' i2 q')
  defer
     apply (simp add: br_def D0'_eq)
    apply (rename_tac it N i1  q'' qm n D' NN i2 q')
  defer
  apply (rename_tac it N i1 q'' qm n D' NN i2 q' r)
proof -
  fix it N i1 q'' qm n qm' NN r' D' n' i2 q'
  
  assume aq'_in_it: "(i2, q') \<in> it"
     and aq''_in_it: "(i1, q'') \<in> it"
     and it_subset: "it \<subseteq> DS q"
     and q''_q'_eq: "q2_\<alpha> q'' = q2_\<alpha> q'"
     and semI_a_b: "sem i2 \<noteq> {}"
  
  let ?it' = "((\<lambda>x. case x of (a, q') \<Rightarrow> (sem a, q2_\<alpha> q')) ` it)"
  assume invar_foreach: 
     "NFA_construct_reachable_abstract_impl_foreach_invar 
      S D rm (ba_to_set ` D0') (q2_\<alpha> q) ?it'
               (state_map_\<alpha> (qm, n), ba_to_set `  d.\<alpha> D', N)"
     and invar_qm_n: "state_map_invar (qm, n)"
     and invar_D': "d.invar D'"

  from aq'_in_it aq''_in_it it_subset DS_OK
  have invar_q': "q2_invar q'" and invar_q'': "q2_invar q''"
    by (auto simp add: NFA_construct_reachable_impl_step_rel_def br_def)   
  have q'_in_S: "q2_\<alpha> q' \<in> S"
  proof -
    from DS_OK have "
        {(a, q'). (q2_\<alpha> q, a, q') \<in> D \<and> a \<noteq> {}} = 
         (\<lambda> (a, q'). (sem a, q2_\<alpha> q')) ` {(a,q'). (a, q') \<in> DS q \<and> 
          sem a \<noteq> {}}"
      unfolding NFA_construct_reachable_impl_step_rel_def 
       apply (insert DS_OK) []
  apply (simp add: NFA_construct_reachable_impl_step_rel_def)
  apply (simp add: in_br_conv br_def)
  apply (simp only: set_eq_iff)
      by (fastforce)
     with aq'_in_it it_subset semI_a_b have "(sem i2, q2_\<alpha> q') \<in> 
          {(a, q'). (q2_\<alpha> q, a, q') \<in> D \<and> a \<noteq> {}}"
      by (simp add: image_iff Bex_def) blast
    hence "(q2_\<alpha> q, q2_\<alpha> q') \<in> LTS_forget_labels D"
      unfolding LTS_forget_labels_def 
      NFA_construct_reachable_impl_step_rel_def
      by (metis (mono_tags, lifting) aq'_in_it 
                 case_prodD case_prodI 
                 in_mono it_subset mem_Collect_eq)
    with q_in_S show ?thesis unfolding S_def accessible_def
      by (metis rtrancl_image_advance)
  qed
  from q'_in_S q''_q'_eq have q''_in_S: "q2_\<alpha> q''\<in> S" by simp
  from ff_OK[OF invar_q'' q''_in_S] q''_q'_eq have ff_q''_eq[simp]: 
    "ff q'' = f (q2_\<alpha> q')" by simp

  define D'' where "D'' = {(a, q'). (q2_\<alpha> q, a, q') \<in> D \<and> a \<noteq> {}} - ?it'"
  from invar_foreach have
     qm_OK: "NFA_construct_reachable_map_OK S rm (snd ` D'') 
     (state_map_\<alpha> (qm, n))" and
     set_N_eq: "set N = snd ` D''" and
     D'_eq: "ba_to_set ` d.\<alpha> D' = (ba_to_set ` D0') \<union>
       {(the (state_map_\<alpha> (qm, n) (q2_\<alpha> q)), a, 
         the (state_map_\<alpha> (qm, n) q')) |a q'. (a, q') \<in> D'' \<and> a \<noteq> {}}"
    unfolding NFA_construct_reachable_abstract_impl_foreach_invar.simps 
              NFA_construct_reachable_map_OK_def
              D''_def[symmetric]
    by (auto simp add: D''_def D0'_eq)
  (* "... and the case that the map needs to be extended." *)
  { 
   
    assume "qm.lookup (ff q'') qm = None"
    with invar_qm_n have q'_nin_dom: 
    "q2_\<alpha> q' \<notin> dom (state_map_\<alpha> (qm, n))"
      unfolding state_map_invar_def state_map_\<alpha>_def 
      by (simp add: qm.correct dom_def)

    from qm_OK have qm_OK':
      "NFA_construct_reachable_map_OK S Map.empty {} (state_map_\<alpha> (qm, n))"
      unfolding NFA_construct_reachable_map_OK_def by simp

    define qm' where "qm'= qm.update_dj 
        (f (q2_\<alpha> q')) (states_enumerate n) qm"
    from state_map_extend_thm [OF f_inj_on invar_qm_n 
                      q'_in_S q'_nin_dom qm_OK', folded qm'_def]
    have invar_qm'_n: "state_map_invar (qm', Suc n)" and
         qm'_alpha: "qm.\<alpha> qm' = (qm.\<alpha> qm) (f (q2_\<alpha> q') 
          \<mapsto> states_enumerate n)" and
         qm'_OK: 
          "NFA_construct_reachable_map_OK S 
           (state_map_\<alpha> (qm, n)) {q2_\<alpha> q'} 
           (state_map_\<alpha> (qm', Suc n))"
      by simp_all

    from qm'_alpha have rm'_q': 
          "state_map_\<alpha> (qm', Suc n) (q2_\<alpha> q') = Some (states_enumerate n)"
      unfolding state_map_\<alpha>_def by simp

    define aa where "aa = state_map_\<alpha> (qm.update_dj (ff q'') 
                     (states_enumerate n) qm, Suc n)"
    
    from invar_qm'_n qm'_OK rm'_q'
    show  "\<exists> a. ((qm.update_dj (ff q'') (states_enumerate n) qm, Suc n), a)
           \<in> br state_map_\<alpha> state_map_invar \<and> NFA_construct_reachable_map_OK S
        (state_map_\<alpha> (qm, n)) {q2_\<alpha> q'} a \<and>
        a (q2_\<alpha> q') =
         Some (states_enumerate n)"
    proof -
      have "((qm.update_dj (ff q'') (states_enumerate n) qm, Suc n), aa)
           \<in> br state_map_\<alpha> state_map_invar \<and> NFA_construct_reachable_map_OK S
        (state_map_\<alpha> (qm, n)) {q2_\<alpha> q'} aa \<and>
        aa (q2_\<alpha> q') =
         Some (states_enumerate n)"
        unfolding qm'_def[symmetric] ff_q''_eq aa_def
        apply (auto simp add: br_def)
        using invar_qm'_n apply blast
        using rm'_q' apply auto[1]
        apply (insert qm'_OK)
        apply (simp add: qm'_def qm'_OK NFA_construct_reachable_map_OK_def)
        apply (simp add: NFA_construct_reachable_map_OK_def)
        apply (simp add: NFA_construct_reachable_map_OK_def rm'_q')
        done
      from this show ?thesis by auto
    qed
  }
  (*  "Consider the case that the map does not need to be extended" *)
  { fix r
    assume "qm.lookup (ff q'') qm = Some r"
    define aa where "aa = (state_map_\<alpha> (qm, n))"
    with invar_qm_n qm_OK
    have " ((qm, n), aa) \<in> br state_map_\<alpha> state_map_invar \<and>
           NFA_construct_reachable_map_OK S (state_map_\<alpha> (qm, n)) {q2_\<alpha> q'} aa \<and>
           aa (q2_\<alpha> q') = qm.lookup (ff q'') qm"
     apply (simp add: state_map_\<alpha>_def qm.correct state_map_invar_def
                    NFA_construct_reachable_map_OK_def rm_eq dom_def br_def)
      using \<open>qm.lookup (ff q'') qm = Some r\<close> qm.lookup_correct by auto
    from this
    show "\<exists> aa.((qm, n), aa) \<in> br state_map_\<alpha> state_map_invar \<and>
           NFA_construct_reachable_map_OK S (state_map_\<alpha> (qm, n)) {q2_\<alpha> q'} aa \<and>
           aa (q2_\<alpha> q') = qm.lookup (ff q'') qm"
      by auto
  }
 
  { (* It remains to show that adding to the transition systems works. 
        Here, a case distinction
        depending on whether the input is weak deterministic, is needed. *)
    fix r'

    from qm_OK rm_q have r_intro1: "state_map_\<alpha> (qm, n) (q2_\<alpha> q) = Some r"
      unfolding NFA_construct_reachable_map_OK_def by simp

    from rm_q rm_eq have r_intro2: "qm.lookup (ff q) qm0 = Some r" 
      using invar_qm0_n
      unfolding state_map_\<alpha>_def state_map_invar_def
      using ff_OK [OF invar_q q_in_S] by (simp add: qm.correct)
    assume semI_eq: "sem i1 = sem i2" 
    from this semI_a_b 
      have semI_ab_noempty: "sem i2 \<noteq> {} \<and> sem i1 \<noteq> {} " 
        by auto
      from inj_semIs_aux semI_eq aq'_in_it aq''_in_it DS_OK0 it_subset
      have xayb: "i1 = i2" 
        by (metis case_prod_conv iv.inj_semIs_aux subset_iff)
    have "insert (r, i2, r') (d.\<alpha> D') = d.\<alpha> (d.add r i2 r' D') \<and>
          d.invar (d.add r i2 r' D')"
      by (metis d_add_OK invar_D' lts_add_def)
    from semI_ab_noempty inj_semI xayb this D0'_eq semI_eq show 
          "insert (the (state_map_\<alpha> (qm, n) (q2_\<alpha> q)), sem i2, r') 
            (ba_to_set `d.\<alpha> D') =
             ba_to_set ` d.\<alpha> (d.add (the (qm.lookup (ff q) qm0)) i1 r' D') \<and>
          d.invar (d.add (the (qm.lookup (ff q) qm0)) i1 r' D') \<and>
          q2_invar q''"   
      apply (simp add: r_intro1 r_intro2 invar_q'' )
      by (smt image_insert ba_to_set.simps)
  } 
qed


definition NFA_construct_reachable_ba_impl where
  "NFA_construct_reachable_ba_impl Sig S I FP DS  =
   do {
     let ((qm, n), Is) = NFA_construct_reachable_init_ba_impl I;
     (((qm, n), \<A>), _) \<leftarrow> WORKLISTT (\<lambda>_. True)
      (\<lambda>((qm, n), AA) q. 
         if (s.memb (the (qm.lookup (ff q) qm)) (nfa_states AA)) then
           (RETURN (((qm, n), AA), []))
         else                    
           do {
             ASSERT (q2_invar q \<and> q2_\<alpha> q \<in> S);
             ((qm', n'), DD', N) \<leftarrow> 
             NFA_construct_reachable_impl_step_ba DS qm n (nfa_trans AA) q;
             RETURN (((qm', n'), 
                 (s.ins_dj (the (qm.lookup (ff q) qm)) (nfa_states AA), (nfa_alphabet AA),
                   DD', nfa_initial AA, 
                  (if (FP q) then (s.ins_dj (the (qm.lookup (ff q) qm))) 
                    (nfa_accepting AA) else (nfa_accepting AA)))), N)
           }
        ) (((qm, n), (s.empty (), Sig, d.empty, Is, s.empty ())), I);
     RETURN \<A>
   }"



lemma NFA_construct_reachable_impl_correct :
fixes D II
defines "I \<equiv> map q2_\<alpha> II"
defines "R \<equiv> build_rel nfa_\<alpha> nfa_invar"
defines "R' \<equiv> build_rel state_map_\<alpha> state_map_invar"
defines "S \<equiv> accessible (LTS_forget_labels D) (set I)"
assumes f_inj_on: "inj_on f S"
    and Sig_cons: "Sig = sem SigI"
    and ff_OK: "\<And>q. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> S \<Longrightarrow> ff q = f (q2_\<alpha> q)" 
    and d_add_OK:
          "lts_add d.\<alpha> d.invar d.add"
    and dist_I: "distinct I"
    and invar_I: "\<And>q. q \<in> set II \<Longrightarrow> q2_invar q" 
    and DS_OK0: "\<And>q. (\<forall> (a, q') \<in> (DS q). canonical_op a)"
    and DS_OK1: "\<And>q. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> S \<Longrightarrow> 
                      inj_on q2_\<alpha> {q'| a q'. (a, q') \<in> (DS q)}"
    and DS_OK: "\<And>q. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> S \<Longrightarrow> 
       (DS q, {(a, q'). (q2_\<alpha> q, a, q') \<in> D}) 
        \<in> NFA_construct_reachable_impl_step_rel"
    and FFP_OK: "\<And>q. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> S \<Longrightarrow> FFP q \<longleftrightarrow> FP (q2_\<alpha> q)"
shows "NFA_construct_reachable_ba_impl SigI S II FFP DS \<le>
   \<Down> R (NFA_construct_reachable_abstract2_impl Sig I FP D)"
unfolding NFA_construct_reachable_ba_impl_def 
          NFA_construct_reachable_abstract2_impl_def 
          WORKLISTT_def
using [[goals_limit = 15]]
apply (refine_rcg)
(* preprocess goals
   initialisation is OK *)
  apply (unfold I_def)
  apply (rule NFA_construct_reachable_init_ba_impl_correct)
  apply (insert f_inj_on ff_OK dist_I invar_I)[4]
  apply (simp_all add: S_def I_def)[4]
  (* goal solved *)
  apply (subgoal_tac "single_valued (rprod R' R)")
  apply assumption
  apply (simp add: rprod_sv R'_def R_def del: rprod_def br_def)
  (* goal solved *)
  apply (subgoal_tac "single_valued (build_rel q2_\<alpha> q2_invar)")
  apply assumption
  apply (simp del: br_def)
  (* goal solved *)
  apply (simp add: br_def R'_def R_def nfa_invar_def 
          s.correct d.correct_common  nfa_\<alpha>_def Sig_cons)
  (* goal solved *)
  defer
  apply simp
  (* goal solved *)
  apply simp
  (* goal solved *)
  apply (clarify, simp add: br_def)+
  defer
  apply (simp add: rprod_sv R'_def R_def del: rprod_def br_def)
  (* goal solved *)
  apply (simp add: br_def)
  (* goal solved *)
  apply (simp add: br_def)
  (* goal solved *)
  apply (simp add: S_def I_def)
  (* goal solved *)
  defer
  defer
  apply (simp add: S_def I_def)
  apply (simp add: S_def I_def br_def)
  apply (simp add: invar_I list.rel_map(2) list.rel_refl_strong)
  apply (simp add: S_def I_def br_def R_def R'_def)
  defer
  (* goal solved
    -- "step OK *)
  apply (unfold I_def[symmetric])
  apply (clarify, simp)+ 
  apply (simp add: br_def)
  apply (unfold I_def)
  apply (rule_tac NFA_construct_reachable_impl_step_correct)
  apply (unfold I_def[symmetric])
  apply (simp_all add: nfa_invar_def f_inj_on[unfolded S_def] ff_OK[unfolded S_def] 
                       d_add_OK DS_OK[unfolded S_def] nfa_\<alpha>_def) [14] 
  (* goal solved *)
  apply (simp add: rprod_sv R'_def R_def  br_def)
  (* goal solved *)
  apply (simp add: R_def br_def R'_def)
  (* goal solved *)
  apply (clarify, simp  add: R_def br_def)+
  apply (unfold S_def[symmetric] nfa_accepting_def snd_conv)
  apply (simp add: br_def nfa_invar_def)
  apply (simp add: nfa_\<alpha>_def)
  apply (simp add: rprod_sv R'_def R_def  br_def nfa_\<alpha>_def nfa_invar_def)
  using DS_OK0
  apply (clarify, simp add: br_def )
  apply fastforce
  using DS_OK0 DS_OK1 apply force
  using DS_OK apply blast
  apply (clarify, simp add: br_def DS_OK R'_def)
  apply (clarify, simp add: br_def DS_OK R'_def)
  apply (clarify, simp add: br_def nfa_invar_def DS_OK R'_def)
  apply (rename_tac x1b x2a x2b q' \<A> qm n Qs i DD Is Fs x2g qm' n' D' x2j r)
  defer
  apply (rename_tac x1b x2a x2b q qm n Qs i DD Is Fs r)
proof -
  fix q rm \<A> qm n Qs i DD Is Fs r
  {
   assume rm_q: "state_map_\<alpha> (qm, n) (q2_\<alpha> q) = Some r" and
         in_R': "state_map_invar (qm, n)" and
         in_R: "nfa_invar (Qs, i, DD, Is, Fs)" and
         invar_q: "q2_invar q" and
         q_in: "q2_\<alpha> q \<in> accessible (LTS_forget_labels D) (q2_\<alpha> ` set II)"

  from q_in have q_in_S: "q2_\<alpha> q \<in> S" unfolding S_def I_def by simp

  from in_R' rm_q ff_OK[OF invar_q q_in_S] have "qm.lookup (ff q) qm = Some r"
    unfolding R'_def 
    by (simp add: state_map_invar_def state_map_\<alpha>_def qm.correct br_def)

  with in_R show "s.memb (the (qm.lookup (ff q) qm)) Qs = 
                (r \<in> \<Q> (nfa_\<alpha> (Qs, i, DD, Is, Fs)))"
    unfolding R_def 
    by (simp add: nfa_invar_def s.correct nfa_\<alpha>_def)
}
  {
  fix x3 x4 qm'' q' \<A> qm n Qs  DD Is Fs bga qm' n' D' bja r
  assume r_nin_Q: "r \<notin> \<Q> \<A>" and 
       rm_q': "state_map_\<alpha> (qm, n) (q2_\<alpha> q') = Some r" and
       weak_invar: "NFA_construct_reachable_abstract_impl_weak_invar 
             Sig I FP D
         (state_map_\<alpha> (qm, n), \<A>)" and
       invar_qm_n: "
       state_map_invar (qm', n')" and
       p1: "d.invar D'" and
       in_R: "((Qs, i, DD, Is, Fs), \<A>) \<in> R" and
       p2: "state_map_invar (qm, n)" and
       invar_q': "q2_invar q'" and 
       q'_in_S: "q2_\<alpha> q' \<in> S" and
       A_cons: "NFA_construct_reachable_abstract_impl_weak_invar Sig I FP D 
        (state_map_\<alpha> (qm, n), \<A>)"

  from A_cons NFA_construct_reachable_abstract_impl_weak_invar_def[of Sig I FP D]
  have "(\<lambda>(rm, \<A>).
       \<exists>s. NFA_construct_reachable_map_OK (accessible (LTS_forget_labels D) (set I)) Map.empty
            (s \<union> set I \<union> {q'. \<exists>a q. q \<in> s \<and> (q, a, q') \<in> D \<and> a \<noteq> {}}) rm \<and>
           s \<subseteq> accessible (LTS_forget_labels D) (set I) \<and>
           \<A> =
           NFA_rename_states
            \<lparr>\<Q> = s, \<Sigma> = Sig, \<Delta> = {qsq \<in> D. fst qsq \<in> s \<and> fst (snd qsq) \<noteq> {}}, \<I> = set I,
               \<F> = {q \<in> s. FP q}\<rparr>
            (the \<circ> rm)) (state_map_\<alpha> (qm, n), \<A>)" 
    by (simp add: NFA_construct_reachable_abstract_impl_weak_invar_def)
  from this
  obtain s where
  s_def: "\<A> =
           NFA_rename_states
            \<lparr>\<Q> = s, \<Sigma> = Sig, \<Delta> = {qsq \<in> D. fst qsq \<in> s \<and> fst (snd qsq) \<noteq> {}}, \<I> = set I,
               \<F> = {q \<in> s. FP q}\<rparr>
            (the \<circ> (state_map_\<alpha> (qm, n)))" 
    by auto
  from this NFA_rename_states_def[of \<A>]
  have "\<Sigma> \<A> = Sig" 
    by auto
  from this in_R R_def br_def
  have bgedsig: "sem i = Sig"
    apply simp
    unfolding br_def nfa_\<alpha>_def
    by simp

  from this rm_q' invar_qm_n ff_OK[OF invar_q' q'_in_S] 
      have qm_f_q': "qm.lookup (ff q') qm = Some r"
     unfolding state_map_\<alpha>_def state_map_invar_def 
     apply (simp add: qm.correct)
     using in_R p2 qm.lookup_correct state_map_invar_def by auto

   from in_R r_nin_Q have r_nin_Qs: "r \<notin> s.\<alpha> Qs" 
     by (simp add: R_def br_def nfa_\<alpha>_def)

  from weak_invar have "\<F> \<A> \<subseteq> \<Q> \<A>"
    unfolding NFA_construct_reachable_abstract_impl_weak_invar_def by auto
  with r_nin_Q have "r \<notin> \<F> \<A>" by auto
  with in_R have r_nin_Fs: "r \<notin> s.\<alpha> Fs" 
      by (simp add: R_def br_def nfa_\<alpha>_def)

  from in_R FFP_OK[OF invar_q' q'_in_S] bgedsig
  have "((s.ins_dj (the (qm.lookup (ff q') qm)) Qs, i, D', Is,
         if FFP q' then s.ins_dj (the (qm.lookup (ff q') qm)) 
          (snd (snd (snd ((Qs, DD, Is, Fs))))) else 
           (snd (snd (snd ((Qs,  DD, Is, Fs)))))),
        \<lparr>\<Q> = insert r (\<Q> \<A>), \<Sigma> = Sig, \<Delta> = ba_to_set ` d.\<alpha> D', \<I> = \<I> \<A>, 
           \<F> = if FP (q2_\<alpha> q') then insert 
           (the (state_map_\<alpha> (qm, n) (q2_\<alpha> q'))) (\<F> \<A>) else \<F> \<A>\<rparr>)
       \<in> R" 
    by (simp add: rm_q' qm_f_q' R_def nfa_\<alpha>_def p1
                nfa_invar_def invar_qm_n s.correct r_nin_Qs r_nin_Fs br_def Sig_cons)
    
  from this bgedsig 
  show "(FFP q' \<longrightarrow>
        (FP (q2_\<alpha> q') \<longrightarrow>
         ((s.ins_dj (the (qm.lookup (ff q') qm)) Qs, i, D', Is,
           s.ins_dj (the (qm.lookup (ff q') qm)) Fs),
          \<lparr>\<Q> = insert r (\<Q> \<A>), \<Sigma> = Sig, \<Delta> = ba_to_set ` d.\<alpha> D', \<I> = \<I> \<A>,
             \<F> = insert r (\<F> \<A>)\<rparr>)
         \<in> R) \<and>
        (\<not> FP (q2_\<alpha> q') \<longrightarrow>
         ((s.ins_dj (the (qm.lookup (ff q') qm)) Qs, i, D', Is,
           s.ins_dj (the (qm.lookup (ff q') qm)) Fs),
          \<lparr>\<Q> = insert r (\<Q> \<A>), \<Sigma> = Sig, \<Delta> = ba_to_set ` d.\<alpha> D', \<I> = \<I> \<A>, \<F> = \<F> \<A>\<rparr>)
         \<in> R)) \<and>
       (\<not> FFP q' \<longrightarrow>
        (FP (q2_\<alpha> q') \<longrightarrow>
         ((s.ins_dj (the (qm.lookup (ff q') qm)) Qs, i, D', Is, Fs),
          \<lparr>\<Q> = insert r (\<Q> \<A>), \<Sigma> = Sig, \<Delta> = ba_to_set ` d.\<alpha> D', \<I> = \<I> \<A>,
             \<F> = insert r (\<F> \<A>)\<rparr>)
         \<in> R) \<and>
        (\<not> FP (q2_\<alpha> q') \<longrightarrow>
         ((s.ins_dj (the (qm.lookup (ff q') qm)) Qs, i, D', Is, Fs),
          \<lparr>\<Q> = insert r (\<Q> \<A>), \<Sigma> = Sig, \<Delta> = ba_to_set ` d.\<alpha> D', \<I> = \<I> \<A>, \<F> = \<F> \<A>\<rparr>)
         \<in> R))"
    using rm_q' by auto
}
qed

lemma NFA_construct_reachable_ba_impl_alt_def :
  "NFA_construct_reachable_ba_impl Sig S I FP DS =
   do {
     let ((qm, n), Is) = NFA_construct_reachable_init_ba_impl I;
     ((_, \<A>), _) \<leftarrow> WORKLISTT (\<lambda>_. True)
      (\<lambda>((qm, n), (Qs, Sig, DD, Is, Fs)) q. do { 
         let r = the (qm.lookup (ff q) qm);
         if (s.memb r Qs) then
           (RETURN (((qm, n), (Qs, Sig, DD, Is, Fs)), []))
         else                    
           do {
             ASSERT (q2_invar q \<and> q2_\<alpha> q \<in> S);
             ((qm', n'), DD', N) \<leftarrow> NFA_construct_reachable_impl_step_ba 
                          DS qm n DD q;
             RETURN (((qm', n'), 
                 (s.ins_dj r Qs, Sig, 
                  DD', Is, 
                  (if (FP q) then (s.ins_dj r Fs) else Fs))), N)
           }
         }
        ) (((qm, n), (s.empty (), Sig, d.empty, Is, s.empty ())), I);
     RETURN \<A>
   }"
  unfolding NFA_construct_reachable_ba_impl_def
  apply (simp add: split_def)
  apply (unfold nfa_selectors_def fst_conv snd_conv prod.collapse)
  using nfa_alphabet_def by presburger



schematic_goal NFA_construct_reachable_ba_impl_code_aux: 
fixes D_it :: "'q2_rep \<Rightarrow> (('b \<times> 'q2_rep),
                     ('m \<times> nat) \<times> 'd \<times> 'q2_rep list) set_iterator"
assumes D_it_OK[rule_format, refine_transfer]: 
         "\<forall>q. q2_invar q \<longrightarrow> q2_\<alpha> q \<in> S \<longrightarrow> set_iterator (D_it q) 
          {p. p \<in> DS q}"
shows "RETURN ?f \<le> NFA_construct_reachable_ba_impl Sig S I FP DS"
 unfolding NFA_construct_reachable_ba_impl_alt_def 
 WORKLISTT_def NFA_construct_reachable_impl_step_ba_def iv.noempty_intervals_sem
 apply (unfold split_def snd_conv fst_conv prod.collapse)
 apply (rule refine_transfer | assumption  | erule conjE)+
done




definition (in automaton_by_lts_bool_algebra_defs) 
NFA_construct_reachable_ba_impl_code where
"NFA_construct_reachable_ba_impl_code 
 qm_ops (ff::'q2_rep \<Rightarrow> 'i) Sig I FP D_it =
(let ((qm, n), Is) = foldl (\<lambda>((qm, n), Is) q. 
         ((map_op_update_dj qm_ops (ff q) (states_enumerate n) qm, Suc n),
             s.ins_dj (states_enumerate n) Is))
                ((map_op_empty qm_ops (), 0), s.empty()) I;
     ((_, AA), _) = worklist (\<lambda>_. True)
        (\<lambda>((qm, n), Qs, Sig, DD, Is, Fs) (q::'q2_rep).
            let r = the (map_op_lookup qm_ops (ff q) qm)
            in if set_op_memb s_ops r Qs then (((qm, n), Qs, Sig, DD, Is, Fs), [])
               else let ((qm', n'), DD', N) = D_it q (\<lambda>_::(('m \<times> nat) \<times> 'd \<times> 'q2_rep list). True)
                           (\<lambda>(a, q') ((qm::'m, n::nat), DD'::'d, N::'q2_rep list).
                              if (noempty_op a) then
                               let r'_opt = map_op_lookup qm_ops (ff q') qm; 
                                   ((qm', n'), r') = if r'_opt = None then 
                                       let r'' = states_enumerate n in 
                                          ((map_op_update_dj qm_ops (ff q') r'' qm, Suc n), r'') 
                                      else ((qm, n), the r'_opt)
                               in ((qm', n'), clts_op_add d_ops r a r' DD', q' # N)
                              else ((qm, n), DD', N))
                           ((qm, n), DD, [])
                    in (((qm', n'), set_op_ins_dj s_ops r Qs, Sig, DD', Is, 
                    if FP q then set_op_ins_dj s_ops r Fs else Fs), N))
        (((qm, n), set_op_empty s_ops (), Sig,
   clts_op_empty d_ops, Is, set_op_empty s_ops ()), I)
 in AA)"



lemma NFA_construct_reachable_interval_impl_code_correct: 
fixes D_it :: "'q2_rep \<Rightarrow> (('b \<times> 'q2_rep),
                     ('m \<times> nat) \<times> 'd \<times> 'q2_rep list) set_iterator"
assumes D_it_OK: "\<forall> q. q2_invar q \<longrightarrow> q2_\<alpha> q \<in> S \<longrightarrow> 
                         set_iterator (D_it q) {p. p \<in> DS q}"
shows "RETURN (NFA_construct_reachable_ba_impl_code qm_ops ff Sig I FP D_it) \<le> 
               NFA_construct_reachable_ba_impl Sig S I FP DS"
proof -
  have rule: 
   "\<And>f1 f2. \<lbrakk>RETURN f1 \<le> NFA_construct_reachable_ba_impl Sig S I FP DS; f1 = f2\<rbrakk> \<Longrightarrow>
              RETURN f2 \<le> NFA_construct_reachable_ba_impl Sig S I FP DS" by simp
  
  note aux_thm = NFA_construct_reachable_ba_impl_code_aux[OF D_it_OK, of I FP]

  note rule' = rule[OF aux_thm]
  show ?thesis 
    apply (rule rule')
    apply (simp add: NFA_construct_reachable_ba_impl_code_def 
            split_def Let_def NFA_construct_reachable_init_ba_impl_def
               nempI_correct
                cong: if_cong)
    done
qed

lemma NFA_construct_reachable_interval_impl_code_correct_full: 
fixes D_it :: "'q2_rep \<Rightarrow> (('b \<times> 'q2_rep),('m \<times> nat) 
        \<times> 'd \<times> 'q2_rep list) set_iterator"
fixes II D DS Sig SigI
defines "S \<equiv> accessible (LTS_forget_labels D) (set (map q2_\<alpha> II))"
assumes f_inj_on: "inj_on f S"
    and ff_OK: "\<And>q. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> S \<Longrightarrow> ff q = f (q2_\<alpha> q)" 
    and sigsigi: "Sig = sem SigI"
    and d_add_OK: 
          "lts_add d.\<alpha> d.invar d.add"
    and dist_I: "distinct (map q2_\<alpha> II)"
    and invar_I: "\<And>q. q \<in> set II \<Longrightarrow> q2_invar q" 
    and fin_S: "finite S"
    and fin_D: "\<And>q. finite {(a, q'). (q, a, q') \<in> D}"
    and DS_OK0: "\<And>q. (\<forall> (a, q') \<in> (DS q). canonical_op a)"
    and DS_OK1: "\<And>q. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> S \<Longrightarrow> inj_on q2_\<alpha> {q'| a q'. (a, q') \<in> (DS q)}"
    and D_it_OK: "(\<And>q. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> S \<Longrightarrow> 
            (set_iterator_genord (D_it q) {p. p \<in> DS q} selP \<and>
             ((DS q), {(a, q'). (q2_\<alpha> q, a, q') \<in> D }) \<in> 
            NFA_construct_reachable_impl_step_rel))"
    and FFP_OK: "\<And>q. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> S \<Longrightarrow> FFP q \<longleftrightarrow> FP (q2_\<alpha> q)"
shows "NFA_isomorphic (NFA_construct_reachable Sig (set (map q2_\<alpha> II)) FP D)
    (nfa_\<alpha> (NFA_construct_reachable_ba_impl_code qm_ops ff SigI II FFP D_it)) \<and>
    nfa_invar (NFA_construct_reachable_ba_impl_code qm_ops ff SigI II FFP D_it)"
proof - 

  have fin_Ds: "(\<And>q. finite {(a, q'). (q, a, q') \<in> D \<and> a \<noteq> {}})"
  proof -
    fix q
    have "finite {(a, q'). (q, a, q') \<in> D}"
      by (simp add: fin_D)
    have "{(a, q'). (q, a, q') \<in> D \<and> a \<noteq> {}} \<subseteq> {(a, q'). (q, a, q') \<in> D}" by auto
    from this show "finite {(a, q'). (q, a, q') \<in> D \<and> a \<noteq> {}}"
      by (simp add: finite_subset fin_D)
  qed
  
  have D_it_OK'' : "\<forall>q. q2_invar q \<longrightarrow> q2_\<alpha> q \<in> S \<longrightarrow>
      set_iterator (D_it q) {p. p \<in> DS q}"
  proof (intro allI impI)
    fix q
    assume "q2_invar q" "q2_\<alpha> q \<in> S"
    with D_it_OK[of q] show
      "set_iterator (D_it q) {p. p \<in> DS q}"
      using set_iterator_intro by blast
    qed 
    thm NFA_construct_reachable_impl_correct[OF _ sigsigi]
  note NFA_construct_reachable_interval_impl_code_correct [OF D_it_OK'']
  also have "NFA_construct_reachable_ba_impl 
             SigI S II FFP DS \<le> \<Down> (build_rel nfa_\<alpha> nfa_invar)
     (NFA_construct_reachable_abstract2_impl Sig (map q2_\<alpha> II) FP D)"
    using NFA_construct_reachable_impl_correct 
        [OF f_inj_on[unfolded S_def] sigsigi ff_OK[unfolded S_def] d_add_OK
          dist_I invar_I, of DS FFP FP] FFP_OK S_def 
    apply (auto simp add: FFP_OK D_it_OK DS_OK0 DS_OK1)
    using DS_OK0 DS_OK1 by force
      also note NFA_construct_reachable_abstract2_impl_correct
  also note NFA_construct_reachable_abstract_impl_correct
  finally have "RETURN (NFA_construct_reachable_ba_impl_code 
            qm_ops ff SigI II FFP D_it) \<le> \<Down> (build_rel nfa_\<alpha> nfa_invar)
     (SPEC (NFA_isomorphic (NFA_construct_reachable 
        Sig (set (map q2_\<alpha> II)) FP D)))"
    using S_def fin_S fin_D
    by (simp add: S_def[symmetric] fin_S fin_Ds)
    
  thus ?thesis 
    by (erule_tac RETURN_ref_SPECD, simp add: br_def)
qed

lemma NFA_construct_reachable_interval_impl_code_correct___remove_unreachable: 
fixes D_it :: "'q2_rep \<Rightarrow> (('b \<times> 'q2_rep) , ('m \<times> nat) \<times> 'd \<times> 'q2_rep list) 
      set_iterator"
fixes II D DS Sig
assumes d_add_OK: 
  (* "\<forall>q a q' q''. (q, a, q') \<in> \<Delta> \<A> \<and> (q, a, q'') \<in> \<Delta> \<A> \<and> q'' \<noteq> q' \<longrightarrow> *)
          "lts_add d.\<alpha> d.invar d.add"
    and f_inj_on: "inj_on f (\<Q> \<A>)"
    and ff_OK: "\<And>q. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> (\<Q> \<A>) \<Longrightarrow> ff q = f (q2_\<alpha> q)" 
    and dist_I: "distinct (map q2_\<alpha> II)" 
    and invar_I: "\<And>q. q \<in> set II \<Longrightarrow> q2_invar q" 
    and I_OK: "set (map q2_\<alpha> II) = \<I> \<A>"
    and fin_D: "finite (\<Delta> \<A>)"
    and DS_OK0: "\<And>q. (\<forall> (a, q') \<in> (DS q). canonical_op a)"
    and DS_OK1: "\<And>q. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> (\<Q> \<A>) \<Longrightarrow>  inj_on q2_\<alpha> {q'| a q'. (a, q') \<in> (DS q)}"
    and D_it_OK: "\<And>q. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> \<Q> \<A> \<Longrightarrow>
                    set_iterator_genord (D_it q) {p. p \<in> DS q} selP \<and>
                    (DS q, {(a, q'). (q2_\<alpha> q, a, q') \<in> \<Delta> \<A>}) 
                    \<in> NFA_construct_reachable_impl_step_rel"
    and FP_OK: "\<And>q. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> \<Q> \<A> \<Longrightarrow> FP q \<longleftrightarrow> (q2_\<alpha> q) \<in> \<F> \<A>"
    and wf_\<A>: "NFA \<A>"
    and sig_\<Sigma>: "\<Sigma> \<A> = sem Sig"
  shows "nfa_invar (NFA_construct_reachable_ba_impl_code qm_ops ff Sig II FP D_it) \<and>
         NFA (nfa_\<alpha> (NFA_construct_reachable_ba_impl_code qm_ops ff Sig II FP D_it)) \<and>
         NFA_isomorphic_wf (nfa_\<alpha> (NFA_construct_reachable_ba_impl_code 
                                qm_ops ff Sig II FP D_it))
                         (NFA_remove_unreachable_states \<A>)"
proof -
 find_theorems name: "is_reachable_from_initial_subset"
  interpret NFA \<A> by fact
  let ?S = "accessible (LTS_forget_labels (\<Delta> \<A>)) (set (map q2_\<alpha> II))"
  from LTS_is_reachable_from_initial_finite I_OK have fin_S: "finite ?S" by simp
  from LTS_is_reachable_from_initial_subset I_OK have S_subset: "?S \<subseteq> \<Q> \<A>" by simp
  from f_inj_on S_subset have f_inj_on': "inj_on f ?S" by (rule subset_inj_on)

  { fix q
    have "{(a, q'). (q, a, q') \<in> \<Delta> \<A>} = 
           (\<lambda>(q,a,q'). (a,q')) ` {(q, a, q') | a q'. (q, a, q') \<in> \<Delta> \<A>}"
      by (auto simp add: image_iff)
    hence "finite {(a, q'). (q, a, q') \<in> \<Delta> \<A>}"
      apply simp
      apply (rule finite_imageI)
      apply (rule finite_subset [OF _ fin_D])
      apply auto
    done
  } note fin_D = this

 
  let ?FP = "\<lambda>q. q \<in> \<F> \<A>"
  let ?I = "map q2_\<alpha> II"
  thm NFA_construct_reachable_interval_impl_code_correct_full
  from NFA_construct_reachable_interval_impl_code_correct_full 
        [OF f_inj_on' ff_OK sig_\<Sigma> d_add_OK dist_I invar_I
         fin_S, where ?FP = ?FP and ?D_it=D_it and selP=selP, 
         OF _ _ _ fin_D DS_OK0 DS_OK1 D_it_OK FP_OK] 
         S_subset 
  have step1:
    "NFA_isomorphic (NFA_construct_reachable (\<Sigma> \<A>) (set ?I) ?FP (\<Delta> \<A>))
      (nfa_\<alpha> (NFA_construct_reachable_ba_impl_code qm_ops ff Sig II FP D_it))"
    "nfa_invar (NFA_construct_reachable_ba_impl_code qm_ops ff Sig II FP D_it)" 
      by (simp_all add: subset_iff)
 
  from NFA.NFA_remove_unreachable_states_implementation 
            [OF wf_\<A> I_OK, of "?FP" "\<Delta> \<A>"]
  have step2: "NFA_construct_reachable (\<Sigma> \<A>) (set ?I)
           ?FP (\<Delta> \<A>) = NFA_remove_unreachable_states \<A>" 
    by simp
 
  from step1(1) step2 NFA_remove_unreachable_states___is_well_formed [OF wf_\<A>] have 
    step3: "NFA_isomorphic_wf (NFA_remove_unreachable_states \<A>) 
                       (nfa_\<alpha> (NFA_construct_reachable_ba_impl_code 
                        qm_ops ff Sig II FP D_it))"
    by (simp add: NFA_isomorphic_wf_def)

  from step3 have step4: "NFA (nfa_\<alpha> 
        (NFA_construct_reachable_ba_impl_code qm_ops ff Sig II FP D_it))"
    unfolding NFA_isomorphic_wf_alt_def by simp

  from step3 step1(2) step4 show ?thesis
    using NFA_isomorphic_wf_sym
    by blast
qed

end


context nfa_dfa_by_lts_bool_algebra_defs 
begin

end

subsection \<open> determinise \<close>

definition determinise_next_state :: 
  "('q, 'q_set, _) set_ops_scheme \<Rightarrow> ('q,'q_set) set_iterator \<Rightarrow> 
   ('q \<Rightarrow> ('q,'q_set) set_iterator) \<Rightarrow> 'q_set" where
  "determinise_next_state s_ops it_S it_D =
   (set_iterator_product it_S it_D) (\<lambda>_. True) (\<lambda>(_,q') S. 
   set_op_ins s_ops q' S) (set_op_empty s_ops ())"


schematic_goal determinise_next_state_code :
   "determinise_next_state s_ops it_S it_D = ?XXXX"
unfolding determinise_next_state_def set_iterator_product_def
by (rule refl)+

lemma determinise_next_state_correct :
assumes s_ops_OK: "StdSet s_ops" 
    and it_S_OK: "set_iterator it_S S"
    and it_D_OK: "\<And>q. set_iterator (it_D q) {q'. (q, a, q') \<in> D}"
shows "set_op_invar s_ops (determinise_next_state s_ops it_S it_D) \<and>
       set_op_\<alpha> s_ops (determinise_next_state s_ops it_S it_D) = 
        {q' . \<exists>q. q \<in> S \<and> (q, a, q') \<in> D}"
proof -
  interpret s: StdSet s_ops by fact
  
  have "(SIGMA aa:S. {q'. (aa, a, q') \<in> D}) = {(q, q') . q \<in> S \<and> (q, a, q') \<in> D}" by auto
  with set_iterator_product_correct[where it_a = it_S and it_b = it_D,
                                            OF it_S_OK it_D_OK]
  have comb_OK: "set_iterator (set_iterator_product it_S it_D)
     {(q, q') . q \<in> S \<and> (q, a, q') \<in> D}" by simp

  have res_eq: "{q' . \<exists>q. q \<in> S \<and> (q, a, q') \<in> D} = snd ` {(q, q') . q \<in> S \<and> (q, a, q') \<in> D}"
    by (auto simp add: image_iff)
  thm set_iterator_no_cond_rule_insert_P[OF comb_OK,
                of "\<lambda>S \<sigma>. s.invar \<sigma> \<and> s.\<alpha> \<sigma> = snd ` S"]
  show ?thesis
    unfolding determinise_next_state_def res_eq
    apply (rule set_iterator_no_cond_rule_insert_P[OF comb_OK,
                of "\<lambda>S \<sigma>. s.invar \<sigma> \<and> s.\<alpha> \<sigma> = snd ` S"])
    by (auto simp add: s.correct image_iff Ball_def)
qed


definition determinise_iterator where
"determinise_iterator s_ops it_A it_S it_D =
 set_iterator_image_filter 
   (\<lambda>a. let nq = determinise_next_state s_ops it_S (\<lambda>q. it_D q a) in 
        (if \<not> (set_op_isEmpty s_ops nq) then 
          Some (a, nq)
         else None)) it_A"

lemma determinise_iterator_code :
   "determinise_iterator s_ops it_A it_S it_D = 
    (\<lambda>c f. it_A c (\<lambda>x \<sigma>. let np = it_S (\<lambda>_. True) (\<lambda>a. it_D a x (\<lambda>_. True)
       (set_op_ins s_ops)) (set_op_empty s_ops ()) in 
        if (\<not> (set_op_isEmpty s_ops np)) then f (x, np) \<sigma> else \<sigma>))"
proof -
  have eqa: "\<And> f. (\<lambda>x \<sigma>. case if (set_op_isEmpty s_ops (it_S (\<lambda>_. True) (\<lambda>a. it_D a x (\<lambda>_. True) 
                            (set_op_ins s_ops))
                            (set_op_empty s_ops ())))
                        then None
                        else Some
                              (x, it_S (\<lambda>_. True)
                                   (\<lambda>a. it_D a x (\<lambda>_. True) (set_op_ins s_ops))
                                   (set_op_empty s_ops ())) of
                   None \<Rightarrow> \<sigma> | Some x' \<Rightarrow> f x' \<sigma>) = 
              (\<lambda>x \<sigma>. if (set_op_isEmpty s_ops (it_S (\<lambda>_. True) (\<lambda>a. it_D a x (\<lambda>_. True) (set_op_ins s_ops))
                            (set_op_empty s_ops ()))) then \<sigma> else f (x, it_S (\<lambda>_. True)
                                   (\<lambda>a. it_D a x (\<lambda>_. True) (set_op_ins s_ops))
                                   (set_op_empty s_ops ())) \<sigma>)"
    by auto
  thus ?thesis 
    unfolding determinise_iterator_def 
              set_iterator_filter_def
              determinise_next_state_code 
              set_iterator_image_filter_def[abs_def]
    apply simp
    unfolding eqa           
    by simp
qed


lemma determinise_iterator_correct :
fixes D :: "('q \<times> 'b \<times> 'q) set"
assumes it_A_OK: "set_iterator it_A A"
shows "set_iterator (determinise_iterator s_ops it_A it_S it_D) 
        {x. x \<in> ((\<lambda>a. (a, determinise_next_state s_ops it_S (\<lambda>q. it_D q a))) ` A)
             \<and> \<not> (set_op_isEmpty s_ops (snd x))}"
  unfolding determinise_iterator_def
  thm set_iterator_image_filter_correct
  thm set_iterator_image_filter_correct [of it_A A 
            "(\<lambda>a. let nq = determinise_next_state s_ops it_S (\<lambda>q. it_D q a)
             in if \<not> (set_op_isEmpty s_ops nq) then Some (a, nq) else None)"]
proof -
  have eqS: "{y. \<exists>x. x \<in> A \<and>
         (let nq = determinise_next_state s_ops it_S (\<lambda>q. it_D q x)
          in if \<not> (set_op_isEmpty s_ops nq) then Some (x, nq) else None) =
         Some y} = {x \<in> (\<lambda>a. (a, determinise_next_state s_ops it_S (\<lambda>q. it_D q a))) ` A. 
          \<not> (set_op_isEmpty s_ops (snd x))} "
    by force
  from this  set_iterator_image_filter_correct [of it_A A 
            "(\<lambda>a. let nq = determinise_next_state s_ops it_S (\<lambda>q. it_D q a)
             in if \<not> (set_op_isEmpty s_ops nq) then Some (a, nq) else None)"]
  have iterator1: "set_iterator it_A A \<Longrightarrow> inj_on
        (\<lambda>a. let nq = determinise_next_state s_ops it_S (\<lambda>q. it_D q a)
           in if \<not> (set_op_isEmpty s_ops nq) then Some (a, nq) else None)
         (A \<inter> dom (\<lambda>a. let nq = determinise_next_state s_ops it_S (\<lambda>q. it_D q a)
           in if \<not> (set_op_isEmpty s_ops nq) then Some (a, nq) else None)) \<Longrightarrow>
          set_iterator
           (set_iterator_image_filter
             (\<lambda>a. let nq = determinise_next_state s_ops it_S (\<lambda>q. it_D q a)
                  in if \<not> (set_op_isEmpty s_ops nq) then Some (a, nq) else None)
             it_A)
           {x \<in> (\<lambda>a. (a, determinise_next_state s_ops it_S (\<lambda>q. it_D q a))) ` A. 
                    \<not> (set_op_isEmpty s_ops (snd x))}" 
    unfolding eqS by simp
  show "set_iterator
     (set_iterator_image_filter
       (\<lambda>a. let nq = determinise_next_state s_ops it_S (\<lambda>q. it_D q a)
            in if \<not> (set_op_isEmpty s_ops nq) then Some (a, nq) else None)
       it_A)
     {x \<in> (\<lambda>a. (a, determinise_next_state s_ops it_S (\<lambda>q. it_D q a))) ` A. 
            \<not> (set_op_isEmpty s_ops (snd x))}"
    apply (rule iterator1)
    using it_A_OK apply simp
    by (smt IntD2 domIff inj_on_def option.inject prod.inject)
qed


definition determinise_impl_aux where
"determinise_impl_aux const s_ops ff it_A it_D it_S I A FP =
 (\<lambda>AA. const (ff AA) (A AA) [I AA] 
          (FP AA) (\<lambda>S. determinise_iterator s_ops (it_A AA) (it_S S) (it_D AA)))"



lemma (in automaton_by_lts_bool_algebra_syntax) dfa_by_map_correct2 [simp]: 
    "nfa nfa_\<alpha> nfa_invar_DFA"    
  unfolding nfa_def nfa_invar_NFA_def DFA_alt_def 
  by (simp add: nfa_invar_DFA_def)



lemma  (in automaton_by_lts_bool_algebra_syntax) determinise_impl_aux_correct :
fixes ss_ops :: "('q::{NFA_states}, 'q_set, _) set_ops_scheme" 
  and \<alpha> :: "'q_set \<times> 'b \<times> 'd \<times> 'q_set \<times> 'q_set \<Rightarrow> ('q, 'a ) NFA_rec"
  and q_\<alpha> :: "'q_set \<Rightarrow> 'q set"
  and q_invar :: "'q_set \<Rightarrow> bool"
assumes const_OK: "dfa_construct 
     nfa_\<alpha> nfa_invar_DFA (set_op_\<alpha> ss_ops) (set_op_invar ss_ops) 
      const sem canonical_op"
    and nfa_OK: "nfa \<alpha> invar"
    and ss_ops_OK: "StdSet ss_ops"
    and FP_OK: "\<And>n q. invar n \<Longrightarrow> set_op_invar ss_ops q \<Longrightarrow>
                set_op_\<alpha> ss_ops q \<subseteq> \<Q> (\<alpha> n) \<Longrightarrow> FP n q = (set_op_\<alpha> ss_ops q \<inter> \<F> (\<alpha> n) \<noteq> {})"
    and I_OK: "\<And>n. invar n \<Longrightarrow> set_op_invar ss_ops (I n) \<and> 
                               set_op_\<alpha> ss_ops (I n) = \<I> (\<alpha> n)"
    and I_nempty: "\<And>n. invar n \<Longrightarrow> set_op_invar ss_ops (I n) \<and> 
                               set_op_\<alpha> ss_ops (I n) \<noteq> {}"
    and inj_setop: "\<And> S. (\<forall> q \<in> S. set_op_invar ss_ops q) \<longrightarrow> 
                          inj_on (set_op_\<alpha> ss_ops) S"
    and A_OK: "\<And>n. invar n \<Longrightarrow> sem (A n) = \<Sigma> (\<alpha> n)"
    and A_OK': "\<And>n. invar n \<Longrightarrow> canonical_op (A n)"
    and L_OK: "\<And>n. invar n \<Longrightarrow> {(q, sem a, q') | q a q'. (q, a, q') \<in> (T n)} = 
                                \<Delta> (\<alpha> n)"
    and finite_\<Delta>: "\<And> n. invar n \<Longrightarrow> finite (\<Delta> (\<alpha> n))"
    and it_A_OK: "\<And>n. invar n \<Longrightarrow> set_iterator (it_A n) 
                                        {a| q a q'. (q, a, q') \<in> (T n)}"
    and it_S_OK: "\<And>S. set_op_invar ss_ops S \<Longrightarrow> 
                       set_iterator (it_S S) (set_op_\<alpha> ss_ops S)"
    and it_D_OK: "\<And>n q a. invar n \<Longrightarrow> a \<in> {a |q a q'. (q, a, q') \<in> (T n)} 
                        \<Longrightarrow>
                           set_iterator (it_D n q a) {q'. (q, a, q') \<in> (T n)}"
    and ff_OK: "\<And>n. invar n \<Longrightarrow> 
        (\<exists>f. inj_on f {q. q \<subseteq> \<Q> (\<alpha> n)} \<and>
            (\<forall>q. set_op_invar ss_ops q \<and> set_op_\<alpha> ss_ops q \<subseteq> \<Q> (\<alpha> n) 
               \<longrightarrow> ff n q = f (set_op_\<alpha> ss_ops q)))" 
  shows "nfa_determinise \<alpha> invar nfa_\<alpha> nfa_invar_DFA T sem
         canonical_op intersect_op empty_op 
        (determinise_impl_aux const ss_ops ff it_A it_D it_S I A FP)"
proof (intro nfa_determinise.intro nfa_OK dfa_by_map_correct2 nfa_determinise_axioms.intro)
  fix n
  assume invar_n: "invar n"
     and labels_OK1: "\<forall>(q, a, q')\<in>T n. canonical_op a"
     and labels_OK2: "\<forall>(q1, a1, q1')\<in>T n.
            \<forall>(q2, a2, q2')\<in>T n. a1 \<noteq> a2 \<longrightarrow> empty_op (intersect_op a1 a2)"
     and T_OK: "\<forall>(q, a, q')\<in>T n. sem a \<noteq> {}"
    
  let ?AA' = "determinise_NFA (\<alpha> n)"
  let ?D_it = "\<lambda>S. determinise_iterator ss_ops (it_A n) (it_S S) (it_D n)"

  have "\<And> a1 a2. set_op_invar ss_ops a1 \<and> set_op_invar ss_ops a2
                 \<Longrightarrow> (set_op_equal ss_ops a1 a2 \<longleftrightarrow> ((set_op_\<alpha> ss_ops a1) = (set_op_\<alpha> ss_ops a2)))"
    by (simp add: StdSet.correct(29) ss_ops_OK)

  have uniq_label_n: "uniq_label_NFA (\<alpha> n)"
    unfolding uniq_label_NFA_def 
    apply (rule_tac allI impI)+
  proof -
    fix q1 \<alpha>1 q1' q2 \<alpha>2 q2'
    assume in\<Delta>: "(q1, \<alpha>1, q1') \<in> \<Delta> (\<alpha> n) \<and>
                  (q2, \<alpha>2, q2') \<in> \<Delta> (\<alpha> n)"

    from in\<Delta> 
    have "(q1, \<alpha>1, q1') \<in> NFA_rec.\<Delta> (\<alpha> n)" by auto
    
    from this L_OK[OF invar_n]
    have "(q1, \<alpha>1, q1') \<in> {(q, sem a, q') |q a q'. (q, a, q') \<in> T n}"
      by auto
    from this
    obtain \<alpha>1I where \<alpha>1I_def: "(q1, \<alpha>1I, q1') \<in> T n \<and> 
                               (q1, sem \<alpha>1I, q1') = (q1, \<alpha>1, q1')"
      by blast

    from in\<Delta> 
    have "(q2, \<alpha>2, q2') \<in> NFA_rec.\<Delta> (\<alpha> n)" by auto
    
    from this L_OK[OF invar_n]
    have "(q2, \<alpha>2, q2') \<in> {(q, sem a, q') |q a q'. (q, a, q') \<in> T n}"
      by auto
    from this
    obtain \<alpha>2I where \<alpha>2I_def: "(q2, \<alpha>2I, q2') \<in> T n \<and> 
                               (q2, sem \<alpha>2I, q2') = (q2, \<alpha>2, q2')"
      by blast

    from \<alpha>1I_def \<alpha>2I_def
    show "\<alpha>1 = \<alpha>2 \<or> \<alpha>1 \<inter> \<alpha>2 = {}"
    proof (cases "\<alpha>1I = \<alpha>2I")
      case True
      from this \<alpha>1I_def \<alpha>2I_def
      have "\<alpha>1 = \<alpha>2" by force
      from this
      show ?thesis by simp
    next
      case False
      from this labels_OK1 labels_OK2
      have "canonical_op \<alpha>1I \<and> canonical_op \<alpha>2I" 
        using \<alpha>1I_def \<alpha>2I_def by auto
      from this False labels_OK2
      have "empty_op (intersect_op \<alpha>1I \<alpha>2I)"
        using \<alpha>1I_def \<alpha>2I_def by auto
      from this 
      have "sem \<alpha>1I \<inter> sem \<alpha>2I = {}"
        by (simp add: \<open>canonical_op \<alpha>1I \<and> canonical_op \<alpha>2I\<close> iv.empty_interval_sem
            iv.intersect_intervals_sem)
      from this \<alpha>1I_def \<alpha>2I_def
      show ?thesis by auto
    qed
  qed

  from I_OK[of n] I_nempty[of n]
  have "\<I> (\<alpha> n) \<noteq> {}" 
    using invar_n by blast

  from invar_n nfa_OK this uniq_label_n
  have AA'_wf: "weak_DFA ?AA'"
    apply (rule_tac determinise_NFA___DFA)
    apply (simp add: nfa_def) 
    by (metis prod_cases5)

  let ?DS' = "\<lambda> q. {x \<in> ((\<lambda>a. (a, determinise_next_state ss_ops (it_S q) (\<lambda>q. it_D n q a))) `
               {a. \<exists>q q'. (q, a, q') \<in> T n}).  \<not> (set_op_isEmpty ss_ops (snd x))}"

  
  
    { fix a q
      assume a_in: "a \<in> {a | q a q'. (q, a, q') \<in> T n}"
         and invar_q: "set_op_invar ss_ops q"
      note it_S_OK' = it_S_OK [OF invar_q]
      from determinise_next_state_correct [OF ss_ops_OK it_S_OK', of "\<lambda>q. it_D n q a" a, OF it_D_OK,
          OF invar_n a_in]
      have "set_op_invar ss_ops 
            (determinise_next_state ss_ops (it_S q) (\<lambda>q. it_D n q a))"
           "set_op_\<alpha> ss_ops (determinise_next_state ss_ops (it_S q) (\<lambda>q. it_D n q a)) =
            {q'. \<exists>qa. qa \<in> set_op_\<alpha> ss_ops q \<and> (qa, a, q') \<in> T n}" by simp_all
    } note det_next_state_eval = this


  { fix q
    assume invar_q: "set_op_invar ss_ops q"
       and q_subset: "set_op_\<alpha> ss_ops q \<in> \<Q> (determinise_NFA (\<alpha> n))"

    from q_subset
    have q_nempty: "set_op_\<alpha> ss_ops q \<noteq> {}"
      unfolding determinise_NFA_def
      by simp

    
 
    let ?DS = "{x \<in> ((\<lambda>a. (a, determinise_next_state ss_ops (it_S q) (\<lambda>q. it_D n q a))) `
               {a. \<exists>q q'. (q, a, q') \<in> T n}).  \<not> (set_op_isEmpty ss_ops (snd x))}"

    
   
    from determinise_iterator_correct 
          [OF it_A_OK, OF invar_n, of ss_ops "it_S q" "it_D n"]
    have D_it_OK: "set_iterator (?D_it q) ?DS" 
      by auto
  
    note it_S_OK' = it_S_OK [OF invar_q]
 
    { fix a
      assume a_in: "a \<in> {a | q a q'. (q, a, q') \<in> T n}"
      from determinise_next_state_correct [OF ss_ops_OK it_S_OK', of "\<lambda>q. it_D n q a" a, OF it_D_OK,
          OF invar_n a_in]
      have "set_op_invar ss_ops 
            (determinise_next_state ss_ops (it_S q) (\<lambda>q. it_D n q a))"
           "set_op_\<alpha> ss_ops (determinise_next_state ss_ops (it_S q) (\<lambda>q. it_D n q a)) =
            {q'. \<exists>qa. qa \<in> set_op_\<alpha> ss_ops q \<and> (qa, a, q') \<in> T n}" by simp_all
    } note det_next_state_eval = this

    have "set_iterator 
             (determinise_iterator ss_ops (it_A n) (it_S q) (it_D n)) (?DS' q) \<and>
              {(a, q'). (set_op_\<alpha> ss_ops q, a, q') \<in> \<Delta> (determinise_NFA (\<alpha> n))} =
              (\<lambda>(a, q'). (sem a, set_op_\<alpha> ss_ops q')) ` (?DS' q) \<and>
              (\<forall>a q'. (a, q') \<in> (?DS' q) \<longrightarrow> set_op_invar ss_ops q') \<and>
              (\<forall>a q'. (a, q') \<in> (?DS' q) \<longrightarrow>
                      (\<forall>q''. (a, q'') \<in> (?DS' q) \<longrightarrow>
                             (set_op_\<alpha> ss_ops q' = set_op_\<alpha> ss_ops q'') = (q' = q'')))" 
      apply (simp add: D_it_OK image_iff det_next_state_eval)
      apply (rule conjI)
      using D_it_OK 
      apply (subgoal_tac "{x \<in> (\<lambda>a. (a, determinise_next_state ss_ops (it_S q) (\<lambda>q. it_D n q a))) `
         {a. \<exists>q q'. (q, a, q') \<in> T n}.
    \<not> set_op_isEmpty ss_ops (snd x)} = {DS_q.
      (\<exists>x. (\<exists>q q'. (q, x, q') \<in> T n) \<and>
           DS_q = (x, determinise_next_state ss_ops (it_S q) (\<lambda>q. it_D n q x))) \<and>
      \<not> set_op_isEmpty ss_ops (snd DS_q)}")
        apply force
      apply blast
      apply (rule set_eqI)
      apply (insert q_subset)
      apply (auto simp add: image_iff det_next_state_eval)
      defer
      unfolding determinise_NFA_def
      apply simp
      apply (rule_tac conjI)
      using L_OK[OF invar_n] q_nempty
      apply auto[1] 
      defer
      defer
      using T_OK q_nempty
      apply (rule_tac conjI)
      using q_nempty apply simp
      apply (rule_tac conjI)
      defer
      using T_OK
      apply simp
      apply blast
      apply (simp add: determinise_NFA_def)
    proof -
      {
        fix a x
        assume p1: "set_op_\<alpha> ss_ops q \<noteq> {} \<and>
       (\<exists>qa. qa \<in> set_op_\<alpha> ss_ops q \<and>
             (\<exists>q'. (qa, a, q') \<in> \<Delta> (\<alpha> n))) \<and>
       a \<noteq> {}"
        from p1
        obtain qa q' where
        qaq'_def: "qa \<in> set_op_\<alpha> ss_ops q \<and> 
                    (qa, a, q') \<in> \<Delta> (\<alpha> n)"
          by auto
        from this L_OK[OF invar_n]
        have "(qa, a, q') \<in> {(q, sem a, q') |q a q'. (q, a, q') \<in> T n}"
          by simp
        from this
        have "\<exists> ai. (qa, ai, q') \<in> T n \<and> sem ai = a"
          by blast

        from this obtain ai where
        ai_def: "(qa, ai, q') \<in> T n \<and> sem ai = a"  
          by blast
        from this
        have c1: "(\<exists>q q'. (q, ai, q') \<in> T n) \<and>
           a = sem ai \<and>
           {q'. \<exists>q\<in>set_op_\<alpha> ss_ops q. (q, a, q') \<in>\<Delta> (\<alpha> n)} =
           {q'. \<exists>qa. qa \<in> set_op_\<alpha> ss_ops q \<and> (qa, ai, q') \<in> T n}"
          apply (rule_tac conjI)
          using ai_def apply force
          apply (rule_tac conjI)
          using ai_def apply force
          using L_OK[OF invar_n]
          apply auto
          using qaq'_def
        proof -
          {
            fix x qb
            assume p1: "qb \<in> set_op_\<alpha> ss_ops q"
               and p2: "(qb, sem ai, x) \<in> \<Delta> (\<alpha> n)"

            from p2 L_OK[OF invar_n] 
            have "\<exists> a1. (qb, a1, x) \<in> T n \<and> sem a1 = sem ai"
              by blast
            from this
            obtain a1 where a1_def:
            "(qb, a1, x) \<in> T n \<and> sem a1 = sem ai" by auto
            from this labels_OK1
            have "(qb, ai, x) \<in> T n" 
              by (metis ai_def iv.inj_semIs_aux old.prod.case)
            from this  p1
            show "\<exists>qa. qa \<in> set_op_\<alpha> ss_ops q \<and> (qa, ai, x) \<in> T n" by auto
          }
          {
            fix x qaa
            show "{(q, sem a, q') |q a q'. (q, a, q') \<in> T n} = 
                  \<Delta> (\<alpha> n) \<Longrightarrow>
       (qa, ai, q') \<in> T n \<Longrightarrow>
       a = sem ai \<Longrightarrow>
       qaa \<in> set_op_\<alpha> ss_ops q \<Longrightarrow>
       (qaa, ai, x) \<in> T n \<Longrightarrow>
       qa \<in> set_op_\<alpha> ss_ops q \<and> (qa, a, q') \<in> \<Delta> (\<alpha> n) \<Longrightarrow>
       \<exists>q\<in>set_op_\<alpha> ss_ops q. (q, sem ai, x) \<in> \<Delta> (\<alpha> n)"
              by blast
          }
        qed
        from this 
        have c4: "{q'. \<exists>qa. qa \<in> set_op_\<alpha> ss_ops q \<and> (qa, ai, q') \<in> T n} \<noteq> {}"
          using qaq'_def by blast
        from c1 det_next_state_eval(2)[of ai]
        have c3: "set_op_\<alpha> ss_ops (determinise_next_state ss_ops (it_S q) (\<lambda>q. it_D n q ai)) =
              {q'. \<exists>qa. qa \<in> set_op_\<alpha> ss_ops q \<and> (qa, ai, q') \<in> T n}"
          by force
        from c1 det_next_state_eval(1)[of ai]
        have c2: "set_op_invar ss_ops (determinise_next_state 
                ss_ops (it_S q) (\<lambda>q. it_D n q ai))"
          by force

        from c4 c2 c3
        have "\<not> set_op_isEmpty ss_ops ( 
              (determinise_next_state ss_ops (it_S q) 
              (\<lambda>q. it_D n q ai)))"
          by (simp add: StdSet.correct(12) ss_ops_OK)

        from this c1
        show "\<exists>aa. (\<exists>q q'. (q, aa, q') \<in> T n) \<and>
            \<not> set_op_isEmpty ss_ops
                (determinise_next_state ss_ops (it_S q) (\<lambda>q. it_D n q aa)) \<and>
            a = sem aa \<and>
            {q'. \<exists>q\<in>set_op_\<alpha> ss_ops q. (q, a, q') \<in> \<Delta> (\<alpha> n)} =
            set_op_\<alpha> ss_ops (determinise_next_state ss_ops (it_S q) (\<lambda>q. it_D n q aa))"
          using c3 by fastforce
      }
      {
        fix x aa qa q' xa xb
        assume p1: "(qa, aa, q') \<in> T n"
           and p2: "xb \<in> set_op_\<alpha> ss_ops 
                (determinise_next_state ss_ops (it_S q) (\<lambda>q. it_D n q aa))"
        from  p1 det_next_state_eval(2)[of aa]
        have "set_op_\<alpha> ss_ops (determinise_next_state ss_ops (it_S q) (\<lambda>q. it_D n q aa)) =
             {q'. \<exists>qa. qa \<in> set_op_\<alpha> ss_ops q \<and> (qa, aa, q') \<in> T n}"
          by force
        from this p2
        have "xb \<in> {q'. \<exists>qa. qa \<in> set_op_\<alpha> ss_ops q \<and> (qa, aa, q') \<in> T n}"
          by blast
        from this L_OK[OF invar_n]
        show "\<exists>q\<in>set_op_\<alpha> ss_ops q. (q, sem aa, xb) \<in> \<Delta> (\<alpha> n)"
          by blast
      }
      {
        fix x aa qa q' xa xb qaa
        assume p1: "qaa \<in> set_op_\<alpha> ss_ops q"
           and p2: "(qaa, sem aa, xb) \<in> \<Delta> (\<alpha> n)"
           and p3: "(qa, aa, q') \<in> T n"
           and p4: "qaa \<in> set_op_\<alpha> ss_ops q"
        from  p3 det_next_state_eval(2)[of aa]
        have c1: "set_op_\<alpha> ss_ops (determinise_next_state ss_ops (it_S q) (\<lambda>q. it_D n q aa)) = 
              {q'. \<exists>qa. qa \<in> set_op_\<alpha> ss_ops q \<and> (qa, aa, q') \<in> T n}"
          by force
        from L_OK[OF invar_n] p2
        have "(qaa, sem aa, xb) \<in> {(q, sem a, q') |q a q'. (q, a, q') \<in> T n}"
          by auto

        from this obtain aa1 where 
        aa1_def: "(qaa, aa1, xb) \<in> T n \<and> sem aa1 = sem aa" by auto
        from aa1_def p3 labels_OK1
        have "aa = aa1"
          by (metis iv.inj_semIs_aux old.prod.case)
        from this aa1_def 
        have "(qaa, aa, xb) \<in> T n" 
          by auto
        from this p1
        have "xb \<in> {q'. \<exists>qa. qa \<in> set_op_\<alpha> ss_ops q \<and> (qa, aa, q') \<in> T n}"
          by auto
        from this c1
        show "xb \<in> set_op_\<alpha> ss_ops (determinise_next_state ss_ops (it_S q) 
                                        (\<lambda>q. it_D n q aa))"
          by auto
      }
      {
        fix x aa qa q'
        assume p1: "(qa, aa, q') \<in> T n"
           and p2: "\<not> set_op_isEmpty ss_ops
                    (determinise_next_state ss_ops (it_S q) (\<lambda>q. it_D n q aa))"
        from p1 det_next_state_eval(2)[of aa]
        have c1: "set_op_\<alpha> ss_ops (determinise_next_state ss_ops (it_S q) (\<lambda>q. it_D n q aa)) =
              {q'. \<exists>qa. qa \<in> set_op_\<alpha> ss_ops q \<and> (qa, aa, q') \<in> T n}"
          by force
        from p1 det_next_state_eval(1)[of aa] 
        have "set_op_invar ss_ops (determinise_next_state ss_ops (it_S q) (\<lambda>q. it_D n q aa))"
          by force
        from this c1 p2 
        have "{q'. \<exists>qa. qa \<in> set_op_\<alpha> ss_ops q \<and> (qa, aa, q') \<in> T n} \<noteq> {}"
          using StdSet.correct(12) ss_ops_OK by fastforce
        from this obtain q1  q2 where
        q1aaq2: "q1 \<in> set_op_\<alpha> ss_ops q \<and> (q1, aa, q2) \<in> T n" 
          by auto
        from L_OK[OF invar_n] q1aaq2
        show " \<exists>qa. qa \<in> set_op_\<alpha> ss_ops q \<and>
            (\<exists>q'. (qa, sem aa, q') \<in> \<Delta> (\<alpha> n))"
          by force
      }
    qed
      
  } note D_it_OK' = this   

  from ff_OK[OF invar_n] obtain f where f_props:
    "inj_on f {q. q \<subseteq> \<Q> (\<alpha> n)}"
    "\<And>q. set_op_invar ss_ops q \<Longrightarrow> set_op_\<alpha> ss_ops q \<subseteq> \<Q> (\<alpha> n) \<Longrightarrow> ff n q = f (set_op_\<alpha> ss_ops q)"
    by blast
  thm D_it_OK'
  term dfa_construct
  note construct_correct = dfa_construct.dfa_construct_correct [OF const_OK AA'_wf,
      where ?I= "[I n]" and ?Sig = "A n" and ?FP="FP n" and ?ff="ff n" 
             and ?f=f and ?D_it = ?D_it and ?DS = ?DS', 
               OF _ _ _ _ _ _ _ _ _ _ _ D_it_OK'] 
                                                                                                     
  show "nfa_invar_DFA (determinise_impl_aux const ss_ops ff it_A it_D it_S I A FP n) \<and>
        NFA_isomorphic_wf
          (nfa_\<alpha> (determinise_impl_aux const ss_ops ff it_A it_D it_S I A FP n))
          (efficient_determinise_NFA (\<alpha> n))"
    unfolding determinise_impl_aux_def efficient_determinise_NFA_def
    apply (rule_tac construct_correct) 
    apply (simp_all add: I_OK[OF invar_n] A_OK[OF invar_n] FP_OK[OF invar_n]
                         f_props  determinise_NFA_def ff_OK[OF invar_n]
                         A_OK'[OF invar_n] )
    using f_props 
       apply (simp add: inj_on_def)
    defer
    using labels_OK1
    apply force
    using det_next_state_eval  
  proof -
    {
      fix q
      assume p1: "set_op_invar ss_ops q"
      thm inj_setop
      have "\<forall> q'. q' \<in> {q'.
           (\<exists>a. (a, q')
                \<in> (\<lambda>a. (a, determinise_next_state ss_ops (it_S q) (\<lambda>q. it_D n q a))) `
                   {a. \<exists>q q'. (q, a, q') \<in> T n}) \<and>
           \<not> set_op_isEmpty ss_ops q'} \<longrightarrow> set_op_invar ss_ops q'"
        apply (rule_tac allI impI)+
      proof -
        fix q'
        assume p2: "q' \<in> {q'. (\<exists>a. (a, q')
                         \<in> (\<lambda>a. (a, determinise_next_state ss_ops (it_S q)
                                      (\<lambda>q. it_D n q a))) `
                            {a. \<exists>q q'. (q, a, q') \<in> T n}) \<and>
                    \<not> set_op_isEmpty ss_ops q'}"
        from this obtain a
          where a_def: "a \<in> {a. \<exists>q q'. (q, a, q') \<in> T n} \<and> 
                        q' = determinise_next_state ss_ops (it_S q)
                                      (\<lambda>q. it_D n q a)"
          by force
        from det_next_state_eval[of a q] p1 a_def
        show "set_op_invar ss_ops q'" by auto
      qed
      from this inj_setop
      show "inj_on (set_op_\<alpha> ss_ops)
          {q'.
           (\<exists>a. (a, q')
                \<in> (\<lambda>a. (a, determinise_next_state ss_ops (it_S q) (\<lambda>q. it_D n q a))) `
                   {a. \<exists>q q'. (q, a, q') \<in> T n}) \<and>
           \<not> set_op_isEmpty ss_ops q'}" by auto
    }
    {
      from AA'_wf
      have finiteQ: "finite (\<Q> (\<alpha> n)) \<and>
                     (\<forall> (q, \<sigma>, q') \<in> \<Delta> (\<alpha> n). q \<in> (\<Q> (\<alpha> n)) \<and> q' \<in> (\<Q> (\<alpha> n)))"
        unfolding weak_DFA_def NFA_def
        by (smt NFA_set.NFA.\<Delta>_consistent NFA_set.NFA.finite_\<Q> 
                case_prodI2 invar_n nfa.nfa_is_wellformed nfa_OK)
      from finite_\<Delta>[OF invar_n] finite_surj[of "\<Delta> (\<alpha> n)" 
                      "{\<sigma>'| q \<sigma>' q'. (q, \<sigma>', q') \<in> \<Delta> (\<alpha> n)}" 
                      "\<lambda> (q, a, q'). a"]
      have finite\<Delta>': "finite {\<sigma>'| q \<sigma>' q'. (q, \<sigma>', q') \<in> \<Delta> (\<alpha> n)}"
        by force
      from finite_\<Delta>[OF invar_n]  finiteQ
      have c0: "{(Q, \<sigma>, {q'. \<exists>q\<in>Q. (q, \<sigma>, q') \<in> \<Delta> (\<alpha> n)}) |Q \<sigma>. Q \<subseteq> \<Q> (\<alpha> n) \<and>
       Q \<noteq> {} \<and> (\<exists>q. q \<in> Q \<and> (\<exists>q'. (q, \<sigma>, q') \<in> \<Delta> (\<alpha> n))) \<and> \<sigma> \<noteq> {}} \<subseteq>
        {(Q1, \<sigma>, Q2) | Q1 \<sigma> Q2. Q1 \<subseteq> \<Q> (\<alpha> n) \<and> Q2 \<subseteq>\<Q> (\<alpha> n) \<and> 
                      \<sigma> \<in> {\<sigma>'| q \<sigma>' q'. (q, \<sigma>', q') \<in> \<Delta> (\<alpha> n)}}"
        by auto
      have c1:"{(Q1, \<sigma>, Q2) | Q1 \<sigma> Q2. Q1 \<subseteq> \<Q> (\<alpha> n) \<and> Q2 \<subseteq>\<Q> (\<alpha> n) \<and> 
                      \<sigma> \<in> {\<sigma>'| q \<sigma>' q'. (q, \<sigma>', q') \<in> \<Delta> (\<alpha> n)}} = 
              (Pow (\<Q> (\<alpha> n))) \<times> {\<sigma>'| q \<sigma>' q'. (q, \<sigma>', q') \<in> \<Delta> (\<alpha> n)} \<times> (Pow (\<Q> (\<alpha> n)))"
        by force
        
      from finite\<Delta>'  finiteQ
      have c2: "finite (Pow (\<Q> (\<alpha> n))) \<and> 
                finite {\<sigma>'| q \<sigma>' q'. (q, \<sigma>', q') \<in> \<Delta> (\<alpha> n)}" by auto
        
      from  c1 c2 finite_cartesian_product
      have "finite {(Q1, \<sigma>, Q2) | Q1 \<sigma> Q2. Q1 \<subseteq> \<Q> (\<alpha> n) \<and> Q2 \<subseteq>\<Q> (\<alpha> n) \<and> 
                      \<sigma> \<in> {\<sigma>'| q \<sigma>' q'. (q, \<sigma>', q') \<in> \<Delta> (\<alpha> n)}}"
        by auto

     from this c0 finite_subset
      show "finite
     {(Q, \<sigma>, {q'. \<exists>q\<in>Q. (q, \<sigma>, q') \<in> \<Delta> (\<alpha> n)}) |Q \<sigma>. Q \<subseteq> \<Q> (\<alpha> n) \<and>
       Q \<noteq> {} \<and> (\<exists>q. q \<in> Q \<and> (\<exists>q'. (q, \<sigma>, q') \<in> \<Delta> (\<alpha> n))) \<and> \<sigma> \<noteq> {}}"
        by auto
    }
    
  qed
qed


definition set_encode_rename :: "('a \<Rightarrow> nat) \<Rightarrow> 'a set \<Rightarrow> nat" where
  "set_encode_rename f S = set_encode (f ` S)"


lemma set_encode_rename_eq:
assumes fin: "finite S" 
    and f_inj_on: "inj_on f S"
    and sub: "A \<subseteq> S" "B \<subseteq> S"
shows "set_encode_rename f A = set_encode_rename f B \<longleftrightarrow> A = B"
proof -
  from sub f_inj_on have f_inj_on': "inj_on f (A \<union> B)"
    by (simp add: inj_on_def Ball_def subset_iff)

  from fin sub have fin': "finite A" "finite B" by (metis finite_subset)+

  from inj_on_Un_image_eq_iff[OF f_inj_on']
       fin' set_encode_eq [of "f ` A" "f ` B"] show ?thesis
    by (simp add: set_encode_rename_def)
qed


definition set_encode_rename_map :: 
  "('q, nat, 'm, _) map_ops_scheme \<Rightarrow> ('q, 'm \<times> nat) set_iterator \<Rightarrow> 'm" where
  "set_encode_rename_map m_ops it =
   fst (it (\<lambda>_. True) (\<lambda>q (m, n). 
   (map_op_update_dj m_ops q n m, 2*n)) (map_op_empty m_ops (), 1))"

lemma set_encode_rename_map_correct :
fixes m_ops ::  "('q, nat, 'm, _) map_ops_scheme" 
  and it :: "('q, 'm \<times> nat) set_iterator" 
defines "m \<equiv> set_encode_rename_map m_ops it"
assumes it_OK: "set_iterator it S"
    and m_ops_OK: "StdMap m_ops"
shows "\<exists>f. inj_on f S \<and> map_op_invar m_ops m \<and> 
           (dom (map_op_\<alpha> m_ops m) = S) \<and>
           (\<forall>q\<in>S. (map_op_\<alpha> m_ops m) q = Some (2 ^ (f q)))"
proof -
  interpret m: StdMap m_ops by fact

  let ?I = "\<lambda>S (m, n).
        \<exists>f n'. inj_on f S \<and> map_op_invar m_ops m \<and> 
           (dom (map_op_\<alpha> m_ops m) = S) \<and>
           (\<forall>q\<in>S. (map_op_\<alpha> m_ops m) q = Some (2 ^ (f q))) \<and>
           (\<forall>q\<in>S. f q < n') \<and> (n = 2 ^ n')"

  obtain m' n where m_eq': 
    "it (\<lambda>_. True) (\<lambda>q (m, n). (map_op_update_dj m_ops q n m, 2*n)) 
        (map_op_empty m_ops (), 1) = (m', n)"
    by (rule prod.exhaust)

  thm it_OK
  have "?I S ((it (\<lambda>_. True) (\<lambda>q (m, n). (map_op_update_dj m_ops q n m, 2*n)) 
        (map_op_empty m_ops (), 1)))"
  proof (rule set_iterator_no_cond_rule_insert_P[OF it_OK, of ?I])
    show "case (m.empty (), 1) of
    (m, n) \<Rightarrow>
      \<exists>f n'.
         inj_on f {} \<and>
         m.invar m \<and>
         dom (m.\<alpha> m) = {} \<and>
         (\<forall>q\<in>{}. m.\<alpha> m q = Some (2 ^ f q)) \<and> (\<forall>q\<in>{}. f q < n') \<and> n = 2 ^ n'"
      apply (simp add: m.correct) 
      apply (rule exI [where x = 0]) 
      apply simp
    done
next
  show "\<And>\<sigma>. case \<sigma> of
         (m, n) \<Rightarrow>
           \<exists>f n'.
              inj_on f S \<and>
              m.invar m \<and>
              dom (m.\<alpha> m) = S \<and>
              (\<forall>q\<in>S. m.\<alpha> m q = Some (2 ^ f q)) \<and> (\<forall>q\<in>S. f q < n') \<and> n = 2 ^ n' \<Longrightarrow>
         case \<sigma> of
         (m, n) \<Rightarrow>
           \<exists>f n'.
              inj_on f S \<and>
              m.invar m \<and>
              dom (m.\<alpha> m) = S \<and>
              (\<forall>q\<in>S. m.\<alpha> m q = Some (2 ^ f q)) \<and> (\<forall>q\<in>S. f q < n') \<and> n = 2 ^ n'"
   by simp 
next
  fix Sa \<sigma> x
  show "x \<in> S - Sa \<Longrightarrow>
       case \<sigma> of
       (m, n) \<Rightarrow>
         \<exists>f n'.
            inj_on f Sa \<and>
            m.invar m \<and>
            dom (m.\<alpha> m) = Sa \<and>
            (\<forall>q\<in>Sa. m.\<alpha> m q = Some (2 ^ f q)) \<and> (\<forall>q\<in>Sa. f q < n') \<and> n = 2 ^ n' \<Longrightarrow>
       Sa \<subseteq> S \<Longrightarrow>
       case case \<sigma> of (m, n) \<Rightarrow> (m.update_dj x n m, 2 * n) of
       (m, n) \<Rightarrow>
         \<exists>f n'.
            inj_on f (insert x Sa) \<and>
            m.invar m \<and>
            dom (m.\<alpha> m) = insert x Sa \<and>
            (\<forall>q\<in>insert x Sa. m.\<alpha> m q = Some (2 ^ f q)) \<and>
            (\<forall>q\<in>insert x Sa. f q < n') \<and> n = 2 ^ n'"
  proof -
    assume q_in: "x \<in> S - Sa"
       and ind_hyp: "case \<sigma> of
       (m, n) \<Rightarrow>
         \<exists>f n'.
            inj_on f Sa \<and>
            m.invar m \<and>
            dom (m.\<alpha> m) = Sa \<and>
            (\<forall>q\<in>Sa. m.\<alpha> m q = Some (2 ^ f q)) \<and> (\<forall>q\<in>Sa. f q < n') \<and> n = 2 ^ n'"
        and S'_subset: "Sa \<subseteq> S"
    obtain m n where mn_eq[simp]: "\<sigma> = (m, n)" by (rule prod.exhaust)

    from ind_hyp obtain f n' where f_props: "
        inj_on f Sa \<and>
        map_op_invar m_ops m \<and>
        dom (map_op_\<alpha> m_ops m) = Sa \<and> (\<forall>q\<in>Sa. map_op_\<alpha> m_ops m q = Some (2 ^ f q)) \<and> 
        (\<forall>q\<in>Sa. f q < n') \<and> (n = 2 ^ n')" 
      by auto

    let ?f' = "\<lambda>q'. if q' = x then n' else f q'"

    from f_props q_in
    show "case case \<sigma> of (m, n) \<Rightarrow> (m.update_dj x n m, 2 * n) of
       (m, n) \<Rightarrow>
         \<exists>f n'.
            inj_on f (insert x Sa) \<and>
            m.invar m \<and>
            dom (m.\<alpha> m) = insert x Sa \<and>
            (\<forall>q\<in>insert x Sa. m.\<alpha> m q = Some (2 ^ f q)) \<and>
            (\<forall>q\<in>insert x Sa. f q < n') \<and> n = 2 ^ n'"
      apply (simp add: m.correct)
      apply (rule exI[where x = ?f'])
      apply (simp add: image_iff Ball_def)
      apply (intro conjI)
        apply (simp add: inj_on_def)
        apply (metis order_less_irrefl)
         
        apply (rule exI [where x = "Suc n'"])
        apply (simp)
        apply (metis less_SucI)
    done
qed
qed
with m_eq' show ?thesis
    apply (simp add: m_def set_encode_rename_map_def)
    apply metis
  done
qed

definition set_encode_rename_impl ::
  "('q, nat, 'm, _) map_ops_scheme \<Rightarrow> 'm \<Rightarrow> ('q, nat) set_iterator \<Rightarrow> nat" where
  "set_encode_rename_impl m_ops m it =
   (it (\<lambda>_. True) (\<lambda>q n. n + the (map_op_lookup m_ops q m)) 0)"
 
lemma set_encode_rename_impl_correct:
assumes invar_m: "map_op_invar m_ops m"
    and f_inj_on: "inj_on f S"
    and m_ops_OK: "StdMap m_ops"
    and m_prop: "\<And>q. q \<in> S \<Longrightarrow> (map_op_\<alpha> m_ops m) q = Some (2 ^ (f q))"
    and it_OK: "set_iterator it S"
shows "set_encode_rename_impl m_ops m it = set_encode_rename f S"
proof -
  interpret m: StdMap m_ops by fact
  let ?I = "\<lambda>S n. n = set_encode_rename f S"

  show ?thesis
  unfolding set_encode_rename_impl_def
  proof (rule set_iterator_no_cond_rule_insert_P[OF it_OK, of ?I])
    fix S' n q
    assume q_in: "q \<in> S - S'" and
           n_eq: "n = set_encode_rename f S'" and
           S'_subset: "S' \<subseteq> S" 

    from it_OK have "finite S" 
      using set_iterator_finite by blast
    with S'_subset have "finite S'" by (metis finite_subset)
    hence fin_f_S': "finite (f ` S')" by (rule finite_imageI)

    from q_in f_inj_on S'_subset
    have fq_nin: "f q \<notin> f ` S'" by (simp add: image_iff Ball_def subset_iff inj_on_def) metis

    from set_encode_insert [OF fin_f_S' fq_nin]
    have enc_insert: "set_encode (insert (f q) (f ` S')) = 2 ^ f q + set_encode (f ` S')" . 

    from q_in m_prop[of q] invar_m have m_q_eq: "map_op_lookup m_ops q m = Some (2 ^ (f q))"
      by (simp add: m.correct)
    show "n + the (map_op_lookup m_ops q m) = set_encode_rename f (insert q S')"
      by (simp add: set_encode_rename_def m_q_eq enc_insert n_eq)
  qed (simp_all add: set_encode_rename_def)
qed


context nfa_dfa_by_lts_bool_algebra_defs
begin


definition determinise_impl where
   "determinise_impl qm_ops m_ops 
          it_S it_S2 it_q it_A it_D_nfa  n =  
       (determinise_impl_aux 
          (nfa.NFA_construct_reachable_ba_impl_code qm_ops) 
          s_ops
          (\<lambda>n q. set_encode_rename_impl m_ops 
                  (set_encode_rename_map m_ops (\<lambda>c f. it_S2 (nfa.nfa_states n) c f)) 
                        (\<lambda>c f. it_q q c f))
          (\<lambda>n c f. it_A (nfa.nfa_labels n) c f) 
          (\<lambda>n. it_D_nfa (nfa.nfa_trans n))
          (\<lambda>S c f. it_S S c f)
          nfa.nfa_initial
          nfa.nfa_alphabet
          (\<lambda>n q. \<not>(s.disjoint q (nfa.nfa_accepting n))) n)"

schematic_goal determinise_impl_code': 
   "determinise_impl qm_ops m_ops it_S it_S2 it_q it_A it_D_nfa  
    (Q1, A1, D1, I1, F1) =  nfa.NFA_construct_reachable_ba_impl_code qm_ops
     (\<lambda>q. it_q q (\<lambda>_. True)
           (\<lambda>q n. n +
                  the (map_op_lookup m_ops q
                        (fst (it_S2 Q1 (\<lambda>_. True)
                               (\<lambda>q (m, n). (map_op_update_dj m_ops q n m, 2 * n))
                               (map_op_empty m_ops (), 1)))))
           0)
     (A1) [I1]
     (\<lambda>q. \<not> s.disjoint q (F1))
     (\<lambda>S. set_iterator_image_filter
           (\<lambda>a. let nq = set_iterator_product (it_S S)
                          (\<lambda>q. it_D_nfa (D1) q a)
                          (\<lambda>_. True) (\<lambda>(uu, y). s.ins y) (s.empty ())
                in if \<not> s.isEmpty nq then Some (a, nq) else None)
           (it_A
             (nfa.nfa_tranlabel (d_nfa.to_list (D1)))))"
  unfolding determinise_impl_def determinise_impl_aux_def 
            set_encode_rename_impl_def set_encode_rename_map_def
            determinise_iterator_def nfa.nfa_labels_def
            determinise_next_state_def
  by simp_all



lemma nfa_tranlabel_code':
  shows "nfa.nfa_tranlabel ts = 
        (List.foldr (\<lambda> e si. lt.ins (fst (snd e)) si) ts (lt.empty ()))"
  apply (induction ts)
  apply simp
  by simp

schematic_goal nfa_tranlabel_code:
   "nfa.nfa_tranlabel = ?XXX"
  unfolding nfa_tranlabel_code'
  by (rule refl)


schematic_goal determinise_impl_code: 
   "determinise_impl qm_ops m_ops it_S it_S2 it_q it_A it_D_nfa  
    (Q1, A1, D1, I1, F1) = ?XXX"
  unfolding determinise_impl_code'
            nfa.NFA_construct_reachable_ba_impl_code_def
            nfa_tranlabel_code
  by (rule refl)


lemma set_iteratei_alt_def :
  "set_iteratei \<alpha> invar it \<longleftrightarrow>
   (\<forall>s. invar s \<longrightarrow> set_iterator (\<lambda>c f \<sigma>. it s c f \<sigma>) (\<alpha> s))"
proof (intro allI impI iffI)
  fix s
  assume it_OK: "set_iteratei \<alpha> invar it"
     and "invar s"
  thus "set_iterator (\<lambda>c f \<sigma>. it s c f \<sigma>) (\<alpha> s)"
    unfolding set_iterator_def set_iterator_def
              set_iteratei_def finite_set_def
              set_iteratei_axioms_def
    by simp
next
  assume rs: "\<forall>s. invar s \<longrightarrow> set_iterator (\<lambda>c f. it s c f ) (\<alpha> s)"

  have "\<forall>s. invar s \<longrightarrow> finite (\<alpha> s)"
  proof (intro allI impI)
fix s
    assume "invar s"
    with rs have "set_iterator_genord (\<lambda>c f. it s c f) (\<alpha> s) (\<lambda> _ _ . True)"
      unfolding set_iterator_def by simp
    
    from set_iterator_genord.finite_S0 [OF this] show "finite (\<alpha> s)" .
  qed

  with rs show "set_iteratei \<alpha> invar it"
    unfolding set_iterator_def set_iterator_def
              set_iteratei_def finite_set_def
              set_iteratei_axioms_def
    by simp
qed


lemma set_iteratei_alt_D :
  "set_iteratei \<alpha> invar it \<Longrightarrow>
   invar s \<Longrightarrow> set_iterator (\<lambda>c f \<sigma>. it s c f \<sigma>) (\<alpha> s)"
by (simp add: set_iteratei_alt_def)
lemma nfa_labels_invar: "d_nfa.invar (nfa.nfa_trans n) \<longrightarrow> lt.invar (nfa.nfa_labels n)"
  apply (rule impI)
proof -
  assume n_invar: "d_nfa.invar (nfa.nfa_trans n)"
  obtain q1 a1 d1 i1 f1 where n_def: "n = (q1, a1, d1, i1, f1)" 
    using prod_cases5 by blast
  from this n_invar
  have invard1: "d_nfa.invar d1" by auto
  from this obtain dl where dl_def: "dl = d_nfa.to_list d1" by auto
  thm lt.correct
  have "lt.invar (nfa.nfa_tranlabel dl)"
    apply (induction dl)
    using lt.correct(2)
    apply simp
    apply simp
    using lt.correct by auto
  from this nfa.nfa_labels_def[of n] dl_def n_def
  show "lt.invar (nfa.nfa_labels n)"
    by auto    
qed

lemma lteq: "nfa.nfa_invar_DFA n \<Longrightarrow> 
  {uu. \<exists>q q'. (q, uu, q') \<in> d_nfa.\<alpha> (nfa.nfa_trans n)} = lt.\<alpha> (nfa.nfa_labels n)"
  unfolding nfa.nfa_labels_def d_nfa.correct lt.correct
proof -
  assume invar: "nfa.nfa_invar_DFA n"
  show "{uu. \<exists>q q'. (q, uu, q') \<in> d_nfa.\<alpha> (nfa.nfa_trans n)} =
        lt.\<alpha> (nfa.nfa_tranlabel (d_nfa.to_list (nfa.nfa_trans n)))"
  proof 
    from invar
    have invarn: "d_nfa.invar (nfa.nfa_trans n)"
      unfolding nfa.nfa_invar_DFA_def nfa.nfa_invar_def
      by simp
    from this d_nfa.correct(3) 
    have eq1: "d_nfa.\<alpha> (nfa.nfa_trans n) = set (d_nfa.to_list (nfa.nfa_trans n))"
      by auto
    {
      show "{uu. \<exists>q q'. (q, uu, q') \<in> d_nfa.\<alpha> (nfa.nfa_trans n)}
              \<subseteq> lt.\<alpha> (nfa.nfa_tranlabel (d_nfa.to_list (nfa.nfa_trans n)))"
      proof
        fix x
        assume p1: "x \<in> {uu. \<exists>q q'. (q, uu, q') \<in> d_nfa.\<alpha> (nfa.nfa_trans n)}"
        from this eq1
        have c1: "x \<in> {uu. \<exists>q q'. (q, uu, q') \<in> set (d_nfa.to_list (nfa.nfa_trans n))}"
          by auto
        obtain dl where
        dl_def: "dl = (d_nfa.to_list (nfa.nfa_trans n))"  by auto
        from this c1
        have "x \<in> {uu. \<exists>q q'. (q, uu, q') \<in> set (dl)}" by auto
        from this
        have "x \<in> lt.\<alpha> (nfa.nfa_tranlabel dl)"
          apply (induction dl)
          apply simp
        proof -
          fix a dl
          assume p1: "x \<in> {uu. \<exists>q q'. (q, uu, q') \<in> set dl} \<Longrightarrow> x \<in> lt.\<alpha> (nfa.nfa_tranlabel dl)"
              and p2: "x \<in> {uu. \<exists>q q'. (q, uu, q') \<in> set (a # dl)}"

          have "lt.invar (nfa.nfa_tranlabel dl)"
            apply (induction dl)
            using lt.correct(2) apply simp
            using lt.correct by auto

          from this
          have "lt.\<alpha> (nfa.nfa_tranlabel (a # dl)) = 
                {fst (snd a)} \<union> lt.\<alpha> (nfa.nfa_tranlabel dl)"
            apply simp
            using lt.correct
            by auto
          from this p1 p2
          show "x \<in> lt.\<alpha> (nfa.nfa_tranlabel (a # dl))"
            by force
        qed
        from this dl_def
        show "x \<in> lt.\<alpha> (nfa.nfa_tranlabel (d_nfa.to_list (nfa.nfa_trans n)))"
          by auto
      qed
    }
    {
      show "lt.\<alpha> (nfa.nfa_tranlabel (d_nfa.to_list (nfa.nfa_trans n)))
             \<subseteq> {uu. \<exists>q q'. (q, uu, q') \<in> d_nfa.\<alpha> (nfa.nfa_trans n)}"
      proof 
        fix x
        assume p1: "x \<in> lt.\<alpha> (nfa.nfa_tranlabel (d_nfa.to_list (nfa.nfa_trans n)))"
        have eq2: "set (d_nfa.to_list (nfa.nfa_trans n)) = d_nfa.\<alpha> (nfa.nfa_trans n)"
          using invarn d_nfa.correct
          by auto
     
        obtain dl where
        dl_def: "dl = (d_nfa.to_list (nfa.nfa_trans n))"  by auto


        have invardl: "lt.invar (nfa.nfa_tranlabel dl)"
            apply (induction dl)
            using lt.correct(2) apply simp
            using lt.correct by auto

        from invardl
        have "lt.\<alpha> (nfa.nfa_tranlabel dl) = {a | q a q'. (q, a, q') \<in> set dl}"
          apply (induction dl)
          using lt.correct apply simp 
        proof -
          fix a dl  
          assume ind: "(lt.invar (nfa.nfa_tranlabel dl) \<Longrightarrow>
               lt.\<alpha> (nfa.nfa_tranlabel dl) = {uu. \<exists>q a q'. uu = a \<and> (q, a, q') \<in> set dl})"

           have invardl: "lt.invar (nfa.nfa_tranlabel dl)"
            apply (induction dl)
            using lt.correct(2) apply simp
            using lt.correct by auto
          from this ind
          have c1': "lt.\<alpha> (nfa.nfa_tranlabel dl) = 
                    {uu. \<exists>q a q'. uu = a \<and> (q, a, q') \<in> set dl}"
            by auto
          from invardl
          have c2: "lt.\<alpha> (nfa.nfa_tranlabel (a # dl)) = 
                {fst (snd a)} \<union> lt.\<alpha> (nfa.nfa_tranlabel dl)"
            apply simp
            using lt.correct
            by auto
          have c1: "set (a # dl) = {a} \<union> set dl" by auto
          thm this
          have "{aa. \<exists>q q'. (q, aa, q') \<in> set (a # dl)} = 
                ({fst (snd a)} \<union> {a. \<exists>q q'. (q, a, q') \<in> set dl})" 
          proof 
            {
              show "{aa. \<exists>q q'. (q, aa, q') \<in> set (a # dl)}
                     \<subseteq> {fst (snd a)} \<union> {a. \<exists>q q'. (q, a, q') \<in> set dl}"
              proof
                fix x
                show " x \<in> {aa. \<exists>q q'. (q, aa, q') \<in> set (a # dl)} \<Longrightarrow>
         x \<in> {fst (snd a)} \<union> {a. \<exists>q q'. (q, a, q') \<in> set dl}"
                proof -
                  assume p1: "x \<in> {aa. \<exists>q q'. (q, aa, q') \<in> set (a # dl)}"
                 
                from this 
                obtain q q' where qq'_def: "(q, x, q') \<in> set (a # dl)" 
                  by auto
                from this
                show "x \<in> {fst (snd a)} \<union> {a. \<exists>q q'. (q, a, q') \<in> set dl} "
                  by auto
              qed
            qed
          }
          {
            show "{fst (snd a)} \<union> {a. \<exists>q q'. (q, a, q') \<in> set dl}
                  \<subseteq> {aa. \<exists>q q'. (q, aa, q') \<in> set (a # dl)}"
            proof
              fix x
              assume p1: "x \<in> {fst (snd a)} \<union> {a. \<exists>q q'. (q, a, q') \<in> set dl}"
              from this 
              obtain q q' where
              qq'_def: "x = fst (snd a) \<or> (q, x, q') \<in> set dl" by auto
              from this
              show "x \<in> {aa. \<exists>q q'. (q, aa, q') \<in> set (a # dl)}"
                by (smt list.set_intros(1) list.set_intros(2) mem_Collect_eq prod.exhaust_sel)
            qed
          }
        qed
        from this c1 c2
        show "lt.\<alpha> (nfa.nfa_tranlabel (a # dl)) =
                 {uu. \<exists>q aa q'. uu = aa \<and> (q, aa, q') \<in> set (a # dl)}"
            apply simp
            unfolding insert_def
            using c1' by auto
        qed
        from this p1 
        show "x \<in> {uu. \<exists>q q'. (q, uu, q') \<in> d_nfa.\<alpha> (nfa.nfa_trans n)}"
          unfolding dl_def
          by (simp add: eq2)
      qed
    }
  qed
qed


end


subsection \<open> Complement \<close>
context automaton_by_lts_bool_algebra_defs 
begin

definition complement_impl where
  "complement_impl = (\<lambda>(Q, A, D, I, F). (Q, A, D, I, s.diff Q F))"

lemma complement_impl_correct :
shows "nfa_complement nfa_\<alpha> nfa_invar_NFA' complement_impl"
proof (intro nfa_complement.intro nfa_complement_axioms.intro)
  show "nfa nfa_\<alpha> nfa_invar_NFA'" by simp

  fix n
  assume invar: "nfa_invar_NFA' n"
  obtain QL AL DL IL FL where n_eq[simp]: "n = (QL, AL, DL, IL, FL)" by (cases n, blast)

 

  from invar have invar_weak: "nfa_invar n" and wf: "NFA (nfa_\<alpha> n)" 
    unfolding nfa_invar_NFA'_def by simp_all

  from invar_weak 
  have "nfa_invar (complement_impl n) \<and> 
        nfa_\<alpha> (complement_impl n) = DFA_complement (nfa_\<alpha> n)"
    apply (simp add: nfa_invar_def nfa_\<alpha>_def 
                     DFA_complement_def complement_impl_def
                     s.correct NFA_rename_states_def 
                     d.correct_common lts_reverse_def)
    done

  with wf this 
  show "nfa_\<alpha> (complement_impl n) = DFA_complement (nfa_\<alpha> n)" 
       "nfa_invar_NFA' (complement_impl n)"
    unfolding nfa_invar_NFA'_def 
    by (simp_all add: DFA_complement___is_well_formed complement_impl_def)
qed

end


context nfa_dfa_by_lts_bool_algebra_defs 
begin

fun complement_impl where
   "complement_impl n = (nfa.complement_impl n)"


schematic_goal complement_impl_code :
  "complement_impl (Q1, A1, D1, I1, F1) = ?code_nfa"
unfolding complement_impl.simps nfa.complement_impl_def split
by (rule refl)+

definition  nfa_dfa_invar' where
     "nfa_dfa_invar' n = ((nfa.nfa_invar_NFA' n) \<and> DFA (nfa.nfa_\<alpha> n))"

definition nfa_dfa_\<alpha> where
     "nfa_dfa_\<alpha> n = (nfa.nfa_\<alpha> n)"

lemma complement_impl_correct :
  shows "nfa_complement nfa_dfa_\<alpha> nfa_dfa_invar' complement_impl"
  using nfa.complement_impl_correct 
  apply (auto simp add: nfa_complement_def 
                   nfa_complement_axioms_def nfa_dfa_invar'_def)
    defer
  using DFA_complement_of_DFA_is_DFA
  apply blast
  apply (simp add: nfa_dfa_\<alpha>_def)
  by (simp add: nfa_def nfa_dfa_\<alpha>_def nfa_dfa_invar'_def)


end


end



