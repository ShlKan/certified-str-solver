theory NFA_states

imports Main

begin

class NFA_states =
  fixes states_enumerate :: "nat \<Rightarrow> 'a"
  assumes states_enumerate_inj: "inj states_enumerate"
begin
  lemma states_enumerate_eq: "states_enumerate n = states_enumerate m \<longleftrightarrow> n = m"
    using states_enumerate_inj
    unfolding inj_on_def by auto

  lemma not_finite_NFA_states_UNIV : "~ (finite (UNIV ::'a set))"
  proof 
    assume fin_UNIV: "finite (UNIV::'a set)"
    hence "finite (states_enumerate ` UNIV)"
      by (rule_tac finite_subset[of _ UNIV], simp_all)
    hence "finite (UNIV::nat set)"
      using states_enumerate_inj
      by (rule finite_imageD)
    thus "False" using infinite_UNIV_nat by simp
  qed
end


instantiation nat :: NFA_states
begin
  definition "states_enumerate q = q"

  instance proof  
    show "inj (states_enumerate::nat \<Rightarrow> nat)"
      unfolding states_enumerate_nat_def
      by (simp add: inj_on_def)
  qed
end

end
