
theory Bool_Algebra

imports Main

begin

locale bool_algebra = 
  fixes sem_intervals :: " 'b \<Rightarrow> 'a set"
  fixes empty_intervals:: "'b \<Rightarrow> bool"
  fixes noempty_intervals:: "'b \<Rightarrow> bool"
  fixes intersect_intervals:: "'b \<Rightarrow> 'b \<Rightarrow> 'b"
  fixes diff_intervals:: "'b \<Rightarrow> 'b \<Rightarrow> 'b"
  fixes elem_intervals:: "'a  \<Rightarrow> 'b \<Rightarrow> bool"
  fixes canonical_intervals:: "'b \<Rightarrow> bool"
  assumes 
    inj_semIs_aux: "\<And> l1 l2. canonical_intervals l1 \<and> canonical_intervals l2 
                            \<and> sem_intervals l1 = sem_intervals l2 
                 \<Longrightarrow> l1 = l2" and
    empty_interval_sem: "canonical_intervals s \<longrightarrow> 
                         empty_intervals s = (sem_intervals s = {})" and
    noempty_intervals_sem: "canonical_intervals s \<longrightarrow> 
                            noempty_intervals s =  (\<not> (empty_intervals s))" and
    intersect_intervals_sem: "canonical_intervals s1 \<and> canonical_intervals s2 \<longrightarrow>
                              sem_intervals (intersect_intervals s1 s2) = 
                              (sem_intervals s1) \<inter> (sem_intervals s2) \<and>
                              canonical_intervals (intersect_intervals s1 s2)" and
    diff_intervals_sem: "canonical_intervals s1 \<and> canonical_intervals s2 \<longrightarrow>
                              sem_intervals (diff_intervals s1 s2) = 
                              (sem_intervals s1) - (sem_intervals s2) \<and>
                              canonical_intervals (diff_intervals s1 s2)" and
    elem_sem: "elem_intervals a s \<equiv>  (a \<in> sem_intervals s)"
begin 


end

end

