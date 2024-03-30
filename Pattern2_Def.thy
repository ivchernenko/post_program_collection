theory Pattern2_Def
  imports Pattern3_Def
begin

definition previous_all where " previous_all s A \<equiv>
\<forall> s1. consecutive s1 s \<longrightarrow> A s1"

definition previous_ex where "previous_ex s A \<equiv>
\<exists> s1. consecutive s1 s \<and> A s1"

definition always2 where  "always2 s A1 A2 \<equiv> 
\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and> A1 s1 s2 \<longrightarrow> A2 s2"

lemma previous_all_one_point: "consecutive s0 s \<Longrightarrow>  A s0 \<Longrightarrow> previous_all s A"
  apply(unfold  previous_all_def)
  apply simp
  by (metis toEnvNum_eq_imp_eq2)

lemma previous_ex_one_point: "consecutive s0 s \<Longrightarrow>  A s0  \<Longrightarrow> previous_ex s A"
  apply(unfold  previous_ex_def)
  by auto

lemma previous_all_rule: "
(\<forall> s1. toEnvP s1 \<and> substate s1 s0 \<and> A s1 \<longrightarrow> A' s1) \<Longrightarrow>
(\<forall> s1. toEnvP s1 \<and> substate s1 s0 \<and> previous_all s1 A  \<longrightarrow> previous_all s1 A')"
  apply(unfold previous_all_def)
  by (meson consecutive.simps substate_trans)

lemma previous_ex_rule: "
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> A s1 \<longrightarrow> A' s1) \<Longrightarrow>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> previous_ex s1 A  \<longrightarrow> previous_ex s1 A')"
  apply(unfold previous_ex_def)
  by (meson consecutive.simps substate_trans)

lemma always2_rule: "consecutive s0 s \<Longrightarrow>
always2 s0 A1 A2 \<and> (\<not> A1 s0 s \<or> A2' s) \<and> (\<forall> s1. toEnvP s1 \<and> substate s1 s0 \<and> A2 s1 \<longrightarrow> A2' s1) \<Longrightarrow> always2 s A1 A2'"
  apply(unfold always2_def)
  by (metis consecutive.elims(2) substate_noteq_imp_substate_of_pred toEnvNum_eq_imp_eq2)

lemma always2_einv2req: "always2 s A1 A2 \<and>  (\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> A2 s1 \<longrightarrow> A2' s1) \<Longrightarrow> always2 s A1 A2'"
  using always2_def by auto

end