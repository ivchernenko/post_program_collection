theory Pattern2_Def
  imports Pattern3_Def
begin

definition previous_all where " previous_all s A \<equiv>
\<forall> s1. consecutive s1 s \<longrightarrow> A s1"

definition previous_ex where "previous_ex s A \<equiv>
\<exists> s1. consecutive s1 s \<and> A s1"

definition always2 where  "always2 s A1 A2 A3 \<equiv> 
always s (\<lambda> s2.( previous_ex s2 A1) \<and> A2 s2 \<longrightarrow> A3 s2)"

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
always2 s0 A1 A2 A3 \<and> (\<not> A1 s0 \<or> ~ A2 s \<or> A3' s) \<and> (\<forall> s1. toEnvP s1 \<and> substate s1 s0 \<and> A3 s1 \<longrightarrow> A3' s1) \<Longrightarrow> always2 s A1 A2 A3'"
  apply(unfold always2_def)
  by (smt (verit) always_def consecutive.elims(2) previous_ex_def substate_noteq_imp_substate_of_pred toEnvNum_eq_imp_eq2)



lemma always2_einv2req: "always2 s A1 A2 A3 \<and>  (\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> A3 s1 \<longrightarrow> A3' s1) \<Longrightarrow> always2 s A1 A2 A3'"
  apply(unfold always2_def)
  by (simp add: always_def)

end