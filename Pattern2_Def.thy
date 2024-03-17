theory Pattern2_Def
  imports Pattern3_Def
begin

definition P2all where " P2all s A \<equiv>
\<forall> s1. consecutive s1 s \<longrightarrow> A s1"

definition P2ex where "P2ex s A \<equiv>
\<exists> s1. consecutive s1 s \<and> A s1"

definition P2 where  "P2 s A1 A2 \<equiv> toEnvP s \<and>
(\<forall> s1 s2. consecutive s1 s2 \<and> substate s2 s \<and> A1 s1 s2 \<longrightarrow> A2 s1 s2)"

lemma P2all_rule: "consecutive s0 s \<Longrightarrow>  A s0 \<Longrightarrow> P2all s A"
  apply(unfold  P2all_def)
  apply simp
  by (metis toEnvNum_eq_imp_eq2)

lemma P2ex_rule: "consecutive s0 s \<Longrightarrow>  A s0  \<Longrightarrow> P2ex s A"
  apply(unfold  P2ex_def)
  by auto

lemma P2_rule: "consecutive s0 s \<Longrightarrow> P2 s0 A1 A2 \<Longrightarrow> (consecutive s0 s \<Longrightarrow> A1 s0 s \<longrightarrow> A2 s0 s) \<Longrightarrow> P2 s A1 A2"
  apply simp
  apply(unfold P2_def)
  apply simp
  by (metis One_nat_def substate_noteq_imp_substate_of_pred toEnvNum_eq_imp_eq2)

end
  
