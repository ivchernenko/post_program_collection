theory Pattern2_Def
  imports Pattern3_Def
begin

definition P2all where " P2all s A \<equiv>
\<forall> s1. consecutive s1 s \<longrightarrow> A s1 s"

definition P2ex where "P2ex s A \<equiv>
\<exists> s1. consecutive s1 s \<and> A s1 s"

definition P2 where  "P2 s A1 A2 \<equiv> toEnvP s \<and>
(\<forall> s1 s2. consecutive s1 s2 \<and> A1 s1 s2 \<longrightarrow> A2 s1 s2)"

lemma P2all_rule: "consecutive s0 s \<Longrightarrow> P2all s A = A s0 s"
  apply(unfold consecutive_def P2all_def)
  by (metis toEnvNum_eq_imp_eq2)

lemma P2ex_rule: "consecutive s0 s \<Longrightarrow> P2ex s A = A s0 s"
  apply(unfold consecutive_def P2ex_def)
  by (metis toEnvNum_eq_imp_eq2)

lemma P2_rule: "consecutive s0 s \<Longrightarrow> P2 s0 A1 A2 \<Longrightarrow> (consecutive s0 s \<Longrightarrow> A1 s0 s \<longrightarrow> A2 s0 s) \<Longrightarrow> P2 s A1 A2"
  apply simp
  apply(unfold P2_def)
  using consecutive_def by blast

end
