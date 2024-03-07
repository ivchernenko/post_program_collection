theory Pattern3_Def
  imports VCTheoryLemmas
begin

definition P3 where "P3 s A1 A2 \<equiv>
\<forall> s1. substate s1 s \<and> toEnvP s1 \<and> A1 s1 \<longrightarrow> A2 s1"

lemma P3_rule: "P3 s0 A1 A2 \<Longrightarrow> (A1 s \<longrightarrow> A2 s) \<Longrightarrow> toEnvP s0 \<and>  toEnvP s \<and> substate s0 s \<and> toEnvNum s0 s = 1 \<Longrightarrow> P3 s A1 A2"
  apply(unfold P3_def)
  using substate_noteq_im_substate_of_pred by blast



end