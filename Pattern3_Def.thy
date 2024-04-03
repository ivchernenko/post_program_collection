theory Pattern3_Def
  imports RequirementLemmas
begin

definition always where "always s A \<equiv>
\<forall> s1. substate s1 s \<and> toEnvP s1 \<longrightarrow> A s1"

lemma always_rule: "always s0 A \<and> (A' s) \<and> (\<forall> s1 . toEnvP s1 \<and> substate s1 s0 \<and>A s1 \<longrightarrow> A' s1) \<Longrightarrow>
consecutive s0 s \<Longrightarrow> always s A'"
  apply(unfold always_def)
  by (metis consecutive.elims(2) substate_noteq_imp_substate_of_pred)


lemma always_einv2req: " always s A \<and>  (\<forall> s1 . toEnvP s1 \<and> substate s1 s \<and>A s1 \<longrightarrow> A' s1) \<Longrightarrow>
  always s A'"
  apply(unfold always_def)
  by simp

end
  
     
