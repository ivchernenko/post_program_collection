theory RequirementLemmas
  imports VCTheoryLemmas
begin

lemma all_disj_rule: "(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> P s1 \<longrightarrow> P' s1) \<and> (\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> Q s1 \<longrightarrow> Q' s1) \<Longrightarrow>
\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> (P s1 \<or> Q s1) \<longrightarrow> (P' s1 \<or> Q' s1)"
  apply auto
  done

lemma all_conj_rule: "(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> P s1 \<longrightarrow> P' s1) \<and> (\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> Q s1 \<longrightarrow> Q' s1) \<Longrightarrow>
\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> (P s1 \<and> Q s1) \<longrightarrow> (P' s1 \<and> Q' s1)"
  apply auto
  done

lemma all_imp_refl: " \<forall> s1. toEnvP s1 \<and> substate s1 s \<and> P s1 \<longrightarrow> P s1"
  apply auto
  done 

end