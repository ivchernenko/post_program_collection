theory Pattern11_Def
  imports VCTheoryLemmas
begin

definition P11inv where "P11inv s A1 A2 \<equiv>
 (\<forall>s1 s2.
      substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and> A1 s1 s2 \<longrightarrow>
      (\<exists>s3 s4. toEnvP s3 \<and> toEnvP s4 \<and> substate s2 s3 \<and> substate s3 s4 \<and> substate s4 s \<and> toEnvNum s3 s4 = 1 \<and> \<not> A2 s3 s4)) "

lemma P11inv_rule: "
P1 \<longrightarrow> P11inv s0 A1 A2 \<Longrightarrow> \<not> A1 s0 s \<Longrightarrow>
P2 \<longrightarrow> P1 \<Longrightarrow> toEnvP s0 \<and> toEnvP s \<and> substate s0 s \<and> toEnvNum s0 s = 1 \<Longrightarrow>
P2 \<longrightarrow> P11inv s A1 A2"
  apply(rule impI)
  apply simp
  apply(subgoal_tac "\<forall> s1. substate s1 s \<and> toEnvP s1  \<and> s1 \<noteq> s \<longrightarrow> substate s1 s0")
   apply(unfold P11inv_def)[1]
  apply(rule allI)+
  subgoal for s1 s2
    apply(cases "s2=s")
     apply (metis One_nat_def toEnvNum_eq_imp_eq2)
    apply(erule allE[of _ s1])
    apply(rotate_tac -1)
    apply(erule allE[of _ s2])
    using substate_trans by blast
  by (metis (full_types) one_is_add substate_linear substate_toEnvNum_id toEnvNum3)

lemma P11_einv2req: "
P11inv s0 A1 A2 \<Longrightarrow>
 toEnvP s0 \<and> toEnvP s \<and>  substate s0 s \<and> toEnvNum s0 s = 1 \<Longrightarrow>
substate s1 s2 \<and>    substate s2 s0 \<and>    toEnvP s1 \<and>    toEnvP s2 \<and>    toEnvNum s1 s2 = 1 \<and>    A1 s1 s2 \<and>    A3 s0 s  \<and>
    (\<forall>s5 s6.        toEnvP s5 \<and> toEnvP s6 \<and> substate s2 s5 \<and> substate s5 s6 \<and> substate s6 s0 \<longrightarrow>        A2 s5 s6) \<longrightarrow>   A4 s"
  apply(unfold P11inv_def)
  by auto



end