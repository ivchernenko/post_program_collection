theory Pattern8_Def
  imports VCTheoryLemmas
begin

definition P8inv where "P8inv a1 a2 a3 T T1 s \<equiv>
\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s \<and> toEnvNum s1 s2 = 1 \<and> a1 s1 s2 \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s \<and> toEnvNum s2 s4 \<le> T \<and> a2 s4 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> a3 s3)) \<or>
toEnvNum s2 s \<ge> T1 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s \<and> toEnvNum s2 s3 < T \<longrightarrow> a3 s3)"


lemma P8inv_rule: "
P1 \<longrightarrow> P8inv a1 a2 a3 T T1 s0 \<Longrightarrow>
P2 \<and> a1 s0 s \<longrightarrow> a2 s \<or> T2 = 0 \<and> a3 s \<Longrightarrow>
T1 + 1 < T \<longrightarrow> a2 s \<or> T2 \<le> T1 + 1 \<and> a3 s \<Longrightarrow>
T1 + 1 < T2 \<and> T < T2 \<longrightarrow> T2 \<le> T + 1 \<and> a2 s \<Longrightarrow>
P2 \<longrightarrow> P1 \<Longrightarrow> toEnvP s0 \<and> toEnvP s \<and> substate s0 s \<and>  toEnvNum s0 s = 1 \<Longrightarrow>
P2 \<longrightarrow> P8inv a1 a2 a3 T T2 s"
  apply(unfold P8inv_def)
  apply(rule impI)
  apply (simp del: One_nat_def)
  apply(subgoal_tac "\<forall> s1. substate s1 s \<and> toEnvP s1  \<and> s1 \<noteq> s \<longrightarrow> substate s1 s0")
  apply(rule allI)+
  subgoal for s1 s2
    apply(cases "s2=s")
     apply (metis bot_nat_0.extremum substate_antisym toEnvNum_eq_imp_eq2 toEnvNum_id)
    apply(erule allE[of _ s1])
     apply(rotate_tac -1)
     apply(erule allE[of _ s2])
     apply(rotate_tac -1)
    apply(rule impI)
    apply(erule impE)
     apply blast
    apply(erule disjE)
    using substate_trans apply blast
    apply(cases "toEnvNum s2 s \<ge> T")
    apply(cases "toEnvNum s2 s \<ge> T2")
    apply (metis leD)
     apply(rule disjI1)
     apply(rule exI[of _ s])
     apply(subgoal_tac "toEnvNum s2 s \<le> T")
     apply(rule conjI)
      apply simp
     apply(rule conjI)
      apply simp
     apply(rule conjI)
      apply(simp)
     apply(rule conjI)
       apply blast
      apply(rule conjI)
    using toEnvNum3[of s2 s0 s]
    apply auto[1]
    apply (smt (verit) add.commute add_le_same_cancel2 leI nle_le not_add_less1 not_one_le_zero toEnvNum3)
     apply (smt (verit) \<open>substate s2 s0 \<and> substate s0 s \<Longrightarrow> toEnvNum s2 s = toEnvNum s2 s0 + toEnvNum s0 s\<close> int_ops(2) nat_int_comparison(2) nat_le_real_less nat_less_real_le zadd_int_left)
    apply(rotate_tac 1)
    apply(erule impE)
     apply (simp add: \<open>substate s2 s0 \<and> substate s0 s \<Longrightarrow> toEnvNum s2 s = toEnvNum s2 s0 + toEnvNum s0 s\<close>)
    apply(rotate_tac -1)
    apply(erule disjE)
     apply(rule disjI1)
     apply(rule exI[of _ s])
    using toEnvNum3 apply force
    using \<open>substate s2 s0 \<and> substate s0 s \<Longrightarrow> toEnvNum s2 s = toEnvNum s2 s0 + toEnvNum s0 s\<close> by auto
  by (smt (verit, ccfv_threshold) add_cancel_right_right le_neq_implies_less less_one linorder_le_less_linear substate_linear substate_toEnvNum_id toEnvNum3 trans_less_add1)

lemma einv2req: "P8inv a1 a2 a3 T T1 s \<Longrightarrow>
\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s \<and> toEnvNum s1 s2 = 1 \<and> a1 s1 s2 \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s \<and> toEnvNum s2 s4 \<le> T \<and> a2 s4 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> a3 s3)) \<or>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s \<and> toEnvNum s2 s3 < T \<longrightarrow> a3 s3)"
  apply(unfold P8inv_def)
  by auto

end
