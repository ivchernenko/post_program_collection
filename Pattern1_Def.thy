theory Pattern1_Def
  imports VCTheoryLemmas
begin

definition P1inv where "P1inv s t t1 A1 A2 A3 \<equiv>
(\<forall> s1. substate s1 s \<and> toEnvP s1 \<and> A1 s1 \<longrightarrow>
(\<exists> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s \<and> toEnvNum s1 s3 \<le> t \<and> A2 s3 \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s3 \<and> s2 \<noteq> s3 \<longrightarrow> A3 s2)) \<or>
toEnvNum s1 s < t1 \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s \<longrightarrow> A3 s2))"

lemma P1inv_simp: "
P1 \<longrightarrow> P1inv s0 t t1 A1 A2 A3 \<Longrightarrow> 
P2 \<and> A1 s \<longrightarrow> A2 s \<or> A3 s \<and> t2 > 0  \<Longrightarrow>
P2 \<and> t1 > 0 \<longrightarrow> A2 s \<and> t1 \<le> t \<or> A3 s \<and> t1 < t2 \<Longrightarrow>
P2 \<longrightarrow> P1 \<Longrightarrow> toEnvP s0 \<and> toEnvP s  \<and> substate s0 s \<and> toEnvNum s0 s = 1 \<Longrightarrow>
P2 \<longrightarrow> P1inv s t t2 A1 A2 A3"
  apply(rule impI)
  apply simp
  apply(rule cut_rl[of "\<forall> s1. substate s1 s \<and> toEnvP s1  \<and> s1 \<noteq> s \<longrightarrow> substate s1 s0"])
   apply(unfold P1inv_def)[1]
      apply(rule allI)
    subgoal for s1
      apply(cases "s1 = s")
       apply (metis substate_antisym toEnvNum_id zero_le) 
      apply(rule impI)
      apply(erule allE[of _ s1])
      apply(rotate_tac -1)
      apply(erule impE)
       apply blast
      apply(erule disjE)
      using substate_trans apply blast
      apply(rotate_tac 1)
      apply(erule impE)
       apply simp
      apply(rotate_tac -1)
      apply(erule disjE)
       apply(rule disjI1)
       apply(rule exI[of _ s])
      apply (metis One_nat_def Suc_eq_plus1 Suc_leI dual_order.trans substate_refl toEnvNum3)
      by (metis One_nat_def Suc_eq_plus1 less_trans_Suc toEnvNum3)
    by (metis (full_types) add_is_1 substate_linear substate_toEnvNum_id toEnvNum3)

lemma einv2req: "
P1inv s t t1 A1 A2 A3 \<Longrightarrow> t1 \<le> t \<Longrightarrow>
(\<forall> s1. substate s1 s \<and> toEnvP s1  \<and> toEnvNum s1 s \<ge> t \<and> A1 s1 \<longrightarrow>
(\<exists> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s \<and> toEnvNum s1 s3 \<le> t \<and> A2 s3 \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s3 \<and> s2 \<noteq> s3 \<longrightarrow> A3 s2)))"
  apply(unfold P1inv_def)
  by auto

end
