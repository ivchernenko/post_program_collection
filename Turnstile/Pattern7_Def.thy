theory Pattern7_Def
  imports VCTheoryLemmas
begin

definition pattern8 where "pattern8 a1 a2 a3 T T1 s \<equiv>
\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s \<and> toEnvNum s1 s2 = 1 \<and> a1 s1 s2 \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s \<and> toEnvNum s2 s4 \<le> T \<and> a2 s4 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> a3 s3)) \<or>
toEnvNum s2 s \<ge> T1 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s \<and> toEnvNum s2 s3 \<le> T \<longrightarrow> a3 s3)"

lemma pattern8_simp: "
P1 \<longrightarrow> pattern8 a1 a2 a3 T T1 s0 \<Longrightarrow>
P2 \<and> a1 s0 s \<longrightarrow> a2 s \<or> T2 = 0 \<and> a3 s \<Longrightarrow>
P2 \<and> T1 < T \<longrightarrow> a2 s \<and>  T2 \<le> T+1  \<or>  T2 \<le> T1 + 1 \<and> a3 s \<Longrightarrow>
P2 \<and> T1 \<ge> T \<longrightarrow> T2 \<le> T1 + 1 \<Longrightarrow>
P2 \<longrightarrow> P1 \<Longrightarrow> toEnvP s0 \<and> toEnvP s \<and> substate s0 s \<and>  toEnvNum s0 s = 1 \<Longrightarrow>
P2 \<longrightarrow> pattern8 a1 a2 a3 T T2 s"
  apply(unfold pattern8_def)
  apply(rule impI)
  apply simp
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
    apply(cases "toEnvNum s2 s \<le> T")
    apply(erule disjE)
    using substate_trans apply blast
     apply(rotate_tac 1)
    apply(erule impE)
      apply (metis One_nat_def Suc_eq_plus1 dual_order.strict_trans1 linorder_le_less_linear not_less_eq_eq toEnvNum3)
    apply(rotate_tac -1)
    apply(erule disjE)
      apply (metis le_Suc_ex substate_refl toEnvNum_substate1 trans_le_add1)
     apply (metis (full_types) One_nat_def Suc_eq_plus1 add_le_mono dual_order.trans le_numeral_extra(4) toEnvNum3)
    apply(erule disjE)
     apply (metis substate_trans)
    by (smt (verit, del_insts) One_nat_def Suc_eq_plus1 dual_order.trans linorder_le_less_linear not_less_eq_eq toEnvNum3)
  by (metis One_nat_def substate_antisym substate_or_substate_pair substate_refl)

lemma einv2reqP8: "pattern8 a1 a2 a3 T T1 s \<Longrightarrow>
\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s \<and> toEnvNum s1 s2 = 1 \<and> a1 s1 s2 \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s \<and> toEnvNum s2 s4 \<le> T \<and> a2 s4 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> a3 s3)) \<or>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s \<and> toEnvNum s2 s3 \<le> T \<longrightarrow> a3 s3)"
  apply(unfold pattern8_def)
  by auto

definition pattern7 where "pattern7 a1 a2 a3 T T1 s \<equiv>
\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s \<and> toEnvNum s1 s2 = 1 \<and> a1 s1 s2 \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s \<and> toEnvNum s2 s4 \<le> T \<and> a2 s4 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> a3 s3)) \<or>
toEnvNum s2 s \<ge> T1 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s \<and> toEnvNum s2 s3 < T \<longrightarrow> a3 s3)"


lemma pattern7_simp: "
P1 \<longrightarrow> pattern7 a1 a2 a3 T T1 s0 \<Longrightarrow>
P2 \<and> a1 s0 s \<longrightarrow> a2 s \<or> T2 = 0 \<and> a3 s \<Longrightarrow>
T1 + 1 < T \<longrightarrow> a2 s \<or> T2 \<le> T1 + 1 \<and> a3 s \<Longrightarrow>
T1 + 1 < T2 \<and> T < T2 \<longrightarrow> T2 \<le> T + 1 \<and> a2 s \<Longrightarrow>
P2 \<longrightarrow> P1 \<Longrightarrow> toEnvP s0 \<and> toEnvP s \<and> substate s0 s \<and>  toEnvNum s0 s = 1 \<Longrightarrow>
P2 \<longrightarrow> pattern7 a1 a2 a3 T T2 s"
  apply(unfold pattern7_def)
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
      apply(simp add: substate_refl)
     apply(rule conjI)
       apply blast
      apply(rule conjI)
    using toEnvNum3[of s2 s0 s]
    apply auto[1]
    apply (metis (full_types) \<open>substate s2 s0 \<and> substate s0 s \<Longrightarrow> toEnvNum s2 s = toEnvNum s2 s0 + toEnvNum s0 s\<close> le_antisym less_add_same_cancel1 less_numeral_extra(1) nat_less_le toEnvNum_substate1)
    apply (smt (verit) \<open>substate s2 s0 \<and> substate s0 s \<Longrightarrow> toEnvNum s2 s = toEnvNum s2 s0 + toEnvNum s0 s\<close> int_ops(2) nat_int_comparison(2) nat_le_real_less nat_less_real_le zadd_int_left)
    apply(rotate_tac 1)
    apply(erule impE)
     apply (simp add: \<open>substate s2 s0 \<and> substate s0 s \<Longrightarrow> toEnvNum s2 s = toEnvNum s2 s0 + toEnvNum s0 s\<close>)
    apply(rotate_tac -1)
    apply(erule disjE)
     apply(rule disjI1)
     apply(rule exI[of _ s])
     apply (metis dual_order.strict_trans2 leI nle_le substate_refl toEnvNum_substate1)
    using \<open>substate s2 s0 \<and> substate s0 s \<Longrightarrow> toEnvNum s2 s = toEnvNum s2 s0 + toEnvNum s0 s\<close> by auto
  by (metis substate_antisym substate_or_substate_pair substate_refl)

lemma einv2reqP7: "pattern7 a1 a2 a3 T T1 s \<Longrightarrow>
\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s \<and> toEnvNum s1 s2 = 1 \<and> a1 s1 s2 \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s \<and> toEnvNum s2 s4 \<le> T \<and> a2 s4 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> a3 s3)) \<or>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s \<and> toEnvNum s2 s3 < T \<longrightarrow> a3 s3)"
  apply(unfold pattern7_def)
  by auto


end


  






 


     


    