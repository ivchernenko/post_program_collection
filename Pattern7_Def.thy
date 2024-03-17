theory Pattern7_Def
  imports VCTheoryLemmas
begin

definition P7inv where "P7inv s T T1 a1 a2 a3\<equiv>
\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s \<and> toEnvNum s1 s2 = 1 \<and> a1 s1 s2 \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s \<and> toEnvNum s2 s4 \<le> T \<and> a2 s4 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> a3 s3)) \<or>
toEnvNum s2 s \<ge> T1 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s \<and> toEnvNum s2 s3 \<le> T \<longrightarrow> a3 s3)"

definition P7 where "P7 s T a1 a2 a3\<equiv>
\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s \<and> toEnvNum s1 s2 = 1 \<and> a1 s1 s2 \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s \<and> toEnvNum s2 s4 \<le> T \<and> a2 s4 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> a3 s3)) \<or>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s \<and> toEnvNum s2 s3 \<le> T \<longrightarrow> a3 s3)"

lemma P7inv_rule: "
P7inv s0 T T1 a1 a2 a3 \<Longrightarrow>
 a1 s0 s \<longrightarrow> a2 s \<or> T2 = 0 \<and> a3 s \<Longrightarrow>
 T1 < T \<longrightarrow> a2 s \<and>  T2 \<le> T+1  \<or>  T2 \<le> T1 + 1 \<and> a3 s \<Longrightarrow>
T1 \<ge> T \<longrightarrow> T2 \<le> T1 + 1 \<Longrightarrow>
 toEnvP s0 \<and> toEnvP s \<and> substate s0 s \<and>  toEnvNum s0 s = 1 \<Longrightarrow>
 P7inv s T T2 a1 a2 a3"
  apply(unfold P7inv_def)
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
      apply (metis dual_order.trans le_add1 substate_refl toEnvNum3)
    apply (smt (verit, ccfv_SIG) add.assoc add.commute le_iff_add toEnvNum3)
    apply(erule disjE)
     apply (metis substate_trans)
    by (smt (verit, del_insts) One_nat_def Suc_eq_plus1 dual_order.trans linorder_le_less_linear not_less_eq_eq toEnvNum3)
  by (metis substate_noteq_imp_substate_of_pred)

  

lemma einv2req: "P7inv s t t1 A1 A2 A3 \<Longrightarrow> P7 s t A1 A2 A3"
  apply(unfold P7inv_def P7_def)
  apply auto
  done


end
