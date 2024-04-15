theory Pattern1_Def
  imports Pattern3_Def
begin

definition P1inv where "P1inv s t t1 A1 A2 A3 \<equiv>
(\<forall> s1. substate s1 s \<and> toEnvP s1 \<and> A1 s1 \<longrightarrow>
(\<exists> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s \<and> toEnvNum s1 s3 \<le> t \<and> A2 s3 \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s3 \<and> s2 \<noteq> s3 \<longrightarrow> A3 s2)) \<or>
toEnvNum s1 s < t1 \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s \<longrightarrow> A3 s2))"

lemma P1inv_rule: "
 P1inv s0 t t1 A1 A2 A3 \<Longrightarrow> 
 A1 s \<longrightarrow> A2 s \<or> A3 s \<and> t2 > 0  \<Longrightarrow>
 t1 > 0 \<longrightarrow> A2 s \<and> t1 \<le> t \<or> A3 s \<and> t1 < t2 \<Longrightarrow>
toEnvP s0 \<and> toEnvP s  \<and> substate s0 s \<and> toEnvNum s0 s = 1 \<Longrightarrow>
 P1inv s t t2 A1 A2 A3"
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
    by (metis substate_noteq_imp_substate_of_pred)

definition P1 where "P1 s t A1 A2 A3 \<equiv>
\<forall> s1. substate s1 s \<and> toEnvP s1 \<and> toEnvNum s1 s \<ge> t \<and> A1 s1 \<longrightarrow>
(\<exists> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s \<and> toEnvNum s1 s3 \<le> t \<and> A2 s3 \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s3 \<and> s2 \<noteq> s3 \<longrightarrow> A3 s2))"

lemma einv2req: "P1inv s t t1 A1 A2 A3 \<Longrightarrow> t1 \<le> t \<Longrightarrow> P1 s t A1 A2 A3"
  apply(unfold P1inv_def P1_def)
  apply auto
  done

definition constrained_until where "constrained_until s1 s t A1 A2 \<equiv>
toEnvNum s1 s \<ge> t \<longrightarrow>
(\<exists> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s \<and> toEnvNum s1 s3 \<le> t \<and> A2 s3 \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s3 \<and> s2 \<noteq> s3 \<longrightarrow> A1 s2))"

definition constrained_until_inv where "constrained_until_inv s1 s t t1 A1 A2 \<equiv>
(\<exists> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s \<and> toEnvNum s1 s3 \<le> t \<and> A2 s3 \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s3 \<and> s2 \<noteq> s3 \<longrightarrow> A1 s2)) \<or>
toEnvNum s1 s < t1 \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s \<longrightarrow> A1 s2)"

lemma constrained_until_rule: "
consecutive s0 s \<Longrightarrow>
(\<forall> s1. toEnvP s1 \<and>  substate s1 s0 \<and> A1 s1 \<longrightarrow> A1' s1) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s0 \<and> A2 s1 \<longrightarrow> A2' s1) \<and>
 (t1 = 0 \<or> A2' s \<and> t1 \<le> t \<or> A1' s \<and> t1 < t1') \<Longrightarrow>
\<forall> s1. toEnvP s1 \<and>  substate s1 s0 \<and> constrained_until_inv s1 s0 t t1 A1 A2 \<longrightarrow> constrained_until_inv s1 s t t1' A1' A2'"
  apply(unfold constrained_until_inv_def)
  apply(rule allI)
  subgoal for s1
    apply(rule impI)
    apply(erule conjE)+
    apply(rotate_tac -1)
    apply(erule disjE)
     apply (metis consecutive.elims(2) substate_trans)
    apply(erule disjE)
     apply simp
    apply(erule disjE)
     apply(rule disjI1)
     apply(rule exI[of _ s])
     apply(rule conjI)
      apply simp
     apply(rule conjI)
    apply simp
      apply (meson substate_trans)
     apply(rule conjI)
      apply simp
     apply(rule conjI)
    using toEnvNum3 apply auto[1]
     apply(rule conjI)
      apply simp
     apply (metis consecutive.elims(2) substate_noteq_imp_substate_of_pred)
    using toEnvNum3
    by (smt (verit, ccfv_SIG) consecutive.elims(2) less_imp_add_positive less_numeral_extra(3) less_one linorder_neqE_nat nat_add_left_cancel_less substate_noteq_imp_substate_of_pred trans_less_add1 zero_less_one)
  done

lemma constrained_until_einv2req: "
(\<forall> s1. toEnvP s1 \<and>  substate s1 s \<and> A1 s1 \<longrightarrow> A1' s1) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> A2 s1 \<longrightarrow> A2' s1) \<and>
t1 \<le> t \<Longrightarrow>
\<forall> s1. toEnvP s1 \<and>  substate s1 s \<and> constrained_until_inv s1 s t t1 A1 A2 \<longrightarrow> constrained_until s1 s t A1' A2'"
  apply(unfold constrained_until_inv_def constrained_until_def)
  by (metis dual_order.trans substate_trans verit_comp_simplify1(3))

lemma constrained_until_one_point: "
toEnvP s \<Longrightarrow>A2 s \<or> A1 s \<and> t1 > 0 \<Longrightarrow> constrained_until_inv s s t t1 A1 A2"
  apply(unfold constrained_until_inv_def)
  by (metis less_eq_nat.simps(1) substate_antisym substate_refl toEnvNum_id)

definition P1'inv where "P1'inv s t t1 A1 A3 A2 \<equiv> 
always s (\<lambda> s1.  A1 s1 \<longrightarrow> constrained_until_inv s1 s t t1 A3 A2)"

definition P1' where "P1' s t A1 A3 A2 \<equiv> 
always s (\<lambda> s1.  A1 s1 \<longrightarrow> constrained_until s1 s t A3 A2)"

lemma P1'einv2req: "P1'inv s t t1 A1 A2 A3 \<Longrightarrow> t1 \<le> t \<Longrightarrow> P1' s t A1 A2 A3"
  apply(unfold P1'inv_def P1'_def)
  using always_einv2req constrained_until_einv2req
  by (smt (verit, ccfv_SIG))

lemma P1'inv_rule_gen: "
 P1'inv s0 t t1 A1 A3 A2 \<Longrightarrow> consecutive s0 s \<Longrightarrow>
(\<not> A1 s \<or> A2' s \<or> A3' s \<and> t2 > 0)  \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s0 \<and> A3 s1 \<longrightarrow> A3' s1) \<and> (\<forall> s1. toEnvP s1 \<and> substate s1 s0 \<and> A2 s1 \<longrightarrow> A2' s1) \<and>  (t1 = 0 \<or> A2' s \<and> t1 \<le> t \<or> A3' s \<and> t1 < t2) \<Longrightarrow>
 P1'inv s t t2 A1 A3' A2'"
  apply(unfold P1'inv_def)
  apply(simp only: imp_conv_disj)
  apply(erule always_rule)
  apply simp
   apply(erule conjE)
  subgoal premises prems1
    apply(rule conjI)
     apply(insert prems1(1,2))[1]
     apply(erule disjE)
      apply(rule disjI1)
      apply assumption (*apply simp*)
     apply(rule disjI2)
     apply(rule constrained_until_one_point)
      apply simp
     apply assumption (*apply simp*)
    apply(insert prems1(1,3))[1]
    apply(rule all_disj_rule)
    apply(rule conjI)
     apply simp
    apply(rule constrained_until_rule)
     apply simp
    apply simp
    done
  done

lemma P1'inv_rule: "
 P1'inv s0 t t1 A1 A3 A2 \<Longrightarrow> consecutive s0 s \<Longrightarrow>
(\<not> A1 s \<or> A2 s \<or> A3 s \<and> t2 > 0)  \<and>
(t1 = 0 \<or> A2 s \<and> t1 \<le> t \<or> A3 s \<and> t1 < t2) \<Longrightarrow>
 P1'inv s t t2 A1 A3 A2"
  using P1'inv_rule_gen by simp

lemma P1'einv2req_gen: "P1'inv s t t1 A1 A2 A3 \<Longrightarrow> (\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> A2 s1 \<longrightarrow> A2' s1) \<and> (\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> A3 s1 \<longrightarrow> A3' s1) \<and>
 t1 \<le> t \<Longrightarrow> P1' s t A1 A2' A3'"
  apply(unfold P1'inv_def P1'_def)
  using always_einv2req constrained_until_einv2req
  by (smt (verit, ccfv_SIG))

end


