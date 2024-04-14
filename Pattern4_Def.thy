theory Pattern4_Def
  imports Pattern1_Def Pattern2_Def
begin

definition P4 where "P4 s t A1 A2 A3 \<equiv> 
\<forall> s1 s2. substate s1 s2  \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and> toEnvNum s2 s \<ge> t \<and> A1 s1 s2 \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s \<and> toEnvNum s2 s4 \<le> t \<and> A2 s4 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> A3 s3))"

definition P4inv where "P4inv s t t1 A1 A2 A3 \<equiv>
(\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1  \<and> A1 s1 s2 \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s \<and> toEnvNum s2 s4 \<le> t \<and> A2 s4 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> A3 s3)) \<or>
toEnvNum s2 s < t1 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s \<longrightarrow> A3 s3))"

lemma P4inv_rule2: "
 P4inv s0 t t1 A1 A2 A3 \<Longrightarrow> 
A1 s0 s \<longrightarrow> A2 s \<or> A3 s \<and> t2 > 0  \<Longrightarrow>
 t1 > 0 \<longrightarrow> A2 s \<and> t1 \<le> t \<or> A3 s \<and> t1 < t2 \<Longrightarrow>
 toEnvP s0 \<and> toEnvP s  \<and> substate s0 s \<and> toEnvNum s0 s = 1 \<Longrightarrow>
 P4inv s t t2 A1 A2 A3"
  apply(rule cut_rl[of "\<forall> s1. substate s1 s \<and> toEnvP s1  \<and> s1 \<noteq> s \<longrightarrow> substate s1 s0"])
   apply(unfold P4inv_def)[1]
   apply(rule allI)+
  subgoal for s1 s2
    apply(cases "s2 = s")
    apply (smt (verit, ccfv_threshold) bot_nat_0.extremum_uniqueI diff_add_0 diff_add_inverse2 less_add_eq_less linorder_le_cases plus_1_eq_Suc substate_antisym substate_toEnvNum_id substate_trans toEnvNum3 toEnvNum_id)
      apply(rule impI)
      apply(erule allE[of _ s1])
    apply(rotate_tac -1)
      apply(erule allE[of _ s2])
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
  using substate_noteq_imp_substate_of_pred by blast

lemma einv2req: "
P4inv s t t1 A1 A2 A3 \<Longrightarrow> t1 \<le> t \<Longrightarrow>
(\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1\<and>  toEnvNum s2 s \<ge> t \<and> A1 s1 s2 \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s \<and> toEnvNum s2 s4 \<le> t \<and> A2 s4 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> A3 s3)))"
  apply(unfold P4inv_def)
  by (smt (verit, best) leD le_eq_less_or_eq order_less_trans)

lemma einv2req2: "
P4inv s t t1 A1 A2 A3 \<Longrightarrow> t1 \<le> t \<Longrightarrow> P4 s t A1 A2 A3"
  apply(unfold P4inv_def P4_def)
  by (smt (verit, best) leD le_eq_less_or_eq order_less_trans)

definition P4' where "P4' s t A1 A2 A3 A4 \<equiv>
always2 s A1 A2 (\<lambda> s2. constrained_until s2 s t A3 A4)"

definition P4'inv where "P4'inv s t t1 b A1 A2 A3 A4 \<equiv>
always2_inv s b A1 A2 (\<lambda> s2. constrained_until_inv s2 s t t1 A3 A4)"


lemma P4'inv_rule: "
 P4'inv s0 t t1 b A1 A2 A3 A4 \<Longrightarrow> 
(((b \<or> \<not> A2 s) \<or> A4 s \<or> A3 s \<and> t2 > 0)  \<and>
(t1 = 0 \<or> A4 s \<and> t1 \<le> t \<or> A3 s \<and> t1 < t2)) \<and> (b' \<longrightarrow> \<not> A1 s)  \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
 P4'inv s t t2 b' A1 A2 A3 A4"
  apply(unfold P4'inv_def)
  apply(erule always2_rule)
   apply simp
  apply(erule conjE)
  subgoal premises prems1
    apply(rule conjI)
     apply(insert prems1(1,2))[1]
     apply(erule conjE)
    subgoal premises prems2
      apply(rule conjI)
       apply(insert prems2(1,2))[1]
       apply(erule disjE)
        apply(rule disjI1)
        apply assumption
       apply(rule disjI2)
       apply(rule constrained_until_one_point)
        apply simp
       apply assumption
      apply(insert prems2(1,3))
      apply(rule constrained_until_rule)
       apply simp
      apply(rule conjI)
       apply(rule all_imp_refl)
      apply(rule conjI)
       apply simp
      apply assumption
      done
    apply(insert prems1(1,3))
    apply simp
    done
  done

lemma P4'inv_rule_gen: "
 P4'inv s0 t t1 b A1 A2 A3 A4 \<Longrightarrow> consecutive s0 s \<Longrightarrow>
(((b \<or> \<not> A2 s) \<or> A4' s \<or> A3' s \<and> t2 > 0)  \<and>
( \<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> A3 s1 \<longrightarrow> A3' s1) \<and>
( \<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> A4 s1 \<longrightarrow> A4' s1) \<and>
(t1 = 0 \<or> A4' s \<and> t1 \<le> t \<or> A3' s \<and> t1 < t2)) \<and> (b' \<longrightarrow> \<not> A1 s)  \<Longrightarrow>

 P4'inv s t t2 b' A1 A2 A3' A4'"
  apply(unfold P4'inv_def)
  apply(erule always2_rule)
   apply simp
  apply(erule conjE)
  subgoal premises prems1
    apply(rule conjI)
     apply(insert prems1(1,2))[1]
     apply(erule conjE)
    subgoal premises prems2
      apply(rule conjI)
       apply(insert prems2(1,2))[1]
       apply(erule disjE)
        apply(rule disjI1)
        apply assumption
       apply(rule disjI2)
       apply(rule constrained_until_one_point)
        apply simp
       apply assumption
      apply(insert prems2(1,3))
      apply(rule constrained_until_rule)
       apply simp
      apply assumption
      done
    apply(insert prems1(1,3))
    apply simp
    done
  done

lemma P4'_einv2req_gen: "P4'inv s t t1 b A1 A2 A3 A4 \<Longrightarrow>(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> A3 s1 \<longrightarrow> A3' s1) \<and> (\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> A4 s1 \<longrightarrow> A4' s1) \<and>
 t1 \<le> t \<Longrightarrow> P4' s t A1 A2 A3' A4'"
  apply(unfold P4'_def P4'inv_def)
  using always2_einv2req constrained_until_einv2req
  by simp


lemma P4'_einv2req: "P4'inv s t t1 b A1 A2 A3 A4 \<Longrightarrow> t1 \<le> t \<Longrightarrow> P4' s t A1 A2 A3 A4"
  apply(unfold P4'_def P4'inv_def)
  using always2_einv2req constrained_until_einv2req
  by (smt (verit, best))

end