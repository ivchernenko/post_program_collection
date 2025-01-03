theory Pattern5_Def
  imports Pattern2_Def
begin

definition P5inv where "P5inv s t t1 A1 A2 \<equiv>
\<forall> s1 s2 s3. substate s1 s2 \<and> substate s2 s3  \<and> substate s3 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvP s2 \<and> toEnvP s3 \<and> toEnvNum s1 s2 = 1 \<and> toEnvNum s2 s3 < t \<and> A1 s1 s2\<longrightarrow>
toEnvNum s2 s \<ge> t1 \<and> A2 s3"

lemma P5inv_rule: "
P1 \<longrightarrow> P5inv s0 t t1 A1 A2 \<Longrightarrow>
P2 \<and> t >0 \<and> A1 s0 s \<longrightarrow> t2 = 0 \<and> A2 s \<Longrightarrow>
P1 \<and> A2 s0 \<and> t1 + 1 < t \<longrightarrow>  A2 s \<Longrightarrow> t2 \<le> t1 + 1 \<Longrightarrow>
P2 \<longrightarrow> P1  \<Longrightarrow> toEnvP s0 \<and> toEnvP s \<and> substate s0 s \<and> toEnvNum s0 s = 1 \<Longrightarrow> 
P2 \<longrightarrow> P5inv s t t2 A1 A2"
  apply(rule impI)
  apply simp
  apply(unfold P5inv_def)
  apply(rule allI)+
  subgoal for s1 s2 s3
    apply(cases "s2 = s")
     apply (metis One_nat_def le_numeral_extra(3) substate_antisym toEnvNum_eq_imp_eq2 toEnvNum_id)
  apply(rule cut_rl[of "\<forall> s1. substate s1 s \<and> toEnvP s1  \<and> s1 \<noteq> s \<longrightarrow> substate s1 s0"])
    apply(cases "s3 = s")
    apply(rule impI)
      apply(erule allE[of _   s1])
     apply(rotate_tac -1)
      apply(erule allE[of _ s2])
     apply(rotate_tac -1)
     apply(erule allE[of _ s0])
     apply(rotate_tac -1)
    apply(erule impE)
    apply (metis One_nat_def dual_order.strict_trans less_add_one toEnvNum3)
    apply (smt (verit, del_insts) One_nat_def Suc_eq_plus1 add_le_mono dual_order.strict_trans2 dual_order.trans le_numeral_extra(4) toEnvNum3)
    apply(rule impI)
      apply(erule allE[of _   s1])
     apply(rotate_tac -1)
      apply(erule allE[of _ s2])
     apply(rotate_tac -1)
     apply(erule allE[of _ s3])
     apply(rotate_tac -1)
    apply(erule impE)
    apply presburger
    apply (smt (verit) One_nat_def Suc_eq_plus1 add_le_mono dual_order.trans le_numeral_extra(4) substate_trans toEnvNum3)
    by (metis (full_types) add_is_1 substate_linear substate_toEnvNum_id toEnvNum3)
  done

lemma einv2req: "P5inv s t t1 A1 A2 \<Longrightarrow>
\<forall> s1 s2 s3. substate s1 s2 \<and> substate s2 s3 \<and> substate s3 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvP s3 \<and> toEnvNum s1 s2 = 1 \<and> toEnvNum s2 s3 < t \<and> A1 s1 s2 \<longrightarrow> A2 s3"
  apply(unfold P5inv_def)
  by auto

definition constrained_always where "constrained_always s1 s t A \<equiv>
\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s \<and> toEnvNum s1 s2 < t \<longrightarrow> A s2"

definition constrained_always_inv where "constrained_always_inv s1 s t t1 A \<equiv>
t = 0 \<or>toEnvNum s1 s \<ge> t1 \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s \<and> toEnvNum s1 s2 < t \<longrightarrow> A s2)"

lemma constrained_always_rule: "consecutive s0 s \<Longrightarrow>
t = 0 \<or> (\<forall> s1. toEnvP s1 \<and> substate s1 s0 \<and> A s1 \<longrightarrow> A' s1) \<and>
(t1 + 1 \<ge> t \<or> A' s) \<and> t1' \<le> t1 + 1 \<Longrightarrow>
(\<forall> s1. toEnvP s1 \<and> substate s1 s0 \<and> constrained_always_inv s1 s0 t t1 A \<longrightarrow> constrained_always_inv s1 s t t1' A')"
  apply(unfold constrained_always_inv_def)
  apply(cases "t = 0")
   apply simp_all
  by (smt (verit) One_nat_def Suc_eq_plus1 dual_order.trans leD not_less_eq_eq substate_noteq_imp_substate_of_pred toEnvNum3)

lemma constrained_always_one_point: "t = 0 \<or> t1 = 0 \<and> ( A s) \<Longrightarrow> constrained_always_inv s s t t1 A"
  apply(unfold constrained_always_inv_def)
  using substate_antisym by blast

lemma constrained_always_einv2req: "
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> A s1 \<longrightarrow> A' s1) \<Longrightarrow>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> constrained_always_inv s1 s t t1 A \<longrightarrow> constrained_always s1 s t A')"
  apply(unfold constrained_always_inv_def constrained_always_def)
  apply auto
  done

definition P5_2 where "P5_2 s t A1 A2 A3 \<equiv>
always2 s A1 A2 (\<lambda> s2. constrained_always s2 s t A3)"

definition P5_2inv where "P5_2inv s t t1 b A1 A2 A3 \<equiv>
always2_inv s b A1 A2 (\<lambda> s2. constrained_always_inv s2 s t t1 A3)"

lemma P5_2_rule: "
P5_2inv s0 t t1 b A1 A2 A3 \<Longrightarrow>consecutive s0 s \<Longrightarrow> (((b \<or> \<not> A2 s) \<or> t = 0 \<or> t1' = 0 \<and> A3 s) \<and> (t = 0 \<or>(t1 + 1 \<ge> t \<or> A3 s) \<and> t1' \<le> t1 + 1)) \<and> (b' \<longrightarrow> \<not> A1 s) \<Longrightarrow>
P5_2inv s t t1' b' A1 A2 A3"
  apply(unfold P5_2inv_def)
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
       apply(rule constrained_always_one_point)
       apply assumption
      apply(insert prems2(1,3))
      apply(rule constrained_always_rule)
      apply simp
      apply simp
      done
    apply(insert prems1(1,3))
    apply simp
    done
  done

lemma P5_2_einv2req: "P5_2inv s t t1 b A1 A2 A3 \<Longrightarrow> P5_2 s t A1 A2 A3"
  apply(unfold P5_2inv_def P5_2_def)
  using always2_einv2req constrained_always_einv2req
  by (metis (no_types, lifting))

definition P5_1 where "P5_1 s t A1 A2 \<equiv>
always s (\<lambda> s1. A1 s1 \<longrightarrow> constrained_always s1 s t A2)"

definition P5_1inv where "P5_1inv s t t1 A1 A2 \<equiv>
always s (\<lambda> s1. A1 s1 \<longrightarrow> constrained_always_inv s1 s t t1 A2)"

lemma P5_1_rule: "
P5_1inv s0 t t1 A1 A2 \<Longrightarrow>consecutive s0 s \<Longrightarrow> ((( \<not> A1 s) \<or> t = 0 \<or> t1' = 0 \<and> A2 s) \<and> (t = 0 \<or>(t1 + 1 \<ge> t \<or> A2 s) \<and> t1' \<le> t1 + 1)) \<Longrightarrow>
P5_1inv s t t1' A1 A2"
  apply(unfold P5_1inv_def)
  apply(simp only: imp_conv_disj)
  apply(erule always_rule)
   apply simp
  apply(erule conjE)
  subgoal premises prems1
    apply(rule conjI)
     apply(insert prems1(1,2))[1]
     apply(erule disjE)
      apply(rule disjI1)
      apply assumption
     apply(rule disjI2)
     apply(rule constrained_always_one_point)
     apply assumption
    apply(insert prems1(1,3))
    apply(rule all_disj_rule)
    apply(rule conjI)
     apply simp
    apply(rule constrained_always_rule)
     apply simp
    apply simp
    done
  done

lemma P5_1_einv2req: "P5_1inv s t t1  A1 A2 \<Longrightarrow> P5_1 s t A1 A2"
  apply(unfold P5_1inv_def P5_1_def)
  using always_einv2req constrained_always_einv2req
  by (smt (verit, ccfv_SIG))

end
