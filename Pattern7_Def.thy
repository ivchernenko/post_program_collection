theory Pattern7_Def
  imports Pattern2_Def
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

definition constrained_weak_until where "constrained_weak_until s1 s t A1 A2 \<equiv>
(\<exists> s4. toEnvP s4 \<and> substate s1 s4 \<and> substate s4 s \<and> toEnvNum s1 s4 \<le> t \<and> A2 s4 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> A1 s3)) \<or>
(\<forall> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s \<and> toEnvNum s1 s3 \<le> t \<longrightarrow> A1 s3)"

definition constrained_weak_until_inv where "constrained_weak_until_inv s1 s t t1 A1 A2 \<equiv>
(\<exists> s4. toEnvP s4 \<and> substate s1 s4 \<and> substate s4 s \<and> toEnvNum s1 s4 \<le> t \<and> A2 s4 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> A1 s3)) \<or>
toEnvNum s1 s \<ge> t1 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s \<and> toEnvNum s1 s3 \<le> t \<longrightarrow> A1 s3)"

lemma constrained_weak_until_one_point: "toEnvP s \<Longrightarrow> A2 s \<or> t1 = 0 \<and> A1 s \<Longrightarrow> constrained_weak_until_inv s s t t1 A1 A2"
  apply(unfold constrained_weak_until_inv_def)
  by (metis substate_antisym substate_refl toEnvNum_id zero_le)

lemma constrained_weak_until_rule: " consecutive s0 s \<Longrightarrow>
(\<forall> s1. toEnvP s1 \<and> substate s1 s0 \<and> A1 s1 \<longrightarrow> A1' s1) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s0 \<and> A2 s1 \<longrightarrow> A2' s1) \<and>
(t1 < t \<and> (A2' s \<and>  t1' \<le> t+1  \<or>  t1' \<le> t1 + 1 \<and> A1' s) \<or> t1 \<ge> t \<and> t1' \<le> t1 + 1) \<Longrightarrow>
(\<forall> s1. toEnvP s1 \<and> substate s1 s0 \<and> constrained_weak_until_inv s1 s0 t t1 A1 A2 \<longrightarrow> constrained_weak_until_inv s1 s t t1' A1' A2')"
  apply(unfold constrained_weak_until_inv_def)
  apply(rule allI)
  subgoal for s1
    apply(rule impI)
    apply(erule conjE)+
    apply(rotate_tac -1)
    apply(erule disjE)
     apply (metis consecutive.simps substate_trans)
    apply(erule disjE)
     apply(erule conjE)+
     apply(erule disjE)
    apply(cases "toEnvNum s1 s0 < t")
      apply(rule disjI1)
      apply(rule exI[of _ s])
      apply(rule conjI)
       apply simp
      apply(rule conjI)
       apply (meson consecutive.elims(2) substate_trans)
      apply(rule conjI)
       apply simp
      apply(rule conjI)
        apply (metis Suc_eq_plus1 add_mono1 consecutive.simps less_Suc_eq_le toEnvNum3)
       apply(rule conjI)
        apply simp
       apply (metis consecutive.elims(2) le_Suc_ex less_or_eq_imp_le substate_noteq_imp_substate_of_pred toEnvNum3 trans_le_add1)
    apply(rule disjI2)
      apply (smt (verit, ccfv_SIG) add.commute consecutive.elims(2) leD leI le_iff_add le_neq_implies_less le_numeral_extra(4) le_trans less_add_one nat_add_left_cancel_le nat_le_linear order.strict_trans1 substate_noteq_imp_substate_of_pred toEnvNum3)
    apply (smt (verit, best) add.commute consecutive.elims(2) nat_add_left_cancel_le order_subst1 substate_noteq_imp_substate_of_pred toEnvNum3)
    apply(rule disjI2)
    apply(rule conjI)
    using toEnvNum3 apply fastforce
    by (metis consecutive.elims(2) dual_order.trans leD less_add_one substate_noteq_imp_substate_of_pred toEnvNum3)
  done

lemma constrained_weak_until_einv2req: "
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> A1 s1 \<longrightarrow> A1' s1) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> A2 s1 \<longrightarrow> A2' s1) \<Longrightarrow>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> constrained_weak_until_inv s1 s t t1 A1 A2 \<longrightarrow> constrained_weak_until s1 s t A1' A2')"
  apply(unfold constrained_weak_until_inv_def constrained_weak_until_def)
  by (meson substate_trans)

definition P7_2 where "P7_2 s t A1 A2 A3 A4 A5 \<equiv>
always2 s A1 A2 (\<lambda> s2. constrained_weak_until s2 s t A3 (\<lambda> s4. previous_ex s4 A4 \<and> A5 s4))"

definition P7_2inv where "P7_2inv s t t1 b1 b2 A1 A2 A3 A4 A5 \<equiv>
always2_inv s b1 A1 A2 (\<lambda> s2. constrained_weak_until_inv s2 s t t1 A3 (\<lambda> s4. previous_ex s4 A4 \<and> A5 s4)) \<and>  (b2 \<longrightarrow> A4 s)" 

lemma P7_2_rule: "
P7_2inv s0 t t1 b1 b2 A1 A2 A3 A4 A5 \<Longrightarrow>consecutive s0 s \<Longrightarrow>
 (((( b1 \<or> \<not> A2 s)  \<or> b2 \<and> A5 s \<or> t1' = 0 \<and> A3 s) \<and> 
(t1 < t \<and> ((b2 \<and> A5 s) \<and>  t1' \<le> t+1  \<or>  t1' \<le> t1 + 1 \<and> A3 s) \<or> t1 \<ge> t \<and> t1' \<le> t1 + 1)) \<and> (b1' \<longrightarrow> \<not> A1 s)) \<and> (b2' \<longrightarrow> A4 s) \<Longrightarrow>
P7_2inv s t t1' b1' b2' A1 A2 A3 A4 A5"
  apply(unfold P7_2inv_def)
  apply(erule conjE)
  apply(erule conjE)
  subgoal premises prems1
    apply(rule conjI)
     apply(insert prems1(1,2,4))[1]
     apply(erule always2_rule)
      apply simp
     apply(erule conjE)
    subgoal premises prems2
      apply(rule conjI)
       apply(insert prems2(1,2))[1]
       apply(erule conjE)
      subgoal premises prems3
        apply(rule conjI)
         apply(insert prems3(1,2))[1]
         apply(erule disjE)
          apply(rule disjI1)
          apply assumption
         apply(rule disjI2)
         apply(rule constrained_weak_until_one_point)
          apply simp
         apply(erule disjE)
          apply(rule disjI1)
          apply(erule conjE)
        subgoal premises prems4
          apply(rule conjI)
           apply(insert prems4(1,2))[1]
           apply(rule previous_ex_one_point[of s0])
            apply simp
           apply (simp add: prems1(3))
          apply(insert prems4(1,3))
          apply assumption
          done
         apply(rule disjI2)
         apply assumption
        apply(insert prems3(1,3))
        apply(rule constrained_weak_until_rule)
         apply simp
        apply(rule conjI)
         apply simp
        apply(rule conjI)
         apply simp
        apply(erule disjE)
         apply(rule disjI1)
         apply(erule conjE)
        subgoal premises prems4
          apply(rule conjI)
           apply(insert prems4(1,2))[1]
           apply assumption
          apply(insert prems4(1,3))
          apply(erule disjE)
           apply(rule disjI1)
           apply(erule conjE)
          subgoal premises prems5
            apply(rule conjI)
             apply(insert prems5(1,2))[1]
             apply(erule conjE)
            subgoal premises prems6
              apply(rule conjI)
               apply(insert prems6(1,2))[1]
               apply(rule previous_ex_one_point[of s0])
              apply simp
               apply (simp add: prems1(3))
              apply(insert prems6(1,3))
              apply assumption
              done
            apply(insert prems5(1,3))
            apply assumption
            done
          apply(rule disjI2)
          apply assumption
          done
        apply(rule disjI2)
        apply assumption
        done
      apply(insert prems2(1,3))
      apply simp
      done
    apply(insert prems1(1,3,5))
    apply simp
    done
  done

lemma P7_2_einv2req: "P7_2inv s t t1 b1 b2  A1 A2 A3 A4 A5 \<Longrightarrow> P7_2 s t A1 A2 A3 A4 A5"
  apply(unfold P7_2inv_def P7_2_def)
  using always2_einv2req constrained_weak_until_einv2req
  by (smt (verit, ccfv_SIG))

end
