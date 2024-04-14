theory Pattern9_def
  imports Pattern4_Def Pattern5_Def
begin

definition P9inv where "P9inv A1 A2 A3 t1 t11 t2 t21 s \<equiv>
(\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and> A1 s1 s2 \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s \<and> toEnvNum s2 s4 \<le> t1 \<and> toEnvNum s4 s \<ge> t21 \<and> A2 s4 \<and>
(\<forall> s5. toEnvP s5 \<and> substate s4 s5 \<and> substate s5 s \<and> toEnvNum s4 s5 < t2 \<longrightarrow> A3 s5) \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>\<not> A2 s3)) \<or>
toEnvNum s2 s < t11 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s \<longrightarrow>\<not> A2 s3))"


lemma P9inv_simp:
" P9inv A1 A2 A3 t1 t11 t2 t21 s0 \<Longrightarrow>
  A1 s0 s \<longrightarrow> A2 s \<and> t22 = 0 \<and> (t2 > 0 \<longrightarrow> A3 s) \<or> t12 > 0 \<and> \<not> A2 s \<Longrightarrow>
 t22 \<le> t21 + 1  \<Longrightarrow>
 t21 + 1 < t2 \<longrightarrow> A3 s \<Longrightarrow>
 t11 > 0 \<and> t12 \<le> t11 \<longrightarrow> t11 \<le> t1 \<and> A2 s \<and> t22 = 0 \<and> (t2 > 0 \<longrightarrow> A3 s) \<Longrightarrow>
 t11 > 0 \<and> A2 s \<longrightarrow> (t11 \<le> t1 \<or> t12 \<le> t1 + 1) \<and>  t22 = 0 \<and> (t2 > 0 \<longrightarrow> A3 s) \<Longrightarrow>
 toEnvP s0 \<and> toEnvP s \<and> substate s0 s \<and>  toEnvNum s0 s = 1 \<Longrightarrow>
 P9inv A1 A2 A3 t1 t12 t2 t22 s"
  apply(unfold P9inv_def)
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
    apply(rotate_tac -1)
    apply(erule disjE)
     apply(erule exE)
    subgoal for s4
      apply(rule disjI1)
      apply(rule exI[of _ s4])
      by (smt (verit) add_mono_thms_linordered_semiring(3) dual_order.strict_trans2 dual_order.trans substate_trans toEnvNum3)
    apply(subgoal_tac "t11 > 0")
     apply(cases "toEnvNum s2 s \<ge> t12")
      apply(rule disjI1)
      apply(rule exI[of _ s])
      apply(rotate_tac 3)
      apply(erule impE)
       apply (smt (verit, ccfv_SIG) add_less_cancel_left dual_order.trans ex_least_nat_le less_imp_add_positive less_one less_or_eq_imp_le linorder_not_le nat_le_linear toEnvNum3)
      apply(rule conjI)
       apply simp
      apply(rule conjI)
       apply simp
      apply(rule conjI)
       apply simp
      apply(rule conjI)
    apply(subgoal_tac "toEnvNum s2 s \<le> t11")
    apply (metis dual_order.trans)
    apply (smt (verit, del_insts) Suc_eq_plus1_left add.commute less_imp_Suc_add nat_arith.suc1 nat_le_iff_add toEnvNum3)
      apply(rule conjI)
       apply simp
      apply(rule conjI)
       apply simp
    apply(rule conjI)
    apply (metis substate_antisym toEnvNum_id)
    apply presburger
     apply(cases "A2 s")
      apply(rule disjI1)
      apply(rule exI[of _ s])
      apply(rule conjI)
       apply simp
      apply(rule conjI)
       apply simp
      apply(rule conjI)
       apply simp
      apply(rule conjI)
    apply (metis (no_types, lifting) Suc_eq_plus1 add_mono1 dual_order.strict_trans1 less_Suc_eq_le not_less_eq_eq toEnvNum3)
      apply(rule conjI)
    apply simp
      apply(rule conjI)
       apply simp
      apply(rule conjI)
    apply (metis substate_antisym toEnvNum_id)
    apply presburger
     apply (metis linorder_le_less_linear)
    by auto
  by (smt (verit, ccfv_threshold) less_one nless_le not_add_less2 substate_linear substate_refl toEnvNum3 toEnvNum_eq_imp_eq2 verit_comp_simplify1(3))


lemma einv2req: "P9inv A1 A2 A3 t1 t11 t2 t21 s \<Longrightarrow> t11 \<le> t1 \<and> t21 < t2 \<Longrightarrow>
(\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and> toEnvNum s2 s \<ge> t1 \<and>
 A1 s1 s2 \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s \<and> toEnvNum s2 s4 \<le> t1 \<and> A2 s4 \<and>
(\<forall> s5. toEnvP s5 \<and> substate s4 s5 \<and> substate s5 s \<and> toEnvNum s4 s5 < t2 \<longrightarrow> A3 s5) \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> \<not> A2 s3)))"
    apply(unfold P9inv_def)
  by (smt (verit, del_insts) leD le_zero_eq nle_le order_le_less_trans substate_refl toEnvNum_id)
  
definition P9' where "P9' s t1 t2 A1 A2 A3 A4 \<equiv> P4' s t1 A1 A2 (\<lambda> s2. \<not> A3 s2) (\<lambda> s3. A3 s3 \<and> constrained_always s3 s t2 A4)"

definition P9'inv where "P9'inv s t1 t2 t11 t21 b1 A1 A2 A3 A4 \<equiv> P4'inv s t1 t11 b1 A1 A2 (\<lambda> s2. \<not> A3 s2) (\<lambda> s3. A3 s3 \<and> constrained_always_inv s3 s t2 t21 A4)" 

lemma P9'inv_rule: "
 P9'inv s0 t1 t2 t11 t21 b A1 A2 A3 A4 \<Longrightarrow> 
(((b \<or> \<not> A2 s) \<or> (A3 s \<and> (t2 = 0 \<or> t21' = 0 \<and> ( A4 s) )) \<or> \<not> A3 s \<and> t11' > 0)  \<and>
( t2 = 0 \<or> (t21 + 1 \<ge> t2 \<or> A4 s) \<and> t21' \<le> t21 + 1) \<and>
(t11 = 0 \<or> (A3 s \<and> (t2 = 0 \<or> t21' = 0 \<and> ( A4 s) )) \<and> t11 \<le> t1 \<or> \<not>A3 s \<and> t11 < t11')) \<and> (b' \<longrightarrow> \<not> A1 s)  \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
 P9'inv s t1 t2 t11' t21' b' A1 A2 A3 A4"
  apply(unfold P9'inv_def)
  apply(erule P4'inv_rule_gen)
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
       apply(erule disjE)
        apply(rule disjI1)
        apply(erule conjE)
      subgoal premises prems3
        apply(rule conjI)
         apply(insert prems3(1,2))[1]
         apply assumption
        apply(insert prems3(1,3))
        apply(rule constrained_always_one_point)
        apply assumption
        done
       apply(rule disjI2)
       apply assumption
      apply(insert prems2(1,3))
      apply(rule conjI)
       apply simp
      apply(erule conjE)
      subgoal premises prems3
        apply(rule conjI)
         apply(insert prems3(1,2))[1]
         apply(rule all_conj_rule)
         apply(rule conjI)
          apply simp
         apply(rule constrained_always_rule)
          apply simp
         apply simp
        apply(insert prems3(1,3))
        apply(erule disjE)
         apply(rule disjI1)
         apply assumption
        apply(rule disjI2)
        apply(erule disjE)
         apply(rule disjI1)
         apply(erule conjE)
        subgoal premises prems4
          apply(rule conjI)
           apply(insert prems4(1,2))[1]
           apply(erule conjE)
          subgoal premises prems5
            apply(rule conjI)
             apply(insert prems5(1,2))[1]
             apply assumption
            apply(insert prems5(1,3))
            apply(rule constrained_always_one_point)
            apply assumption
            done
          apply(insert prems4(1,3))
          apply assumption
          done
        apply(rule disjI2)
        apply assumption
        done
      done
    apply(insert prems1(1,3))
    apply simp
    done
  done

lemma P9'einv2req: "
 P9'inv s t1 t2 t11 t21 b A1 A2 A3 A4 \<Longrightarrow> t11 \<le> t1 \<Longrightarrow>
 P9' s t1 t2 A1 A2 A3 A4"
  apply(unfold P9'inv_def P9'_def)
  using P4'_einv2req_gen constrained_always_einv2req
  by (smt (verit, best))

end
