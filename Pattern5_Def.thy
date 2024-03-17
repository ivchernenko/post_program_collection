theory Pattern5_Def
  imports VCTheoryLemmas
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

definition P5_1 where "P5_1 s t A1 A2 \<equiv>
\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 < t \<and> A1 s1 \<longrightarrow> A2 s2"

definition P5_1inv where "P5_1inv s t t1 A1 A2 \<equiv>
\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2  \<and>  toEnvNum s1 s2 < t \<and> A1 s1 \<longrightarrow>
toEnvNum s1 s \<ge> t1 \<and> A2 s2"

lemma P5_1inv_rule: "
P5_1inv s0 t t1 A1 A2 \<Longrightarrow>
 t >0 \<and> A1  s \<longrightarrow> t2 = 0 \<and> A2 s \<Longrightarrow>
 t1 + 1 < t \<longrightarrow>  A2 s \<Longrightarrow> t2 \<le> t1 + 1 \<Longrightarrow>
 toEnvP s0 \<and> toEnvP s \<and> substate s0 s \<and> toEnvNum s0 s = 1 \<Longrightarrow> 
P5_1inv s t t2 A1 A2"
  apply(unfold P5_1inv_def)
  apply(rule allI)+
  subgoal for s1 s2
    apply(cases "s1=s")
    apply (metis le_numeral_extra(3) substate_antisym toEnvNum_id)
   apply(cases "s2 = s")
    apply(rule impI)
      apply(erule allE[of _   s1])
     apply(rotate_tac -1)
      apply(erule allE[of _ s0])
     apply(rotate_tac -1)
    apply(erule impE)
      apply (metis canonically_ordered_monoid_add_class.lessE less_add_one substate_noteq_imp_substate_of_pred toEnvNum3 trans_less_add1)
    apply (metis add_mono_thms_linordered_semiring(3) dual_order.strict_trans2 dual_order.trans substate_noteq_imp_substate_of_pred toEnvNum3)
    apply(rule impI)
      apply(erule allE[of _   s1])
     apply(rotate_tac -1)
      apply(erule allE[of _ s2])
    apply(rotate_tac -1)
    apply(erule impE)
    using substate_noteq_imp_substate_of_pred apply blast
    by (smt (verit, ccfv_SIG) add.assoc add.commute le_Suc_ex le_add1 substate_noteq_imp_substate_of_pred toEnvNum3)
  done

lemma P5_1_einv2req: "P5_1inv s t t1 A1 A2 \<Longrightarrow> P5_1 s t A1 A2"
  apply(unfold P5_1inv_def P5_1_def)
  apply auto
  done


end

