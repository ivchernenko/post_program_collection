theory Pattern12_Def
  imports VCTheoryLemmas
begin

definition P12sub where "P12sub s t A1 A2 A3 \<equiv>
\<exists> s1. toEnvP s1 \<and> substate s1 s \<and> toEnvNum s1 s > t \<and> A1 s1 \<and> A2 s \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s \<and> s1 \<noteq> s2 \<and> s2 \<noteq> s \<longrightarrow> A3 s2)"

definition P12 where "P12 s t A1 A2 A3 A4 \<equiv>
P12sub s t A1 A2 A3 \<longrightarrow>
A4 s"

definition P12inv where "P12inv s t1 A1 A3 \<equiv> 
\<forall> s1. substate s1 s \<and> toEnvP s1 \<and> toEnvNum s1 s > t1 \<and> A1 s1 \<longrightarrow>
(\<exists> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s \<and> s1 \<noteq> s2 \<and> \<not> A3 s2)"

lemma einv2req: "  P12inv s0 t1 A1 A3 \<or> (A2 s \<longrightarrow> A4 s) \<Longrightarrow> t1 < t \<Longrightarrow>
toEnvP s0 \<and> toEnvP s \<and> substate s0 s \<and> toEnvNum s0 s = 1 \<Longrightarrow>
P12sub s t A1 A2 A3 \<longrightarrow>  A4 s"
  apply(unfold P12inv_def P12_def P12sub_def)
  apply(subgoal_tac "\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> s1 \<noteq> s \<longrightarrow> substate s1 s0")
   apply(rule impI)
   apply(erule exE)
  subgoal for s1
    apply(erule disjE)
    apply(rotate_tac -1)
     apply(erule allE[of _ s1])
     apply(rotate_tac -1)
     apply(erule impE)
      apply(rule context_conjI)
       apply (metis less_nat_zero_code toEnvNum_id)
      apply(rule conjI)
       apply simp
      apply(rule conjI)
    using toEnvNum3[of s1 s0 s]
       apply linarith
      apply simp
     apply(erule exE)
      apply (metis substate_antisym substate_trans toEnvNum_id zero_neq_one)
    by simp
  apply(rule allI)
  subgoal for s1
    apply(rule impI)
    apply(subgoal_tac "substate s1 s0 \<or> substate s0 s1 \<and> s1 \<noteq> s0")
    apply(rotate_tac -1)
     apply(erule disjE)
      apply simp
    using toEnvNum3[of s0 s1 s]
    apply (metis add_gr_0 less_add_same_cancel1 less_add_same_cancel2 less_one substate_toEnvNum_id)
    using substate_linear by blast
  done

lemma P12inv_rule: "\<not> A3 s \<or> t1 < t2 \<and> P12inv s0 t1 A1 A3 \<Longrightarrow> toEnvP s0 \<and> toEnvP s \<and> substate s0 s \<and> toEnvNum s0 s = 1 \<Longrightarrow> P12inv s t2 A1 A3"
  apply(unfold P12inv_def)
  apply(rule allI)
  apply(rule impI)
  apply(erule disjE)
   apply fastforce
  apply(rotate_tac -1)
  apply(erule conjE)
  subgoal for s1
    apply(erule allE[of _ s1])
  apply(subgoal_tac "\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> s1 \<noteq> s \<longrightarrow> substate s1 s0")
     apply (smt (verit, ccfv_SIG) add_less_imp_less_left canonically_ordered_monoid_add_class.lessE dual_order.strict_trans less_one linorder_neq_iff not_add_less2 substate_trans toEnvNum3)
    apply(subgoal_tac "substate s1 s0 \<or> substate s0 s1 \<and> s1 \<noteq> s0")
    apply(rotate_tac -1)
     apply(erule disjE)
      apply simp
    using toEnvNum3[of s0 s1 s]
    apply (metis (full_types) add_is_1 substate_linear substate_toEnvNum_id toEnvNum3)
    apply (simp add: \<open>substate s0 s1 \<and> substate s1 s \<Longrightarrow> toEnvNum s0 s = toEnvNum s0 s1 + toEnvNum s1 s\<close>)
    using substate_linear by blast
  done

definition P12op where "P12op s t A1 A2 \<equiv>
\<exists>  s1. toEnvP s1 \<and> substate s1 s \<and> toEnvNum s1 s \<ge> t \<and> A1 s1 \<and>
(\<forall> s2. toEnvP s1 \<and> substate s1 s2 \<and> substate s2 s \<and> s1 \<noteq> s2 \<longrightarrow> A2 s2)"

end