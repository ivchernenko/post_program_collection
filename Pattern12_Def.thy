theory Pattern12_Def
  imports VCTheoryLemmas
begin

definition P12inv where "P12inv s t1 A1 A2 \<equiv> 
\<forall> s1. substate s1 s \<and> toEnvP s1 \<and> toEnvNum s1 s \<ge> t1 \<and> A1 s1 \<longrightarrow>
(\<exists> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s \<and> s1 \<noteq> s2 \<and> \<not> A2 s2)"

lemma P12inv_rule: "\<not> A2 s \<and> (t2 = 0 \<longrightarrow> \<not> A1 s) \<or> (t1 < t2 \<or> t1 = 0 \<and> \<not> A1 s) \<and> P12inv s0 t1 A1 A2 \<Longrightarrow> toEnvP s0 \<and> toEnvP s \<and> substate s0 s \<and> toEnvNum s0 s = 1 \<Longrightarrow> P12inv s t2 A1 A2"
  apply(unfold P12inv_def)
+  apply(rule allI)
  apply(rule impI)
  apply(erule disjE)
   apply (metis gr_implies_not0 le_neq_implies_less substate_refl toEnvNum_id)
  apply(rotate_tac -1)
  apply(erule conjE)
  subgoal for s1
    apply(erule allE[of _ s1])
    by (smt (verit) Suc_eq_plus1 dual_order.strict_trans1 less_Suc_eq_le less_zeroE linorder_le_less_linear substate_noteq_imp_substate_of_pred substate_trans toEnvNum3 toEnvNum_id)
  done

  
definition P12op where "P12op s t A1 A2 \<equiv>
\<exists>  s1. toEnvP s1 \<and> substate s1 s \<and> toEnvNum s1 s \<ge> t \<and> A1 s1 \<and>
(\<forall> s2. toEnvP s1 \<and> substate s1 s2 \<and> substate s2 s \<and> s1 \<noteq> s2 \<longrightarrow> A2 s2)"

lemma einv2req_neg: "P12inv s t1 A1 A2 \<Longrightarrow> t1 \<le> t \<Longrightarrow> \<not> P12op s t A1 A2"
  apply(unfold P12inv_def P12op_def)
  apply auto
  done

lemma einv2req_imp: "A3 \<or> P12inv s t1 A1 A2 \<Longrightarrow> t1 \<le> t \<Longrightarrow> P12op s t A1 A2 \<longrightarrow> A3"
  apply(unfold P12inv_def P12op_def)
  apply auto
  done



end