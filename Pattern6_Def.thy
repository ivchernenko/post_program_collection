theory Pattern6_Def
  imports VCTheoryLemmas
begin

definition P6 where "P6 s A1 A2 A3 \<equiv>
\<forall> s1 s2 s3. substate s1 s2 \<and> substate s2 s3 \<and> substate s3 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvP s3 \<and> toEnvNum s1 s2 = 1 \<and> A1 s1 s2  \<and>
(\<forall> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s3 \<longrightarrow> \<not> A3 s4) \<longrightarrow> A2 s3"

definition P6inv where "P6inv s A1 A3 \<equiv>
\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and>  A1 s1 s2 \<longrightarrow>
(\<exists> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s \<and> A3 s3)"

lemma P6inv_rule1: "P1 \<longrightarrow> P6inv s0 A1 A3 \<Longrightarrow> A1 s0 s \<longrightarrow> P2 \<and>  A3 s \<Longrightarrow> P2 \<longrightarrow> P1  \<Longrightarrow> toEnvP s0 \<and> toEnvP s \<and> substate s0 s \<and> toEnvNum s0 s = 1 \<Longrightarrow>
P2 \<longrightarrow> P6inv s A1 A3"
  apply(unfold P6inv_def)
  by (smt (verit, del_insts) less_add_same_cancel2 less_nat_zero_code less_one linorder_neqE_nat substate_linear substate_toEnvNum_id substate_trans toEnvNum3)

lemma P6inv_rule2: "A3 s \<Longrightarrow> toEnvP s \<Longrightarrow> P6inv s A1 A3"
  apply(unfold P6inv_def)
  by auto

lemma P6_rule: "P6 s0 A1 A2 A3 \<Longrightarrow> \<not> A3 s \<longrightarrow> A2 s \<Longrightarrow> toEnvP s0 \<and> toEnvP s \<and> substate s0 s \<and> substate s0 s \<and> toEnvNum s0 s = 1 \<Longrightarrow> P6 s A1 A2 A3"
  apply(unfold P6_def)
  by (smt (verit, best) One_nat_def add_is_1 substate_linear substate_toEnvNum_id toEnvNum3)

lemma einv2req: "P6 s0 A1 A2 A3 \<Longrightarrow>  P6inv s0 A1 A3 \<Longrightarrow> A1 s0 s \<and> \<not> A3 s \<longrightarrow> A2 s \<Longrightarrow> toEnvP s0 \<and> toEnvP s \<and> substate s0 s \<and> toEnvNum s0 s = 1 \<Longrightarrow> P6 s A1 A2 A3"
  apply(unfold P6_def P6inv_def)
  by (smt (verit, ccfv_threshold) less_one nat_neq_iff not_add_less2 substate_linear substate_toEnvNum_id substate_trans toEnvNum3 toEnvNum_eq_imp_eq2)

end
  
  