theory Pattern2_Def
  imports Pattern3_Def
begin

definition previous_all where " previous_all s A \<equiv>
\<forall> s1. consecutive s1 s \<longrightarrow> A s1"

definition previous_ex where "previous_ex s A \<equiv>
\<exists> s1. consecutive s1 s \<and> A s1"

definition always2 where  "always2 s A1 A2 A3 \<equiv> 
always s (\<lambda> s2.( previous_ex s2 A1) \<and> A2 s2 \<longrightarrow> A3 s2)"

definition always2_inv where  "always2_inv s b A1 A2 A3 \<equiv> 
always s (\<lambda> s2.( previous_ex s2 A1) \<and> A2 s2 \<longrightarrow> A3 s2) \<and> (b \<longrightarrow> \<not>A1 s)"

lemma previous_all_one_point: "consecutive s0 s \<Longrightarrow>  A s0 \<Longrightarrow> previous_all s A"
  apply(unfold  previous_all_def)
  apply simp
  by (metis toEnvNum_eq_imp_eq2)

lemma previous_ex_one_point: "consecutive s0 s \<Longrightarrow>  A s0  \<Longrightarrow> previous_ex s A"
  apply(unfold  previous_ex_def)
  by auto

lemma previous_all_rule: "
(\<forall> s1. toEnvP s1 \<and> substate s1 s0 \<and> A s1 \<longrightarrow> A' s1) \<Longrightarrow>
(\<forall> s1. toEnvP s1 \<and> substate s1 s0 \<and> previous_all s1 A  \<longrightarrow> previous_all s1 A')"
  apply(unfold previous_all_def)
  by (meson consecutive.simps substate_trans)

lemma previous_ex_rule: "
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> A s1 \<longrightarrow> A' s1) \<Longrightarrow>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> previous_ex s1 A  \<longrightarrow> previous_ex s1 A')"
  apply(unfold previous_ex_def)
  by (meson consecutive.simps substate_trans)

lemma previous_ex_not: "\<not> previous_ex s A \<longleftrightarrow> previous_all s (\<lambda> s0. \<not> A s0)"
  using previous_all_def previous_ex_def by presburger

lemma always2_rule: "
always2_inv s0 b A1 A2 A3 \<Longrightarrow>consecutive s0 s \<Longrightarrow> (((b \<or> ~ A2 s) \<or> A3' s) \<and> (\<forall> s1. toEnvP s1 \<and> substate s1 s0 \<and> A3 s1 \<longrightarrow> A3' s1)) \<and> (b' \<longrightarrow> \<not>A1 s) \<Longrightarrow>
 always2_inv s b' A1 A2 A3'"
  apply(unfold always2_inv_def)
 (* by (smt (verit, ccfv_threshold) always_def consecutive.elims(2) previous_all_def previous_all_one_point previous_ex_def substate_noteq_imp_substate_of_pred)
*)
  apply(simp only: imp_conv_disj de_Morgan_conj previous_ex_not )
  apply(erule conjE)
  apply(erule conjE)
  subgoal premises prems1
    apply(rule conjI)
     apply(insert prems1(1,2,4))[1]
     apply(erule always_rule)
      apply simp
     apply(erule conjE)
    subgoal premises prems2
      apply(rule conjI)
       apply(insert prems2(1,2))[1]
       apply(erule disjE)
        apply(rule disjI1)
        apply(erule disjE)
         apply(rule disjI1)
         apply(rule previous_all_one_point[of s0])
      apply simp
      using prems1(3) apply simp
        apply(rule disjI2)
        apply assumption (*apply simp*)
       apply(rule disjI2)
       apply assumption
      apply(insert prems2(1,3))[1]
      apply auto
      done
    apply(insert prems1(1,3,5))
    apply simp
    done
  done

lemma always2_einv2req: "always2_inv s b A1 A2 A3 \<Longrightarrow>  (\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> A3 s1 \<longrightarrow> A3' s1) \<Longrightarrow> always2 s A1 A2 A3'"
  apply(unfold always2_def always2_inv_def)
  by (metis (mono_tags, lifting) always_einv2req)

end