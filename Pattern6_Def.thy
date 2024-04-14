theory Pattern6_Def
  imports Pattern2_Def
begin

definition P6 where "P6 s A1 A2 A3 \<equiv>
\<forall> s1 s2 s3. substate s1 s2 \<and> substate s2 s3 \<and> substate s3 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvP s3 \<and> toEnvNum s1 s2 = 1 \<and> A1 s1 s2  \<and>
(\<forall> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s3 \<longrightarrow> \<not> A3 s4) \<longrightarrow> A2 s3"

definition P6_1 where "P6_1 s A1 A2 A3 \<equiv>
\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> A1 s1  \<and>
(\<forall> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s2 \<longrightarrow> \<not> A3 s3) \<longrightarrow> A2 s2"

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



definition P6inv1 where "P6inv1 s w A1 A2 A3 \<equiv>
\<forall>s1 s2 s3.
   substate s1 s2 \<and>
   substate s2 s3 \<and>
   substate s3 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvP s3 \<and> toEnvNum s1 s2 = 1 \<and> A1 s1 s2 \<and> (\<forall>s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s3 \<longrightarrow> \<not> A3 s4) \<longrightarrow>
   A2 s3 \<and> (w \<or> s3 \<noteq> s)"

lemma P6inv1_rule: "P6inv1 s0 w1 A1 A2 A3 \<Longrightarrow>
A1 s0 s \<and> \<not> A3 s \<longrightarrow> A2 s \<and> w2 \<Longrightarrow>
w1 \<and> A2 s0 \<and> \<not> A3 s \<longrightarrow> A2 s \<and> w2 \<Longrightarrow>
 toEnvP s0 \<and> toEnvP s \<and> substate s0 s \<and> toEnvNum s0 s = 1 \<Longrightarrow> P6inv1 s w2 A1 A2 A3"
  apply(unfold P6inv1_def)
  by (smt (verit, ccfv_threshold) substate_noteq_imp_substate_of_pred substate_trans toEnvNum_eq_imp_eq2)

lemma einv2req1: "P6inv1 s w A1 A2 A3 \<Longrightarrow> P6 s A1 A2 A3"
  apply(unfold P6inv1_def P6_def)
  by auto

definition P6_1inv1 where "P6_1inv1 s w A1 A2 A3 \<equiv>
\<forall>s1 s2.
   substate s1 s2 \<and>
   substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and>  A1 s1 \<and> (\<forall>s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s2 \<longrightarrow> \<not> A3 s3) \<longrightarrow>
   A2 s2 \<and> (w \<or> s2 \<noteq> s)"

lemma P6_1inv1_rule: "P6_1inv1 s0 w1 A1 A2 A3 \<Longrightarrow>
A1 s \<and> \<not> A3 s \<longrightarrow> A2 s \<and> w2 \<Longrightarrow>
w1 \<and> A2 s0 \<and> \<not> A3 s \<longrightarrow> A2 s \<and> w2 \<Longrightarrow>
 toEnvP s0 \<and> toEnvP s \<and> substate s0 s \<and> toEnvNum s0 s = 1 \<Longrightarrow> P6_1inv1 s w2 A1 A2 A3"
  apply(unfold P6_1inv1_def)
  by (smt (verit, ccfv_threshold) substate_noteq_imp_substate_of_pred substate_trans toEnvNum_eq_imp_eq2)

lemma P6_1einv2req: "P6_1inv1 s w A1 A2 A3 \<Longrightarrow> P6_1 s A1 A2 A3"
  apply(unfold P6_1inv1_def P6_1_def)
  apply auto
  done

definition weak_until where "weak_until s1 s A1 A2 \<equiv>
(\<exists> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s \<and> A2 s3 \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s3 \<and> s2 \<noteq> s3 \<longrightarrow> A1 s2)) \<or>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s\<longrightarrow> A1 s2)"

definition weak_until_inv where "weak_until_inv s1 s w A1 A2 \<equiv>
(\<exists> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s \<and> A2 s3 \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s3 \<and> s2 \<noteq> s3 \<longrightarrow> A1 s2)) \<or>
w \<and> (\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s\<longrightarrow> A1 s2)"

lemma weak_until_rule: "consecutive s0 s \<Longrightarrow>
(\<forall> s1. toEnvP s1 \<and> substate s1 s0 \<and> A1 s1 \<longrightarrow> A1' s1) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s0 \<and> A2 s1 \<longrightarrow> A2' s1) \<and>
(\<not> w \<or>  A2' s \<or> w' \<and> A1' s) \<Longrightarrow>
\<forall> s1. toEnvP s1 \<and> substate s1 s0 \<and> weak_until_inv s1 s0 w A1 A2 \<longrightarrow> weak_until_inv s1 s w' A1' A2'"
  apply(unfold weak_until_inv_def)
  by (smt (verit, best) consecutive.elims(2) substate_noteq_imp_substate_of_pred substate_refl substate_trans)

lemma weak_until_one_point: "toEnvP s \<Longrightarrow> A2 s \<or> w \<and> A1 s \<Longrightarrow> weak_until_inv s s w A1 A2"
  apply(unfold weak_until_inv_def)
  using substate_antisym substate_refl by blast

lemma weak_until_einv2req: "
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> A1 s1 \<longrightarrow> A1' s1) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> A2 s1 \<longrightarrow> A2' s1) \<Longrightarrow>
\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> weak_until_inv s1 s w A1 A2 \<longrightarrow> weak_until s1 s A1' A2'"
  apply(unfold weak_until_inv_def weak_until_def)
  by (meson substate_trans)
  

definition P6_2 where "P6_2 s A1 A2 A3 A4 A5 \<equiv>
always2 s A1 A2 (\<lambda> s2. weak_until s2 s A3 (\<lambda> s4. previous_ex s4 A4 \<and> A5 s4))"

definition P6_2inv where "P6_2inv s w b1 b2 A1 A2 A3 A4 A5 \<equiv>
always2_inv s b1 A1 A2 (\<lambda> s2. weak_until_inv s2 s w A3 (\<lambda> s4. previous_ex s4 A4 \<and> A5 s4)) \<and>  (b2 \<longrightarrow> A4 s) "

lemma P6_2_rule: "
P6_2inv s0 w b1 b2 A1 A2 A3 A4 A5 \<Longrightarrow> consecutive s0 s \<Longrightarrow>
(( ( (b1 \<or> \<not>A2 s) \<or> b2 \<and> A5 s \<or> w' \<and> A3 s ) \<and> (\<not> w \<or> b2 \<and> A5 s \<or> w' \<and> A3 s)) \<and> (b1' \<longrightarrow>\<not> A1 s)) \<and> (b2' \<longrightarrow> A4 s) \<Longrightarrow>
P6_2inv s w' b1' b2' A1 A2 A3 A4 A5"
  apply(unfold P6_2inv_def)
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
         apply(rule weak_until_one_point)
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
          apply(insert prems4(1,3))[1]
          apply assumption
          done
         apply(rule disjI2)
         apply assumption
        apply(insert prems3(1,3))
        apply(rule weak_until_rule)
         apply simp
        apply(rule conjI)
         apply simp
        apply(rule conjI)
         apply simp
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
           apply(rule previous_ex_one_point[of s0])
          apply simp
           apply (simp add: prems1(3))
          apply(insert prems4(1,3))
          apply assumption
          done
        apply(rule disjI2)
        apply assumption
        done
      apply(insert prems2(1,3))
      apply assumption
      done
    apply(insert prems1(1,3,5))
    apply assumption
    done
  done

lemma P6_2_einv2req: "P6_2inv  s w b1 b2 A1 A2 A3 A4 A5 \<Longrightarrow> P6_2 s A1 A2 A3 A4 A5"
  apply(unfold P6_2_def P6_2inv_def)
  using always2_einv2req Pattern6_Def.weak_until_einv2req
  by (smt (verit, ccfv_SIG))

end
