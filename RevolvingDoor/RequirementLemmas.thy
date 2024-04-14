theory RequirementLemmas
  imports VCTheoryLemmas
begin

lemma P4_disj2req: "
(\<forall> s5. toEnvP s5 \<and> substate s5 s \<and> P s5 \<longrightarrow>
(\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s5 \<and> toEnvNum s1 s2 = 1 \<and> vc1 s1 s2 \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s5 \<and> toEnvNum s2 s4 \<le> t \<and> vc2 s4 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> vc3 s3)) \<or>
toEnvNum s2 s5 < T s5 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s5 \<longrightarrow> vc3 s3))) \<Longrightarrow>
toEnvP s \<and> T s \<le> t \<and> P s \<Longrightarrow>
(\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and>  toEnvNum s2 s \<ge> t \<and> vc1 s1 s2 \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s \<and> toEnvNum s2 s4 \<le> t \<and> vc2 s4 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> vc3 s3)))"
  apply(erule allE[of _ s])
  using substate_refl
  by (smt (verit) dual_order.trans less_le_not_le)

lemma P5_left2req: "
(\<forall> s5. toEnvP s5 \<and> substate s5 s \<and> P s5 \<longrightarrow>
(\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s5 \<and> toEnvNum s1 s2 = 1 \<and> vc1 s1 s2 \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s5 \<and> toEnvNum s2 s4 \<le> t \<and> vc2 s4 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> vc3 s3)))) \<Longrightarrow>
toEnvP s \<and>  P s \<Longrightarrow>
(\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and>  toEnvNum s2 s \<ge> t \<and> vc1 s1 s2 \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s \<and> toEnvNum s2 s4 \<le> t \<and> vc2 s4 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> vc3 s3)))"
  apply(erule allE[of _ s])
  using substate_refl
  by blast

lemma P5_disj2req: "
(\<forall> s5. toEnvP s5 \<and> substate s5 s \<and> P s5 \<longrightarrow>
(\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s5 \<and> toEnvNum s1 s2 = 1 \<and> vc1 s1 s2 \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s5 \<and> toEnvNum s2 s4 \<le> t \<and> vc2 s4 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> vc3 s3)) \<or>
toEnvNum s2 s5 < t1 s5 \<and> (\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s5 \<longrightarrow> vc3 s3))) \<Longrightarrow>
toEnvP s \<and>  P s \<and> t1 s \<le> t \<Longrightarrow>
(\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and>  toEnvNum s2 s \<ge> t \<and> vc1 s1 s2 \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s \<and> toEnvNum s2 s4 \<le> t \<and> vc2 s4 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> vc3 s3)))"
  apply(erule allE[of _ s])
  by (smt (verit) dual_order.trans linorder_not_le substate_refl)
  

lemma P4_ex_or_all_imp_ex_or_all: "
(\<forall> s4. toEnvP s4 \<and> substate s4 s0 \<and> P1 s4 \<longrightarrow>
(\<forall> s1. toEnvP s1 \<and> substate s1 s4 \<and> vc1 s1 \<longrightarrow>
(\<exists> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s4 \<and> toEnvNum s1 s3 \<le> T \<and> vc2 s3 \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s3 \<and> s2 \<noteq> s3 \<longrightarrow> vc3 s2)) \<or>
toEnvNum s1 s4 < T1 s4 \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s4 \<longrightarrow> vc3 s2))) \<Longrightarrow>
(\<forall> s4. toEnvP s4 \<and> substate s4 s0 \<and> P2 s4 \<longrightarrow>
(\<forall> s1. toEnvP s1 \<and> substate s1 s4 \<and> vc1 s1 \<longrightarrow>
(\<exists> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s4 \<and> toEnvNum s1 s3 \<le> T \<and> vc2 s3 \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s3 \<and> s2 \<noteq> s3 \<longrightarrow> vc3 s2)) \<or>
toEnvNum s1 s4 < T2 s4 \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s4 \<longrightarrow> vc3 s2))) \<Longrightarrow>
vc1 s \<longrightarrow> vc2 s \<or> vc3 s \<and> T2 s > 0  \<Longrightarrow>
T1 s0 > 0 \<longrightarrow> vc2 s \<and> T1 s0 \<le> T \<or> vc3 s \<and> T1 s0 < T2 s \<Longrightarrow>
toEnvP s0 \<and> toEnvP s \<and>  P1 s0 \<and> substate s0 s \<and> toEnvNum s0 s = 1 \<Longrightarrow>
(\<forall> s4. toEnvP s4 \<and> substate s4 s \<and> P2 s4 \<longrightarrow>
(\<forall> s1. toEnvP s1 \<and> substate s1 s4 \<and> vc1 s1 \<longrightarrow>
(\<exists> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s4 \<and> toEnvNum s1 s3 \<le> T \<and> vc2 s3 \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s3 \<and> s2 \<noteq> s3 \<longrightarrow> vc3 s2)) \<or>
toEnvNum s1 s4 < T2 s4 \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s4 \<longrightarrow> vc3 s2)))"
  apply(rule allI)
  subgoal for s4
    apply(rule cut_rl[of "\<forall> s1. substate s1 s \<and> toEnvP s1  \<and> s1 \<noteq> s \<longrightarrow> substate s1 s0"])
     apply(cases "s4 = s")
      apply(rule impI)
      apply(rule allI)
    subgoal for s1
      apply(cases "s1 = s") 
       apply (metis less_eq_nat.simps(1) substate_antisym toEnvNum_id)
      apply(erule allE[of _ s0])
      apply(rotate_tac -1)
      apply(erule impE)
      using substate_refl  apply simp
      apply(rotate_tac -1)
      apply(rule impI)
      apply(erule allE[of _ s1])
      apply(rotate_tac -1)
      apply(erule impE)
       apply blast
      apply(rotate_tac -1)
      apply(erule disjE)
       apply (metis substate_trans)
      apply(rotate_tac 2)
      apply(erule impE)
       apply simp
      apply(rotate_tac -1)
      apply(erule disjE)
       apply(rule disjI1)
       apply(rule exI[of _ s])
       apply(rule conjI)
        apply simp
       apply(rule conjI)
        apply simp
       apply(rule conjI)
        apply simp
       apply(rule conjI)
      using toEnvNum3[of s1 s0 s] apply (metis Suc_eq_plus1 Suc_leI dual_order.trans)
       apply(rule conjI)
        apply simp
       apply presburger
      apply(rule disjI2)
      apply(rule conjI)
      using toEnvNum3 apply (metis Suc_eq_plus1 less_trans_Suc)
      by metis
     apply simp
    using substate_or_substate_pair by (meson substate_antisym substate_refl)
  done

lemma P5_ex_or_all_imp_ex_or_all: "
(\<forall> s5. toEnvP s5 \<and> substate s5 s0 \<and> P1 s5 \<longrightarrow>
(\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s5 \<and> toEnvNum s1 s2 = 1 \<and> vc1 s1 s2 \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s5 \<and> toEnvNum s2 s4 \<le> T \<and> vc2 s4 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> vc3 s3)) \<or>
toEnvNum s2 s5 < T1 s5 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s5 \<longrightarrow> vc3 s3))) \<Longrightarrow>
(\<forall> s5. toEnvP s5 \<and> substate s5 s0 \<and> P2 s5 \<longrightarrow>
(\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s5 \<and> toEnvNum s1 s2 = 1 \<and> vc1 s1 s2 \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s5 \<and> toEnvNum s2 s4 \<le> T \<and> vc2 s4 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> vc3 s3)) \<or>
toEnvNum s2 s5 < T2 s5 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s5 \<longrightarrow> vc3 s3))) \<Longrightarrow>
vc1 s0 s \<longrightarrow> vc2 s \<or> vc3 s \<and> T2 s > 0  \<Longrightarrow>
T1 s0 > 0 \<longrightarrow> vc2 s \<and> T1 s0 \<le> T \<or> vc3 s \<and> T1 s0 < T2 s \<Longrightarrow>
toEnvP s0 \<and> toEnvP s \<and>  P1 s0 \<and> substate s0 s \<and> toEnvNum s0 s = 1 \<Longrightarrow>
(\<forall> s5. toEnvP s5 \<and> substate s5 s \<and> P2 s5 \<longrightarrow>
(\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s5 \<and> toEnvNum s1 s2 = 1 \<and> vc1 s1 s2 \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s5 \<and> toEnvNum s2 s4 \<le> T \<and> vc2 s4 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> vc3 s3)) \<or>
toEnvNum s2 s5 < T2 s5 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s5 \<longrightarrow> vc3 s3)))"
  apply(rule allI)
  subgoal for s5
    apply(rule cut_rl[of "\<forall> s1. substate s1 s \<and> toEnvP s1  \<and> s1 \<noteq> s \<longrightarrow> substate s1 s0"])
     apply(cases "s5 = s")
      apply(rule impI)
      apply((rule allI)+)
    subgoal for s1 s2
      apply(cases "s2 = s")
       apply (metis less_eq_nat.simps(1) substate_antisym toEnvNum_eq_imp_eq2 toEnvNum_id)
      apply(erule allE[of _ s0])
      apply(rotate_tac -1)
      apply(erule impE)
      using substate_refl  apply simp
      apply(rotate_tac -1)
      apply(rule impI)
      apply(erule allE[of _ s1])
      apply(rotate_tac -1)
      apply(erule allE[of _ s2])
      apply(rotate_tac -1)
      apply(erule impE)
      apply blast
      apply(rotate_tac -1)
      apply(erule disjE)
       apply (metis substate_trans)
      apply(rotate_tac 2)  
      apply(erule impE)
       apply simp
      apply(rotate_tac -1)
      apply(erule disjE)
       apply(rule disjI1)
       apply(rule exI[of _ s])
       apply(rule conjI)
        apply simp
       apply(rule conjI)
        apply simp
       apply(rule conjI)
        apply simp
       apply(rule conjI)
      using toEnvNum3[of s2 s0 s] apply (metis Suc_eq_plus1 Suc_leI dual_order.trans)
       apply(rule conjI)
        apply simp
       apply presburger
      apply(rule disjI2)
      apply(rule conjI)
      using toEnvNum3 apply (metis Suc_eq_plus1 less_trans_Suc)
      by metis
     apply (smt (verit, del_insts))
    using substate_or_substate_pair by (meson substate_antisym substate_refl)
  done   

lemma P5_ex_or_all_imp_ex: "
(\<forall> s5. toEnvP s5 \<and> substate s5 s0 \<and> P1 s5 \<longrightarrow>
(\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s5 \<and> toEnvNum s1 s2 = 1 \<and> vc1 s1 s2 \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s5 \<and> toEnvNum s2 s4 \<le> T \<and> vc2 s4 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> vc3 s3)) \<or>
toEnvNum s2 s5 < T1 s5 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s5 \<longrightarrow> vc3 s3))) \<Longrightarrow>
(\<forall> s5. toEnvP s5 \<and> substate s5 s0 \<and> P2 s5 \<longrightarrow>
(\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s5 \<and> toEnvNum s1 s2 = 1 \<and> vc1 s1 s2 \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s5 \<and> toEnvNum s2 s4 \<le> T \<and> vc2 s4 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> vc3 s3)))) \<Longrightarrow>
vc1 s0 s \<longrightarrow> vc2 s  \<Longrightarrow>
T1 s0 > 0 \<longrightarrow> vc2 s \<and> T1 s0 \<le> T \<Longrightarrow>
toEnvP s0 \<and> toEnvP s \<and>  P1 s0 \<and> substate s0 s \<and> toEnvNum s0 s = 1 \<Longrightarrow>
(\<forall> s5. toEnvP s5 \<and> substate s5 s \<and> P2 s5 \<longrightarrow>
(\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s5 \<and> toEnvNum s1 s2 = 1 \<and> vc1 s1 s2 \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s5 \<and> toEnvNum s2 s4 \<le> T \<and> vc2 s4 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> vc3 s3)) ))"
  apply(rule cut_rl[of "
(\<forall> s5. toEnvP s5 \<and> substate s5 s \<and> P2 s5 \<longrightarrow>
(\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s5 \<and> toEnvNum s1 s2 = 1 \<and> vc1 s1 s2 \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s5 \<and> toEnvNum s2 s4 \<le> T \<and> vc2 s4 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> vc3 s3)) \<or>
toEnvNum s2 s5 < 0 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s5 \<longrightarrow> vc3 s3) ))"])
  apply simp
  apply(rule P5_ex_or_all_imp_ex_or_all[of s0 P1])
  by auto


lemma P5_ex_imp_ex_or_all: "
(\<forall> s5. toEnvP s5 \<and> substate s5 s0 \<and> P1 s5 \<longrightarrow>
(\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s5 \<and> toEnvNum s1 s2 = 1 \<and> vc1 s1 s2 \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s5 \<and> toEnvNum s2 s4 \<le> T \<and> vc2 s4 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> vc3 s3)) )) \<Longrightarrow>
(\<forall> s5. toEnvP s5 \<and> substate s5 s0 \<and> P2 s5 \<longrightarrow>
(\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s5 \<and> toEnvNum s1 s2 = 1 \<and> vc1 s1 s2 \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s5 \<and> toEnvNum s2 s4 \<le> T \<and> vc2 s4 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> vc3 s3)) \<or>
toEnvNum s2 s5 < T2 s5 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s5 \<longrightarrow> vc3 s3))) \<Longrightarrow>
vc1 s0 s \<longrightarrow> vc2 s \<or> vc3 s \<and> T2 s > 0  \<Longrightarrow>
toEnvP s0 \<and> toEnvP s \<and>  P1 s0 \<and> substate s0 s \<and> toEnvNum s0 s = 1 \<Longrightarrow>
(\<forall> s5. toEnvP s5 \<and> substate s5 s \<and> P2 s5 \<longrightarrow>
(\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s5 \<and> toEnvNum s1 s2 = 1 \<and> vc1 s1 s2 \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s5 \<and> toEnvNum s2 s4 \<le> T \<and> vc2 s4 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> vc3 s3)) \<or>
toEnvNum s2 s5 < T2 s5 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s5 \<longrightarrow> vc3 s3)))"
  apply(rule cut_rl[of "(\<forall> s5. toEnvP s5 \<and> substate s5 s0 \<and> P1 s5 \<longrightarrow>
(\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s5 \<and> toEnvNum s1 s2 = 1 \<and> vc1 s1 s2 \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s5 \<and> toEnvNum s2 s4 \<le> T \<and> vc2 s4 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> vc3 s3)) \<or>
toEnvNum s2 s5 < 0 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s5 \<longrightarrow> vc3 s3)))"])
   apply(rule P5_ex_or_all_imp_ex_or_all[of s0 P1])
  by auto

lemma P5_ex_imp_ex: "
(\<forall> s5. toEnvP s5 \<and> substate s5 s0 \<and> P1 s5 \<longrightarrow>
(\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s5 \<and> toEnvNum s1 s2 = 1 \<and> vc1 s1 s2 \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s5 \<and> toEnvNum s2 s4 \<le> T \<and> vc2 s4 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> vc3 s3)) )) \<Longrightarrow>
(\<forall> s5. toEnvP s5 \<and> substate s5 s0 \<and> P2 s5 \<longrightarrow>
(\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s5 \<and> toEnvNum s1 s2 = 1 \<and> vc1 s1 s2 \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s5 \<and> toEnvNum s2 s4 \<le> T \<and> vc2 s4 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> vc3 s3)))) \<Longrightarrow>
vc1 s0 s \<longrightarrow> vc2 s  \<Longrightarrow>
toEnvP s0 \<and> toEnvP s \<and>  P1 s0 \<and> substate s0 s \<and> toEnvNum s0 s = 1 \<Longrightarrow>
(\<forall> s5. toEnvP s5 \<and> substate s5 s \<and> P2 s5 \<longrightarrow>
(\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s5 \<and> toEnvNum s1 s2 = 1 \<and> vc1 s1 s2 \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s5 \<and> toEnvNum s2 s4 \<le> T \<and> vc2 s4 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> vc3 s3)) ))"
  apply(rule cut_rl[of "
(\<forall> s5. toEnvP s5 \<and> substate s5 s0 \<and> P2 s5 \<longrightarrow>
(\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s5 \<and> toEnvNum s1 s2 = 1 \<and> vc1 s1 s2 \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s5 \<and> toEnvNum s2 s4 \<le> T \<and> vc2 s4 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> vc3 s3)) \<or>
toEnvNum s2 s5 < 0 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s5 \<longrightarrow> vc3 s3) ))"])
   apply(rule P5_ex_or_all_imp_ex[of s0 P1])
  by auto

end
