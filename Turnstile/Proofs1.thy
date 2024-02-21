theory Proofs1
  imports Requirements VCTheoryLemmas
begin

definition inv1 where "inv1 s \<equiv> R1 s \<and> extraInv s"

definition pred1 where "pred1 s1 s2 s s5 \<equiv>
substate s1 s2 \<and> substate s2 s5 \<and> substate s5 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvP s5 \<and> toEnvNum s1 s2 = 1 \<and> 10 - 1 = toEnvNum s2 s \<and>
 getVarBool s1 open' \<and> getVarBool s2 PdOut' = True \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s5 \<and> s3 \<noteq> s5 \<longrightarrow> getVarBool s3 open') \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s5 s4 \<and> substate s4 s \<and> toEnvNum s2 s4 \<le> 10 - 1 \<and> \<not> getVarBool s4 open' \<and>
(\<forall> s3. toEnvP s3 \<and> substate s5 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> getVarBool s3 open'))"

lemma minimalOpened_ltime_le_10_R1: "substate s1 s2 \<and> substate s2 s0 \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvP s0 \<and> substate s0 s \<and>
toEnvNum s1 s2 = 1 \<and> toEnvNum s2 s0 = 10 - 2 \<and> getVarBool s1 open' \<and> getVarBool s2 PdOut' = True \<and>
 getPstate s0 Controller' = Controller'minimalOpened' \<and> ltime s0 Controller' < 10 \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Init'init' = Controller'minimalOpened' \<longrightarrow> ltime s1 Init'init' \<le> 10) \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Init'init' = Controller'minimalOpened' \<longrightarrow>
      (\<exists>s2 s3.
          toEnvP s2 \<and>
          toEnvP s3 \<and>
          substate s2 s3 \<and>
          substate s3 s1 \<and>
          toEnvNum s2 s3 = 1 \<and>
          toEnvNum s2 s1 = ltime s1 Init'init' \<and> getPstate s2 Init'init' = Controller'isClosed' \<and> getVarBool s3 Init'init')) \<and>
(\<forall>s2. toEnvP s2 \<and> substate s2 s \<and> getPstate s2 Init'init' = Controller'minimalOpened' \<longrightarrow>
      (\<forall>s1. toEnvP s1 \<and> substate s1 s2 \<and> toEnvNum s1 s2 < ltime s2 Init'init' \<longrightarrow>
            getPstate s1 Init'init' = Controller'minimalOpened')) \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> (getPstate s1 Init'init' = Controller'isClosed' \<or> getPstate s1 Init'init' = STOP) \<longrightarrow>
      \<not> getVarBool s1 Controller'minimalOpened') \<longrightarrow>
(\<exists> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s0 \<and> \<not> getVarBool s3 open')"
  apply(rule impI)
  apply(rule exE[of "(\<lambda> s2. \<exists> s3.
              toEnvP s2 \<and>
              toEnvP s3 \<and>
              substate s2 s3 \<and>
              substate s3 s0 \<and>
              toEnvNum s2 s3 = 1 \<and>
              toEnvNum s2 s0 = ltime s0 Init'init' \<and> getPstate s2 Init'init' = Controller'isClosed' \<and> getVarBool s3 Init'init')"])
   apply blast
  apply(erule exE)
  subgoal for s3 s4
    apply(cases "substate s2 s3")
     apply(rule exI[of _ s3])
    using substate_trans
     apply meson
    apply(rule cut_rl[of "s1=s3"])
    using substate_trans
     apply meson
    apply(rule cut_rl[of "toEnvNum s3 s0 \<le> toEnvNum s1 s0"])

     apply(rule cut_rl[of "toEnvNum s1 s0 = toEnvNum s3 s0"])
    using toEnvNum_eq_imp_eq2 substate_trans apply meson
     apply(rule le_antisym)
      apply(rule cut_rl[of "toEnvNum s2 s0 < toEnvNum s3 s0"])
    using toEnvNum3 apply auto[1]
      apply(rule le_neq_implies_less)
       apply(rule toEnvNum_substate2)
    using substate_linear substate_trans
       apply meson
    using toEnvNum_eq_imp_eq2 substate_refl substate_trans
      apply metis
     apply assumption

    apply((erule conjE)+)
    using toEnvNum3[of s1 s2 s0] by arith
  done

lemma minimalOpened_not_passed_R1: "substate s1 s2 \<and> substate s2 s0 \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvP s0 \<and> substate s0 s \<and>
toEnvNum s1 s2 = 1 \<and> toEnvNum s2 s0 \<le> 10 - 2 \<and> getVarBool s1 open' \<and> getVarBool s2 PdOut' = True \<and>
 getPstate s0 Controller' = Controller'minimalOpened' \<and> ltime s0 Controller' = 10 \<and> \<not> getVarBool s0 passed' \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Init'init' = Controller'minimalOpened' \<longrightarrow> ltime s1 Init'init' \<le> 10) \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Init'init' = Controller'minimalOpened' \<longrightarrow>
      (\<exists>s2 s3.
          toEnvP s2 \<and>
          toEnvP s3 \<and>
          substate s2 s3 \<and>
          substate s3 s1 \<and>
          toEnvNum s2 s3 = 1 \<and>
          toEnvNum s2 s1 = ltime s1 Init'init' \<and> getPstate s2 Init'init' = Controller'isClosed' \<and> getVarBool s3 Init'init')) \<and>
(\<forall>s2. toEnvP s2 \<and> substate s2 s \<and> getPstate s2 Init'init' = Controller'minimalOpened' \<longrightarrow>
      (\<forall>s1. toEnvP s1 \<and> substate s1 s2 \<and> toEnvNum s1 s2 < ltime s2 Init'init' \<longrightarrow>
            getPstate s1 Init'init' = Controller'minimalOpened')) \<and>
(\<forall>s1. toEnvP s1 \<and>
      substate s1 s \<and> getPstate s1 Init'init' = Controller'minimalOpened' \<and> \<not> getVarBool s1 EntranceController'isOpened' \<longrightarrow>
      (\<forall>s2. toEnvP s2 \<and> substate s2 s1 \<and> toEnvNum s2 s1 + 1 < ltime s1 Init'init' \<longrightarrow> \<not> getVarBool s2 Init')) \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> (getPstate s1 Init'init' = Controller'isClosed' \<or> getPstate s1 Init'init' = STOP) \<longrightarrow>
      \<not> getVarBool s1 Controller'minimalOpened') \<longrightarrow>
(\<exists> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s0 \<and> \<not> getVarBool s3 open')"
  by (metis Suc_1 Suc_diff_Suc le_imp_less_Suc le_numeral_extra(4) less_diff_conv numeral_Bit0 numeral_Bit1 trans_less_add1)

lemma isOpened_R1: "substate s1 s2 \<and> substate s2 s0 \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvP s0 \<and> substate s0 s \<and>
toEnvNum s1 s2 = 1 \<and> toEnvNum s2 s0 = 10 - 2 \<and> getVarBool s1 open' \<and> getVarBool s2 PdOut' = True \<and>
 getPstate s0 Controller' = Controller'isOpened'  \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Init'init' = Controller'minimalOpened' \<longrightarrow> ltime s1 Init'init' \<le> 10) \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Init'init' = Controller'minimalOpened' \<longrightarrow>
      (\<exists>s2 s3.
          toEnvP s2 \<and>
          toEnvP s3 \<and>
          substate s2 s3 \<and>
          substate s3 s1 \<and>
          toEnvNum s2 s3 = 1 \<and>
          toEnvNum s2 s1 = ltime s1 Init'init' \<and> getPstate s2 Init'init' = Controller'isClosed' \<and> getVarBool s3 Init'init')) \<and>
(\<forall>s2. toEnvP s2 \<and> substate s2 s \<and> getPstate s2 Init'init' = Controller'minimalOpened' \<longrightarrow>
      (\<forall>s1. toEnvP s1 \<and> substate s1 s2 \<and> toEnvNum s1 s2 < ltime s2 Init'init' \<longrightarrow>
            getPstate s1 Init'init' = Controller'minimalOpened')) \<and>
(\<forall>s1. toEnvP s1 \<and>
      substate s1 s \<and> getPstate s1 Init'init' = Controller'minimalOpened' \<and> \<not> getVarBool s1 EntranceController'isOpened' \<longrightarrow>
      (\<forall>s2. toEnvP s2 \<and> substate s2 s1 \<and> toEnvNum s2 s1 + 1 < ltime s1 Init'init' \<longrightarrow> \<not> getVarBool s2 Init')) \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Init'init' = Controller'isOpened' \<longrightarrow> ltime s1 Init'init' \<le> 90) \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Init'init' = Controller'isOpened' \<longrightarrow>
      (\<exists>s2 s3.
          toEnvP s2 \<and>
          toEnvP s3 \<and>
          substate s2 s3 \<and>
          substate s3 s1 \<and>
          toEnvNum s2 s3 = 1 \<and>
          toEnvNum s2 s1 = ltime s1 Init'init' \<and>
          getPstate s2 Init'init' = Controller'minimalOpened' \<and>
          ltime s2 Init'init' = 10 \<and> \<not> getVarBool s2 EntranceController'isOpened' \<and> \<not> getVarBool s3 PdOut')) \<and>
(\<forall>s3. toEnvP s3 \<and> substate s3 s \<and> getPstate s3 Init'init' = Controller'isOpened' \<longrightarrow>
      (\<forall>s1. toEnvP s1 \<and> substate s1 s3 \<and> toEnvNum s1 s3 < ltime s3 Init'init' \<longrightarrow> getPstate s1 Init'init' = Controller'isOpened') \<and>
      (\<forall>s2. toEnvP s2 \<and> substate s2 s3 \<and> toEnvNum s2 s3 + 1 < ltime s3 Init'init' \<longrightarrow> \<not> getVarBool s2 Init'))  \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> (getPstate s1 Init'init' = Controller'isClosed' \<or> getPstate s1 Init'init' = STOP) \<longrightarrow>
      \<not> getVarBool s1 Controller'minimalOpened') \<longrightarrow>
(\<exists> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s0 \<and> \<not> getVarBool s3 open')"
  apply(rule impI)
  apply(rule exE[of "(\<lambda> s2. \<exists> s3.
          toEnvP s2 \<and>
          toEnvP s3 \<and>
          substate s2 s3 \<and>
          substate s3 s0 \<and>
          toEnvNum s2 s3 = 1 \<and>
          toEnvNum s2 s0 = ltime s0 Init'init' \<and>
          getPstate s2 Init'init' = Controller'minimalOpened' \<and>
          ltime s2 Init'init' = 10 \<and> \<not> getVarBool s2 EntranceController'isOpened' \<and> \<not> getVarBool s3 PdOut')"])
   apply blast
  apply(erule exE)
  subgoal for s3 s4
    apply(cases "substate s2 s3")
    apply(rule cut_rl[of "substate s3 s0"])
      apply(rule impE[OF minimalOpened_not_passed_R1[of s1 s2 s3 s]])
       apply((erule conjE)+)
       apply(insert substate_trans[of s3 s0 s] toEnvNum3[of s2 s3 s0])[1]
       apply(((rule conjI),arith)+)
       apply assumption
        apply(erule exE)
    subgoal for s5
      apply(rule exI[of _ s5])
      using substate_trans[of s5 s3 s0] by blast
    using substate_trans[of s3 s4 s0] apply blast
    apply(cases "s2=s4")
    apply blast
    apply(rule cut_rl[of "substate s4 s1"])
     apply(rule cut_rl[of "(\<forall>s2. toEnvP s2 \<and> substate s2 s0 \<and> toEnvNum s2 s0 + 1 < ltime s0 Init'init' \<longrightarrow> \<not> getVarBool s2 Init')"])
      apply(erule allE[of _ s2])
      apply(erule impE)
       apply(rule cut_rl[of "toEnvNum s1 s0 < toEnvNum s3 s0"])
    using toEnvNum3[of s1 s2 s0] apply arith
    using toEnvNum3 toEnvNum_substate2
       apply (smt (verit) nat_less_le substate_trans toEnvNum_eq_imp_eq1 toEnvNum_eq_imp_eq2)
    apply blast
     apply blast

    apply(rule cut_rl[of "\<not> substate s1 s4 \<or> s1=s4"])
    using substate_refl substate_trans substate_linear
     apply metis
    apply(rule cut_rl[of "toEnvNum s1 s0 \<le> toEnvNum s4 s0"])
    using substate_trans toEnvNum_substate2 toEnvNum_eq_imp_eq2
     apply (meson le_antisym) 
    apply(rule cut_rl[of "toEnvNum s2 s0 < toEnvNum s3 s0 \<and> toEnvNum s2 s0 \<noteq> toEnvNum s4 s0"])
    using toEnvNum3
     apply (smt (verit) Suc_leI le_SucE plus_1_eq_Suc substate_trans toEnvNum_eq_imp_eq1 toEnvNum_eq_imp_eq2)
    using substate_linear substate_trans toEnvNum_substate2 toEnvNum_eq_imp_eq2
    by (smt (verit) nat_less_le)
  done

end


   