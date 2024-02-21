theory Proofs4
  imports Requirements VCTheoryLemmas
begin

definition inv4 where "inv4 s \<equiv> R4 s \<and> extraInv s"

definition pred4 where "pred4 s1 s2 s s5 \<equiv>
substate s1 s2 \<and> substate s2 s5 \<and> substate s5 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and> toEnvNum s2 s = 100 \<and>
\<not> getVarBool s1 open' \<and> getVarBool s2 open' \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s5 \<and> s3 \<noteq> s5 \<longrightarrow> getVarBool s3 open') \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s5 s4 \<and> substate s4 s \<and> toEnvNum s2 s4 \<le> 100 \<and> \<not> getVarBool s4 open' \<and>
(\<forall> s3. toEnvP s3 \<and> substate s5 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> getVarBool s3 open'))"

lemma minimalOpened_open: "toEnvP s1 \<and> toEnvP s2 \<and> toEnvP s0 \<and> substate s1 s2 \<and> substate s2 s0 \<and> substate s0 s\<and> toEnvNum s1 s2 = 1 \<and>
10 \<le> toEnvNum s2 s0 \<and> toEnvNum s2 s0 \<le> 99 \<and> \<not> getVarBool s1 open' \<and> getVarBool s2 open' \<and>
 getPstate s0 Controller' = Controller'minimalOpened' \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Init'init' = Controller'minimalOpened' \<longrightarrow> ltime s1 Init'init' \<le> 10) \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Init'init' = Controller'minimalOpened' \<longrightarrow>
      (\<exists>s2 s3.
          toEnvP s2 \<and>
          toEnvP s3 \<and>
          substate s2 s3 \<and>
          substate s3 s1 \<and>
          toEnvNum s2 s3 = 1 \<and>
          toEnvNum s2 s1 = ltime s1 Init'init' \<and> getPstate s2 Init'init' = Controller'isClosed' \<and> getVarBool s3 Init'init')) \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> (getPstate s1 Init'init' = Controller'isClosed' \<or> getPstate s1 Init'init' = STOP) \<longrightarrow>
      \<not> getVarBool s1 Controller'minimalOpened')
\<longrightarrow>
(\<exists> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s0 \<and> \<not> getVarBool s3 open')"
  apply(rule impI)
  apply(rule exE[of " (\<lambda> s2. \<exists> s3.
          toEnvP s2 \<and>
          toEnvP s3 \<and>
          substate s2 s3 \<and>
          substate s3 s0 \<and>
          toEnvNum s2 s3 = 1 \<and>
          toEnvNum s2 s0 = ltime s0 Init'init' \<and> getPstate s2 Init'init' = Controller'isClosed' \<and> getVarBool s3 Init'init') "])
   apply blast
  apply(drule exE)
   prefer 2
   apply assumption
  subgoal for s3 s4
    apply(rule exI[of _ s3])
    apply(rule cut_rl[of "substate s2 s3"])
    using substate_trans
     apply meson 
    using toEnvNum_substate2 substate_trans
    by (smt (verit) le_antisym le_trans substate_linear toEnvNum_eq_imp_eq2)
  done

lemma isOpened_open: "toEnvP s1 \<and> toEnvP s2 \<and> toEnvP s0 \<and> substate s1 s2 \<and> substate s2 s0 \<and> substate s0 s\<and> toEnvNum s1 s2 = 1 \<and>
 toEnvNum s2 s0 = 99 \<and> \<not> getVarBool s1 open' \<and> getVarBool s2 open' \<and>
 getPstate s0 Controller' = Controller'isOpened' \<and> ltime s0 Controller' < 90 \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Init'init' = Controller'minimalOpened' \<longrightarrow> ltime s1 Init'init' \<le> 10) \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Init'init' = Controller'minimalOpened' \<longrightarrow>
      (\<exists>s2 s3.
          toEnvP s2 \<and>
          toEnvP s3 \<and>
          substate s2 s3 \<and>
          substate s3 s1 \<and>
          toEnvNum s2 s3 = 1 \<and>
          toEnvNum s2 s1 = ltime s1 Init'init' \<and> getPstate s2 Init'init' = Controller'isClosed' \<and> getVarBool s3 Init'init')) \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> (getPstate s1 Init'init' = Controller'isClosed' \<or> getPstate s1 Init'init' = STOP) \<longrightarrow>
      \<not> getVarBool s1 Controller'minimalOpened') \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Init'init' = Controller'isOpened' \<longrightarrow> ltime s1 Init'init' \<le> 90) \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Init'init' = Controller'isOpened' \<longrightarrow>
      (\<exists>s2 s3.
          toEnvP s2 \<and>
          toEnvP s3 \<and>
          substate s2 s3 \<and>
          substate s3 s1 \<and>
          toEnvNum s2 s3 = 1 \<and>
          toEnvNum s2 s1 = ltime s1 Init'init' \<and>
          getPstate s2 Init'init' = Controller'minimalOpened' \<and> \<not> getVarBool s2 EntranceController'isOpened' \<and> \<not> getVarBool s3 PdOut')) 
\<longrightarrow>
(\<exists> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s0 \<and> \<not> getVarBool s3 open')"
  apply(rule impI)
  apply(rule exE[of "(\<lambda> s2.\<exists> s3.
              toEnvP s2 \<and>
              toEnvP s3 \<and>
              substate s2 s3 \<and>
              substate s3 s0 \<and>
              toEnvNum s2 s3 = 1 \<and>
              toEnvNum s2 s0 = ltime s0 Init'init' \<and>
              getPstate s2 Init'init' = Controller'minimalOpened' \<and> \<not> getVarBool s2 EntranceController'isOpened' \<and> \<not> getVarBool s3 PdOut')"])
  apply blast
  apply(drule exE)
   prefer 2
   apply assumption
  subgoal for s3 s4
 apply(rule cut_rl[of " substate s3 s0 "])
    apply(rule impE[OF minimalOpened_open[of s1 s2 s3 s]])
    subgoal
      apply((drule conjE[of _ _ ?thesis])+)
                          defer
                          apply assumption+
    using substate_trans apply -[1]
    apply(rule cut_rl[of "substate s2 s3"])
apply(rule conjI)
      apply blast
    apply(rule conjI)
      apply blast
    apply(rule conjI)
      apply blast
    apply(rule conjI)
      apply blast
    apply(rule conjI)
       apply blast
     apply(rule conjI)
       apply meson
    apply(rule conjI)
      apply blast
     apply(rule conjI)  
    using toEnvNum3[of s2 s3 s0] apply arith
     apply(rule conjI)
    using toEnvNum3[of s2 s3 s0] apply arith
     apply blast
     apply(rule cut_rl[of "\<not>substate s3 s2 \<or> s2=s3"])
    using substate_linear substate_refl
      apply meson
     apply(rule cut_rl[of "toEnvNum s3 s0 \<le> toEnvNum s2 s0"])
    using toEnvNum_substate2 toEnvNum_eq_imp_eq2
      apply (meson le_antisym) 
    by arith
   apply(drule exE)
    prefer 2
    apply assumption
  subgoal for s5
    apply(rule exI[of _ s5])
    using substate_trans[of s5 s3 s0]
    by blast
  using substate_trans[of s3 s4 s0] by blast
  done

theorem proof_4_1: "VC1 inv4 s0"
  apply(simp only: VC1_def inv4_def R4_def extraInv_def)
  by auto

theorem proof_4_346: "VC346 inv4 env s0 PdOut_value paid_value opened_value"
  apply(simp only: VC346_def)
  by auto

theorem proof_4_348: "VC348 inv4 env s0 PdOut_value paid_value opened_value"
  apply(simp only: VC348_def)
  by auto

end
