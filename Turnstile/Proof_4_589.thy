theory Proof_4_589
  imports Proofs4
begin

thm VC589_def

abbreviation s where " s s0 PdOut'value paid'value opened'value \<equiv>
 (toEnv
   (setPstate
     (setPstate
       (setVarBool
         (setVarBool
           (setPstate
             (setVarBool
               (setVarBool (setVarBool (setVarBool s0 PdOut' PdOut'value) paid' paid'value) opened'
                 opened'value)
               Controller'minimalOpened' False)
             Init'init' Controller'isClosed')
           EntranceController'isClosed' False)
         Controller'isOpened' True)
       Controller'minimalOpened' Unlocker'unlock')
     Controller'isClosed' EntranceController'isClosed'))"

theorem proof_4_589: "VC589 inv4 env s0 PdOut_value paid_value opened_value"
  apply(simp only: VC589_def inv4_def R4_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
   apply(rule conjI)
    apply simp
   apply(drule conjE)
    prefer 2
    apply assumption
   apply(drule conjE)
    prefer 2
    apply assumption
   apply((rule allI)+)
  subgoal premises vc_prems for s1 s2
    using vc_prems(2) apply -
    apply(drule conjE)
     prefer 2
     apply assumption
    subgoal premises invs0
      apply(rule impI)
      apply(rule disjE[of "100 < toEnvNum s2 (s s0 PdOut_value paid_value opened_value)" 
"100 = toEnvNum s2 (s s0 PdOut_value paid_value opened_value)"])
      using le_imp_less_or_eq apply blast
      apply(rule cut_rl[of "\<exists>s4. toEnvP s4 \<and>
         substate s2 s4 \<and>
         substate s4 s0 \<and>
         toEnvNum s2 s4 \<le> 100 \<and>
         \<not> getVarBool s4 Controller'minimalOpened' \<and>
         (\<forall>s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> getVarBool s3 Controller'minimalOpened')"])
        apply(drule exE)
         prefer 2
         apply assumption
      subgoal for s4
        apply(rule exI[of _ s4])
        by simp
      subgoal premises req_prems
        using invs0(1) req_prems apply -
        apply(drule conjE)
         prefer 2
         apply assumption
        apply(drule allE[of _ s1])
        prefer 2
         apply assumption
        apply(drule allE[of _ s2])
        prefer 2
         apply assumption
        by(simp split: if_splits)
      apply(rule cut_rl[of "\<forall> s5. toEnvP s5 \<and> substate s2 s5 \<and> substate s5 (s s0 PdOut_value paid_value opened_value) \<longrightarrow>
pred4 s1 s2 (s s0 PdOut_value paid_value opened_value) s5"])
       apply(drule allE[of _ s2])
      prefer 2
        apply assumption
       apply(drule impE)
      prefer 3
      apply assumption
      using substate_refl apply blast
       apply(simp only: pred4_def)
       apply(drule impE)
      prefer 3
      apply assumption
      using substate_refl substate_trans substate_antisym apply blast
       apply assumption
      apply(rule allI)
      subgoal premises prems for s5
        apply(induction rule: state_ind)
        using prems(1) apply simp
         apply(simp only: pred4_def)
         apply(rule impI)

         apply(rule exI[of _  "s s0 PdOut_value paid_value opened_value"])
         apply(((rule conjI),simp)+)
        using substate_trans substate_antisym apply blast

        subgoal for s5
          apply(simp only: pred4_def)
          apply(rule impI)
          apply(cases "getVarBool (predEnv s5) open' = False")
           apply(rule exI[of _ "predEnv s5"])
           apply(rule conjI)
        apply(rule toEnvP_substate_pred_imp_toEnvP_pred[of s2])
            apply blast
       apply(rule conjI)
          using substate_refl apply simp
       apply(rule conjI)
      using predEnv_substate substate_trans apply blast
       apply(rule conjI)
      using toEnvNum3[of s2 "predEnv s5"
 "(s s0 PdOut_value paid_value opened_value) "] 
        apply force
       apply(rule conjI)
        apply blast
      using substate_antisym apply blast
      apply(drule impE)
        prefer 3
        apply assumption
       apply(((rule conjI),blast)+)
      using substate_imp_substatete_predEnv_or_eq apply blast
      apply(drule exE)
       prefer 2
       apply assumption
      subgoal for s4
        apply(rule exI[of _ s4])
       apply(rule conjI)
         apply blast
        apply(rule conjI)
        using predEnv_substate substate_trans apply blast
        apply(((rule conjI),blast)+)
        using predEnv_substate_imp_substate_or_eq by blast
      done
    done
  done
  done
