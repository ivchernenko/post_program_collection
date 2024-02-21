theory Proof_1_338
  imports Proofs1  Extra338
begin

abbreviation s where " s s0 PdOut'value paid'value opened'value \<equiv>
 (toEnv
   (setPstate
     (setVarBool
       (setPstate
         (setVarBool
           (setPstate
             (setVarBool
               (setVarBool
                 (setVarBool (setVarBool (setVarBool s0 PdOut' PdOut'value) paid' paid'value) opened'
                   opened'value)
                 Controller'minimalOpened' True)
               EntranceController'isOpened' False)
             Init'init' Controller'minimalOpened')
           EntranceController'isClosed' True)
         Controller'isClosed' EntranceController'isOpened')
       Controller'isOpened' False)
     Controller'minimalOpened' STOP))"

theorem proof_1_338: "VC338 inv1 env s0 PdOut_value paid_value opened_value"
  apply(unfold VC338_def inv1_def R1_def)
  apply(rule impI)
  apply(rule conjI)
   apply(rule conjI)
    apply simp
   apply(unfold extraInv_def)[1]
   apply(erule conjE)
   apply(erule conjE)
   apply((rule allI)+)
  subgoal premises vc_prems for s1 s2
    apply(insert vc_prems(2))
    apply(erule conjE)
    subgoal premises invs0
      apply(rule impI)
      apply((erule conjE)+)
      apply(erule le_imp_less_or_eq[THEN disjE])
      apply(rule cut_rl[of "  \<exists>s4. toEnvP s4 \<and>
         substate s2 s4 \<and>
         substate s4  s0 \<and>
         toEnvNum s2 s4 \<le> 10 - 1 \<and>
         \<not> getVarBool s4 Controller'minimalOpened' \<and>
         (\<forall>s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> getVarBool s3 Controller'minimalOpened')"])
      apply(erule exE)
    subgoal for s4
      apply(rule exI[of _ s4])
      by simp
     apply(insert invs0(1))[1]
     apply(erule conjE)
     apply(erule allE[of _ s1])
     apply(erule allE[of _ s2])
     apply(simp split: if_splits)
apply(rule cut_rl[of "\<forall> s5. toEnvP s5 \<and> substate s2 s5 \<and> substate s5 (s s0 PdOut_value paid_value opened_value) \<longrightarrow>
pred1 s1 s2 (s s0 PdOut_value paid_value opened_value) s5"])
     apply(erule allE[of _ s2])
     apply(erule impE)
    using substate_refl apply blast
     apply(unfold pred1_def)
     apply(erule impE)
      apply(insert substate_refl substate_trans substate_antisym)[1]
    apply blast
     apply assumption
      apply(rule allI)
      subgoal premises prems for s5
        apply(induction rule: state_ind)
        using prems apply simp
         apply(rule impI)

         apply((erule conjE)+)
         apply(erule allE[of _ s0])
         apply(erule impE)
        using invs0(1) substate_refl apply(simp split: if_splits)
          using vc_prems(1) apply(simp split: if_splits)
          using invs0(2) substate_refl
           apply meson

        subgoal for s5
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
      using prems(8) apply fastforce
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
  using extra338 by (auto simp add: VC338_def)

end

         
      