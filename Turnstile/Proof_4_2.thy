theory Proof_4_2
  imports Proofs4
begin

abbreviation s where "s s0 PdOut_value paid_value opened_value \<equiv> 
  (toEnv
       (setPstate
         (setVarBool
           (setPstate
             (setVarBool
               (setPstate
                 (setVarBool
                   (setVarBool
                     (setPstate
                       (setPstate
                         (setPstate
                           (setVarBool (setVarBool (setVarBool s0 Init' PdOut_value) Init'init' paid_value) Controller'isClosed'
                             opened_value)
                           Init'init' Controller'isClosed')
                         Controller'isClosed' EntranceController'isClosed')
                       Init' STOP)
                     Controller'minimalOpened' True)
                   EntranceController'isOpened' False)
                 Init'init' Controller'minimalOpened')
               EntranceController'isClosed' True)
             Controller'isClosed' EntranceController'isOpened')
           Controller'isOpened' False)
         Controller'minimalOpened' STOP))"

theorem proof_4_2: "VC2 inv4 env s0 PdOut_value paid_value opened_value"
  apply(unfold VC2_def)
  apply(unfold inv4_def R4_def)
  apply(rule impI)
  apply(rule conjI)
   apply(rule conjI)
    apply simp
   apply(unfold extraInv_def)
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
   apply(rule cut_rl[of "\<exists>s4. toEnvP s4 \<and>
         substate s2 s4 \<and>
         substate s4 s0 \<and>
         toEnvNum s2 s4 \<le> 100 \<and>
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
pred4 s1 s2 (s s0 PdOut_value paid_value opened_value) s5"])
     apply(erule allE[of _ s2])
     apply(erule impE)
    using substate_refl apply blast
     apply(unfold pred4_def)
     apply(erule impE)
    apply(insert substate_refl substate_trans substate_antisym)[1]
    apply metis
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

         apply(insert vc_prems(1))[1]
         apply(rule cut_rl[of False])
          apply blast
        subgoal premises ind_base
          using vc_prems(1) apply simp
          apply(insert invs0(2))
          apply((erule conjE)+)
          apply(rule cut_rl[of "toEnvNum emptyState s0 = 1"])
     using ind_base(10) substate_refl[of s0]
     apply (smt (verit) le_antisym ltime_le_toEnvNum numeral_le_one_iff semiring_norm(69))
     using substate_refl[of s0] by blast 

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
     
