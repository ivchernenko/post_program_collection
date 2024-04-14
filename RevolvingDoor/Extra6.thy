theory Extra6
  imports ExtraInv VCTheoryLemmas
begin

theorem extra6: "VC6 extraInv env s0 userValue pressure_value"
  apply(simp only: VC6_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
   apply simp
  apply((drule conjE)+)
                   prefer 18
                   apply assumption
                  prefer 17
                  apply assumption
                 prefer 16
                 apply assumption
                prefer 15
                apply assumption
               prefer 14
               apply assumption
              prefer 13
              apply assumption
             prefer 12
             apply assumption
            prefer 11
            apply assumption
           prefer 10
           apply assumption
          prefer 9
          apply assumption
         prefer 8
         apply assumption
        prefer 7
        apply assumption
       prefer 6
       apply assumption
      prefer 5
      apply assumption
     prefer 4
     apply assumption
    prefer 3
    apply assumption
   prefer 2
   apply assumption
  subgoal premises prems
    apply(rule conjI)
    using prems(1-5) prems(6) apply simp
    apply(rule conjI)
    using prems(1-5) prems(7) apply simp
    apply(rule conjI)
    using prems(1-5) prems(8) apply simp
    apply(rule conjI)
    using prems(1-5) prems(9) apply simp
     apply blast
    apply(rule conjI)
    using prems(1-5) prems(10) apply simp
    apply(rule conjI)
    using prems(1-5) prems(11) apply simp
    apply(rule conjI)
    using prems(1-5) prems(12) apply -[1]
     apply(rule allI)
     apply(rule impI)
    subgoal for s1
      apply(cases "s1 =  (toEnv
       (setPstate (setVarBool (setVarBool (setVarAny s0 userValue pressure_value) rotation False) brake True) ERROR
         Controller'suspended))")
       apply(rule exI[of _ s0])
      apply(rule exI[of _ " (toEnv
       (setPstate (setVarBool (setVarBool (setVarAny s0 userValue pressure_value) rotation False) brake True) ERROR
         Controller'suspended))"])
      using substate_refl toEnvNum_id  apply simp
      by (simp split: if_splits)
    apply(rule conjI)
    using prems(1-5) prems(13) apply -[1]
     apply((rule allI)+)
     apply(rule impI)
      apply(simp split: if_splits)
    apply(rule cut_rl[of "s0 =  (toEnv
          (setPstate (setVarBool (setVarBool (setVarAny s0 userValue True) rotation False) brake True) user Controller'suspended))"])
       apply simp
    apply(rule cut_rl[of "substate s0  (toEnv
          (setPstate (setVarBool (setVarBool (setVarAny s0 userValue True) rotation False) brake True) user Controller'suspended))"])
    using substate_trans substate_asym apply blast
    using substate_refl apply simp
     apply blast
    apply(rule conjI)
    using prems(1-5) prems(14) apply -[1]
     apply(rule allI)
     apply(rule impI)
    subgoal for s1
      apply(cases "s1= (toEnv
       (setPstate (setVarBool (setVarBool (setVarAny s0 userValue pressure_value) rotation False) brake True) ERROR
         Controller'suspended))") 
      apply(rule exI[of _ s0])
      apply(rule exI[of _ " (toEnv
       (setPstate (setVarBool (setVarBool (setVarAny s0 userValue pressure_value) rotation False) brake True) ERROR
         Controller'suspended))"])
      using substate_refl toEnvNum_id  apply (simp)
       apply(rule allI)
      apply((rule impI)+)
   apply(rule cut_rl[of "s0 =  (toEnv
          (setPstate (setVarBool (setVarBool (setVarAny s0 userValue True) rotation False) brake True) user Controller'suspended))"])
       apply simp
    apply(rule cut_rl[of "substate s0  (toEnv
          (setPstate (setVarBool (setVarBool (setVarAny s0 userValue True) rotation False) brake True) user Controller'suspended))"])
    using substate_trans substate_asym apply blast
    using substate_refl apply simp
    by (simp split: if_splits)
  apply(rule conjI)
  using prems(1-5) prems(15) apply simp
  apply(rule conjI)
  using prems(1-5) prems(16) apply simp
  apply(rule conjI)
  using prems(1-5) prems(15) prems(17) apply simp
  using prems(1-5) prems(18) by simp
  done

end
