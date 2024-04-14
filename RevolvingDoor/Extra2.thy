theory Extra2
  imports ExtraInv VCTheoryLemmas
begin
 
theorem extra2: "VC2 extraInv env s0 user_value pressure_value"
  apply(simp only: VC2_def extraInv_def)
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
using prems(1-5)  prems(12) apply simp
     apply(rule exI[of _ s0])
     apply simp
     apply(rule exI[of _ "toEnv (setPstate (setVarBool (setVarAny s0 True True) brake True) user Controller'suspended)"])
  using substate_refl toEnvNum_id apply simp
  apply(rule conjI)
   apply((rule allI)+)
   apply(rule impI)
  using prems(1-5) apply(simp split: if_splits)
    apply(rule cut_rl[of "(toEnv (setPstate (setVarBool (setVarAny s0 True True) brake True) user Controller'suspended))  = s0"])
     apply simp
    apply(rule cut_rl[of "substate s0 (toEnv (setPstate (setVarBool (setVarAny s0 True True) brake True) user Controller'suspended)) "])
  using substate_trans substate_asym apply blast
  using substate_refl apply simp
   apply(simp only: One_nat_def[symmetric])
  using prems(13) apply simp
   apply blast
  apply(rule conjI)
   apply(rule allI)
  apply(rule impI)
  using prems(1-5) apply (simp split: if_splits)
 apply(rule exI[of _ s0])
    apply simp
 apply(rule exI[of _ "(toEnv (setPstate (setVarBool (setVarAny s0 user_value pressure_value) brake True) ERROR Controller'suspended)) "])
  apply simp
    apply (metis substate.simps(10) substate.simps(2) substate.simps(3) substate.simps(9) substate_asym substate_refl toEnvNum_id)
  using prems(14) apply auto[1]
  apply(rule conjI)
  using prems(1-5) prems(15) apply simp
  apply(rule conjI)
  using prems(1-5) prems(16) apply simp
  apply(rule conjI)
   apply(rule allI)
   apply(rule impI)
  using prems(1-5) apply (simp split: if_splits)
  using substate_refl prems(15) apply auto[1]
  using prems(17) apply auto[1]
  using prems(1-5) prems(18) by simp
  done

end
   