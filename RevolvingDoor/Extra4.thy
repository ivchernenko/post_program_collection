theory Extra4
  imports ExtraInv VCTheoryLemmas
begin

theorem extra4: "VC4 extraInv env s0 user_value pressure_value"
  apply(simp only: VC4_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
   apply simp
  apply((drule conjE)+)
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
     apply(rule allI)
     apply(rule impI)
    subgoal for s1
      apply(cases "s1=(toEnv (setVarAny s0 user_value pressure_value))")
    using prems(1-4) prems(5) apply -
      apply(drule allE[of _ s0])
       prefer 2
       apply assumption
      apply(drule impE)
    using  substate_refl apply simp
       prefer 2
       apply assumption
      apply(drule disjE)
        prefer 3
        apply assumption
       apply(rule disjI1)
      apply simp
      apply(rule disjI2)
      apply(drule exE)
       prefer 2
    apply assumption
      apply(drule exE)
       prefer 2
      apply assumption
    subgoal for s2 s3
      apply(rule exI[of _ s2])
      apply(rule exI[of _ s3])
      apply(rule conjI)
       apply fast
      apply(rule conjI)
       apply fast
      apply(rule conjI)
       apply auto[1]
      apply(rule conjI)
       apply fast
      apply(rule conjI)
       apply fast
      apply(rule conjI)
       apply fast
      apply(rule conjI)
       apply fast
      apply(rule conjI)
       apply fast
      apply((rule allI)+)
      apply simp
      by (smt (verit) substate.simps(2) substate.simps(9) substate_toEnvNum_id toEnvP.simps(1))
    using prems(5) by (simp split: if_splits)
  apply(rule conjI)
  using prems(1-4) prems(6) apply simp
  apply(rule conjI)
  using prems(1-4) prems(7) apply simp
  apply(rule conjI)
  using prems(1-4) prems(8) apply simp
   apply blast
  apply(rule conjI)
  using prems(1-4) prems(9) apply simp
  apply(rule conjI)
  using prems(1-4) prems(10) apply simp
  apply(rule conjI)
  using prems(1-4) prems(11) apply simp
  apply(rule conjI)
  using prems(1-4) prems(12) apply simp
   apply blast
  apply(rule conjI)
  using prems(1-4) prems(13) apply simp
  apply(rule conjI)
  using prems(1-4) prems(14) substate_refl apply simp
  apply(rule conjI)
  using prems(1-4) prems(15) apply simp
  apply(rule conjI)
  using prems(1-4) prems(16) apply simp
  using prems(1-4) prems(17) by simp
  done

end