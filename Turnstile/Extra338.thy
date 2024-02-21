theory Extra338
  imports ExtraInv VCTheoryLemmas
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
                     (setVarBool (setVarBool (setVarBool s0 Init' PdOut_value) Init'init' paid_value) Controller'isClosed'
                       opened_value)
                     Controller'minimalOpened' True)
                   EntranceController'isOpened' False)
                 Init'init' Controller'minimalOpened')
               EntranceController'isClosed' True)
             Controller'isClosed' EntranceController'isOpened')
           Controller'isOpened' False)
         Controller'minimalOpened' STOP))"

theorem extra338: "VC338 extraInv env s0 PdOut_value paid_value opened_value"
  apply(unfold VC338_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
   apply simp
  apply(erule conjE)
  apply(erule conjE)
  subgoal premises vc_prems
    apply(insert vc_prems(2))
    apply((erule conjE)+)
    subgoal premises ei
      apply(rule conjI)
      using vc_prems(1) ei(1) ei(2) apply simp
      apply(rule conjI)
       apply(insert ei(1) ei(3))[1]
       apply(rule allI)
      subgoal for s1
        apply(cases "s1 = (s s0 PdOut_value paid_value opened_value)")
         apply(rule impI)
         apply(erule allE[of _ s0])
         apply(erule impE)
        using vc_prems(1) substate_refl apply simp
         apply(erule exE)
        subgoal for s2
          apply(rule exI[of _ s2])
          by simp
        by simp
      apply(rule conjI)
      using vc_prems(1) ei(1) ei(4) apply simp
      apply(rule conjI)
      using vc_prems(1) ei(1) ei(5) apply simp
      apply(rule conjI)
       apply(insert ei(1) ei(6))[1]
       apply(rule allI)
      subgoal for s1
        apply(cases "s1 = (s s0 PdOut_value paid_value opened_value)")
         apply(rule impI)
        apply(rule exI[of _ s0])
         apply(rule exI[of _ "s s0 PdOut_value paid_value opened_value"])
        using vc_prems(1) substate_refl toEnvNum_id apply simp
        by simp
      apply(rule conjI)
      using vc_prems(1) ei(1) ei(7) apply simp
      apply(rule conjI)
      using vc_prems(1) ei(1) ei(8) apply simp
      apply(rule conjI)
      using vc_prems(1) ei(1) ei(9) apply simp
      apply(rule conjI)
      using vc_prems(1) ei(1) ei(10) apply simp
      apply(rule conjI)
      using vc_prems(1) ei(1) ei(11) apply simp
      apply(rule conjI)
      using vc_prems(1) ei(1) ei(12) apply simp
      apply(rule conjI)
      using vc_prems(1) ei(1) ei(13) apply simp
     apply(rule conjI)
      using vc_prems(1) ei(1) ei(14) apply simp
     apply(rule conjI)
       apply(insert ei(1) ei(15))[1]
       apply(rule allI)
      subgoal for s1
        apply(cases "s1 = (s s0 PdOut_value paid_value opened_value)")
         apply(rule impI)
        apply(rule exI[of _ s0])
         apply(rule exI[of _ "s s0 PdOut_value paid_value opened_value"])
         apply(insert vc_prems(1) substate_refl toEnvNum_id)
        apply(rule conjI)
          apply simp
         apply(rule conjI)
          apply simp
         apply(rule conjI)
          apply simp
         apply(rule conjI)
          apply simp
         apply(rule conjI)
          apply simp
         apply(rule conjI)
          apply simp
        using substate_antisym
         apply (metis (no_types, lifting))
        by simp
      apply(rule conjI)
      using vc_prems(1) ei(1) ei(16) apply simp
      apply(rule conjI)
      using vc_prems(1) ei(1) ei(17) apply simp
      apply(rule conjI)
      using vc_prems(1) ei(1) ei(18) apply simp
      apply(rule conjI)
      using vc_prems(1) ei(1) ei(19) apply simp
       apply blast
      apply(rule conjI)
       apply(insert ei(1) ei(20))[1]
        apply(rule allI)
      subgoal for s1
        apply(cases "s1 = (s s0 PdOut_value paid_value opened_value)")
         apply(rule impI)
        apply(rule disjI1)
        apply(rule exI[of _ s0])
         apply(rule exI[of _ "s s0 PdOut_value paid_value opened_value"])
         apply(insert vc_prems(1) ei(17) substate_refl toEnvNum_id)
         apply(rule conjI)
          apply simp
         apply(rule conjI)
          apply simp
         apply(rule conjI)
          apply simp
         apply(rule conjI)
          apply simp
         apply(rule conjI)
          apply simp
         apply(rule conjI)
          apply simp
         apply(rule conjI)
          apply auto[1]
         apply(rule conjI)
          apply simp
        using substate_antisym
         apply (metis less_numeral_extra(1) less_numeral_extra(3) substate_trans) 
        by simp
      apply(rule conjI)
      using vc_prems(1) ei(1) ei(21) apply simp
      apply(rule conjI)
      using vc_prems(1) ei(1) ei(22) apply simp
      apply(rule conjI)
      using vc_prems(1) ei(1) ei(23) apply simp
      apply(rule conjI)
      using vc_prems(1) ei(1) ei(24) apply simp
      apply(rule conjI)
      using vc_prems(1) ei(1) ei(25) apply simp
      apply(rule conjI)
      using vc_prems(1) ei(1) ei(26) apply simp
      apply(rule conjI)
      using vc_prems(1) ei(1) ei(27) apply simp
      apply(rule conjI)
      using vc_prems(1) ei(1) ei(28) apply simp
      apply(rule conjI)
      using vc_prems(1) ei(1) ei(29) apply simp
      using vc_prems(1) ei(1) ei(30) by simp
    done
  done

end