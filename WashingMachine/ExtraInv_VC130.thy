theory ExtraInv_VC130
  imports ExtraInv
begin

abbreviation s where "s s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value \<equiv>
  (toEnv
       (setPstate
         (setPstate
           (setVarBool
             (setVarBool
               (setVarBool
                 (setVarBool
                   (setVarInt
                     (setVarInt
                       (setVarBool (setVarBool (setVarBool (setVarBool s0 Washing' startButton'value) Washing'idle' locked'value) Washing'locking' waterLevel'value)
                         Washing'waterSupply' waterPresence'value)
                       Washing'wash' temp'value)
                     Washing'draining' freq'value)
                   Drum'rightToLeft' TURN_OFF')
                 lock' TURN_OFF')
               Drum'leftRotation' TURN_OFF')
             Drum'leftToRight' TURN_OFF')
           Washing'idle' STOP)
         Washing' Washing'idle'))"

theorem extra130: "VC130 extraInv env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC130_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
   apply simp
  apply(erule conjE)
  subgoal premises vc_prems
    apply(insert vc_prems(1))
    apply((erule conjE)+)
    subgoal premises ei
      apply(insert vc_prems(2)[simplified] ei(2))
      apply(rule conjI)
      using ei(3) ei(8) apply simp
      apply(rule conjI)
      using ei(4) apply simp
      apply(rule conjI)
      using ei(5) ei(4) apply simp
      apply(rule conjI)
      using ei(6) apply simp
      apply(rule conjI)
      using ei(7) apply simp
      apply(rule conjI)
      using ei(8) apply simp
      apply(rule conjI)
      using ei(9) apply simp
      apply(rule conjI)
      using ei(10) apply simp
      apply(rule conjI)
      using ei(11) apply simp
      apply(rule conjI)
      using ei(12) apply simp
      apply(rule conjI)
      using ei(13) ei(14) apply simp
      apply(rule conjI)
      using ei(14) apply simp
      apply(rule conjI)
      using ei(15) apply simp
      apply(rule conjI)
       apply((rule P10inv_rule[OF ei(16)]);auto)
      apply(unfold P11inv_def)[1]
      apply(rule impI)
      apply(rule allI)+
      apply(rule impI)
      apply(rule exI[of _ s0])
      apply(rule exI[of _ "(s s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value )"])
      using vc_prems(2)[simplified] apply(simp split: if_splits)
      using ei(8) substate_toEnvNum_id apply blast
      using ei(8) substate_refl by blast
    done
  done

end