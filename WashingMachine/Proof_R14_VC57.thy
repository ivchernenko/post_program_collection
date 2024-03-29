theory Proof_R14_VC57
  imports ExtraInv
begin

abbreviation s where "s s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value \<equiv>
 (toEnv
       (setVarInt
         (setVarInt
           (setVarBool (setVarBool (setVarBool (setVarBool s0 Washing' startButton'value) Washing'idle' locked'value) Washing'locking' waterLevel'value)
             Washing'waterSupply' waterPresence'value)
           Washing'wash' temp'value)
         Washing'draining' freq'value))"


theorem "VC57 inv14 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC57_def inv14_def R14_def)
  apply(rule impI)
  apply(rule conjI)
   apply(rule conjI)
    apply simp
   apply(erule conjE)
   apply(erule conjE)
   apply(rotate_tac)
   apply(erule conjE)
  subgoal premises vc_prems
    apply(insert vc_prems(4))
    apply(unfold extraInv_def)[1]
    apply(erule conjE)+
    subgoal premises ei
      apply(rule allI)+
      subgoal for s1 s2 s3 s4
        apply(cases "s4 = s s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value")
        using vc_prems(2)[simplified] ei(1) apply simp
        using ei(12) substate_refl apply presburger
                apply(insert vc_prems(3))
        apply(erule conjE)
        apply(erule allE[of _ s1])
        apply(erule allE[of _ s2])
        apply(erule allE[of _ s3])
        apply(erule allE[of _ s4])
        by auto
      done
    done

