theory Proof_R2_VC20
  imports ExtraInv_VC20
begin

abbreviation s where "s s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value \<equiv>
 (toEnv
       (setVarInt
         (setVarInt
           (setVarBool (setVarBool (setVarBool (setVarBool s0 Washing' startButton'value) Washing'idle' locked'value) Washing'locking' waterLevel'value)
             Washing'waterSupply' waterPresence'value)
           Washing'wash' temp'value)
         Washing'draining' freq'value))"

theorem "VC20 inv2 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC20_def inv2_def R2_def)
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
      subgoal for s1 s2 s3
        apply(cases "s3 = s s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value")
        subgoal premises s3_value
          apply(simp only: s3_value substate_refl simp_thms(21, 22) toEnvP.simps)
          apply(rule P10_einv2req)
          using vc_prems(2)[simplified] ei(1) ei(15) by auto
        apply(insert vc_prems(3))
        apply(erule conjE)
        apply(erule allE[of _ s1])
        apply(erule allE[of _ s2])
        apply(erule allE[of _ s3])
        by simp
      done
    done
  using extra20 by(auto simp add: VC20_def)

end
