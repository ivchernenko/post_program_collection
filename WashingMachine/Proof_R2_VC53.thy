theory Proof_R2_VC53
  imports ExtraInv_VC53
begin

abbreviation s where "s s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value \<equiv>
 (toEnv
   (setVarBool
     (setVarInt
       (setVarInt
         (setVarBool (setVarBool (setVarBool (setVarBool s0 Washing' startButton'value) Washing'idle' locked'value) Washing'locking' waterLevel'value)
           Washing'waterSupply' waterPresence'value)
         Washing'wash' temp'value)
       Washing'draining' freq'value)
     Drum'leftRotation' SUFFICIENT'))"

theorem "VC53 inv2 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC53_def inv2_def R2_def)
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
        using vc_prems(2)[simplified] apply simp
        using ei(1) ei(4) substate_refl apply presburger
                apply(insert vc_prems(3))
        apply(erule conjE)
        apply(erule allE[of _ s1])
        apply(erule allE[of _ s2])
        apply(erule allE[of _ s3])
        by simp
      done
    done
  using extra53 by(auto simp add: VC53_def)

end
