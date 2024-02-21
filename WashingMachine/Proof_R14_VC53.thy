theory Proof_R14_VC53 
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


theorem "VC53 inv14 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC53_def inv14_def R14_def)
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
         apply(rule impI)
        apply(subgoal_tac "s3 = s0 \<and> substate s0 (s s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value) \<and>
(toEnvNum s0 (s s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value) = 1) = True")
        subgoal premises req_prems
          apply(rule rev_mp[OF req_prems(2)])
          apply(simp only: req_prems(1,3) substate_refl simp_thms(21, 22) toEnvP.simps ei(1))
          apply(rule P11_einv2req)
          using vc_prems(2)[simplified] ei by auto
        apply(simp split: if_splits)
        using ei(1) substate_toEnvNum_id apply blast
              apply(insert vc_prems(3))
        apply(erule conjE)
        apply(erule allE[of _ s1])
        apply(erule allE[of _ s2])
        apply(erule allE[of _ s3])
        apply(erule allE[of _ s4])
        by auto
      done
    done
  using extra53 by(auto simp add: VC53_def)

end
