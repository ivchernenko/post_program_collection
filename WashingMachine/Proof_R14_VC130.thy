theory Proof_R14_VC130
  imports ExtraInv_VC130
begin

theorem "VC130 inv14 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC130_def inv14_def R14_def)
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
         apply (metis ei(7) substate_toEnvNum_id)
               apply(insert vc_prems(3))
        apply(erule conjE)
        apply(erule allE[of _ s1])
        apply(erule allE[of _ s2])
        apply(erule allE[of _ s3])
        apply(erule allE[of _ s4])
        by auto
      done
    done
  using extra130 by(auto simp add: VC130_def)

end
