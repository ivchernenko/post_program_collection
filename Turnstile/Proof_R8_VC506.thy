theory Proof_R8_VC506
  imports ExtraInv8_VC506
begin

theorem "VC506 inv8 env s0 PdOut_value paid_value opened_value"
  apply(unfold VC506_def inv8_def R8_def)
  apply rule
  apply(rule context_conjI)
  using extra506 apply(auto simp add: VC506_def)[1]
  apply rule
   apply simp
  subgoal premises prems
    apply(insert prems(2))
    apply(unfold extraInv8_def)
    apply(erule conjE)+
    subgoal premises ei
      apply(cases "getVarBool s0 passed'")
      apply(rule einv2reqP7)
      using prems(1) ei(13) apply simp
      apply(rule einv2reqP7)
      using prems(1) ei(14) by simp
    done
  done
 
