theory Proof_R8_VC338
  imports ExtraInv8_VC338
begin

theorem "VC338 inv8 env s0 PdOut_value paid_value opened_value"
  apply(unfold VC338_def inv8_def R8_def)
  apply rule
  apply(rule context_conjI)
  using extra338 apply(simp add: VC338_def)
  apply rule
   apply simp
  subgoal premises prems
    apply(insert prems(2))
    apply(unfold extraInv8_def)
    apply(erule conjE)+
    subgoal premises ei
      apply(rule einv2reqP7)
      using prems(1) ei(14) by simp
    done
  done

end
