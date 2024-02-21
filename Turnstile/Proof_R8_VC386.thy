theory Proof_R8_VC386
  imports ExtraInv8_VC386
begin

theorem "VC386 inv8 env s0 PdOut_value paid_value opened_value"
  apply(unfold VC386_def inv8_def R8_def)
  apply rule
  apply(rule context_conjI)
  using extra386 apply(auto simp add: VC386_def)[1]
  apply rule
   apply simp
  subgoal premises prems
    apply(insert prems(2))
    apply(unfold extraInv8_def)
    apply(erule conjE)+
    subgoal premises ei
      apply(rule einv2reqP7)
      using prems(1) ei(10) by simp
    done
  done

end