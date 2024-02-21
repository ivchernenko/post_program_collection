theory Proof_R8_VC458
  imports ExtraInv8_VC458
begin


theorem "VC458 inv8 env s0 PdOut_value paid_value opened_value"
  apply(unfold VC458_def inv8_def R8_def)
  apply rule
  apply(rule context_conjI)
  using extra458 apply(auto simp add: VC458_def)[1]
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