theory Proof_R8_VC434
  imports ExtraInv8_VC434
begin


theorem "VC434 inv8 env s0 PdOut_value paid_value opened_value"
  apply(unfold VC434_def inv8_def R8_def)
  apply rule
  apply(rule context_conjI)
  using extra434 apply(auto simp add: VC434_def)[1]
  apply rule
   apply simp
  subgoal premises prems
    apply(insert prems(2))
    apply(unfold extraInv8_def)
    apply(erule conjE)+
    subgoal premises ei
      apply(rule einv2reqP7)
      using prems(1) ei(13) by simp
    done
  done

end
