theory ExtraInv_VC53
  imports ExtraInv
begin

theorem extra53: "VC53 extraInv env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC53_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
   apply simp
  apply(erule conjE)
  subgoal premises vc_prems
    apply(insert vc_prems(1))
    apply((erule conjE)+)
    subgoal premises ei
      apply(insert vc_prems(2)[simplified] ei(2))
      apply(rule conjI)
      using ei(3) apply simp
      apply(rule conjI)
      using ei(4) apply simp
      apply(rule conjI)
      using ei(5) ei(4) apply simp
      apply(rule conjI)
      using ei(6) apply simp
      apply(rule conjI)
      using ei(7) apply simp
      apply(rule conjI)
      using ei(8) apply simp
      apply(rule conjI)
      using ei(9) apply simp
      apply(rule conjI)
      using ei(10) apply simp
      apply(rule conjI)
      using ei(11) apply simp
      apply(rule conjI)
      using ei(12) apply simp
      apply(rule conjI)
      using ei(13) ei(14) apply simp
      apply(rule conjI)
      using ei(14) apply simp
      apply(rule conjI)
      using ei(15) apply simp
      apply(rule conjI)
       apply((rule P10inv_rule[OF ei(16)]);auto)
      apply((rule P11inv_rule[OF ei(17)]);auto)
      done
    done
  done

end