theory ExtraInv4_VC4
  imports ExtraInv4
begin

theorem "VC4 extraInv env s0 user_value pressure_value"
  apply(unfold VC4_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  apply simp
  apply(erule conjE)
  subgoal premises vc_prems
    apply(insert vc_prems(1))
    apply(erule conjE)+
    subgoal premises ei
      apply(insert vc_prems(2)[simplified] ei(2))
      apply rule
       apply((rule P9inv_simp[OF ei(3)]);auto)
       apply (simp add: ei(6))
      apply rule
      using ei(4) apply simp
      apply rule
      using ei(5) apply simp
      apply rule
      using ei(6) apply simp
      apply rule
      using ei(7) apply simp
      using ei(8) by simp
    done
  done

end
      