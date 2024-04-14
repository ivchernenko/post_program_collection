theory ExtraInv4_VC12
  imports ExtraInv4
begin

theorem "VC12 extraInv env s0 user_value pressure_value"
  apply(unfold VC12_def extraInv_def)
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
       apply simp
      apply rule
       apply(cases "ltime s0 Controller' = 1")
      apply((rule P9inv_simp[OF ei(4)]);auto)
         apply (simp add: ei(8))
        apply (simp add: ei(8))
       apply((rule P9inv_simp[OF ei(5)]);auto)
        apply (simp add: ei(8))
       apply (simp add: Suc_lessI)
      apply rule
       apply simp
      apply rule
      using ei(6) apply simp
      apply rule
      using ei(7) apply simp
      using ei(8) by simp
    done
  done

end

