theory ExtraInv_VC13
  imports ExtraInv_new RequirementLemmas
begin

theorem extra_13: "VC13 extraInv env s0 user_value pressure_value"
    apply(unfold VC13_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
   apply simp
  apply(erule conjE)
  apply(erule conjE)
  apply(erule conjE)
   apply(erule conjE)
  subgoal premises vc_prems
    apply(insert vc_prems(4))
    apply((erule conjE)+)
    subgoal premises ei
      thm ei(1)
      apply(insert vc_prems(1,2,3,5) ei(1))
      apply(rule conjI)
      using ei(2) apply simp
      apply(rule conjI)
      using ei(3) apply simp
      apply(rule conjI)
      using ei(4) ei(6) apply simp
      apply(rule conjI)
      using  ei(5) apply simp
      apply(rule conjI)
      using ei(6) ei(7) apply simp
      apply(rule conjI)
      using ei(7) apply simp
      apply(rule conjI)
      using ei(8) apply auto[1]
      apply(rule conjI)
      apply(insert ei(3))
       apply((rule P5_ex_or_all_imp_ex[OF ei(8) ei(9)]); (auto))
      using ei(10) by auto
    done
  done

end

