theory ExtraInv_VC2
  imports ExtraInv_new RequirementLemmas
begin

theorem extra_2: "VC2 extraInv env s0 user_value pressure_value"
  apply(unfold VC2_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
   apply simp
  apply(erule conjE)
  apply(erule conjE)
  apply(rotate_tac)
  apply(erule conjE)
  subgoal premises vc_prems
    apply(insert vc_prems(3))
    apply((erule conjE)+)
    subgoal premises ei
      apply(insert vc_prems(1,2,4) ei(2))
      apply(rule conjI)
      using ei(3) apply simp
      apply(rule conjI)
      using ei(4) apply simp
      apply(rule conjI)
      using ei(5) apply simp
      apply(rule conjI)
      using  ei(6) apply simp
      apply(rule conjI)
      using ei(5) ei(7) apply simp
      apply(rule conjI)
      using ei(8) apply simp
      apply(rule conjI)
       apply((rule P5_ex_imp_ex_or_all[OF ei(11) ei(9)]); (auto))
      apply(rule conjI)
      using ei(10) apply auto[1]
      using ei(11) by auto
    done
  done

end