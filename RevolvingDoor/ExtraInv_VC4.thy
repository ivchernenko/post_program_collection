theory ExtraInv_VC4
  imports ExtraInv_new RequirementLemmas
begin

theorem extra_4: "VC4 extraInv env s0 user_value pressure_value"
  apply(unfold VC4_def extraInv_def)
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
      apply(insert vc_prems(1,2) ei(1))
      apply(rule conjI)
      using ei(2) apply simp
      apply(rule conjI)
      using ei(3) apply simp
      apply(rule conjI)
      using ei(4) apply simp
      apply(rule conjI)
      using  ei(5) apply simp
      apply(rule conjI)
      using ei(6) ei(7) apply simp
      apply(rule conjI)
      using ei(7) apply simp
      apply(rule conjI)
      using ei(8) apply auto[1]
      apply(rule conjI)
      using ei(9) apply auto[1]
      apply(insert ei(4))
      apply((rule P5_ex_imp_ex[OF ei(10) ei(10)]); (auto))
      done
    done
  done

end
