theory ExtraInv8_VC506
  imports ExtraInv8
begin


theorem extra506: "VC506 extraInv8 env s0 PdOut_value paid_value opened_value"
  apply(unfold VC506_def extraInv8_def)
  apply rule+
   apply simp
  apply(erule conjE)
  subgoal premises vc_prems
    apply(insert vc_prems(1))
    apply(erule conjE)+
    subgoal premises ei
      apply(insert vc_prems(2)[simplified] ei(2))
      apply rule
      using ei(3) apply simp
      apply rule
      using ei(4) apply simp
      apply rule
      using ei(5) apply simp
      apply rule
      using ei(6) substate_refl  apply simp
      apply rule
      using ei(7) apply simp
      apply rule
      using ei(8) apply simp
      apply rule
      using ei(9) apply simp
      apply rule
      using ei(10) apply simp
      apply rule
       apply simp
      apply rule
       apply simp
      apply rule
       apply simp
      apply rule
       apply(insert ei(14))[1]
      apply((erule pattern7_simp);(auto simp add: substate_refl toEnvNum_id))
       apply (metis ei(6) substate.simps(2) toEnvP.elims(2))
      apply(insert ei(15))
      apply((erule pattern7_simp);(auto simp add: substate_refl toEnvNum_id))
      by (metis ei(6) substate.simps(2) toEnvP.elims(2))
    done
  done

end

