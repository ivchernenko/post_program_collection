theory ExtraInv8_VC338
  imports ExtraInv8
begin

theorem extra338: "VC338 extraInv8 env s0 PdOut_value paid_value opened_value"
  apply(unfold VC338_def extraInv8_def)
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
      using ei(6) apply simp
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
       apply simp
      apply(insert ei(11))
      apply((erule pattern7_simp); (auto simp add: substate_refl toEnvNum_id))
      done
    done
  done

end