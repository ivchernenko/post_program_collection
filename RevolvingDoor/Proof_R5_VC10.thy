theory Proof_R5_VC10
  imports  ExtraInv_VC10
begin

abbreviation s where "s s0 user_value pressure_value \<equiv>
(toEnv (setVarAny s0 user_value pressure_value))"

theorem proof_5_10: "VC10 inv5 env s0 user_value pressure_value"
  apply(unfold VC10_def inv5_def R5_def)
  apply(rule impI)
  apply(rule cut_rl[of "extraInv (s s0 user_value pressure_value)"])
   apply(rule conjI)
    apply(rule conjI)
     apply simp
    apply(erule conjE)
    apply(erule conjE)
    apply(erule conjE)
    apply(erule conjE)
    apply(unfold extraInv_def)[1]
  subgoal premises vc_prems
    thm vc_prems
    apply(insert vc_prems(1))
    apply((erule conjE)+)
    subgoal premises ei
      apply(rule P5_left2req[OF ei(9)])
      using vc_prems(2,3,4,6) by simp
    done
  using extra_10 by(auto simp add: VC10_def)

end
      

