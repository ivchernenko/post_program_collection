theory Proof_R5_VC3
  imports  ExtraInv_VC3
begin

abbreviation s where "s s0 user_value pressure_value \<equiv>
(toEnv (setPstate (setVarBool (setVarAny s0 user_value pressure_value) rotation True) ERROR Controller'rotating))"

theorem proof_5_3: "VC3 inv5 env s0 user_value pressure_value"
  apply(unfold VC3_def inv5_def R5_def)
  apply(rule impI)
  apply(rule cut_rl[of "extraInv (s s0 user_value pressure_value)"])
   apply(rule conjI)
    apply(rule conjI)
     apply simp
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
      using vc_prems(2,3,5) by simp
    done
  using extra_3 by(auto simp add: VC3_def)

end
      

