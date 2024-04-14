theory Proof_4_4
  imports Proofs_4 Extra4
begin

abbreviation s where "s s0 user_value pressure_value \<equiv>
  (toEnv (setVarAny s0 user_value pressure_value))"

theorem proof_4_4: "VC4 inv4 env s0 user_value pressure_value"
  apply(simp only: VC4_def inv4_def R4_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
   apply(rule conjI)
    apply simp
  apply((rule allI)+)
    apply(rule impI)
 subgoal premises prems for s1 s2 s3
    apply(cases "s3 = s s0 user_value pressure_value")
     apply(cases "s2 = s s0 user_value pressure_value")   
      using prems(2)  apply (simp split: if_splits)
      using prems(1)
        apply (smt (z3) getPstate.simps(9) substate_toEnvNum_id)
      apply(rule cut_rl[of "substate s2 s0 \<and> toEnvNum s2 s0 <DELAY'TIMEOUT"])
      using prems(1)
       apply (smt (z3) getPstate.simps(9) prems(2) substate_refl) 
      using prems(2) apply (simp split: if_splits)
      apply(rule cut_rl[of "substate s3 s0"])
      using prems apply meson
      using prems(2)  by (simp split: if_splits)
    apply(simp only: extraInv_def[symmetric])
    using extra4 VC4_def by auto

end
  