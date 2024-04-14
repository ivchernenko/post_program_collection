theory Proof_1_14
  imports Proofs_1
begin

theorem proof_1_14: "VC14 inv1 env s0 user_value pressure_value"
  apply(simp only: VC14_def inv1_def R1_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
   apply(rule conjI)
    apply simp
   apply((rule allI)+)
   apply(rule impI)
  subgoal premises prems for s1 s2
    using prems(2) apply(simp split: if_splits)
    using prems
    apply (smt (z3) getPstate.simps(9) le_refl ltime.simps(9) substate_toEnvNum_id)
        using prems(1)
    by (meson prems(2))
    