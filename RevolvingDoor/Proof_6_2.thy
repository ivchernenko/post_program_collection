theory Proof_6_2
  imports Proofs_6 Extra2
begin


theorem proof_6_2: "VC2 inv6 env s0 user_value pressure_value"
  apply(simp only: VC2_def inv6_def R6_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
   apply(rule conjI)
    apply simp
   apply(rule allI)
   apply(rule impI)
  subgoal premises prems for s1
    using prems(2) apply (simp split: if_splits)
    using prems(1) apply simp
    using substate_refl apply presburger
    using prems(1) by blast
  apply(simp only: extraInv_def[symmetric])
  using extra2 VC2_def by auto

end