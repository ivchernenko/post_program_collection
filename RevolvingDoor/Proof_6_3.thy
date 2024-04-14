theory Proof_6_3
  imports Proofs_6
begin

theorem proof_6_2: "VC3 inv6 env s0 user_value pressure_value"
  apply(simp only: VC3_def inv6_def R6_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
   apply(rule conjI)
    apply simp
   apply(rule allI)
   apply(rule impI)
  subgoal premises prems for s1
    using prems(2) apply (simp split: if_splits)
    using prems(1) 
     apply (simp add: substate_refl)
    using prems(1) by blast
    