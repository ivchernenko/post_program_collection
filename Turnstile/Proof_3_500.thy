theory Proof_3_500
  imports Proofs3
begin

theorem proof_3_500: "VC500 inv3 env s0 PdOut_value paid_value opened_value"
  apply(unfold VC500_def)
  apply simp
  apply(unfold inv3_def R3_def)
  apply(rule impI)
  apply(rule conjI)
   apply(rule conjI)
    apply simp
   apply(unfold extraInv_def)[1]
   apply(erule conjE)
   apply(erule conjE)
  subgoal premises vc_prems
    apply((rule allI)+)
    apply(rule impI)
    apply(simp split: if_splits)
    using vc_prems(1,3) substate_refl[of s0] apply blast
    using vc_prems(2) by auto
