theory Proof_6_351
  imports Proofs6
begin

theorem extraInv_proof: "VC351 extraInv env s0 PdOut_value paid_value opened_value"
  sorry

abbreviation VC where "VC inv0 env s0 PdOut_value paid_value opened_value \<equiv> VC351 inv0 env s0 PdOut_value paid_value opened_value"
lemmas VC_def = VC351_def
lemmas Req_def = R6_def
abbreviation loopinv where "loopinv s \<equiv> inv6 s"
lemmas loopinv_def = inv6_def


theorem req_proof: "VC inv6 env s0 input_values"
  apply(unfold VC_def)
  apply simp
  apply(unfold loopinv_def Req_def)
  apply(rule impI)
  apply(erule conjE)
  apply(erule conjE)
  apply(rule conjI)
   apply(rule conjI)
    apply simp
   apply(unfold extraInv_def)[1]
  subgoal premises vc_prems
    apply(rule allI)
    apply(rule impI)
    apply(simp split: if_splits)
    using vc_prems(1,3)
    sledgehammer
     apply (meson substate_refl)
    using vc_prems(2) by auto
  using extraInv_proof by (auto simp add: VC_def)
