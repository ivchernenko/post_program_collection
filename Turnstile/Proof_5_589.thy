theory Proof_5_589
  imports Proofs5
begin

theorem proof_5_590: "VC590 inv5 env s0 PdOut_value paid_value opened_value"
  apply(unfold VC590_def)
  apply simp
  apply(unfold inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
   apply(rule conjI)
    apply simp
   apply(unfold extraInv_def)[1]
   apply(drule conjE)
    prefer 2
    apply assumption
  apply(drule conjE)
   prefer 2
    apply assumption
  subgoal premises vc_prems
    apply((rule allI)+)
    apply(rule impI)
    apply(simp split: if_splits del: One_nat_def)
    subgoal for s1 s2
      apply(rule impE[OF isOpened_R5[of s1 s2 s0 s0]])
       apply(insert vc_prems substate_refl)[1]
      subgoal
        apply((drule conjE[of _ _ ?thesis])+)
                            defer
                            apply assumption+
        by blast
      by blast
    using vc_prems(2)  by blast