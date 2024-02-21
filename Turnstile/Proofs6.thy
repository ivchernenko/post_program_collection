theory Proofs6
  imports Requirements VCTheoryLemmas
begin

definition inv6 where "inv6 s \<equiv> R6 s \<and> extraInv s"

theorem proof_6_1: "VC1 inv6 s0"
  apply(unfold VC1_def inv6_def R6_def extraInv_def)
  by auto

theorem proof_6_2: "VC2 R6 env s0 PdOut_value paid_value opened_value"
  apply(unfold VC2_def inv6_def R6_def extraInv_def)
  by auto

theorem proof_6_9: "VC9 R6 env s0 PdOut_value paid_value opened_value"
  apply(unfold VC9_def inv6_def R6_def extraInv_def)
  by auto

theorem proof_6_14: "VC14 R6 env s0 PdOut_value paid_value opened_value"
  apply(unfold VC14_def inv6_def R6_def extraInv_def)
  by auto

theorem proof_6_15: "VC15 R6 env s0 PdOut_value paid_value opened_value"
  apply(unfold VC15_def inv6_def R6_def extraInv_def)
  by auto

end