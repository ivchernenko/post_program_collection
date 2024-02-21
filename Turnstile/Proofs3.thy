theory Proofs3
  imports Requirements VCTheoryLemmas
begin

definition inv3 where "inv3 s \<equiv> R3 s \<and> extraInv s"

theorem proof_3_1: "VC1 inv3 s0"
  apply(unfold VC1_def inv3_def R3_def extraInv_def)
  by auto

theorem proof_3_2: "VC2 R3 env s0 PdOut_value paid_value opened_value"
  apply(unfold VC2_def inv3_def R3_def extraInv_def)
  by auto

theorem proof_3_370: "VC370 R3 env s0 PdOut_value paid_value opened_value"
  apply(unfold VC370_def inv3_def R3_def extraInv_def)
  by auto

end