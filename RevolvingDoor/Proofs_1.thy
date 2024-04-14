theory Proofs_1
  imports Requirements ExtraInv VCTheoryLemmas
begin

definition inv1 where "inv1 s \<equiv> R1 s \<and> extraInv s"

theorem proof_1_1: "VC1 inv1 s0"
  apply(simp only: VC1_def inv1_def R1_def extraInv_def)
  by auto

theorem proof_1_2: "VC2 R1 env s0 user_value pressure_value"
  apply(simp only: VC2_def R1_def)
  by auto

theorem proof_1_3: "VC3 R1 env s0 user_value pressure_value"
  apply(simp only: VC3_def R1_def)
  by auto

theorem proof_1_4: "VC4 R1 env s0 user_value pressure_value"
  apply(simp only: VC4_def R1_def)
  by auto

theorem proof_1_5: "VC5 R1 env s0 user_value pressure_value"
  apply(simp only: VC5_def R1_def)
  by auto

theorem proof_1_6: "VC6 R1 env s0 user_value pressure_value"
  apply(simp only: VC6_def R1_def)
  by auto

theorem proof_1_7: "VC7 R1 env s0 user_value pressure_value"
  apply(simp only: VC7_def R1_def)
  by auto

theorem proof_1_9: "VC9 R1 env s0 user_value pressure_value"
  apply(simp only: VC9_def R1_def)
  by auto

theorem proof_1_10: "VC10 R1 env s0 user_value pressure_value"
  apply(simp only: VC10_def R1_def)
  by auto

theorem proof_1_11: "VC11 R1 env s0 user_value pressure_value"
  apply(simp only: VC11_def R1_def)
  by auto

theorem proof_1_12: "VC12 R1 env s0 user_value pressure_value"
  apply(simp only: VC12_def R1_def)
  by auto

theorem proof_1_13: "VC13 R1 env s0 user_value pressure_value"
  apply(simp only: VC13_def R1_def)
  by auto

end