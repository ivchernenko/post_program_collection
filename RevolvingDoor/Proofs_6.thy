theory Proofs_6
  imports Requirements ExtraInv VCTheoryLemmas
begin

definition inv6 where "inv6 s \<equiv> R6 s \<and> extraInv s"

theorem proof_6_1: "VC1 inv6 s0"
  apply(simp only: VC1_def inv6_def R6_def extraInv_def)
  by auto

theorem proof_6_4: "VC4 R6 env s0 user_value pressure_value"
  apply(simp only: VC4_def inv6_def R6_def extraInv_def)
  using substate_refl  by auto

theorem proof_6_5: "VC5 inv6 env s0 user_value pressure_value"
  apply(simp only: VC5_def inv6_def R6_def extraInv_def)
  using substate_refl  by auto

theorem proof_6_6: "VC6 R6 env s0 user_value pressure_value"
  apply(simp only: VC6_def inv6_def R6_def extraInv_def)
  by auto

theorem proof_6_7: "VC7 inv6 env s0 user_value pressure_value"
  apply(simp only: VC7_def inv6_def R6_def extraInv_def)
  using substate_refl  by auto

theorem proof_6_8: "VC8 R6 env s0 user_value pressure_value"
  apply(simp only: VC8_def inv6_def R6_def extraInv_def)
  using substate_refl  by auto

theorem proof_6_9: "VC9 R6 env s0 user_value pressure_value"
  apply(simp only: VC9_def inv6_def R6_def extraInv_def)
  by auto

theorem proof_6_10: "VC10 R6 env s0 user_value pressure_value"
  apply(simp only: VC10_def inv6_def R6_def extraInv_def)
  using substate_refl  by auto

theorem proof_6_11: "VC11 inv6 env s0 user_value pressure_value"
  apply(simp only: VC11_def inv6_def R6_def extraInv_def)
  using substate_refl  by auto

theorem proof_6_12: "VC12 R6 env s0 user_value pressure_value"
  apply(simp only: VC12_def inv6_def R6_def extraInv_def)
  using substate_refl  by auto

theorem proof_6_13: "VC13 R6 env s0 user_value pressure_value"
  apply(simp only: VC13_def inv6_def R6_def extraInv_def)
  by auto

theorem proof_6_14: "VC14 R6 env s0 user_value pressure_value"
  apply(simp only: VC14_def inv6_def R6_def extraInv_def)
  using substate_refl  by auto

end