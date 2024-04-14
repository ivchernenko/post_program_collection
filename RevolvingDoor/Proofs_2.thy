theory Proofs_2
  imports Requirements ExtraInv VCTheoryLemmas
begin

definition inv2 where "inv2 s \<equiv> R2 s \<and> extraInv s"

theorem proof_2_1: "VC1 inv2 s0"
  apply(simp only: VC1_def inv2_def R2_def extraInv_def)
  by auto

theorem proof_2_2: "VC2 R2 env s0 user_value pressure_value"
  apply(simp only: VC2_def inv2_def R2_def extraInv_def)
  by auto

theorem proof_2_3: "VC3 R2 env s0 user_value pressure_value"
  apply(simp only: VC3_def inv2_def R2_def extraInv_def)
  by auto

theorem proof_2_4: "VC4 R2 env s0 user_value pressure_value"
  apply(simp only: VC4_def inv2_def R2_def extraInv_def)
  by auto

theorem proof_2_5: "VC5 inv2 env s0 user_value pressure_value"
  apply(simp only: VC5_def inv2_def R2_def extraInv_def)
  by auto

theorem proof_2_6: "VC6 R2 env s0 user_value pressure_value"
  apply(simp only: VC6_def inv2_def R2_def extraInv_def)
  by auto

theorem proof_2_7: "VC7 inv2 env s0 user_value pressure_value"
  apply(simp only: VC7_def inv2_def R2_def extraInv_def)
  by auto

theorem proof_2_8: "VC8 R2 env s0 user_value pressure_value"
  apply(simp only: VC8_def inv2_def R2_def extraInv_def)
  apply auto
   apply(drule allE[of _ "(toEnv (reset (setVarAny s0 True False) user))"])
    prefer 2
    apply assumption
   apply auto
  using substate_toEnvNum_id by blast

theorem proof_2_9: "VC9 R2 env s0 user_value pressure_value"
  apply(simp only: VC9_def inv2_def R2_def extraInv_def)
  by auto

theorem proof_2_10: "VC10 R2 env s0 user_value pressure_value"
  apply(simp only: VC10_def inv2_def R2_def extraInv_def)
  by auto

theorem proof_2_11: "VC11 inv2 env s0 user_value pressure_value"
  apply(simp only: VC11_def inv2_def R2_def extraInv_def)
  by auto

theorem proof_2_12: "VC12 R2 env s0 user_value pressure_value"
  apply(simp only: VC12_def inv2_def R2_def extraInv_def)
  by auto

theorem proof_2_13: "VC13 R2 env s0 user_value pressure_value"
  apply(simp only: VC13_def inv2_def R2_def extraInv_def)
  by auto

theorem proof_2_14: "VC14 R2 env s0 user_value pressure_value"
  apply(simp only: VC14_def inv2_def R2_def extraInv_def)
  apply auto
   apply(drule allE[of _ "(toEnv (setVarAny s0 user_value False))"])
    prefer 2
    apply assumption
   apply auto
  using substate_toEnvNum_id by blast

end
