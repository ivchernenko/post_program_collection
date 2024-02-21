theory Proofs2
  imports Requirements VCTheoryLemmas
begin

definition inv2 where "inv2 s \<equiv> R2 s \<and> extraInv s"

theorem proof_2_1: "VC1 inv2 s0"
  apply(unfold VC1_def inv2_def R2_def extraInv_def)
  by auto

theorem proof_2_338: "VC338 R2 env s0 PdOut_value paid_value opened_value"
  apply(unfold VC338_def inv2_def R2_def extraInv_def)
  by auto

theorem proof_2_339: "VC339 R2 env s0 PdOut_value paid_value opened_value"
  apply(unfold VC339_def inv2_def R2_def extraInv_def)
  by auto

theorem proof_2_340: "VC340 R2 env s0 PdOut_value paid_value opened_value"
  apply(unfold VC340_def inv2_def R2_def extraInv_def)
  by auto

theorem proof_2_341: "VC341 R2 env s0 PdOut_value paid_value opened_value"
  apply(unfold VC341_def inv2_def R2_def extraInv_def)
  by auto

theorem proof_2_342: "VC342 R2 env s0 PdOut_value paid_value opened_value"
  apply(unfold VC342_def inv2_def R2_def extraInv_def)
  by auto

theorem proof_2_343: "VC343 R2 env s0 PdOut_value paid_value opened_value"
  apply(unfold VC343_def inv2_def R2_def extraInv_def)
  by auto

theorem proof_2_344: "VC344 R2 env s0 PdOut_value paid_value opened_value"
  apply(unfold VC344_def inv2_def R2_def extraInv_def)
  by auto

theorem proof_2_345: "VC345 R2 env s0 PdOut_value paid_value opened_value"
  apply(unfold VC345_def inv2_def R2_def extraInv_def)
  by auto

theorem proof_2_346: "VC346 R2 env s0 PdOut_value paid_value opened_value"
  apply(unfold VC346_def inv2_def R2_def extraInv_def)
  by auto

theorem proof_2_347: "VC347 R2 env s0 PdOut_value paid_value opened_value"
  apply(unfold VC347_def inv2_def R2_def extraInv_def)
  by auto

theorem proof_2_348: "VC348 R2 env s0 PdOut_value paid_value opened_value"
  apply(unfold VC348_def inv2_def R2_def extraInv_def)
  by auto

theorem proof_2_362: "VC362 R2 env s0 PdOut_value paid_value opened_value"
  apply(unfold VC362_def inv2_def R2_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
   apply simp
  apply((rule allI)+)
  apply(rule impI)
  apply(simp split: if_splits)
  using substate_toEnvNum_id apply blast
  by auto

end