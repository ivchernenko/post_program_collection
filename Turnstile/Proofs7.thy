theory Proofs7
  imports Requirements VCTheoryLemmas
begin

definition inv7 where "inv7 s \<equiv> R7 s \<and> extraInv s"

theorem proof_7_1: "VC1 inv7 s0"
  apply(unfold VC1_def inv7_def R7_def extraInv_def)
  by auto

theorem proof_7_347: "VC347 R7 env s0 PdOut_value paid_value opened_value"
  apply(unfold VC347_def inv7_def R7_def extraInv_def)
  by auto

theorem proof_7_348: "VC348 R7 env s0 PdOut_value paid_value opened_value"
  apply(unfold VC348_def inv7_def R7_def extraInv_def)
  by auto

theorem proof_7_349: "VC349 R7 env s0 PdOut_value paid_value opened_value"
  apply(unfold VC349_def inv7_def R7_def extraInv_def)
  by auto

theorem proof_7_350: "VC350 R7 env s0 PdOut_value paid_value opened_value"
  apply(unfold VC350_def inv7_def R7_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
   apply simp
  apply((rule allI)+)
  apply(rule impI)
  apply(simp split: if_splits)
  using substate_toEnvNum_id apply blast
  by auto

end