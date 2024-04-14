theory Proof_R5_VC15
  imports  ExtraInv_new
begin

theorem proof_5_15: "VC15 inv5 env s0 user_value pressure_value"
  apply(unfold VC15_def inv5_def)
  apply(rule impI)
  apply simp
  apply(unfold extraInv_def)
  by (metis One_nat_def substate.simps(2) toEnvP.elims(2) zero_neq_numeral)

end


      

