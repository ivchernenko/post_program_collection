theory Proof_R2_VC22
  imports ExtraInv "../VCTheoryLemmas"
begin

theorem "VC22 R2 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC22_def  R2_def)
  by auto

theorem "VC23 R2 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC23_def  R2_def)
  by auto

end