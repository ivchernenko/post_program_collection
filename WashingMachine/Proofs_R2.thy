theory Proofs_R2
  imports ExtraInv
begin

theorem "VC30 R2 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC30_def R2_def)
  by auto

theorem "VC40 R2 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC40_def R2_def)
  by auto

end