theory Proofs_R14
  imports Requirements "../VCTheoryLemmas"
begin

theorem  "VC54 R14 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC54_def R14_def)
  by auto

theorem  "VC55 R14 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC55_def R14_def)
  by auto

end