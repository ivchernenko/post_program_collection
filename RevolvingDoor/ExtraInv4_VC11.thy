theory ExtraInv4_VC11
  imports ExtraInv4
begin

theorem "VC11 extraInv env s0 user_value pressure_value"
  apply(unfold VC11_def)
  by simp

end