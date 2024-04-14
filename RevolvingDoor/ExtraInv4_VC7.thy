theory ExtraInv4_VC7
  imports ExtraInv4
begin

theorem "VC7 extraInv env s0 user_value pressure_value"
  apply(unfold VC7_def)
  by simp

end