theory ExtraInv4_VC5
  imports ExtraInv4
begin

theorem "VC5 extraInv env s0 user_value pressure_value"
  apply(unfold VC5_def )
  by simp

end
