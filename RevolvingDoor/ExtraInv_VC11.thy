theory ExtraInv_VC11
  imports ExtraInv_new RequirementLemmas
begin

theorem extra_11: "VC11 extraInv env s0 user_value pressure_value"
  apply(unfold VC11_def)
  by simp

end


