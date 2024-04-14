theory ExtraInv_VC7
  imports ExtraInv_new RequirementLemmas
begin

theorem extra_7: "VC7 extraInv env s0 user_value pressure_value"
  apply(unfold VC7_def)
  by simp