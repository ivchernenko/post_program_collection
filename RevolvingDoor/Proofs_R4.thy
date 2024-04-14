theory Proofs_R4
  imports ExtraInv4
begin

definition inv4 where "inv4 s \<equiv> extraInv1 s \<and> R4_3 s"

theorem "VC1 inv4 s0"
  apply(unfold VC1_def inv4_def R4_3_def P9'_def P4'_def always2_def always_def constrained_until_def constrained_always_def)
  using extra1 VC1_def apply auto
  done

theorem "VC2 inv4 env s0 user_value pressure_value"
  apply(unfold VC2_def inv4_def R4_3_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra2 VC2_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv1_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P9'einv2req)
  done

theorem "VC3 inv4 env s0 user_value pressure_value"
  apply(unfold VC3_def inv4_def R4_3_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra3 VC3_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv1_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P9'einv2req)
  done

theorem "VC4 inv4 env s0 user_value pressure_value"
  apply(unfold VC4_def inv4_def R4_3_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra4 VC4_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv1_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P9'einv2req)
  done

theorem "VC5 inv4 env s0 user_value pressure_value"
  apply(unfold VC5_def inv4_def R4_3_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra5 VC5_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv1_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P9'einv2req)
  done

theorem "VC6 inv4 env s0 user_value pressure_value"
  apply(unfold VC6_def inv4_def R4_3_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra6 VC6_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv1_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P9'einv2req)
  done

theorem "VC7 inv4 env s0 user_value pressure_value"
  apply(unfold VC7_def inv4_def R4_3_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra7 VC7_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv1_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P9'einv2req)
  done

theorem "VC8 inv4 env s0 user_value pressure_value"
  apply(unfold VC8_def inv4_def R4_3_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra8 VC8_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv1_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P9'einv2req)
  done

theorem "VC9 inv4 env s0 user_value pressure_value"
  apply(unfold VC9_def inv4_def R4_3_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra9 VC9_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv1_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P9'einv2req)
  done

theorem "VC10 inv4 env s0 user_value pressure_value"
  apply(unfold VC10_def inv4_def R4_3_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra10 VC10_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv1_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P9'einv2req)
  done

theorem "VC11 inv4 env s0 user_value pressure_value"
  apply(unfold VC11_def inv4_def R4_3_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra11 VC11_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv1_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P9'einv2req)
  done

theorem "VC12 inv4 env s0 user_value pressure_value"
  apply(unfold VC12_def inv4_def R4_3_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra12 VC12_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv1_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P9'einv2req)
  done

theorem "VC13 inv4 env s0 user_value pressure_value"
  apply(unfold VC13_def inv4_def R4_3_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra13 VC13_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv1_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P9'einv2req)
  done

theorem "VC14 inv4 env s0 user_value pressure_value"
  apply(unfold VC14_def inv4_def R4_3_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra14 VC14_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv1_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P9'einv2req)
  done

theorem "VC15 inv4 env s0 user_value pressure_value"
  apply(unfold VC15_def inv4_def R4_3_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra15 VC15_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv1_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P9'einv2req)
  done

theorem "VC16 inv4 env s0 user_value pressure_value"
  apply(unfold VC16_def inv4_def R4_3_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra16 VC16_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv1_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P9'einv2req)
  done

end
