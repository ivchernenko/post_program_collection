theory Proofs_R2_1
  imports ExtraInv_R2_1 Requirements
begin

definition inv2_1 where "inv2_1 s \<equiv> extraInv s \<and> R2_1 s"

theorem "VC1 inv2_1 s0"
  apply(unfold VC1_def inv2_1_def R2_1_def P7_def)
  using extra1 VC1_def apply auto
  done

theorem "VC148 inv2_1 env s0 motion_value light_value"
  apply(unfold VC148_def inv2_1_def R2_1_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra148 VC148_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
    apply(auto simp add:  Pattern7_Def.einv2req)
  done

theorem "VC166 inv2_1 env s0 motion_value light_value"
  apply(unfold VC166_def inv2_1_def R2_1_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra166 VC166_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
    apply(auto simp add:  Pattern7_Def.einv2req)
  done

theorem "VC184 inv2_1 env s0 motion_value light_value"
  apply(unfold VC184_def inv2_1_def R2_1_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra184 VC184_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
    apply(auto simp add:  Pattern7_Def.einv2req)
  done

theorem "VC202 inv2_1 env s0 motion_value light_value"
  apply(unfold VC202_def inv2_1_def R2_1_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra202 VC202_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
    apply(auto simp add:  Pattern7_Def.einv2req)
  done

theorem "VC220 inv2_1 env s0 motion_value light_value"
  apply(unfold VC220_def inv2_1_def R2_1_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra220 VC220_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
    apply(auto simp add:  Pattern7_Def.einv2req)
  done

theorem "VC238 inv2_1 env s0 motion_value light_value"
  apply(unfold VC238_def inv2_1_def R2_1_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra238 VC238_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
    apply(auto simp add:  Pattern7_Def.einv2req)
  done

theorem "VC256 inv2_1 env s0 motion_value light_value"
  apply(unfold VC256_def inv2_1_def R2_1_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra256 VC256_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
    apply(auto simp add:  Pattern7_Def.einv2req)
  done

theorem "VC274 inv2_1 env s0 motion_value light_value"
  apply(unfold VC274_def inv2_1_def R2_1_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra274 VC274_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
    apply(auto simp add:  Pattern7_Def.einv2req)
  done

end