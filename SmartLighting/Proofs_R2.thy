theory Proofs_R2
  imports ExtraInv_R2 Requirements
begin

definition inv2 where "inv2 s \<equiv> extraInv s \<and> R2 s"

theorem "VC1 inv2 s0"
  apply(unfold VC1_def inv2_def R2_def P5_1_def P2all_def)
  using extra1 VC1_def apply auto
  done

theorem "VC146 inv2 env s0 motion_value light_value"
  apply(unfold VC146_def inv2_def R2_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra146 VC146_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  Pattern5_Def.P5_1_einv2req)
  done

theorem "VC164 inv2 env s0 motion_value light_value"
  apply(unfold VC164_def inv2_def R2_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra164 VC164_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  Pattern5_Def.P5_1_einv2req)
  done

theorem "VC182 inv2 env s0 motion_value light_value"
  apply(unfold VC182_def inv2_def R2_def)
  apply(rule impI)
  apply(rule context_conjI)
  using  VC182_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  Pattern5_Def.P5_1_einv2req)
  done

theorem "VC200 inv2 env s0 motion_value light_value"
  apply(unfold VC200_def inv2_def R2_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra200 VC200_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  Pattern5_Def.P5_1_einv2req)
  done

theorem "VC218 inv2 env s0 motion_value light_value"
  apply(unfold VC218_def inv2_def R2_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra218 VC218_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  Pattern5_Def.P5_1_einv2req)
  done

theorem "VC236 inv2 env s0 motion_value light_value"
  apply(unfold VC236_def inv2_def R2_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra236 VC236_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  Pattern5_Def.P5_1_einv2req)
  done

theorem "VC254 inv2 env s0 motion_value light_value"
  apply(unfold VC254_def inv2_def R2_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra254 VC254_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  Pattern5_Def.P5_1_einv2req)
  done

theorem "VC272 inv2 env s0 motion_value light_value"
  apply(unfold VC272_def inv2_def R2_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra272 VC272_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  Pattern5_Def.P5_1_einv2req)
  done

end
