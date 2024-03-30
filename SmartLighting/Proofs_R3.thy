theory Proofs_R3
imports ExtraInv_R3 Requirements
begin

definition inv3 where "inv3 s \<equiv> extraInv s \<and> R3 s"

theorem "VC1 inv3 s0"
  apply(unfold VC1_def inv3_def R3_def P5_2_def always2_def constrained_always_def)
  using extra1 VC1_def apply auto
  done

theorem "VC148 inv3 env s0 motion_value light_value"
  apply(unfold VC148_def inv3_def R3_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra148 VC148_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P5_2_einv2req)
  done

theorem "VC149 inv3 env s0 motion_value light_value"
  apply(unfold VC149_def inv3_def R3_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra149 VC149_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P5_2_einv2req)
  done

theorem "VC150 inv3 env s0 motion_value light_value"
  apply(unfold VC150_def inv3_def R3_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra150 VC150_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P5_2_einv2req)
  done

theorem "VC151 inv3 env s0 motion_value light_value"
  apply(unfold VC151_def inv3_def R3_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra151 VC151_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P5_2_einv2req)
  done

theorem "VC152 inv3 env s0 motion_value light_value"
  apply(unfold VC152_def inv3_def R3_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra152 VC152_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P5_2_einv2req)
  done

theorem "VC153 inv3 env s0 motion_value light_value"
  apply(unfold VC153_def inv3_def R3_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra153 VC153_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P5_2_einv2req)
  done

theorem "VC154 inv3 env s0 motion_value light_value"
  apply(unfold VC154_def inv3_def R3_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra154 VC154_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P5_2_einv2req)
  done

theorem "VC155 inv3 env s0 motion_value light_value"
  apply(unfold VC155_def inv3_def R3_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra155 VC155_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P5_2_einv2req)
  done

theorem "VC156 inv3 env s0 motion_value light_value"
  apply(unfold VC156_def inv3_def R3_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra156 VC156_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P5_2_einv2req)
  done

theorem "VC157 inv3 env s0 motion_value light_value"
  apply(unfold VC157_def inv3_def R3_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra157 VC157_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P5_2_einv2req)
  done

end