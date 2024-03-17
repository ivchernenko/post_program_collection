theory Proofs_R1
  imports CommonExtraInv Requirements
begin

definition inv1 where "inv1 s \<equiv> R1 s \<and> commonExtraInv s"

theorem "VC1 inv1  s0"
  apply(unfold VC1_def inv1_def R1_def commonExtraInv_def)
  by auto

theorem "VC146 inv1 env s0 motion_value light_value"
  apply(unfold VC146_def inv1_def R1_def)
  apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)+
   apply auto[1]
  using cei146 VC146_def by auto

theorem "VC147 inv1 env s0 motion_value light_value"
  apply(unfold VC147_def inv1_def R1_def)
  apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)+
   apply auto[1]
  using cei147 VC147_def by auto

theorem "VC148 inv1 env s0 motion_value light_value"
  apply(unfold VC148_def inv1_def R1_def)
  apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)+
   apply auto[1]
  using cei148 VC148_def by auto

theorem "VC149 inv1 env s0 motion_value light_value"
  apply(unfold VC149_def inv1_def R1_def)
  apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)+
   apply auto[1]
  using cei149 VC149_def by auto

theorem "VC150 inv1 env s0 motion_value light_value"
  apply(unfold VC150_def inv1_def R1_def)
  apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)+
   apply auto[1]
  using cei150 VC150_def by auto

theorem "VC151 inv1 env s0 motion_value light_value"
  apply(unfold VC151_def inv1_def R1_def)
  apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)+
   apply auto[1]
  using cei151 VC151_def by auto

theorem "VC152 inv1 env s0 motion_value light_value"
  apply(unfold VC152_def inv1_def R1_def)
  apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)+
   apply auto[1]
  using cei152 VC152_def by auto

theorem "VC153 inv1 env s0 motion_value light_value"
  apply(unfold VC153_def inv1_def R1_def)
  apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)+
   apply auto[1]
  using cei153 VC153_def by auto

theorem "VC154 inv1 env s0 motion_value light_value"
  apply(unfold VC154_def inv1_def R1_def)
  apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)+
   apply auto[1]
  using cei154 VC154_def by auto

theorem "VC155 inv1 env s0 motion_value light_value"
  apply(unfold VC155_def inv1_def R1_def)
  apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)+
   apply auto[1]
  using cei155 VC155_def by auto

theorem "VC156 inv1 env s0 motion_value light_value"
  apply(unfold VC156_def inv1_def R1_def)
  apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)+
   apply auto[1]
  using cei156 VC156_def by auto

theorem "VC157 inv1 env s0 motion_value light_value"
  apply(unfold VC157_def inv1_def R1_def)
  apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)+
   apply auto[1]
  using cei157 VC157_def by auto

theorem "VC158 inv1 env s0 motion_value light_value"
  apply(unfold VC158_def inv1_def R1_def)
  apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)+
   apply auto[1]
  using cei158 VC158_def by auto

theorem "VC159 inv1 env s0 motion_value light_value"
  apply(unfold VC159_def inv1_def R1_def)
  apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)+
   apply auto[1]
  using cei159 VC159_def by auto

theorem "VC160 inv1 env s0 motion_value light_value"
  apply(unfold VC160_def inv1_def R1_def)
  apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)+
   apply auto[1]
  using cei160 VC160_def by auto

theorem "VC161 inv1 env s0 motion_value light_value"
  apply(unfold VC161_def inv1_def R1_def)
  apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)+
   apply auto[1]
  using cei161 VC161_def by auto

theorem "VC162 inv1 env s0 motion_value light_value"
  apply(unfold VC162_def inv1_def R1_def)
  apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)+
   apply auto[1]
  using cei162 VC162_def by auto

theorem "VC163 inv1 env s0 motion_value light_value"
  apply(unfold VC163_def inv1_def R1_def)
  apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)+
   apply auto[1]
  using cei163 VC163_def by auto

theorem "VC164 inv1 env s0 motion_value light_value"
  apply(unfold VC164_def inv1_def R1_def)
  apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)+
   apply auto[1]
  using cei164 VC164_def by auto

theorem "VC182 inv1 env s0 motion_value light_value"
  apply(unfold VC182_def inv1_def R1_def)
  apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)+
   apply auto[1]
  using cei182 VC182_def by auto

theorem "VC200 inv1 env s0 motion_value light_value"
  apply(unfold VC200_def inv1_def R1_def)
  apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)+
   apply auto[1]
  using cei200 VC200_def by auto

theorem "VC218 inv1 env s0 motion_value light_value"
  apply(unfold VC218_def inv1_def R1_def)
  apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)+
   apply auto[1]
  using cei218 VC218_def by auto

theorem "VC236 inv1 env s0 motion_value light_value"
  apply(unfold VC236_def inv1_def R1_def)
  apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)+
   apply auto[1]
  using cei236 VC236_def by auto

theorem "VC254 inv1 env s0 motion_value light_value"
  apply(unfold VC254_def inv1_def R1_def)
  apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)+
   apply auto[1]
  using cei254 VC254_def by auto

theorem "VC272 inv1 env s0 motion_value light_value"
  apply(unfold VC272_def inv1_def R1_def)
  apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)+
   apply auto[1]
  using cei272 VC272_def by auto

end
