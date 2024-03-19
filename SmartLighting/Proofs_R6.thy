theory Proofs_R6
  imports CommonExtraInv Requirements
begin

definition inv6 where "inv6 s \<equiv> R6 s \<and> commonExtraInv s"

theorem "VC1 inv6 s0"
  apply(unfold VC1_def inv6_def R6_def)
  using cei1 VC1_def apply auto
  done

theorem "VC146 inv6 env s0 motion_value light_value"
  apply(unfold VC146_def inv6_def R6_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    by auto
  using cei146 VC146_def by auto

theorem "VC147 inv6 env s0 motion_value light_value"
  apply(unfold VC147_def inv6_def R6_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    by auto
  using cei147 VC147_def by auto

theorem "VC148 inv6 env s0 motion_value light_value"
  apply(unfold VC148_def inv6_def R6_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    by auto
  using cei148 VC148_def by auto

theorem "VC149 inv6 env s0 motion_value light_value"
  apply(unfold VC149_def inv6_def R6_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    by auto
  using cei149 VC149_def by auto

theorem "VC150 inv6 env s0 motion_value light_value"
  apply(unfold VC150_def inv6_def R6_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    by auto
  using cei150 VC150_def by auto

theorem "VC151 inv6 env s0 motion_value light_value"
  apply(unfold VC151_def inv6_def R6_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    by auto
  using cei151 VC151_def by auto

theorem "VC152 inv6 env s0 motion_value light_value"
  apply(unfold VC152_def inv6_def R6_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    by auto
  using cei152 VC152_def by auto

theorem "VC153 inv6 env s0 motion_value light_value"
  apply(unfold VC153_def inv6_def R6_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    by auto
  using cei153 VC153_def by auto

theorem "VC154 inv6 env s0 motion_value light_value"
  apply(unfold VC154_def inv6_def R6_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    by auto
  using cei154 VC154_def by auto

theorem "VC155 inv6 env s0 motion_value light_value"
  apply(unfold VC155_def inv6_def R6_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    by auto
  using cei155 VC155_def by auto

theorem "VC156 inv6 env s0 motion_value light_value"
  apply(unfold VC156_def inv6_def R6_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    by auto
  using cei156 VC156_def by auto

theorem "VC157 inv6 env s0 motion_value light_value"
  apply(unfold VC157_def inv6_def R6_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    by auto
  using cei157 VC157_def by auto

theorem "VC158 inv6 env s0 motion_value light_value"
  apply(unfold VC158_def inv6_def R6_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    by auto
  using cei158 VC158_def by auto

theorem "VC159 inv6 env s0 motion_value light_value"
  apply(unfold VC159_def inv6_def R6_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    by auto
  using cei159 VC159_def by auto

theorem "VC160 inv6 env s0 motion_value light_value"
  apply(unfold VC160_def inv6_def R6_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    by auto
  using cei160 VC160_def by auto

theorem "VC161 inv6 env s0 motion_value light_value"
  apply(unfold VC161_def inv6_def R6_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    by auto
  using cei161 VC161_def by auto

theorem "VC162 inv6 env s0 motion_value light_value"
  apply(unfold VC162_def inv6_def R6_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    by auto
  using cei162 VC162_def by auto

theorem "VC163 inv6 env s0 motion_value light_value"
  apply(unfold VC163_def inv6_def R6_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    by auto
  using cei163 VC163_def by auto

theorem "VC166 inv6 env s0 motion_value light_value"
  apply(unfold VC166_def inv6_def R6_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    by auto
  using cei166 VC166_def by auto

theorem "VC184 inv6 env s0 motion_value light_value"
  apply(unfold VC184_def inv6_def R6_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    by auto
  using cei184 VC184_def by auto

theorem "VC202 inv6 env s0 motion_value light_value"
  apply(unfold VC202_def inv6_def R6_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    by auto
  using cei202 VC202_def by auto

theorem "VC220 inv6 env s0 motion_value light_value"
  apply(unfold VC220_def inv6_def R6_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    by auto
  using cei220 VC220_def by auto

theorem "VC238 inv6 env s0 motion_value light_value"
  apply(unfold VC238_def inv6_def R6_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    by auto
  using cei238 VC238_def by auto

theorem "VC256 inv6 env s0 motion_value light_value"
  apply(unfold VC256_def inv6_def R6_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    by auto
  using cei256 VC256_def by auto

theorem "VC274 inv6 env s0 motion_value light_value"
  apply(unfold VC274_def inv6_def R6_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    by auto
  using cei274 VC274_def by auto

end