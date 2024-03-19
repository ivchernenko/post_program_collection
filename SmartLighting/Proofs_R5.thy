theory Proofs_R5
  imports CommonExtraInv Requirements
begin

definition inv5 where "inv5 s \<equiv> R5 s \<and> commonExtraInv s"

theorem "VC1 inv5 s0"
  apply(unfold VC1_def inv5_def R5_def)
  using cei1 VC1_def apply auto
  done

theorem "VC146 inv5 env s0 motion_value light_value"
  apply(unfold VC146_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    using substate_toEnvNum_id[of _ s0] by force
  using cei146 VC146_def by auto

theorem "VC147 inv5 env s0 motion_value light_value"
  apply(unfold VC147_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    using substate_toEnvNum_id[of _ s0] by force
  using cei147 VC147_def by auto

theorem "VC148 inv5 env s0 motion_value light_value"
  apply(unfold VC148_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    using substate_toEnvNum_id[of _ s0] by force
  using cei148 VC148_def by auto

theorem "VC149 inv5 env s0 motion_value light_value"
  apply(unfold VC149_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    using substate_toEnvNum_id[of _ s0] by force
  using cei149 VC149_def by auto

theorem "VC150 inv5 env s0 motion_value light_value"
  apply(unfold VC150_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    using substate_toEnvNum_id[of _ s0] by force
  using cei150 VC150_def by auto

theorem "VC151 inv5 env s0 motion_value light_value"
  apply(unfold VC151_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    using substate_toEnvNum_id[of _ s0] by force
  using cei151 VC151_def by auto

theorem "VC152 inv5 env s0 motion_value light_value"
  apply(unfold VC152_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    using substate_toEnvNum_id[of _ s0] by force
  using cei152 VC152_def by auto

theorem "VC153 inv5 env s0 motion_value light_value"
  apply(unfold VC153_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    using substate_toEnvNum_id[of _ s0] by force
  using cei153 VC153_def by auto

theorem "VC154 inv5 env s0 motion_value light_value"
  apply(unfold VC154_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    using substate_toEnvNum_id[of _ s0] by force
  using cei154 VC154_def by auto

theorem "VC155 inv5 env s0 motion_value light_value"
  apply(unfold VC155_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    using substate_toEnvNum_id[of _ s0] by force
  using cei155 VC155_def by auto

theorem "VC156 inv5 env s0 motion_value light_value"
  apply(unfold VC156_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    using substate_toEnvNum_id[of _ s0] by force
  using cei156 VC156_def by auto

theorem "VC157 inv5 env s0 motion_value light_value"
  apply(unfold VC157_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    using substate_toEnvNum_id[of _ s0] by force
  using cei157 VC157_def by auto

theorem "VC158 inv5 env s0 motion_value light_value"
  apply(unfold VC158_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    using substate_toEnvNum_id[of _ s0] by force
  using cei158 VC158_def by auto

theorem "VC159 inv5 env s0 motion_value light_value"
  apply(unfold VC159_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    using substate_toEnvNum_id[of _ s0] by force
  using cei159 VC159_def by auto

theorem "VC160 inv5 env s0 motion_value light_value"
  apply(unfold VC160_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    using substate_toEnvNum_id[of _ s0] by force
  using cei160 VC160_def by auto

theorem "VC161 inv5 env s0 motion_value light_value"
  apply(unfold VC161_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    using substate_toEnvNum_id[of _ s0] by force
  using cei161 VC161_def by auto

theorem "VC162 inv5 env s0 motion_value light_value"
  apply(unfold VC162_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    using substate_toEnvNum_id[of _ s0] by force
  using cei162 VC162_def by auto

theorem "VC163 inv5 env s0 motion_value light_value"
  apply(unfold VC163_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    using substate_toEnvNum_id[of _ s0] by force
  using cei163 VC163_def by auto

theorem "VC166 inv5 env s0 motion_value light_value"
  apply(unfold VC166_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    using substate_toEnvNum_id[of _ s0] by force
  using cei166 VC166_def by auto

theorem "VC184 inv5 env s0 motion_value light_value"
  apply(unfold VC184_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    using substate_toEnvNum_id[of _ s0] by force
  using cei184 VC184_def by auto

theorem "VC202 inv5 env s0 motion_value light_value"
  apply(unfold VC202_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    using substate_toEnvNum_id[of _ s0] by force
  using cei202 VC202_def by auto

theorem "VC220 inv5 env s0 motion_value light_value"
  apply(unfold VC220_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    using substate_toEnvNum_id[of _ s0] by force
  using cei220 VC220_def by auto

theorem "VC238 inv5 env s0 motion_value light_value"
  apply(unfold VC238_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    using substate_toEnvNum_id[of _ s0] by force
  using cei238 VC238_def by auto

theorem "VC256 inv5 env s0 motion_value light_value"
  apply(unfold VC256_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    using substate_toEnvNum_id[of _ s0] by force
  using cei256 VC256_def by auto

theorem "VC274 inv5 env s0 motion_value light_value"
  apply(unfold VC274_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    using substate_toEnvNum_id[of _ s0] by force
  using cei274 VC274_def by auto

end