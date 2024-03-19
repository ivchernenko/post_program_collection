theory CommonExtraInv
  imports SmartLighting "../VCTheoryLemmas"
begin

definition commonExtraInv where "commonExtraInv s== toEnvP s \<and>
(getPstate s Motion' = Motion'noMovement' \<longrightarrow> getVarBool s turnedOn' = False) \<and>
(getPstate s Motion' = Motion'movement' \<longrightarrow> getVarBool s turnedOn' = True) \<and>
(getPstate s Motion' = STOP \<longrightarrow> getVarBool s turnedOn' = False) \<and>
(getPstate s Motion' = Motion'movement' \<longrightarrow> ltime s Motion' \<le> LIGHTING_TIME'TIMEOUT) \<and>
getPstate s Motion' \<in> {Motion'noMovement', Motion'movement', STOP} \<and>
(getPstate s Lighting' = Lighting'night' \<longrightarrow> getVarBool s dayLight' = False \<and> getVarBool s dimLight' = False \<and> getVarInt s timeOfDay' = NIGHT') \<and>
(getPstate s Lighting' = Lighting'night' \<longrightarrow> getPstate s Motion' = STOP) \<and>
(getPstate s Lighting' \<notin> {Lighting'night', STOP} \<longrightarrow> getPstate s Motion' \<noteq> STOP) \<and>
(getPstate s Lighting' = Lighting'earlyMorning' \<longrightarrow> getVarBool s dayLight' = False \<and> getVarInt s timeOfDay' = EARLY_MORNING') \<and>
(getPstate s Lighting' = Lighting'morningLighting' \<longrightarrow> getVarBool s dimLight' = True \<and> getVarBool s dayLight' = False \<and> getVarInt s timeOfDay' = MORNING_LIGHTING') \<and>
(getPstate s Lighting' = Lighting'morningOrDay' \<longrightarrow> getVarInt s timeOfDay' = DAY') \<and>
(getPstate s Lighting' = Lighting'evening' \<longrightarrow> getVarInt s timeOfDay' = EVENING') \<and>
(getPstate s Lighting' = Lighting'morningLighting' \<longrightarrow> ltime s Lighting' \<le> MORNING_LIGHTING_TIME'TIMEOUT) \<and>
(getPstate s Lighting' \<in> {Lighting'night', Lighting'earlyMorning', Lighting'morningLighting', Lighting'morningOrDay', Lighting'evening', STOP}) \<and>
(getPstate s Init' = Init'init' \<longrightarrow> getPstate s Motion' = STOP \<and> getPstate s Lighting' = STOP) \<and>
(getPstate s Init' = STOP \<longrightarrow>  getPstate s Lighting' \<noteq> STOP)"

theorem cei1: "VC1 commonExtraInv s0"
  apply(unfold VC1_def commonExtraInv_def)
  by simp

theorem cei146: "VC146 commonExtraInv env s0 motion_value light_value"
  apply(unfold VC146_def commonExtraInv_def)
  by simp

theorem cei147: "VC147 commonExtraInv env s0 motion_value light_value"
  apply(unfold VC147_def commonExtraInv_def)
  by simp

theorem cei148: "VC148 commonExtraInv env s0 motion_value light_value"
  apply(unfold VC148_def commonExtraInv_def)
  by simp

theorem cei149: "VC149 commonExtraInv env s0 motion_value light_value"
  apply(unfold VC149_def commonExtraInv_def)
  by simp

theorem cei150: "VC150 commonExtraInv env s0 motion_value light_value"
  apply(unfold VC150_def commonExtraInv_def)
  by simp

theorem cei151: "VC151 commonExtraInv env s0 motion_value light_value"
  apply(unfold VC151_def commonExtraInv_def)
  by simp

theorem cei152: "VC152 commonExtraInv env s0 motion_value light_value"
  apply(unfold VC152_def commonExtraInv_def)
  by simp

theorem cei153: "VC153 commonExtraInv env s0 motion_value light_value"
  apply(unfold VC153_def commonExtraInv_def)
  by simp

theorem cei154: "VC154 commonExtraInv env s0 motion_value light_value"
  apply(unfold VC154_def commonExtraInv_def)
  by simp

theorem cei155: "VC155 commonExtraInv env s0 motion_value light_value"
  apply(unfold VC155_def commonExtraInv_def)
  by simp

theorem cei156: "VC156 commonExtraInv env s0 motion_value light_value"
  apply(unfold VC156_def commonExtraInv_def)
  by simp

theorem cei157: "VC157 commonExtraInv env s0 motion_value light_value"
  apply(unfold VC157_def commonExtraInv_def)
  by simp

theorem cei158: "VC158 commonExtraInv env s0 motion_value light_value"
  apply(unfold VC158_def commonExtraInv_def)
  by simp

theorem cei159: "VC159 commonExtraInv env s0 motion_value light_value"
  apply(unfold VC159_def commonExtraInv_def)
  by simp

theorem cei160: "VC160 commonExtraInv env s0 motion_value light_value"
  apply(unfold VC160_def commonExtraInv_def)
  by simp

theorem cei161: "VC161 commonExtraInv env s0 motion_value light_value"
  apply(unfold VC161_def commonExtraInv_def)
  by simp

theorem cei162: "VC162 commonExtraInv env s0 motion_value light_value"
  apply(unfold VC162_def commonExtraInv_def)
  by auto

theorem cei163: "VC163 commonExtraInv env s0 motion_value light_value"
  apply(unfold VC163_def commonExtraInv_def)
  by force

theorem cei164: "VC164 commonExtraInv env s0 motion_value light_value"
  apply(unfold VC164_def commonExtraInv_def)
  by force

theorem cei182: "VC182 commonExtraInv env s0 motion_value light_value"
  apply(unfold VC182_def commonExtraInv_def)
  by force

theorem cei200: "VC200 commonExtraInv env s0 motion_value light_value"
  apply(unfold VC200_def commonExtraInv_def)
  by force

theorem cei218: "VC218 commonExtraInv env s0 motion_value light_value"
  apply(unfold VC218_def commonExtraInv_def)
  by force

theorem cei236: "VC236 commonExtraInv env s0 motion_value light_value"
  apply(unfold VC236_def commonExtraInv_def)
  by force

theorem cei254: "VC254 commonExtraInv env s0 motion_value light_value"
  apply(unfold VC254_def commonExtraInv_def)
  by force

theorem cei272: "VC272 commonExtraInv env s0 motion_value light_value"
  apply(unfold VC272_def commonExtraInv_def)
  by force

theorem cei166: "VC166 commonExtraInv env s0 motion_value light_value"
  apply(unfold VC166_def commonExtraInv_def)
  by force

theorem cei184: "VC184 commonExtraInv env s0 motion_value light_value"
  apply(unfold VC184_def commonExtraInv_def)
  by force

theorem cei202: "VC202 commonExtraInv env s0 motion_value light_value"
  apply(unfold VC202_def commonExtraInv_def)
  by force

theorem cei220: "VC220 commonExtraInv env s0 motion_value light_value"
  apply(unfold VC220_def commonExtraInv_def)
  by force

theorem cei238: "VC238 commonExtraInv env s0 motion_value light_value"
  apply(unfold VC238_def commonExtraInv_def)
  by force

theorem cei256: "VC256 commonExtraInv env s0 motion_value light_value"
  apply(unfold VC256_def commonExtraInv_def)
  by force

theorem cei274: "VC274 commonExtraInv env s0 motion_value light_value"
  apply(unfold VC274_def commonExtraInv_def)
  by force

end