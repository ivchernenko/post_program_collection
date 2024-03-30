theory ExtraInv_R3
  imports CommonExtraInv "../Patterns"
begin

definition extraInv where "extraInv s \<equiv> commonExtraInv s \<and>
(getPstate s  Lighting' = Lighting'morningLighting' \<longrightarrow>
P5_2inv s (MORNING_LIGHTING_TIME'TIMEOUT + 1) (ltime s Lighting' - 1) (\<lambda> s1 s2.  getVarInt s1 timeOfDay' = EARLY_MORNING' \<and> getVarInt s2 timeOfDay' = MORNING_LIGHTING')
(\<lambda> s3. getVarBool s3 dimLight' = TURNED_ON')) \<and>
(getPstate s  Lighting' \<noteq> Lighting'morningLighting' \<longrightarrow>
P5_2inv s (MORNING_LIGHTING_TIME'TIMEOUT + 1) MORNING_LIGHTING_TIME'TIMEOUT (\<lambda> s1 s2.  getVarInt s1 timeOfDay' = EARLY_MORNING' \<and> getVarInt s2 timeOfDay' = MORNING_LIGHTING')
(\<lambda> s3. getVarBool s3 dimLight' = TURNED_ON'))"

theorem extra1: "VC1 extraInv s0"
  apply(unfold VC1_def extraInv_def commonExtraInv_def P5_2inv_def always2_def constrained_always_def)
  apply auto
  done

theorem extra146: "VC146 extraInv env s0 motion_value light_value"
  apply(unfold VC146_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei146 VC146_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply simp
  done

theorem extra147: "VC147 extraInv env s0 motion_value light_value"
  apply(unfold VC147_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei147 VC147_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply simp
  done

theorem extra148: "VC148 extraInv env s0 motion_value light_value"
  apply(unfold VC148_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei148 VC148_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule conjI)
   apply(simp;(rule impI;simp)?)
   apply(rule P5_2_rule[of s0])
    apply auto
  done

theorem extra149: "VC149 extraInv env s0 motion_value light_value"
  apply(unfold VC149_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei149 VC149_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule conjI)
   apply(simp;(rule impI;simp)?)
  apply(simp;(rule impI;simp)?)
  apply(rule P5_2_rule[of s0])
   apply auto
  done

theorem extra150: "VC150 extraInv env s0 motion_value light_value"
  apply(unfold VC150_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei150 VC150_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply simp
  done

theorem extra151: "VC151 extraInv env s0 motion_value light_value"
  apply(unfold VC151_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei151 VC151_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply simp
  done

theorem extra152: "VC152 extraInv env s0 motion_value light_value"
  apply(unfold VC152_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei152 VC152_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule conjI)
   apply(simp;(rule impI;simp)?)
  apply(simp;(rule impI;simp)?)
  apply(rule P5_2_rule[of s0])
   apply auto
  done

theorem extra153: "VC153 extraInv env s0 motion_value light_value"
  apply(unfold VC153_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei153 VC153_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule conjI)
  apply(simp;(rule impI;simp)?)
   apply(rule P5_2_rule[of s0])
    apply auto
  done

theorem extra154: "VC154 extraInv env s0 motion_value light_value"
  apply(unfold VC154_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei154 VC154_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule conjI)
  apply simp
  apply(simp;(rule impI;simp)?)
  apply(rule P5_2_rule[of s0])
   apply auto
  done

theorem extra155: "VC155 extraInv env s0 motion_value light_value"
  apply(unfold VC155_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei155 VC155_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule conjI)
   apply(simp;(rule impI;simp)?)
  apply(simp;(rule impI;simp)?)
  apply(rule P5_2_rule[of s0])
   apply auto
  done

theorem extra156: "VC156 extraInv env s0 motion_value light_value"
  apply(unfold VC156_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei156 VC156_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply simp
  done

theorem extra157: "VC157 extraInv env s0 motion_value light_value"
  apply(unfold VC157_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei157 VC157_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply simp
  done

theorem extra158: "VC158 extraInv env s0 motion_value light_value"
  apply(unfold VC158_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei158 VC158_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule conjI)
   apply(simp;(rule impI;simp)?)
  apply(simp;(rule impI;simp)?)
  apply(rule P5_2_rule[of s0])
   apply auto
  done

end