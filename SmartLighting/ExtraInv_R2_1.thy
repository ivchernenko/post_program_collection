theory ExtraInv_R2_1
  imports CommonExtraInv Requirements
begin

definition extraInv where "extraInv s \<equiv> commonExtraInv s \<and>
(getPstate s Motion' = Motion'movement' \<longrightarrow>
P7inv s LIGHTING_TIME'TIMEOUT (ltime s Motion' - 1) (\<lambda> s1 s2. getVarInt s1 timeOfDay' \<noteq> NIGHT' \<and> getVarInt s2 timeOfDay' \<noteq> NIGHT' \<and> getVarBool s2 motion' \<and> getVarBool s2 light' = LOW')
(\<lambda> s4. getVarInt s4 timeOfDay' = NIGHT') (\<lambda> s3. getVarBool s3 dayLight' = TURNED_ON' \<or> getVarBool s3 dimLight' = TURNED_ON')) \<and>
(getPstate s Motion' \<noteq> Motion'movement' \<longrightarrow>
P7inv s LIGHTING_TIME'TIMEOUT (LIGHTING_TIME'TIMEOUT - 1) (\<lambda> s1 s2. getVarInt s1 timeOfDay' \<noteq> NIGHT' \<and> getVarInt s2 timeOfDay' \<noteq> NIGHT' \<and> getVarBool s2 motion' \<and> getVarBool s2 light' = LOW')
(\<lambda> s4. getVarInt s4 timeOfDay' = NIGHT') (\<lambda> s3. getVarBool s3 dayLight' = TURNED_ON' \<or> getVarBool s3 dimLight' = TURNED_ON'))"

theorem extra1: "VC1 extraInv s0"
  apply(unfold VC1_def extraInv_def commonExtraInv_def P7inv_def)
  apply auto
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
   apply(rule P7inv_rule[of s0])
       apply auto
  done

theorem extra166: "VC166 extraInv env s0 motion_value light_value"
  apply(unfold VC166_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei166 VC166_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply simp
  done

theorem extra184: "VC184 extraInv env s0 motion_value light_value"
  apply(unfold VC184_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei184 VC184_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply simp
  done

theorem extra202: "VC202 extraInv env s0 motion_value light_value"
  apply(unfold VC202_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei202 VC202_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule conjI)
   apply(simp;(rule impI;simp)?)
   apply(rule P7inv_rule[of s0])
       apply auto
  done

theorem extra220: "VC220 extraInv env s0 motion_value light_value"
  apply(unfold VC220_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei220 VC220_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply simp
  done

theorem extra238: "VC238 extraInv env s0 motion_value light_value"
  apply(unfold VC238_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei238 VC238_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule conjI)
   apply(simp;(rule impI;simp)?)
   apply(rule P7inv_rule[of s0])
       apply auto
  done

theorem extra256: "VC256 extraInv env s0 motion_value light_value"
  apply(unfold VC256_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei256 VC256_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply simp
  done

theorem extra274: "VC274 extraInv env s0 motion_value light_value"
  apply(unfold VC274_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei274 VC274_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply simp
  done

end