theory ExtraInv_R8
  imports CommonExtraInv "../Patterns"
begin

definition extraInv where "extraInv s \<equiv>commonExtraInv s \<and>
(getPstate s Motion' = Motion'movement' \<longrightarrow>
P1inv s (LIGHTING_TIME'TIMEOUT - 1) (ltime s Motion' - 1) (\<lambda> s2. P2ex s2 (\<lambda> s1. getVarBool s1 motion' = True \<and> getVarBool s2 motion' = False))
 (\<lambda> s3. getVarBool s3 dayLight' = False \<and> getVarBool s3 dimLight'= False \<or> getVarBool s3 motion' = True \<or>
 P2ex s3 (\<lambda> s2'.  getVarInt s2' timeOfDay' = MORNING_LIGHTING' \<or> getVarInt s3 timeOfDay' = MORNING_LIGHTING'))
(\<lambda> s2. (getVarBool s2 dayLight' = True \<or> getVarBool s2 dimLight' = True) \<and> getVarBool s2 motion' = False \<and>
 P2all s2 (\<lambda> s1'. getVarInt s1' timeOfDay' \<noteq> MORNING_LIGHTING' \<and>getVarInt s2 timeOfDay' \<noteq> MORNING_LIGHTING'))) \<and>
(getPstate s Motion' \<noteq> Motion'movement' \<longrightarrow>
P1inv s (LIGHTING_TIME'TIMEOUT - 1) 0 (\<lambda> s2. P2ex s2 (\<lambda> s1. getVarBool s1 motion' = True \<and> getVarBool s2 motion' = False))
 (\<lambda> s3. getVarBool s3 dayLight' = False \<and> getVarBool s3 dimLight'= False \<or> getVarBool s3 motion' = True \<or>
 P2ex s3 (\<lambda> s2'.  getVarInt s2' timeOfDay' = MORNING_LIGHTING' \<or> getVarInt s3 timeOfDay' = MORNING_LIGHTING'))
(\<lambda> s2. (getVarBool s2 dayLight' = True \<or> getVarBool s2 dimLight' = True) \<and> getVarBool s2 motion' = False \<and>
 P2all s2 (\<lambda> s1'. getVarInt s1' timeOfDay' \<noteq> MORNING_LIGHTING' \<and>getVarInt s2 timeOfDay' \<noteq> MORNING_LIGHTING')))"

theorem extra1: "VC1 extraInv s0"
  apply(unfold VC1_def extraInv_def commonExtraInv_def P1inv_def P2ex_def P2all_def)
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
   apply(rule P1inv_rule[of s0])
      apply simp
     apply simp
    apply simp
   apply simp
  apply simp
  done
      

theorem extra164: "VC164 extraInv env s0 motion_value light_value"
  apply(unfold VC164_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei164 VC164_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply simp
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
   apply(rule P1inv_rule[of s0])
      apply simp
     apply simp
    apply auto[1]
   apply auto[1]
  apply auto[1]
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
   apply(rule P1inv_rule[of s0])
      apply auto[1]
     apply auto[1]
     apply(rule P2ex_rule[of s0])
      apply auto[1]
     apply auto[1]
    apply auto[1]
    apply(rule P2ex_rule[of s0])
     apply auto[1]
    apply auto[1]
   apply auto[1]
  apply auto[1]
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