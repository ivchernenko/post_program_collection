theory ExtraInv_R2
  imports CommonExtraInv "../Patterns"
begin

definition extraInv where "extraInv s \<equiv> commonExtraInv s \<and>
(getPstate s Motion' = Motion'noMovement' \<longrightarrow>
P5_1inv s LIGHTING_TIME'TIMEOUT (LIGHTING_TIME'TIMEOUT - 1) (\<lambda> s1.  getVarBool s1 motion' = True \<and>  getVarBool s1 light' = LOW')
  (\<lambda> s3. P2all s3 (\<lambda> s2. getVarInt s2 timeOfDay' = NIGHT' \<or> getVarInt s3 timeOfDay' = NIGHT' \<or>
 getVarBool s3 dayLight' = True \<or> getVarBool s3 dimLight' = True))) \<and>
(getPstate s Motion' = Motion'movement' \<longrightarrow>
P5_1inv s LIGHTING_TIME'TIMEOUT (ltime s Motion' - 1) (\<lambda> s1.  getVarBool s1 motion' = True \<and>  getVarBool s1 light' = LOW')
  (\<lambda> s3. P2all s3 (\<lambda> s2. getVarInt s2 timeOfDay' = NIGHT' \<or> getVarInt s3 timeOfDay' = NIGHT' \<or>
 getVarBool s3 dayLight' = True \<or> getVarBool s3 dimLight' = True)))"

theorem extra1: "VC1 extraInv ss0"
  apply(unfold VC1_def extraInv_def commonExtraInv_def P5_1inv_rule)
  apply auto
  done

theorem extra146: "VC146 extraInv env s0 motion_value light_value"
  apply(unfold VC146_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei146 VC146_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule conjI)
  subgoal
    apply simp
    done
  subgoal
    apply(simp;((rule impI;simp)?);rule P5_1inv_rule[of s0])
        apply simp
    subgoal
      apply simp
      apply(rule P2all_rule[of s0])
       apply simp
      by simp
      apply simp
     apply simp
    by simp
  done

theorem extra164: "VC164 extraInv env s0 motion_value light_value"
  apply(unfold VC164_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei164 VC164_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule conjI)
  subgoal
    apply(simp;((rule impI;simp)?);rule P5_1inv_rule[of s0])
        apply simp
       apply simp
      apply simp
     apply simp
    by simp
  by simp

theorem extra82: "VC182 extraInv env s0 motion_value light_value"
  apply(unfold VC182_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei182 VC182_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  by simp

theorem extra200: "VC200 extraInv env s0 motion_value light_value"
  apply(unfold VC200_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei200 VC200_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule conjI)
   apply simp
  subgoal
    apply(simp;((rule impI;simp)?);rule P5_1inv_rule[of s0])
        apply simp
      apply simp
      apply(cases light_value)
        apply simp
    subgoal
      apply simp
      apply(rule P2all_rule[of s0])
       apply simp
      by simp
    subgoal
      apply simp
      apply(rule imp_rule)
        apply assumption
       apply(rule P2all_rule[of s0])
      apply simp
       apply assumption
      by simp
     apply simp
    by simp
  done

theorem extra218: "VC218 extraInv env s0 motion_value light_value"
  apply(unfold VC218_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei218 VC218_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule conjI)
   apply(simp;(rule impI; simp)?)
   apply(rule P5_1inv_rule[of s0])
       apply simp
      apply simp
     apply simp
    apply simp
   apply simp
  by simp

theorem extra236: "VC236 extraInv env s0 motion_value light_value"
  apply(unfold VC236_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei236 VC236_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule conjI)
   apply simp
  apply(simp;(rule impI; simp)?) 
  apply(rule P5_1inv_rule[of s0])
      apply simp
     apply simp
    apply simp
    apply(rule P2all_rule[of s0])
     apply simp
    apply simp
   apply simp
  by simp

theorem extra254: "VC254 extraInv env s0 motion_value light_value"
  apply(unfold VC254_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei254 VC254_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  by simp

theorem extra272: "VC272 extraInv env s0 motion_value light_value"
  apply(unfold VC272_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei272 VC272_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  by simp

end