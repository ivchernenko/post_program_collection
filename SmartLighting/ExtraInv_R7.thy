theory ExtraInv_R7
  imports CommonExtraInv "../Patterns"
begin

definition extraInv where "extraInv s \<equiv> commonExtraInv s \<and>
(getPstate s Motion' = Motion'movement' \<longrightarrow> 
always s (\<lambda> s1. getVarBool s1 motion' = False \<longrightarrow> constrained_until_inv s1 s (LIGHTING_TIME'TIMEOUT + MORNING_LIGHTING_TIME'TIMEOUT) (ltime s Motion' - 1)
(\<lambda> s2. (getVarBool s2 dayLight' = True \<or> getVarBool s2 dimLight' = True) \<and> getVarBool s2 motion' = False)
 (\<lambda> s3. getVarBool s3 dayLight' = False \<and> getVarBool s3 dimLight'= False \<or> getVarBool s3 motion' = True))) \<and>
(getPstate s Motion' \<noteq>  Motion'movement' \<and> getPstate s Lighting' = Lighting'morningLighting' \<longrightarrow> 
always s (\<lambda> s1. getVarBool s1 motion' = False \<longrightarrow> constrained_until_inv s1 s (LIGHTING_TIME'TIMEOUT + MORNING_LIGHTING_TIME'TIMEOUT)
 (LIGHTING_TIME'TIMEOUT + ltime s Lighting' - 1)
(\<lambda> s2. (getVarBool s2 dayLight' = True \<or> getVarBool s2 dimLight' = True) \<and> getVarBool s2 motion' = False)
 (\<lambda> s3. getVarBool s3 dayLight' = False \<and> getVarBool s3 dimLight'= False \<or> getVarBool s3 motion' = True))) \<and>
(getPstate s Motion' \<noteq>  Motion'movement' \<and> getPstate s Lighting' = Lighting'morningOrDay' \<longrightarrow> 
always s (\<lambda> s1. getVarBool s1 motion' = False \<longrightarrow> constrained_until_inv s1 s (LIGHTING_TIME'TIMEOUT + MORNING_LIGHTING_TIME'TIMEOUT)
(LIGHTING_TIME'TIMEOUT + MORNING_LIGHTING_TIME'TIMEOUT)
(\<lambda> s2. (getVarBool s2 dayLight' = True \<or> getVarBool s2 dimLight' = True) \<and> getVarBool s2 motion' = False)
 (\<lambda> s3. getVarBool s3 dayLight' = False \<and> getVarBool s3 dimLight'= False \<or> getVarBool s3 motion' = True)))  \<and>
(getPstate s Motion' \<noteq>  Motion'movement' \<and> getPstate s Lighting' \<in> {Lighting'night', Lighting'earlyMorning', Lighting'evening'} \<longrightarrow> 
always s (\<lambda> s1. getVarBool s1 motion' = False \<longrightarrow> constrained_until_inv s1 s (LIGHTING_TIME'TIMEOUT + MORNING_LIGHTING_TIME'TIMEOUT) 0
(\<lambda> s2. (getVarBool s2 dayLight' = True \<or> getVarBool s2 dimLight' = True) \<and> getVarBool s2 motion' = False)
 (\<lambda> s3. getVarBool s3 dayLight' = False \<and> getVarBool s3 dimLight'= False \<or> getVarBool s3 motion' = True)))"

theorem extra1: "VC1 extraInv s0"
  apply(unfold VC1_def extraInv_def commonExtraInv_def always_def constrained_until_inv_def)
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
  apply(simp only: imp_conv_disj)
   apply(rule always_rule[of s0])
    apply(rule conj_forward)
      prefer 2
      apply(rotate_tac -1)
      apply assumption
     prefer 2
     apply(rule conj_forward)
       prefer 2
       apply(rule disj_forward)
         prefer 2
      apply(rotate_tac -1)
         apply assumption
        prefer 2
        apply(rule constrained_until_one_point)
         apply simp
      apply(rotate_tac -1)
        apply assumption
      apply(rotate_tac -1)
       apply assumption
      prefer 2
      apply(rule all_disj_rule)
      apply(rule conj_forward)
        prefer 2
  apply(rule all_imp_refl)
      apply(rotate_tac -1)
        apply assumption
       prefer 2 
       apply(rule constrained_until_rule[of s0])
        apply simp
       apply(rule conj_forward)
         prefer 2
         apply(rule all_imp_refl)
         apply(rotate_tac -1)
         apply assumption
        prefer 2
        apply(rule conj_forward)
          prefer 2
        apply(rule all_imp_refl)
         apply(rotate_tac -1)
          apply assumption
         prefer 2
         apply(rotate_tac -1)
         apply assumption
         apply(rotate_tac -1)
        apply assumption
         apply(rotate_tac -1)
       apply assumption
         apply(rotate_tac -1)
      apply assumption
         apply(rotate_tac -1)
     apply assumption
    apply auto[2]
  apply(rule conjI)
   apply simp
  apply simp
  done







