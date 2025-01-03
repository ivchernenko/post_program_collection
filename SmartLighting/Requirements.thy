theory Requirements
  imports SmartLighting "../Pattern5_Def" "../Pattern2_Def" "../Pattern7_Def" "../Pattern1_Def" "../Pattern3_Def"
begin

definition R1 where "R1 s \<equiv> toEnvP s \<and>
(\<forall> s1. substate s1 s \<and> toEnvP s1 \<and> getVarInt s1 timeOfDay' = NIGHT' \<longrightarrow> getVarBool s1 dayLight' = TURNED_OFF' \<and> getVarBool s1 dimLight' = TURNED_OFF')"

definition R2 where "R2 s \<equiv> toEnvP s \<and>
P5_1 s LIGHTING_TIME'TIMEOUT (\<lambda> s1.  getVarBool s1 motion' = True \<and>  getVarBool s1 light' = LOW')
  (\<lambda> s3. P2all s3 (\<lambda> s2. getVarInt s2 timeOfDay' = NIGHT' \<or> getVarInt s3 timeOfDay' = NIGHT' \<or>
 getVarBool s3 dayLight' = True \<or> getVarBool s3 dimLight' = True))
"

definition R2_1 where "R2_1 s \<equiv> toEnvP s \<and>
P7 s LIGHTING_TIME'TIMEOUT (\<lambda> s1 s2. getVarInt s1 timeOfDay' \<noteq> NIGHT' \<and> getVarInt s2 timeOfDay' \<noteq> NIGHT' \<and> getVarBool s2 motion' \<and> getVarBool s2 light' = LOW')
(\<lambda> s4. getVarInt s4 timeOfDay' = NIGHT') (\<lambda> s3. getVarBool s3 dayLight' = TURNED_ON' \<or> getVarBool s3 dimLight' = TURNED_ON')"


definition R3 where "R3 s == toEnvP s \<and>
P5_2 s (MORNING_LIGHTING_TIME'TIMEOUT + 1) (\<lambda> s1 s2.  getVarInt s1 timeOfDay' = EARLY_MORNING' \<and> getVarInt s2 timeOfDay' = MORNING_LIGHTING')
(\<lambda> s3. getVarBool s3 dimLight' = TURNED_ON')"

definition R4 where "R4 s \<equiv> toEnvP s \<and>
(\<forall> s2 s1. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and>  getVarInt s1 timeOfDay' = DAY' \<longrightarrow> getVarBool s2 dimLight' = False)"

definition R5 where "R5 s \<equiv> toEnvP s \<and>
(\<forall> s2 s1. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and>  getVarInt s1 timeOfDay' = EVENING' \<longrightarrow> getVarBool s2 dayLight' = False)"

definition R6 where "R6 s == toEnvP s \<and>
(\<forall> s1. substate s1 s \<and> toEnvP s1 \<and> getVarBool s1 dayLight' = TURNED_ON' \<longrightarrow> getVarBool s1 dimLight' = TURNED_OFF')"

definition R7 where "R7  s \<equiv> toEnvP s \<and>
P1 s (LIGHTING_TIME'TIMEOUT + MORNING_LIGHTING_TIME'TIMEOUT) (\<lambda> s1. getVarBool s1 motion' = False)
 (\<lambda> s3. getVarBool s3 dayLight' = False \<and> getVarBool s3 dimLight'= False \<or> getVarBool s3 motion' = True)
(\<lambda> s2. (getVarBool s2 dayLight' = True \<or> getVarBool s2 dimLight' = True) \<and> getVarBool s2 motion' = False)"

definition R7_1 where "R7_1 s \<equiv> toEnvP s \<and>
always s (\<lambda> s1. getVarBool s1 motion' = False \<longrightarrow> constrained_until s1 s (LIGHTING_TIME'TIMEOUT + MORNING_LIGHTING_TIME'TIMEOUT)
(\<lambda> s2. (getVarBool s2 dayLight' = True \<or> getVarBool s2 dimLight' = True) \<and> getVarBool s2 motion' = False)
 (\<lambda> s3. getVarBool s3 dayLight' = False \<and> getVarBool s3 dimLight'= False \<or> getVarBool s3 motion' = True))"

definition R8 where "R8 s \<equiv> toEnvP s \<and>
P1 s (LIGHTING_TIME'TIMEOUT - 1) (\<lambda> s2. P2ex s2 (\<lambda> s1. getVarBool s1 motion' = True \<and> getVarBool s2 motion' = False))
 (\<lambda> s3. getVarBool s3 dayLight' = False \<and> getVarBool s3 dimLight'= False \<or> getVarBool s3 motion' = True \<or>
 P2ex s3 (\<lambda> s2'.  getVarInt s2' timeOfDay' = MORNING_LIGHTING' \<or> getVarInt s3 timeOfDay' = MORNING_LIGHTING'))
(\<lambda> s2. (getVarBool s2 dayLight' = True \<or> getVarBool s2 dimLight' = True) \<and> getVarBool s2 motion' = False \<and>
 P2all s2 (\<lambda> s1'. getVarInt s1' timeOfDay' \<noteq> MORNING_LIGHTING' \<and>getVarInt s2 timeOfDay' \<noteq> MORNING_LIGHTING'))"

end