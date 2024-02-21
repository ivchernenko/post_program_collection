theory Requirements
  imports MassageChair
begin

definition R1 where "R1 s \<equiv> toEnvP s \<and>
(\<forall> s1. substate s1 s \<and> toEnvP s1 \<and> getVarBool s1 up' = True \<longrightarrow> getVarBool s1 down' = False)"

definition R2 where "R2 s \<equiv> toEnvP s \<and>
(\<forall> s1. substate s1 s \<and> toEnvP s1 \<and> (getVarBool s1 buttonDown' = False \<or> getVarBool s1 lower' = True) \<longrightarrow> getVarBool s1 down'= True)"

definition R3 where "R3 s \<equiv> toEnvP s \<and>
(\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and>
 getVarBool s1 move' = True \<and> getVarInt s1 vibration' = 0 \<and> getVarBool s2 vibrationButton' = PRESSED' \<and> getVarBool s2 move' = True \<longrightarrow>
 getVarInt s2 vibration' = FAST')"

definition R4 where "R4 s \<equiv> toEnvP s \<and>
(\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and>
 getVarBool s1 move' = True \<and> getVarInt s1 vibration' = FAST' \<and> getVarBool s2 vibrationButton' = PRESSED' \<and> getVarBool s2 move' = True \<longrightarrow>
 getVarInt s2 vibration' = MODERATE')"

definition R5 where "R5 s \<equiv> toEnvP s \<and>
(\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and>
 getVarInt s1 vibration' = MODERATE' \<and> getVarBool s2 vibrationButton' = PRESSED' \<longrightarrow>  getVarInt s2 vibration' = 0)"

definition R6 where "R6 s \<equiv> toEnvP s \<and>
(\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and> toEnvNum s2 s \<ge> 20 * 60 * 10 \<and> getVarBool s1 min10' = True \<and>
getVarBool s2 changeDuration' = PRESSED' \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s  \<and> toEnvNum s2 s4 \<le> 20 * 60 *10 \<and> (getVarBool s4 move' = False \<or> getVarBool s4 changeDuration' = PRESSED') \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> getVarBool s3 move' = True \<and> getVarBool s3 changeDuration' = False)))"

end