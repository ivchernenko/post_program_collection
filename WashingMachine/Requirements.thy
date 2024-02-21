theory Requirements
  imports WashingMachine "../Pattern6_Def" "../Pattern4_Def"
begin

definition R1 where "R1 s \<equiv> toEnvP s \<and>
(\<forall> s2 s1. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and> getVarBool s1 lock' = False \<and> getVarBool s2 startButton' = True \<longrightarrow>
getVarBool s2 lock' = True)"

definition R2 where "R2 s \<equiv> toEnvP s \<and>
(\<forall> s1 s2 s3. substate s1 s2 \<and> substate s2 s3 \<and> substate s3 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvP s3 \<and> toEnvNum s1 s2 = 1 \<and> s2 \<noteq> s3 \<and>
 (getVarBool s1 lock' = False \<and> getVarBool s2 lock' = True) \<and> getVarBool s3 locked' = True \<and>
(\<forall> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s3 \<and> s2 \<noteq>  s4 \<and> s4 \<noteq> s3 \<longrightarrow> getVarBool s4 locked' = False) \<longrightarrow>
getVarBool s3 filling' = True \<and> (getVarBool s3 left' = True \<or> getVarBool s3 right' = True))"

definition R3 where "R3 s \<equiv> toEnvP s \<and>
(\<forall> s2 s1. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and> getVarBool s1 filling' = False \<and> getVarBool s2 locked' = False \<longrightarrow>
getVarBool s2 filling' = False)"

definition R4 where "R4 s \<equiv> toEnvP s \<and>
(\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and> toEnvP  s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and>
 getVarBool s1 filling' = True \<and> getVarBool s2 waterLevel' \<noteq> SUFFICIENT' \<longrightarrow> getVarBool s2 filling' = True)"

definition R5 where "R5 s \<equiv> toEnvP s \<and>
(\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and> getVarBool s1 filling' = True \<and> getVarBool s2 waterLevel' = SUFFICIENT' \<longrightarrow>
getVarBool s2 filling' = False \<and> getVarBool s2 washing' = True)"

definition R6a where "R6a s \<equiv> toEnvP s \<and>
(\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and> toEnvNum s2 s >= WASHING_TIME'TIMEOUT \<and>
 getVarBool s1 washing' = False \<and> getVarBool s2 washing' = True \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s \<and> toEnvNum s2 s4 \<le> WASHING_TIME'TIMEOUT \<and> getVarBool s4 washing' = False \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> getVarBool s3 washing' = True)))"

definition R6a' where "R6a' s \<equiv> toEnvP s \<and>
P4 s WASHING_TIME'TIMEOUT (\<lambda> s1 s2. getVarBool s1 washing' = False \<and> getVarBool s2 washing' = True) (\<lambda> s4. getVarBool s4 washing' = False)
 (\<lambda> s3. getVarBool s3 washing' = True)"

definition R6b where "R6b s \<equiv> toEnvP s \<and>
(\<forall> s1 s2 s3. substate s1 s2 \<and> substate s2 s3 \<and> substate s3 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvP s3 \<and> toEnvNum s1 s2 = 1 \<and> toEnvNum s2 s3 < WASHING_TIME'TIMEOUT \<and>
getVarBool s1 washing' = False \<and> getVarBool s2 washing' = True \<longrightarrow> getVarBool s3 washing' = True)"

definition R7 where "R7 s \<equiv> toEnvP s \<and>
(\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and> getVarBool s1 washing' = True \<and> getVarBool s2 washing' = False \<longrightarrow>
getVarBool s2 drain' = True)"

definition R8 where "R8 s \<equiv> toEnvP s \<and>
(\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and> getVarBool s1 drain' = True \<and> getVarBool s2 waterPresence' = True \<longrightarrow>
getVarBool s2 drain' = True)"

definition R9 where "R9 s \<equiv> toEnvP s \<and>
(\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and> getVarBool s1 drain' = True \<and> getVarBool s2 waterPresence' = False \<longrightarrow>
getVarBool s2 drain' = False \<and> getVarBool s2 lock' = False)"

definition R10 where "R10 s \<equiv> toEnvP s \<and>
(\<forall> s1. substate s1 s \<and>  toEnvP s1  \<and> getVarBool s1 lock' = False \<longrightarrow> getVarBool s1 left' = False \<and> getVarBool s1 right' = False)"

definition R11 where "R11 s \<equiv> toEnvP s \<and>
P6 s (\<lambda> s1 s2. getVarBool s1 lock' = False \<and> getVarBool s2 lock' = True)
 (\<lambda> s3. getVarBool s3 left' = False \<and> getVarBool s3 right' = False \<and> getVarBool s3 filling' = False) (\<lambda> s4. getVarBool s4 locked' = True) "

definition R12 where "R12 s \<equiv> toEnvP s \<and>
(\<forall> s1. substate s1 s \<and> toEnvP s1 \<and> getVarBool s1 left' = True \<longrightarrow> getVarBool s1 right' = False)"

definition R13a where "R13a s \<equiv> toEnvP s \<and>
P4 s DIRECTION_CHANGE_PERIOD'TIMEOUT (\<lambda> s1 s2. getVarBool s1 left' = False \<and> getVarBool s2 left' = True) (\<lambda> s4. getVarBool s4 left' = False)
 (\<lambda> s3. getVarBool s3 left' = True)"

definition R13b where "R13b s \<equiv> toEnvP s \<and>
(\<forall> s1 s2 s3. substate s1 s2 \<and> substate s2 s3 \<and> substate s3 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvP s3 \<and> toEnvNum s1 s2 = 1 \<and>
 toEnvNum s2 s3 < DIRECTION_CHANGE_PERIOD'TIMEOUT \<and> getVarBool s1 left' = False \<and> getVarBool s2 left' = True \<longrightarrow> getVarBool s3 left' = True)"

definition R14 where "R14 s \<equiv> toEnvP s \<and>
(\<forall> s1 s2 s3 s4. substate s1 s2 \<and> substate s2 s3 \<and> substate s3 s4 \<and> substate s4 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvP s3 \<and> toEnvP s4 \<and> toEnvNum s1 s2 = 1 \<and> 
toEnvNum s3 s4 = 1 \<and>
(getVarBool s1 left' = True \<and> getVarBool s2 left' = False \<and> \<not> (getVarBool s1 drain' = True \<and> getVarBool s2 drain' = False)) \<and>
 (getVarInt s4 freq' = 0 \<and> \<not> (getVarBool s3 drain' = True \<and> getVarBool s4 drain' = False)) \<and>
(\<forall> s5 s6. toEnvP s5 \<and> toEnvP s6 \<and> substate s2 s5 \<and> substate s5 s6 \<and> substate s6 s3 \<longrightarrow>
 getVarInt s6 freq' \<noteq> 0 \<and> \<not> (getVarBool s5 drain' = True \<and> getVarBool s6 drain' = False)) \<longrightarrow>
getVarBool s4 right' = True)"

end