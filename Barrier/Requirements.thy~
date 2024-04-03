theory Requirements
  imports Barrier
begin

definition R1 where "R1 s \<equiv> toEnvP s \<and>
(\<forall> s1. substate s1 s \<and> toEnvP s1 \<and> getVarBool s1 up' = True \<longrightarrow> getVarBool s1 down' = False)"

definition R2 where "R2 s \<equiv> toEnvP s \<and>
(\<forall> s1. substate s1 s \<and> toEnvP s1 \<and> getVarBool s1 peCarUnder' = True \<longrightarrow> getVarBool s1 down' = False)"

definition R3 where "R3 s \<equiv> toEnvP s \<and>
(\<forall> s1 s2 s3. substate s1 s2 \<and> substate s2 s3 \<and> substate s3 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvP s3 \<and> toEnvNum s1 s2 = 1 \<and>
 getVarBool s1 down' = True \<and> getVarBool s2 down' = False \<and>
 (\<forall> s4 s5. toEnvP s4 \<and> toEnvP s5 \<and> substate s2 s4 \<and> substate s4 s5 \<and> substate s5 s3 \<and> toEnvNum s4 s5 = 1 \<longrightarrow>
 \<not> (getVarBool s4 carInFront' = False \<and> getVarBool s5 carInFront' = True)) \<longrightarrow>
getVarBool s3 up' = False)"

definition R4 where "R4 s \<equiv> toEnvP s \<and>
(\<forall> s1. substate s1 s \<and> toEnvP s1 \<and> toEnvNum s1 s \<ge> OPEN_TIME'TIMEOUT \<and> getVarBool s1 green' = True \<longrightarrow>
(\<exists> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s \<and> toEnvNum s1 s3 \<le> OPEN_TIME'TIMEOUT \<and> (getVarBool s3 down' = True \<or> getVarBool s3 peCarUnder' = True ) \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s3 \<and> s2 \<noteq> s3 \<longrightarrow> getVarBool s2 down' = False \<and> getVarBool s2 peCarUnder' = False)))"

definition R5 where "R5 s \<equiv> toEnvP s \<and>
(\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and>
 getVarBool s1 carInFront' = False \<and> getVarBool s2 carInFront' = True \<and> getVarBool s1 red' = True \<and> getVarBool s2 opened' = False \<longrightarrow> getVarBool s2 up' = True)"

definition R6 where "R6 s \<equiv> toEnvP s \<and>
(\<forall> s1 s2 s3. substate s1 s2 \<and> substate s2 s3 \<and> substate s3 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvP s3 \<and> toEnvNum s1 s2 = 1 \<and> toEnvNum s2 s3 < OPEN_TIME'TIMEOUT \<and>
getVarBool s1 green' = False \<and> getVarBool s2 green' = True \<longrightarrow> getVarBool s3 down' = False)"

definition R7 where "R7 s \<equiv> toEnvP s \<and>
(\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 < OPEN_TIME'TIMEOUT \<and>
getVarBool s1 peCarUnder' = True \<longrightarrow> getVarBool s2 down' = False)"

definition R8 where "R8 s \<equiv> toEnvP s \<and>
(\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> substate s2 s \<and> toEnvNum s1 s2 = 1 \<and> getVarBool s1 down' = True \<and> getVarBool s2 peCarUnder' = True \<longrightarrow> 
getVarBool s2 up' = True)"

definition R9 where "R9 s \<equiv> toEnvP s \<and>
(\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> getVarBool s1 up' = True \<and> getVarBool s2 opened' = False \<longrightarrow> getVarBool s2 up' = True)"

definition R10 where "R10 s \<equiv> toEnvP s \<and>
(\<forall> s1 s2 s3. substate s1 s2 \<and> substate s2 s3 \<and> substate s3 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvP s3 \<and> toEnvNum s1 s2 = 1 \<and> toEnvNum s2 s3 < OPEN_TIME'TIMEOUT \<and>
getVarBool s1 carInFront' = False \<and> getVarBool s2 carInFront' = True \<and> getVarBool s2 green' = True \<longrightarrow> getVarBool s3 down' = False)"

definition R11 where "R11 s \<equiv> toEnvP s \<and>
(\<forall> s1. substate s1 s \<and> toEnvP s1 \<and> (getVarBool s1 up' = True \<or> getVarBool s1 down' = True) \<longrightarrow> getVarBool s1 red' = True)"

definition R12 where "R12 s \<equiv> toEnvP s \<and> 
(\<forall> s1. substate s1 s \<and> toEnvP s1 \<and> getVarBool s1 red' = True \<longrightarrow> getVarBool s1 green' = False)"

end

