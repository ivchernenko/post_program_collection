theory Requirements
  imports Barrier "../Patterns"
begin

definition R1 where "R1 s \<equiv> toEnvP s \<and>
(\<forall> s1. substate s1 s \<and> toEnvP s1 \<and> getVarBool s1 up' = True \<longrightarrow> getVarBool s1 down' = False)"

definition R2 where "R2 s \<equiv> toEnvP s \<and>
(\<forall> s1. substate s1 s \<and> toEnvP s1 \<and> getVarBool s1 peCarUnder' = True \<longrightarrow> getVarBool s1 down' = False)"

definition R3 where "R3 s \<equiv> toEnvP s \<and>
P6_2 s (\<lambda> s1. getVarBool s1 down' = True) (\<lambda> s2. getVarBool s2 closed' = True) (\<lambda> s3. getVarBool s3 up' = False)
 (\<lambda> s4. getVarBool s4 carInFront' = False) (\<lambda> s5. getVarBool s5 carInFront' = True)"

definition R4Pattern where "R4Pattern s t A1 A2 A3 A4 A5 A6 A7 \<equiv> P1' s t A1 (\<lambda> s2. (previous_all s2 A2 \<or> A3 s2) \<and> A4 s2) (\<lambda> s3. (previous_ex s3 A5 \<and> A6 s3) \<or> A7 s3)"


definition R4 where "R4 s \<equiv> toEnvP s \<and>
R4Pattern s (OPEN_TIME'TIMEOUT) (\<lambda> s1. getVarBool s1 green' = True) (\<lambda> s2. getVarBool s2 carInFront' = True) (\<lambda> s3. getVarBool s3 carInFront' = False)
(\<lambda> s4. getVarBool s4 down' = False \<and> getVarBool s4 opened' = True \<and> getVarBool s4 peCarUnder' = False) 
(\<lambda> s2. getVarBool s2 carInFront' = False) (\<lambda> s3. getVarBool s3 carInFront' = True)
(\<lambda> s4. getVarBool s4 down' = True \<or> getVarBool s4 opened' = False \<or> getVarBool s4 peCarUnder' = True) "


definition R5 where "R5 s \<equiv> toEnvP s \<and>
(\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and>
 getVarBool s1 carInFront' = False \<and> getVarBool s2 carInFront' = True \<and>  getVarBool s2 opened' = False \<longrightarrow> getVarBool s2 up' = True)"

definition R6 where "R6 s \<equiv> toEnvP s \<and>
P5_2 s OPEN_TIME'TIMEOUT  (\<lambda> s1. getVarBool s1 green' = False) (\<lambda> s2. getVarBool s2 green' = True) (\<lambda> s3. getVarBool s3 down' = False)"

definition R7 where "R7 s \<equiv> toEnvP s \<and>
P5_1 s OPEN_TIME'TIMEOUT (\<lambda> s1. getVarBool s1 peCarUnder' = True) (\<lambda> s2. getVarBool s2 down' = False)"

definition R8 where "R8 s \<equiv> toEnvP s \<and>
(\<forall> s2 s1. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> substate s2 s \<and> toEnvNum s1 s2 = 1 \<and> getVarBool s1 down' = True \<and> getVarBool s2 peCarUnder' = True \<and>
getVarBool s2 opened' = False \<and> getVarBool s2 closed' = False \<longrightarrow>  getVarBool s2 up' = True)"

definition R9 where "R9 s \<equiv> toEnvP s \<and>
(\<forall> s2 s1. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and>
 getVarBool s1 up' = True \<and> getVarBool s2 opened' = False \<longrightarrow> getVarBool s2 up' = True)"

definition R9' where "R9' s \<equiv> toEnvP s \<and>
always2 s (\<lambda> s1. getVarBool s1 up' = True) (\<lambda> s2. getVarBool s2 opened' = False) (\<lambda> s2. getVarBool s2  up' = True)"

definition R10 where "R10 s \<equiv> toEnvP s \<and>
(\<forall> s1 s2 s3. substate s1 s2 \<and> substate s2 s3 \<and> substate s3 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvP s3 \<and> toEnvNum s1 s2 = 1 \<and> toEnvNum s2 s3 < OPEN_TIME'TIMEOUT \<and>
getVarBool s1 carInFront' = False \<and> getVarBool s2 carInFront' = True \<and> getVarBool s2 green' = True \<longrightarrow> getVarBool s3 down' = False)"

definition R11 where "R11 s \<equiv> toEnvP s \<and>
(\<forall> s1. substate s1 s \<and> toEnvP s1 \<and> (getVarBool s1 up' = True \<or> getVarBool s1 down' = True) \<longrightarrow> getVarBool s1 red' = True)"

definition R12 where "R12 s \<equiv> toEnvP s \<and> 
(\<forall> s1. substate s1 s \<and> toEnvP s1 \<and> getVarBool s1 red' = True \<longrightarrow> getVarBool s1 green' = False)"

end

