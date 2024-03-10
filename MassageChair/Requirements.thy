theory Requirements
  imports MassageChair "../Pattern1_Def" "../Pattern6_Def" "../Pattern12_Def" "../Pattern2_Def"
begin

definition R1 where "R1 s \<equiv> toEnvP s \<and>
(\<forall> s1. substate s1 s \<and> toEnvP s1 \<and> getVarBool s1 up' = True \<longrightarrow> getVarBool s1 down' = False)"

definition R2 where "R2 s \<equiv> toEnvP s \<and>
(\<forall> s1. substate s1 s \<and> toEnvP s1 \<and> (getVarBool s1 buttonDown' = False \<or> getVarBool s1 lower' = True) \<longrightarrow> getVarBool s1 down'= False)"

definition R3 where "R3 s \<equiv> toEnvP s \<and>
(\<forall> s1. substate s1 s \<and> toEnvP s1 \<and> getVarBool s1 enabled' = False \<longrightarrow> getVarBool s1 up' = False \<and> getVarBool s1 down' = False)"

definition R4 where "R4 s \<equiv> toEnvP s \<and>
(\<forall> s2 s1. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and> getVarBool s1 enabled' = False \<and> getVarBool s2 enabled' = True \<and>
getVarBool s2 rollerButton' = False \<longrightarrow> getVarBool s2 roller' = False)"

definition R5 where "R5 s \<equiv> toEnvP s \<and>
(\<forall> s1. substate s1 s \<and> toEnvP s1 \<and> getVarBool s1 rollerButton' = PRESSED' \<and> getVarBool s1 enabled' = True \<longrightarrow> getVarBool s1 roller' = True)"

abbreviation MASSAGE_TIME where "MASSAGE_TIME \<equiv> ROLLER_MASSAGE_TIME'TIMEOUT + VIBRATION_MASSAGE_TIME'TIMEOUT"

definition R6 where "R6 s \<equiv> toEnvP s \<and>
P1 s MASSAGE_TIME (\<lambda> s1. getVarBool s1 roller' = True \<or> getVarBool s1 vibration' = True)
 (\<lambda> s3. getVarBool s3 roller' = False \<and> getVarBool s3 vibration' = False \<or> getVarBool s3 startButton' = PRESSED')
(\<lambda> s2. (getVarBool s2 roller' = True \<or> getVarBool s2 vibration' = True) \<and> getVarBool s2 startButton' \<noteq> PRESSED')"

definition R7 where "R7 s \<equiv> toEnvP s \<and>
(\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 > ON_OFF_TIME'TIMEOUT  \<and> (getVarBool s1 enabled' = True) \<and>
 (getVarBool s2 onOff' \<noteq> PRESSED') \<and>
(\<forall>  s3. toEnvP s3 \<and>substate s1 s3 \<and> substate s3 s2 \<and> s1 \<noteq> s3 \<and> s3 \<noteq> s2 \<longrightarrow> getVarBool s3 onOff' = PRESSED') \<longrightarrow>
getVarBool s2 roller' = False \<and> getVarBool s2 vibration' = False)"

definition R7_1 where "R7_1 s \<equiv> toEnvP s \<and>
P2 s (\<lambda> s1 s2.  P12op s1 ON_OFF_TIME'TIMEOUT (\<lambda> s3. getVarBool s3 enabled' = True)  (\<lambda> s4. getVarBool s4 onOff' = PRESSED') \<and> getVarBool s2 onOff' \<noteq> PRESSED')
 (\<lambda> s1 s2. getVarBool s2 roller' = False \<and> getVarBool s2 vibration' = False)
"

definition R8 where "R8 s \<equiv> toEnvP s \<and>
(\<forall> s1 s2 s4. substate s1 s2 \<and> substate s2 s4 \<and> substate s4 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvP s4 \<and> toEnvNum s1 s2 > ON_OFF_TIME'TIMEOUT  \<and> (getVarBool s1 enabled' = True) \<and>
 (getVarBool s2 onOff' \<noteq> PRESSED') \<and>
(\<forall>  s3. toEnvP s3 \<and>substate s1 s3 \<and> substate s3 s2 \<and> s1 \<noteq> s3 \<and> s3 \<noteq> s2 \<longrightarrow> getVarBool s3 onOff' = PRESSED') \<and>
(\<forall> s5. toEnvP s5 \<and> substate s2 s5 \<and> substate s5 s4 \<longrightarrow> getVarBool s5 upper' = False) \<longrightarrow>
getVarBool s4 up' = True)"


definition R8_1 where "R8_1 s \<equiv> toEnvP s \<and>
P6 s (\<lambda> s3 s4. P12op s3 ON_OFF_TIME'TIMEOUT (\<lambda> s1. getVarBool s1 enabled' = True) (\<lambda> s2. getVarBool s2 onOff' = PRESSED') \<and> getVarBool s4 onOff' \<noteq> PRESSED')
(\<lambda> s5. getVarBool s5 up' = True) (\<lambda> s6. getVarBool s6 upper' = True)"


definition R9 where "R9 s \<equiv> toEnvP s \<and>
P6 s (\<lambda> s1 s2. getVarBool s1 enabled' = True \<and> getVarBool s2 enabled' = False) (\<lambda> s3. getVarBool s3 up' = True) (\<lambda> s4. getVarBool s4 upper' = True)"

end



