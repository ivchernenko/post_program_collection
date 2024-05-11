theory Requirements
  imports VendingMachine "../Patterns"
begin

definition R1 where "R1 s \<equiv> toEnvP s \<and>
P6_4 s (\<lambda> s1. getVarInt s1 mode'= IDLE') (\<lambda> s2. getVarInt s2 mode' = CHOICE') (\<lambda> s3. getVarBool s3 product1' = False)
 (\<lambda> s4. getVarBool s4 button1' = True)
"

definition R2 where "R2 s \<equiv> toEnvP s \<and>
always2 s (\<lambda> s1. getVarBool s1 product1' = False) (\<lambda> s2. getVarInt s2 credit' < PRICE1')
 (\<lambda> s2. getVarBool s2 product1' = False)"

definition R3 where "R3 s \<equiv> toEnvP s \<and>
P6_5 s (\<lambda> s1. getVarInt s1 mode' = CHOICE')
 (\<lambda> s2. getVarBool s2 cancel' = False \<and> getVarBool s2 button1' = PRESSED' \<and> getVarInt s2 credit' < PRICE1')
(\<lambda> s3. getVarBool s3 lockChanger' = False \<and> getVarInt s3 mode' = ADD_MONEY')
 (\<lambda> s4. getVarBool s4 cancel' = True \<or> getVarInt s4 credit' \<ge> PRICE1')"

definition R4 where "R4 s \<equiv> toEnvP s \<and>
(\<forall> s1. substate s1 s \<and> toEnvP s1 \<and> toEnvNum s1 s \<ge> 1 \<and> getVarBool s1 given1' = True \<and> getVarInt s1 credit' > 0 \<longrightarrow>
(\<exists> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s \<and> toEnvNum s1 s3 \<le> 1 \<and> getVarBool s3 dispense' = True \<and> getVarInt s3 change' = getVarInt s3 credit' \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s3 \<and> s2 \<noteq> s3 \<longrightarrow> getVarBool s2 dispense' = False)))"

definition R5 where "R5 s \<equiv> toEnvP s \<and>
(\<forall> s1. substate s1 s \<and> toEnvP s1 \<and> getVarInt s1 mode' = IDLE' \<longrightarrow> getVarBool s1 lockChanger' = False)"

definition R6 where "R6 s \<equiv> toEnvP s \<and>
(\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and>
 getVarInt s1 mode' \<noteq> IDLE' \<and> getVarBool s1 product1' = False \<and> getVarBool s1 product2' = False \<and> getVarBool s2 cancel' = True \<longrightarrow>
 getVarBool s2 dispense' = True \<and> getVarInt s2 change' = getVarInt s2 credit')"

definition R7 where "R7 s \<equiv>  toEnvP s \<and>
(\<forall> s1. substate s1 s \<and> toEnvP s1 \<and> getVarInt s1 mode' = IDLE' \<longrightarrow> getVarInt s1 credit' = 0)"

definition R8 where "R8 s \<equiv> toEnvP s \<and> 
(\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and>  getVarBool s1 lockChanger' = False \<longrightarrow>
 getVarInt s2 credit' =  getVarInt s1 credit' + getVarInt s2 deposited')"

definition R9 where "R9 s \<equiv> toEnvP s \<and>
(\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and> getVarBool s2 given1' = True \<longrightarrow>
 getVarInt s2 credit' = getVarInt s1 credit' - PRICE1')"

definition R10 where "R10 s \<equiv> toEnvP s \<and>
(\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and> toEnvNum s2 s \<ge> 1 \<and>
 getVarBool s1 product1' = True \<and> getVarBool s2 product1' = False \<and> getVarBool s2 given1' = False \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s \<and> toEnvNum s2 s4 \<le> 1 \<and> getVarInt s4 mode' = CHOICE' \<and>
(\<forall> s3. substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> getVarInt s3 mode' \<noteq> CHOICE')))"

definition R11 where "R11 s \<equiv> toEnvP s \<and>
(\<forall> s1. substate s1 s \<and> toEnvP s1 \<and> (getVarBool s1 product1' = True \<or> getVarBool s1 product2' = True) \<longrightarrow> getVarBool s1 lockChanger' = True)"

definition R12 where "R12 s \<equiv> toEnvP s \<and>
(\<forall> s1. substate s1 s \<and> toEnvP s1 \<and> getVarBool s1 product1' = True \<longrightarrow> getVarBool s1 product2' = False)"

end