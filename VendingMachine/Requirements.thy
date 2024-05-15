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
P4' s 2 (\<lambda> s1. getVarBool s1 product1' = True) (\<lambda> s2. getVarBool s2 given1' = True \<and> getVarInt s2 credit' > 0)
(\<lambda> s3. getVarBool s3 dispense' = False \<and> getVarBool s3 paidOut' = False)
 (\<lambda> s4. getVarBool s4 dispense' = True \<and> getVarInt s4 change' = getVarInt s4 credit' \<or> getVarBool s4 paidOut' =True)"

definition R5 where "R5 s \<equiv> toEnvP s \<and>
always s (\<lambda> s1. getVarInt s1 mode' = IDLE' \<longrightarrow> getVarBool s1 lockChanger' = False)"

definition R6 where "R6 s \<equiv> toEnvP s \<and>
P4' s 2 (\<lambda> s1. getVarInt s1 mode' = CHOICE' \<or> getVarInt s1 mode' = ADD_MONEY') (\<lambda> s2. getVarBool s2 cancel')
(\<lambda> s3. getVarBool s3 dispense' = False \<and> getVarBool s3 paidOut' = False)
 (\<lambda> s4. getVarBool s4 dispense' = True \<and> getVarInt s4 change' = getVarInt s4 credit' \<or> getVarBool s4 paidOut' =True)"

definition R7 where "R7 s \<equiv>  toEnvP s \<and>
always s (\<lambda> s1.  getVarInt s1 mode' = IDLE' \<longrightarrow> getVarInt s1 credit' \<le> 0)"

definition R8 where "R8 s \<equiv> toEnvP s \<and> 
always2_2 s (\<lambda> s1. getVarBool s1 lockChanger' = False) (\<lambda> s2. True)
 (\<lambda> s1 s2. getVarInt s2 credit' = getVarInt s1 credit' + getVarInt s2 deposited')"

definition R9 where "R9 s \<equiv> toEnvP s \<and>
always2_2 s (\<lambda> s1. getVarBool s1 product1' = True) (\<lambda> s2. getVarBool s2 given1' = True)
 (\<lambda> s1 s2. getVarInt s2 credit' = getVarInt s1 credit' - PRICE1')"

definition R10 where "R10 s \<equiv> toEnvP s \<and>
P4' s 1 (\<lambda> s1. getVarBool s1 product1' = True) (\<lambda> s2. getVarBool s2 product1' = False \<and> getVarBool s2 given1' = False)
(\<lambda> s3. getVarInt s3 mode' \<noteq> CHOICE') (\<lambda> s4. getVarInt s4 mode' = CHOICE')"

definition R11 where "R11 s \<equiv> toEnvP s \<and>
always s (\<lambda> s1. getVarBool s1 product1' = True \<or> getVarBool s1 product2' = True \<longrightarrow> getVarBool s1 lockChanger' = True)"

definition R12 where "R12 s \<equiv> toEnvP s \<and>
(\<forall> s1. substate s1 s \<and> toEnvP s1 \<and> getVarBool s1 product1' = True \<longrightarrow> getVarBool s1 product2' = False)"

end