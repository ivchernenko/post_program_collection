theory ExtraInv_R6
  imports CommonExtraInv "../Patterns"
begin

definition extraInv where "extraInv s == commonExtraInv s \<and>
P4'inv s 2 
(if getPstate s Controller' = Controller'sale' \<and> getPstate s Sale1' = STOP \<and> getPstate s Sale2' = STOP then 1
else if getPstate s Controller' = Controller'payOut' \<and> getVarBool s dispense' = False then 2 else 0)
(getPstate s Controller' \<noteq> Controller'choice' \<and> getVarInt s mode' \<noteq> ADD_MONEY')
(\<lambda> s1. getVarInt s1 mode' = CHOICE' \<or> getVarInt s1 mode' = ADD_MONEY') (\<lambda> s2. getVarBool s2 cancel')
(\<lambda> s3. getVarBool s3 dispense' = False \<and> getVarBool s3 paidOut' = False)
 (\<lambda> s4. getVarBool s4 dispense' = True \<and> getVarInt s4 change' = getVarInt s4 credit' \<or> getVarBool s4 paidOut' = True)"

end