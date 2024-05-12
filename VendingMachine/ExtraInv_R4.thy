theory ExtraInv_R4
  imports CommonExtraInv "../Patterns"
begin

definition extraInv where "extraInv s == commonExtraInv s \<and>
P4'inv s 2 
(if getPstate s Controller' = Controller'sale' \<and> getPstate s Sale1' = STOP \<and> getPstate s Sale2' = STOP then 1
else if getPstate s Controller' = Controller'payOut' \<and> getVarBool s dispense' = False then 2 else 0)
(getPstate s Sale1' \<noteq> Sale1'delivery')
(\<lambda> s1. getVarBool s1 product1' = True) (\<lambda> s2. getVarBool s2 given1' = True \<and> getVarInt s2 credit' > 0)
(\<lambda> s3. getVarBool s3 dispense' = False \<and> getVarBool s3 paidOut' = False)
 (\<lambda> s4. getVarBool s4 dispense' = True \<and> getVarInt s4 change' = getVarInt s4 credit' \<or> getVarBool s4 paidOut' = True)"

end