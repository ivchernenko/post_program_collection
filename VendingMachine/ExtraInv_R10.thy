theory ExtraInv_R10
  imports CommonExtraInv "../Patterns"
begin

definition extraInv where "extraInv s \<equiv> commonExtraInv s \<and>
P4'inv s 1 (if getPstate s Sale1' = ERROR then 1 else 0) (getPstate s Sale1' \<noteq> Sale1'delivery') 
 (\<lambda> s1. getVarBool s1 product1' = True) (\<lambda> s2. getVarBool s2 product1' = False \<and> getVarBool s2 given1' = False)
(\<lambda> s3. getVarInt s3 mode' \<noteq> CHOICE') (\<lambda> s4. getVarInt s4 mode' = CHOICE')"

end