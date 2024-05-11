theory ExtraInv_R1
  imports CommonExtraInv "../Patterns"
begin

definition extraInv where "extraInv s \<equiv> commonExtraInv s \<and>
P6_4inv s (getPstate s Controller' \<noteq> Controller'sale') (getPstate s Controller' \<noteq> Controller'choice')
 (getPstate s Controller' \<noteq> Controller'waiting')
 (\<lambda> s1. getVarInt s1 mode'= IDLE') (\<lambda> s2. getVarInt s2 mode' = CHOICE') (\<lambda> s3. getVarBool s3 product1' = False)
 (\<lambda> s4. getVarBool s4 button1' = True)"

end