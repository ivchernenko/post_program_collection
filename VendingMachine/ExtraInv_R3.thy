theory ExtraInv_R3
  imports CommonExtraInv "../Patterns"
begin

definition extraInv where "extraInv s \<equiv> commonExtraInv s \<and>
P6_5inv s (getPstate s Sale1' = Sale1'addMoney') (getPstate s Controller' \<noteq> Controller'choice') (\<lambda> s1. getVarInt s1 mode' = CHOICE')
 (\<lambda> s2. getVarBool s2 cancel' = False \<and> getVarBool s2 button1' = PRESSED' \<and> getVarInt s2 credit' < PRICE1')
(\<lambda> s3. getVarBool s3 lockChanger' = False \<and> getVarInt s3 mode' = ADD_MONEY')
 (\<lambda> s4. getVarBool s4 cancel' = True \<or> getVarInt s4 credit' \<ge> PRICE1')"

end