theory ExtraInv_R6
  imports CommonExtraInv "../Patterns"
begin

definition extraInv where "extraInv s \<equiv> commonExtraInv s \<and>
P5_2inv s OPEN_TIME'TIMEOUT (if getPstate s Opening' = Opening'open' then ltime s Opening' - 1 else
 if getPstate s Opening' = Opening'opening' \<and> getVarBool s green' = True then 0 else OPEN_TIME'TIMEOUT - 1) (getPstate s Opening'  = Opening'open')
  (\<lambda> s1. getVarBool s1 green' = False) (\<lambda> s2. getVarBool s2 green' = True) (\<lambda> s3. getVarBool s3 down' = False)"

end
