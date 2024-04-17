theory ExtraInv_R7
  imports CommonExtraInv "../Patterns"
begin

definition extraInv where "extraInv s \<equiv> commonExtraInv s \<and>
P5_1inv s OPEN_TIME'TIMEOUT (if getPstate s Opening' = Opening'open' then ltime s Opening' - 1 else
 if getPstate s Opening' = Opening'opening' \<or> getPstate s Opening' = STOP  then 0 else OPEN_TIME'TIMEOUT - 1)
  (\<lambda> s1. getVarBool s1 peCarUnder' = True) (\<lambda> s2. getVarBool s2 down' = False)"

end