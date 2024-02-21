theory ExtraInv_R6a
  imports CommonExtraInv "../Pattern4_Def" Requirements
begin

definition extraInv where "extraInv s \<equiv>
commonExtraInv s \<and>
(getPstate s Washing' \<noteq> Washing'wash' \<longrightarrow>
P4inv s WASHING_TIME'TIMEOUT 0
 (\<lambda> s1 s2. getVarBool s1 washing' = False \<and> getVarBool s2 washing' = True )
 (\<lambda> s4. getVarBool s4 washing' = False )
 (\<lambda> s3. getVarBool s3 washing' = True)) \<and>
(getPstate s Washing' = Washing'wash' \<longrightarrow>
P4inv s WASHING_TIME'TIMEOUT (ltime s Washing')
 (\<lambda> s1 s2. getVarBool s1 washing' = False \<and> getVarBool s2 washing' = True )
 (\<lambda> s4. getVarBool s4 washing' = False )
 (\<lambda> s3. getVarBool s3 washing' = True))"

theorem extra1: "VC1 extraInv s0"
  apply(unfold VC1_def extraInv_def P4inv_def)
  using cei1 by(auto simp add: VC1_def)

definition inv6a where "inv6a s \<equiv> extraInv s \<and> R6a s"

end