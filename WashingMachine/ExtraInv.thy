theory ExtraInv
  imports Requirements "../Pattern10_Def" "../Pattern11_Def"
begin

definition extraInv where "extraInv s \<equiv> toEnvP s \<and>
(\<forall>  s1. substate s1 s \<and> toEnvP s1 \<and>  getPstate s1 Washing' = Washing'idle' \<longrightarrow> 
getVarBool s1 filling' = False \<and> getVarBool s1 drain' = False \<and> getVarBool s1 heater' = False \<and> getVarBool s1 lock' = False \<and> getVarBool s1 washing' = False) \<and>
(\<forall>  s1. substate s1 s \<and> toEnvP s1 \<and>  getPstate s1 Washing' = Washing'locking' \<longrightarrow> 
getVarBool s1 filling' = False \<and> getVarBool s1 drain' = False \<and> getVarBool s1 heater' = False \<and> getVarBool s1 lock' = True \<and> getVarBool s1 washing' = False) \<and>
(\<forall>  s1. substate s1 s \<and> toEnvP s1 \<and>  getPstate s1 Washing' = Washing'waterSupply' \<longrightarrow> 
getVarBool s1 filling' = True \<and> getVarBool s1 drain' = False \<and> getVarBool s1 heater' = False \<and> getVarBool s1 lock' = True \<and> getVarBool s1 washing' = False) \<and>
(\<forall>  s1. substate s1 s \<and> toEnvP s1 \<and>  getPstate s1 Washing' = Washing'wash' \<longrightarrow> 
getVarBool s1 filling' = False \<and> getVarBool s1 drain' = False \<and> getVarBool s1 lock' = True \<and> getVarBool s1 washing' = True) \<and>
(\<forall> s1. substate s1 s \<and> toEnvP s1 \<and> getPstate s1 Washing' = Washing'wash' \<longrightarrow> ltime s1 Washing' \<le> WASHING_TIME'TIMEOUT) \<and>
(\<forall>  s1. substate s1 s \<and> toEnvP s1 \<and>  getPstate s1 Washing' = Washing'draining' \<longrightarrow> 
getVarBool s1 filling' = False \<and> getVarBool s1 drain' = True \<and> getVarBool s1 heater' = False \<and> getVarBool s1 lock' = True \<and> getVarBool s1 washing' = False) \<and>
(\<forall> s1. substate s1 s \<and> toEnvP s1 \<and> getPstate s1 Washing' \<in> {Washing'idle', Washing'locking'} \<longrightarrow> getPstate s1 Drum' = STOP) \<and>
(\<forall> s1. substate s1 s \<and> toEnvP s1 \<and> getPstate s1 Washing' \<in> {Washing'waterSupply', Washing'wash', Washing'draining'} \<longrightarrow> getPstate s1 Drum' \<noteq> STOP) \<and>
(\<forall> s1. substate s1 s \<and> toEnvP s1 \<longrightarrow> getPstate s1 Washing' \<in> {Washing'idle', Washing'locking', Washing'waterSupply',  Washing'wash', Washing'draining'}) \<and>
(\<forall> s1. substate s1 s \<and> toEnvP s1 \<and> getPstate s1 Drum' = Drum'leftRotation' \<longrightarrow> getVarBool s1 left' = True \<and> getVarBool s1 right' = False) \<and>
(\<forall> s1. substate s1 s \<and> toEnvP s1 \<and> getPstate s1 Drum' = Drum'rightRotation' \<longrightarrow> getVarBool s1 left' = False \<and> getVarBool s1 right' = True) \<and>
(\<forall> s1. substate s1 s \<and> toEnvP s1 \<and> getPstate s1 Drum' \<in> {Drum'leftToRight', Drum'rightToLeft', STOP} \<longrightarrow>
 getVarBool s1 left' = False \<and> getVarBool s1 right' =False) \<and>
(\<forall> s1. substate s1 s \<and> toEnvP s1 \<longrightarrow> getPstate s1 Drum' \<in> {Drum'leftRotation', Drum'leftToRight', Drum'rightRotation', Drum'rightToLeft', STOP}) \<and>
(getPstate s Washing' \<noteq> Washing'locking' \<longrightarrow>
P10inv s (\<lambda> s1 s2. getVarBool s1 lock' = False \<and> getVarBool s2 lock' = True) (\<lambda> s3. getVarBool s3 locked' = False))  \<and>
(getPstate s Drum' \<noteq> Drum'leftToRight' \<longrightarrow>
P11inv s (\<lambda> s1 s2. getVarBool s1 left' = True \<and> getVarBool s2 left' = False \<and> \<not> (getVarBool s1 drain' = True \<and> getVarBool s2 drain' = False))
(\<lambda> s5 s6.  ( getVarInt s6 freq' \<noteq> 0 \<and> \<not> (getVarBool s5 drain' = True \<and> getVarBool s6 drain' = False))))
"

definition inv2 where "inv2 s \<equiv> R2 s \<and> extraInv s"
definition inv14 where "inv14 s \<equiv> R14 s \<and> extraInv s"

theorem "VC1 inv2 s0"
  apply(unfold VC1_def inv2_def R2_def extraInv_def P10inv_def P11inv_def)
  by auto

end