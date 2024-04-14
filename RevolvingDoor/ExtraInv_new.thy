theory ExtraInv_new
  imports Requirements
begin

definition extraInv where "extraInv s \<equiv> toEnvP s \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Controller = Controller'rotating \<longrightarrow> ltime s1 Controller \<le> DELAY'TIMEOUT) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Controller = Controller'suspended \<longrightarrow> ltime s1 Controller \<le> SUSPENSION_TIME'TIMEOUT) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Controller = Controller'motionless \<longrightarrow>
 getVarBool s1 rotation = False \<and> getVarBool s1 brake = False) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Controller = Controller'rotating \<longrightarrow>
 getVarBool s1 rotation = True \<and> getVarBool s1 brake = False) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Controller = Controller'suspended \<longrightarrow>
 getVarBool s1 rotation = False \<and> getVarBool s1 brake = True) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<longrightarrow>
 getPstate s1 Controller = Controller'motionless \<or> getPstate s1 Controller = Controller'rotating \<or>
getPstate s1 Controller = Controller'suspended) \<and>
(\<forall> s5. toEnvP s5 \<and> substate s5 s \<and> getPstate s5 Controller = Controller'suspended \<longrightarrow>
(\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s5 \<and> toEnvNum s1 s2 = 1 \<and> getVarBool s1 brake \<and> \<not> getVarBool s2 pressure \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s5 \<and> toEnvNum s2 s4 \<le> SUSPENSION_TIME'TIMEOUT \<and> (getVarBool s4 rotation = True \<or> getVarBool s4 pressure) \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> getVarBool s3 rotation = False \<and> \<not> getVarBool s3 pressure)) \<or>
toEnvNum s2 s5 < ltime s5 Controller \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s5 \<longrightarrow> getVarBool s3 rotation = False \<and> \<not> getVarBool s3 pressure) )) \<and>
(\<forall> s5. toEnvP s5 \<and> substate s5 s \<and> getPstate s5 Controller = Controller'rotating \<longrightarrow>
(\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s5 \<and> toEnvNum s1 s2 = 1 \<and> getVarBool s1 brake \<and> \<not> getVarBool s2 pressure \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s5 \<and> toEnvNum s2 s4 \<le> SUSPENSION_TIME'TIMEOUT \<and> (getVarBool s4 rotation = True \<or> getVarBool s4 pressure) \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> getVarBool s3 rotation = False \<and> \<not> getVarBool s3 pressure))  )) \<and>
(\<forall> s5. toEnvP s5 \<and> substate s5 s \<and> getPstate s5 Controller = Controller'motionless \<longrightarrow>
(\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s5 \<and> toEnvNum s1 s2 = 1 \<and> getVarBool s1 brake \<and> \<not> getVarBool s2 pressure \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s5 \<and> toEnvNum s2 s4 \<le> SUSPENSION_TIME'TIMEOUT \<and> (getVarBool s4 rotation = True \<or> getVarBool s4 pressure) \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> getVarBool s3 rotation = False \<and> \<not> getVarBool s3 pressure)) ))"

theorem extra_1: "VC1 extraInv  s0"
  apply(unfold VC1_def extraInv_def)
  by auto

definition inv5 where "inv5 s \<equiv> R5 s \<and> extraInv s"

end