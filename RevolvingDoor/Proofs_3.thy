theory Proofs_3
  imports Requirements ExtraInv VCTheoryLemmas
begin

definition pred3 where "pred3 s1 s2 s s5 \<equiv>
substate s1 s2 \<and>
    substate s2 s \<and>
    toEnvP s1 \<and>
    toEnvP s2 \<and>
    toEnvNum s1 s2 = 1 \<and> DELAY'TIMEOUT = toEnvNum s2 s \<and> getVarBool s1 rotation = True \<and> \<not> getVarBool s2 user \<and>
(\<forall> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s5 \<and> s4 \<noteq> s5 \<longrightarrow> getVarBool s4 rotation = True \<and> \<not> getVarBool s4 user)
 \<longrightarrow>
    (\<exists>s4. toEnvP s4 \<and>
          substate s5 s4 \<and>
          substate s4 s \<and>
          toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
          (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
          (\<forall>s3. toEnvP s3 \<and> substate s5 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user))"

thm extraInv_def
lemma rotating_not_vc3: "toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Controller = Controller'rotating \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 ERROR = Controller'rotating \<longrightarrow>
      (\<exists>s2 s3.
          toEnvP s2 \<and>
          toEnvP s3 \<and>
          substate s2 s3 \<and>
          substate s3 s1 \<and>
          toEnvNum s2 s3 = ERROR \<and>
          toEnvNum s2 s1 = ltime s1 ERROR \<and>
          ((getPstate s2 ERROR = Controller'motionless \<or> getPstate s2 ERROR = Controller'rotating) \<and>
           getVarBool s3 user \<or>
           getPstate s2 ERROR = Controller'suspended) \<and>
          \<not> getVarBool s3 pressure)) \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 ERROR = Controller'motionless \<longrightarrow>
      getVarBool s1 rotation = False \<and> getVarBool s1 brake = False) \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 ERROR = Controller'rotating \<longrightarrow>
      getVarBool s1 rotation = True \<and> getVarBool s1 brake = False) \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 ERROR = Controller'suspended \<longrightarrow>
      getVarBool s1 rotation = False \<and> getVarBool s1 brake = True) \<Longrightarrow>
(\<exists> s2 s3. toEnvP s2 \<and> toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s1 \<and> toEnvNum s2 s1 \<le> ltime s1 Controller \<and> toEnvNum s2 s3 = 1 \<and>
 (getVarBool s2 rotation = False \<or> getVarBool s3 user))
"
  by (metis eq_imp_le substate_trans)

definition inv3 where "inv3 s \<equiv> R3 s \<and> extraInv s"

theorem proof_3_1: "VC1 inv3 s0"
  apply(simp only: VC1_def inv3_def R3_def extraInv_def)
  by  auto

theorem proof_3_5: "VC5 inv3 env  s0 user_value pressure_value"
  apply(simp only: VC5_def inv3_def R3_def extraInv_def)
  by  auto

theorem proof_3_7: "VC7 inv3 env  s0 user_value pressure_value"
  apply(simp only: VC7_def inv3_def R3_def extraInv_def)
  by  auto

theorem proof_3_11: "VC11 inv3 env  s0 user_value pressure_value"
  apply(simp only: VC11_def inv3_def R3_def extraInv_def)
  by  auto
end
 


    
  
 