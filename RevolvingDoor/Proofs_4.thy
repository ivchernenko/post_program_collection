theory Proofs_4
  imports Requirements ExtraInv VCTheoryLemmas
begin

thm extraInv_def

lemma suspended_not_rotation_and_pressure:
"toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Controller = Controller'suspended \<and>
(\<forall>s1 s2 s3.
    toEnvP s1 \<and>
    toEnvP s2 \<and>
    toEnvP s3 \<and>
    substate s1 s2 \<and>
    substate s2 s3 \<and>
    substate s3 s \<and>
    toEnvNum s1 s2 = ERROR \<and> toEnvNum s1 s3 < ltime s3 ERROR \<and> getPstate s3 ERROR = Controller'suspended \<longrightarrow>
    getPstate s1 ERROR = Controller'suspended \<and> \<not> getVarBool s2 pressure) \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 ERROR = Controller'suspended \<longrightarrow>
      getVarBool s1 rotation = False \<and> getVarBool s1 brake = True) \<Longrightarrow>
(\<forall> s2 s3. toEnvP s2 \<and> toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s1 \<and> toEnvNum s2 s3 = 1 \<and>
toEnvNum s2 s1 < ltime s1 Controller \<longrightarrow> \<not>(getVarBool s2 rotation = True \<and> getVarBool s3 pressure))"
  by blast

definition inv4 where "inv4 s \<equiv> R4 s \<and> extraInv s"

theorem proof_4_1: "VC1 inv4 s0"
  apply(simp only: VC1_def inv4_def R4_def extraInv_def)
  by auto

theorem proof_4_2: "VC2 R4 env s0 user_value pressure_value"
  apply(simp only: VC2_def R4_def)
  by auto

theorem proof_4_3: "VC3 R4 env s0 user_value pressure_value"
  apply(simp only: VC3_def R4_def)
  apply auto
  subgoal for s1 s2
    apply(rule cut_rl[of "toEnvNum s2 s0 < DELAY'TIMEOUT"])
    using substate_refl apply fast
    by simp
  done

theorem proof_4_5: "VC5 inv4 env  s0 user_value pressure_value"
  apply(simp only: VC5_def)
  by auto

theorem proof_4_6: "VC6 R4 env s0 user_value pressure_value"
  apply(simp only: VC6_def R4_def)
  by auto

theorem proof_4_7: "VC7 inv4 env  s0 user_value pressure_value"
  apply(simp only: VC7_def)
  by auto

theorem proof_4_8: "VC8 R4 env s0 user_value pressure_value"
  apply(simp only: VC8_def R4_def)
  apply auto
  subgoal for s1 s2
    apply(rule cut_rl[of "toEnvNum s2 s0 < DELAY'TIMEOUT"])
    using substate_refl apply fast
    by simp
  done

theorem proof_4_9: "VC9 R4 env s0 user_value pressure_value"
  apply(simp only: VC9_def R4_def)
  apply auto
  subgoal for s1 s2
    apply(rule cut_rl[of "toEnvNum s2 s0 < DELAY'TIMEOUT"])
    using substate_refl apply fast
    by simp
  done

theorem proof_4_10: "VC10 R4 env s0 user_value pressure_value"
  apply(simp only: VC10_def R4_def)
  apply auto
  subgoal for s1 s2
    apply(rule cut_rl[of "toEnvNum s2 s0 < DELAY'TIMEOUT"])
    using substate_refl apply fast
    by simp
  done

theorem proof_4_11: "VC11 inv4 env  s0 user_value pressure_value"
  apply(simp only: VC11_def)
  by auto

theorem proof_4_14: "VC14 R4 env s0 user_value pressure_value"
  apply(simp only: VC14_def R4_def)
  apply auto
  subgoal for s1 s2
    apply(rule cut_rl[of "toEnvNum s2 s0 < DELAY'TIMEOUT"])
    using substate_refl apply fast
    by simp
  done

end