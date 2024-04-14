theory Proof_4_13
  imports Proofs_4
begin

abbreviation s where "s s0 user_value pressure_value \<equiv>
  (toEnv
   (setPstate (setVarBool (setVarBool (setVarAny s0 user_value pressure_value) brake False) rotation True) ERROR
     Controller'rotating))"


theorem proof_4_13: "VC13 inv4 env s0 user_value pressure_value"
  apply(simp only: VC13_def inv4_def R4_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
   apply(rule conjI)
    apply simp
  apply((rule allI)+)
    apply(rule impI)
   apply(drule conjE)
    prefer 2
    apply assumption
   apply(drule conjE)
    prefer 2
    apply assumption
   apply(drule conjE)
    prefer 2
    apply assumption
   apply(drule conjE)
    prefer 2
    apply assumption
   apply(drule conjE)
    prefer 2
    apply assumption
  subgoal premises prems for s1 s2 s3
    using prems(1) prems(2) prems(3) prems(4) prems(5) prems(7)  apply (simp split: if_splits)
     apply(rule cut_rl[of "\<forall>s2 s3.
   toEnvP s2 \<and>
   toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s0 \<and> toEnvNum s2 s3 = ERROR \<and> toEnvNum s2 s0 < ltime s0 ERROR \<longrightarrow>
   \<not> (getVarBool s2 rotation = True \<and> getVarBool s3 pressure)"])
      using prems(1) prems(2) prems(3) prems(4) prems(5) prems(7)  apply (simp split: if_splits)
        apply(rule cut_rl[of "toEnvNum s1 s0 < DELAY'TIMEOUT"])
         apply(drule allE[of _ s1])
          prefer 2
          apply assumption
         apply(drule allE[of _ s2])
          prefer 2
      apply assumption
         apply auto[1]
      using toEnvNum3[of s1 s2 s0] apply auto[1]
       apply(rule suspended_not_rotation_and_pressure[of _ s0])
       apply(rule conjI)
      using prems(6) apply fast
       apply(rule conjI)
      using substate_refl apply fast
       apply(rule conjI)
        apply auto[1]
      using prems(6) apply fast
      apply(rule cut_rl[of "substate s3 s0"])
      using prems apply meson
      using prems(2)  by (simp split: if_splits)
      
      
      