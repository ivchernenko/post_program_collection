theory Proof_3_10
  imports Proofs_3
begin

thm extraInv_def
context
  fixes s2 s0:: state
fixes user_value pressure_value:: bool
assumes toEnvPs2:  "toEnvP s2 \<and> toEnvP s0" 
and vc: " env (setVarAny s0 user_value pressure_value) \<and>
        getPstate (setVarAny s0 user_value pressure_value) ERROR = Controller'rotating \<and>
\<not> getVarBool (setVarAny s0 user_value pressure_value) pressure \<and>
\<not> getVarBool (setVarAny s0 user_value pressure_value) user \<and>
\<not> DELAY'TIMEOUT \<le> ltime (setVarAny s0 user_value pressure_value) Controller"
and extraInvs0: "(\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 ERROR = Controller'motionless \<longrightarrow>
      (\<forall>s2. toEnvP s2 \<and> substate s2 s1 \<longrightarrow> getPstate s2 ERROR = Controller'motionless \<and> \<not> getVarBool s2 user) \<or>
      (\<exists>s2 s3.
          toEnvP s2 \<and>
          substate s2 s3 \<and>
          substate s3 s1 \<and>
          toEnvNum s2 s3 = ERROR \<and>
          getPstate s2 ERROR = Controller'rotating \<and>
          ltime s2 ERROR = DELAY'TIMEOUT \<and>
          \<not> getVarBool s3 user \<and>
          \<not> getVarBool s3 pressure \<and>
          (\<forall>s4 s5.
              toEnvP s4 \<and> toEnvP s5 \<and> substate s3 s4 \<and> substate s4 s5 \<and> substate s5 s1 \<and> toEnvNum s4 s5 = ERROR \<longrightarrow>
              getPstate s4 ERROR = Controller'motionless \<and> \<not> getVarBool s5 user))) \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 ERROR = Controller'rotating \<longrightarrow> ltime s1 ERROR \<le> DELAY'TIMEOUT) \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 ERROR = Controller'rotating \<longrightarrow>
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
(\<forall>s1 s2 s3.
    toEnvP s1 \<and>
    toEnvP s2 \<and>
    toEnvP s3 \<and>
    substate s1 s2 \<and>
    substate s2 s3 \<and>
    substate s3 s0 \<and>
    getPstate s3 ERROR = Controller'rotating \<and> toEnvNum s1 s2 = ERROR \<and> toEnvNum s1 s3 < ltime s3 ERROR \<longrightarrow>
    getPstate s1 ERROR = Controller'rotating \<and> \<not> getVarBool s2 user) \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 ERROR = Controller'rotating \<longrightarrow>
      (\<exists>s2 s3.
          toEnvP s2 \<and>
          toEnvP s3 \<and>
          substate s2 s3 \<and>
          substate s3 s1 \<and>
          toEnvNum s2 s3 = ERROR \<and>
          (getPstate s2 ERROR = Controller'motionless \<and> getVarBool s3 user \<or>
           getPstate s2 ERROR = Controller'suspended) \<and>
          \<not> getVarBool s3 pressure \<and>
          (\<forall>s4. toEnvP s4 \<and> substate s3 s4 \<and> substate s4 s1 \<longrightarrow> getPstate s4 ERROR = Controller'rotating))) \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 ERROR = Controller'suspended \<longrightarrow> ltime s1 ERROR = DELAY'TIMEOUT) \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 ERROR = Controller'suspended \<longrightarrow>
      (\<exists>s2 s3.
          toEnvP s2 \<and>
          toEnvP s3 \<and>
          substate s2 s3 \<and>
          substate s3 s1 \<and>
          toEnvNum s2 s3 = ERROR \<and>
          toEnvNum s2 s1 = ltime s1 ERROR \<and>
          (getPstate s2 ERROR \<noteq> Controller'motionless \<or> getVarBool s3 user) \<and> getVarBool s3 pressure)) \<and>
(\<forall>s1 s2 s3.
    toEnvP s1 \<and>
    toEnvP s2 \<and>
    toEnvP s3 \<and>
    substate s1 s2 \<and>
    substate s2 s3 \<and>
    substate s3 s0 \<and>
    toEnvNum s1 s2 = ERROR \<and> toEnvNum s1 s3 < ltime s3 ERROR \<and> getPstate s3 ERROR = Controller'suspended \<longrightarrow>
    getPstate s1 ERROR = Controller'suspended \<and> \<not> getVarBool s2 pressure) \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 ERROR = Controller'suspended \<longrightarrow>
      (\<exists>s2 s3.
          toEnvP s2 \<and>
          toEnvP s3 \<and>
          substate s2 s3 \<and>
          substate s3 s1 \<and>
          toEnvNum s2 s3 = ERROR \<and>
          (getPstate s2 ERROR = Controller'motionless \<and> getVarBool s3 user \<or>
           getPstate s2 ERROR = Controller'rotating) \<and>
          getVarBool s3 pressure \<and>
          (\<forall>s4. toEnvP s4 \<and> substate s3 s4 \<and> substate s4 s1 \<longrightarrow> getPstate s4 ERROR = Controller'suspended))) \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 ERROR = Controller'motionless \<longrightarrow>
      getVarBool s1 rotation = False \<and> getVarBool s1 brake = False) \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 ERROR = Controller'rotating \<longrightarrow>
      getVarBool s1 rotation = True \<and> getVarBool s1 brake = False) \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 ERROR = Controller'suspended \<longrightarrow>
      getVarBool s1 rotation = False \<and> getVarBool s1 brake = True) \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<longrightarrow>
      getPstate s1 ERROR = Controller'motionless \<or>
      getPstate s1 ERROR = Controller'rotating \<or> getPstate s1 ERROR = Controller'suspended)"
begin


lemma VC10_R3_ind_step_aux1: " toEnvP s2a \<Longrightarrow>
         substate s2 s2a \<and>
         substate s2a
         (toEnv (setVarAny s0 user'value pressure'value)) \<and>
         s2 \<noteq> s2a \<Longrightarrow>
         substate s1 s2 \<and>
         substate s2
          (toEnv (setVarAny s0 user'value pressure'value)) \<and>
         toEnvP s1 \<and>
         toEnvP s2 \<and>
         toEnvNum s1 s2 = ERROR \<and>
         DELAY'TIMEOUT =
         toEnvNum s2
          (toEnv (setVarAny s0 user'value pressure'value)) \<and>
         getVarBool s1 rotation = True \<and>
         \<not> getVarBool s2 user \<and>
         (\<forall>s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s2a \<and> s4 \<noteq> s2a \<longrightarrow>
               getVarBool s4 rotation = True \<and> \<not> getVarBool s4 user) \<longrightarrow>
         (\<exists>s4. toEnvP s4 \<and>
               substate s2a s4 \<and>
               substate s4
                (toEnv (setVarAny s0 user'value pressure'value)) \<and>
               toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
               (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
               (\<forall>s3. toEnvP s3 \<and> substate s2a s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
                     getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user)) \<Longrightarrow>
         substate s1 s2 \<and>
         substate s2
          (toEnv (setVarAny s0 user'value pressure'value)) \<and>
         toEnvP s1 \<and>
         toEnvP s2 \<and>
         toEnvNum s1 s2 = ERROR \<and>
         DELAY'TIMEOUT =
         toEnvNum s2
          (toEnv (setVarAny s0 user'value pressure'value)) \<and>
         getVarBool s1 rotation = True \<and>
         \<not> getVarBool s2 user \<and>
         (\<forall>s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 (predEnv s2a) \<and> s4 \<noteq> predEnv s2a \<longrightarrow>
               getVarBool s4 rotation = True \<and> \<not> getVarBool s4 user) \<Longrightarrow>
         \<not> (getVarBool (predEnv s2a) rotation = False \<or> getVarBool (predEnv s2a) user) \<Longrightarrow>
         toEnvP x \<and>
         substate s2a x \<and>
         substate x
          (toEnv (setVarAny s0 user'value pressure'value)) \<and>
         toEnvNum s2 x \<le> DELAY'TIMEOUT \<and>
         (getVarBool x rotation = False \<or> getVarBool x user) \<and>
         (\<forall>s3. toEnvP s3 \<and> substate s2a s3 \<and> substate s3 x \<and> s3 \<noteq> x \<longrightarrow>
               getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user) \<Longrightarrow>
         \<exists>s4. toEnvP s4 \<and>
              substate (predEnv s2a) s4 \<and>
              substate s4
               (toEnv (setVarAny s0 user'value pressure'value)) \<and>
              toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
              (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
              (\<forall>s3. toEnvP s3 \<and> substate (predEnv s2a) s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
                    getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user)"
  apply(rule exI[of _ x])
  by (smt (z3) predEnv_substate predEnv_substate_imp_eq_or_substate substate_trans)
  
lemma VC10_R3_ind_step: " toEnvP s2a \<Longrightarrow>
           substate s2 s2a \<and>
           substate s2a
            (toEnv (setVarAny s0 user'value pressure'value)) \<and>
           s2 \<noteq> s2a \<Longrightarrow>
           substate s1 s2 \<and>
           substate s2
           (toEnv (setVarAny s0 user'value pressure'value)) \<and>
           toEnvP s1 \<and>
           toEnvP s2 \<and>
           toEnvNum s1 s2 = ERROR \<and>
           DELAY'TIMEOUT =
           toEnvNum s2
            (toEnv (setVarAny s0 user'value pressure'value)) \<and>
           getVarBool s1 rotation = True \<and>
           \<not> getVarBool s2 user \<and>
           (\<forall>s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s2a \<and> s4 \<noteq> s2a \<longrightarrow>
                 getVarBool s4 rotation = True \<and> \<not> getVarBool s4 user) \<longrightarrow>
           (\<exists>s4. toEnvP s4 \<and>
                 substate s2a s4 \<and>
                 substate s4
                 (toEnv (setVarAny s0 user'value pressure'value)) \<and>
                 toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
                 (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
                 (\<forall>s3. toEnvP s3 \<and> substate s2a s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
                       getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user)) \<Longrightarrow>
           substate s1 s2 \<and>
           substate s2
            (toEnv (setVarAny s0 user'value pressure'value)) \<and>
           toEnvP s1 \<and>
           toEnvP s2 \<and>
           toEnvNum s1 s2 = ERROR \<and>
           DELAY'TIMEOUT =
           toEnvNum s2
            (toEnv (setVarAny s0 user'value pressure'value)) \<and>
           getVarBool s1 rotation = True \<and>
           \<not> getVarBool s2 user \<and>
           (\<forall>s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 (predEnv s2a) \<and> s4 \<noteq> predEnv s2a \<longrightarrow>
                 getVarBool s4 rotation = True \<and> \<not> getVarBool s4 user) \<longrightarrow>
           (\<exists>s4. toEnvP s4 \<and>
                 substate (predEnv s2a) s4 \<and>
                 substate s4
                  (toEnv (setVarAny s0 user'value pressure'value)) \<and>
                 toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
                 (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
                 (\<forall>s3. toEnvP s3 \<and> substate (predEnv s2a) s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
                       getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user))"
  apply(rule impI)
  apply(cases "(getVarBool (predEnv s2a) rotation = False \<or> getVarBool (predEnv s2a) user)")
   apply(rule exI[of _ "predEnv s2a"])
   apply(rule conjI)
    apply(rule toEnvP_substate_pred_imp_toEnvP_pred[of s2])
  using toEnvPs2 substate_eq_or_predEnv apply fast
   apply(rule conjI)
  using substate_refl apply fast
   apply(rule conjI)
  using predEnv_substate substate_trans apply fast
   apply(rule conjI)
    apply(rule cut_rl[of "substate s2 (predEnv s2a) \<and>
 substate (predEnv s2a)
 (toEnv (setVarAny s0 user'value pressure'value))"])
  using toEnvNum3[of s2 "predEnv s2a" 
"(toEnv (setVarAny s0 user'value pressure'value))"]
     apply arith
  using substate_eq_or_predEnv predEnv_substate substate_trans apply fast
   apply(rule conjI)
    apply assumption
  using substate_asym apply fast
  apply(rule exE[of "\<lambda> s4. toEnvP s4 \<and>
          substate s2a s4 \<and>
          substate s4
          (toEnv (setVarAny s0 user'value pressure'value)) \<and>
          toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
          (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
          (\<forall>s3. toEnvP s3 \<and> substate s2a s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
                getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user)"])
  using substate_eq_or_predEnv apply blast
  by ((rule VC10_R3_ind_step_aux1);blast)

lemma VC10_R3_ind_base: "substate s1 s2 \<and>
       substate s2 (toEnv (setVarAny s0 user'value pressure'value)) \<and>
       toEnvP s1 \<and>
       toEnvP s2 \<and>
       toEnvNum s1 s2 = ERROR \<and>
       DELAY'TIMEOUT = toEnvNum s2 (toEnv (setVarAny s0 user'value pressure'value)) \<and>
       getVarBool s1 rotation = True \<and>
       \<not> getVarBool s2 user \<and>
       (\<forall>s4. toEnvP s4 \<and>
             substate s2 s4 \<and>
             substate s4 (toEnv (setVarAny s0 user'value pressure'value)) \<and>
             s4 \<noteq> toEnv (setVarAny s0 user'value pressure'value) \<longrightarrow>
             getVarBool s4 rotation = True \<and> \<not> getVarBool s4 user) \<Longrightarrow>
       toEnvP s2a \<and>
toEnvP s3 \<and>
       substate s2a s3 \<and>
       substate s3 s0 \<and>
       toEnvNum s2a s0 \<le> ltime s0 ERROR \<and>
       toEnvNum s2a s3 = ERROR \<and> (getVarBool s2a rotation = False \<or> getVarBool s3 user) \<Longrightarrow>
       \<exists>s4. toEnvP s4 \<and>
            substate (toEnv (setVarAny s0 user'value pressure'value)) s4 \<and>
            substate s4 (toEnv (setVarAny s0 user'value pressure'value)) \<and>
            toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
            (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
            (\<forall>s3. toEnvP s3 \<and>
                  substate (toEnv (setVarAny s0 user'value pressure'value)) s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
                  getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user)"
  apply(rule cut_rl[of "substate s2 s2a"])
 apply(drule conjE[of _ _ "\<exists>s4. toEnvP s4 \<and>
         substate (toEnv (setVarAny s0 user'value pressure'value)) s4 \<and>
         substate s4 (toEnv (setVarAny s0 user'value pressure'value)) \<and>
         toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
         (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
         (\<forall>s3. toEnvP s3 \<and> substate (toEnv (setVarAny s0 user'value pressure'value)) s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
               getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user)"])
    apply(drule conjE[of _ _ "\<exists>s4. toEnvP s4 \<and>
         substate (toEnv (setVarAny s0 user'value pressure'value)) s4 \<and>
         substate s4 (toEnv (setVarAny s0 user'value pressure'value)) \<and>
         toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
         (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
         (\<forall>s3. toEnvP s3 \<and> substate (toEnv (setVarAny s0 user'value pressure'value)) s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
               getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user)"])
  apply(drule conjE[of _ _ "\<exists>s4. toEnvP s4 \<and>
         substate (toEnv (setVarAny s0 user'value pressure'value)) s4 \<and>
         substate s4 (toEnv (setVarAny s0 user'value pressure'value)) \<and>
         toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
         (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
         (\<forall>s3. toEnvP s3 \<and> substate (toEnv (setVarAny s0 user'value pressure'value)) s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
               getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user)"])
  apply(drule conjE[of _ _ "\<exists>s4. toEnvP s4 \<and>
         substate (toEnv (setVarAny s0 user'value pressure'value)) s4 \<and>
         substate s4 (toEnv (setVarAny s0 user'value pressure'value)) \<and>
         toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
         (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
         (\<forall>s3. toEnvP s3 \<and> substate (toEnv (setVarAny s0 user'value pressure'value)) s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
               getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user)"])
  apply(drule conjE[of _ _ "\<exists>s4. toEnvP s4 \<and>
         substate (toEnv (setVarAny s0 user'value pressure'value)) s4 \<and>
         substate s4 (toEnv (setVarAny s0 user'value pressure'value)) \<and>
         toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
         (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
         (\<forall>s3. toEnvP s3 \<and> substate (toEnv (setVarAny s0 user'value pressure'value)) s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
               getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user)"])
  apply(drule conjE[of _ _ "\<exists>s4. toEnvP s4 \<and>
         substate (toEnv (setVarAny s0 user'value pressure'value)) s4 \<and>
         substate s4 (toEnv (setVarAny s0 user'value pressure'value)) \<and>
         toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
         (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
         (\<forall>s3. toEnvP s3 \<and> substate (toEnv (setVarAny s0 user'value pressure'value)) s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
               getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user)"])
  apply(drule conjE[of _ _ "\<exists>s4. toEnvP s4 \<and>
         substate (toEnv (setVarAny s0 user'value pressure'value)) s4 \<and>
         substate s4 (toEnv (setVarAny s0 user'value pressure'value)) \<and>
         toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
         (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
         (\<forall>s3. toEnvP s3 \<and> substate (toEnv (setVarAny s0 user'value pressure'value)) s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
               getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user)"])
  apply(drule conjE[of _ _ "\<exists>s4. toEnvP s4 \<and>
         substate (toEnv (setVarAny s0 user'value pressure'value)) s4 \<and>
         substate s4 (toEnv (setVarAny s0 user'value pressure'value)) \<and>
         toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
         (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
         (\<forall>s3. toEnvP s3 \<and> substate (toEnv (setVarAny s0 user'value pressure'value)) s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
               getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user)"])
  apply(drule conjE[of _ _ "\<exists>s4. toEnvP s4 \<and>
         substate (toEnv (setVarAny s0 user'value pressure'value)) s4 \<and>
         substate s4 (toEnv (setVarAny s0 user'value pressure'value)) \<and>
         toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
         (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
         (\<forall>s3. toEnvP s3 \<and> substate (toEnv (setVarAny s0 user'value pressure'value)) s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
               getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user)"])
  apply(drule conjE[of _ _ "\<exists>s4. toEnvP s4 \<and>
         substate (toEnv (setVarAny s0 user'value pressure'value)) s4 \<and>
         substate s4 (toEnv (setVarAny s0 user'value pressure'value)) \<and>
         toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
         (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
         (\<forall>s3. toEnvP s3 \<and> substate (toEnv (setVarAny s0 user'value pressure'value)) s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
               getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user)"])
  apply(drule conjE[of _ _ "\<exists>s4. toEnvP s4 \<and>
         substate (toEnv (setVarAny s0 user'value pressure'value)) s4 \<and>
         substate s4 (toEnv (setVarAny s0 user'value pressure'value)) \<and>
         toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
         (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
         (\<forall>s3. toEnvP s3 \<and> substate (toEnv (setVarAny s0 user'value pressure'value)) s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
               getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user)"])
  apply(drule conjE[of _ _ "\<exists>s4. toEnvP s4 \<and>
         substate (toEnv (setVarAny s0 user'value pressure'value)) s4 \<and>
         substate s4 (toEnv (setVarAny s0 user'value pressure'value)) \<and>
         toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
         (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
         (\<forall>s3. toEnvP s3 \<and> substate (toEnv (setVarAny s0 user'value pressure'value)) s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
               getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user)"])
  apply(drule conjE[of _ _ "\<exists>s4. toEnvP s4 \<and>
         substate (toEnv (setVarAny s0 user'value pressure'value)) s4 \<and>
         substate s4 (toEnv (setVarAny s0 user'value pressure'value)) \<and>
         toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
         (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
         (\<forall>s3. toEnvP s3 \<and> substate (toEnv (setVarAny s0 user'value pressure'value)) s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
               getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user)"])
apply(drule conjE[of _ _ "\<exists>s4. toEnvP s4 \<and>
         substate (toEnv (setVarAny s0 user'value pressure'value)) s4 \<and>
         substate s4 (toEnv (setVarAny s0 user'value pressure'value)) \<and>
         toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
         (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
         (\<forall>s3. toEnvP s3 \<and> substate (toEnv (setVarAny s0 user'value pressure'value)) s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
               getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user)"])
               apply(cases "getVarBool s2a rotation = False")
   apply(drule allE[of _ s2a "\<exists>s4. toEnvP s4 \<and>
         substate (toEnv (setVarAny s0 user'value pressure'value)) s4 \<and>
         substate s4 (toEnv (setVarAny s0 user'value pressure'value)) \<and>
         toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
         (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
         (\<forall>s3. toEnvP s3 \<and> substate (toEnv (setVarAny s0 user'value pressure'value)) s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
               getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user)"])
  using substate_trans substate_asym
                  apply (metis less_one not_one_less_zero substate.simps(2) substate.simps(9) toEnvNum_id)
                 apply assumption
  apply(drule allE[of _ s3 "\<exists>s4. toEnvP s4 \<and>
         substate (toEnv (setVarAny s0 user'value pressure'value)) s4 \<and>
         substate s4 (toEnv (setVarAny s0 user'value pressure'value)) \<and>
         toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
         (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
         (\<forall>s3. toEnvP s3 \<and> substate (toEnv (setVarAny s0 user'value pressure'value)) s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
               getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user)"])
                  apply(rule cut_rl[of "getVarBool s3 user"])
  apply(drule impE[of _ _ "\<exists>s4. toEnvP s4 \<and>
         substate (toEnv (setVarAny s0 user'value pressure'value)) s4 \<and>
         substate s4 (toEnv (setVarAny s0 user'value pressure'value)) \<and>
         toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
         (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
         (\<forall>s3. toEnvP s3 \<and> substate (toEnv (setVarAny s0 user'value pressure'value)) s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
               getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user)"])
                     apply(rule conjI)
  apply assumption
                     apply(rule conjI)
  using substate_trans apply fast
                     apply(rule conjI)
                      apply auto
    apply(simp split: if_splits)
  using substate_refl  substate_asym[of s0 "(toEnv (setVarAny s0 user'value pressure'value))"] apply auto
   apply(simp split: if_splits)
  apply(rule cut_rl[of "substate s2 s0 \<and> substate s2a s0 "])
  apply(rule cut_rl[of "substate s2 s2a \<or> substate s2a s2"])
    apply(drule disjE[of _ _ "substate s2 s2a"])
      apply assumption
      apply(rule cut_rl[of "toEnvNum s2 s0 < toEnvNum s2a s0"])
       apply(rule cut_rl[of "toEnvNum s2 s0 \<ge> toEnvNum s2a s0"])
  apply simp
  using vc apply simp
      apply (metis linorder_le_less_linear shift_toEnvNum substate_asym substate_shift toEnvPs2)
     apply assumption
  using substate_total apply fast
  using substate_trans apply fast
apply(simp split: if_splits)
  apply(rule cut_rl[of "substate s2 s0 \<and> substate s2a s0 "])
  apply(rule cut_rl[of "substate s2 s2a \<or> substate s2a s2 \<and> s2 \<noteq> s2a"])
    apply(drule disjE[of _ _ "substate s2 s2a"])
      apply assumption
      apply(rule cut_rl[of "toEnvNum s2 s0 < toEnvNum s2a s0"])
      apply(rule cut_rl[of "toEnvNum s2 s0 \<ge> toEnvNum s2a s0"])
       apply simp
  using vc apply simp
     apply (metis linorder_le_less_linear shift_toEnvNum substate_asym substate_shift toEnvPs2)
  apply assumption
  using substate_total apply fast
  using substate_trans by fast
  
lemma VC10_R3_ind_proof:   "toEnvP s5 \<and>  substate s2 s5 \<and>
 substate s5 (toEnv (setVarAny s0 user'value pressure'value))
 \<longrightarrow> pred3 s1 s2 (toEnv (setVarAny s0 user'value pressure'value))
 s5"
  apply(induction rule: state_down_ind)
  using toEnvPs2 apply simp
   apply(simp only: pred3_def)
   apply(rule impI)
  apply(rule cut_rl[of "\<exists>s2 s3.
   toEnvP s2 \<and>
toEnvP s3 \<and>
   substate s2 s3 \<and>
   substate s3 s0 \<and>
   toEnvNum s2 s0 \<le> ltime s0 ERROR \<and>
   toEnvNum s2 s3 = ERROR \<and> (getVarBool s2 rotation = False \<or> getVarBool s3 user)"])
    apply(drule exE[of _ " \<exists>s4. toEnvP s4 \<and>
         substate (toEnv (setVarAny s0 user'value pressure'value)) s4 \<and>
         substate s4 (toEnv (setVarAny s0 user'value pressure'value)) \<and>
         toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
         (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
         (\<forall>s3. toEnvP s3 \<and> substate (toEnv (setVarAny s0 user'value pressure'value)) s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
               getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user)"])
   apply(drule exE[of _ " \<exists>s4. toEnvP s4 \<and>
         substate (toEnv (setVarAny s0 user'value pressure'value)) s4 \<and>
         substate s4 (toEnv (setVarAny s0 user'value pressure'value)) \<and>
         toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
         (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
         (\<forall>s3. toEnvP s3 \<and> substate (toEnv (setVarAny s0 user'value pressure'value)) s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
               getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user)"])
      apply((rule VC10_R3_ind_base);blast)
     apply assumption
    apply assumption
   apply(rule rotating_not_vc3[of s0 s0])
   apply(rule conjI)
  using toEnvPs2 apply fast
   apply(rule conjI)
  using substate_refl apply fast
   apply(rule conjI)
  using vc apply simp
 using  extraInvs0  apply fast
apply(simp only: pred3_def)
  by ((rule VC10_R3_ind_step);fast) 

end

lemma VC10_R3_aux1: "DELAY'TIMEOUT < toEnvNum s2 (toEnv (setVarAny s0 user_value pressure_value)) \<Longrightarrow> 
 substate s2 (toEnv (setVarAny s0 user_value pressure_value)) \<Longrightarrow>  substate s2 s0 \<and> DELAY'TIMEOUT \<le> toEnvNum s2 s0"
  by (simp split: if_splits)


lemma VC10_R3_aux2: " \<not> DELAY'TIMEOUT \<le> ltime (setVarAny s0 user_value pressure_value) ERROR \<Longrightarrow>
    substate s1 s2 \<Longrightarrow>
    \<not> getVarBool (setVarAny s0 user_value pressure_value) user \<Longrightarrow>
    substate s2 (toEnv (setVarAny s0 user_value pressure_value)) \<Longrightarrow>
    \<not> getVarBool (setVarAny s0 user_value pressure_value) pressure \<Longrightarrow>
    toEnvP s1 \<Longrightarrow>
    getPstate (setVarAny s0 user_value pressure_value) ERROR = Controller'rotating \<Longrightarrow>
    toEnvP s2 \<Longrightarrow>
    env (setVarAny s0 user_value pressure_value) \<Longrightarrow>
    toEnvNum s1 s2 = ERROR \<Longrightarrow>
    DELAY'TIMEOUT \<le> toEnvNum s2 (toEnv (setVarAny s0 user_value pressure_value)) \<Longrightarrow>
    getVarBool s1 rotation = True \<and> \<not> getVarBool s2 user \<Longrightarrow>
    toEnvP s0 \<Longrightarrow>
    \<forall>s1 s2.
       substate s1 s2 \<and>
       substate s2 s0 \<and>
       toEnvP s1 \<and>
       toEnvP s2 \<and>
       toEnvNum s1 s2 = ERROR \<and>
       DELAY'TIMEOUT \<le> toEnvNum s2 s0 \<and> getVarBool s1 rotation = True \<and> \<not> getVarBool s2 user \<longrightarrow>
       (\<exists>s4. toEnvP s4 \<and>
             substate s2 s4 \<and>
             substate s4 s0 \<and>
             toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
             (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
             (\<forall>s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
                   getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user)) \<Longrightarrow>
    DELAY'TIMEOUT = toEnvNum s2 (toEnv (setVarAny s0 user_value pressure_value)) \<Longrightarrow>
    pred3 s1 s2 (toEnv (setVarAny s0 user_value pressure_value)) s2 \<Longrightarrow>
    \<exists>s4. toEnvP s4 \<and>
         substate s2 s4 \<and>
         substate s4 (toEnv (setVarAny s0 user_value pressure_value)) \<and>
         toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
         (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
         (\<forall>s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
               getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user)"
apply(simp only: pred3_def)
  using substate_asym
  by meson 

lemma VC10_R3: "  ((((((toEnvP s0 \<and>
             (\<forall>s1 s2.
                 substate s1 s2 \<and>
                 substate s2 s0 \<and>
                 toEnvP s1 \<and>
                 toEnvP s2 \<and>
                 toEnvNum s1 s2 = ERROR \<and>
                 DELAY'TIMEOUT \<le> toEnvNum s2 s0 \<and> getVarBool s1 rotation = True \<and> \<not> getVarBool s2 user \<longrightarrow>
                 (\<exists>s4. toEnvP s4 \<and>
                       substate s2 s4 \<and>
                       substate s4 s0 \<and>
                       toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
                       (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
                       (\<forall>s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
                             getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user)))) \<and>
            (\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 ERROR = Controller'motionless \<longrightarrow>
                  (\<forall>s2. toEnvP s2 \<and> substate s2 s1 \<longrightarrow>
                        getPstate s2 ERROR = Controller'motionless \<and> \<not> getVarBool s2 user) \<or>
                  (\<exists>s2 s3.
                      toEnvP s2 \<and>
                      substate s2 s3 \<and>
                      substate s3 s1 \<and>
                      toEnvNum s2 s3 = ERROR \<and>
                      getPstate s2 ERROR = Controller'rotating \<and>
                      ltime s2 ERROR = DELAY'TIMEOUT \<and>
                      \<not> getVarBool s3 user \<and>
                      \<not> getVarBool s3 pressure \<and>
                      (\<forall>s4 s5.
                          toEnvP s4 \<and>
                          toEnvP s5 \<and> substate s3 s4 \<and> substate s4 s5 \<and> substate s5 s1 \<and> toEnvNum s4 s5 = ERROR \<longrightarrow>
                          getPstate s4 ERROR = Controller'motionless \<and> \<not> getVarBool s5 user))) \<and>
            (\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 ERROR = Controller'rotating \<longrightarrow>
                  ltime s1 ERROR \<le> DELAY'TIMEOUT) \<and>
            (\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 ERROR = Controller'rotating \<longrightarrow>
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
            (\<forall>s1 s2 s3.
                toEnvP s1 \<and>
                toEnvP s2 \<and>
                toEnvP s3 \<and>
                substate s1 s2 \<and>
                substate s2 s3 \<and>
                substate s3 s0 \<and>
                getPstate s3 ERROR = Controller'rotating \<and> toEnvNum s1 s2 = ERROR \<and> toEnvNum s1 s3 < ltime s3 ERROR \<longrightarrow>
                getPstate s1 ERROR = Controller'rotating \<and> \<not> getVarBool s2 user) \<and>
            (\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 ERROR = Controller'rotating \<longrightarrow>
                  (\<exists>s2 s3.
                      toEnvP s2 \<and>
                      toEnvP s3 \<and>
                      substate s2 s3 \<and>
                      substate s3 s1 \<and>
                      toEnvNum s2 s3 = ERROR \<and>
                      (getPstate s2 ERROR = Controller'motionless \<and> getVarBool s3 user \<or>
                       getPstate s2 ERROR = Controller'suspended) \<and>
                      \<not> getVarBool s3 pressure \<and>
                      (\<forall>s4. toEnvP s4 \<and> substate s3 s4 \<and> substate s4 s1 \<longrightarrow>
                            getPstate s4 ERROR = Controller'rotating))) \<and>
            (\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 ERROR = Controller'suspended \<longrightarrow>
                  ltime s1 ERROR = DELAY'TIMEOUT) \<and>
            (\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 ERROR = Controller'suspended \<longrightarrow>
                  (\<exists>s2 s3.
                      toEnvP s2 \<and>
                      toEnvP s3 \<and>
                      substate s2 s3 \<and>
                      substate s3 s1 \<and>
                      toEnvNum s2 s3 = ERROR \<and>
                      toEnvNum s2 s1 = ltime s1 ERROR \<and>
                      (getPstate s2 ERROR \<noteq> Controller'motionless \<or> getVarBool s3 user) \<and> getVarBool s3 pressure)) \<and>
            (\<forall>s1 s2 s3.
                toEnvP s1 \<and>
                toEnvP s2 \<and>
                toEnvP s3 \<and>
                substate s1 s2 \<and>
                substate s2 s3 \<and>
                substate s3 s0 \<and>
                toEnvNum s1 s2 = ERROR \<and>
                toEnvNum s1 s3 < ltime s3 ERROR \<and> getPstate s3 ERROR = Controller'suspended \<longrightarrow>
                getPstate s1 ERROR = Controller'suspended \<and> \<not> getVarBool s2 pressure) \<and>
            (\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 ERROR = Controller'suspended \<longrightarrow>
                  (\<exists>s2 s3.
                      toEnvP s2 \<and>
                      toEnvP s3 \<and>
                      substate s2 s3 \<and>
                      substate s3 s1 \<and>
                      toEnvNum s2 s3 = ERROR \<and>
                      (getPstate s2 ERROR = Controller'motionless \<and> getVarBool s3 user \<or>
                       getPstate s2 ERROR = Controller'rotating) \<and>
                      getVarBool s3 pressure \<and>
                      (\<forall>s4. toEnvP s4 \<and> substate s3 s4 \<and> substate s4 s1 \<longrightarrow>
                            getPstate s4 ERROR = Controller'suspended))) \<and>
            (\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 ERROR = Controller'motionless \<longrightarrow>
                  getVarBool s1 rotation = False \<and> getVarBool s1 brake = False) \<and>
            (\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 ERROR = Controller'rotating \<longrightarrow>
                  getVarBool s1 rotation = True \<and> getVarBool s1 brake = False) \<and>
            (\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 ERROR = Controller'suspended \<longrightarrow>
                  getVarBool s1 rotation = False \<and> getVarBool s1 brake = True) \<and>
            (\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<longrightarrow>
                  getPstate s1 ERROR = Controller'motionless \<or>
                  getPstate s1 ERROR = Controller'rotating \<or> getPstate s1 ERROR = Controller'suspended)) \<and>
           env (setVarAny s0 user_value pressure_value)) \<and>
          getPstate (setVarAny s0 user_value pressure_value) ERROR = Controller'rotating) \<and>
         \<not> getVarBool (setVarAny s0 user_value pressure_value) pressure) \<and>
        \<not> getVarBool (setVarAny s0 user_value pressure_value) user) \<and>
       \<not> DELAY'TIMEOUT \<le> ltime (setVarAny s0 user_value pressure_value) ERROR \<Longrightarrow>
       substate s1 s2 \<and>
       substate s2 (toEnv (setVarAny s0 user_value pressure_value)) \<and>
       toEnvP s1 \<and>
       toEnvP s2 \<and>
       toEnvNum s1 s2 = ERROR \<and>
       DELAY'TIMEOUT \<le> toEnvNum s2 (toEnv (setVarAny s0 user_value pressure_value)) \<and>
       getVarBool s1 rotation = True \<and> \<not> getVarBool s2 user \<longrightarrow>
       (\<exists>s4. toEnvP s4 \<and>
             substate s2 s4 \<and>
             substate s4 (toEnv (setVarAny s0 user_value pressure_value)) \<and>
             toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
             (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
             (\<forall>s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
                   getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user))"
  
  apply(rule impI)
  apply(drule conjE[of _ _ "  \<exists>s4. toEnvP s4 \<and>
         substate s2 s4 \<and>
         substate s4 (toEnv (setVarAny s0 user_value pressure_value)) \<and>
         toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
         (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
         (\<forall>s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
               getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user)"])
 apply(drule conjE[of _ _ "  \<exists>s4. toEnvP s4 \<and>
         substate s2 s4 \<and>
         substate s4 (toEnv (setVarAny s0 user_value pressure_value)) \<and>
         toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
         (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
         (\<forall>s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
               getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user)"])
 apply(drule conjE[of _ _ "  \<exists>s4. toEnvP s4 \<and>
         substate s2 s4 \<and>
         substate s4 (toEnv (setVarAny s0 user_value pressure_value)) \<and>
         toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
         (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
         (\<forall>s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
               getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user)"])
 apply(drule conjE[of _ _ "  \<exists>s4. toEnvP s4 \<and>
         substate s2 s4 \<and>
         substate s4 (toEnv (setVarAny s0 user_value pressure_value)) \<and>
         toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
         (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
         (\<forall>s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
               getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user)"])
 apply(drule conjE[of _ _ " \<exists>s4. toEnvP s4 \<and>
         substate s2 s4 \<and>
         substate s4 (toEnv (setVarAny s0 user_value pressure_value)) \<and>
         toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
         (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
         (\<forall>s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
               getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user)"])
 apply(drule conjE[of _ _ " \<exists>s4. toEnvP s4 \<and>
         substate s2 s4 \<and>
         substate s4 (toEnv (setVarAny s0 user_value pressure_value)) \<and>
         toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
         (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
         (\<forall>s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
               getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user)"])
 apply(drule conjE[of _ _ "  \<exists>s4. toEnvP s4 \<and>
         substate s2 s4 \<and>
         substate s4 (toEnv (setVarAny s0 user_value pressure_value)) \<and>
         toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
         (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
         (\<forall>s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
               getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user)"])
 apply(drule conjE[of _ _ "  \<exists>s4. toEnvP s4 \<and>
         substate s2 s4 \<and>
         substate s4 (toEnv (setVarAny s0 user_value pressure_value)) \<and>
         toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
         (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
         (\<forall>s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
               getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user)"])
 apply(drule conjE[of _ _ "  \<exists>s4. toEnvP s4 \<and>
         substate s2 s4 \<and>
         substate s4 (toEnv (setVarAny s0 user_value pressure_value)) \<and>
         toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
         (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
         (\<forall>s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
               getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user)"])
 apply(drule conjE[of _ _ "  \<exists>s4. toEnvP s4 \<and>
         substate s2 s4 \<and>
         substate s4 (toEnv (setVarAny s0 user_value pressure_value)) \<and>
         toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
         (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
         (\<forall>s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
               getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user)"])
 apply(drule conjE[of _ _ "  \<exists>s4. toEnvP s4 \<and>
         substate s2 s4 \<and>
         substate s4 (toEnv (setVarAny s0 user_value pressure_value)) \<and>
         toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
         (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
         (\<forall>s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
               getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user)"])
 apply(drule conjE[of _ _ " \<exists>s4. toEnvP s4 \<and>
         substate s2 s4 \<and>
         substate s4 (toEnv (setVarAny s0 user_value pressure_value)) \<and>
         toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
         (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
         (\<forall>s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
               getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user)"])
                 apply(drule conjE[of _ _ "  \<exists>s4. toEnvP s4 \<and>
         substate s2 s4 \<and>
         substate s4 (toEnv (setVarAny s0 user_value pressure_value)) \<and>
         toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
         (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
         (\<forall>s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
               getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user)"])
  apply(rule disjE[of "DELAY'TIMEOUT < toEnvNum s2 (toEnv (setVarAny s0 user_value pressure_value))"
"DELAY'TIMEOUT = toEnvNum s2 (toEnv (setVarAny s0 user_value pressure_value))"])
  using le_imp_less_or_eq
    apply linarith 
                apply(rule cut_rl[of "substate s2 s0 \<and> toEnvNum s2 s0 \<ge> DELAY'TIMEOUT"])
  apply(rule cut_rl[of "(\<exists>s4. toEnvP s4 \<and>
                   substate s2 s4 \<and>
                   substate s4 s0 \<and>
                   toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
                   (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
                   (\<forall>s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
                         getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user))"])
                   apply (metis substate.simps(10) substate.simps(2) substate.simps(3) substate.simps(9))
                    apply(drule allE[of _ s1 " \<exists>s4. toEnvP s4 \<and>
         substate s2 s4 \<and>
         substate s4 s0 \<and>
         toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
         (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
         (\<forall>s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
               getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user)"])
apply(drule allE[of _ s2 " \<exists>s4. toEnvP s4 \<and>
         substate s2 s4 \<and>
         substate s4 s0 \<and>
         toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
         (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
         (\<forall>s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
               getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user)"])
                   apply fast
                  apply assumption
                 apply assumption
                apply((rule VC10_R3_aux1);assumption)
  apply(rule cut_rl[of "pred3 s1 s2 
 (toEnv (setVarAny s0 user_value pressure_value))
s2"])
  apply((rule VC10_R3_aux2);assumption)
   apply(rule mp[of "toEnvP s2 \<and>  substate s2 s2 \<and>
 substate s2 (toEnv (setVarAny s0 user_value pressure_value))"])
 
  print_state
                apply((rule VC10_R3_ind_proof);fast)
  print_state
  using substate_refl apply fast
              apply assumption
             apply assumption
            apply assumption
           apply assumption
          apply assumption
         apply assumption
        apply assumption
       apply assumption
      apply assumption
     apply assumption
    apply assumption
   apply assumption
  by assumption

theorem proof_3_10: "VC10 inv3 env s0 user_value pressure_value"
  apply(simp only: VC10_def inv3_def R3_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  apply(rule conjI)
   apply(simp)
   apply((rule allI);(rule allI))
   apply(rule VC10_R3)
   apply assumption
  