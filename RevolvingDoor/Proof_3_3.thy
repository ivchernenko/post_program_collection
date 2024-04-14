theory Proof_3_3
  imports Proofs_3
begin

context
  fixes s2 s0:: state
fixes user_value pressure_value:: bool
assumes toEnvPs2:  "toEnvP s2 \<and> toEnvP s0" and extraInvs0: "extraInv s0" 
and vc: " env (setVarAny s0 user_value pressure_value) \<and>
         getPstate (setVarAny s0 user_value pressure_value) ERROR = Controller'motionless \<and>
        getVarBool (setVarAny s0 user_value pressure_value) user"
begin

lemma VC2_R3_ind_step_aux1: " toEnvP s2a \<Longrightarrow>
         substate s2 s2a \<and>
         substate s2a
           (toEnv (setPstate (setVarBool (setVarAny s0 user'value pressure'value) rotation True) ERROR Controller'rotating)) \<and>
         s2 \<noteq> s2a \<Longrightarrow>
         substate s1 s2 \<and>
         substate s2
           (toEnv (setPstate (setVarBool (setVarAny s0 user'value pressure'value) rotation True) ERROR Controller'rotating)) \<and>
         toEnvP s1 \<and>
         toEnvP s2 \<and>
         toEnvNum s1 s2 = ERROR \<and>
         DELAY'TIMEOUT =
         toEnvNum s2
           (toEnv (setPstate (setVarBool (setVarAny s0 user'value pressure'value) rotation True) ERROR Controller'rotating)) \<and>
         getVarBool s1 rotation = True \<and>
         \<not> getVarBool s2 user \<and>
         (\<forall>s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s2a \<and> s4 \<noteq> s2a \<longrightarrow>
               getVarBool s4 rotation = True \<and> \<not> getVarBool s4 user) \<longrightarrow>
         (\<exists>s4. toEnvP s4 \<and>
               substate s2a s4 \<and>
               substate s4
                 (toEnv (setPstate (setVarBool (setVarAny s0 user'value pressure'value) rotation True) ERROR Controller'rotating)) \<and>
               toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
               (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
               (\<forall>s3. toEnvP s3 \<and> substate s2a s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
                     getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user)) \<Longrightarrow>
         substate s1 s2 \<and>
         substate s2
          (toEnv (setPstate (setVarBool (setVarAny s0 user'value pressure'value) rotation True) ERROR Controller'rotating)) \<and>
         toEnvP s1 \<and>
         toEnvP s2 \<and>
         toEnvNum s1 s2 = ERROR \<and>
         DELAY'TIMEOUT =
         toEnvNum s2
           (toEnv (setPstate (setVarBool (setVarAny s0 user'value pressure'value) rotation True) ERROR Controller'rotating)) \<and>
         getVarBool s1 rotation = True \<and>
         \<not> getVarBool s2 user \<and>
         (\<forall>s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 (predEnv s2a) \<and> s4 \<noteq> predEnv s2a \<longrightarrow>
               getVarBool s4 rotation = True \<and> \<not> getVarBool s4 user) \<Longrightarrow>
         \<not> (getVarBool (predEnv s2a) rotation = False \<or> getVarBool (predEnv s2a) user) \<Longrightarrow>
         toEnvP x \<and>
         substate s2a x \<and>
         substate x
           (toEnv (setPstate (setVarBool (setVarAny s0 user'value pressure'value) rotation True) ERROR Controller'rotating)) \<and>
         toEnvNum s2 x \<le> DELAY'TIMEOUT \<and>
         (getVarBool x rotation = False \<or> getVarBool x user) \<and>
         (\<forall>s3. toEnvP s3 \<and> substate s2a s3 \<and> substate s3 x \<and> s3 \<noteq> x \<longrightarrow>
               getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user) \<Longrightarrow>
         \<exists>s4. toEnvP s4 \<and>
              substate (predEnv s2a) s4 \<and>
              substate s4
                (toEnv (setPstate (setVarBool (setVarAny s0 user'value pressure'value) rotation True) ERROR Controller'rotating)) \<and>
              toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
              (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
              (\<forall>s3. toEnvP s3 \<and> substate (predEnv s2a) s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
                    getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user)"
  apply(rule exI[of _ x])
  by (smt (z3) predEnv_substate predEnv_substate_imp_eq_or_substate substate_trans)
  
lemma VC2_R3_ind_step: " toEnvP s2a \<Longrightarrow>
           substate s2 s2a \<and>
           substate s2a
             (toEnv (setPstate (setVarBool (setVarAny s0 user'value pressure'value) rotation True) ERROR Controller'rotating)) \<and>
           s2 \<noteq> s2a \<Longrightarrow>
           substate s1 s2 \<and>
           substate s2
             (toEnv (setPstate (setVarBool (setVarAny s0 user'value pressure'value) rotation True) ERROR Controller'rotating)) \<and>
           toEnvP s1 \<and>
           toEnvP s2 \<and>
           toEnvNum s1 s2 = ERROR \<and>
           DELAY'TIMEOUT =
           toEnvNum s2
            (toEnv (setPstate (setVarBool (setVarAny s0 user'value pressure'value) rotation True) ERROR Controller'rotating)) \<and>
           getVarBool s1 rotation = True \<and>
           \<not> getVarBool s2 user \<and>
           (\<forall>s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s2a \<and> s4 \<noteq> s2a \<longrightarrow>
                 getVarBool s4 rotation = True \<and> \<not> getVarBool s4 user) \<longrightarrow>
           (\<exists>s4. toEnvP s4 \<and>
                 substate s2a s4 \<and>
                 substate s4
                   (toEnv (setPstate (setVarBool (setVarAny s0 user'value pressure'value) rotation True) ERROR Controller'rotating)) \<and>
                 toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
                 (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
                 (\<forall>s3. toEnvP s3 \<and> substate s2a s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
                       getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user)) \<Longrightarrow>
           substate s1 s2 \<and>
           substate s2
             (toEnv (setPstate (setVarBool (setVarAny s0 user'value pressure'value) rotation True) ERROR Controller'rotating)) \<and>
           toEnvP s1 \<and>
           toEnvP s2 \<and>
           toEnvNum s1 s2 = ERROR \<and>
           DELAY'TIMEOUT =
           toEnvNum s2
             (toEnv (setPstate (setVarBool (setVarAny s0 user'value pressure'value) rotation True) ERROR Controller'rotating)) \<and>
           getVarBool s1 rotation = True \<and>
           \<not> getVarBool s2 user \<and>
           (\<forall>s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 (predEnv s2a) \<and> s4 \<noteq> predEnv s2a \<longrightarrow>
                 getVarBool s4 rotation = True \<and> \<not> getVarBool s4 user) \<longrightarrow>
           (\<exists>s4. toEnvP s4 \<and>
                 substate (predEnv s2a) s4 \<and>
                 substate s4
                  (toEnv (setPstate (setVarBool (setVarAny s0 user'value pressure'value) rotation True) ERROR Controller'rotating)) \<and>
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
  (toEnv (setPstate (setVarBool (setVarAny s0 user'value pressure'value) rotation True) ERROR Controller'rotating))"])
  using toEnvNum3[of s2 "predEnv s2a" 
" (toEnv (setPstate (setVarBool (setVarAny s0 user'value pressure'value) rotation True) ERROR Controller'rotating))"]
     apply arith
  using substate_eq_or_predEnv predEnv_substate substate_trans apply fast
   apply(rule conjI)
    apply assumption
  using substate_asym apply fast
  apply(rule exE[of "\<lambda> s4. toEnvP s4 \<and>
          substate s2a s4 \<and>
          substate s4
            (toEnv (setPstate (setVarBool (setVarAny s0 user'value pressure'value) rotation True) ERROR Controller'rotating)) \<and>
          toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
          (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
          (\<forall>s3. toEnvP s3 \<and> substate s2a s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
                getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user)"])
  using substate_eq_or_predEnv apply blast
  by ((rule VC2_R3_ind_step_aux1);blast)

thm VC3_def
lemma VC2_R3_ind_proof:   "toEnvP s5 \<and>  substate s2 s5 \<and>
 substate s5  (toEnv (setPstate (setVarBool (setVarAny s0 user'value pressure'value) rotation True) ERROR Controller'rotating))
 \<longrightarrow> pred3 s1 s2  (toEnv (setPstate (setVarBool (setVarAny s0 user'value pressure'value) rotation True) ERROR Controller'rotating))
 s5"
  apply(induction rule: state_down_ind)
  using toEnvPs2 apply simp
   apply(simp only: pred3_def)
   apply(rule impI)
  apply(rule cut_rl[of "getVarBool s0 rotation = False"])
    apply(rule cut_rl[of "getVarBool s0 rotation = True \<and> \<not> getVarBool s0 user"])
     apply fast
  apply(rule cut_rl[of "substate s2 s0 \<and>
          substate s0
           (toEnv (setPstate (setVarBool (setVarAny s0 user'value pressure'value) rotation True) ERROR Controller'rotating)) \<and>
          s0 \<noteq>
          (toEnv (setPstate (setVarBool (setVarAny s0 user'value pressure'value) rotation True) ERROR Controller'rotating)) "])
  using toEnvPs2  apply fast
  using substate_refl toEnvNum_id apply((simp split: if_splits);auto)
  using extraInvs0 extraInv_def vc
   apply (smt (verit) getPstate.simps(9) predEnv.simps(9) predEnv_substate substate_eq_or_predEnv toEnvPs2)
 apply(simp only: pred3_def)
  by ((rule VC2_R3_ind_step);fast) 
end


lemma VC2_R3: " (((((toEnvP s0 \<and>
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
           extraInv s0) \<and>
          env (setVarAny s0 user_value pressure_value)) \<and>
         getPstate (setVarAny s0 user_value pressure_value) ERROR = Controller'motionless) \<and>
        getVarBool (setVarAny s0 user_value pressure_value) user) \<and>
      \<not>  getVarBool (setVarAny s0 user_value pressure_value) pressure \<Longrightarrow>
       substate s1 s2 \<and>
       substate s2
        (toEnv (setPstate (setVarBool (setVarAny s0 user'value pressure'value) rotation True) ERROR Controller'rotating)) \<and>
       toEnvP s1 \<and>
       toEnvP s2 \<and>
       toEnvNum s1 s2 = ERROR \<and>
       DELAY'TIMEOUT
       \<le> toEnvNum s2
           (toEnv (setPstate (setVarBool (setVarAny s0 user'value pressure'value) rotation True) ERROR Controller'rotating)) \<and>
       getVarBool s1 rotation = True \<and> \<not> getVarBool s2 user \<longrightarrow>
       (\<exists>s4. toEnvP s4 \<and>
             substate s2 s4 \<and>
             substate s4
               (toEnv (setPstate (setVarBool (setVarAny s0 user'value pressure'value) rotation True) ERROR Controller'rotating)) \<and>
             toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
             (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
             (\<forall>s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
                   getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user))"
  apply(rule impI)
  apply(rule disjE[of "DELAY'TIMEOUT < toEnvNum s2
  (toEnv (setPstate (setVarBool (setVarAny s0 user'value pressure'value) rotation True) ERROR Controller'rotating))"
"DELAY'TIMEOUT = toEnvNum s2
 (toEnv (setPstate (setVarBool (setVarAny s0 user'value pressure'value) rotation True) ERROR Controller'rotating))"])
  using le_imp_less_or_eq apply fast
   apply(rule cut_rl[of "substate s2 s0 \<and> toEnvNum s2 s0 \<ge> DELAY'TIMEOUT"])
  apply(rule cut_rl[of "(\<exists>s4. toEnvP s4 \<and>
                   substate s2 s4 \<and>
                   substate s4 s0 \<and>
                   toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
                   (getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
                   (\<forall>s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
                         getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user))"])
  apply (metis substate.simps(10) substate.simps(2) substate.simps(3) substate.simps(9))
    apply blast
   apply(simp split: if_splits)
  apply(rule cut_rl[of "pred3 s1 s2 
 (toEnv (setPstate (setVarBool (setVarAny s0 user'value pressure'value) rotation True) ERROR Controller'rotating))
s2"])
   apply(simp only: pred3_def)
   apply (smt (z3) substate_asym)
   apply(rule mp[of "toEnvP s2 \<and>  substate s2 s2 \<and>
 substate s2
  (toEnv (setPstate (setVarBool (setVarAny s0 user'value pressure'value) rotation True) ERROR Controller'rotating))"])
   apply((rule VC2_R3_ind_proof);blast)
  using substate_refl by fast
  
  

theorem proof_3_2: "VC3 inv3 env s0 user_value pressure_value"
  apply(simp only: VC3_def inv3_def R3_def)
  apply(rule impI)
  apply(rule conjI)
  apply(rule conjI)
   apply(simp)
   apply((rule allI);(rule allI))
   apply((rule VC2_R3);blast)