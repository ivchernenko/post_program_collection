theory ExtraInv4
  imports Requirements
begin


definition extraInv where "extraInv s \<equiv> toEnvP s \<and>
(getPstate s Controller' \<in> {Controller'motionless', Controller'rotating'} \<longrightarrow>
P9inv (\<lambda> s1 s2. getVarBool s1 rotation' = True \<and> getVarBool s2 pressure' = True) (\<lambda> s4. getVarBool s4 brake' = True)  (\<lambda> s5. getVarBool s5 brake' = True)
1 0 SUSPENSION_TIME'TIMEOUT (SUSPENSION_TIME'TIMEOUT - 1) s) \<and>
(getPstate s Controller'= Controller'suspended' \<and> ltime s Controller' = 1 \<longrightarrow>
P9inv (\<lambda> s1 s2. getVarBool s1 rotation' = True \<and> getVarBool s2 pressure' = True) (\<lambda> s4. getVarBool s4 brake' = True)  (\<lambda> s5. getVarBool s5 brake' = True)
1 1 SUSPENSION_TIME'TIMEOUT 0 s) \<and>
(getPstate s Controller'= Controller'suspended' \<and> ltime s Controller' > 1  \<longrightarrow>
P9inv (\<lambda> s1 s2. getVarBool s1 rotation' = True \<and> getVarBool s2 pressure' = True) (\<lambda> s4. getVarBool s4 brake' = True)  (\<lambda> s5. getVarBool s5 brake' = True)
1 0 SUSPENSION_TIME'TIMEOUT (ltime s Controller' - 1) s) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Controller' = Controller'motionless' \<longrightarrow> getVarBool s1 brake' = False \<and> getVarBool s1 rotation' = False) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Controller' = Controller'rotating' \<longrightarrow> getVarBool s1 brake' = False \<and> getVarBool s1 rotation' = True) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Controller' = Controller'suspended' \<longrightarrow> getVarBool s1 brake' = True \<and> getVarBool s1 rotation' = False)
 "

theorem "VC1 extraInv s0"
  apply(unfold VC1_def extraInv_def P9inv_def)
  by auto

definition commonExtraInv where "commonExtraInv s \<equiv> toEnvP s \<and>
( getPstate s Controller' = Controller'motionless' \<longrightarrow> getVarBool s brake' = False \<and> getVarBool s rotation' = False) \<and>
(getPstate s Controller' = Controller'rotating' \<longrightarrow> getVarBool s brake' = False \<and> getVarBool s rotation' = True) \<and>
( getPstate s Controller' = Controller'suspended' \<longrightarrow> getVarBool s brake' = True \<and> getVarBool s rotation' = False) \<and>
(getPstate s Controller' = Controller'suspended' \<longrightarrow> ltime s Controller' \<le> SUSPENSION_TIME'TIMEOUT) \<and>
(getPstate s Controller' \<in> {Controller'motionless', Controller'rotating', Controller'suspended'})"

theorem cei1: "VC1 commonExtraInv s0"
  apply(unfold VC1_def extraInv_def commonExtraInv_def)
  by auto

theorem cei2: "VC2 commonExtraInv env s0 user_value pressure_value"
  apply(unfold VC2_def extraInv_def commonExtraInv_def)
  by force

theorem cei3: "VC3 commonExtraInv env s0 user_value pressure_value"
  apply(unfold VC3_def extraInv_def commonExtraInv_def)
  by force

theorem cei4: "VC4 commonExtraInv env s0 user_value pressure_value"
  apply(unfold VC4_def extraInv_def commonExtraInv_def)
  by force

theorem cei5: "VC5 commonExtraInv env s0 user_value pressure_value"
  apply(unfold VC5_def extraInv_def commonExtraInv_def)
  by force

theorem cei6: "VC6 commonExtraInv env s0 user_value pressure_value"
  apply(unfold VC6_def extraInv_def commonExtraInv_def)
  by force

theorem cei7: "VC7 commonExtraInv env s0 user_value pressure_value"
  apply(unfold VC7_def extraInv_def commonExtraInv_def)
  by force

theorem cei8: "VC8 commonExtraInv env s0 user_value pressure_value"
  apply(unfold VC8_def extraInv_def commonExtraInv_def)
  by force

theorem cei9: "VC9 commonExtraInv env s0 user_value pressure_value"
  apply(unfold VC9_def extraInv_def commonExtraInv_def)
  by force

theorem cei10: "VC10 commonExtraInv env s0 user_value pressure_value"
  apply(unfold VC10_def extraInv_def commonExtraInv_def)
  by force

theorem cei11: "VC11 commonExtraInv env s0 user_value pressure_value"
  apply(unfold VC11_def extraInv_def commonExtraInv_def)
  by force

theorem cei12: "VC12 commonExtraInv env s0 user_value pressure_value"
  apply(unfold VC12_def extraInv_def commonExtraInv_def)
  by force

theorem cei13: "VC13 commonExtraInv env s0 user_value pressure_value"
  apply(unfold VC13_def extraInv_def commonExtraInv_def)
  by force

theorem cei14: "VC14 commonExtraInv env s0 user_value pressure_value"
  apply(unfold VC14_def extraInv_def commonExtraInv_def)
  by force

theorem cei15: "VC15 commonExtraInv env s0 user_value pressure_value"
  apply(unfold VC15_def extraInv_def commonExtraInv_def)
  by force

theorem cei16: "VC16 commonExtraInv env s0 user_value pressure_value"
  apply(unfold VC16_def extraInv_def commonExtraInv_def)
  by force

definition extraInv1 where "extraInv1 s \<equiv> commonExtraInv s \<and>
P9'inv s 1 SUSPENSION_TIME'TIMEOUT 0 (if getPstate s Controller' = Controller'suspended' then (ltime s Controller' - 1) else (SUSPENSION_TIME'TIMEOUT - 1))
(getPstate s Controller' \<noteq> Controller'rotating') 
 (\<lambda> s1. getVarBool s1 rotation' = True) (\<lambda> s2. getVarBool s2 pressure' = True) (\<lambda> s3. getVarBool s3 brake' = True)
 (\<lambda> s4. getVarBool s4 rotation' = False)"

theorem extra1: "VC1 extraInv1 s0"
  apply(unfold VC1_def extraInv1_def commonExtraInv_def P9'inv_def P4'inv_def always2_inv_def always_def constrained_until_inv_def constrained_always_inv_def)
  apply auto
  done

theorem extra2: "VC2 extraInv1 env s0 user_value pressure_value"
  apply(unfold VC2_def extraInv1_def)
 apply(rule impI)
  apply(rule conjI)
  using cei2 VC2_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule P9'inv_rule)
   apply(auto split: if_splits)
  done

theorem extra3: "VC3 extraInv1 env s0 user_value pressure_value"
  apply(unfold VC3_def extraInv1_def)
 apply(rule impI)
  apply(rule conjI)
  using cei3 VC3_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule P9'inv_rule)
   apply(auto split: if_splits)
  done

theorem extra4: "VC4 extraInv1 env s0 user_value pressure_value"
  apply(unfold VC4_def extraInv1_def)
 apply(rule impI)
  apply(rule conjI)
  using cei4 VC4_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule P9'inv_rule)
   apply(auto split: if_splits)
  done

theorem extra5: "VC5 extraInv1 env s0 user_value pressure_value"
  apply(unfold VC5_def extraInv1_def)
 apply(rule impI)
  apply(rule conjI)
  using cei5 VC5_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule P9'inv_rule)
   apply(auto split: if_splits)
  done

theorem extra6: "VC6 extraInv1 env s0 user_value pressure_value"
  apply(unfold VC6_def extraInv1_def)
 apply(rule impI)
  apply(rule conjI)
  using cei6 VC6_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule P9'inv_rule)
   apply(auto split: if_splits)
  done

theorem extra7: "VC7 extraInv1 env s0 user_value pressure_value"
  apply(unfold VC7_def extraInv1_def)
 apply(rule impI)
  apply(rule conjI)
  using cei7 VC7_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule P9'inv_rule)
   apply(auto split: if_splits)
  done

theorem extra8: "VC8 extraInv1 env s0 user_value pressure_value"
  apply(unfold VC8_def extraInv1_def)
 apply(rule impI)
  apply(rule conjI)
  using cei8 VC8_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule P9'inv_rule)
   apply(auto split: if_splits)
  done

theorem extra9: "VC9 extraInv1 env s0 user_value pressure_value"
  apply(unfold VC9_def extraInv1_def)
 apply(rule impI)
  apply(rule conjI)
  using cei9 VC9_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule P9'inv_rule)
   apply(auto split: if_splits)
  done

theorem extra10: "VC10 extraInv1 env s0 user_value pressure_value"
  apply(unfold VC10_def extraInv1_def)
 apply(rule impI)
  apply(rule conjI)
  using cei10 VC10_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule P9'inv_rule)
   apply(auto split: if_splits)
  done

theorem extra11: "VC11 extraInv1 env s0 user_value pressure_value"
  apply(unfold VC11_def extraInv1_def)
 apply(rule impI)
  apply(rule conjI)
  using cei11 VC11_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule P9'inv_rule)
   apply(auto split: if_splits)
  done

theorem extra12: "VC12 extraInv1 env s0 user_value pressure_value"
  apply(unfold VC12_def extraInv1_def)
 apply(rule impI)
  apply(rule conjI)
  using cei12 VC12_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule P9'inv_rule)
   apply(auto split: if_splits)
  done

theorem extra13: "VC13 extraInv1 env s0 user_value pressure_value"
  apply(unfold VC13_def extraInv1_def)
 apply(rule impI)
  apply(rule conjI)
  using cei13 VC13_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule P9'inv_rule)
   apply(auto split: if_splits)
  done

theorem extra14: "VC14 extraInv1 env s0 user_value pressure_value"
  apply(unfold VC14_def extraInv1_def)
 apply(rule impI)
  apply(rule conjI)
  using cei14 VC14_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule P9'inv_rule)
   apply(auto split: if_splits)
  done

theorem extra15: "VC15 extraInv1 env s0 user_value pressure_value"
  apply(unfold VC15_def extraInv1_def)
 apply(rule impI)
  apply(rule conjI)
  using cei15 VC15_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule P9'inv_rule)
   apply(auto split: if_splits)
  done

theorem extra16: "VC16 extraInv1 env s0 user_value pressure_value"
  apply(unfold VC16_def extraInv1_def)
 apply(rule impI)
  apply(rule conjI)
  using cei16 VC16_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule P9'inv_rule)
   apply(auto split: if_splits)
  done

end