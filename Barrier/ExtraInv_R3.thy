theory ExtraInv_R3
  imports CommonExtraInv "../Patterns"
begin

definition extraInv where "extraInv s \<equiv> commonExtraInv s \<and>
(getPstate s Opening' = STOP \<longrightarrow>
P6_2inv s True (getPstate s Opening' = Opening'closing') (getPstate s CarController' = CarController'waitingForCar')
 (\<lambda> s1. getVarBool s1 down' = True) (\<lambda> s2. getVarBool s2 closed' = True) (\<lambda> s3. getVarBool s3 up' = False)
 (\<lambda> s4. getVarBool s4 carInFront' = False) (\<lambda> s5. getVarBool s5 carInFront' = True)) \<and>
(getPstate s Opening' \<noteq> STOP \<longrightarrow>
P6_2inv s False (getPstate s Opening' = Opening'closing') (getPstate s CarController' = CarController'waitingForCar'
) (\<lambda> s1. getVarBool s1 down' = True) (\<lambda> s2. getVarBool s2 closed' = True) (\<lambda> s3. getVarBool s3 up' = False)
 (\<lambda> s4. getVarBool s4 carInFront' = False) (\<lambda> s5. getVarBool s5 carInFront' = True))"

theorem extra2': "VC2 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC2_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei2 VC2_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule conjI)
   apply(simp;(rule impI;simp)?)
  apply(simp;(rule impI;simp)?)
  apply(cases "getPstate s0 Opening' = STOP")
  subgoal
  apply(rule P6_2_rule[of s0])
    by auto
  subgoal
  apply(rule P6_2_rule[of s0])
    by auto
  done

definition extraInv2 where "extraInv2 s \<equiv> commonExtraInv s \<and>
P6_2inv s (getPstate s Opening' = STOP) (getPstate s Opening' = Opening'closing') (getPstate s CarController' = CarController'waitingForCar')
 (\<lambda> s1. getVarBool s1 down' = True) (\<lambda> s2. getVarBool s2 closed' = True) (\<lambda> s3. getVarBool s3 up' = False)
 (\<lambda> s4. getVarBool s4 carInFront' = False) (\<lambda> s5. getVarBool s5 carInFront' = True)"

theorem extra1: "VC1 extraInv2 s0"
  apply(unfold VC1_def extraInv2_def commonExtraInv_def P6_2inv_def always2_def always_def previous_ex_def weak_until_inv_def)
  apply auto
  done

theorem extra2: "VC2 extraInv2 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC2_def extraInv2_def)
  apply(rule impI)
  apply(rule conjI)
  using cei2 VC2_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule P6_2_rule[of s0])
   apply auto
  done

theorem extra3: "VC3 extraInv2 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC3_def extraInv2_def)
  apply(rule impI)
  apply(rule conjI)
  using cei3 VC3_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule P6_2_rule[of s0])
   apply auto
  done

theorem extra4: "VC4 extraInv2 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC4_def extraInv2_def)
  apply(rule impI)
  apply(rule conjI)
  using cei4 VC4_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply simp
  done

theorem extra14: "VC14 extraInv2 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC14_def extraInv2_def)
  apply(rule impI)
  apply(rule conjI)
  using cei14 VC14_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule P6_2_rule[of s0])
   apply auto
  done

theorem extra15: "VC15 extraInv2 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC15_def extraInv2_def)
  apply(rule impI)
  apply(rule conjI)
  using cei15 VC15_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule P6_2_rule[of s0])
   apply auto
  done

theorem extra16: "VC16 extraInv2 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC16_def extraInv2_def)
  apply(rule impI)
  apply(rule conjI)
  using cei16 VC16_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule P6_2_rule[of s0])
   apply auto
  done

theorem extra17: "VC17 extraInv2 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC17_def extraInv2_def)
  apply(rule impI)
  apply(rule conjI)
  using cei17 VC17_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule P6_2_rule[of s0])
   apply auto
  done

theorem extra18: "VC18 extraInv2 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC18_def extraInv2_def)
  apply(rule impI)
  apply(rule conjI)
  using cei18 VC18_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule P6_2_rule[of s0])
   apply auto
  done

theorem extra19: "VC19 extraInv2 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC19_def extraInv2_def)
  apply(rule impI)
  apply(rule conjI)
  using cei19 VC19_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule P6_2_rule[of s0])
   apply auto
  done

theorem extra20: "VC20 extraInv2 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC20_def extraInv2_def)
  apply(rule impI)
  apply(rule conjI)
  using cei20 VC20_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule P6_2_rule[of s0])
   apply auto
  done

theorem extra21: "VC21 extraInv2 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC21_def extraInv2_def)
  apply(rule impI)
  apply(rule conjI)
  using cei21 VC21_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule P6_2_rule[of s0])
   apply auto
  done

theorem extra22: "VC22 extraInv2 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC22_def extraInv2_def)
  apply(rule impI)
  apply(rule conjI)
  using cei22 VC22_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule P6_2_rule[of s0])
   apply auto
  done

theorem extra23: "VC23 extraInv2 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC23_def extraInv2_def)
  apply(rule impI)
  apply(rule conjI)
  using cei23 VC23_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule P6_2_rule[of s0])
   apply auto
  done

theorem extra24: "VC24 extraInv2 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC24_def extraInv2_def)
  apply(rule impI)
  apply(rule conjI)
  using cei24 VC24_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule P6_2_rule[of s0])
   apply auto
  done

theorem extra25: "VC25 extraInv2 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC25_def extraInv2_def)
  apply(rule impI)
  apply(rule conjI)
  using cei25 VC25_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply simp
  done

theorem extra26: "VC26 extraInv2 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC26_def extraInv2_def)
  apply(rule impI)
  apply(rule conjI)
  using cei26 VC26_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule P6_2_rule[of s0])
   apply auto
  done

theorem extra27: "VC27 extraInv2 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC27_def extraInv2_def)
  apply(rule impI)
  apply(rule conjI)
  using cei27 VC27_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule P6_2_rule[of s0])
   apply auto
  done

theorem extra28: "VC28 extraInv2 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC28_def extraInv2_def)
  apply(rule impI)
  apply(rule conjI)
  using cei28 VC28_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply simp
  done

theorem extra29: "VC29 extraInv2 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC29_def extraInv2_def)
  apply(rule impI)
  apply(rule conjI)
  using cei29 VC29_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule P6_2_rule[of s0])
   apply auto
  done

theorem extra30: "VC30 extraInv2 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC30_def extraInv2_def)
  apply(rule impI)
  apply(rule conjI)
  using cei30 VC30_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule P6_2_rule[of s0])
   apply auto
  done

theorem extra31: "VC31 extraInv2 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC31_def extraInv2_def)
  apply(rule impI)
  apply(rule conjI)
  using cei31 VC31_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule P6_2_rule[of s0])
   apply auto
  done

theorem extra32: "VC32 extraInv2 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC32_def extraInv2_def)
  apply(rule impI)
  apply(rule conjI)
  using cei32 VC32_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule P6_2_rule[of s0])
   apply auto
  done

theorem extra33: "VC33 extraInv2 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC33_def extraInv2_def)
  apply(rule impI)
  apply(rule conjI)
  using cei33 VC33_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule P6_2_rule[of s0])
   apply auto
  done

theorem extra34: "VC34 extraInv2 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC34_def extraInv2_def)
  apply(rule impI)
  apply(rule conjI)
  using cei34 VC34_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule P6_2_rule[of s0])
   apply auto
  done

theorem extra35: "VC35 extraInv2 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC35_def extraInv2_def)
  apply(rule impI)
  apply(rule conjI)
  using cei35 VC35_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule P6_2_rule[of s0])
   apply auto
  done

theorem extra36: "VC36 extraInv2 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC36_def extraInv2_def)
  apply(rule impI)
  apply(rule conjI)
  using cei36 VC36_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule P6_2_rule[of s0])
   apply auto
  done

theorem extra37: "VC37 extraInv2 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC37_def extraInv2_def)
  apply(rule impI)
  apply(rule conjI)
  using cei37 VC37_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule P6_2_rule[of s0])
   apply auto
  done

end