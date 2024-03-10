theory ExtraInv_R8
  imports CommonExtraInv "../Pattern6_Def" "../Pattern12_Def"
begin

definition extraInv where "extraInv s \<equiv> commonExtraInv s \<and>
P6inv1 s (getPstate s Controller' = Controller'backLifting' \<and> getVarBool s up' = True)
(\<lambda> s3 s4. P12op s3 ON_OFF_TIME'TIMEOUT (\<lambda> s1. getVarBool s1 enabled' = True) (\<lambda> s2. getVarBool s2 onOff' = PRESSED') \<and> getVarBool s4 onOff' \<noteq> PRESSED')
(\<lambda> s5. getVarBool s5 up' = True) (\<lambda> s6. getVarBool s6 upper') \<and>
(getPstate s Controller' \<in> {Controller'turnedOff', Controller'turnedOn'} \<longrightarrow>
P12inv s (ltime s Controller') (\<lambda> s1. getVarBool s1 enabled' = True) (\<lambda> s2. getVarBool s2 onOff' = PRESSED')) \<and>
(getPstate s Controller' = Controller'backLifting' \<and> getVarBool s up' = False \<or> getPstate s Controller' = Controller'turningOn' \<longrightarrow>
P12inv s 0 (\<lambda> s1. getVarBool s1 enabled' = True) (\<lambda> s2. getVarBool s2 onOff' = PRESSED'))"

theorem extra1: "VC1 extraInv s0"
  apply(unfold VC1_def extraInv_def P6inv1_def P12inv_def)
  using cei1 apply (auto simp add: VC1_def)
  done

theorem extra182: "VC182 extraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC182_def extraInv_def)
    apply(rule impI)
  apply(rule conjI)
  using cei182 VC182_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply simp
  done

theorem extra362: "VC362 extraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC362_def extraInv_def)
    apply(rule impI)
  apply(rule conjI)
  using cei362 VC362_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply simp
  done

theorem extra542: "VC542 extraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC542_def extraInv_def)
    apply(rule impI)
  apply(rule conjI)
  using cei542 VC542_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply simp
  done

theorem extra722: "VC722 extraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC722_def extraInv_def)
    apply(rule impI)
  apply(rule conjI)
  using cei722 VC722_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule conjI)
  subgoal
   apply simp
    apply(rule P6inv1_rule[of s0])
       apply simp
    subgoal
      apply simp
      apply(rule Pattern12_Def.einv2req_neg)
      by auto
    by auto
  apply(rule conjI)
  subgoal
   apply simp
    apply(rule P12inv_rule[of _ _ _ _ _ s0])
    by auto
  apply simp
  done

theorem extra902: "VC902 extraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC902_def extraInv_def)
    apply(rule impI)
  apply(rule conjI)
  using cei902 VC902_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply simp
  done

theorem extra1262: "VC1262 extraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1262_def extraInv_def)
    apply(rule impI)
  apply(rule conjI)
  using cei1262 VC1262_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule conjI)
  subgoal
    apply simp
    apply(rule P6inv1_rule[of s0])
       apply simp
    subgoal
      apply simp
     apply(rule Pattern12_Def.einv2req_neg)
      by auto
    by auto
  apply(rule conjI)
  subgoal
   apply simp
    apply(rule P12inv_rule[of _ _ _ _ _ s0])
    by auto
  by simp

theorem extra1622: "VC1622 extraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1622_def extraInv_def)
    apply(rule impI)
  apply(rule conjI)
  using cei1622 VC1622_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule conjI)
  subgoal
    apply simp
    apply(rule P6inv1_rule[of s0])
       apply simp
    subgoal
      apply simp
     apply(rule Pattern12_Def.einv2req_neg)
      by auto
    by auto
  apply(rule conjI)
  subgoal
   apply simp
    apply(rule P12inv_rule[of _ _ _ _ _ s0])
    by auto
  by simp

theorem extra1802: "VC1802 extraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1802_def extraInv_def)
    apply(rule impI)
  apply(rule conjI)
  using cei1802 VC1802_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
   apply(rule conjI)
  subgoal
    apply simp
    apply(rule P6inv1_rule[of s0])
    by auto
  by auto

end

  

   