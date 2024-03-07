theory ExtraInv_R7
  imports CommonExtraInv "../Pattern12_Def"
begin

definition extraInv where "extraInv s \<equiv> commonExtraInv s \<and>
(getPstate s Controller' = Controller'turningOn' \<longrightarrow>
P12inv s 0 (\<lambda> s1. getVarBool s1 enabled' = True) (\<lambda> s2. getVarBool s2 onOff' = PRESSED')) \<and>
(getPstate s Controller' = Controller'turnedOn' \<longrightarrow>
P12inv s (ltime s Controller' - 1) (\<lambda> s1. getVarBool s1 enabled' = True) (\<lambda> s2. getVarBool s2 onOff' = PRESSED'))"

theorem extra1: "VC1 extraInv s0"
  apply(unfold VC1_def extraInv_def P12inv_def)
  using cei1 VC1_def by auto

theorem extra182: "VC182 extraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC182_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei182 VC182_def apply force
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  by simp

theorem extra362: "VC362 extraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC362_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei362 VC362_def apply force
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  by simp

theorem extra542: "VC542 extraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC542_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei542 VC542_def apply force
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  by simp

theorem extra722: "VC722 extraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC722_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei722 VC722_def apply force
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(auto intro: P12inv_rule)
  done

theorem extra902: "VC902 extraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC902_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei902 VC902_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  by simp

theorem extra1082: "VC1082 extraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1082_def )
  by simp

theorem extra1262: "VC1262 extraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1262_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei1262 VC1262_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply simp
  apply(rule P12inv_rule[of _ _ _ _ s0])
   apply auto
  done

theorem extra1442: "VC1442 extraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1442_def)
  by simp

theorem extra1622: "VC1622 extraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1622_def extraInv_def)
    apply(rule impI)
  apply(rule conjI)
  using cei1622 VC1622_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply simp
  apply(rule P12inv_rule[of _ _ _ _ s0])
   apply auto
  done

theorem extra1802: "VC1802 extraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1802_def extraInv_def)
      apply(rule impI)
  apply(rule conjI)
  using cei1802 VC1802_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  by simp

end
