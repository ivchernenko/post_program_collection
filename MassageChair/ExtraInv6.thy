theory ExtraInv6
  imports CommonExtraInv Requirements
begin

definition extraInv where "extraInv s \<equiv> commonExtraInv s \<and>
(getPstate s Roller' \<noteq> Roller'massaging' \<and> getPstate s Vibration' \<noteq> Vibration'massaging' \<longrightarrow>
P1inv s MASSAGE_TIME 0 (\<lambda> s1. getVarBool s1 roller' = True \<or> getVarBool s1 vibration' = True)
 (\<lambda> s3. getVarBool s3 roller' = False \<and> getVarBool s3 vibration' = False \<or> getVarBool s3 startButton' = PRESSED')
(\<lambda> s2. (getVarBool s2 roller' = True \<or> getVarBool s2 vibration' = True) \<and> getVarBool s2 startButton' \<noteq> PRESSED')) \<and>
(getPstate s Roller' = Roller'waiting' \<and> getPstate s Vibration' = Vibration'massaging' \<longrightarrow>
P1inv s MASSAGE_TIME (ltime s Vibration') (\<lambda> s1. getVarBool s1 roller' = True \<or> getVarBool s1 vibration' = True)
 (\<lambda> s3. getVarBool s3 roller' = False \<and> getVarBool s3 vibration' = False \<or> getVarBool s3 startButton' = PRESSED')
(\<lambda> s2. (getVarBool s2 roller' = True \<or> getVarBool s2 vibration' = True) \<and> getVarBool s2 startButton' \<noteq> PRESSED')) \<and>
(getPstate s Roller' = Roller'massaging' \<and> getPstate s Vibration' = Vibration'waiting' \<longrightarrow>
P1inv s MASSAGE_TIME (ltime s Roller') (\<lambda> s1. getVarBool s1 roller' = True \<or> getVarBool s1 vibration' = True)
 (\<lambda> s3. getVarBool s3 roller' = False \<and> getVarBool s3 vibration' = False \<or> getVarBool s3 startButton' = PRESSED')
(\<lambda> s2. (getVarBool s2 roller' = True \<or> getVarBool s2 vibration' = True) \<and> getVarBool s2 startButton' \<noteq> PRESSED')) \<and>
(getPstate s Roller' = STOP \<and> getPstate s Vibration' = Vibration'massaging' \<longrightarrow>
P1inv s MASSAGE_TIME (ROLLER_MASSAGE_TIME'TIMEOUT + ltime s Vibration') (\<lambda> s1. getVarBool s1 roller' = True \<or> getVarBool s1 vibration' = True)
 (\<lambda> s3. getVarBool s3 roller' = False \<and> getVarBool s3 vibration' = False \<or> getVarBool s3 startButton' = PRESSED')
(\<lambda> s2. (getVarBool s2 roller' = True \<or> getVarBool s2 vibration' = True) \<and> getVarBool s2 startButton' \<noteq> PRESSED')) \<and>
(getPstate s Roller' = Roller'massaging' \<and> getPstate s Vibration' = STOP \<longrightarrow>
P1inv s MASSAGE_TIME (VIBRATION_MASSAGE_TIME'TIMEOUT + ltime s Roller') (\<lambda> s1. getVarBool s1 roller' = True \<or> getVarBool s1 vibration' = True)
 (\<lambda> s3. getVarBool s3 roller' = False \<and> getVarBool s3 vibration' = False \<or> getVarBool s3 startButton' = PRESSED')
(\<lambda> s2. (getVarBool s2 roller' = True \<or> getVarBool s2 vibration' = True) \<and> getVarBool s2 startButton' \<noteq> PRESSED')) \<and>
(getPstate s Roller' = Roller'massaging' \<and> getPstate s Vibration' = Vibration'massaging' \<and> ltime s Roller' \<le> ltime s Vibration' \<longrightarrow>
P1inv s MASSAGE_TIME ( ltime s Vibration') (\<lambda> s1. getVarBool s1 roller' = True \<or> getVarBool s1 vibration' = True)
 (\<lambda> s3. getVarBool s3 roller' = False \<and> getVarBool s3 vibration' = False \<or> getVarBool s3 startButton' = PRESSED')
(\<lambda> s2. (getVarBool s2 roller' = True \<or> getVarBool s2 vibration' = True) \<and> getVarBool s2 startButton' \<noteq> PRESSED')) \<and>
(getPstate s Roller' = Roller'massaging' \<and> getPstate s Vibration' = Vibration'massaging' \<and> ltime s Roller' > ltime s Vibration' \<longrightarrow>
P1inv s MASSAGE_TIME ( ltime s Roller') (\<lambda> s1. getVarBool s1 roller' = True \<or> getVarBool s1 vibration' = True)
 (\<lambda> s3. getVarBool s3 roller' = False \<and> getVarBool s3 vibration' = False \<or> getVarBool s3 startButton' = PRESSED')
(\<lambda> s2. (getVarBool s2 roller' = True \<or> getVarBool s2 vibration' = True) \<and> getVarBool s2 startButton' \<noteq> PRESSED'))"

theorem extra1: "VC1 extraInv s0"
  apply(unfold VC1_def extraInv_def P1inv_def)
  using cei1 by(auto simp add: VC1_def)

theorem extra1622: "VC1622 extraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1622_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei1622 VC1622_def apply force
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(auto intro: P1inv_rule)
  done

theorem extra1627: "VC1627 extraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1627_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei1627 VC1627_def apply force
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(auto intro: P1inv_rule)
  done

theorem extra1632: "VC1632 extraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1632_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei1632 VC1632_def apply force
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(auto intro: P1inv_rule)
  done

theorem extra1637: "VC1637 extraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1637_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei1637 VC1637_def apply force
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(auto intro: P1inv_rule)
  done

theorem extra1667: "VC1667 extraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1667_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei1667 VC1667_def apply force
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(auto intro: P1inv_rule)
  done

theorem extra1697: "VC1697 extraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1697_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei1697 VC1697_def apply force
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(auto intro: P1inv_rule)
  done

theorem extra1727: "VC1727 extraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1727_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei1727 VC1727_def apply force
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(auto intro: P1inv_rule)
  done


theorem extra1652: "VC1652 extraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1652_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei1652 VC1652_def apply force
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(auto intro: P1inv_rule)
  done


theorem extra1682: "VC1682 extraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1682_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei1682 VC1682_def   apply force
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(auto intro: P1inv_rule)
  done

theorem extra1712: "VC1712 extraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1712_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei1712 VC1712_def apply force
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(auto intro: P1inv_rule)
  done

theorem extra1742: "VC1742 extraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1742_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei1742 VC1742_def apply force
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(auto intro: P1inv_rule)
  done

theorem extra1772: "VC1772 extraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1772_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei1772 VC1772_def apply force
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(auto intro: P1inv_rule)
  done



