theory CommonExtraInv
  imports MassageChair "../VCTheoryLemmas"
begin

definition commonExtraInv where "commonExtraInv s \<equiv> toEnvP s \<and>
(getPstate s Controller' \<in> {Controller'turnedOn', Controller'turningOff'} \<longrightarrow> getVarBool s enabled' = True \<and> getPstate s BackMovement' = BackMovement'ctrl') \<and>
(getPstate s Controller' \<in> {Controller'turnedOff', Controller'turningOn', Controller'backLifting'} \<longrightarrow> 
getVarBool s enabled' = False \<and> getPstate s Roller' = STOP \<and> getPstate s Vibration' = STOP \<and> getPstate s BackMovement' = STOP) \<and>
(getPstate s Roller'\<noteq> Roller'massaging' \<longrightarrow> getVarBool s roller' = False) \<and>
(getPstate s Roller' = Roller'massaging' \<longrightarrow> getVarBool s roller' = True) \<and>
(getPstate s Vibration' \<noteq> Vibration'massaging' \<longrightarrow> getVarBool s vibration' = False) \<and>
(getPstate s Vibration' = Vibration'massaging' \<longrightarrow> getVarBool s vibration' = True) \<and>
(getPstate s Roller' = Roller'massaging' \<longrightarrow> ltime s Roller' \<le> ROLLER_MASSAGE_TIME'TIMEOUT) \<and>
(getPstate s Vibration' = Vibration'massaging' \<longrightarrow> ltime s Vibration' \<le> VIBRATION_MASSAGE_TIME'TIMEOUT) \<and>
(getPstate s Roller' \<in> {Roller'waiting', Roller'massaging', STOP}) \<and>
(getPstate s Vibration' \<in> {Vibration'waiting', Vibration'massaging', STOP}) \<and>
(getPstate s Controller' = Controller'turnedOn' \<longrightarrow> ltime s Controller' \<le> ON_OFF_TIME'TIMEOUT)"

theorem cei1: "VC1 commonExtraInv s0"
  apply(unfold VC1_def commonExtraInv_def)
  by simp

theorem extra2: "VC2 commonExtraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC2_def)
  by simp

theorem cei182: "VC182 commonExtraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC182_def commonExtraInv_def)
  by simp

theorem cei362: "VC362 commonExtraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC362_def commonExtraInv_def)
  by simp

theorem cei542: "VC542 commonExtraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC542_def commonExtraInv_def)
  by simp

theorem cei722: "VC722 commonExtraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC722_def commonExtraInv_def)
  by simp

theorem cei902: "VC902 commonExtraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC902_def commonExtraInv_def)
  by simp

theorem cei1082: "VC1082 commonExtraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1082_def)
  by simp

theorem cei1262: "VC1262 commonExtraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1262_def commonExtraInv_def)
  by simp

theorem extra1292: "VC1292 commonExtraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1292_def commonExtraInv_def)
  by simp

theorem extra1322: "VC1322 commonExtraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1322_def)
  by simp

theorem cei1622: "VC1622 commonExtraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1622_def commonExtraInv_def)
  by simp

theorem cei1627: "VC1627 commonExtraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1627_def commonExtraInv_def)
  by simp

theorem cei1632: "VC1632 commonExtraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1632_def commonExtraInv_def)
  by simp

theorem cei1637: "VC1637 commonExtraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1637_def commonExtraInv_def)
  by simp
  

theorem cei1667: "VC1667 commonExtraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1667_def commonExtraInv_def)
  by simp

theorem cei1652: "VC1652 commonExtraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1652_def commonExtraInv_def)
  by simp

theorem cei1682: "VC1682 commonExtraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1682_def commonExtraInv_def)
  by simp

theorem cei1683: "VC1683 commonExtraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
    apply(unfold VC1683_def commonExtraInv_def)
  by simp

theorem cei1684: "VC1684 commonExtraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1684_def commonExtraInv_def)
  by simp

theorem cei1697: "VC1697 commonExtraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1697_def commonExtraInv_def)
  by simp

theorem cei1712: "VC1712 commonExtraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1712_def commonExtraInv_def)
  by simp

theorem cei1727: "VC1727 commonExtraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1727_def commonExtraInv_def)
  by simp

theorem cei1742: "VC1742 commonExtraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1742_def commonExtraInv_def)
  by simp

theorem cei1772: "VC1772 commonExtraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1772_def commonExtraInv_def)
  by simp

theorem cei1802: "VC1802 commonExtraInv env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1802_def commonExtraInv_def)
  by simp

end