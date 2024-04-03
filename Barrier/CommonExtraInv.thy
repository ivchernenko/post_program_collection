theory CommonExtraInv
  imports Barrier
begin

definition commonExtraInv where  "commonExtraInv s \<equiv> toEnvP s \<and>
(getPstate s Opening' = Opening'open' \<longrightarrow> getVarBool s green' = True \<and> getVarBool s red' = False \<and> getVarBool s up' = False \<and> getVarBool s down' = False) \<and>
(getPstate s Opening' = Opening'closing' \<longrightarrow> getVarBool s green' = False \<and> getVarBool s red' = True \<and> getVarBool s up' = False \<and> getVarBool s down' = True) \<and>
(getPstate s Opening' = STOP \<longrightarrow> getVarBool s green' = False \<and> getVarBool s up' = False \<and> getVarBool s down' = False) \<and>
(getPstate s Opening' = Opening'open' \<longrightarrow> ltime s Opening' \<le> OPEN_TIME'TIMEOUT) \<and>
(getPstate s CarController' \<in> {CarController'waitingForCar', CarController'waitingForCarPassing'}) \<and>
(getPstate s Opening' \<in> {Opening'opening', Opening'open', Opening'closing', STOP})"

theorem cei1: "VC1 commonExtraInv s0"
  apply(unfold VC1_def commonExtraInv_def)
  by auto

theorem cei2: "VC2 commonExtraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC2_def commonExtraInv_def)
  by force

theorem cei3: "VC3 commonExtraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC3_def commonExtraInv_def)
  by force

theorem cei4: "VC4 commonExtraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC4_def commonExtraInv_def)
  by force

theorem cei5: "VC5 commonExtraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC5_def commonExtraInv_def)
  by force

theorem cei6: "VC6 commonExtraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC6_def commonExtraInv_def)
  by force

theorem cei7: "VC7 commonExtraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC7_def commonExtraInv_def)
  by force

theorem cei8: "VC8 commonExtraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC8_def commonExtraInv_def)
  by force

theorem cei9: "VC9 commonExtraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC9_def commonExtraInv_def)
  by force

theorem cei10: "VC10 commonExtraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC10_def commonExtraInv_def)
  by force

theorem cei11: "VC11 commonExtraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC11_def commonExtraInv_def)
  by force

theorem cei12: "VC12 commonExtraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC12_def commonExtraInv_def)
  by force

theorem cei13: "VC13 commonExtraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC13_def commonExtraInv_def)
  by force

theorem cei14: "VC14 commonExtraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC14_def commonExtraInv_def)
  by force

theorem cei15: "VC15 commonExtraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC15_def commonExtraInv_def)
  by force

theorem cei16: "VC16 commonExtraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC16_def commonExtraInv_def)
  by force

theorem cei17: "VC17 commonExtraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC17_def commonExtraInv_def)
  by force

theorem cei18: "VC18 commonExtraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC18_def commonExtraInv_def)
  by force

theorem cei19: "VC19 commonExtraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC19_def commonExtraInv_def)
  by force

theorem cei20: "VC20 commonExtraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC20_def commonExtraInv_def)
  by force

theorem cei21: "VC21 commonExtraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC21_def commonExtraInv_def)
  by force

theorem cei22: "VC22 commonExtraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC22_def commonExtraInv_def)
  by force

theorem cei23: "VC23 commonExtraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC23_def commonExtraInv_def)
  by force

theorem cei24: "VC24 commonExtraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC24_def commonExtraInv_def)
  by force

theorem cei25: "VC25 commonExtraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC25_def commonExtraInv_def)
  by force

theorem cei26: "VC26 commonExtraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC26_def commonExtraInv_def)
  by force

theorem cei27: "VC27 commonExtraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC27_def commonExtraInv_def)
  by force

theorem cei28: "VC28 commonExtraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC28_def commonExtraInv_def)
  by force

theorem cei29: "VC29 commonExtraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC29_def commonExtraInv_def)
  by force

theorem cei30: "VC30 commonExtraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC30_def commonExtraInv_def)
  by force

theorem cei31: "VC31 commonExtraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC31_def commonExtraInv_def)
  by force

theorem cei32: "VC32 commonExtraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC32_def commonExtraInv_def)
  by force

theorem cei33: "VC33 commonExtraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC33_def commonExtraInv_def)
  by force

theorem cei34: "VC34 commonExtraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC34_def commonExtraInv_def)
  by force

theorem cei35: "VC35 commonExtraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC35_def commonExtraInv_def)
  by force

theorem cei36: "VC36 commonExtraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC36_def commonExtraInv_def)
  by force

theorem cei37: "VC37 commonExtraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC37_def commonExtraInv_def)
  by force

theorem cei38: "VC38 commonExtraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC38_def commonExtraInv_def)
  by force

theorem cei39: "VC39 commonExtraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC39_def commonExtraInv_def)
  by force

theorem cei40: "VC40 commonExtraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC40_def commonExtraInv_def)
  by force

theorem cei41: "VC41 commonExtraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC41_def commonExtraInv_def)
  by force

theorem cei42: "VC42 commonExtraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC42_def commonExtraInv_def)
  by force

theorem cei43: "VC43 commonExtraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC43_def commonExtraInv_def)
  by force

theorem cei44: "VC44 commonExtraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC44_def commonExtraInv_def)
  by force

theorem cei45: "VC45 commonExtraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC45_def commonExtraInv_def)
  by force

theorem cei46: "VC46 commonExtraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC46_def commonExtraInv_def)
  by force

theorem cei47: "VC47 commonExtraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC47_def commonExtraInv_def)
  by force

theorem cei48: "VC48 commonExtraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC48_def commonExtraInv_def)
  by force

end