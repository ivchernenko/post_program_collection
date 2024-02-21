theory CommonExtraInv
  imports WashingMachine "../VCTheoryLemmas"
begin

definition commonExtraInv where "commonExtraInv s \<equiv> toEnvP s \<and>
( getPstate s Washing' = Washing'idle' \<longrightarrow> 
getVarBool s filling' = False \<and> getVarBool s drain' = False \<and> getVarBool s heater' = False \<and> getVarBool s lock' = False \<and> getVarBool s washing' = False) \<and>
( getPstate s Washing' = Washing'locking' \<longrightarrow> 
getVarBool s filling' = False \<and> getVarBool s drain' = False \<and> getVarBool s heater' = False \<and> getVarBool s lock' = True \<and> getVarBool s washing' = False) \<and>
(  getPstate s Washing' = Washing'waterSupply' \<longrightarrow> 
getVarBool s filling' = True \<and> getVarBool s drain' = False \<and> getVarBool s heater' = False \<and> getVarBool s lock' = True \<and> getVarBool s washing' = False) \<and>
(  getPstate s Washing' = Washing'wash' \<longrightarrow> 
getVarBool s filling' = False \<and> getVarBool s drain' = False \<and> getVarBool s lock' = True \<and> getVarBool s washing' = True) \<and>
( getPstate s Washing' = Washing'wash' \<longrightarrow> ltime s Washing' \<le> WASHING_TIME'TIMEOUT) \<and>
(  getPstate s Washing' = Washing'draining' \<longrightarrow> 
getVarBool s filling' = False \<and> getVarBool s drain' = True \<and> getVarBool s heater' = False \<and> getVarBool s lock' = True \<and> getVarBool s washing' = False) \<and>
( getPstate s Washing' \<in> {Washing'idle', Washing'locking'} \<longrightarrow> getPstate s Drum' = STOP) \<and>
( getPstate s Washing' \<in> {Washing'waterSupply', Washing'wash', Washing'draining'} \<longrightarrow> getPstate s Drum' \<noteq> STOP) \<and>
( getPstate s Washing' \<in> {Washing'idle', Washing'locking', Washing'waterSupply',  Washing'wash', Washing'draining'}) \<and>
( getPstate s Drum' = Drum'leftRotation' \<longrightarrow> getVarBool s left' = True \<and> getVarBool s right' = False) \<and>
( getPstate s Drum' = Drum'rightRotation' \<longrightarrow> getVarBool s left' = False \<and> getVarBool s right' = True) \<and>
( getPstate s Drum' \<in> {Drum'leftToRight', Drum'rightToLeft', STOP} \<longrightarrow>
 getVarBool s left' = False \<and> getVarBool s right' =False) \<and>
( getPstate s Drum' \<in> {Drum'leftRotation', Drum'leftToRight', Drum'rightRotation', Drum'rightToLeft', STOP}) \<and>
(getPstate s Drum' \<in> {Drum'leftRotation', Drum'rightRotation'} \<longrightarrow> ltime s Drum' \<le> DIRECTION_CHANGE_PERIOD'TIMEOUT)"

theorem cei1: "VC1 commonExtraInv  s0 "
  apply(unfold VC1_def commonExtraInv_def)
  by simp


theorem cei10: "VC10 commonExtraInv env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC10_def commonExtraInv_def)
  by simp

theorem cei20: "VC20 commonExtraInv env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC20_def commonExtraInv_def)
  by simp

theorem cei23: "VC23 commonExtraInv env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC23_def commonExtraInv_def)
  by simp

theorem cei53: "VC53 commonExtraInv env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC53_def commonExtraInv_def)
  by simp

theorem cei54: "VC54 commonExtraInv env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC54_def commonExtraInv_def)
  by simp

theorem cei55: "VC55 commonExtraInv env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC55_def commonExtraInv_def)
  by simp

theorem cei56: "VC56 commonExtraInv env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC56_def commonExtraInv_def)
  by simp

theorem cei57: "VC57 commonExtraInv env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC57_def commonExtraInv_def)
  by simp

theorem cei43: "VC43 commonExtraInv env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC43_def commonExtraInv_def)
  by simp

theorem cei63: "VC63 commonExtraInv env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC63_def commonExtraInv_def)
  by simp

theorem cei73: "VC73 commonExtraInv env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC73_def commonExtraInv_def)
  by simp

theorem cei130: "VC130 commonExtraInv env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC130_def commonExtraInv_def)
  by simp

theorem cei143: "VC143 commonExtraInv env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC143_def commonExtraInv_def)
  by auto

theorem cei150: "VC150 commonExtraInv env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC150_def commonExtraInv_def)
  apply simp
  by force


theorem cei160: "VC160 commonExtraInv env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC160_def commonExtraInv_def)
  by simp

theorem cei40: "VC40 commonExtraInv env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC40_def commonExtraInv_def)
  by simp

end
  