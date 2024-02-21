theory ExtraInv_R13a
  imports CommonExtraInv "../Pattern4_Def"
begin

definition extraInv where "extraInv s \<equiv> commonExtraInv s \<and>
(getPstate s Drum' = Drum'leftRotation' \<longrightarrow>
P4inv s DIRECTION_CHANGE_PERIOD'TIMEOUT (ltime s Drum') (\<lambda> s1 s2. getVarBool s1 left' = False \<and> getVarBool s2 left' = True) (\<lambda> s4. getVarBool s4 left' = False)
(\<lambda> s3. getVarBool s3 left' = True)) \<and>
(getPstate s Drum' \<noteq> Drum'leftRotation' \<longrightarrow>
P4inv s DIRECTION_CHANGE_PERIOD'TIMEOUT 0 (\<lambda> s1 s2. getVarBool s1 left' = False \<and> getVarBool s2 left' = True) (\<lambda> s4. getVarBool s4 left' = False)
(\<lambda> s3. getVarBool s3 left' = True)) "

theorem extra1: "VC1 extraInv s0 "
  apply(unfold VC1_def extraInv_def P4inv_def)
  using cei1 by(auto simp add: VC1_def)

theorem extra53: "VC53 extraInv env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC53_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei53 apply(auto simp add: VC53_def)[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(auto intro: P4inv_rule2)
  done

theorem extra54: "VC54 extraInv env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC54_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei54 apply(auto simp add: VC54_def)[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(auto intro: P4inv_rule2)
  done

theorem extra55: "VC55 extraInv env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC55_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei55 apply(auto simp add: VC55_def)[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(auto intro: P4inv_rule2)
  done

theorem extra57: "VC57 extraInv env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC57_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei57 apply(auto simp add: VC57_def)[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(auto intro: P4inv_rule2)
  done

theorem extra130: "VC130 extraInv env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC130_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei130 apply(auto simp add: VC130_def)[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
   apply(cases "getPstate s0 Drum' = Drum'leftRotation'")
   apply(auto intro: P4inv_rule2)
  done

theorem extra56: "VC56 extraInv env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC56_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei56 apply(auto simp add: VC56_def)[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(auto intro: P4inv_rule2)
  done

theorem extra10: "VC10 extraInv env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC10_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei10 apply(auto simp add: VC10_def)[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(auto intro: P4inv_rule2)
  done

theorem extra23: "VC23 extraInv env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC23_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei23 apply(auto simp add: VC23_def)[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(auto intro: P4inv_rule2)
  done

end
