theory ExtraInv_R6b
  imports "../Pattern5_Def" CommonExtraInv
begin

definition extraInv where "extraInv s \<equiv> commonExtraInv s \<and>
(getPstate s Washing' = Washing'wash' \<longrightarrow> 
P5inv s WASHING_TIME'TIMEOUT (ltime s Washing' - 1) (\<lambda>s1 s2. getVarBool s1 washing' = False \<and> getVarBool s2 washing' = True)
 (\<lambda> s3. getVarBool s3 washing' = True)) \<and>
(getPstate s Washing' \<noteq> Washing'wash' \<longrightarrow>
P5inv s WASHING_TIME'TIMEOUT 0 (\<lambda>s1 s2. getVarBool s1 washing' = False \<and> getVarBool s2 washing' = True)
 (\<lambda> s3. getVarBool s3 washing' = True))"

theorem extra1: "VC1 extraInv s0"
  apply(unfold VC1_def extraInv_def P5inv_def)
  using cei1 by(auto simp add: VC1_def)

theorem extra43: "VC43 extraInv env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC43_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei43 apply(auto simp add: VC43_def)[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule conjI)
  subgoal
    apply(rule P5inv_rule)
    by auto
  by simp

theorem extra53: "VC53 extraInv env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC53_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei53 apply(auto simp add: VC53_def)[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule conjI)
   apply simp
  subgoal
    apply(rule P5inv_rule)
    by auto
  done


theorem extra63: "VC63 extraInv env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC63_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei63 apply(auto simp add: VC63_def)[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule conjI)
   apply simp
  subgoal
    apply(rule P5inv_rule)
    by auto
  done

theorem extra73: "VC73 extraInv env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC73_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei73 apply(auto simp add: VC73_def)[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule conjI)
  subgoal
    apply(rule P5inv_rule)
    by auto
  by simp

theorem extra143: "VC143 extraInv env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC143_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei143 apply(auto simp add: VC143_def)[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  by simp

end

