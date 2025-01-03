theory ExtraInv_R11
  imports Requirements CommonExtraInv
begin

definition extraInv  where "extraInv s \<equiv> commonExtraInv s \<and>
(getPstate s Washing' \<in> {Washing'waterSupply', Washing'wash', Washing'draining'} \<longrightarrow> 
P6inv s (\<lambda> s1 s2. getVarBool s1 lock' = False \<and> getVarBool s2 lock' = True)
(\<lambda> s4. getVarBool s4 locked' = True))"

theorem extra1: "VC1 extraInv s0"
  apply(unfold VC1_def extraInv_def commonExtraInv_def P6inv_def)
  by auto

theorem extra23: "VC23 extraInv env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC23_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei23 apply(auto simp add: VC23_def)[1]
  apply(erule conjE)+
  apply simp
  by(auto simp add: P6inv_rule2)

theorem extra43: "VC43 extraInv env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC43_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei43 apply(auto simp add: VC43_def)[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule P6inv_rule1)
  by auto

theorem extra53: "VC53 extraInv env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC53_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei53 apply(auto simp add: VC53_def)[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule P6inv_rule1)
  by auto

theorem extra40: "VC40 extraInv env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC40_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  using cei40 apply(auto simp add: VC40_def)[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
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