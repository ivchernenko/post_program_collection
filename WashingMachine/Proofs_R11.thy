theory Proofs_R11
  imports ExtraInv_R11
begin

definition inv11 where "inv11 s \<equiv> R11 s \<and> extraInv s"

theorem "VC1 R11 s0"
  apply(unfold VC1_def R11_def P6_def)
  by auto

theorem extra23: "VC23 R11 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC23_def R11_def)
  apply(rule impI)
  apply(rule conjI)
  apply simp
  apply(rule P6_rule)
  by auto

theorem extra40: "VC40 inv11 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC40_def inv11_def R11_def)
  apply(rule impI)
  apply(rule conjI)
   apply (rule conjI)
    apply simp
  subgoal
    apply(unfold extraInv_def commonExtraInv_def)
    apply(erule conjE)+
    apply(rule P6_rule)
    by auto
  using extra40 by(auto simp add: VC40_def)

theorem extra43: "VC43 inv11 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC43_def inv11_def R11_def)
  apply(rule impI)
  apply(rule conjI)
   apply (rule conjI)
    apply simp
  subgoal
    apply(unfold extraInv_def commonExtraInv_def)
    apply(erule conjE)+
    apply(rule Pattern6_Def.einv2req)
    by auto
  using extra43 by(auto simp add: VC43_def)

theorem "VC143 inv11 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC143_def inv11_def R11_def)
 apply(rule impI)
  apply(rule conjI)
   apply (rule conjI)
    apply simp
  subgoal
    apply(unfold extraInv_def commonExtraInv_def)
    apply(erule conjE)+
    by simp
  using extra143 by(auto simp add: VC143_def)

end