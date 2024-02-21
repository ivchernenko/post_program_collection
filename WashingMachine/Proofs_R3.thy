theory Proofs_R3
  imports Requirements CommonExtraInv
begin

definition inv3 where "inv3 s \<equiv> R3 s \<and> commonExtraInv s"

theorem  "VC1 R3  s0 "
  apply(unfold VC1_def  R3_def)
  by auto

theorem  "VC10 R3 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC10_def  R3_def)
  apply auto
  using substate_toEnvNum_id by blast

theorem  "VC20 R3 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC20_def  R3_def)
  apply auto
  using substate_toEnvNum_id by blast

theorem  "VC23 R3 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC23_def  R3_def)
  by auto

theorem  "VC40 R3 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC40_def  R3_def)
  apply auto
  using substate_toEnvNum_id by blast

theorem  "VC43 R3 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC43_def  R3_def)
  by auto

theorem  "VC53 R3 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC53_def  R3_def)
  apply auto
  using substate_toEnvNum_id by blast

theorem  "VC63 R3 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC63_def  R3_def)
  apply auto
  using substate_toEnvNum_id by blast

theorem  "VC73 R3 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC73_def  R3_def)
  apply auto
  using substate_toEnvNum_id by blast

theorem  "VC83 R3 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC83_def  R3_def)
  apply auto
  using substate_toEnvNum_id by blast

theorem  "VC93 R3 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC93_def  R3_def)
  apply auto
  using substate_toEnvNum_id by blast

theorem  "VC143 inv3 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC143_def inv3_def  R3_def)
    apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
  apply(erule conjE)+
  subgoal
    apply auto
    using substate_toEnvNum_id by (blast+)?
  using cei143 by(auto simp add: VC143_def)

end

  




