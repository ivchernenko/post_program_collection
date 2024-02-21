theory Proofs1
  imports CommonExtraInv Requirements
begin

definition inv1 where "inv1 s \<equiv> R1 s \<and> commonExtraInv s"

theorem  "VC1 R1  s0"
  apply(unfold VC1_def R1_def)
  by auto

theorem  "VC10 R1 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC10_def R1_def)
  by auto

theorem  "VC20 R1 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC20_def R1_def)
  by auto

theorem  "VC23 inv1 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC23_def inv1_def R1_def)
  apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)
   apply auto[1]
  using cei23 by(auto simp add: VC23_def)

theorem  "VC40 inv1 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC40_def inv1_def R1_def)
    apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)
   apply auto[1]
  using cei40 by(auto simp add: VC40_def)

theorem  "VC43 inv1 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC43_def inv1_def R1_def)
    apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)
   apply auto[1]
  using cei43 by(auto simp add: VC43_def)

theorem  "VC53 inv1 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC53_def inv1_def R1_def)
    apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)
   apply auto[1]
  using cei53 by(auto simp add: VC53_def)

theorem  "VC54 inv1 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC54_def inv1_def R1_def)
    apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)
   apply auto[1]
  using cei54 by(auto simp add: VC54_def)

theorem  "VC55 inv1 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC55_def inv1_def R1_def)
    apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)
   apply auto[1]
  using cei55 by(auto simp add: VC55_def)

theorem  "VC57 inv1 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC57_def inv1_def R1_def)
    apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)
   apply auto[1]
  using cei57 by(auto simp add: VC57_def)

theorem  "VC63 inv1 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC63_def inv1_def R1_def)
    apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)
   apply auto[1]
  using cei63 by(auto simp add: VC63_def)

theorem  "VC73 inv1 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC73_def inv1_def R1_def)
    apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)
   apply auto[1]
  using cei73 by(auto simp add: VC73_def)

theorem  "VC130 inv1 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC130_def inv1_def R1_def)
    apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)+
  subgoal
   apply auto[1]
    using substate_toEnvNum_id by blast+

theorem  "VC143 inv1 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC143_def inv1_def R1_def)
    apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)
   apply auto[1]
  using cei143 by(auto simp add: VC143_def)

theorem  "VC150 inv1 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC150_def inv1_def R1_def)
    apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)
   apply auto[1]
  using cei150 by(auto simp add: VC150_def)

theorem  "VC160 inv1 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC160_def inv1_def R1_def)
    apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)
   apply auto[1]
  using cei160 by(auto simp add: VC160_def)

end
  