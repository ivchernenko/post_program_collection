theory Proofs_R2
  imports CommonExtraInv Requirements "../VCTheoryLemmas"
begin

definition inv2 where "inv2 s \<equiv> R2 s \<and> commonExtraInv s"

theorem "VC1 inv2 s0"
  apply(unfold VC1_def inv2_def R2_def commonExtraInv_def)
  apply auto
  done

theorem cei2: "VC2 inv2 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC2_def inv2_def R2_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of s0] by (force+)?
  using cei2 VC2_def by auto

theorem cei3: "VC3 inv2 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC3_def inv2_def R2_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of s0] by (force+)?
  using cei3 VC3_def by auto

theorem cei14: "VC14 inv2 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC14_def inv2_def R2_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of s0] by (force+)?
  using cei14 VC14_def by auto

theorem cei15: "VC15 inv2 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC15_def inv2_def R2_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of s0] by (force+)?
  using cei15 VC15_def by auto

theorem cei16: "VC16 inv2 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC16_def inv2_def R2_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of s0] by (force+)?
  using cei16 VC16_def by auto

theorem cei17: "VC17 inv2 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC17_def inv2_def R2_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of s0] by (force+)?
  using cei17 VC17_def by auto

theorem cei18: "VC18 inv2 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC18_def inv2_def R2_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of s0] by (force+)?
  using cei18 VC18_def by auto

theorem cei19: "VC19 inv2 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC19_def inv2_def R2_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of s0] by (force+)?
  using cei19 VC19_def by auto

theorem cei20: "VC20 inv2 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC20_def inv2_def R2_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of s0] by (force+)?
  using cei20 VC20_def by auto

theorem cei21: "VC21 inv2 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC21_def inv2_def R2_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of s0] by (force+)?
  using cei21 VC21_def by auto

theorem cei22: "VC22 inv2 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC22_def inv2_def R2_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of s0] by (force+)?
  using cei22 VC22_def by auto

theorem cei23: "VC23 inv2 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC23_def inv2_def R2_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of s0] by (force+)?
  using cei23 VC23_def by auto

theorem cei24: "VC24 inv2 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC24_def inv2_def R2_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of s0] by (force+)?
  using cei24 VC24_def by auto

theorem cei25: "VC25 inv2 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC25_def inv2_def R2_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of s0] by (force+)?
  using cei25 VC25_def by auto

end
