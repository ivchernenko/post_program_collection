theory Proofs_R9
  imports CommonExtraInv Requirements
begin

definition inv9 where "inv9 s \<equiv> R9 s \<and> commonExtraInv s"

theorem "VC1 inv9 s0"
  apply(unfold VC1_def inv9_def R9_def)
  using cei1 VC1_def apply auto
  done

theorem  "VC2 inv9 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC2_def inv9_def R9_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei2 VC2_def by auto

theorem  "VC3 inv9 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC3_def inv9_def R9_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei3 VC3_def by auto

theorem  "VC14 inv9 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC14_def inv9_def R9_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei14 VC14_def by auto

theorem  "VC15 inv9 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC15_def inv9_def R9_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei15 VC15_def by auto

theorem  "VC16 inv9 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC16_def inv9_def R9_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei16 VC16_def by auto

theorem  "VC17 inv9 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC17_def inv9_def R9_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei17 VC17_def by auto

theorem  "VC18 inv9 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC18_def inv9_def R9_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei18 VC18_def by auto

theorem  "VC19 inv9 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC19_def inv9_def R9_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei19 VC19_def by auto

theorem  "VC20 inv9 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC20_def inv9_def R9_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei20 VC20_def by auto

theorem  "VC21 inv9 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC21_def inv9_def R9_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei21 VC21_def by auto

theorem  "VC22 inv9 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC22_def inv9_def R9_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei22 VC22_def by auto

theorem  "VC23 inv9 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC23_def inv9_def R9_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei23 VC23_def by auto

theorem  "VC24 inv9 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC24_def inv9_def R9_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei24 VC24_def by auto

theorem  "VC25 inv9 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC25_def inv9_def R9_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei25 VC25_def by auto

theorem  "VC26 inv9 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC26_def inv9_def R9_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei26 VC26_def by auto

theorem  "VC27 inv9 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC27_def inv9_def R9_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei27 VC27_def by auto

theorem  "VC28 inv9 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC28_def inv9_def R9_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei28 VC28_def by auto

theorem  "VC29 inv9 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC29_def inv9_def R9_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei29 VC29_def by auto

theorem  "VC30 inv9 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC30_def inv9_def R9_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei30 VC30_def by auto

theorem  "VC31 inv9 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC31_def inv9_def R9_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei31 VC31_def by auto

theorem  "VC32 inv9 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC32_def inv9_def R9_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei32 VC32_def by auto

theorem  "VC33 inv9 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC33_def inv9_def R9_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei33 VC33_def by auto

theorem  "VC34 inv9 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC34_def inv9_def R9_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei34 VC34_def by auto

theorem  "VC35 inv9 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC35_def inv9_def R9_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei35 VC35_def by auto

theorem  "VC36 inv9 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC36_def inv9_def R9_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei36 VC36_def by auto