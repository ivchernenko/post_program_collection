theory Proofs_R5
  imports CommonExtraInv Requirements
begin

definition inv5 where "inv5 s \<equiv>  R5 s \<and> commonExtraInv s"

theorem "VC1 inv5 s0"
  apply(unfold VC1_def inv5_def R5_def)
  using cei1 VC1_def  apply auto
  done

theorem cei2: "VC2 inv5 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC2_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei2 VC2_def by auto

theorem cei3: "VC3 inv5 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC3_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei3 VC3_def by auto

theorem cei14: "VC14 inv5 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC14_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei14 VC14_def by auto

theorem cei15: "VC15 inv5 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC15_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei15 VC15_def by auto

theorem cei16: "VC16 inv5 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC16_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei16 VC16_def by auto

theorem cei17: "VC17 inv5 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC17_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei17 VC17_def by auto

theorem cei18: "VC18 inv5 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC18_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei18 VC18_def by auto

theorem cei19: "VC19 inv5 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC19_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei19 VC19_def by auto

theorem cei20: "VC20 inv5 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC20_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei20 VC20_def by auto

theorem cei21: "VC21 inv5 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC21_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei21 VC21_def by auto

theorem cei22: "VC22 inv5 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC22_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei22 VC22_def by auto

theorem cei23: "VC23 inv5 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC23_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei23 VC23_def by auto

theorem cei24: "VC24 inv5 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC24_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei24 VC24_def by auto

theorem cei25: "VC25 inv5 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC25_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei25 VC25_def by auto

theorem cei26: "VC26 inv5 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC26_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei26 VC26_def by auto

theorem cei27: "VC27 inv5 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC27_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei27 VC27_def by auto

theorem cei28: "VC28 inv5 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC28_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei28 VC28_def by auto

theorem cei29: "VC29 inv5 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC29_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei29 VC29_def by auto

theorem cei30: "VC30 inv5 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC30_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei30 VC30_def by auto

theorem cei31: "VC31 inv5 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC31_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei31 VC31_def by auto

theorem cei32: "VC32 inv5 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC32_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei32 VC32_def by auto

theorem cei33: "VC33 inv5 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC33_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei33 VC33_def by auto

theorem cei34: "VC34 inv5 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC34_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei34 VC34_def by auto

theorem cei35: "VC35 inv5 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC35_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei35 VC35_def by auto

theorem cei36: "VC36 inv5 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC36_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei36 VC36_def by auto

theorem cei37: "VC37 inv5 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC37_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei37 VC37_def by auto

theorem cei38: "VC38 inv5 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC38_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei38 VC38_def by auto

theorem cei39: "VC39 inv5 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC39_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei39 VC39_def by auto

theorem cei40: "VC40 inv5 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC40_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei40 VC40_def by auto

theorem cei41: "VC41 inv5 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC41_def inv5_def R5_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto 
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei41 VC41_def by auto

end
