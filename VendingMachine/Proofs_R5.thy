theory Proofs_R5
  imports CommonExtraInv Requirements
begin

definition inv5 where "inv5 s \<equiv> R5 s \<and> commonExtraInv s"

theorem "VC1 inv5 s0"
  apply(unfold VC1_def inv5_def R5_def commonExtraInv_def always_def)
  apply auto
  done

theorem  "VC9 inv5 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC9_def inv5_def R5_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei9 apply((auto simp add: VC9_def)[1];fastforce)
  done

theorem  "VC18 inv5 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC18_def inv5_def R5_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei18 apply((auto simp add: VC18_def)[1];fastforce)
  done

theorem  "VC27 inv5 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC27_def inv5_def R5_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei27 apply((auto simp add: VC27_def)[1];fastforce)
  done

theorem  "VC36 inv5 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC36_def inv5_def R5_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei36 apply((auto simp add: VC36_def)[1];fastforce)
  done

theorem  "VC45 inv5 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC45_def inv5_def R5_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei45 apply((auto simp add: VC45_def)[1];fastforce)
  done

theorem  "VC54 inv5 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC54_def inv5_def R5_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei54 apply((auto simp add: VC54_def)[1];fastforce)
  done

theorem  "VC63 inv5 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC63_def inv5_def R5_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei63 apply((auto simp add: VC63_def)[1];fastforce)
  done

theorem  "VC72 inv5 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC72_def inv5_def R5_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei72 apply((auto simp add: VC72_def)[1];fastforce)
  done

theorem  "VC81 inv5 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC81_def inv5_def R5_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei81 apply((auto simp add: VC81_def)[1];fastforce)
  done

theorem  "VC90 inv5 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC90_def inv5_def R5_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei90 apply((auto simp add: VC90_def)[1];fastforce)
  done

theorem  "VC99 inv5 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC99_def inv5_def R5_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei99 apply((auto simp add: VC99_def)[1];fastforce)
  done

theorem  "VC108 inv5 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC108_def inv5_def R5_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei108 apply((auto simp add: VC108_def)[1];fastforce)
  done

theorem  "VC117 inv5 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC117_def inv5_def R5_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei117 apply((auto simp add: VC117_def)[1];fastforce)
  done

theorem  "VC126 inv5 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC126_def inv5_def R5_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei126 apply((auto simp add: VC126_def)[1];fastforce)
  done

theorem  "VC135 inv5 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC135_def inv5_def R5_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei135 apply((auto simp add: VC135_def)[1];fastforce)
  done

theorem  "VC144 inv5 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC144_def inv5_def R5_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei144 apply((auto simp add: VC144_def)[1];fastforce)
  done

theorem  "VC162 inv5 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC162_def inv5_def R5_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei162 apply((auto simp add: VC162_def)[1];fastforce)
  done

theorem  "VC153 inv5 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC153_def inv5_def R5_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei153 apply((auto simp add: VC153_def)[1];fastforce)
  done

theorem  "VC171 inv5 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC171_def inv5_def R5_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei171 apply((auto simp add: VC171_def)[1];fastforce)
  done

theorem  "VC234 inv5 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC234_def inv5_def R5_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei234 apply((auto simp add: VC234_def)[1];fastforce)
  done

theorem  "VC882 inv5 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC882_def inv5_def R5_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei882 apply((auto simp add: VC882_def)[1];fastforce)
  done