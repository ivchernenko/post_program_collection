theory Proofs_R2
  imports Requirements CommonExtraInv
begin

definition inv2 where "inv2 s \<equiv> R2 s \<and> commonExtraInv s"

theorem "VC1 inv2 s0"
  apply(unfold VC1_def inv2_def R2_def always2_def always_def commonExtraInv_def)
  apply auto
  done

theorem  "VC72 inv2 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC72_def inv2_def R2_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei72 VC72_def by auto

theorem  "VC153 inv2 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC153_def inv2_def R2_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei153 VC153_def by auto

theorem  "VC234 inv2 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC234_def inv2_def R2_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei234 VC234_def by auto

theorem  "VC315 inv2 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC315_def inv2_def R2_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei315 VC315_def by auto

theorem  "VC324 inv2 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC324_def inv2_def R2_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei324 VC324_def by auto

theorem  "VC333 inv2 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC333_def inv2_def R2_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei333 VC333_def by auto

theorem  "VC342 inv2 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC342_def inv2_def R2_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei342 VC342_def by auto

theorem  "VC351 inv2 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC351_def inv2_def R2_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei351 VC351_def by auto

theorem  "VC360 inv2 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC360_def inv2_def R2_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei360 VC360_def by auto


theorem  "VC369 inv2 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC369_def inv2_def R2_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei369 VC369_def by auto

theorem  "VC378 inv2 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC378_def inv2_def R2_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei378 VC378_def by auto


theorem  "VC387 inv2 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC387_def inv2_def R2_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei387 VC387_def by auto


theorem  "VC396 inv2 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC396_def inv2_def R2_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei396 VC396_def by auto


theorem  "VC405 inv2 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC405_def inv2_def R2_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei405 VC405_def by auto


theorem  "VC738 inv2 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC738_def inv2_def R2_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei738 apply((auto simp add: VC738_def)[1];fastforce)
  done

theorem  "VC747 inv2 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC747_def inv2_def R2_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei747 apply((auto simp add: VC747_def)[1];fastforce)
  done

theorem  "VC756 inv2 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC756_def inv2_def R2_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei756 apply((auto simp add: VC756_def)[1];fastforce)
  done

theorem  "VC765 inv2 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC765_def inv2_def R2_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei765 apply((auto simp add: VC765_def)[1];fastforce)
  done

theorem  "VC774 inv2 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC774_def inv2_def R2_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei774 apply((auto simp add: VC774_def)[1];fastforce)
  done

theorem  "VC783 inv2 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC783_def inv2_def R2_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei783 apply((auto simp add: VC783_def)[1];fastforce)
  done

theorem  "VC792 inv2 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC792_def inv2_def R2_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei792 apply((auto simp add: VC792_def)[1];fastforce)
  done

theorem  "VC801 inv2 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC801_def inv2_def R2_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei801 apply((auto simp add: VC801_def)[1];fastforce)
  done

theorem  "VC810 inv2 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC810_def inv2_def R2_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei810 apply((auto simp add: VC810_def)[1];fastforce)
  done

end