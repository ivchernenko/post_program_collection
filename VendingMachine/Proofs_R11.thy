theory Proofs_R11
  imports CommonExtraInv Requirements
begin

definition inv11 where "inv11 s \<equiv> R11 s \<and> commonExtraInv s"

theorem "VC1 inv11 s0"
  apply(unfold VC1_def inv11_def R11_def commonExtraInv_def always_def)
  apply auto
  done

theorem  "VC9 inv11 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC9_def inv11_def R11_def always2_def always_def previous_ex_def)
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

theorem  "VC18 inv11 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC18_def inv11_def R11_def always2_def always_def previous_ex_def)
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

theorem  "VC27 inv11 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC27_def inv11_def R11_def always2_def always_def previous_ex_def)
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

theorem  "VC36 inv11 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC36_def inv11_def R11_def always2_def always_def previous_ex_def)
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

theorem  "VC45 inv11 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC45_def inv11_def R11_def always2_def always_def previous_ex_def)
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

theorem  "VC54 inv11 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC54_def inv11_def R11_def always2_def always_def previous_ex_def)
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

theorem  "VC63 inv11 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC63_def inv11_def R11_def always2_def always_def previous_ex_def)
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

theorem  "VC72 inv11 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC72_def inv11_def R11_def always2_def always_def previous_ex_def)
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

theorem  "VC81 inv11 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC81_def inv11_def R11_def always2_def always_def previous_ex_def)
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

theorem  "VC90 inv11 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC90_def inv11_def R11_def always2_def always_def previous_ex_def)
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

theorem  "VC99 inv11 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC99_def inv11_def R11_def always2_def always_def previous_ex_def)
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

theorem  "VC108 inv11 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC108_def inv11_def R11_def always2_def always_def previous_ex_def)
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

theorem  "VC117 inv11 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC117_def inv11_def R11_def always2_def always_def previous_ex_def)
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

theorem  "VC126 inv11 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC126_def inv11_def R11_def always2_def always_def previous_ex_def)
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

theorem  "VC135 inv11 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC135_def inv11_def R11_def always2_def always_def previous_ex_def)
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

theorem  "VC144 inv11 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC144_def inv11_def R11_def always2_def always_def previous_ex_def)
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

theorem  "VC162 inv11 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC162_def inv11_def R11_def always2_def always_def previous_ex_def)
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

theorem  "VC153 inv11 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC153_def inv11_def R11_def always2_def always_def previous_ex_def)
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

theorem  "VC171 inv11 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC171_def inv11_def R11_def always2_def always_def previous_ex_def)
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

theorem  "VC180 inv11 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC180_def inv11_def R11_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei180 apply((auto simp add: VC180_def)[1];fastforce)
  done

theorem  "VC189 inv11 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC189_def inv11_def R11_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei189 apply((auto simp add: VC189_def)[1];fastforce)
  done

theorem  "VC198 inv11 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC198_def inv11_def R11_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei198 apply((auto simp add: VC198_def)[1];fastforce)
  done

theorem  "VC207 inv11 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC207_def inv11_def R11_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei207 apply((auto simp add: VC207_def)[1];fastforce)
  done

theorem  "VC216 inv11 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC216_def inv11_def R11_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei216 apply((auto simp add: VC216_def)[1];fastforce)
  done

theorem  "VC225 inv11 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC225_def inv11_def R11_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei225 apply((auto simp add: VC225_def)[1];fastforce)
  done

theorem  "VC234 inv11 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC234_def inv11_def R11_def always2_def always_def previous_ex_def)
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

theorem  "VC315 inv11 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC315_def inv11_def R11_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei315 apply((auto simp add: VC315_def)[1];fastforce)
  done

theorem  "VC324 inv11 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC324_def inv11_def R11_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei324 apply((auto simp add: VC324_def)[1];fastforce)
  done

theorem  "VC333 inv11 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC333_def inv11_def R11_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei333 apply((auto simp add: VC333_def)[1];fastforce)
  done

theorem  "VC342 inv11 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC342_def inv11_def R11_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei342 apply((auto simp add: VC342_def)[1];fastforce)
  done

theorem  "VC351 inv11 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC351_def inv11_def R11_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei351 apply((auto simp add: VC351_def)[1];fastforce)
  done

theorem  "VC360 inv11 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC360_def inv11_def R11_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei360 apply((auto simp add: VC360_def)[1];fastforce)
  done

theorem  "VC369 inv11 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC369_def inv11_def R11_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei369 apply((auto simp add: VC369_def)[1];fastforce)
  done

theorem  "VC378 inv11 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC378_def inv11_def R11_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei378 apply((auto simp add: VC378_def)[1];fastforce)
  done

theorem  "VC387 inv11 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC387_def inv11_def R11_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei387 apply((auto simp add: VC387_def)[1];fastforce)
  done

theorem  "VC396 inv11 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC396_def inv11_def R11_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei396 apply((auto simp add: VC396_def)[1];fastforce)
  done

theorem  "VC405 inv11 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC405_def inv11_def R11_def always2_def always_def previous_ex_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei405 apply((auto simp add: VC405_def)[1];fastforce)
  done

theorem  "VC738 inv11 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC738_def inv11_def R11_def always2_def always_def previous_ex_def)
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

theorem  "VC747 inv11 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC747_def inv11_def R11_def always2_def always_def previous_ex_def)
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


theorem  "VC756 inv11 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC756_def inv11_def R11_def always2_def always_def previous_ex_def)
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

theorem  "VC765 inv11 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC765_def inv11_def R11_def always2_def always_def previous_ex_def)
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

theorem  "VC774 inv11 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC774_def inv11_def R11_def always2_def always_def previous_ex_def)
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

theorem  "VC783 inv11 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC783_def inv11_def R11_def always2_def always_def previous_ex_def)
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

theorem  "VC792 inv11 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC792_def inv11_def R11_def always2_def always_def previous_ex_def)
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

theorem  "VC801 inv11 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC801_def inv11_def R11_def always2_def always_def previous_ex_def)
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

theorem  "VC882 inv11 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC882_def inv11_def R11_def always2_def always_def previous_ex_def)
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