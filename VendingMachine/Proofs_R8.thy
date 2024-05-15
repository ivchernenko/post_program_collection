theory Proofs_R8
  imports Requirements CommonExtraInv
begin

definition inv8 where "inv8 s \<equiv> R8 s \<and> commonExtraInv s"

theorem "VC1 inv8 s0"
  apply(unfold VC1_def inv8_def R8_def commonExtraInv_def always2_2_def always2_def  always_def
previous_ex_def  previous_all_def)
  apply auto
  done

theorem  "VC9 inv8 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC9_def inv8_def R8_def always2_2_def always2_def always_def previous_ex_def previous_all_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei9 apply(( simp add: VC9_def)[1];blast)
  done

theorem  "VC72 inv8 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC72_def inv8_def R8_def always2_2_def always2_def always_def previous_ex_def previous_all_def)
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

theorem  "VC135 inv8 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC135_def inv8_def R8_def always2_2_def always2_def always_def previous_ex_def previous_all_def)
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

theorem  "VC234 inv8 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC234_def inv8_def R8_def always2_2_def always2_def always_def previous_ex_def previous_all_def)
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

theorem  "VC315 inv8 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC315_def inv8_def R8_def always2_2_def always2_def always_def previous_ex_def previous_all_def)
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

theorem  "VC153 inv8 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC153_def inv8_def R8_def always2_2_def always2_def always_def previous_ex_def previous_all_def)
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

theorem  "VC324 inv8 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC324_def inv8_def R8_def always2_2_def always2_def always_def previous_ex_def previous_all_def)
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

theorem  "VC333 inv8 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC333_def inv8_def R8_def always2_2_def always2_def always_def previous_ex_def previous_all_def)
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

theorem  "VC342 inv8 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC342_def inv8_def R8_def always2_2_def always2_def always_def previous_ex_def previous_all_def)
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

theorem  "VC351 inv8 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC351_def inv8_def R8_def always2_2_def always2_def always_def previous_ex_def previous_all_def)
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

theorem  "VC360 inv8 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC360_def inv8_def R8_def always2_2_def always2_def always_def previous_ex_def previous_all_def)
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

theorem  "VC369 inv8 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC369_def inv8_def R8_def always2_2_def always2_def always_def previous_ex_def previous_all_def)
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

theorem  "VC378 inv8 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC378_def inv8_def R8_def always2_2_def always2_def always_def previous_ex_def previous_all_def)
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

theorem  "VC387 inv8 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC387_def inv8_def R8_def always2_2_def always2_def always_def previous_ex_def previous_all_def)
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

theorem  "VC396 inv8 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC396_def inv8_def R8_def always2_2_def always2_def always_def previous_ex_def previous_all_def)
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

theorem  "VC405 inv8 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC405_def inv8_def R8_def always2_2_def always2_def always_def previous_ex_def previous_all_def)
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

theorem  "VC738 inv8 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC738_def inv8_def R8_def always2_2_def always2_def always_def previous_ex_def previous_all_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei738 apply(simp add: VC738_def)
  by blast

theorem  "VC747 inv8 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC747_def inv8_def R8_def always2_2_def always2_def always_def previous_ex_def previous_all_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei747 apply(simp add: VC747_def)
  by blast

theorem  "VC756 inv8 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC756_def inv8_def R8_def always2_2_def always2_def always_def previous_ex_def previous_all_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei756 apply(simp add: VC756_def)
  by blast

theorem  "VC765 inv8 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC765_def inv8_def R8_def always2_2_def always2_def always_def previous_ex_def previous_all_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei765 apply((simp add: VC765_def);blast)
  done

theorem  "VC774 inv8 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC774_def inv8_def R8_def always2_2_def always2_def always_def previous_ex_def previous_all_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply(force+)?
    done
  using cei774 apply((simp add: VC774_def);blast)
  done

theorem  "VC783 inv8 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC783_def inv8_def R8_def always2_2_def always2_def always_def previous_ex_def previous_all_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei783 apply((simp add: VC783_def);blast)
  done

theorem  "VC792 inv8 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC792_def inv8_def R8_def always2_2_def always2_def always_def previous_ex_def previous_all_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei792 apply((simp add: VC792_def);blast)
  done

theorem  "VC801 inv8 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC801_def inv8_def R8_def always2_2_def always2_def always_def previous_ex_def previous_all_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei801 apply((simp add: VC801_def);blast)
  done

theorem  "VC810 inv8 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC810_def inv8_def R8_def always2_2_def always2_def always_def previous_ex_def previous_all_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei810 apply((simp add: VC810_def);blast)
  done

theorem  "VC639 inv8 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC639_def inv8_def R8_def always2_2_def always2_def always_def previous_ex_def previous_all_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei639 apply((simp add: VC639_def);blast)
  done

theorem  "VC882 inv8 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC882_def inv8_def R8_def always2_2_def always2_def always_def previous_ex_def previous_all_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei882 apply((simp add: VC882_def);blast)
  done

theorem  "VC963 inv8 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC963_def inv8_def R8_def always2_2_def always2_def always_def previous_ex_def previous_all_def)
  apply(rule impI)
  apply(rule conjI)
  subgoal
   apply(unfold commonExtraInv_def)[1]
    apply(erule conjE)+
    apply auto
    using substate_toEnvNum_id[of _ s0] apply (force+)?
    done
  using cei963 apply((simp add: VC963_def);blast)
  done

end
    