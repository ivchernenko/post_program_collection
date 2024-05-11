theory Proofs_R3
  imports ExtraInv_R3 Requirements
begin

definition inv3 where "inv3 s \<equiv> extraInv s \<and> R3 s"

lemmas einv_rule = P6_5_rule
lemmas req_rule = P6_5_einv2req

theorem extra1: "VC1 extraInv s0"
  apply(unfold VC1_def extraInv_def commonExtraInv_def P6_5inv_def P6_2inv_def always2_inv_def weak_until_inv_def
always_def previous_ex_def)
  apply auto
  done

theorem extra9: "VC9 extraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
apply(unfold VC9_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei9 apply((auto simp add: VC9_def)[1];fastforce)
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule einv_rule)
   apply(auto split: if_splits)
  done

theorem extra72: "VC72 extraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
apply(unfold VC72_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei72 apply((auto simp add: VC72_def)[1];fastforce)
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule einv_rule)
   apply(auto split: if_splits)
  done