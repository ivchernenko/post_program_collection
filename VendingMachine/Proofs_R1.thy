theory Proofs_R1
  imports ExtraInv_R1 Requirements
begin

definition inv1 where "inv1 s \<equiv> extraInv s \<and> R1 s"

lemmas einv_rule = P6_4_rule
lemmas req_rule = P6_4_einv2req

theorem extra1: "VC1 extraInv s0"
  apply(unfold VC1_def extraInv_def commonExtraInv_def P6_4inv_def P6_3inv_def always2_inv_def weak_until_inv_def
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
  using cei72 apply(auto simp add: VC72_def;blast)
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule einv_rule)
   apply(auto split: if_splits)
  done

theorem extra153: "VC153 extraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
apply(unfold VC153_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei153 apply(auto simp add: VC153_def;blast)
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule einv_rule)
   apply(auto split: if_splits)
  done

theorem extra234: "VC234 extraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
apply(unfold VC234_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei234 apply(auto simp add: VC234_def;blast)
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule einv_rule)
   apply(auto split: if_splits)
  done

theorem extra315: "VC315 extraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
apply(unfold VC315_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei315 apply(auto simp add: VC315_def;blast)
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule einv_rule)
   apply(auto split: if_splits)
  done

theorem extra324: "VC324 extraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
apply(unfold VC324_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei324 apply(auto simp add: VC324_def;blast)
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule einv_rule)
   apply(auto split: if_splits)
  done

theorem extra333: "VC333 extraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
apply(unfold VC333_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei333 apply(auto simp add: VC333_def;blast)
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule einv_rule)
   apply(auto split: if_splits)
  done

theorem extra342: "VC342 extraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
apply(unfold VC342_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei342 apply(auto simp add: VC342_def;blast)
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule einv_rule)
   apply(auto split: if_splits)
  done

theorem extra351: "VC351 extraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
apply(unfold VC351_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei351 apply(auto simp add: VC351_def;blast)
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule einv_rule)
   apply(auto split: if_splits)
  done

theorem extra360: "VC360 extraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
apply(unfold VC360_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei360 apply(auto simp add: VC360_def;blast)
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule einv_rule)
   apply(auto split: if_splits)
  done

theorem extra369: "VC369 extraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
apply(unfold VC369_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei369 apply(auto simp add: VC369_def;blast)
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule einv_rule)
   apply(auto split: if_splits)
  done

theorem extra378: "VC378 extraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
apply(unfold VC378_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei378 apply(auto simp add: VC378_def;blast)
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule einv_rule)
   apply(auto split: if_splits)
  done

theorem extra387: "VC387 extraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
apply(unfold VC387_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei387 apply(auto simp add: VC387_def;blast)
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule einv_rule)
   apply(auto split: if_splits)
  done

theorem extra396: "VC396 extraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
apply(unfold VC396_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei396 apply(auto simp add: VC396_def;blast)
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule einv_rule)
   apply(auto split: if_splits)
  done

theorem extra405: "VC405 extraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
apply(unfold VC405_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei405 apply(auto simp add: VC405_def;blast)
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule einv_rule)
   apply(auto split: if_splits)
  done

theorem extra738: "VC738 extraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
apply(unfold VC738_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei738 apply((auto simp add: VC738_def)[1];fastforce)
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule einv_rule)
   apply(auto split: if_splits)
  done

theorem extra747: "VC747 extraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
apply(unfold VC747_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei747 apply((auto simp add: VC747_def)[1];fastforce)
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule einv_rule)
   apply(auto split: if_splits)
  done

theorem extra756: "VC756 extraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
apply(unfold VC756_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei756 apply((auto simp add: VC756_def)[1];fastforce)
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule einv_rule)
   apply(auto split: if_splits)
  done

theorem extra765: "VC765 extraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
apply(unfold VC765_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei765 apply((auto simp add: VC765_def)[1];fastforce)
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule einv_rule)
   apply(auto split: if_splits)
  done

theorem extra774: "VC774 extraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
apply(unfold VC774_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei774 apply((auto simp add: VC774_def)[1];fastforce)
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule einv_rule)
   apply(auto split: if_splits)
  done

theorem extra783: "VC783 extraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
apply(unfold VC783_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei783 apply((auto simp add: VC783_def)[1];fastforce)
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule einv_rule)
   apply(auto split: if_splits)
  done

theorem extra792: "VC792 extraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
apply(unfold VC792_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei792 apply((auto simp add: VC792_def)[1];fastforce)
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule einv_rule)
   apply(auto split: if_splits)
  done

theorem extra801: "VC801 extraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
apply(unfold VC801_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei801 apply((auto simp add: VC801_def)[1];fastforce)
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule einv_rule)
   apply(auto split: if_splits)
  done

theorem extra810: "VC810 extraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
apply(unfold VC810_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei810 apply((auto simp add: VC810_def)[1];fastforce)
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule einv_rule)
   apply(auto split: if_splits)
  done

theorem  "VC1 inv1 s0"
  apply(unfold VC1_def inv1_def R1_def  P6_4_def P6_3_def always2_def weak_until_def
always_def previous_ex_def)
  using extra1 VC1_def apply auto
  done

theorem  "VC72 inv1 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC72_def inv1_def R1_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra72 VC72_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: req_rule)
  done

theorem  "VC153 inv1 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC153_def inv1_def R1_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra153 VC153_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: req_rule)
  done

theorem  "VC234 inv1 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC234_def inv1_def R1_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra234 VC234_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: req_rule)
  done


theorem  "VC315 inv1 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC315_def inv1_def R1_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra315 VC315_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: req_rule)
  done

theorem  "VC324 inv1 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC324_def inv1_def R1_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra324 VC324_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: req_rule)
  done

theorem  "VC333 inv1 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC333_def inv1_def R1_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra333 VC333_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: req_rule)
  done

theorem  "VC342 inv1 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC342_def inv1_def R1_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra342 VC342_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: req_rule)
  done


theorem  "VC351 inv1 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC351_def inv1_def R1_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra351 VC351_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: req_rule)
  done

theorem  "VC360 inv1 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC360_def inv1_def R1_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra360 VC360_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: req_rule)
  done

theorem  "VC369 inv1 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC369_def inv1_def R1_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra369 VC369_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: req_rule)
  done


theorem  "VC378 inv1 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC378_def inv1_def R1_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra378 VC378_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: req_rule)
  done

theorem  "VC387 inv1 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC387_def inv1_def R1_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra387 VC387_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: req_rule)
  done

theorem  "VC396 inv1 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC396_def inv1_def R1_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra396 VC396_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: req_rule)
  done

theorem  "VC405 inv1 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC405_def inv1_def R1_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra405 VC405_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: req_rule)
  done

theorem  "VC738 inv1 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC738_def inv1_def R1_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra738 apply((auto simp add: VC738_def)[1];fastforce)
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: req_rule)
  done

theorem  "VC747 inv1 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC747_def inv1_def R1_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra747 apply((auto simp add: VC747_def)[1];fastforce)
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: req_rule)
  done

theorem  "VC756 inv1 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC756_def inv1_def R1_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra756 apply((auto simp add: VC756_def)[1];fastforce)
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: req_rule)
  done

theorem  "VC765 inv1 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC765_def inv1_def R1_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra765 apply((auto simp add: VC765_def)[1];fastforce)
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: req_rule)
  done

theorem  "VC774 inv1 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC774_def inv1_def R1_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra774 apply((auto simp add: VC774_def)[1];fastforce)
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: req_rule)
  done

theorem  "VC783 inv1 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC783_def inv1_def R1_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra783 apply((auto simp add: VC783_def)[1];fastforce)
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: req_rule)
  done

theorem  "VC792 inv1 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC792_def inv1_def R1_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra792 apply((auto simp add: VC792_def)[1];fastforce)
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: req_rule)
  done

theorem  "VC801 inv1 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC801_def inv1_def R1_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra801 apply((auto simp add: VC801_def)[1];fastforce)
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: req_rule)
  done

theorem  "VC810 inv1 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC810_def inv1_def R1_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra810 apply((auto simp add: VC810_def)[1];fastforce)
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: req_rule)
  done

end
