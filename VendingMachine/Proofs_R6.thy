theory Proofs_R6
  imports ExtraInv_R6 Requirements
begin

definition inv6 where "inv6 s \<equiv> extraInv s \<and> R6 s"

lemmas einv_rule = P4'inv_rule
lemmas req_rule = P4'_einv2req

theorem extra1: "VC1 extraInv s0"
  apply(unfold VC1_def extraInv_def commonExtraInv_def P4'inv_def always2_inv_def constrained_until_inv_def
always_def previous_ex_def)
  apply auto
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

theorem extra153: "VC153 extraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
apply(unfold VC153_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei153 apply((auto simp add: VC153_def)[1];fastforce)
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
  using cei234 apply((auto simp add: VC234_def)[1];fastforce)
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
  using cei315 apply((auto simp add: VC315_def)[1];fastforce)
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
  using cei324 apply((auto simp add: VC324_def)[1];fastforce)
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
  using cei333 apply((auto simp add: VC333_def)[1];fastforce)
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
  using cei342 apply((auto simp add: VC342_def)[1];fastforce)
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
  using cei351 apply((auto simp add: VC351_def)[1];fastforce)
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
  using cei360 apply((auto simp add: VC360_def)[1];fastforce)
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
  using cei369 apply((auto simp add: VC369_def)[1];fastforce)
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
  using cei378 apply((auto simp add: VC378_def)[1];fastforce)
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
  using cei387 apply((auto simp add: VC387_def)[1];fastforce)
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
  using cei396 apply((auto simp add: VC396_def)[1];fastforce)
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
  using cei405 apply((auto simp add: VC405_def)[1];fastforce)
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

theorem extra639: "VC639 extraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
apply(unfold VC639_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei639 apply((auto simp add: VC639_def)[1];fastforce)
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule einv_rule)
   apply(auto split: if_splits)
  done

theorem extra882: "VC882 extraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
apply(unfold VC882_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei882 apply((auto simp add: VC882_def)[1];fastforce)
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule einv_rule)
   apply(auto split: if_splits)
  done

theorem extra963: "VC963 extraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
apply(unfold VC963_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei963 apply((auto simp add: VC963_def)[1];fastforce)
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule einv_rule)
   apply(auto split: if_splits)
  done

theorem  "VC1 inv6 s0"
  apply(unfold VC1_def inv6_def R6_def P4'_def always2_def constrained_until_def
always_def previous_ex_def)
  using extra1 VC1_def  apply auto
  done

theorem  "VC72 inv6 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC72_def inv6_def R6_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra72 apply((auto simp add: VC72_def)[1];fastforce)
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
    apply(auto simp add: req_rule)
  done

theorem  "VC153 inv6 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC153_def inv6_def R6_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra153 apply((auto simp add: VC153_def)[1];fastforce)
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
    apply(auto simp add: req_rule)
  done

theorem  "VC153 inv6 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC153_def inv6_def R6_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra153 apply((auto simp add: VC153_def)[1];fastforce)
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
    apply(auto simp add: req_rule)
  done

theorem  "VC315 inv6 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC315_def inv6_def R6_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra315 apply((auto simp add: VC315_def)[1];fastforce)
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
    apply(auto simp add: req_rule)
  done

theorem  "VC324 inv6 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC324_def inv6_def R6_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra324 apply((auto simp add: VC324_def)[1];fastforce)
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
    apply(auto simp add: req_rule)
  done

theorem  "VC333 inv6 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC333_def inv6_def R6_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra333 apply((auto simp add: VC333_def)[1];fastforce)
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
    apply(auto simp add: req_rule)
  done

theorem  "VC342 inv6 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC342_def inv6_def R6_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra342 apply((auto simp add: VC342_def)[1];fastforce)
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
    apply(auto simp add: req_rule)
  done

theorem  "VC351 inv6 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC351_def inv6_def R6_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra351 apply((auto simp add: VC351_def)[1];fastforce)
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
    apply(auto simp add: req_rule)
  done

theorem  "VC360 inv6 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC360_def inv6_def R6_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra360 apply((auto simp add: VC360_def)[1];fastforce)
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
    apply(auto simp add: req_rule)
  done

theorem  "VC369 inv6 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC369_def inv6_def R6_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra369 apply((auto simp add: VC369_def)[1];fastforce)
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
    apply(auto simp add: req_rule)
  done

theorem  "VC378 inv6 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC378_def inv6_def R6_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra378 apply((auto simp add: VC378_def)[1];fastforce)
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
    apply(auto simp add: req_rule)
  done

theorem  "VC387 inv6 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC387_def inv6_def R6_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra387 apply((auto simp add: VC387_def)[1];fastforce)
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
    apply(auto simp add: req_rule)
  done

theorem  "VC396 inv6 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC396_def inv6_def R6_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra396 apply((auto simp add: VC396_def)[1];fastforce)
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
    apply(auto simp add: req_rule)
  done

theorem  "VC405 inv6 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC405_def inv6_def R6_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra405 apply((auto simp add: VC405_def)[1];fastforce)
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
    apply(auto simp add: req_rule)
  done

theorem  "VC738 inv6 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC738_def inv6_def R6_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra738 apply((auto simp add: VC738_def)[1];fastforce)
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
    apply(auto simp add: req_rule)
  done

theorem  "VC747 inv6 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC747_def inv6_def R6_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra747 apply((auto simp add: VC747_def)[1];fastforce)
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
    apply(auto simp add: req_rule)
  done

theorem  "VC756 inv6 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC756_def inv6_def R6_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra756 apply((auto simp add: VC756_def)[1];fastforce)
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
    apply(auto simp add: req_rule)
  done

theorem  "VC765 inv6 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC765_def inv6_def R6_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra765 apply((auto simp add: VC765_def)[1];fastforce)
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
    apply(auto simp add: req_rule)
  done

theorem  "VC774 inv6 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC774_def inv6_def R6_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra774 apply((auto simp add: VC774_def)[1];fastforce)
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
    apply(auto simp add: req_rule)
  done

theorem  "VC783 inv6 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC783_def inv6_def R6_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra783 apply((auto simp add: VC783_def)[1];fastforce)
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
    apply(auto simp add: req_rule)
  done

theorem  "VC792 inv6 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC792_def inv6_def R6_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra792 apply((auto simp add: VC792_def)[1];fastforce)
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
    apply(auto simp add: req_rule)
  done

theorem  "VC801 inv6 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC801_def inv6_def R6_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra801 apply((auto simp add: VC801_def)[1];fastforce)
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
    apply(auto simp add: req_rule)
  done

theorem  "VC810 inv6 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC810_def inv6_def R6_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra810 apply((auto simp add: VC810_def)[1];fastforce)
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
    apply(auto simp add: req_rule)
  done

theorem  "VC810 inv6 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC810_def inv6_def R6_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra810 apply((auto simp add: VC810_def)[1];fastforce)
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
    apply(auto simp add: req_rule)
  done

theorem  "VC810 inv6 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC810_def inv6_def R6_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra810 apply((auto simp add: VC810_def)[1];fastforce)
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
    apply(auto simp add: req_rule)
  done

theorem  "VC810 inv6 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC810_def inv6_def R6_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra810 apply((auto simp add: VC810_def)[1];fastforce)
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
    apply(auto simp add: req_rule)
  done

theorem  "VC639 inv6 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC639_def inv6_def R6_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra639 apply((auto simp add: VC639_def)[1];fastforce)
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
    apply(auto simp add: req_rule)
  done

theorem  "VC882 inv6 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC882_def inv6_def R6_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra882 apply((auto simp add: VC882_def)[1];fastforce)
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
    apply(auto simp add: req_rule)
  done

theorem  "VC963 inv6 env s0  button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value"
  apply(unfold VC963_def inv6_def R6_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra963 apply((auto simp add: VC963_def)[1];fastforce)
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
    apply(auto simp add: req_rule)
  done


end