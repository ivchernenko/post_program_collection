theory Proofs_R7
  imports ExtraInv_R7 Requirements
begin

definition inv7 where "inv7 s \<equiv> extraInv s \<and> R7_1 s"

lemma "VC1 inv7 s0"
  apply(unfold VC1_def inv7_def R7_1_def extraInv_def commonExtraInv_def  P12inv_def P2_def P12op_def consecutive_def)
  apply auto
  done

theorem  "VC2 inv7 env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC2_def inv7_def R7_1_def)
  by simp

theorem  "VC182 inv7 env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC182_def inv7_def R7_1_def)
  apply(rule impI)
  apply(rule conjI)
  using extra182 apply(auto simp add: VC182_def)[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply simp
  done

theorem  "VC362 inv7 env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC362_def inv7_def R7_1_def)
  apply(rule impI)
  apply(rule conjI)
  using extra362 apply(auto simp add: VC362_def)[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply simp
  done

theorem  "VC542 inv7 env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC542_def inv7_def R7_1_def)
  apply(rule impI)
  apply(rule conjI)
  using extra542 apply(auto simp add: VC542_def)[1]
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply simp
  done

theorem  "VC722 inv7 env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC722_def inv7_def R7_1_def)
  apply(rule impI)
  apply(rule conjI)
  using extra722 apply(auto simp add: VC722_def)[1]
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply simp
  apply(rule P2_rule[of s0])
    apply(simp_all add: consecutive_def)
  apply(rule Pattern12_Def.einv2req_neg)
   apply auto
  done

theorem  "VC902 inv7 env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC902_def inv7_def R7_1_def)
  apply(rule impI)
  apply(rule conjI)
  using extra902 apply(auto simp add: VC902_def)[1]
  apply(rule conjI)
  apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply simp
  done

theorem  "VC1082 inv7 env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1082_def inv7_def R7_1_def)
  apply simp
  done

theorem  "VC1262 inv7 env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1262_def inv7_def R7_1_def)
  apply(rule impI)
  apply(rule conjI)
  using extra1262 apply(auto simp add: VC1262_def)[1]
  apply(rule conjI)
  apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply simp
  apply(rule P2_rule[of s0])
    apply(simp_all add: consecutive_def)
  apply(rule Pattern12_Def.einv2req_neg)
   apply auto
  done

theorem  "VC1622 inv7 env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1622_def inv7_def R7_1_def)
   apply(rule impI)
  apply(rule conjI)
  using extra1622 apply(auto simp add: VC1622_def)[1] 
  apply(rule conjI)
  apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply simp
  apply(rule P2_rule[of s0])
    apply(auto simp add: consecutive_def)
  apply(rule Pattern12_Def.einv2req_imp)
    apply auto
  done

theorem  "VC1802 inv7 env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1802_def inv7_def R7_1_def)
   apply(rule impI)
  apply(rule conjI)
  using extra1802 apply(auto simp add: VC1802_def)[1] 
  apply(rule conjI)
  apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply simp
  apply(rule P2_rule[of s0])
    apply(simp_all add: consecutive_def)
  done

end

