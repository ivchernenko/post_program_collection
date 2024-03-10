theory Proofs_R8
  imports Requirements ExtraInv_R8
begin

definition inv8 where "inv8 s \<equiv> extraInv s \<and> R8_1 s"

theorem "VC1 inv8 s0"
  apply(unfold VC1_def inv8_def R8_1_def P6_def P12op_def)
  using extra1 VC1_def apply auto
  done

theorem  "VC182 inv8 env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC182_def inv8_def R8_1_def)
   apply(rule impI)
  apply(rule conjI)
  using extra182 apply(auto simp add: VC182_def)[1] 
  apply(rule conjI)
  apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply simp
  done

theorem  "VC362 inv8 env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC362_def inv8_def R8_1_def)
   apply(rule impI)
  apply(rule conjI)
  using extra362 apply(auto simp add: VC362_def)[1] 
  apply(rule conjI)
  apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply simp
  done

theorem  "VC542 inv8 env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC542_def inv8_def R8_1_def)
   apply(rule impI)
  apply(rule conjI)
  using extra542 apply(auto simp add: VC542_def)[1] 
  apply(rule conjI)
  apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply simp
  done

theorem  "VC722 inv8 env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC722_def inv8_def R8_1_def)
   apply(rule impI)
  apply(rule context_conjI)
  using extra722 apply(auto simp add: VC722_def)[1]
  apply(rule conjI)
  apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply simp
  apply(rule Pattern6_Def.einv2req1)
  apply auto
  done

theorem  "VC902 inv8 env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC902_def inv8_def R8_1_def)
   apply(rule impI)
  apply(rule context_conjI)
  using extra902 apply(auto simp add: VC902_def)[1]
  apply(rule conjI)
  apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply simp
  done

theorem  "VC1262 inv8 env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1262_def inv8_def R8_1_def)
   apply(rule impI)
  apply(rule context_conjI)
  using extra1262 apply(auto simp add: VC1262_def)[1]
  apply(rule conjI)
  apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply simp
  apply(rule Pattern6_Def.einv2req1)
  apply auto
  done

theorem  "VC1622 inv8 env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1622_def inv8_def R8_1_def)
   apply(rule impI)
  apply(rule context_conjI)
  using extra1622 apply(auto simp add: VC1622_def)[1]
  apply(rule conjI)
  apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply simp
  apply(rule Pattern6_Def.einv2req1)
  apply auto
  done

theorem  "VC1802 inv8 env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1802_def inv8_def R8_1_def)
   apply(rule impI)
  apply(rule context_conjI)
  using extra1802 apply(auto simp add: VC1802_def)[1]
  apply(rule conjI)
  apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply simp
   apply(rule Pattern6_Def.einv2req1)
  apply auto
  done

end
