theory Proofs_R9
  imports ExtraInv_R9 Requirements
begin

definition inv9 where "inv9 s \<equiv> extraInv s \<and> R9 s"

theorem "VC1 inv9 s0"
  apply(unfold VC1_def inv9_def R9_def P6_def)
  using extra1 VC1_def apply auto
  done

theorem extra182: "VC182 inv9 env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC182_def inv9_def R9_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra182 VC182_def apply auto[1]
apply(rule conjI)
    apply simp
  apply(erule conjE)
     apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(rule Pattern6_Def.einv2req1)
  apply auto
  done

theorem extra542: "VC542 inv9 env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC542_def inv9_def R9_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra542 VC542_def apply auto[1]
apply(rule conjI)
    apply simp
  apply(erule conjE)
     apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply simp
  done

theorem extra722: "VC722 inv9 env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC722_def inv9_def R9_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra722 VC722_def apply auto[1]
  apply(rule conjI)
    apply simp
  apply(erule conjE)
     apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply simp
  apply(rule Pattern6_Def.einv2req1)
  apply auto
  done

theorem extra902: "VC902 inv9 env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC902_def inv9_def R9_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra902 VC902_def apply auto[1]
  apply(rule conjI)
    apply simp
  apply(erule conjE)
     apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply simp
  done

theorem extra1262: "VC1262 inv9 env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1262_def inv9_def R9_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra1262 VC1262_def apply auto[1]
 apply(rule conjI)
    apply simp
  apply(erule conjE)
     apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply simp
  apply(rule Pattern6_Def.einv2req1)
  apply auto
  done

theorem extra1622: "VC1622 inv9 env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1622_def inv9_def R9_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra1622 VC1622_def apply auto[1]
  apply(rule conjI)
    apply simp
  apply(erule conjE)
     apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply simp
  apply(rule Pattern6_Def.einv2req1)
  apply auto
  done

theorem extra1802: "VC1802 inv9 env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1802_def inv9_def R9_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra1802 VC1802_def apply auto[1]
  apply(rule conjI)
    apply simp
  apply(erule conjE)
     apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply simp
  apply(rule Pattern6_Def.einv2req1)
  apply auto
  done

end
