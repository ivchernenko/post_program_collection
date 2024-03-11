theory Proofs_R2
  imports commonExtraInv Requirements
begin

definition inv2 where "inv2 s \<equiv> R2 s \<and> commonExtraInv s"

theorem "VC1 R2 s0"
  apply(unfold VC1_def R2_def)
  apply auto
  done

theorem  "VC182 inv2 env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC182_def inv2_def R2_def)
  apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)+
   apply auto[1]
  using cei182 VC182_def apply auto
  done

theorem  "VC362 inv2 env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC362_def inv2_def R2_def)
  apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)+
   apply auto[1]
  using cei362 VC362_def apply auto
  done

theorem  "VC542 inv2 env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC542_def inv2_def R2_def)
  apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)+
   apply auto[1]
  using cei542 VC542_def apply auto
  done

theorem  "VC722 inv2 env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC722_def inv2_def R2_def)
  apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)+
   apply auto[1]
  using cei722 VC722_def apply auto
  done

theorem  "VC902 inv2 env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC902_def inv2_def R2_def)
  apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)+
   apply auto[1]
  using cei902 VC902_def apply auto
  done

theorem  "VC1262 inv2 env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1262_def inv2_def R2_def)
  apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)+
   apply auto[1]
  using cei1262 VC1262_def apply auto
  done

theorem  "VC1622 inv2 env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1622_def inv2_def R2_def)
  apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)+
   apply auto[1]
  using cei1622 VC1622_def apply auto
  done

theorem  "VC1802 inv2 env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1802_def inv2_def R2_def)
  apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)+
   apply auto[1]
  using cei1802 VC1802_def apply auto
  done

end