theory Proofs_R4
  imports CommonExtraInv Requirements
begin

definition inv4 where "inv4 s \<equiv> R4 s \<and> commonExtraInv s"

theorem "VC1 R4 s0"
  apply(unfold VC1_def R4_def)
  apply auto
  done

theorem  "VC182 inv4 env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC182_def inv4_def R4_def)
  apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)+
   apply auto[1]
  using cei182 VC182_def apply auto
  done

theorem  "VC362 inv4 env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC362_def inv4_def R4_def)
  apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)+
   apply auto[1]
  using cei362 VC362_def apply auto
  done

theorem  "VC542 inv4 env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC542_def inv4_def R4_def)
  apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)+
   apply auto[1]
  using cei542 VC542_def apply auto
  done

theorem  "VC722 inv4 env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC722_def inv4_def R4_def)
  apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)+
   apply auto[1]
  using cei722 VC722_def apply auto
  done

theorem  "VC902 inv4 env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC902_def inv4_def R4_def)
  apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)+
   apply auto[1]
  using cei902 VC902_def apply auto
  done

theorem  "VC1262 inv4 env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1262_def inv4_def R4_def)
  apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)+
   apply auto[1]
  using cei1262 VC1262_def apply auto
  done

theorem  "VC1622 inv4 env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1622_def inv4_def R4_def)
  apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)+
   apply auto[1]
  using cei1622 VC1622_def apply auto
  done

theorem  "VC1802 inv4 env s0 onOff'value startButton'value rollerButton'value vibrationButton'value buttonUp'value buttonDown'value
 upper'value lower'value"
  apply(unfold VC1802_def inv4_def R4_def)
  apply(rule impI)
  apply(rule conjI)
   apply(unfold commonExtraInv_def)[1]
   apply(erule conjE)+
   apply auto[1]
  using cei1802 VC1802_def apply auto
  done

end