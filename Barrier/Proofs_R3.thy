theory Proofs_R3
  imports ExtraInv_R3 Requirements
begin

definition inv3 where "inv3 s \<equiv> extraInv2 s \<and> R3 s"

theorem "VC1 inv3 s0"
  apply(unfold VC1_def inv3_def R3_def P6_2_def always2_def always_def weak_until_def previous_ex_def)
  using extra1 VC1_def apply auto
  done

theorem "VC2 inv3 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC2_def inv3_def R3_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra2 VC2_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv2_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P6_2_einv2req)
  done

theorem "VC3 inv3 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC3_def inv3_def R3_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra3 VC3_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv2_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P6_2_einv2req)
  done

theorem "VC4 inv3 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC4_def inv3_def R3_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra4 VC4_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv2_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P6_2_einv2req)
  done

theorem "VC14 inv3 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC14_def inv3_def R3_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra14 VC14_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv2_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P6_2_einv2req)
  done

theorem "VC15 inv3 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC15_def inv3_def R3_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra15 VC15_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv2_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P6_2_einv2req)
  done

theorem "VC16 inv3 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC16_def inv3_def R3_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra16 VC16_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv2_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P6_2_einv2req)
  done

theorem "VC17 inv3 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC17_def inv3_def R3_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra17 VC17_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv2_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P6_2_einv2req)
  done

theorem "VC18 inv3 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC18_def inv3_def R3_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra18 VC18_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv2_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P6_2_einv2req)
  done

theorem "VC19 inv3 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC19_def inv3_def R3_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra19 VC19_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv2_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P6_2_einv2req)
  done

theorem "VC20 inv3 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC20_def inv3_def R3_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra20 VC20_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv2_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P6_2_einv2req)
  done

theorem "VC21 inv3 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC21_def inv3_def R3_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra21 VC21_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv2_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P6_2_einv2req)
  done

theorem "VC22 inv3 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC22_def inv3_def R3_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra22 VC22_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv2_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P6_2_einv2req)
  done

theorem "VC23 inv3 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC23_def inv3_def R3_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra23 VC23_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv2_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P6_2_einv2req)
  done

theorem "VC24 inv3 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC24_def inv3_def R3_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra24 VC24_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv2_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P6_2_einv2req)
  done

end