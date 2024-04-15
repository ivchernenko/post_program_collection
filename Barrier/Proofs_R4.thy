theory Proofs_R4
  imports ExtraInv_r4
begin

definition inv4 where "inv4 s \<equiv> extraInv s \<and> R4 s"

theorem "VC1 inv4 s0"
  apply(unfold VC1_def inv4_def R4_def R4Pattern_def P1'_def always_def constrained_until_def previous_all_def previous_ex_def)
  using extra1 VC1_def apply auto
  done

theorem  "VC2 inv4 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC2_def inv4_def R4_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra2 VC2_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: R4Pattern_einv2req)
  done

theorem  "VC3 inv4 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC3_def inv4_def R4_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra3 VC3_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: R4Pattern_einv2req)
  done

theorem  "VC14 inv4 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC14_def inv4_def R4_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra14 VC14_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: R4Pattern_einv2req)
  done

theorem  "VC15 inv4 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC15_def inv4_def R4_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra15 VC15_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: R4Pattern_einv2req)
  done

theorem  "VC16 inv4 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC16_def inv4_def R4_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra16 VC16_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: R4Pattern_einv2req)
  done

theorem  "VC17 inv4 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC17_def inv4_def R4_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra17 VC17_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: R4Pattern_einv2req)
  done

theorem  "VC18 inv4 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC18_def inv4_def R4_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra18 VC18_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: R4Pattern_einv2req)
  done

theorem  "VC19 inv4 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC19_def inv4_def R4_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra19 VC19_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: R4Pattern_einv2req)
  done

theorem  "VC20 inv4 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC20_def inv4_def R4_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra20 VC20_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: R4Pattern_einv2req)
  done

theorem  "VC21 inv4 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC21_def inv4_def R4_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra21 VC21_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: R4Pattern_einv2req)
  done

theorem  "VC22 inv4 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC22_def inv4_def R4_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra22 VC22_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: R4Pattern_einv2req)
  done

theorem  "VC23 inv4 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC23_def inv4_def R4_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra23 VC23_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: R4Pattern_einv2req)
  done

theorem  "VC24 inv4 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC24_def inv4_def R4_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra24 VC24_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: R4Pattern_einv2req)
  done

theorem  "VC25 inv4 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC25_def inv4_def R4_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra25 VC25_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: R4Pattern_einv2req)
  done

theorem  "VC26 inv4 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC26_def inv4_def R4_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra26 VC26_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: R4Pattern_einv2req)
  done

theorem  "VC27 inv4 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC27_def inv4_def R4_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra27 VC27_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: R4Pattern_einv2req)
  done

theorem  "VC28 inv4 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC28_def inv4_def R4_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra28 VC28_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: R4Pattern_einv2req)
  done

theorem  "VC29 inv4 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC29_def inv4_def R4_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra29 VC29_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: R4Pattern_einv2req)
  done

theorem  "VC30 inv4 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC30_def inv4_def R4_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra30 VC30_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: R4Pattern_einv2req)
  done

theorem  "VC31 inv4 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC31_def inv4_def R4_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra31 VC31_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: R4Pattern_einv2req)
  done

theorem  "VC32 inv4 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC32_def inv4_def R4_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra32 VC32_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: R4Pattern_einv2req)
  done

theorem  "VC33 inv4 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC33_def inv4_def R4_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra33 VC33_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: R4Pattern_einv2req)
  done

theorem  "VC34 inv4 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC34_def inv4_def R4_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra34 VC34_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: R4Pattern_einv2req)
  done

theorem  "VC35 inv4 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC35_def inv4_def R4_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra35 VC35_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: R4Pattern_einv2req)
  done

theorem  "VC36 inv4 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC36_def inv4_def R4_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra36 VC36_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: R4Pattern_einv2req)
  done

end