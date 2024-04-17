theory Proofs_R7
  imports ExtraInv_r7 Requirements
begin

definition inv7 where "inv7 s \<equiv> extraInv s \<and> R7 s"

theorem extra1: "VC1 extraInv s0"
  apply(unfold VC1_def extraInv_def commonExtraInv_def P5_1inv_def always_def constrained_always_inv_def)
  apply auto
  done

theorem extra2: "VC2 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
apply(unfold VC2_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei2 VC2_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule P5_1_rule)
   apply(auto split: if_splits)
  done

theorem extra3: "VC3 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
apply(unfold VC3_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei3 VC3_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule P5_1_rule)
   apply(auto split: if_splits)
  done

theorem extra14: "VC14 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
apply(unfold VC14_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei14 VC14_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule P5_1_rule)
   apply(auto split: if_splits)
  done

theorem extra15: "VC15 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
apply(unfold VC15_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei15 VC15_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule P5_1_rule)
   apply(auto split: if_splits)
  done

theorem extra16: "VC16 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
apply(unfold VC16_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei16 VC16_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule P5_1_rule)
   apply(auto split: if_splits)
  done

theorem extra17: "VC17 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
apply(unfold VC17_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei17 VC17_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule P5_1_rule)
   apply(auto split: if_splits)
  done

theorem extra18: "VC18 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
apply(unfold VC18_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei18 VC18_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule P5_1_rule)
   apply(auto split: if_splits)
  done

theorem extra19: "VC19 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
apply(unfold VC19_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei19 VC19_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule P5_1_rule)
   apply(auto split: if_splits)
  done

theorem extra20: "VC20 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
apply(unfold VC20_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei20 VC20_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule P5_1_rule)
   apply(auto split: if_splits)
  done

theorem extra21: "VC21 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
apply(unfold VC21_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei21 VC21_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule P5_1_rule)
   apply(auto split: if_splits)
  done

theorem extra22: "VC22 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
apply(unfold VC22_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei22 VC22_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule P5_1_rule)
   apply(auto split: if_splits)
  done

theorem extra23: "VC23 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
apply(unfold VC23_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei23 VC23_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule P5_1_rule)
   apply(auto split: if_splits)
  done

theorem extra24: "VC24 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
apply(unfold VC24_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei24 VC24_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule P5_1_rule)
   apply(auto split: if_splits)
  done

theorem extra25: "VC25 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
apply(unfold VC25_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei25 VC25_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule P5_1_rule)
   apply(auto split: if_splits)
  done

theorem extra26: "VC26 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
apply(unfold VC26_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei26 VC26_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule P5_1_rule)
   apply(auto split: if_splits)
  done

theorem extra27: "VC27 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
apply(unfold VC27_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei27 VC27_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule P5_1_rule)
   apply(auto split: if_splits)
  done

theorem extra28: "VC28 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
apply(unfold VC28_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei28 VC28_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule P5_1_rule)
   apply(auto split: if_splits)
  done

theorem extra29: "VC29 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
apply(unfold VC29_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei29 VC29_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule P5_1_rule)
   apply(auto split: if_splits)
  done

theorem extra30: "VC30 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
apply(unfold VC30_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei30 VC30_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule P5_1_rule)
   apply(auto split: if_splits)
  done

theorem extra31: "VC31 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
apply(unfold VC31_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei31 VC31_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule P5_1_rule)
   apply(auto split: if_splits)
  done

theorem extra32: "VC32 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
apply(unfold VC32_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei32 VC32_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule P5_1_rule)
   apply(auto split: if_splits)
  done

theorem extra33: "VC33 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
apply(unfold VC33_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei33 VC33_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule P5_1_rule)
   apply(auto split: if_splits)
  done

theorem extra34: "VC34 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
apply(unfold VC34_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei34 VC34_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule P5_1_rule)
   apply(auto split: if_splits)
  done

theorem extra35: "VC35 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
apply(unfold VC35_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei35 VC35_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule P5_1_rule)
   apply(auto split: if_splits)
  done

theorem extra36: "VC36 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
apply(unfold VC36_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei36 VC36_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule P5_1_rule)
   apply(auto split: if_splits)
  done

theorem  "VC2 inv7 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC2_def inv7_def R7_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra2 VC2_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: P5_1_einv2req)
  done

theorem  "VC3 inv7 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC3_def inv7_def R7_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra3 VC3_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: P5_1_einv2req)
  done

theorem  "VC14 inv7 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC14_def inv7_def R7_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra14 VC14_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: P5_1_einv2req)
  done

theorem  "VC15 inv7 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC15_def inv7_def R7_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra15 VC15_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: P5_1_einv2req)
  done

theorem  "VC16 inv7 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC16_def inv7_def R7_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra16 VC16_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: P5_1_einv2req)
  done

theorem  "VC17 inv7 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC17_def inv7_def R7_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra17 VC17_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: P5_1_einv2req)
  done

theorem  "VC18 inv7 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC18_def inv7_def R7_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra18 VC18_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: P5_1_einv2req)
  done

theorem  "VC19 inv7 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC19_def inv7_def R7_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra19 VC19_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: P5_1_einv2req)
  done

theorem  "VC20 inv7 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC20_def inv7_def R7_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra20 VC20_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: P5_1_einv2req)
  done

theorem  "VC21 inv7 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC21_def inv7_def R7_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra21 VC21_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: P5_1_einv2req)
  done

theorem  "VC22 inv7 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC22_def inv7_def R7_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra22 VC22_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: P5_1_einv2req)
  done

theorem  "VC23 inv7 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC23_def inv7_def R7_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra23 VC23_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: P5_1_einv2req)
  done

theorem  "VC24 inv7 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC24_def inv7_def R7_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra24 VC24_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: P5_1_einv2req)
  done

theorem  "VC25 inv7 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC25_def inv7_def R7_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra25 VC25_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: P5_1_einv2req)
  done

theorem  "VC26 inv7 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC26_def inv7_def R7_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra26 VC26_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: P5_1_einv2req)
  done

theorem  "VC27 inv7 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC27_def inv7_def R7_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra27 VC27_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: P5_1_einv2req)
  done

theorem  "VC28 inv7 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC28_def inv7_def R7_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra28 VC28_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: P5_1_einv2req)
  done

theorem  "VC29 inv7 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC29_def inv7_def R7_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra29 VC29_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: P5_1_einv2req)
  done

theorem  "VC30 inv7 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC30_def inv7_def R7_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra30 VC30_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: P5_1_einv2req)
  done

theorem  "VC31 inv7 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC31_def inv7_def R7_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra31 VC31_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: P5_1_einv2req)
  done

theorem  "VC32 inv7 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC32_def inv7_def R7_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra32 VC32_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: P5_1_einv2req)
  done

theorem  "VC33 inv7 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC33_def inv7_def R7_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra33 VC33_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: P5_1_einv2req)
  done

theorem  "VC34 inv7 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC34_def inv7_def R7_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra34 VC34_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: P5_1_einv2req)
  done

theorem  "VC35 inv7 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC35_def inv7_def R7_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra35 VC35_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: P5_1_einv2req)
  done

theorem  "VC36 inv7 env s0 carInFront'value peCarUnder'value opened'value closed'value"
  apply(unfold VC36_def inv7_def R7_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra36 VC36_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add: P5_1_einv2req)
  done

end