theory Proofs_R13a
  imports ExtraInv_R13a Requirements
begin

definition inv13a where "inv13a s \<equiv> extraInv s \<and> R13a s"

theorem "VC1 R13a s0"
  apply(unfold VC1_def R13a_def P4_def)
  by auto

theorem  "VC53 inv13a env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC53_def inv13a_def R13a_def)
   apply(rule impI)
   apply(rule context_conjI)
  using extra53 apply(auto simp add: VC53_def)[1]
apply(rule conjI)
    apply simp
  apply(erule conjE)
     apply(unfold extraInv_def commonExtraInv_def)
    apply(erule conjE)+
    apply(auto simp add: Pattern4_Def.einv2req2)
    done

   

