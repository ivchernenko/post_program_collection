theory Proof_R6a_VC43
  imports ExtraInv_R6a_VC53
begin



 theorem proof43: "VC43 inv6a env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
   apply(unfold VC43_def inv6a_def R6a_def)
   apply(rule impI)
   apply(rule context_conjI)
   using extra43 apply(auto simp add: VC43_def)[1]
   apply(rule conjI)
    apply simp
   apply(unfold extraInv_def commonExtraInv_def)
   apply(erule conjE)
   apply(rule Pattern4_Def.einv2req)
   by auto

 theorem proof53: "VC53 inv6a env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
   apply(unfold VC53_def inv6a_def R6a_def)
   apply(rule impI)
   apply(rule context_conjI)
   using extra53 apply(auto simp add: VC53_def)[1]
   apply(rule conjI)
    apply simp
   apply(unfold extraInv_def commonExtraInv_def)
   apply(erule conjE)
   apply(rule Pattern4_Def.einv2req)
   by auto

 theorem proof63: "VC63 inv6a env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
   apply(unfold VC63_def inv6a_def R6a_def)
   apply(rule impI)
   apply(rule context_conjI)
   using extra63 apply(auto simp add: VC63_def)[1]
   apply(rule conjI)
    apply simp
   apply(unfold extraInv_def commonExtraInv_def)
   apply(erule conjE)
   apply(rule Pattern4_Def.einv2req)
   by auto

 theorem proof73: "VC73 inv6a env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
   apply(unfold VC73_def inv6a_def R6a_def)
   apply(rule impI)
   apply(rule context_conjI)
   using extra73 apply(auto simp add: VC73_def)[1]
   apply(rule conjI)
    apply simp
   apply(unfold extraInv_def commonExtraInv_def)
   apply(erule conjE)
   apply(rule Pattern4_Def.einv2req)
   by auto

 theorem proof143: "VC143 inv6a env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
   apply(unfold VC143_def inv6a_def R6a_def)
   apply(rule impI)
   apply(rule context_conjI)
   using extra143 apply(auto simp add: VC143_def)[1]
   apply(rule conjI)
    apply simp
   apply(unfold extraInv_def commonExtraInv_def)
   apply(erule conjE)
   by simp

 theorem proof150: "VC150 inv6a env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
   apply(unfold VC150_def inv6a_def R6a_def)
   apply(rule impI)
   apply(rule context_conjI)
   using extra150 apply(auto simp add: VC150_def)[1]
   apply(rule conjI)
    apply simp
   apply(unfold extraInv_def commonExtraInv_def)
   apply(erule conjE)
   by simp

 theorem proof160: "VC160 inv6a env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
   apply(unfold VC160_def inv6a_def R6a_def)
   apply(rule impI)
   apply(rule context_conjI)
   using extra160 apply(auto simp add: VC160_def)[1]
   apply(rule conjI)
    apply simp
   apply(unfold extraInv_def commonExtraInv_def)
   apply(erule conjE)
   by simp

 theorem proof23: "VC23 inv6a env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
   apply(unfold VC23_def inv6a_def R6a_def)
   apply(rule impI)
   apply(rule context_conjI)
   using extra23 apply(auto simp add: VC23_def)[1]
   apply(rule conjI)
    apply simp
   apply(unfold extraInv_def commonExtraInv_def)
   apply(erule conjE)
   apply(rule Pattern4_Def.einv2req)
   by auto

 theorem proof40: "VC40 inv6a env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
   apply(unfold VC40_def inv6a_def R6a_def)
   apply(rule impI)
   apply(rule context_conjI)
   using extra40 apply(auto simp add: VC40_def)[1]
   apply(rule conjI)
    apply simp
   apply(unfold extraInv_def commonExtraInv_def)
   apply(erule conjE)
   apply(rule Pattern4_Def.einv2req)
   by auto

definition inv6a' where "inv6a' s \<equiv> extraInv s \<and> R6a' s"

 theorem proof40': "VC40 inv6a' env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
   apply(unfold VC40_def inv6a'_def R6a'_def)
   apply(rule impI)
   apply(rule context_conjI)
   using extra40 apply(auto simp add: VC40_def)[1]
   apply(rule conjI)
    apply simp
   apply(erule conjE)
     apply(unfold extraInv_def commonExtraInv_def)
     apply(erule conjE)+
   apply(auto simp add: Pattern4_Def.einv2req2)
   done

end
