theory Proofs_R6b
  imports ExtraInv_R6b Requirements
begin

definition inv6b where "inv6b s \<equiv> extraInv s \<and> R6b s"

theorem "VC1 R6b s0"
  apply(unfold VC1_def R6b_def)
  by auto

theorem  "VC43 inv6b env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC43_def inv6b_def R6b_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra43 apply(auto simp add: VC43_def)[1]
  apply(rule conjI)
   apply simp
  apply(erule conjE)
  subgoal premises prems
    apply(insert prems(1,3))
    apply(unfold extraInv_def commonExtraInv_def)
    apply(erule conjE)+
  apply(rule Pattern5_Def.einv2req)
    by auto
  done

theorem  "VC53 inv6b env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC53_def inv6b_def R6b_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra53 apply(auto simp add: VC53_def)[1]
  apply(rule conjI)
   apply simp
  apply(erule conjE)
  subgoal premises prems
    apply(insert prems(1,3))
    apply(unfold extraInv_def commonExtraInv_def)
    apply(erule conjE)+
    apply(rule Pattern5_Def.einv2req)
    by auto
  done

theorem  "VC63 inv6b env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC63_def inv6b_def R6b_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra63 apply(auto simp add: VC63_def)[1]
  apply(rule conjI)
   apply simp
  apply(erule conjE)
  subgoal premises prems
    apply(insert prems(1,3))
    apply(unfold extraInv_def commonExtraInv_def)
    apply(erule conjE)+
    apply(rule Pattern5_Def.einv2req)
    by auto
  done

theorem  "VC73 inv6b env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC73_def inv6b_def R6b_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra73 apply(auto simp add: VC73_def)[1]
  apply(rule conjI)
   apply simp
  apply(erule conjE)
  subgoal premises prems
    apply(insert prems(1,3))
    apply(unfold extraInv_def commonExtraInv_def)
    apply(erule conjE)+
    apply(rule Pattern5_Def.einv2req)
    by auto
  done

theorem  "VC143 inv6b env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC143_def inv6b_def R6b_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra143 apply(auto simp add: VC143_def)[1]
  apply(rule conjI)
   apply simp
  apply(erule conjE)
  subgoal premises prems
    apply(insert prems(1,3))
    apply(unfold extraInv_def commonExtraInv_def)
    apply(erule conjE)+
    apply(rule Pattern5_Def.einv2req)
    by auto
  done

end
