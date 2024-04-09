theory Proofs_R13b
  imports ExtraInv_R13b Requirements
begin

definition inv13b where "inv13b s \<equiv> extraInv1 s \<and> R13b s"

theorem "VC1 inv13b s0"
  apply(unfold VC1_def inv13b_def R13b_def P7_2_def always2_def always_def constrained_weak_until_def previous_ex_def)
  using extra1' VC1_def apply auto
  done

theorem "VC43 inv13b env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC43_def inv13b_def R13b_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra43' VC43_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv1_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P7_2_einv2req)
  done

theorem "VC44 inv13b env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC44_def inv13b_def R13b_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra44' VC44_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv1_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P7_2_einv2req)
  done

theorem "VC45 inv13b env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC45_def inv13b_def R13b_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra45' VC45_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv1_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P7_2_einv2req)
  done

theorem "VC46 inv13b env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC46_def inv13b_def R13b_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra46' VC46_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv1_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P7_2_einv2req)
  done

theorem "VC47 inv13b env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC47_def inv13b_def R13b_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra47' VC47_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv1_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P7_2_einv2req)
  done

theorem "VC48 inv13b env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC48_def inv13b_def R13b_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra48' VC48_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv1_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P7_2_einv2req)
  done

theorem "VC48 inv13b env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC48_def inv13b_def R13b_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra48' VC48_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv1_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P7_2_einv2req)
  done

theorem "VC49 inv13b env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC49_def inv13b_def R13b_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra49' VC49_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv1_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P7_2_einv2req)
  done

theorem "VC50 inv13b env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC50_def inv13b_def R13b_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra50' VC50_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv1_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P7_2_einv2req)
  done

theorem "VC51 inv13b env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC51_def inv13b_def R13b_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra51' VC51_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv1_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P7_2_einv2req)
  done

theorem "VC132 inv13b env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC132_def inv13b_def R13b_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra132' VC132_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv1_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P7_2_einv2req)
  done

theorem "VC133 inv13b env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC133_def inv13b_def R13b_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra133' VC133_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv1_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P7_2_einv2req)
  done

theorem "VC134 inv13b env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC134_def inv13b_def R13b_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra134' VC134_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv1_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P7_2_einv2req)
  done

theorem "VC135 inv13b env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC135_def inv13b_def R13b_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra135' VC135_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv1_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P7_2_einv2req)
  done

theorem "VC136 inv13b env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC136_def inv13b_def R13b_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra136' VC136_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv1_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P7_2_einv2req)
  done

theorem "VC137 inv13b env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC137_def inv13b_def R13b_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra137' VC137_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv1_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P7_2_einv2req)
  done

theorem "VC138 inv13b env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC138_def inv13b_def R13b_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra138' VC138_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv1_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P7_2_einv2req)
  done

theorem "VC139 inv13b env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC139_def inv13b_def R13b_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra139' VC139_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv1_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P7_2_einv2req)
  done

theorem "VC140 inv13b env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC140_def inv13b_def R13b_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra140' VC140_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv1_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P7_2_einv2req)
  done

theorem "VC141 inv13b env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC141_def inv13b_def R13b_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra141' VC141_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv1_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P7_2_einv2req)
  done

end