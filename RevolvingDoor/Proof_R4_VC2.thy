theory Proof_R4_VC2
  imports ExtraInv4_VC2
begin

definition inv4 where "inv4 s \<equiv> extraInv s \<and> R4_1 s"

theorem "VC2 inv4 env s0 user_value pressure_value"
  apply(unfold VC2_def inv4_def R4_1_def)
  apply rule
  apply(rule context_conjI)
  using extra2 apply(auto simp add: VC2_def)[1]
  apply rule
   apply simp
  apply(erule conjE)
  subgoal premises prems
        apply(insert prems(1))
    apply(unfold extraInv_def)
    apply(erule conjE)+
    subgoal premises ei
      apply(rule einv2req)
      using ei(3) prems(3)[simplified] by auto
    done
  done

end
