theory ExtraInv_R13b 
  imports commonExtraInv "../Patterns"
begin

definition extraInv1 where "extraInv1 s \<equiv> commonExtraInv s \<and>
(getPstate s Drum' = Drum'leftRotation' \<longrightarrow> 
P7_2inv s (DIRECTION_CHANGE_PERIOD'TIMEOUT - 1) (ltime s Drum' - 1) False (getPstate s Washing' = Washing'draining')
 (\<lambda> s1. getVarBool s1 left' = False) (\<lambda> s2. getVarBool s2 left' = True) (\<lambda> s3. getVarBool s3 left' = True)
(\<lambda> s4. getVarBool s4 drain' = True) (\<lambda> s5. getVarBool s5 drain' = False)) \<and>
(getPstate s Drum' \<noteq> Drum'leftRotation' \<longrightarrow> 
P7_2inv s (DIRECTION_CHANGE_PERIOD'TIMEOUT - 1) (DIRECTION_CHANGE_PERIOD'TIMEOUT - 1)  True (getPstate s Washing' = Washing'draining')
 (\<lambda> s1. getVarBool s1 left' = False) (\<lambda> s2. getVarBool s2 left' = True) (\<lambda> s3. getVarBool s3 left' = True)
(\<lambda> s4. getVarBool s4 drain' = True) (\<lambda> s5. getVarBool s5 drain' = False))"

theorem extra1': "VC1 extraInv1 s0"
  apply(unfold VC1_def extraInv1_def commonExtraInv_def P7_2inv_def always2_def always_def constrained_weak_until_inv_def previous_ex_def)
  apply auto
  done

theorem extra23': "VC23 extraInv1 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC23_def extraInv1_def)
  apply(rule impI)
  apply(rule conjI)
  using cei23 VC23_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule conjI)
   apply(simp;(rule impI;simp)?)
   apply(rule P7_2_rule[of s0])
    apply auto
  done

theorem extra43': "VC43 extraInv1 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC43_def extraInv1_def)
  apply(rule impI)
  apply(rule conjI)
  using cei43 VC43_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule conjI)
   apply(simp;(rule impI;simp)?)
   apply(rule P7_2_rule[of s0])
    apply auto
  done

theorem extra44': "VC44 extraInv1 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC44_def extraInv1_def)
  apply(rule impI)
  apply(rule conjI)
  using cei44 VC44_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
    apply(rule conjI)
   apply(simp;(rule impI;simp)?) 
  apply(simp;(rule impI;simp)?)
   apply(rule P7_2_rule[of s0])
    apply auto
  done

theorem extra45': "VC45 extraInv1 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC45_def extraInv1_def)
  apply(rule impI)
  apply(rule conjI)
  using cei45 VC45_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule conjI)
   apply(simp;(rule impI;simp)?)
  apply(simp;(rule impI;simp)?)
  apply(rule P7_2_rule[of s0])
    apply auto
  done

theorem extra46': "VC46 extraInv1 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC46_def extraInv1_def)
  apply(rule impI)
  apply(rule conjI)
  using cei46 VC46_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule conjI)
   apply(simp;(rule impI;simp)?)
  apply(simp;(rule impI;simp)?)
  apply(rule P7_2_rule[of s0])
    apply auto
  done

theorem extra47': "VC47 extraInv1 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC47_def extraInv1_def)
  apply(rule impI)
  apply(rule conjI)
  using cei47 VC47_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule conjI)
   apply(simp;(rule impI;simp)?)
  apply(simp;(rule impI;simp)?)
  apply(rule P7_2_rule[of s0])
    apply auto
  done

theorem extra48': "VC48 extraInv1 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC48_def extraInv1_def)
  apply(rule impI)
  apply(rule conjI)
  using cei48 VC48_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule conjI)
   apply(simp;(rule impI;simp)?)
  apply(rule P7_2_rule[of s0])
    apply auto
  done

theorem extra49': "VC49 extraInv1 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC49_def extraInv1_def)
  apply(rule impI)
  apply(rule conjI)
  using cei49 VC49_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
    apply(rule conjI)
   apply(simp;(rule impI;simp)?)
  apply(simp;(rule impI;simp)?)
  apply(rule P7_2_rule[of s0])
    apply auto
  done

theorem extra50': "VC50 extraInv1 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC50_def extraInv1_def)
  apply(rule impI)
  apply(rule conjI)
  using cei50 VC50_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply simp
  done

theorem extra51': "VC51 extraInv1 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC51_def extraInv1_def)
  apply(rule impI)
  apply(rule conjI)
  using cei51 VC51_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply simp
  done

theorem extra132': "VC132 extraInv1 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC132_def extraInv1_def)
  apply(rule impI)
  apply(rule conjI)
  using cei132 VC132_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
   apply(rule conjI)
   apply(simp;(rule impI;simp)?)
  apply(simp;(rule impI;simp)?)
  apply(rule P7_2_rule[of s0])
    apply auto
  done

theorem extra133': "VC133 extraInv1 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC133_def extraInv1_def)
  apply(rule impI)
  apply(rule conjI)
  using cei133 VC133_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
     apply(rule conjI)
   apply(simp;(rule impI;simp)?)
  apply(rule P7_2_rule[of s0])
    apply auto
  done

theorem extra134': "VC134 extraInv1 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC134_def extraInv1_def)
  apply(rule impI)
  apply(rule conjI)
  using cei134 VC134_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
    apply(rule conjI)
   apply(simp;(rule impI;simp)?)
   apply(simp;(rule impI;simp)?)
  apply(rule P7_2_rule[of s0])
    apply auto
  done

theorem extra135': "VC135 extraInv1 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC135_def extraInv1_def)
  apply(rule impI)
  apply(rule conjI)
  using cei135 VC135_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
      apply(rule conjI)
   apply(simp;(rule impI;simp)?)
   apply(simp;(rule impI;simp)?)
  apply(rule P7_2_rule[of s0])
    apply auto
  done

theorem extra136': "VC136 extraInv1 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC136_def extraInv1_def)
  apply(rule impI)
  apply(rule conjI)
  using cei136 VC136_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
      apply(rule conjI)
   apply(simp;(rule impI;simp)?)
   apply(simp;(rule impI;simp)?)
  apply(rule P7_2_rule[of s0])
    apply auto
  done

theorem extra137': "VC137 extraInv1 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC137_def extraInv1_def)
  apply(rule impI)
  apply(rule conjI)
  using cei137 VC137_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
     apply(rule conjI)
   apply(simp;(rule impI;simp)?)
   apply(simp;(rule impI;simp)?)
  apply(rule P7_2_rule[of s0])
    apply auto
  done

theorem extra138': "VC138 extraInv1 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC138_def extraInv1_def)
  apply(rule impI)
  apply(rule conjI)
  using cei138 VC138_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
    apply(rule conjI)
   apply(simp;(rule impI;simp)?)
  apply(rule P7_2_rule[of s0])
    apply auto
  done

theorem extra139': "VC139 extraInv1 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC139_def extraInv1_def)
  apply(rule impI)
  apply(rule conjI)
  using cei139 VC139_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
       apply(rule conjI)
   apply(simp;(rule impI;simp)?)
   apply(simp;(rule impI;simp)?)
  apply(rule P7_2_rule[of s0])
    apply auto
  done

theorem extra140': "VC140 extraInv1 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC140_def extraInv1_def)
  apply(rule impI)
  apply(rule conjI)
  using cei140 VC140_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply simp
  done

theorem extra141': "VC141 extraInv1 env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC141_def extraInv1_def)
  apply(rule impI)
  apply(rule conjI)
  using cei141 VC141_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply simp
  done

end
