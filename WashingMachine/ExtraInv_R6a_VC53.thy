theory ExtraInv_R6a_VC53
  imports ExtraInv_R6a
begin

theorem extra53: "VC53 extraInv env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC53_def extraInv_def commonExtraInv_def)
  apply(rule impI)
  apply(rule conjI)
   apply simp
  apply(erule conjE)
  apply(rule conjI)
  subgoal
    apply(rule P4inv_rule)
    by auto
  by simp

 theorem extra43: "VC43 extraInv env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC43_def extraInv_def commonExtraInv_def)
  apply(rule impI)
  apply(rule conjI)
   apply simp
  apply(erule conjE)
   apply(rule conjI)
    apply simp
   subgoal
     apply(rule P4inv_rule)
     by auto
   done

 theorem extra63: "VC63 extraInv env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
  apply(unfold VC63_def extraInv_def commonExtraInv_def)
  apply(rule impI)
  apply(rule conjI)
   apply simp
  apply(erule conjE)
   apply(rule conjI)
   subgoal
     apply(rule P4inv_rule)
     by auto
   by simp

 theorem extra73: "VC73 extraInv env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
   apply(unfold VC73_def extraInv_def commonExtraInv_def)
  apply(rule impI)
  apply(rule conjI)
   apply simp
  apply(erule conjE)
   apply(rule conjI)
    apply simp
   subgoal
     apply(rule P4inv_rule)
     by auto
   done

 theorem extra150: "VC150 extraInv env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
   apply(unfold VC150_def extraInv_def)  
  apply(rule impI)
   apply(rule conjI)
   using cei150 apply(auto simp add: VC150_def)[1]
   apply(unfold commonExtraInv_def)
  apply(erule conjE)
   apply(rule conjI)
    apply simp
   apply simp
   done

 theorem extra143: "VC143 extraInv env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
   apply(unfold VC143_def extraInv_def)  
   apply(rule impI)
   apply(rule conjI)
   using cei143 apply(auto simp add: VC143_def)[1]
   apply(unfold commonExtraInv_def)
   apply(erule conjE)
   apply(rule conjI)
    apply simp
   apply simp
   done

 theorem extra160: "VC160 extraInv env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
   apply(unfold VC160_def extraInv_def) 
   apply(rule impI)
   apply(rule conjI)
   using cei160 apply(auto simp add: VC160_def)[1]
   apply(unfold commonExtraInv_def)
   apply(erule conjE)
   apply(rule conjI)
    apply simp
   apply simp
   done

 theorem extra23: "VC23 extraInv env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
   apply(unfold VC23_def extraInv_def)
   apply(rule impI)
   apply(rule conjI)
   using cei23 apply(auto simp add: VC23_def)[1]
   apply(unfold commonExtraInv_def)
   apply(erule conjE)+
   apply(rule conjI)
   subgoal
     apply(rule P4inv_rule)
     by auto
   by simp

 theorem extra40: "VC40 extraInv env s0 startButton'value locked'value waterLevel'value waterPresence'value temp'value freq'value"
   apply(unfold VC40_def extraInv_def)
   apply(rule impI)
   apply(rule conjI)
   using cei40 apply(auto simp add: VC40_def)[1]
   apply(unfold commonExtraInv_def)
   apply(erule conjE)+
   apply(rule conjI)
   subgoal
     apply(rule P4inv_rule)
     by auto 
   by simp

end
    