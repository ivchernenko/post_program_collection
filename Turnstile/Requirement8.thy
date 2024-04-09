theory Requirement8
  imports Turnstile "../Patterns"
begin

definition R8 where "R8 s \<equiv> toEnvP s \<and>
P7_2 s 100 (\<lambda> s1. getVarBool s1 open' = False) (\<lambda> s2. getVarBool s2 open' = True) (\<lambda> s3. getVarBool s3 open' = True) (\<lambda> s4. True) (\<lambda> s5. getVarBool s5 PdOut' = True)"

definition commonExtraInv where "commonExtraInv s \<equiv> toEnvP s \<and>
(getPstate s Controller' \<in> {Controller'isClosed', STOP} \<longrightarrow> getVarBool s open' = False) \<and>
(getPstate s Controller' \<in> {Controller'minimalOpened', Controller'isOpened'} \<longrightarrow> getVarBool s open' = True) \<and>
(getPstate s Controller' = Controller'minimalOpened' \<longrightarrow> ltime s Controller' \<le> 11) \<and>
(getPstate s Controller' = Controller'isOpened' \<longrightarrow> ltime s Controller' \<le> 90) \<and>
(getPstate s Controller' \<in> {Controller'isClosed', Controller'minimalOpened', Controller'isOpened', STOP})"

theorem "VC1 commonExtraInv s0"
  apply(unfold VC1_def commonExtraInv_def)
  by auto

theorem "VC338 commonExtraInv env s0 PdOut_value paid_value opened_value"
  apply(unfold VC338_def commonExtraInv_def)
  by force

theorem "VC362 commonExtraInv env s0 PdOut_value paid_value opened_value"
  apply(unfold VC362_def commonExtraInv_def)
  by force

theorem cei386: "VC386 commonExtraInv env s0 PdOut_value paid_value opened_value"
  apply(unfold VC386_def commonExtraInv_def)
  by force

theorem cei506: "VC506 commonExtraInv env s0 PdOut_value paid_value opened_value"
  apply(unfold VC506_def commonExtraInv_def)
  by force

definition extraInv1 where "extraInv1 s \<equiv> commonExtraInv s \<and>
(getPstate s Controller' \<in> {Controller'isClosed', STOP} \<longrightarrow>
P7_2inv s 100 100 True True  (\<lambda> s1. getVarBool s1 open' = False) (\<lambda> s2. getVarBool s2 open' = True) (\<lambda> s3. getVarBool s3 open' = True)
 (\<lambda> s4. True) (\<lambda> s5. getVarBool s5 PdOut' = True)) \<and>
(getPstate s Controller' = Controller'isOpened' \<longrightarrow>
P7_2inv s 100 (ltime s Controller' + 10) False True  (\<lambda> s1. getVarBool s1 open' = False) (\<lambda> s2. getVarBool s2 open' = True) (\<lambda> s3. getVarBool s3 open' = True)
 (\<lambda> s4. True) (\<lambda> s5. getVarBool s5 PdOut' = True)) \<and>
(getPstate s Controller' = Controller'minimalOpened' \<and> getVarBool s passed' = True \<longrightarrow>
P7_2inv s 100 (ltime s Controller' + 89) False True  (\<lambda> s1. getVarBool s1 open' = False) (\<lambda> s2. getVarBool s2 open' = True) (\<lambda> s3. getVarBool s3 open' = True)
 (\<lambda> s4. True) (\<lambda> s5. getVarBool s5 PdOut' = True)) \<and>
(getPstate s Controller' = Controller'minimalOpened' \<and> getVarBool s passed' = False \<longrightarrow>
P7_2inv s 100 (ltime s Controller' - 1) False True  (\<lambda> s1. getVarBool s1 open' = False) (\<lambda> s2. getVarBool s2 open' = True) (\<lambda> s3. getVarBool s3 open' = True)
 (\<lambda> s4. True) (\<lambda> s5. getVarBool s5 PdOut' = True))"

theorem extra1': "VC1 extraInv1 s0"
  apply(unfold VC1_def extraInv1_def commonExtraInv_def P7_2inv_def always2_def always_def constrained_weak_until_inv_def previous_ex_def)
  apply auto
  done


theorem extra386': "VC386 extraInv1 env s0 PdOut_value paid_value opened_value"
  apply(unfold VC386_def extraInv1_def)
 apply(rule impI)
  apply(rule conjI)
  using cei386 VC386_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule conjI)
   apply(simp;(rule impI;simp)?)
    apply(cases "getVarBool s0 passed'")
  subgoal
    apply(rule P7_2_rule[of s0])
    by auto
  subgoal
    apply(rule P7_2_rule[of s0])
    by auto
  apply(rule conjI)
   apply(simp;(rule impI;simp)?)
  apply(rule conjI)
   apply(simp;(rule impI;simp)?)
  apply(simp;(rule impI;simp)?)
  done

theorem extra506': "VC506 extraInv1 env s0 PdOut_value paid_value opened_value"
  apply(unfold VC506_def extraInv1_def)
 apply(rule impI)
  apply(rule conjI)
  using cei506 VC506_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(rule conjI)
   apply simp
  apply(rule conjI)
   apply simp
  apply(rule conjI)
  subgoal
   apply simp
   apply(rule impI)
   apply simp
    apply(rule P7_2_rule[of s0])
    by auto
  subgoal
    apply simp
  apply(rule impI)
   apply simp
    apply(rule P7_2_rule[of s0])
    by auto
  done

definition inv8_1 where  "inv8_1 s \<equiv> extraInv1 s \<and> R8 s"

theorem "VC506 inv8_1 env s0  PdOut_value paid_value opened_value"
  apply(unfold VC506_def inv8_1_def R8_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra506' VC506_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv1_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P7_2_einv2req)
  done


definition extraInv2 where "extraInv2 s \<equiv> commonExtraInv s \<and>
((((getPstate s Controller' \<in> {Controller'isClosed', STOP} \<and>
P7_2inv s 100 100 True True  (\<lambda> s1. getVarBool s1 open' = False) (\<lambda> s2. getVarBool s2 open' = True) (\<lambda> s3. getVarBool s3 open' = True)
 (\<lambda> s4. True) (\<lambda> s5. getVarBool s5 PdOut' = True)) \<or>
(getPstate s Controller' = Controller'isOpened' \<and>
P7_2inv s 100 (ltime s Controller' + 10) False True  (\<lambda> s1. getVarBool s1 open' = False) (\<lambda> s2. getVarBool s2 open' = True) (\<lambda> s3. getVarBool s3 open' = True)
 (\<lambda> s4. True) (\<lambda> s5. getVarBool s5 PdOut' = True))) \<or>
(getPstate s Controller' = Controller'minimalOpened' \<and> getVarBool s passed' = True \<and>
P7_2inv s 100 (ltime s Controller' + 89) False True  (\<lambda> s1. getVarBool s1 open' = False) (\<lambda> s2. getVarBool s2 open' = True) (\<lambda> s3. getVarBool s3 open' = True)
 (\<lambda> s4. True) (\<lambda> s5. getVarBool s5 PdOut' = True))) \<or>
(getPstate s Controller' = Controller'minimalOpened' \<and> getVarBool s passed' = False \<and>
P7_2inv s 100 (ltime s Controller' - 1) False True  (\<lambda> s1. getVarBool s1 open' = False) (\<lambda> s2. getVarBool s2 open' = True) (\<lambda> s3. getVarBool s3 open' = True)
 (\<lambda> s4. True) (\<lambda> s5. getVarBool s5 PdOut' = True)))"

theorem extra1: "VC1 extraInv2 s0"
  apply(unfold VC1_def extraInv2_def commonExtraInv_def P7_2inv_def always2_def always_def constrained_weak_until_inv_def previous_ex_def)
  apply auto
  done
 

theorem extra386: "VC386 extraInv2 env s0 PdOut_value paid_value opened_value"
  apply(unfold VC386_def extraInv2_def)
 apply(rule impI)
  apply(rule conjI)
  using cei386 VC386_def apply auto[1]
 apply(unfold commonExtraInv_def)
  apply(erule conjE)
  apply(erule conjE)
  apply(rotate_tac 1)
  apply(erule conjE)
  apply(simp del: disj_assoc)
  apply(((erule disjE)+);simp?;(rule P7_2_rule[of s0]);auto)
  done

theorem extra506: "VC506 extraInv2 env s0 PdOut_value paid_value opened_value"
  apply(unfold VC506_def extraInv2_def)
 apply(rule impI)
  apply(rule conjI)
  using cei506 VC506_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)
  apply(erule conjE)
  apply(rotate_tac 1)
  apply(erule conjE)
  apply(simp del: disj_assoc)
  apply(((erule disjE)+);simp?;(rule P7_2_rule[of s0]);auto)
  done

definition inv8_2 where "inv8_2 s \<equiv> extraInv2 s \<and> R8 s"

theorem "VC506 inv8_2 env s0  PdOut_value paid_value opened_value"
  apply(unfold VC506_def inv8_2_def R8_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra506 VC506_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv2_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P7_2_einv2req)
  done
  

definition extraInv3 where "extraInv3 s \<equiv>  commonExtraInv s \<and>
P7_2inv s 100
(if getPstate s Controller' \<in> {Controller'isClosed', STOP} then 100 else if getPstate s Controller' = Controller'isOpened' then (ltime s Controller' + 10)
else if getPstate s Controller' = Controller'minimalOpened' then if getVarBool s passed' = True then (ltime s Controller' + 89) else (ltime s Controller' - 1)
else 100)
(getPstate s Controller' \<in> {Controller'isClosed', STOP}) True
 (\<lambda> s1. getVarBool s1 open' = False) (\<lambda> s2. getVarBool s2 open' = True) (\<lambda> s3. getVarBool s3 open' = True)
 (\<lambda> s4. True) (\<lambda> s5. getVarBool s5 PdOut' = True)"

theorem extra1_3: "VC1 extraInv3 s0"
  apply(unfold VC1_def extraInv3_def commonExtraInv_def P7_2inv_def always2_def always_def constrained_weak_until_inv_def previous_ex_def)
  apply auto
  done

theorem extra386_3: "VC386 extraInv3 env s0 PdOut_value paid_value opened_value"
  apply(unfold VC386_def extraInv3_def)
 apply(rule impI)
  apply(rule conjI)
  using cei386 VC386_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule P7_2_rule')
  apply(auto split: if_splits)
  done

theorem extra506_3: "VC506 extraInv3 env s0 PdOut_value paid_value opened_value"
  apply(unfold VC506_def extraInv3_def)
 apply(rule impI)
  apply(rule conjI)
  using cei506 VC506_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule P7_2_rule')
  apply(auto split: if_splits)
  done

definition inv8_3 where "inv8_3 s \<equiv> extraInv3 s \<and> R8 s"


theorem "VC506 inv8_3 env s0  PdOut_value paid_value opened_value"
  apply(unfold VC506_def inv8_3_def R8_def)
  apply(rule impI)
  apply(rule context_conjI)
  using extra506_3 VC506_def apply auto[1]
  apply(rule conjI)
   apply simp
  apply(unfold extraInv3_def commonExtraInv_def)
  apply(erule conjE)+
  apply(auto simp add:  P7_2_einv2req)
  done

end

