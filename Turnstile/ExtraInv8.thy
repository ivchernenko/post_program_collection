theory ExtraInv8
  imports Requirements Pattern7_def 
begin

definition extraInv8  where "extraInv8 s \<equiv> toEnvP s \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Controller' = Controller'minimalOpened' \<longrightarrow> ltime s1 Controller' \<le> 11) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Controller' = Controller'isOpened' \<longrightarrow> ltime s1 Controller' \<le> 90) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> (getPstate s1 Controller' = Controller'isClosed' \<or> getPstate s1 Controller' = STOP) \<longrightarrow>
 \<not> getVarBool s1 open') \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and>
 (getPstate s1 Controller' = Controller'minimalOpened' \<or> getPstate s1 Controller' = Controller'isOpened') \<longrightarrow> 
  getVarBool s1 open') \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 EntranceController' = EntranceController'isClosed' \<longrightarrow> \<not>getVarBool s1 enter') \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 EntranceController' = EntranceController'isOpened' \<longrightarrow> getVarBool s1 enter') \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<longrightarrow> getPstate s1 Controller' \<in>
 {Controller'isClosed', Controller'minimalOpened', Controller'isOpened', STOP}) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<longrightarrow> getPstate s1 EntranceController' \<in>
 {EntranceController'isClosed', EntranceController'isOpened', STOP}) \<and>
(getPstate s Controller' = Controller'isClosed' \<longrightarrow>
 pattern7 (\<lambda> s1 s2. getVarBool s1 open' = False \<and> getVarBool s2 open' = True) (\<lambda> s4. getVarBool s4 PdOut') (\<lambda> s3. getVarBool s3 open' = True) 101 100 s)\<and>
(getPstate s Controller' = STOP \<longrightarrow>
 pattern7 (\<lambda> s1 s2. getVarBool s1 open' = False \<and> getVarBool s2 open' = True) (\<lambda> s4. getVarBool s4 PdOut') (\<lambda> s3. getVarBool s3 open' = True) 101 100 s)\<and>
(getPstate s Controller' = Controller'isOpened' \<longrightarrow>
 pattern7
 (\<lambda> s1 s2. getVarBool s1 open' = False \<and> getVarBool s2 open' = True)
 (\<lambda> s4. getVarBool s4 PdOut')
 (\<lambda> s3. getVarBool s3 open' = True)
 101 (ltime s Controller' + 10) s) \<and>
(getPstate s Controller' = Controller'minimalOpened' \<and> getVarBool s passed' \<longrightarrow>
 pattern7
 (\<lambda> s1 s2. getVarBool s1 open' = False \<and> getVarBool s2 open' = True)
 (\<lambda> s4. getVarBool s4 PdOut')
 (\<lambda> s3. getVarBool s3 open' = True)
 101 (ltime s Controller' + 89) s) \<and>
(getPstate s Controller' = Controller'minimalOpened' \<and> \<not>getVarBool s passed' \<longrightarrow>
 pattern7
 (\<lambda> s1 s2. getVarBool s1 open' = False \<and> getVarBool s2 open' = True)
 (\<lambda> s4. getVarBool s4 PdOut')
 (\<lambda> s3. getVarBool s3 open' = True)
 101 (ltime s Controller' - 1) s)"

definition inv8 where "inv8 s \<equiv> extraInv8 s \<and> R8 s"

theorem extra1: "VC1 inv8 s0"
  apply(unfold VC1_def inv8_def R8_def  extraInv8_def pattern7_def)
  by auto


end