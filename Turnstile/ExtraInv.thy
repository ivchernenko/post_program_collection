theory ExtraInv
  imports Turnstile
begin

definition extraInv where "extraInv s \<equiv> toEnvP s \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Init' = Init'init' \<longrightarrow> toEnvNum emptyState s1 = 1)\<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Init' = STOP \<longrightarrow> 
(\<exists> s2. toEnvP s2 \<and> substate s2 s1 \<and> getPstate s2 Init' = Init'init' \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s1 \<and> s2 \<noteq> s3 \<longrightarrow> getPstate s3 Init' = STOP))) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Controller' = Controller'isClosed' \<longrightarrow>
(\<exists> s2 s3. toEnvP s2 \<and> substate s2 s3 \<and>  substate s3 s1 \<and> toEnvNum s2 s3 = 1 \<and>
 (getPstate s2 Controller' = Controller'minimalOpened' \<and> ltime s2 Controller' = 10 \<and> getVarBool s3 passed' \<or> 
getPstate s2 Controller' = Controller'isOpened' \<and> (ltime s2 Controller' = 90 \<or> getVarBool s3 PdOut')  \<or>
getPstate s2 Init' = Init'init') \<and>
(\<forall> s4. toEnvP s4 \<and> substate s3 s4 \<and> substate s4 s1 \<longrightarrow> getPstate s4 Controller' = Controller'isClosed') \<and>
(\<forall> s5. toEnvP s5 \<and> substate s3 s5 \<and> substate s5 s1 \<and> s3 \<noteq> s5 \<longrightarrow> \<not> getVarBool s5 paid'))) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Controller' = Controller'minimalOpened' \<longrightarrow> ltime s1 Controller' \<le> 10) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Controller' = Controller'minimalOpened' \<longrightarrow>
(\<exists> s2 s3. toEnvP s2 \<and> toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s1 \<and> toEnvNum s2 s3 = 1 \<and> toEnvNum s2 s1 = ltime s1 Controller' \<and>
getPstate s2 Controller' = Controller'isClosed' \<and> getVarBool s3 paid')) \<and>
(\<forall> s2. toEnvP s2 \<and> substate s2 s \<and> getPstate s2 Controller' = Controller'minimalOpened' \<longrightarrow>
(\<forall> s1. toEnvP s1 \<and> substate s1 s2 \<and> toEnvNum s1 s2 < ltime s2 Controller' \<longrightarrow>
 getPstate s1 Controller' = Controller'minimalOpened')) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Controller' = Controller'isOpened' \<longrightarrow> ltime s1 Controller' \<le> 90) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Controller' = Controller'isOpened' \<longrightarrow>
(\<exists> s2 s3. toEnvP s2 \<and> toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s1 \<and> toEnvNum s2 s3 = 1 \<and> toEnvNum s2 s1 = ltime s1 Controller' \<and>
getPstate s2 Controller' = Controller'minimalOpened' \<and> ltime s2 Controller' = 10 \<and> \<not> getVarBool s2 passed' \<and> \<not> getVarBool s3 PdOut')) \<and>
(\<forall> s3. toEnvP s3 \<and> substate s3 s \<and> getPstate s3 Controller' = Controller'isOpened' \<longrightarrow>
(\<forall> s1. toEnvP s1 \<and> substate s1 s3 \<and> toEnvNum s1 s3 < ltime s3 Controller' \<longrightarrow> getPstate s1 Controller' = Controller'isOpened') \<and>
(\<forall> s2. toEnvP s2 \<and> substate s2 s3 \<and> toEnvNum s2 s3 + 1 < ltime s3 Controller' \<longrightarrow> \<not> getVarBool s2 PdOut')) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Controller' = STOP \<longrightarrow> toEnvNum emptyState s1 = 1) \<and>
(\<forall> s1. toEnvP s1 \<and>  substate s1 s \<and> getPstate s1 Controller' = Controller'minimalOpened' \<and> getVarBool s passed'  \<longrightarrow>
(\<exists> s2 s3. toEnvP s2 \<and> toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s1 \<and>
 toEnvNum s2 s3 = 1 \<and> toEnvNum s2 s1 < ltime s1 Controller' \<and>  \<not> getVarBool s2 passed' \<and> getVarBool s3 PdOut')) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Controller' = Controller'minimalOpened' \<and> \<not> getVarBool s1 passed' \<longrightarrow>
(\<forall> s2. toEnvP s2 \<and> substate s2 s1 \<and> toEnvNum s2 s1 + 1 < ltime s1 Controller' \<longrightarrow> \<not> getVarBool s2 PdOut')) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 EntranceController' = EntranceController'isClosed' \<longrightarrow>
(\<exists> s2 s3. toEnvP s2 \<and> toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s1 \<and> toEnvNum s2 s3 = 1 \<and>
 (getPstate s2 EntranceController' = EntranceController'isOpened' \<and> \<not>getVarBool s3 opened' \<or> getPstate s2 Init' = Init'init') \<and>
(\<forall> s4. toEnvP s4 \<and> substate s3 s4 \<and> substate s4 s1 \<longrightarrow> getPstate s4 EntranceController' = EntranceController'isClosed') \<and>
(\<forall> s5. toEnvP s5 \<and> substate s3 s5 \<and> substate s5 s1 \<and> s3 \<noteq> s5 \<longrightarrow> \<not> getVarBool s5 opened'))) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 EntranceController' = EntranceController'isOpened' \<longrightarrow>
(\<exists> s2 s3. toEnvP s2 \<and> toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s1 \<and> toEnvNum s2 s3 = 1 \<and>
 (getPstate s2 EntranceController' = EntranceController'isClosed' \<and> getVarBool s3 opened') \<and>
(\<forall> s4. toEnvP s4 \<and> substate s3 s4 \<and> substate s4 s1 \<longrightarrow> getPstate s4 EntranceController' = EntranceController'isOpened') \<and>
(\<forall> s5. toEnvP s5 \<and> substate s3 s5 \<and> substate s5 s1 \<and> s3 \<noteq> s5 \<longrightarrow> getVarBool s5 opened'))) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 EntranceController' = STOP \<longrightarrow>
(\<forall> s2. toEnvP s2 \<and> substate s2 s1 \<and> s2 \<noteq> s1 \<longrightarrow> getPstate s2 Init' \<noteq> Init'init')) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Unlocker' = Unlocker'unlock' \<longrightarrow> ltime s1 Unlocker' \<le> 10) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Unlocker' = Unlocker'unlock' \<longrightarrow>
(\<exists> s2 s3. toEnvP s2 \<and> toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s1 \<and> toEnvNum s2 s3 = 1 \<and> toEnvNum s2 s1 = ltime s1 Unlocker' \<and>
getPstate s2 EntranceController' = EntranceController'isOpened' \<and> \<not> getVarBool s3 opened')) \<and>
(\<forall> s3. toEnvP s3 \<and> substate s3 s \<and> getPstate s3 Unlocker' = Unlocker'unlock' \<longrightarrow>
(\<forall> s1. toEnvP s1 \<and> substate s1 s3 \<and> toEnvNum s1 s3 < ltime s3 Unlocker' \<longrightarrow> getPstate s1 Unlocker' =Unlocker'unlock') \<and>
(\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s3 \<and> toEnvNum s1 s2 = 1 \<and>
 toEnvNum s2 s3 + 1 < ltime s3 Unlocker' \<longrightarrow>
 getPstate s1 EntranceController' \<noteq> EntranceController'isOpened' \<or> getVarBool s2 opened')) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Unlocker' = STOP \<longrightarrow>
(\<exists> s2 s3. toEnvP s2 \<and> toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s1 \<and> toEnvNum s2 s3 = 1 \<and> 
getPstate s2 Unlocker' = Unlocker'unlock' \<and> ltime s2 Unlocker' = 10 \<and>
 (getPstate s2 EntranceController' \<noteq> EntranceController'isOpened' \<or> getVarBool s3 opened') \<and>
(\<forall> s4. toEnvP s4 \<and> substate s3 s4 \<and> substate s4 s1 \<longrightarrow> getPstate s4 Unlocker' = STOP) \<and>
(\<forall> s4 s5. toEnvP s4 \<and> toEnvP s5 \<and> substate s3 s4 \<and> substate s4 s5 \<and> substate s5 s1 \<and> toEnvNum s4 s5 = 1 \<longrightarrow>
getPstate s4 EntranceController' \<noteq> EntranceController'isOpened' \<or> getVarBool s5 opened')) \<or>
(\<forall> s4. toEnvP s4 \<and> substate s4 s1 \<longrightarrow> getPstate s4 Unlocker' = STOP) \<and>
(\<forall> s4 s5. toEnvP s4 \<and> toEnvP s5 \<and> substate s4 s5 \<and> substate s5 s1 \<and> toEnvNum s4 s5 = 1 \<longrightarrow>
getPstate s4 EntranceController' \<noteq> EntranceController'isOpened' \<or> getVarBool s5 opened')) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> (getPstate s1 Controller' = Controller'isClosed' \<or> getPstate s1 Controller' = STOP) \<longrightarrow>
\<not>getVarBool s1 open') \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and>
 (getPstate s1 Controller' = Controller'isOpened' \<or> getPstate s1 Controller' = Controller'minimalOpened') \<longrightarrow>
getVarBool s1 open') \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and>
 (getPstate s1 EntranceController' = EntranceController'isClosed' \<or> getPstate s1 EntranceController' = STOP) \<longrightarrow>
\<not>getVarBool s1 enter') \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> (getPstate s1 EntranceController' = EntranceController'isOpened') \<longrightarrow>
getVarBool s1 enter') \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> (getPstate s1 Unlocker' = Unlocker'unlock') \<longrightarrow>
getVarBool s1 reset') \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> (getPstate s1 Unlocker' = STOP) \<longrightarrow>
\<not>getVarBool s1 reset') \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<longrightarrow> getPstate s1 Init' = Init'init' \<or> getPstate s1 Init' = STOP) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<longrightarrow>
 getPstate s1 Controller' = Controller'isClosed' \<or> getPstate s1 Controller' = Controller'minimalOpened' \<or>
getPstate s1 Controller' = Controller'isOpened' \<or> getPstate s1 Controller' = STOP) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<longrightarrow>
 getPstate s1 EntranceController' \<in> {EntranceController'isClosed', EntranceController'isOpened', STOP}) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<longrightarrow>
getPstate s1 Unlocker' \<in> {Unlocker'unlock', STOP})"

end