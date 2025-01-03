theory Requirements
  imports ExtraInv
begin

definition R1 where "R1 s \<equiv> toEnvP s \<and>
(\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and> toEnvNum s2 s \<ge> 10 - 1 \<and>
 getVarBool s1 open' \<and> getVarBool s2 PdOut' = True \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s \<and> toEnvNum s2 s4 \<le> 10 - 1 \<and> \<not> getVarBool s4 open' \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> getVarBool s3 open')))"

definition R2 where "R2 s \<equiv> toEnvP s \<and>
(\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and>
 \<not> getVarBool s1 open' \<and> \<not> getVarBool s2 paid' \<longrightarrow> \<not> getVarBool s2 open')"

definition R3 where "R3 s \<equiv> toEnvP s \<and>
(\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and> 
\<not> getVarBool s1 open' \<and> \<not> getVarBool s1 paid' \<and> getVarBool s2 paid' \<longrightarrow> getVarBool s2 open')"

definition R4 where "R4 s \<equiv> toEnvP s \<and>
(\<forall> s1. substate s1 s \<and> toEnvP s1 \<and> toEnvNum s1 s \<ge> 100 \<and>
 getVarBool s1 open' \<longrightarrow>
(\<exists> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s \<and> toEnvNum s1 s3 \<le> 100 \<and> \<not> getVarBool s3 open' \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s3 \<and> s2 \<noteq> s3 \<longrightarrow> getVarBool s2 open')))"

definition R5 where "R5 s \<equiv> toEnvP s \<and>
(\<forall> s1 s2 s3. toEnvP s1 \<and> toEnvP s2 \<and> toEnvP s3 \<and> substate s1 s2 \<and> substate s2 s3 \<and> substate s3 s \<and>
toEnvNum s1 s2 = 1 \<and> toEnvNum s2 s3 < 10 \<and> \<not> getVarBool s1 open' \<and> getVarBool s2 open' \<longrightarrow>
getVarBool s3 open')"

definition R6 where "R6 s \<equiv> toEnvP s \<and>
(\<forall> s1. substate s1 s \<and> toEnvP s1 \<and> getVarBool s1 opened' \<longrightarrow> getVarBool s1 enter')"

definition R7 where "R7 s \<equiv> toEnvP s \<and>
(\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and> 
getVarBool s1 enter' \<and> \<not> getVarBool s2 enter' \<longrightarrow> getVarBool s2 reset')"

definition R8 where "R8 s\<equiv> toEnvP s \<and>
(\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s \<and> toEnvNum s1 s2 = 1 \<and> getVarBool s1 open' = False \<and> getVarBool s2 open' = True \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s \<and> toEnvNum s2 s4 \<le> 101 \<and> getVarBool s4 PdOut' \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> getVarBool s3 open' = True)) \<or>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s \<and> toEnvNum s2 s3 < 101 \<longrightarrow> getVarBool s3 open' = True))"

end