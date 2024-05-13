theory CommonExtraInv
  imports VendingMachine
begin

definition commonExtraInv where "commonExtraInv s \<equiv> toEnvP s \<and>
(getPstate s Controller' = Controller'waiting' \<longrightarrow>
 getVarInt s mode' = IDLE' \<and> getVarBool s lockChanger' = False \<and> getVarInt s credit' \<le> 0) \<and>
(getPstate s Controller' = Controller'choice' \<longrightarrow> getVarInt s mode' = CHOICE' \<and> getVarBool s lockChanger' = True) \<and>
(getPstate s Controller' = Controller'payOut' \<longrightarrow> getVarInt s mode' = PAYING_OUT') \<and>
(getPstate s Controller' \<noteq> Controller'sale' \<longrightarrow> getPstate s Sale1' = STOP \<and> getPstate s Sale2' = STOP) \<and>
(getPstate s Controller' \<noteq> Controller'payOut' \<longrightarrow> getVarBool s dispense' = False \<and> getVarInt s change' = 0) \<and>
(getPstate s Controller' \<in> {Controller'waiting', Controller'choice', Controller'sale', Controller'payOut'}) \<and>
(getPstate s Sale1' = Sale1'addMoney' \<longrightarrow> getVarInt s mode' = ADD_MONEY' \<and> getVarBool s lockChanger' = False \<and>
\<not> (getVarBool s cancel' \<or> getVarInt s credit' \<ge> PRICE1')) \<and>
(getPstate s Sale1' = Sale1'delivery' \<longrightarrow>
 getVarInt s mode' = DELIVERY' \<and> getVarInt s credit' \<ge> PRICE1' \<and> getVarBool s product1' = True) \<and>
(getPstate s Sale1' = Sale1'delivery' \<longrightarrow> ltime s Sale1' \<le> DELIVERY_TIME_LIMIT'TIMEOUT) \<and>
(getPstate s Sale1' \<noteq> Sale1'delivery' \<longrightarrow> getVarBool s product1' = False)  \<and>
(getPstate s Sale1' \<in> {Sale1'addMoney', Sale1'delivery', STOP, ERROR}) \<and>
(getPstate s Sale2' = Sale2'addMoney' \<longrightarrow> getVarInt s mode' = ADD_MONEY' \<and> getVarBool s lockChanger' = False \<and>
\<not> (getVarBool s cancel' \<or> getVarInt s credit' \<ge> PRICE2')) \<and>
(getPstate s Sale2' = Sale2'delivery' \<longrightarrow>
 getVarInt s mode' = DELIVERY' \<and> getVarInt s credit' \<ge> PRICE2' \<and> getVarBool s product2' = True) \<and>
(getPstate s Sale2' = Sale2'delivery' \<longrightarrow> ltime s Sale2' \<le> DELIVERY_TIME_LIMIT'TIMEOUT) \<and>
(getPstate s Sale2' \<noteq> Sale2'delivery' \<longrightarrow> getVarBool s product2' = False)  \<and>
(getPstate s Sale2' \<in> {Sale2'addMoney', Sale2'delivery', STOP, ERROR}) \<and>
(getPstate s Sale1' \<noteq> STOP \<longrightarrow> getPstate s Sale2' = STOP) \<and>
(getPstate s Sale2' \<noteq> STOP \<longrightarrow> getPstate s Sale1' = STOP) \<and>
(getPstate s Sale1' = ERROR \<longrightarrow> getVarInt s mode' = DELIVERY') \<and>
(getPstate s Sale2' = ERROR \<longrightarrow> getVarInt s mode' = DELIVERY')
"

theorem cei: "VC1 commonExtraInv s0"
  apply(unfold VC1_def commonExtraInv_def)
  apply auto
  done

theorem cei9: "VC9 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC9_def commonExtraInv_def)
  by force

theorem cei18: "VC18 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC18_def commonExtraInv_def)
  by force

theorem cei27: "VC27 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC27_def commonExtraInv_def)
  by force

theorem cei36: "VC36 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC36_def commonExtraInv_def)
  by force

theorem cei45: "VC45 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC45_def commonExtraInv_def)
  by force

theorem cei54: "VC54 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC54_def commonExtraInv_def)
  by force

theorem cei63: "VC63 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC63_def commonExtraInv_def)
  by force

theorem cei72: "VC72 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC72_def commonExtraInv_def)
  by force

theorem cei81: "VC81 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC81_def commonExtraInv_def)
  by force

theorem cei90: "VC90 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC90_def commonExtraInv_def)
  by force

theorem cei99: "VC99 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC99_def commonExtraInv_def)
  by force

theorem cei108: "VC108 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC108_def commonExtraInv_def)
  by force

theorem cei117: "VC117 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC117_def commonExtraInv_def)
  by force

theorem cei126: "VC126 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC126_def commonExtraInv_def)
  by force

theorem cei135: "VC135 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC135_def commonExtraInv_def)
  by force

theorem cei144: "VC144 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC144_def commonExtraInv_def)
  by force

theorem cei153: "VC153 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC153_def commonExtraInv_def)
  by force

theorem cei162: "VC162 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC162_def commonExtraInv_def)
  by force

theorem cei171: "VC171 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC171_def commonExtraInv_def)
  by force

theorem cei180: "VC180 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC180_def commonExtraInv_def)
  by force

theorem cei189: "VC189 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC189_def commonExtraInv_def)
  by force

theorem cei198: "VC198 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC198_def commonExtraInv_def)
  by force

theorem cei207: "VC207 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC207_def commonExtraInv_def)
  by force

theorem cei216: "VC216 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC216_def commonExtraInv_def)
  by force

theorem cei225: "VC225 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC225_def commonExtraInv_def)
  by force

theorem cei234: "VC234 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC234_def commonExtraInv_def)
  by force

theorem cei243: "VC243 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC243_def commonExtraInv_def)
  by force

theorem cei252: "VC252 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC252_def commonExtraInv_def)
  by force

theorem cei261: "VC261 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC261_def commonExtraInv_def)
  by force

theorem cei270: "VC270 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC270_def commonExtraInv_def)
  by force

theorem cei279: "VC279 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC279_def commonExtraInv_def)
  by force

theorem cei288: "VC288 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC288_def commonExtraInv_def)
  by force

theorem cei297: "VC297 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC297_def commonExtraInv_def)
  by force

theorem cei306: "VC306 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC306_def commonExtraInv_def)
  by force

theorem cei315: "VC315 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC315_def commonExtraInv_def)
  by force

theorem cei324: "VC324 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC324_def commonExtraInv_def)
  by force

theorem cei333: "VC333 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC333_def commonExtraInv_def)
  by force

theorem cei342: "VC342 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC342_def commonExtraInv_def)
  by force

theorem cei351: "VC351 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC351_def commonExtraInv_def)
  by force

theorem cei360: "VC360 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC360_def commonExtraInv_def)
  by force

theorem cei369: "VC369 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC369_def commonExtraInv_def)
  by force

theorem cei378: "VC378 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC378_def commonExtraInv_def)
  by force

theorem cei387: "VC387 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC387_def commonExtraInv_def)
  by force

theorem cei396: "VC396 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC396_def commonExtraInv_def)
  by force

theorem cei405: "VC405 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC405_def commonExtraInv_def)
  by force

theorem cei738: "VC738 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC738_def commonExtraInv_def)
  by force

theorem cei747: "VC747 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC747_def commonExtraInv_def)
  by force

theorem cei756: "VC756 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC756_def commonExtraInv_def)
  by force

theorem cei765: "VC765 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC765_def commonExtraInv_def)
  by force

theorem cei774: "VC774 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC774_def commonExtraInv_def)
  by force

theorem cei783: "VC783 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC783_def commonExtraInv_def)
  by force

theorem cei792: "VC792 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC792_def commonExtraInv_def)
  by force

theorem cei801: "VC801 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC801_def commonExtraInv_def)
  by force

theorem cei810: "VC810 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC810_def commonExtraInv_def)
  by force

theorem cei639: "VC639 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC639_def commonExtraInv_def)
  by force

theorem cei882: "VC882 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC882_def commonExtraInv_def)
  by force

theorem cei963: "VC963 commonExtraInv env s0 button1'value button2'value deposited'value given1'value given2'value paidOut'value
 cancel'value "
  apply(unfold VC963_def commonExtraInv_def)
  by force

end