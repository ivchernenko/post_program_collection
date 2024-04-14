theory ExtraInv_R4
  imports CommonExtraInv "../Patterns"
begin

definition R4Pattern_inv where "R4Pattern_inv s t t1 b1 b2 A1 A2 A3 A4 A5 A6 A7 \<equiv> 
P1'inv s t t1 A1 (\<lambda> s2. (previous_all s2 A2 \<or> A3 s2) \<and> A4 s2) (\<lambda> s3. (previous_ex s3 A5 \<and> A6 s3) \<or> A7 s3) \<and>
(b1 = A2 s) \<and> (b2 = A5 s)"

lemma R4Pattern_rule: "
 R4Pattern_inv s0 t t1 b1 b2 A1 A2 A3 A4 A5 A6 A7 \<Longrightarrow>
(\<not> A1 s \<or> (b2 \<and> A6 s \<or> A7 s) \<or> (b1 \<or> A3 s) \<and> A4 s \<and> t2 > 0)  \<and>
(t1 = 0 \<or> (b2 \<and> A6 s \<or> A7 s) \<and> t1 \<le> t \<or> (b1 \<or> A3 s) \<and> A4 s  \<and> t1 < t2) \<and>
(b1' = A2 s)\<and> (b2' = A5 s) \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
 R4Pattern_inv s t t2 b1' b2' A1 A2 A3 A4 A5 A6 A7"
apply( unfold R4Pattern_inv_def)
 (* using P1'inv_rule1 previous_ex_one_point previous_all_one_point
  by (smt (z3))
*)


