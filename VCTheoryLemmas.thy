theory VCTheoryLemmas
  imports VCTheory
begin

lemma substate_refl[simp]: "substate s s"
  apply(cases s)
         apply(auto)
  done

lemma substate_trans:
"substate s1 s2 \<Longrightarrow> substate s2 s3 \<Longrightarrow> substate s1 s3"
  apply((induction s3); (simp split: if_splits))
  done

lemma substate_antisym:
 "substate s1 s2 \<Longrightarrow> substate s2 s1 \<Longrightarrow> s1=s2"
  apply((induction s2 arbitrary: s1); (metis substate.simps substate_refl substate_trans))
  done 

(*
lemma toEnvP_imp_gtime_gt_0: "toEnvP s \<Longrightarrow> toEnvNum emptyState s > 0"
  apply(cases s)
           apply auto
  done


lemma predEnv_substate: "substate (predEnv s) s"
  apply(induction s)
   by auto


lemma substate_imp_substatete_predEnv_or_eq: 
"substate s1 s2 \<and> toEnvP s1 \<Longrightarrow> substate s1 (predEnv s2) \<or> s1=s2"
  apply((induction s2); (simp split: if_splits))
          apply auto
  done
*)

lemma substate_linear: 
"substate s1 s \<and> substate s2 s \<Longrightarrow>
 substate s1 s2 \<or> substate s2 s1"
  apply((induction s);(simp split: if_splits))
  done

lemma toEnvNum_id[simp]: "toEnvNum s s = 0"
  apply(cases s)
         apply(auto)
  done

lemma substate_toEnvNum_id:
"substate s1 s2 \<and> toEnvNum s1 s2 = 0 \<and> toEnvP s1 \<and>
toEnvP s2 \<Longrightarrow> s1=s2"
  apply((cases s2);(simp split: if_splits))
  done

(*
lemma predEnvPI: "\<not> toEnvP s \<and>
toEnvNum emptyState s > 0 \<longrightarrow>
toEnvP (predEnv s)"
  apply(induction s)
         apply(auto)
  done

lemma predEnvP: "toEnvNum emptyState s > 1 \<Longrightarrow>
toEnvP (predEnv s)"
  apply(induction s)
  using predEnvPI apply auto
  done

lemma toEnvP_substate_pred_imp_toEnvP_pred:
"toEnvP s1 \<and> substate s1 (predEnv s2) \<Longrightarrow> toEnvP (predEnv s2)"
  apply(induction s2)
            apply auto
  by (simp split: if_splits)

lemma gtime_predI:
 "\<not> toEnvP s \<Longrightarrow>   toEnvNum emptyState s =
 toEnvNum emptyState (predEnv s)"
  apply(induction s)
         apply(auto)
  done

lemma gtime_pred:
"toEnvP s \<longrightarrow> toEnvNum emptyState s =
toEnvNum emptyState (predEnv s) + 1"
  apply(induction s)
  using gtime_predI apply auto
  done


lemma shift_spec:
 "toEnvP s \<and> toEnvNum emptyState s > n \<Longrightarrow>
toEnvP (shift s n) \<and>
 toEnvNum emptyState (shift s n) =
 toEnvNum emptyState s - n"
  apply(induction n)
  using predEnvP apply auto
  using gtime_pred predEnvP
  by (metis Suc_eq_plus1 diff_Suc_1 diff_diff_eq) 
*)

lemma toEnvNum3: "substate s1 s2 \<and> substate s2 s3
 \<Longrightarrow> toEnvNum s1 s3 = toEnvNum s1 s2 + toEnvNum s2 s3"
  apply((induction s3); (simp split: if_splits); (meson substate.simps substate_antisym))
  done

lemma external_ltime[simp]: "toEnvP s \<Longrightarrow> ltime s p > 0"
  apply(cases s)
  by auto

(*
lemma emptyState_substate: "substate emptyState s"
  apply(induction s)
         apply(auto)
  done
*)

(*
lemma toEnvNum_substate1: "substate s1 s2 \<and> substate s2 s3 \<Longrightarrow> toEnvNum s1 s2 \<le> toEnvNum s1 s3"
  using toEnvNum3 apply auto
  done

lemma substate_imp_toEnvNum_le: "substate s1 s2 \<and> substate s2 s3 \<Longrightarrow> toEnvNum s2 s3 \<le> toEnvNum s1 s3"
  using toEnvNum3 apply auto
  done

lemma toEnvNum_eq_imp_eq1: "substate s1 s2 \<and> substate s1 s3 \<and> substate s2 s4 \<and> substate s3 s4 \<and> toEnvP s2 \<and> toEnvP s3 \<and>
toEnvNum s1 s2 = toEnvNum s1 s3 \<longrightarrow> s2=s3"
  using substate_linear toEnvNum3 substate_toEnvNum_id
  by (metis add_eq_self_zero)
*)

lemma toEnvNum_eq_imp_eq2: "substate s1 s3 \<and> substate s2 s3 \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s3 = toEnvNum s2 s3 \<Longrightarrow>
s1=s2"
  using substate_linear toEnvNum3 substate_toEnvNum_id
  by (metis add_cancel_left_left)

(*
lemma toEnvNum_le_imp_substate: "substate s1 s3 \<and> substate s2 s3 \<and> toEnvP s1 \<and> toEnvP s2 \<and>toEnvNum s2 s3 \<le> toEnvNum s1 s3 \<Longrightarrow> substate s1 s2"
  by (metis substate_linear substate_refl le_antisym substate_imp_toEnvNum_le toEnvNum_eq_imp_eq2)

lemma substate_or_eq_or_substate_pairs:
"toEnvP s1 \<and> toEnvP s2 \<and> toEnvP s3 \<and> toEnvP s4 \<and> substate s1 s2 \<and> substate s2 s \<and> substate s3 s4 \<and> substate s4 s \<and>
toEnvNum s1 s2 = 1 \<and> toEnvNum s3 s4 = 1 \<longrightarrow> substate s2 s3 \<or> s1=s3 \<and> s2=s4 \<or> substate s4 s1"
  apply(induction s)
           apply simp_all
  by (metis less_eq_nat.simps(1) substate_antisym toEnvNum_le_imp_substate)

lemma substate_or_substate_pair:
"toEnvP s1 \<and> toEnvP s2 \<and> toEnvP s3 \<and> substate s1 s \<and> substate s2 s3 \<and> substate s3 s \<and> toEnvNum s2 s3 = 1 \<longrightarrow>
substate s1 s2 \<or> substate s3 s1"
  by (metis add_Suc_right gr0_conv_Suc le_add2 mult.right_neutral not_gr_zero one_eq_mult_iff substate_linear substate_refl substate_toEnvNum_id toEnvNum_le_imp_substate verit_sum_simplify)
*)

(*
lemma shift_substate: "substate (shift s n) s"
  apply(induction n)
  using substate_refl apply auto
  using predEnv_substate substate_trans apply blast
  done


lemma toEnvNum_shift: "toEnvP s \<and>
toEnvNum emptyState s > n
  \<Longrightarrow> toEnvNum (shift s n) s = n"
  using shift_spec toEnvNum3 emptyState_substate
  by (metis add.right_neutral add_diff_inverse_nat diff_add_inverse diff_add_inverse2 diff_less_mono2 nat_diff_split not_gr_zero shift_substate)


lemma substate_shift:
"toEnvP s1 \<and> toEnvP s \<and> substate s1 s \<and> 
toEnvNum s1 s \<ge> n \<Longrightarrow> 
substate s1 (shift s n)"
  apply(induction n)
   apply auto
  using toEnvNum_shift
  by (metis diff_diff_cancel emptyState_substate less_imp_diff_less not_less_eq_eq
 substate_imp_substatete_predEnv_or_eq substate_imp_toEnvNum_le verit_comp_simplify1(3)) 


lemma predEnv_toEnvP_or_emptyState:
"toEnvP (predEnv s) \<or> predEnv s = emptyState"
  apply(induction s)
         apply(auto)
  done

lemma shiftEnvP_or_emptyState: "n \<noteq> 0 \<longrightarrow>
 toEnvP (shift s n) \<or> shift s n = emptyState"
  apply(cases n)
  using predEnv_toEnvP_or_emptyState by auto
*)

(*
lemma shift_toEnvNum: 
"toEnvP s \<and> toEnvP s1 \<and> substate s1 s \<Longrightarrow>
shift s (toEnvNum s1 s) = s1"
  apply(rule cut_rl[of "substate s1 (shift s (toEnvNum s1 s))"])
   apply(rule cut_rl[of "toEnvNum emptyState s1 > 0"])
    apply (smt (verit, del_insts) add_cancel_right_left emptyState_substate less_add_same_cancel2 linorder_not_less shift.simps(1)
 shiftEnvP_or_emptyState shift_substate substate_toEnvNum_id toEnvNum3 toEnvNum_shift substate_imp_toEnvNum_le)
   apply((cases s1);simp)
  using substate_shift apply auto
  done


lemma ltime_le_toEnvNum: 
"ltime s p \<le> toEnvNum emptyState s"
  apply(induction s)
         apply(auto)
  done


lemma predEnv_substate_imp_substate_or_eq:
"toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s \<and>
 substate s2 s \<and> substate (predEnv s1) s2 \<longrightarrow> 
 substate s1 s2 \<or> s2 = predEnv s1"
  using substate_antisym substate_imp_substatete_predEnv_or_eq substate_linear by blast
*)

end
