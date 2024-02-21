theory VCTheoryLemmas
  imports VCTheory
begin

lemma substate_refl: "substate s s"
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

lemma predEnv_substate: "substate (predEnv s) s"
  apply(induction s)
  using substate_refl  by auto

lemma substate_imp_substatete_predEnv_or_eq: 
"substate s1 s2 \<and> toEnvP s1 \<Longrightarrow> substate s1 (predEnv s2) \<or> s1=s2"
  apply((induction s2); (simp split: if_splits))
          apply auto
  done

lemma substate_linear: 
"substate s1 s \<and> substate s2 s \<longrightarrow>
 substate s1 s2 \<or> substate s2 s1"
  apply(induction s)
         apply(auto)
  done

lemma toEnvNum_id: "toEnvNum s s = 0"
  apply(cases s)
         apply(auto)
  done

lemma substate_toEnvNum_id:
"substate s1 s2 \<and> toEnvNum s1 s2 = 0 \<and> toEnvP s1 \<and>
toEnvP s2 \<longrightarrow> s1=s2"
  apply(cases s2)
         apply(auto)
  done

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

lemma toEnvNum3: "substate s1 s2 \<and> substate s2 s3
 \<Longrightarrow> toEnvNum s1 s3 = toEnvNum s1 s2 + toEnvNum s2 s3"
  apply((induction s3); (simp split: if_splits); (meson substate.simps substate_antisym))
  done

lemma emptyState_substate: "substate emptyState s"
  apply(induction s)
         apply(auto)
  done

lemma toEnvNum_substate1: "substate s1 s2 \<and> substate s2 s3 \<Longrightarrow> toEnvNum s1 s2 \<le> toEnvNum s1 s3"
  using toEnvNum3 apply auto
  done

lemma toEnvNum_substate2: "substate s1 s2 \<and> substate s2 s3 \<Longrightarrow> toEnvNum s2 s3 \<le> toEnvNum s1 s3"
  using toEnvNum3 apply auto
  done

lemma toEnvNum_eq_imp_eq1: "substate s1 s2 \<and> substate s1 s3 \<and> substate s2 s4 \<and> substate s3 s4 \<and> toEnvP s2 \<and> toEnvP s3 \<and>
toEnvNum s1 s2 = toEnvNum s1 s3 \<longrightarrow> s2=s3"
  using substate_linear toEnvNum3 substate_toEnvNum_id
  by (metis add_eq_self_zero)

lemma toEnvNum_eq_imp_eq2: "substate s1 s3 \<and> substate s2 s3 \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s3 = toEnvNum s2 s3 \<longrightarrow>
s1=s2"
  using substate_linear toEnvNum3 substate_toEnvNum_id
  by (metis add_cancel_left_left)

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
  by (metis diff_Suc_Suc diff_diff_cancel emptyState_substate less_imp_diff_less not_less_eq_eq substate_imp_substatete_predEnv_or_eq toEnvNum_substate2 verit_comp_simplify1(3)) 

lemma predEnv_toEnvP_or_emptyState:
"toEnvP (predEnv s) \<or> predEnv s = emptyState"
  apply(induction s)
         apply(auto)
  done

lemma shiftEnvP_or_emptyState: "n \<noteq> 0 \<longrightarrow>
 toEnvP (shift s n) \<or> shift s n = emptyState"
  apply(cases n)
  using predEnv_toEnvP_or_emptyState by auto

lemma shift_toEnvNum: 
"toEnvP s \<and> toEnvP s1 \<and> substate s1 s \<Longrightarrow>
shift s (toEnvNum s1 s) = s1"
  apply(rule cut_rl[of "substate s1 (shift s (toEnvNum s1 s))"])
   apply(rule cut_rl[of "toEnvNum emptyState s1 > 0"])
  apply (smt (verit, del_insts) add_cancel_right_left emptyState_substate less_add_same_cancel2 linorder_not_less shift.simps(1) shiftEnvP_or_emptyState shift_substate substate_toEnvNum_id toEnvNum3 toEnvNum_shift toEnvNum_substate2)
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


lemma substate_imp_toEnvNum_le: "substate s1 s2 \<and> substate s2 s3 \<Longrightarrow> toEnvNum s2 s3 \<le> toEnvNum s1 s3"
  using toEnvNum3 apply auto
  done

lemma toEnvNum_le_imp_substate: "substate s1 s3 \<and> substate s2 s3 \<and> toEnvP s1 \<and> toEnvP s2 \<and>toEnvNum s2 s3 \<le> toEnvNum s1 s3 \<Longrightarrow> substate s1 s2"
  by (metis substate_linear substate_refl le_antisym substate_imp_toEnvNum_le toEnvNum_eq_imp_eq2)


lemma substate_or_substate_pair:
"toEnvP s1 \<and> toEnvP s2 \<and> toEnvP s3 \<and> substate s1 s \<and> substate s2 s3 \<and> substate s3 s \<and> toEnvNum s2 s3 = 1 \<longrightarrow>
substate s1 s2 \<or> substate s3 s1"
  by (metis add_Suc_right gr0_conv_Suc le_add2 mult.right_neutral not_gr_zero one_eq_mult_iff substate_linear substate_refl substate_toEnvNum_id
 toEnvNum_le_imp_substate verit_sum_simplify)

lemma state_ind: 
"toEnvP s \<and> toEnvP s1 \<Longrightarrow> P s \<Longrightarrow>
 (\<And> s2. toEnvP s2 \<Longrightarrow>
 (substate s1 s2 \<and> substate s2 s \<and> s1 \<noteq> s2)
 \<Longrightarrow> P s2 \<Longrightarrow> P (predEnv s2)) \<Longrightarrow>
toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s \<longrightarrow>
 P s2"
proof -
  assume 1: "toEnvP s \<and> toEnvP s1"
  define Q:: "nat \<Rightarrow> bool" where 
"Q = (\<lambda> n. P (shift s n))"
  from Q_def  1 shift_toEnvNum have P_def:
"\<And> s'. toEnvP s' \<and> substate s' s \<Longrightarrow> 
P s' = Q (toEnvNum s' s)" by auto
  define n where "n = toEnvNum s2 s"
  assume base: "P s" and ind_step:
"\<And> s2. toEnvP s2 \<Longrightarrow>
 (substate s1 s2 \<and> substate s2 s \<and> s1 \<noteq> s2)
 \<Longrightarrow> P s2 \<Longrightarrow> P (predEnv s2)"
  show ?thesis
  proof
    assume 2: "toEnvP s2 \<and> substate s1 s2 \<and>
 substate s2 s"
    with 1  n_def shift_toEnvNum have s2_def: "s2 = shift s n"
      by auto
     from 2 show "P s2"
      apply(simp only: P_def n_def[symmetric])
      apply(simp only: s2_def)
    proof(induction n)
      case 0
      then show ?case using Q_def base by auto
    next
      case (Suc n)
      then show ?case 
        apply(simp only: Q_def)
        print_state
      proof cases
        assume 3: "s1 = shift s n"
        assume 4: "toEnvP (shift s (Suc n)) \<and>
    substate s1 (shift s (Suc n)) \<and>
    substate (shift s (Suc n)) s"
        from 3 have 5: "substate (shift s n) s1"
          using substate_refl by auto
        from predEnv_substate have
"substate (shift s (Suc n)) (shift s n)"
          by simp
        with 4 5  substate_antisym substate_trans
        have "s1 = shift s (Suc n)"
          by blast
        with 3 have
 "shift s n = shift s (Suc n)" by simp
        with 4 gtime_pred show
 "P (shift s (Suc n))" by fastforce
      next
        assume 3: "s1 \<noteq> shift s n"
        assume 4: "toEnvP (shift s (Suc n)) \<and>
    substate s1 (shift s (Suc n)) \<and>
    substate (shift s (Suc n)) s"
from predEnv_substate have
"substate (shift s (Suc n)) (shift s n)"
  by simp
  with 4 substate_trans have 5:
 "substate s1 (shift s n)" by blast
  have 6: "toEnvP (shift s n)"
  proof cases
    assume "n = 0"
    with 1 show ?thesis by auto
  next 
    assume "n \<noteq> 0"
    with shiftEnvP_or_emptyState have
"toEnvP (shift s n) \<or>
 (shift s n) =  emptyState" by auto
    thus ?thesis
    proof
      assume "toEnvP (shift s n)"
      thus ?thesis by assumption
    next
      assume "shift s n = emptyState"
      with 5 have "s1 = emptyState"
        by (cases s1; auto)
      with 1 show ?thesis by auto
    qed
  qed
  assume "(toEnvP (shift s n) \<and>
     substate s1 (shift s n) \<and>
     substate (shift s n) s \<Longrightarrow>
     P (shift s n))"
  with 3 5 6 shift_substate ind_step
  show "P (shift s (Suc n))"
    by auto
qed
qed
qed
qed

end
