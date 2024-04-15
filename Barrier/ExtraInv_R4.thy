theory ExtraInv_R4
  imports CommonExtraInv Requirements
begin

definition R4Pattern_inv where "R4Pattern_inv s t t1 b1 b2 A1 A2 A3 A4 A5 A6 A7 \<equiv> 
P1'inv s t t1 A1 (\<lambda> s2. (previous_all s2 A2 \<or> A3 s2) \<and> A4 s2) (\<lambda> s3. (previous_ex s3 A5 \<and> A6 s3) \<or> A7 s3) \<and>
(b1 \<longrightarrow> A2 s) \<and> (b2 \<longrightarrow> A5 s)"

lemma R4Pattern_rule: "
 R4Pattern_inv s0 t t1 b1 b2 A1 A2 A3 A4 A5 A6 A7 \<Longrightarrow>
((\<not> A1 s \<or> (b2 \<and> A6 s \<or> A7 s) \<or> ((b1 \<or> A3 s) \<and> A4 s) \<and> t2 > 0)  \<and>
(t1 = 0 \<or> (b2 \<and> A6 s \<or> A7 s) \<and> t1 \<le> t \<or> ((b1 \<or> A3 s) \<and> A4 s)  \<and> t1 < t2)) \<and>
(b1' \<longrightarrow> A2 s)\<and> (b2' \<longrightarrow> A5 s) \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
 R4Pattern_inv s t t2 b1' b2' A1 A2 A3 A4 A5 A6 A7"
apply( unfold R4Pattern_inv_def)
 (* using P1'inv_rule1 previous_ex_one_point previous_all_one_point
  by (smt (z3))
*)
  apply(erule conjE)
  apply(erule conjE)
  subgoal premises prems1
    apply(rule conjI)
     apply(insert prems1(1,2,4))[1]
     apply(erule P1'inv_rule_gen)
      apply simp
     apply(erule conjE)
    subgoal premises prems2
      apply(rule conjI)
       apply(insert prems2(1,2))[1]
       apply(erule disjE)
        apply(rule disjI1)
        apply simp
       apply(rule disjI2)
       apply(erule disjE)
        apply(rule disjI1)
        apply(erule disjE)
         apply(rule disjI1)
         apply(erule conjE)
      subgoal premises prems3
        apply(rule conjI)
         apply(insert prems3(1,2))[1]
         apply(rule previous_ex_one_point[of s0])
          apply simp
         apply (simp add: prems1(3))
        apply(insert prems3(1,3))
        apply simp
        done
        apply(rule disjI2)
        apply simp
       apply(rule disjI2)
       apply(erule conjE)
      subgoal premises prems3
        apply(rule conjI)
         apply(insert prems3(1,2))[1]
         apply(erule conjE)
        subgoal premises prems4
          apply(rule conjI)
           apply(insert prems4(1,2))[1]
           apply(erule disjE)
            apply(rule disjI1)
            apply(rule previous_all_one_point[of s0])
             apply simp
            apply (simp add: prems1(3))
           apply(rule disjI2)
           apply simp
          apply(insert prems4(1,3))
          apply simp
          done
        apply(insert prems3(1,3))
        apply simp
        done
      apply(insert prems2(1,3))
      apply(rule conjI)
       apply simp
      apply(rule conjI)
       apply simp
      apply(erule disjE)
       apply(rule disjI1)
       apply simp
      apply(rule disjI2)
      apply(erule disjE)
       apply(rule disjI1)
       apply(erule conjE)
      subgoal premises prems3
        apply(rule conjI)
         apply(insert prems3(1,2))[1]
         apply(erule disjE)
          apply(rule disjI1)
          apply(erule conjE)
        subgoal premises prems4
          apply(rule conjI)
           apply(insert prems4(1,2))[1]
           apply(rule previous_ex_one_point[of s0])
            apply simp
           apply (simp add: prems1(3))
          apply(insert prems4(1,3))
          apply simp
          done
         apply(rule disjI2)
         apply simp
        apply(insert prems3(1,3))
        apply simp
        done
      apply(rule disjI2)
      apply(erule conjE)
      subgoal premises prems3
        apply(rule conjI)
         apply(insert prems3(1,2))[1]
         apply(erule conjE)
        subgoal premises prems4
          apply(rule conjI)
           apply(insert prems4(1,2))[1]
           apply(erule disjE)
            apply(rule disjI1)
            apply(rule previous_all_one_point[of s0])
             apply simp
            apply (simp add: prems1(3))
           apply(rule disjI2)
           apply simp
          apply(insert prems4(1,3))
          apply simp
          done
        apply(insert prems3(1,3))
        apply simp
        done
      done
    apply(insert prems1(1,3,5))
    apply simp
    done
  done

lemma R4Pattern_einv2req: "R4Pattern_inv s t t1 b1 b2 A1 A2 A3 A4 A5 A6 A7 \<Longrightarrow> t1 \<le> t \<Longrightarrow> R4Pattern s t A1 A2 A3 A4 A5 A6 A7"
  apply(unfold R4Pattern_def R4Pattern_inv_def)
  using P1'einv2req_gen
  by force

definition extraInv where "extraInv s \<equiv> commonExtraInv s \<and>
R4Pattern_inv s (OPEN_TIME'TIMEOUT) (if getPstate s Opening' = Opening'open' then ltime s Opening' else 0)
 (getPstate s CarController' = CarController'waitingForCarPassing') (getPstate s CarController' = CarController'waitingForCar')
 (\<lambda> s1. getVarBool s1 green' = True) (\<lambda> s2. getVarBool s2 carInFront' = True) (\<lambda> s3. getVarBool s3 carInFront' = False)
(\<lambda> s4. getVarBool s4 down' = False \<and> getVarBool s4 opened' = True \<and> getVarBool s4 peCarUnder' = False) 
(\<lambda> s2. getVarBool s2 carInFront' = False) (\<lambda> s3. getVarBool s3 carInFront' = True)
(\<lambda> s4. getVarBool s4 down' = True \<or> getVarBool s4 opened' = False \<or> getVarBool s4 peCarUnder' = True)"

theorem extra1: "VC1 extraInv s0"
  apply(unfold VC1_def extraInv_def commonExtraInv_def R4Pattern_inv_def P1'inv_def always_def constrained_until_def previous_all_def previous_ex_def)
  apply auto
  done


theorem extra2: "VC2 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
apply(unfold VC2_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei2 VC2_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule R4Pattern_rule)
   apply(auto split: if_splits)
  done

theorem extra3: "VC3 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
apply(unfold VC3_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei3 VC3_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule R4Pattern_rule)
   apply(auto split: if_splits)
  done

theorem extra4: "VC4 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
apply(unfold VC4_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei4 VC4_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule R4Pattern_rule)
   apply(auto split: if_splits)
  done

theorem extra14: "VC14 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
apply(unfold VC14_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei14 VC14_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule R4Pattern_rule)
   apply(auto split: if_splits)
  done

theorem extra15: "VC15 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
apply(unfold VC15_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei15 VC15_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule R4Pattern_rule)
   apply(auto split: if_splits)
  done

theorem extra16: "VC16 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
apply(unfold VC16_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei16 VC16_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule R4Pattern_rule)
   apply(auto split: if_splits)
  done

theorem extra17: "VC17 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
apply(unfold VC17_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei17 VC17_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule R4Pattern_rule)
   apply(auto split: if_splits)
  done

theorem extra18: "VC18 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
apply(unfold VC18_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei18 VC18_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule R4Pattern_rule)
   apply(auto split: if_splits)
  done

theorem extra19: "VC19 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
apply(unfold VC19_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei19 VC19_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule R4Pattern_rule)
   apply(auto split: if_splits)
  done

theorem extra20: "VC20 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
apply(unfold VC20_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei20 VC20_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule R4Pattern_rule)
   apply(auto split: if_splits)
  done

theorem extra21: "VC21 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
apply(unfold VC21_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei21 VC21_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule R4Pattern_rule)
   apply(auto split: if_splits)
  done

theorem extra22: "VC22 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
apply(unfold VC22_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei22 VC22_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule R4Pattern_rule)
   apply(auto split: if_splits)
  done

theorem extra23: "VC23 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
apply(unfold VC23_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei23 VC23_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule R4Pattern_rule)
   apply(auto split: if_splits)
  done

theorem extra24: "VC24 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
apply(unfold VC24_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei24 VC24_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule R4Pattern_rule)
   apply(auto split: if_splits)
  done

theorem extra25: "VC25 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
apply(unfold VC25_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei25 VC25_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule R4Pattern_rule)
   apply(auto split: if_splits)
  done

theorem extra26: "VC26 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
apply(unfold VC26_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei26 VC26_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule R4Pattern_rule)
   apply(auto split: if_splits)
  done

theorem extra27: "VC27 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
apply(unfold VC27_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei27 VC27_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule R4Pattern_rule)
   apply(auto split: if_splits)
  done

theorem extra28: "VC28 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
apply(unfold VC28_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei28 VC28_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule R4Pattern_rule)
   apply(auto split: if_splits)
  done

theorem extra29: "VC29 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
apply(unfold VC29_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei29 VC29_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule R4Pattern_rule)
   apply(auto split: if_splits)
  done

theorem extra30: "VC30 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
apply(unfold VC30_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei30 VC30_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule R4Pattern_rule)
   apply(auto split: if_splits)
  done

theorem extra31: "VC31 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
apply(unfold VC31_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei31 VC31_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule R4Pattern_rule)
   apply(auto split: if_splits)
  done

theorem extra32: "VC32 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
apply(unfold VC32_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei32 VC32_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule R4Pattern_rule)
   apply(auto split: if_splits)
  done

theorem extra33: "VC33 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
apply(unfold VC33_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei33 VC33_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule R4Pattern_rule)
   apply(auto split: if_splits)
  done

theorem extra34: "VC34 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
apply(unfold VC34_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei34 VC34_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule R4Pattern_rule)
   apply(auto split: if_splits)
  done

theorem extra35: "VC35 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
apply(unfold VC35_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei35 VC35_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule R4Pattern_rule)
   apply(auto split: if_splits)
  done

theorem extra36: "VC36 extraInv env s0 carInFront'value peCarUnder'value opened'value closed'value"
apply(unfold VC36_def extraInv_def)
 apply(rule impI)
  apply(rule conjI)
  using cei36 VC36_def apply auto[1]
  apply(unfold commonExtraInv_def)
  apply(erule conjE)+
  apply(erule R4Pattern_rule)
   apply(auto split: if_splits)
  done

end
