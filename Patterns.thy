theory Patterns imports
Pattern1_Def
Pattern2_Def
Pattern3_Def
Pattern4_Def
Pattern5_Def
Pattern6_Def
Pattern7_Def
Pattern9_Def
Pattern10_Def
Pattern11_Def
Pattern12_Def
begin


lemma imp_rule: "(A1 \<Longrightarrow> \<not>A1') \<Longrightarrow> (A2 \<Longrightarrow> A2') \<Longrightarrow> A1 \<or> A2 \<Longrightarrow> A1' \<longrightarrow> A2'"
  by auto

end
