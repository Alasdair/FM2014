theory HoareLogic
  imports CKA
begin

context ckat begin

definition hoare_triple :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("\<lbrace> _ \<rbrace> _ \<lbrace> _ \<rbrace>" [54,54,54] 53)
  where "\<lbrace>p\<rbrace>x\<lbrace>q\<rbrace> \<equiv> p\<cdot>x = p\<cdot>x\<cdot>q \<and> p \<in> B \<and> q \<in> B"

declare hoare_triple_def [simp]

lemma hoare_equiv: "\<lbrace>p\<rbrace>x\<lbrace>q\<rbrace> = (p \<in> B \<and> q \<in> B \<and> p\<cdot>x \<le> p\<cdot>x\<cdot>q)"
  by (metis eq_iff hoare_triple_def mult_isol mult_oner test_top)

lemma hoare_equiv2: "\<lbrace>p\<rbrace>x\<lbrace>q\<rbrace> = (p \<in> B \<and> q \<in> B \<and> p\<cdot>x \<le> x\<cdot>q)"
  by (metis encoding_eq hoare_triple_def)

theorem composition_rule: "\<lbrakk>\<lbrace>p\<rbrace>x\<lbrace>q\<rbrace>; \<lbrace>q\<rbrace>y\<lbrace>r\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>p\<rbrace>x\<cdot>y\<lbrace>r\<rbrace>"
  by (smt hoare_triple_def mult_assoc)

theorem weakening_rule: "\<lbrakk>p \<in> B; p \<le> p'; \<lbrace>p'\<rbrace>x\<lbrace>q\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>p\<rbrace>x\<lbrace>q\<rbrace>"
  by (metis composition_rule encoding_eq hoare_triple_def mult_onel mult_oner)

theorem weakening_rule2: "\<lbrakk>\<lbrace>p\<rbrace>x\<lbrace>q'\<rbrace>; q' \<le> q; q \<in> B\<rbrakk> \<Longrightarrow> \<lbrace>p\<rbrace>x\<lbrace>q\<rbrace>"
  by (smt hoare_equiv hoare_triple_def mult_isol order_trans)

lemma pull_test: "\<lbrakk>p \<in> B; q \<in> B; \<lbrace>p\<cdot>q\<rbrace>x\<lbrace>r\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>p\<rbrace>q\<cdot>x\<lbrace>r\<rbrace>"
  by (metis hoare_triple_def mult_assoc)

theorem skip_rule: "\<lbrace>p\<rbrace>1\<lbrace>q\<rbrace> \<longleftrightarrow> (p \<le> q \<and> p \<in> B \<and> q \<in> B)"
  by (metis hoare_equiv2 mult_1_left mult_1_right)

corollary skip_true: "p \<in> B \<Longrightarrow> \<lbrace>p\<rbrace>1\<lbrace>p\<rbrace>"
  by (metis eq_refl skip_rule)

lemma choice: "\<lbrakk>\<lbrace>p\<rbrace>x\<lbrace>q\<rbrace>; \<lbrace>p\<rbrace>y\<lbrace>q\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>p\<rbrace>x+y\<lbrace>q\<rbrace>"
  by (smt hoare_triple_def distrib_right' distrib_left)

lemma failure: "\<lbrakk>p \<in> B; q \<in> B\<rbrakk> \<Longrightarrow> \<lbrace>p\<rbrace>0\<lbrace>q\<rbrace>"
  by (metis annil annir hoare_triple_def)

lemma iteration: "\<lbrace>p\<rbrace>x\<lbrace>p\<rbrace> \<Longrightarrow> \<lbrace>p\<rbrace>x\<^sup>\<star>\<lbrace>p\<rbrace>"
  by (metis hoare_equiv2 star_sim2)

lemma iteration2: "\<lbrace>p\<rbrace>x\<lbrace>p\<rbrace> \<Longrightarrow> \<lbrace>p\<rbrace>x\<^sup>+\<lbrace>p\<rbrace>"
  by (metis composition_rule iteration star_trancl)

theorem concurrency: "\<lbrakk>x = x\<cdot>q'; \<lbrace>p\<rbrace>x\<lbrace>q\<rbrace>; \<lbrace>p'\<rbrace>x'\<lbrace>q'\<rbrace>; x' = x'\<cdot>q\<rbrakk> \<Longrightarrow> \<lbrace>p\<parallel>p'\<rbrace>x\<parallel>x'\<lbrace>q\<parallel>q'\<rbrace>"
  by (metis hoare_triple_def mult_assoc par_comm test_exchanger test_par_closed)

theorem frame_rule: "\<lbrakk>r \<in> B; x\<cdot>r = x; r\<cdot>x = x; \<lbrace>p\<rbrace>x\<lbrace>q\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>p\<parallel>r\<rbrace>x\<lbrace>q\<parallel>r\<rbrace>"
  by (unfold hoare_triple_def, metis par_comm mult_assoc test_par_closed test_eq)

end

end
