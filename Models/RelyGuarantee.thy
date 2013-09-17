theory RelyGuarantee
  imports PowerInvariant Evaluation
begin

no_notation
  Transitive_Closure.trancl ("(_\<^sup>+)" [1000] 999)

definition trancl :: "'a lan \<Rightarrow> 'a lan" ("_\<^sup>+" [101] 100) where
  "x\<^sup>+ \<equiv> x\<cdot>x\<^sup>\<star>"

definition I :: "'a lan set" where
  "I \<equiv> {x. \<exists>y. x = \<iota> y}"

definition quintuple :: "'a rel lan \<Rightarrow> 'a rel lan \<Rightarrow> 'a set top \<Rightarrow> 'a rel lan \<Rightarrow> 'a set top \<Rightarrow> bool" ("_, _ \<turnstile> \<lbrace>_\<rbrace> _ \<lbrace>_\<rbrace>") where
  "r, g \<turnstile> \<lbrace>p\<rbrace> c \<lbrace>q\<rbrace> \<longleftrightarrow> r \<parallel> c \<triangleright> p \<le> q \<and> c \<le> g \<and> r \<in> I \<and> g \<in> I"

lemma inv_dist:
  assumes "r \<in> I" shows "r\<parallel>(x\<cdot>y) \<le> (r\<parallel>x)\<cdot>(r\<parallel>y)"
proof -
  obtain r' where [simp]: "r = \<iota> r'"
    using assms by (auto simp: I_def)
  thus ?thesis by simp (rule pow_inv1)
qed

lemma inv_mult_par: "r \<in> I \<Longrightarrow> s \<in> I \<Longrightarrow> r \<cdot> s \<le> r \<parallel> s"
  apply (simp add: I_def)
  apply (erule exE)+
  apply simp
  by (metis fin_l_prod_le_shuffle pow_inv_finite)

lemma inv_par_closed: "r \<in> I \<Longrightarrow> s \<in> I \<Longrightarrow> r \<parallel> s \<in> I"
  sorry

lemma sequential:
  assumes "r, g1 \<turnstile> \<lbrace>p\<rbrace> c1 \<lbrace>q\<rbrace>" and "r, g2 \<turnstile> \<lbrace>q\<rbrace> c2 \<lbrace>s\<rbrace>"
  shows "r, (g1 \<parallel> g2) \<turnstile> \<lbrace>p\<rbrace> c1 \<cdot> c2 \<lbrace>s\<rbrace>"
proof -
  have r_inv: "r \<in> I"
    by (metis assms(1) quintuple_def)

  {
    have "r \<parallel> (c1 \<cdot> c2) \<triangleright> p \<le> (r \<parallel> c1) \<cdot> (r \<parallel> c2) \<triangleright> p"
      by (metis inv_dist mod2_isol r_inv)
    also have "... \<le> r \<parallel> c2 \<triangleright> r \<parallel> c1 \<triangleright> p"
      by (metis mod2_mult)
    also have "... \<le> r \<parallel> c2 \<triangleright> q"
      by (metis assms(1) mod2_isor quintuple_def)
    also have "... \<le> s"
      by (metis assms(2) quintuple_def)
    finally have "r \<parallel> (c1 \<cdot> c2) \<triangleright> p \<le> s" .
  }
  moreover
  {
    have "c1 \<cdot> c2 \<le> g1 \<cdot> g2"
      by (metis assms(1) assms(2) quintuple_def seq.mult_isol_var)
    also have "... \<le> g1 \<parallel> g2"
      by (metis assms(1) assms(2) inv_mult_par quintuple_def)
    finally have "c1 \<cdot> c2 \<le> g1 \<parallel> g2" .
  }
  ultimately show ?thesis
    by (metis assms(1) assms(2) inv_par_closed quintuple_def)
qed

lemma parallel
  

end