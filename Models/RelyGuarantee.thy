theory RelyGuarantee
  imports PowerInvariant Evaluation
begin

definition quintuple :: "'a rel set \<Rightarrow> 'a rel set \<Rightarrow> 'a set top \<Rightarrow> 'a rel lan \<Rightarrow> 'a set top \<Rightarrow> bool" ("_, _ \<turnstile> \<lbrace>_\<rbrace> _ \<lbrace>_\<rbrace>") where
  "r, g \<turnstile> \<lbrace>p\<rbrace> c \<lbrace>q\<rbrace> \<longleftrightarrow> relyF r \<parallel> c \<triangleright> p \<le> q \<and> guar c \<le> g"

theorem weakening:
  assumes "r, g \<turnstile> \<lbrace>p\<rbrace> c1 \<lbrace>q\<rbrace>"
  and "r' \<le> r" and "g \<le> g'" and "p' \<le> p" and "q \<le> q'"
  shows "r', g' \<turnstile> \<lbrace>p'\<rbrace> c1 \<lbrace>q'\<rbrace>"
proof (simp add: quintuple_def, intro conjI)
  have "relyF r' \<parallel> c1 \<triangleright> p' \<le> relyF r \<parallel> c1 \<triangleright> p'"
    by (metis assms(2) mod2_isol par.mult_isol relyF_iso shuffle_comm)
  also have "... \<le> relyF r \<parallel> c1 \<triangleright> p"
    by (metis assms(4) mod2_isor)
  also have "... \<le> q"
    by (metis assms(1) quintuple_def)
  also have "... \<le> q'"
    by (metis assms(5))
  finally show "rely r' \<parallel> c1 \<triangleright> p' \<le> q'" .

  show "guar c1 \<le> g'"
    by (metis assms(1) assms(3) order_trans quintuple_def)
qed

theorem sequential:
  assumes "r, g \<turnstile> \<lbrace>p\<rbrace> c1 \<lbrace>q\<rbrace>" and "r, g \<turnstile> \<lbrace>q\<rbrace> c2 \<lbrace>s\<rbrace>"
  shows "r, g \<turnstile> \<lbrace>p\<rbrace> c1 \<cdot> c2 \<lbrace>s\<rbrace>"
proof -
  {
    have "rely r \<parallel> (c1 \<cdot> c2) \<triangleright> p \<le> (rely r \<parallel> c1) \<cdot> (rely r \<parallel> c2) \<triangleright> p"
      by (metis rely_l_prod mod2_isol)
    also have "... \<le> rely r \<parallel> c2 \<triangleright> rely r \<parallel> c1 \<triangleright> p"
      by (metis mod2_mult)
    also have "... \<le> rely r \<parallel> c2 \<triangleright> q"
      by (metis assms(1) mod2_isor quintuple_def)
    also have "... \<le> s"
      by (metis assms(2) quintuple_def)
    finally have "rely r \<parallel> (c1 \<cdot> c2) \<triangleright> p \<le> s" .
  }
  moreover
  {
    have "guar (c1 \<cdot> c2) \<le> guar c1 \<union> guar c2"
      by (metis guar_l_prod)
    also have "... \<le> g"
      by (metis assms(1) assms(2) le_sup_iff quintuple_def)
    finally have "guar (c1 \<cdot> c2) \<le> g" .
  }
  ultimately show ?thesis
    by (metis quintuple_def)
qed

corollary weakened_sequential:
  assumes "r1, g1 \<turnstile> \<lbrace>p\<rbrace> c1 \<lbrace>q\<rbrace>" and "r2, g2 \<turnstile> \<lbrace>q\<rbrace> c2 \<lbrace>s\<rbrace>"
  shows "(r1 \<inter> r2), (g1 \<union> g2) \<turnstile> \<lbrace>p\<rbrace> c1 \<cdot> c2 \<lbrace>s\<rbrace>"
  by (blast intro!: sequential[where q = q] weakening[OF assms(1)] weakening[OF assms(2)])

lemma "guar c \<le> g \<Longrightarrow> c \<le> rely g"
  apply (auto simp add: guar_def rely_def)

theorem parallel:
  assumes "r1, g1 \<turnstile> \<lbrace>p1\<rbrace> c1 \<lbrace>q1\<rbrace>" and "g2 \<le> r1"
  and "r2, g2 \<turnstile> \<lbrace>p2\<rbrace> c2 \<lbrace>q2\<rbrace>" and "g1 \<le> r2"
  shows "(r1 \<sqinter> r2), (g1 \<parallel> g2) \<turnstile> \<lbrace>p1 \<sqinter> p2\<rbrace> c1 \<parallel> c2 \<lbrace>q1 \<sqinter> q2\<rbrace>" 
proof (simp add: quintuple_def, intro conjI)
  have "rely (r1 \<inter> r2) \<parallel> (c1 \<parallel> c2) \<triangleright> inf p1 p2 \<le> rely (r1 \<inter> r2) \<parallel> (c1 \<parallel> c2) \<triangleright> p1"
    by (metis inf_le1 mod2_isor)
  also have "... \<le> rely r1 \<parallel> (c1 \<parallel> c2) \<triangleright> p1"
    by (metis Int_lower1 mod2_isol par.mult_isol rely_iso shuffle_comm)
  also have "... \<le> rely r1 \<parallel> (c1 \<parallel> rely g2) \<triangleright> p1"
    sledgehammer

end