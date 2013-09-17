theory PowerInvariant
  imports Language Topped
begin

definition pow_inv :: "'a set \<Rightarrow> 'a lan" ("\<iota>") where
  "pow_inv X \<equiv> {xs. lfinite xs \<and> lset xs \<subseteq> X}"

definition symbols :: "'a lan \<Rightarrow> 'a set" ("\<rho>") where
  "symbols X \<equiv> \<Union>xs\<in>X. lset xs"

lemma galois_connection: "X \<subseteq> FIN \<Longrightarrow> \<rho> X \<subseteq> Y \<longleftrightarrow> X \<subseteq> \<iota> Y"
  by (auto simp add: pow_inv_def symbols_def FIN_def)

lemma pow_inv_finite: "\<iota> X \<subseteq> FIN"
  by (auto simp add: pow_inv_def FIN_def)

lemma \<rho>_iso: "Y \<subseteq> FIN \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> \<rho> X \<subseteq> \<rho> Y"
  by (metis Int_absorb1 galois_connection le_infI1 order_refl)

lemma \<iota>_iso: "X \<subseteq> Y \<Longrightarrow> \<iota> X \<subseteq> \<iota> Y"
  by (metis galois_connection order_refl order_trans pow_inv_finite)

lemma pow_inv_par [simp]: "\<iota> r \<parallel> \<iota> r = \<iota> r"
  sorry

lemma pow_inv_l_prod_par: "\<iota> r \<cdot> \<iota> s \<le> \<iota> r \<parallel> \<iota> s"
  by (metis fin_l_prod_le_shuffle pow_inv_finite)

lemma pow_inv_exchange1: "\<iota> r \<cdot> (x \<parallel> y) \<subseteq> \<iota> r \<cdot> x \<parallel> \<iota> r \<cdot> y"
  using exchange[where A = "\<iota> r" and B = "\<iota> r", simplified, OF pow_inv_finite] .

lemma pow_inv1: "\<iota> r \<parallel> x \<cdot> y \<subseteq> (\<iota> r \<parallel> x) \<cdot> (\<iota> r \<parallel> y)"
  sorry

end