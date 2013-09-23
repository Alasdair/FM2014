theory PowerInvariant
  imports Language Topped
begin

definition rely :: "'a set \<Rightarrow> 'a lan" where
  "rely X \<equiv> {xs. lset xs \<subseteq> X}"

definition guar :: "'a lan \<Rightarrow> 'a set" where
  "guar X \<equiv> \<Union>xs\<in>X. lset xs"

lemma shuffle_mono: "a \<le> b \<Longrightarrow> c \<le> d \<Longrightarrow> a \<parallel> c \<le> b \<parallel> d"
  by (metis par.mult_isol_var)

lemma inf_traces [intro!]: "x \<cdot> {} \<le> x"
  by (auto simp add: l_prod_def)

lemma [elim]: "lfinite zs \<Longrightarrow> zs \<in> xs \<sha> ys \<Longrightarrow> lfinite xs"
  apply (auto simp add: tshuffle_words_def)
  by (metis lfinite_lefts)

lemma [elim]: "lfinite zs \<Longrightarrow> zs \<in> xs \<sha> ys \<Longrightarrow> lfinite ys"
  apply (auto simp add: tshuffle_words_def)
  by (metis lfinite_rights)

lemma test1 [simp]: "(x \<parallel> y) \<inter> FIN = (x \<inter> FIN) \<parallel> (y \<inter> FIN)"
  apply (auto simp add: l_prod_def shuffle_def FIN_def)
  apply (rename_tac xs ys zs)
  apply (rule_tac x = "lmap \<langle>id,id\<rangle> ` (xs \<sha> ys)" in exI)
  apply (intro conjI)
  apply (rule_tac x = xs in exI)
  apply (rule_tac x = ys in exI)
  by (auto intro: lfinite_shuffle)

definition rshuffle :: "'a lan \<Rightarrow> 'a lan \<Rightarrow> 'a lan" (infixl "\<star>" 85) where
  "x \<star> y = (x \<inter> FIN) \<parallel> y"

lemma "x \<star> y \<le> x \<parallel> y"
  by (simp add: rshuffle_def, rule shuffle_mono, auto)

lemma rexchange: "(a \<star> b) \<parallel> (c \<star> d) = (a \<parallel> c) \<star> (b \<parallel> d)"
  apply (rule antisym)
  apply (simp_all add: rshuffle_def)
  apply (metis order_refl par.mult_assoc shuffle_comm)
  by (metis eq_iff par.mult_assoc shuffle_comm)

lemma [simp]: "x \<star> {LNil} = x \<inter> FIN"
  by (simp add: rshuffle_def)

lemma [simp]: "{LNil} \<star> x = x"
  by (simp add: rshuffle_def FIN_def)

lemmas rexchange_a = rexchange[where a = "{LNil}", simplified]
  and rexchange_b = rexchange[where b = "{LNil}", simplified]
  and rexchange_c = rexchange[where c = "{LNil}", simplified]
  and rexchange_d = rexchange[where d = "{LNil}", simplified]

thm rexchange_a
thm rexchange_b
thm rexchange_c
thm rexchange_d

definition fshuffle :: "'a lan \<Rightarrow> 'a lan \<Rightarrow> 'a lan" (infixl "\<diamondsuit>" 85) where
  "x \<diamondsuit> y = (x \<inter> FIN) \<parallel> (y \<inter> FIN)"

definition ishuffle :: "'a lan \<Rightarrow> 'a lan \<Rightarrow> 'a lan" (infixl "\<box>" 85) where
  "x \<box> y = (x \<cdot> {}) \<parallel> (y \<cdot> {})"

lemma [simp]: "(x \<cdot> {}) \<inter> FIN = {}"
  by (auto simp add: l_prod_def FIN_def)

lemma [simp]: "(x \<inter> FIN) \<cdot> {} = {}"
  by (auto simp add: l_prod_def FIN_def)

lemma [elim]: "lfinite zs \<Longrightarrow> zs \<in> xs \<sha> ys \<Longrightarrow> lfinite xs"
  apply (auto simp add: tshuffle_words_def)
  by (metis lfinite_lefts)

lemma [elim]: "lfinite zs \<Longrightarrow> zs \<in> xs \<sha> ys \<Longrightarrow> lfinite ys"
  apply (auto simp add: tshuffle_words_def)
  by (metis lfinite_rights)

lemma test1 [simp]: "(x \<parallel> y) \<inter> FIN = (x \<inter> FIN) \<parallel> (y \<inter> FIN)"
  apply (auto simp add: l_prod_def shuffle_def FIN_def)
  apply (rename_tac xs ys zs)
  apply (rule_tac x = "lmap \<langle>id,id\<rangle> ` (xs \<sha> ys)" in exI)
  apply (intro conjI)
  apply (rule_tac x = xs in exI)
  apply (rule_tac x = ys in exI)
  by (auto intro: lfinite_shuffle)

lemma [simp]: "(x \<parallel> y) \<cdot> {} = (x \<parallel> y \<cdot> {}) \<union> (x \<cdot> {} \<parallel> y)"
  apply (auto simp add: l_prod_def shuffle_def)
  apply (rename_tac xs ys zs)
  apply (rule_tac x = "lmap \<langle>id,id\<rangle> ` (xs \<sha> ys)" in exI)
  apply (intro conjI)
  apply (rule_tac x = xs in exI)
  apply (rule_tac x = ys in exI)
  apply (intro conjI)
  apply simp_all
  apply (metis imageI lfinite_shuffle)
  apply (metis (mono_tags) lfinite_lefts mem_Collect_eq tshuffle_words_def)
  by (metis (mono_tags) lfinite_rights mem_Collect_eq tshuffle_words_def)

lemma [simp]: "(x \<box> y) \<diamondsuit> z = {}"
  by (simp add: fshuffle_def ishuffle_def)

lemma [simp]: "(x \<diamondsuit> y) \<box> z = {}"
  by (simp add: fshuffle_def ishuffle_def)

lemma [simp]: "x \<box> (y \<diamondsuit> z) = {}"
  by (simp add: fshuffle_def ishuffle_def)

lemma [simp]: "x \<diamondsuit> (y \<box> z) = {}"
  by (simp add: fshuffle_def ishuffle_def)

lemma [simp]: "x \<box> (y \<union> z) = x \<box> y \<union> x \<box> z"
  sorry

lemma [simp]: "(x \<union> y) \<box> z = x \<box> z \<union> y \<box> z"
  sorry

lemma [simp]: "x \<diamondsuit> (y \<union> z) = x \<diamondsuit> y \<union> x \<diamondsuit> z"
  sorry

lemma [simp]: "(x \<union> y) \<diamondsuit> z = x \<diamondsuit> z \<union> y \<diamondsuit> z"
  sorry

lemma [simp]: "x \<diamondsuit> (y \<diamondsuit> z) = x \<diamondsuit> y \<diamondsuit> z"
  sorry

lemma [simp]: "x \<box> (y \<box> z) = x \<box> y \<box> z"
  sorry

lemma [simp]: "(x \<parallel> y) \<inter> FIN = x \<diamondsuit> y"
  sorry

declare test1[simp del]

definition pshuffle :: "'a lan \<Rightarrow> 'a lan \<Rightarrow> 'a lan" (infixl "\<bullet>" 85) where
  "x \<bullet> y = (x \<inter> FIN) \<parallel> (y \<inter> FIN) \<union> (x \<cdot> {}) \<parallel> (y \<cdot> {})" 

lemma pshuffle_bd: "x \<bullet> y = x \<diamondsuit> y \<union> x \<box> y"
  by (simp add: pshuffle_def fshuffle_def ishuffle_def)

lemma inf_traces: "x \<cdot> {} \<le> x"
  by (auto simp add: l_prod_def)

lemma pshuffle_le: "x \<bullet> y \<le> x \<parallel> y"
  apply (simp add: pshuffle_def, intro conjI)
  apply (metis inf_traces par.mult_isol_var)
  by (metis inf_commute inf_le2 par.mult_isol_var)

lemma pshuffle_assoc: "(x \<bullet> y) \<bullet> z = x \<bullet> (y \<bullet> z)"
  by (simp add: pshuffle_bd)

lemma shuffle_mono: "a \<le> b \<Longrightarrow> c \<le> d \<Longrightarrow> a \<parallel> c \<le> b \<parallel> d"
  by (metis par.mult_isol_var)

lemma [simp]: "a \<diamondsuit> b \<parallel> c \<diamondsuit> d = (a \<parallel> c) \<diamondsuit> (b \<parallel> d)"
  apply (simp add: fshuffle_def)
  by (metis fshuffle_def par.mult_assoc shuffle_comm test1)

lemma iexchange [simp]: "a \<box> b \<parallel> c \<box> d \<subseteq> (a \<parallel> c) \<box> (b \<parallel> d)"
  apply (simp add: ishuffle_def shuffle_dist par.distrib_right' shuffle_assoc[symmetric])
  apply (rule le_supI1)
  apply (rule shuffle_mono)
  apply (simp add: shuffle_assoc)
  apply (rule shuffle_mono)
  apply (rule inf_traces)
  apply (subst shuffle_comm)
  apply (rule shuffle_mono)
  by (intro order_refl inf_traces)+

lemma rely_exchange: "(a \<bullet> b) \<parallel> (c \<bullet> d) \<subseteq> (a \<parallel> c) \<bullet> (b \<parallel> d)"
  apply (simp add: pshuffle_bd shuffle_dist par.distrib_right')
  apply (intro conjI)
  prefer 2
  apply (rule le_supI2)
  apply (rule iexchange)
  apply (rule le_supI2)
  apply (simp add: fshuffle_def ishuffle_def shuffle_dist par.distrib_right')
  apply (rule le_supI1)
  apply (simp add: shuffle_assoc)
  apply (rule shuffle_mono)
  apply simp
  apply (subst shuffle_comm)
  apply (simp add: shuffle_assoc)
  apply (rule shuffle_mono)
  apply simp
  apply (subst shuffle_comm)
  apply (rule shuffle_mono)
  apply simp_all
  apply (rule le_supI2)
  apply (simp add: fshuffle_def ishuffle_def shuffle_dist par.distrib_right')
  apply (rule le_supI2)+
  apply (simp add: shuffle_assoc)
  apply (rule shuffle_mono)
  apply simp
  apply (subst shuffle_comm)
  apply (simp add: shuffle_assoc)
  apply (rule shuffle_mono)
  apply simp
  apply (subst shuffle_comm)
  apply (rule shuffle_mono)
  by simp_all

lemma rely_exchange2: "(a \<parallel> c) \<bullet> (b \<parallel> d) \<subseteq> (a \<bullet> b) \<parallel> (c \<bullet> d)"

lemma [simp]: "x \<bullet> {LNil} = x \<inter> FIN"
  by (simp add: pshuffle_def FIN_def)

lemma [simp]: "{LNil} \<bullet> x = x \<inter> FIN"
  by (simp add: pshuffle_def FIN_def)

thm rely_exchange[where a = "{LNil}", simplified]
thm rely_exchange[where b = "{LNil}", simplified]
thm rely_exchange[where c = "{LNil}", simplified]
thm rely_exchange[where d = "{LNil}", simplified]

lemma finite_infinite_split: "y = (y \<inter> FIN) \<union> (y \<cdot> {})"
  sorry

lemma "x \<parallel> (y \<inter> FIN) \<union> x \<parallel> (y \<cdot> {}) = x \<parallel> y"
  by (metis finite_infinite_split par.distrib_left)

lemma par_inter: "x \<parallel> y \<union> x \<parallel> (y \<inter> z) = x \<parallel> y"
  by (metis par.distrib_left sup_inf_absorb)

lemma shuffle_assoc_var: "(a \<parallel> b) \<parallel> (c \<parallel> d) = a \<parallel> b \<parallel> c \<parallel> d"
  sorry

lemma test4: "b \<subseteq> c \<union> d \<Longrightarrow> a \<parallel> b \<subseteq> a \<parallel> c \<union> a \<parallel> d"
  by (metis par.distrib_left par.mult_isol)

find_theorems "_ \<le> _ \<Longrightarrow> _ \<le> sup _ _"

lemma test5: "x \<parallel> y \<cdot> {} \<subseteq> (x \<parallel> y) \<cdot> {}"
  by (metis par.order_prop test3)

lemma test6: "x \<cdot> {} \<parallel> z \<union> (x \<inter> FIN) \<parallel> z = x \<parallel> z"
  by (metis finite_infinite_split par.add_comm par.distrib_left shuffle_comm)


lemma "x \<bullet> (y \<parallel> z) \<subseteq> (x \<bullet> y) \<parallel> z"
proof (simp add: pshuffle_def par.distrib_right' shuffle_dist test2 test3, intro conjI)
  have "(x \<inter> FIN) \<parallel> ((y \<inter> FIN) \<parallel> (z \<inter> FIN)) \<subseteq> (x \<inter> FIN) \<parallel> (y \<cdot> {} \<parallel> z) \<union> (x \<inter> FIN) \<parallel> ((y \<inter> FIN) \<parallel> z)"
    apply (rule test4)
    apply (rule le_supI2)
    by (metis inf.commute inf_le2 par.mult_isor shuffle_comm)
  also have "... \<subseteq> x \<parallel> (y \<cdot> {} \<parallel> z) \<union> (x \<inter> FIN) \<parallel> ((y \<inter> FIN) \<parallel> z)"
    apply (rule sup_mono)
    apply simp_all
    by (metis inf_commute inf_le2 par.mult_isor)
  finally show "(x \<inter> FIN) \<parallel> ((y \<inter> FIN) \<parallel> (z \<inter> FIN)) \<subseteq> x \<parallel> y \<cdot> {} \<parallel> z \<union> (x \<inter> FIN) \<parallel> (y \<inter> FIN) \<parallel> z"
    by (metis par.mult_assoc)

  have "x \<parallel> (y \<parallel> z \<cdot> {}) \<subseteq> x \<parallel> y \<cdot> {} \<parallel> z \<union> (x \<inter> FIN) \<parallel> (y \<inter> FIN) \<parallel> z"
    sledgehammer

lemma "x \<parallel> y \<cdot> {} \<subseteq> (x \<parallel> y) \<cdot> {}"
  

lemma "x \<parallel> y \<cdot> {} \<parallel> z \<union> x \<parallel> (y \<inter> FIN) \<parallel> z"

lemma "(a \<bullet> b) \<parallel> (c \<bullet> d) \<subseteq> (a \<parallel> c) \<bullet> (b \<parallel> d)"
  oops

lemma galois_connection: "(X \<subseteq> FIN \<and> guar X \<subseteq> Y) \<longleftrightarrow> X \<subseteq> rely Y"
  by (auto simp add: rely_def guar_def FIN_def)

lemma galois_connection_var: "X \<subseteq> FIN \<Longrightarrow> guar X \<subseteq> Y \<longleftrightarrow> X \<subseteq> rely Y"
  by (metis galois_connection)

lemma guar_iso: "X \<subseteq> Y \<Longrightarrow> guar X \<subseteq> guar Y"
  by (auto simp add: guar_def)

lemma rely_iso: "X \<subseteq> Y \<Longrightarrow> rely X \<subseteq> rely Y"
  by (metis galois_connection order_refl order_trans)

lemma rely_prod: "rely r \<cdot> rely r = rely r"
  apply (simp add: rely_def)
  apply (subst fin_l_prod)
  apply simp
  apply (auto simp add: FIN_def)
  by (metis empty_subsetI lappend_LNil1 lfinite_code(1) lset_LNil)

lemma rely_finite: "rely r \<subseteq> FIN"
  by (metis galois_connection order_refl)

lemma rely_prod_le_shuffle: "rely r \<cdot> rely s \<subseteq> rely r \<parallel> rely s"
  by (metis fin_l_prod_le_shuffle rely_finite)

lemma tshuffle_lsetl [elim]: "xs \<in> ys \<sha> zs \<Longrightarrow> Inl x \<in> lset xs \<Longrightarrow> x \<in> lset ys"
  by (auto simp add: tshuffle_words_def lefts_def image_def) (metis is_left.simps(1) unl.simps(1))

lemma tshuffle_lsetr [elim]: "xs \<in> ys \<sha> zs \<Longrightarrow> Inr x \<in> lset xs \<Longrightarrow> x \<in> lset zs"
  by (auto simp add: tshuffle_words_def rights_def image_def) (metis is_right.simps(1) unr.simps(1))

lemma rely_par_Un: "rely r \<parallel> rely s \<subseteq> rely (r \<union> s)"
proof -
  have "rely r \<parallel> rely s \<subseteq> FIN"
    by (metis fin_shuffle rely_finite)
  moreover have "guar (rely r \<parallel> rely s) \<subseteq> r \<union> s"
  proof (auto simp add: guar_def shuffle_def)
    fix xs ys zs z
    assume "(case z of Inl x \<Rightarrow> id x | Inr x \<Rightarrow> id x) \<notin> s" and "zs \<in> xs \<sha> ys"
    and "xs \<in> rely r" and "ys \<in> rely s" and "z \<in> lset zs"
    thus "(case z of Inl x \<Rightarrow> id x | Inr x \<Rightarrow> id x) \<in> r"
      by (cases z, auto simp add: rely_def) (metis in_mono tshuffle_lsetr)
  qed
  ultimately show ?thesis
    by (simp add: galois_connection[symmetric])
qed

lemma rely_par_le: "rely r \<parallel> rely r \<subseteq> rely r"
proof (auto intro: lfinite_shuffle simp add: shuffle_def rely_def FIN_def)
  fix zs ys xs x
  assume "xs \<in> zs \<sha> ys" and "lset zs \<subseteq> r" and "lfinite zs" and "lset ys \<subseteq> r" and "lfinite ys" and "x \<in> lset xs"
  thus "(case x of Inl x \<Rightarrow> id x | Inr x \<Rightarrow> id x) \<in> r"
    by (cases x) auto
qed

lemma rely_par_idem [simp]: "rely r \<parallel> rely r = rely r"
  by (metis rely_par_le rely_prod rely_prod_le_shuffle subset_antisym)

lemma rely_prod_par: "rely r \<cdot> rely r = rely r \<parallel> rely r"
  by (metis rely_par_idem rely_prod)

lemma rely_lappend [simp]: "(\<exists>rs. rs \<in> rely r \<and> rs = rs' \<frown> rs'') \<longleftrightarrow> (rs' \<in> rely r \<and> rs'' \<in> rely r)"
  by (auto simp add: rely_def FIN_def)

lemma lappend_in_l_prod: "lfinite xs \<Longrightarrow> xs \<in> X \<Longrightarrow> ys \<in> Y \<Longrightarrow> xs \<frown> ys \<in> X \<cdot> Y"
  by (auto simp add: l_prod_def)

lemma LCons_cont [simp]: "LCons x ` \<Union>{f xs ys|xs ys. P xs ys} = \<Union>{LCons x ` f xs ys|xs ys. P xs ys}"
  by (auto simp add: image_def)

lemma [simp]: "LCons x ` (ys \<cdot> zs) = LCons x ` ys \<cdot> zs"
  apply (auto simp add: l_prod_def)
  apply (metis image_eqI lappend_LCons lfinite_LCons)
  by (metis image_eqI lappend_LCons lfinite_LCons)

lemma tshuffle_image1: "LCons (Inl x) ` (xs \<sha> ys) \<subseteq> LCons x xs \<sha> ys"
  by (auto simp add: tshuffle_words_def)

lemma tshuffle_image2: "LCons (Inr y) ` (xs \<sha> ys) \<subseteq> xs \<sha> LCons y ys"
  by (auto simp add: tshuffle_words_def)

lemma rely_dist: "lfinite rs \<Longrightarrow> lfinite xs \<Longrightarrow> rs \<sha> (xs \<frown> ys) \<subseteq> \<Union>{(rs' \<sha> xs) \<cdot> (rs'' \<sha> ys) |rs' rs''. rs = rs' \<frown> rs''}"
proof (induct rs arbitrary: xs rule: lfinite_induct)
  case Nil
  thus ?case
    apply simp
    apply (rule_tac x = "{lmap Inr (xs \<frown> ys)}" in exI)
    apply simp
    apply (rule exI[of _ LNil])+
    by (auto simp add: l_prod_def lmap_lappend_distrib)
next
  case (Cons r rs) note ih_rs = this
  from Cons.prems show ?case
  proof (induct xs rule: lfinite_induct)
    case Nil
    show ?case
      apply auto
      apply (rule_tac x = "LCons r rs \<sha> ys" in exI)
      apply simp
      apply (rule_tac x = LNil in exI)
      by simp
  next
    case (Cons z zs)
    hence z_zs_finite: "lfinite (LCons z zs)"
      by (metis lfinite_LCons)
    have "LCons r rs \<sha> (LCons z zs \<frown> ys) = LCons r rs \<sha> (LCons z (zs \<frown> ys))"
      by simp
    also have "... = LCons (Inl r) ` (rs \<sha> LCons z (zs \<frown> ys)) \<union> LCons (Inr z) ` (LCons r rs \<sha> (zs \<frown> ys))"
      by (simp only: LCons_tshuffle)
    also have "... = LCons (Inl r) ` (rs \<sha> (LCons z zs \<frown> ys)) \<union> LCons (Inr z) ` (LCons r rs \<sha> (zs \<frown> ys))"
      by simp
    also have "... \<subseteq> LCons (Inl r) ` \<Union>{(rs' \<sha> LCons z zs) \<cdot> (rs'' \<sha> ys) |rs' rs''. rs = rs' \<frown> rs''} \<union> LCons (Inr z) ` \<Union>{(rs' \<sha> zs) \<cdot> (rs'' \<sha> ys) |rs' rs''. LCons r rs = rs' \<frown> rs''}"
      by (rule sup_mono[OF image_mono[OF ih_rs(2)[OF z_zs_finite]] image_mono[OF Cons(2)]])
    also have "... = \<Union>{LCons (Inl r) ` ((rs' \<sha> LCons z zs) \<cdot> (rs'' \<sha> ys)) |rs' rs''. rs = rs' \<frown> rs''} \<union> \<Union>{LCons (Inr z) ` ((rs' \<sha> zs) \<cdot> (rs'' \<sha> ys)) |rs' rs''. LCons r rs = rs' \<frown> rs''}"
      by simp
    also have "... \<subseteq> \<Union>{(rs' \<sha> LCons z zs) \<cdot> (rs'' \<sha> ys) |rs' rs''. LCons r rs = rs' \<frown> rs''} \<union> \<Union>{LCons (Inr z) ` ((rs' \<sha> zs) \<cdot> (rs'' \<sha> ys)) |rs' rs''. LCons r rs = rs' \<frown> rs''}"
      apply (rule sup_mono[OF _ order_refl])
      apply (rule Sup_mono)
      apply auto
      apply (rule_tac x = "(LCons r rs' \<sha> LCons z zs) \<cdot> (rs'' \<sha> ys)" in exI)
      apply (intro conjI)
      apply (rule_tac x = "LCons r rs'" in exI)
      apply (rule_tac x = rs'' in exI)
      apply simp
      by (intro l_prod_isol tshuffle_image1)
    also have "... \<subseteq> \<Union>{(rs' \<sha> LCons z zs) \<cdot> (rs'' \<sha> ys) |rs' rs''. LCons r rs = rs' \<frown> rs''} \<union> \<Union>{(rs' \<sha> LCons z zs) \<cdot> (rs'' \<sha> ys) |rs' rs''. LCons r rs = rs' \<frown> rs''}"
      apply (rule sup_mono[OF order_refl _])
      apply (rule Sup_mono)
      apply auto
      apply (rule_tac x = "(rs' \<sha> LCons z zs) \<cdot> (rs'' \<sha> ys)" in exI)
      apply (intro conjI)
      apply (rule_tac x = rs' in exI)
      apply (rule_tac x = rs'' in exI)
      apply simp
      by (intro l_prod_isol tshuffle_image2)
    also have "... = \<Union>{(rs' \<sha> LCons z zs) \<cdot> (rs'' \<sha> ys) |rs' rs''. LCons r rs = rs' \<frown> rs''}"
      by simp
    finally show ?case .
  qed
qed

lemma set_comp_Union_iso3: "(\<And>x y z. P x y z \<Longrightarrow> f x y z \<subseteq> g x y z) \<Longrightarrow> \<Union>{f x y z |x y z. P x y z} \<subseteq> \<Union>{g x y z |x y z. P x y z}"
  by auto (metis in_mono)

lemma set_comp_Union_eq4: "(\<And>x y z w. P x y z w \<Longrightarrow> f x y z w = g x y z w) \<Longrightarrow> \<Union>{f x y z w |x y z w. P x y z w} = \<Union>{g x y z w |x y z w. P x y z w}"
  by auto metis+

lemma set_comp_Union_eq3: "(\<And>x y z. P x y z \<Longrightarrow> f x y z = g x y z) \<Longrightarrow> \<Union>{f x y z |x y z. P x y z} = \<Union>{g x y z |x y z. P x y z}"
  by auto metis+

lemma set_comp_Union_eq2: "(\<And>x y z. P x y \<Longrightarrow> f x y = g x y) \<Longrightarrow> \<Union>{f x y |x y. P x y} = \<Union>{g x y |x y. P x y}"
  by auto

lemma [simp]: "lmap \<langle>id,id\<rangle> ` (x \<cdot> y) = lmap \<langle>id,id\<rangle> ` x \<cdot> lmap \<langle>id,id\<rangle> ` y"
  apply (simp add: image_def)
  apply (auto simp add: l_prod_def)
  apply (metis lfinite_lmap lmap_lappend_distrib)
  apply (metis lfinite_lmap lmap_lappend_distrib)
  by (metis l_prod_def lappend_in_l_prod lmap_lappend_distrib par.add_comm)

lemma guar_l_prod: "guar (x \<cdot> y) \<subseteq> guar x \<union> guar y"
  by (auto simp add: guar_def l_prod_def)

lemma rely_l_prod: "rely r \<parallel> x \<cdot> y \<subseteq> (rely r \<parallel> x) \<cdot> (rely r \<parallel> y)"
proof -
  let ?lhs_inf = "\<Union>{lmap \<langle>id,id\<rangle> ` (rs \<sha> xs) |rs xs. rs \<in> rely r \<and> xs \<in> x \<and> \<not> lfinite xs}"
  let ?lhs_fin = "\<Union>{lmap \<langle>id,id\<rangle> ` (rs \<sha> (xs \<frown> ys)) |rs xs ys. rs \<in> rely r \<and> xs \<in> x \<and> ys \<in> y \<and> lfinite xs}"

  have inf_case: "?lhs_inf \<subseteq> \<Union>{lmap \<langle>id,id\<rangle> ` (rs \<sha> xs) |rs xs. rs \<in> rely r \<and> xs \<in> x} \<cdot> \<Union>{lmap \<langle>id,id\<rangle> ` (rs \<sha> ys) |rs ys. rs \<in> rely r \<and> ys \<in> y}"
    by (auto simp only: l_prod_def) (metis (lifting, full_types) lfinite_lmap lfinite_rights mem_Collect_eq tshuffle_words_def)

  have "?lhs_fin \<subseteq> \<Union>{lmap \<langle>id,id\<rangle> ` \<Union>{(rs' \<sha> xs) \<cdot> (rs'' \<sha> ys) |rs' rs''. rs = rs' \<frown> rs''} |rs xs ys. rs \<in> rely r \<and> xs \<in> x \<and> ys \<in> y \<and> lfinite xs}"
    by (intro set_comp_Union_iso3 image_mono rely_dist) (auto simp add: rely_def FIN_def)
  also have "... \<subseteq> \<Union>{\<Union>{lmap \<langle>id,id\<rangle> ` ((rs' \<sha> xs) \<cdot> (rs'' \<sha> ys)) |rs' rs''. rs = rs' \<frown> rs''} |rs xs ys. rs \<in> rely r \<and> xs \<in> x \<and> ys \<in> y \<and> lfinite xs}"
    by (rule set_comp_Union_iso3) blast
  also have "... = \<Union>{\<Union>{lmap \<langle>id,id\<rangle> ` (rs' \<sha> xs) \<cdot> lmap \<langle>id,id\<rangle> ` (rs'' \<sha> ys) |rs' rs''. rs = rs' \<frown> rs''} |rs xs ys. rs \<in> rely r \<and> xs \<in> x \<and> ys \<in> y \<and> lfinite xs}"
    by simp
  also have "... = \<Union>{lmap \<langle>id,id\<rangle> ` (rs' \<sha> xs) \<cdot> lmap \<langle>id,id\<rangle> ` (rs'' \<sha> ys) |rs' rs'' rs xs ys. rs = rs' \<frown> rs'' \<and> rs \<in> rely r \<and> xs \<in> x \<and> ys \<in> y \<and> lfinite xs}"
    by blast
  also have "... = \<Union>{lmap \<langle>id,id\<rangle> ` (rs' \<sha> xs) \<cdot> lmap \<langle>id,id\<rangle> ` (rs'' \<sha> ys) |rs' rs'' xs ys. (\<exists>rs. rs \<in> rely r \<and> rs = rs' \<frown> rs'') \<and> xs \<in> x \<and> ys \<in> y \<and> lfinite xs}"
    by blast
  also have "... = \<Union>{lmap \<langle>id,id\<rangle> ` (rs' \<sha> xs) \<cdot> lmap \<langle>id,id\<rangle> ` (rs'' \<sha> ys) |rs' rs'' xs ys. rs' \<in> rely r \<and> rs'' \<in> rely r \<and> xs \<in> x \<and> ys \<in> y \<and> lfinite xs}"
    by simp
  also have "... = \<Union>{{zs \<frown> ws |zs ws. zs \<in> lmap \<langle>id,id\<rangle> ` (rs' \<sha> xs) \<and> ws \<in> lmap \<langle>id,id\<rangle> ` (rs'' \<sha> ys)} |rs' rs'' xs ys. rs' \<in> rely r \<and> rs'' \<in> rely r \<and> xs \<in> x \<and> ys \<in> y \<and> lfinite xs}"
    apply (rule set_comp_Union_eq4)
    apply (erule conjE)
    apply (subst fin_l_prod)
    apply (auto simp add: FIN_def)
    by (metis (full_types) FIN_def in_mono lfinite_shuffle mem_Collect_eq rely_finite)
  also have "... = \<Union>{lmap \<langle>id,id\<rangle> ` (rs \<sha> xs) |rs xs. rs \<in> rely r \<and> xs \<in> x \<and> lfinite xs} \<cdot> \<Union>{lmap \<langle>id,id\<rangle> ` (rs \<sha> ys) |rs ys. rs \<in> rely r \<and> ys \<in> y}"
    apply (subst fin_l_prod)
    apply (simp add: FIN_def)
    apply clarify
    apply (metis (full_types) FIN_def lfinite_lmap lfinite_shuffle mem_Collect_eq rely_finite set_mp)
    by blast
  also have "... \<subseteq> \<Union>{lmap \<langle>id,id\<rangle> ` (rs \<sha> xs) |rs xs. rs \<in> rely r \<and> xs \<in> x} \<cdot> \<Union>{lmap \<langle>id,id\<rangle> ` (rs \<sha> ys) |rs ys. rs \<in> rely r \<and> ys \<in> y}"
    by (auto intro!: l_prod_isol)
  finally have fin_case: "?lhs_fin \<subseteq> \<Union>{lmap \<langle>id,id\<rangle> ` (rs \<sha> xs) |rs xs. rs \<in> rely r \<and> xs \<in> x} \<cdot> \<Union>{lmap \<langle>id,id\<rangle> ` (rs \<sha> ys) |rs ys. rs \<in> rely r \<and> ys \<in> y}" .

  have "rely r \<parallel> x \<cdot> y = \<Union>{lmap \<langle>id,id\<rangle> ` (rs \<sha> zs) |rs zs. rs \<in> rely r \<and> zs \<in> x \<cdot> y}"
    by (simp add: shuffle_def)
  also have "... = ?lhs_inf \<union> ?lhs_fin"
    by (simp add: l_prod_def) blast
  also have "... \<subseteq> \<Union>{lmap \<langle>id,id\<rangle> ` (rs \<sha> xs) |rs xs. rs \<in> rely r \<and> xs \<in> x} \<cdot> \<Union>{lmap \<langle>id,id\<rangle> ` (rs \<sha> ys) |rs ys. rs \<in> rely r \<and> ys \<in> y}"
    by (subst Un_absorb[symmetric], rule sup_mono[OF inf_case fin_case])
  also have "... = (rely r \<parallel> x) \<cdot> (rely r \<parallel> y)"
    by (simp add: shuffle_def)
  finally show ?thesis .
qed

end