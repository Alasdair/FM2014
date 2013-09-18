theory PowerInvariant
  imports Language Topped
begin

inductive_set prefixes :: "'a llist \<Rightarrow> 'a llist set" for xs :: "'a llist" where
  prefix: "ltake (enat n) xs \<in> prefixes xs"

lemma "LNil \<in> prefixes xs" using prefix[where n = 0]
  by (auto simp: enat_0)

lemma prefixes_lappend: "lfinite xs \<Longrightarrow> xs \<in> prefixes (xs \<frown> ys)"
  by (metis lfinite_llength_enat ltake_all ltake_lappend1 order_refl prefixes.simps)

definition Pref :: "'a lan \<Rightarrow> 'a lan" where
  "Pref X = (\<Union>xs\<in>X. prefixes xs)"

lemma prefixes_lfinite: "ys \<in> prefixes xs \<Longrightarrow> lfinite ys"
  by (induct ys rule: prefixes.induct) (metis enat_ile lfinite_conv_llength_enat llength_ltake min_max.inf_le1)

lemma Pref_finite: "Pref X \<subseteq> FIN"
  by (auto simp add: Pref_def FIN_def) (metis prefixes_lfinite)

lemma prefixes_ltake: "zs \<in> prefixes (ltake n xs) \<Longrightarrow> zs \<in> prefixes xs"
  by (induct zs rule: prefixes.induct) (metis lprefix_def lprefix_trans ltake_is_lprefix prefixes.prefix prefixes_lappend prefixes_lfinite)

lemma prefixes_prefix: "ys \<in> prefixes xs \<Longrightarrow> zs \<in> prefixes ys \<Longrightarrow> zs \<in> prefixes xs"
  by (induct ys rule: prefixes.induct) (auto intro: prefixes_ltake)

lemma Pref_idem [simp]: "Pref (Pref X) = Pref X"
  apply (auto simp add: Pref_def)
  apply (rule_tac x = xa in bexI)
  apply (metis prefixes_prefix)
  apply blast
  by (metis lappend_LNil2 prefixes_lappend prefixes_lfinite)

lemma Pref_continuous: "Pref (\<Union>X) = \<Union>(Pref ` X)"
  by (simp add: Pref_def)

lemma Pref_lower_adjoint: "lower_adjoint Pref"
  by (simp add: lower_is_jp join_preserving_def Pref_continuous)

lemma Pref_ge_finite: "X \<subseteq> FIN \<Longrightarrow> X \<subseteq> Pref X"
  by (auto simp add: Pref_def FIN_def) (metis (full_types) lprefix_def lprefix_refl mem_Collect_eq prefixes_lappend subsetD)

lemma Pref_refl_finite: "X \<subseteq> Pref X \<Longrightarrow> X \<subseteq> FIN"
  apply (auto simp add: Pref_def FIN_def)
  apply (drule_tac c = x in subsetD)
  apply assumption
  apply auto
  by (metis prefixes_lfinite)

lemma [iff]: "X \<subseteq> Pref X \<longleftrightarrow> X \<subseteq> FIN"
  by (metis Pref_ge_finite Pref_refl_finite)

lemma prefixes_refl: "lfinite xs \<Longrightarrow> xs \<in> prefixes xs"
  by (metis lappend_LNil2 prefixes_lappend)

lemma prefixes_contra_refl: "xs \<notin> prefixes xs \<Longrightarrow> \<not> lfinite xs"
  by (metis prefixes_refl)

lemma Pref_mono: "X \<subseteq> Y \<Longrightarrow> Pref X \<subseteq> Pref Y"
  by (auto simp add: Pref_def)

definition pow_inv :: "'a set \<Rightarrow> 'a lan" ("\<iota>") where
  "pow_inv X \<equiv> {xs. lset xs \<subseteq> X} \<inter> FIN"

lemma Pref_pow_inv: "Pref (\<iota> X) = \<iota> X"
proof (auto simp add: pow_inv_def Pref_def)
  fix xs y ys
  assume "ys \<in> prefixes xs" and "lset xs \<subseteq> X" and "y \<in> lset ys"
  thus "y \<in> X"
    by - (induct ys rule: prefixes.induct, metis lset_ltake set_mp)
next
  fix ys xs :: "'a llist"
  assume "ys \<in> prefixes xs" thus "ys \<in> FIN"
    by (metis FIN_def mem_Collect_eq prefixes_lfinite)
next
  fix xs
  assume "xs \<in> FIN" and "lset xs \<subseteq> X"
  moreover hence "xs \<in> prefixes xs"
    by (metis FIN_def lappend_LNil2 mem_Collect_eq prefixes_lappend)
  ultimately show "\<exists>ys\<in>{xs. lset xs \<subseteq> X} \<inter> FIN. xs \<in> prefixes ys"
    by blast
qed

definition symbols :: "'a lan \<Rightarrow> 'a set" ("\<rho>") where
  "symbols X \<equiv> \<Union>xs\<in>X. lset xs"

lemma galois_connection: "X \<subseteq> FIN \<Longrightarrow> \<rho> X \<subseteq> Y \<longleftrightarrow> X \<subseteq> \<iota> Y"
  by (auto simp add: pow_inv_def symbols_def FIN_def)

lemma \<rho>_iso: "Y \<subseteq> FIN \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> \<rho> X \<subseteq> \<rho> Y"
  by (metis Int_absorb1 galois_connection le_infI1 order_refl)

lemma pow_inv_finite: "\<iota> X \<subseteq> FIN"
  by (simp add: pow_inv_def)

lemma \<iota>_iso: "X \<subseteq> Y \<Longrightarrow> \<iota> X \<subseteq> \<iota> Y"
  by (metis galois_connection order_refl order_trans pow_inv_finite)

lemma Pref_0 [simp]: "Pref {} = {}"
  by (auto simp add: Pref_def)

lemma Pref_zeror [simp]: "Pref X \<cdot> {} = {}"
  by (auto simp add: Pref_def l_prod_def) (metis prefixes_lfinite)

(*
lemma "ys \<in> prefixes xs \<Longrightarrow> Y \<noteq> {} \<Longrightarrow> xs \<in> X \<Longrightarrow> \<not> lfinite xs \<Longrightarrow> \<exists>zs\<in>X \<parallel> Y. ys \<in> prefixes zs"
proof (induct ys rule: prefixes.induct)
  fix n
  assume "xs \<in> X" and "\<not> lfinite xs"
  {
    fix ys
    assume "ys \<in> Y"2
    hence "\<exists>zs\<in>X \<parallel> Y. ltake (enat n) xs \<in> prefixes zs"
      apply (auto simp add: shuffle_def)
      apply (rule_tac x = "lmap \<langle>id,id\<rangle> ` (xs \<sha> ys)" in exI)
      apply auto
      apply (rule_tac x = xs in exI)
      apply (rule_tac x = ys in exI)
      apply simp
      apply (rule `xs \<in> X`)
      sorry
  }
  thus "\<exists>zs\<in>X \<parallel> Y. ltake (enat n) xs \<in> prefixes zs"
    sorry
qed
*)

lemma pow_inv_par [simp]: "\<iota> r \<parallel> \<iota> r = \<iota> r"
  sorry

(*
lemma pow_inv_l_prod_par: "\<iota> r \<cdot> \<iota> s \<le> \<iota> r \<parallel> \<iota> s"
  by (metis fin_l_prod_le_shuffle)
*)

lemma pow_inv_exchange1: "\<iota> r \<cdot> (x \<parallel> y) \<subseteq> \<iota> r \<cdot> x \<parallel> \<iota> r \<cdot> y"
  using exchange[where A = "\<iota> r" and B = "\<iota> r", simplified, OF pow_inv_finite] .

(*
shows "(lmap \<langle>id,id\<rangle> ` (a \<sha> b)) \<cdot> (lmap \<langle>id,id\<rangle> ` (c \<sha> d)) \<subseteq> lmap \<langle>id, id\<rangle> ` ((b \<frown> c) \<sha> (a \<frown> d))"
*)

lemma interleave_exchange:
  assumes "llength (\<rr> t) = llength (cs \<frown> ds)"
  and "llength (\<ll> t) = llength (as \<frown> bs)"
  shows "\<exists>t' t''. (as \<frown> bs) \<triangleright> t \<triangleleft> (cs \<frown> ds) = (as \<triangleright> t' \<triangleleft> cs) \<frown> (bs \<triangleright> t'' \<triangleleft> ds)"
  sorry

lemma tshuffle_interleave: "zs \<in> xs \<sha> ys \<Longrightarrow> zs = xs \<triangleright> traj zs \<triangleleft> ys"
  by (auto simp add: tshuffle_words_def) (metis reinterleave)

lemma traj_interleave: "traj (xs \<triangleright> zs \<triangleleft> ys) = lmap (\<lambda>x. ()) xs \<triangleright> zs \<triangleleft> lmap (\<lambda>x. ()) ys"
  sorry

declare interleave_only_left[simp]
declare lfilter_left_interleave[simp]
declare lfilter_right_interleave[simp]

lemma [simp]: "lmap unl (lmap Inl xs) = xs"
  by (metis lmap2_id unl.simps(1))

lemma [simp]: "lset (lmap (\<lambda>x. y) (LCons x xs)) = {y}"
  by auto

lemma [simp]: "llength (lfilter is_left t) = llength xs \<longleftrightarrow> lfilter is_left t = lmap (\<lambda>x. Inl ()) xs"
  sorry

lemma [simp]: "llength (lfilter is_right t) = llength xs \<longleftrightarrow> lfilter is_right t = lmap (\<lambda>x. Inr ()) xs"
  sorry

lemma lefts_interleave_var: "llength (\<ll> t) = llength xs \<Longrightarrow> \<ll> (xs \<triangleright> t \<triangleleft> ys) = xs"
  by (simp add: lefts_def)

lemma rights_interleave_var: "llength (\<rr> t) = llength ys \<Longrightarrow> \<rr> (xs \<triangleright> t \<triangleleft> ys) = ys"
  sorry


lemma "rs \<sha> (xs \<frown> ys) \<subseteq> \<Union>{(rs' \<sha> xs) \<cdot> (rs'' \<sha> ys) |rs' rs''. rs = rs' \<frown> rs''}"
proof -
  {
    fix zs
    assume "zs \<in> rs \<sha> (xs \<frown> ys)"
    hence zs_def: "zs = rs \<triangleright> traj zs \<triangleleft> (xs \<frown> ys)"
      by (metis tshuffle_interleave)
    have "\<exists>rs' rs''. rs = rs' \<frown> rs'' \<and> lfinite rs'"
      by (rule_tac x = LNil in exI) auto
    then obtain rs' rs'' where rs_def: "rs = rs' \<frown> rs''" and rs'_finite: "lfinite rs'"
      by blast
    have "\<exists>t' t''. zs = (rs' \<triangleright> t' \<triangleleft> xs) \<frown> (rs'' \<triangleright> t'' \<triangleleft> ys)"
      apply (subst zs_def)
      apply (subst rs_def)
      apply (rule interleave_exchange)
      apply (simp only: rights_def o_def)
      apply (subst traj_lfilter_rights[where f = "unr \<circ> Inr" and xs = "xs \<frown> ys"])
      apply (simp add: rights_def)
      apply (rule arg_cong) back
      apply (subst zs_def)
      apply simp
      apply (subgoal_tac "lfilter is_right (traj zs) = 
      sledgehammer
      apply (subst rights_interleave)
    then obtain t' t'' where "zs = (rs' \<triangleright> t' \<triangleleft> xs) \<frown> (rs'' \<triangleright> t'' \<triangleleft> ys)"
      sledgehammer

  apply auto
  apply (subgoal_tac "\<exists>rs' rs''. rs = rs' \<frown> rs''")
  apply (erule exE)+
  apply (rule_tac x = "(rs' \<sha> xs) \<cdot> (rs'' \<sha> ys)" in exI)
  apply (intro conjI)
  apply (rule_tac x = rs' in exI)
  apply (rule_tac x = rs'' in exI)
  apply simp
  sledgehammer

lemma pow_inv1: "\<iota> r \<parallel> x \<cdot> y \<subseteq> (\<iota> r \<parallel> x) \<cdot> (\<iota> r \<parallel> y)"
  apply (simp add: shuffle_def)
proof -
  let ?lhs_inf = "\<Union>{lmap \<langle>id,id\<rangle> ` (rs \<sha> xs) |rs xs. rs \<in> \<iota> r \<and> xs \<in> x \<and> \<not> lfinite xs}"
  let ?lhs_fin = "\<Union>{lmap \<langle>id,id\<rangle> ` (rs \<sha> (xs \<frown> ys)) |rs xs ys. rs \<in> \<iota> r \<and> xs \<in> x \<and> ys \<in> y \<and> lfinite xs}"

  have "?lhs_inf \<subseteq> \<Union>{lmap \<langle>id,id\<rangle> ` (rs \<sha> xs) |rs xs. rs \<in> \<iota> r \<and> xs \<in> x} \<cdot> \<Union>{lmap \<langle>id,id\<rangle> ` (rs \<sha> ys) |rs ys. rs \<in> \<iota> r \<and> ys \<in> y}"
    by (auto simp only: l_prod_def) (metis (lifting, full_types) lfinite_lmap lfinite_rights mem_Collect_eq tshuffle_words_def)

  have "?lhs_fin \<subseteq> \<Union>{lmap \<langle>id,id\<rangle> ` (rs \<sha> xs) |rs xs. rs \<in> \<iota> r \<and> xs \<in> x} \<cdot> \<Union>{lmap \<langle>id,id\<rangle> ` (rs \<sha> ys) |rs ys. rs \<in> \<iota> r \<and> ys \<in> y}"
    apply (auto simp add: l_prod_def)
    apply (rename_tac rs xs ys zs)
    apply (rule_tac x = "lmap \<langle>id,id\<rangle> ` (rs \<sha> (xs \<frown> ys))" in exI)
    apply (intro conjI)
    prefer 2
    apply simp
    apply (subgoal_tac "zs = (LNil \<frown> rs) \<triangleright> traj zs \<triangleleft> (xs \<frown> ys)")
    prefer 2
    apply simp
    apply (metis tshuffle_interleave)
    apply (subgoal_tac "\<exists>t' t''. LNil \<frown> rs \<triangleright> traj zs \<triangleleft> xs \<frown> ys = (LNil \<triangleright> t' \<triangleleft> xs) \<frown> (rs \<triangleright> t'' \<triangleleft> ys)")

    apply (metis reinterleave)
    apply (erule exE)+
    apply (subgoal_tac "lfinite (lmap \<langle>id,id\<rangle> (rs \<triangleright> traj xa \<triangleleft> xs))")
    apply (erule_tac x = "lmap \<langle>id,id\<rangle> (rs \<triangleright> traj xa \<triangleleft> xs)" in allE)
    apply simp
    apply (erule_tac x = "lmap \<langle>id,id\<rangle> (rs \<triangleright> traj xa \<triangleleft> ys)" in allE)
    apply (
    sledgehammer

  have "\<iota> r \<parallel> x \<cdot> y = \<Union>{lmap \<langle>id,id\<rangle> ` (rs \<sha> zs) |rs zs. rs \<in> \<iota> r \<and> zs \<in> x \<cdot> y}"
    by (simp add: shuffle_def)
  also have "... = ?lhs_inf \<union> ?lhs_fin"
    by (simp add: l_prod_def) blast

end