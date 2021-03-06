theory Rely_Guarantee_Inf
  imports Language
begin

definition atomic :: "'a set \<Rightarrow> 'a lan" ("\<langle>_\<rangle>" [0] 1000) where
  "\<langle>R\<rangle> \<equiv> ((\<lambda>x. LCons x LNil) ` R)"

lemma atomic_zero [simp]: "\<langle>{}\<rangle> = {}"
  by (auto simp add: atomic_def)

lemma [iff]: "\<langle>X\<rangle> \<subseteq> \<langle>Y\<rangle> \<longleftrightarrow> X \<subseteq> Y"
  by (auto simp add: atomic_def)

lemma [iff]: "\<langle>X\<rangle> = \<langle>Y\<rangle> \<longleftrightarrow> X = Y"
  by (auto simp add: atomic_def)

lemma atom_finite [intro!]: "\<langle>R\<rangle> \<subseteq> FIN"
  by (auto simp add: FIN_def atomic_def)

lemma [dest!]: "x \<in> lset (xs \<frown> ys) \<Longrightarrow> x \<in> lset xs \<or> x \<in> lset ys"
  by (metis in_lset_lappend_iff)

lemma rely_power1: "x \<in> power \<langle>R\<rangle> i \<Longrightarrow> lfinite x"
  by (induct i arbitrary: x) (auto simp add: l_prod_def atomic_def)

lemma rely_power2: "x \<in> power \<langle>R\<rangle> i \<Longrightarrow> y \<in> lset x \<Longrightarrow> y \<in> R"
proof (induct i arbitrary: x)
  case 0 thus ?case
    by simp
next
  case (Suc n) thus ?case
    apply simp
    apply (erule rev_mp)
    apply (subst fin_l_prod)
    by (auto simp add: atomic_def FIN_def)
qed

lemma lset_LCons_subsetD: "lset (LCons x xs) \<subseteq> R \<Longrightarrow> lset xs \<subseteq> R"
  by (metis Coinductive_List.lset_eq_lsetp Collect_mono dual_order.trans lsetp.intros(2))

lemma rely_power3: "lfinite xs \<Longrightarrow> lset xs \<subseteq> R \<Longrightarrow> \<exists>X. (\<exists>i. X = power \<langle>R\<rangle> i) \<and> xs \<in> X"
proof (induct xs rule: lfinite.induct)
  case lfinite_LNil
  thus ?case
    apply (rule_tac x = "power \<langle>R\<rangle> 0" in exI)
    apply auto
    apply (rule_tac x = 0 in exI)
    by auto
next
  case (lfinite_LConsI xs x)
  then obtain X and i where "X = Language.power \<langle>R\<rangle> i" and "xs \<in> X"
    by - (auto dest: lset_LCons_subsetD)
  from this show ?case
    apply (rule_tac x = "\<langle>R\<rangle> \<cdot> X" in exI)
    apply auto
    apply (rule_tac x = "Suc i" in exI)
    apply auto
    apply (subst fin_l_prod)
    apply auto
    apply (rule_tac x = "LCons x LNil" in exI)
    apply (rule_tac x = xs in exI)
    apply auto
    apply (insert lfinite_LConsI(3))
    by (simp add: atomic_def)
qed

lemma fin_rely_def: "\<langle>R\<rangle>\<^sup>\<star> = {xs. lfinite xs \<and> lset xs \<subseteq> R}"
  apply (subst star_power_fin)
  apply (auto simp add: powers_def)
  apply (metis rely_power1)
  apply (metis rely_power2)
  by (metis rely_power3)

lemma power_star_leq: "power X n \<subseteq> X\<^sup>\<star>"
  apply (induct n)
  apply simp_all
  apply (metis insert_subset seq.star_ref)
  by (metis seq.prod_star_closure seq.star_ext)

lemma omega_power: "X\<^sup>\<omega> = power X n \<cdot> X\<^sup>\<omega>"
  apply (induct n)
  apply simp_all
  by (metis seq.mult_assoc seq.omega_unfold_eq)

lemma atomic_power: "power \<langle>R\<rangle> n = {xs. llength xs = enat n \<and> lset xs \<subseteq> R}"
  apply (induct n)
  apply simp_all
  defer
  apply (subst fin_l_prod)
  apply (metis atom_finite)
  apply (auto simp add: atomic_def)
  apply (metis eSuc_enat)
  apply (rule_tac x = "LCons (lhd x) LNil" in exI)
  apply (subgoal_tac "x \<noteq> LNil")
  prefer 2
  apply (metis Nat.diff_le_self Suc_n_not_le_n diff_Suc_Suc enat.inject idiff_enat_enat ldropn_LNil llength_ldropn)
  apply (rule_tac x = "ltl x" in exI)
  apply (intro conjI)
  apply (metis lappend_code(1) lappend_code(2) llist.collapse)
  apply (simp add: image_def)
  apply (metis lhd_in_lset subsetD)
  apply (subgoal_tac "\<exists>y ys. x = LCons y ys")
  apply (erule exE)+
  apply simp
  apply (metis co.enat.inject eSuc_enat)
  apply (metis neq_LNil_conv)
  apply (metis dual_order.trans lset_ltl)
  apply (metis zero_enat_def)
  by (metis llength_eq_0 zero_enat_def)

lemma atomic_omega_inf: "xs \<in> \<langle>R\<rangle>\<^sup>\<omega> \<Longrightarrow> \<not> lfinite xs"
proof auto
  assume "xs \<in> \<langle>R\<rangle>\<^sup>\<omega>"
  and "lfinite xs"

  then obtain n where "llength xs = enat n"
    by (metis lfinite_llength_enat)

  from `xs \<in> \<langle>R\<rangle>\<^sup>\<omega>` have "xs \<in> power \<langle>R\<rangle> (Suc n) \<cdot> \<langle>R\<rangle>\<^sup>\<omega>"
    by (metis omega_power)

  hence "xs \<in> {xs. llength xs = enat (Suc n) \<and> lset xs \<subseteq> R} \<cdot> \<langle>R\<rangle>\<^sup>\<omega>"
    by (metis atomic_power omega_power)

  hence "llength xs > enat n"
    apply -
    apply (erule rev_mp)
    apply (subst fin_l_prod)
    apply auto
    apply (metis FIN_def lfinite_conv_llength_enat mem_Collect_eq)
    by (metis enat_less_enat_plusI lessI)

  from this and `llength xs = enat n` show False
    by (metis less_irrefl)
qed

lemma LNil_atomic_omega: "LNil \<notin> \<langle>R\<rangle>\<^sup>\<omega>"
  by (metis atomic_omega_inf lfinite_code(1))

lemma lset_member_position: "x \<in> lset xs \<Longrightarrow> (\<exists>n. lnth xs n = x)"
  by (rule lset_ex_lnth[where P = "\<lambda>y. y = x"]) blast

lemma atomic_omega_lset: "xs \<in> \<langle>R\<rangle>\<^sup>\<omega> \<Longrightarrow> x \<in> lset xs \<Longrightarrow> x \<in> R"
proof -
  assume "xs \<in> \<langle>R\<rangle>\<^sup>\<omega>" and "x \<in> lset xs"
  
  then obtain n where "lnth xs n = x"
    by (metis lset_member_position)

  from `xs \<in> \<langle>R\<rangle>\<^sup>\<omega>` have "xs \<in> power \<langle>R\<rangle> (Suc n) \<cdot> \<langle>R\<rangle>\<^sup>\<omega>"
    by (metis omega_power)

  hence "xs \<in> {xs. llength xs = enat (Suc n) \<and> lset xs \<subseteq> R} \<cdot> \<langle>R\<rangle>\<^sup>\<omega>"
    by (metis atomic_power omega_power)

  hence "lnth xs n \<in> R"
    apply -
    apply (erule rev_mp)
    apply (subst fin_l_prod)
    apply (metis (full_types) FIN_def atomic_power mem_Collect_eq rely_power1 subsetI)
    apply auto
    apply (subgoal_tac "lnth xs n = lnth (xs \<frown> ys) n")
    apply (metis enat_ord_simps(2) in_lset_conv_lnth in_mono lessI)
    by (metis enat_ord_simps(2) lessI lnth_lappend1)

  from this and `lnth xs n = x`
  show "x \<in> R"
    by auto
qed

lemma inf_rely_def: "\<langle>R\<rangle>\<^sup>\<omega> = {xs. \<not> lfinite xs \<and> lset xs \<subseteq> R}"
proof (rule antisym)
  show "{xs. \<not> lfinite xs \<and> lset xs \<subseteq> R} \<subseteq> \<langle>R\<rangle>\<^sup>\<omega>"
    apply (rule seq.omega_coinduct_eq_var2)
    apply (subst fin_l_prod)
    apply (metis atom_finite)
    apply (simp add: atomic_def image_def)
    apply auto
    apply (rule_tac x = "LCons (lhd x) LNil" in exI)
    apply (rule_tac x = "ltl x" in exI)
    apply (intro conjI)
    apply (metis lappend_code(1) lappend_code(2) lfinite.simps llist.collapse)
    apply (metis in_mono lfinite.simps lhd_in_lset)
    apply (metis lfinite_ltl)
    by (metis lset_ltl subset_trans)
next
  show "\<langle>R\<rangle>\<^sup>\<omega> \<subseteq> {xs. \<not> lfinite xs \<and> lset xs \<subseteq> R}"
    apply auto
    apply (metis atomic_omega_inf)
    by (metis atomic_omega_lset)
qed

lemma rely_def: "\<langle>R\<rangle>\<^sup>\<infinity> = {xs. lset xs \<subseteq> R}"
  by (auto simp add: loop_def inf_rely_def fin_rely_def)

lemma rely_galois: "X \<subseteq> \<langle>R\<rangle>\<^sup>\<infinity> \<longleftrightarrow> \<Union>(lset ` X) \<subseteq> R"
  by (auto simp add: rely_def)

lemma rely_galois_2: "X \<subseteq> \<langle>R\<rangle>\<^sup>\<infinity> \<longleftrightarrow> (\<forall>xs\<in>X. lset xs \<subseteq> R)"
  by (auto simp add: rely_def)

lemma lset_lefts [iff]: "lset (\<ll> xs) \<subseteq> R \<longleftrightarrow> lset (lfilter is_left xs) \<subseteq> Inl ` R"
  apply (auto simp add: lefts_def image_def subset_iff)
  apply (erule_tac x = "unl t" in allE)
  apply (erule impE)
  apply (rule_tac x = t in exI)
  apply auto
  apply (rule_tac x = "unl t" in bexI)
  apply auto
  apply (subgoal_tac "\<exists>t' t''. t = Inl t' \<or> t = Inr t''")
  apply (erule exE)+
  apply (erule disjE)
  apply simp_all
  by (metis swap.cases)

lemma lset_rights [iff]: "lset (\<rr> xs) \<subseteq> R \<longleftrightarrow> lset (lfilter is_right xs) \<subseteq> Inr ` R"
  apply (auto simp add: rights_def image_def subset_iff)
  apply (erule_tac x = "unr t" in allE)
  apply (erule impE)
  apply (rule_tac x = t in exI)
  apply auto
  apply (rule_tac x = "unr t" in bexI)
  apply auto
  apply (subgoal_tac "\<exists>t' t''. t = Inl t' \<or> t = Inr t''")
  apply (erule exE)+
  apply (erule disjE)
  apply simp_all
  by (metis swap.cases)

lemma lset_lr [intro]: "lset (\<ll> xs) \<subseteq> R \<Longrightarrow> lset (\<rr> xs) \<subseteq> S \<Longrightarrow> lset (lmap \<langle>id,id\<rangle> xs) \<subseteq> R \<union> S"
  apply simp
  apply (auto simp add: subset_iff)
  by (metis (full_types) DEADID.map_id Projr_Inr imageE not_is_right sum.simps(5) sum.simps(6) unl.simps(1))

lemma rely_union1_fin: "\<langle>R\<rangle>\<^sup>\<star> \<parallel> \<langle>S\<rangle>\<^sup>\<star> \<subseteq> \<langle>R \<union> S\<rangle>\<^sup>\<star>"
  apply (simp add: fin_rely_def shuffle_def Sup_le_iff)
  apply clarify
  apply (intro conjI)
  apply (metis lfinite_lmap lfinite_shuffle)
  apply (simp add: tshuffle_words_def)
  by (metis llist.set_map lset_lr)

lemma rely_union1_inf: "\<langle>R\<rangle>\<^sup>\<omega> \<parallel> \<langle>S\<rangle>\<^sup>\<omega> \<subseteq> \<langle>R \<union> S\<rangle>\<^sup>\<omega>"
  apply (simp add: inf_rely_def shuffle_def Sup_le_iff)
  apply clarify
  apply (intro conjI)
  apply (metis fair_non_empty lfinite_lmap shuffle_fair)
  by (metis (mono_tags) lset_lr mem_Collect_eq tshuffle_words_def)

lemma rely_union1: "\<langle>R\<rangle>\<^sup>\<infinity> \<parallel> \<langle>S\<rangle>\<^sup>\<infinity> \<subseteq> \<langle>R \<union> S\<rangle>\<^sup>\<infinity>"
  apply (simp add: rely_def shuffle_def Sup_le_iff tshuffle_words_def)
  apply clarify
  by (metis (hide_lams, no_types) Un_iff lset_lefts lset_lr lset_rights set_rev_mp)

lemma lmap_unl_Inl: "(\<forall>x\<in>lset xs. is_left x) \<Longrightarrow> lmap unl xs = ys \<longleftrightarrow> xs = lmap Inl ys"
  apply (auto simp del: lmap.compositionality)
  apply (rule sym)
  apply (rule lmap2_id_var)
  apply auto
  by (metis is_left.simps(2) obj_sumE unl.simps(1))

lemma lmap_unr_Inr: "(\<forall>x\<in>lset xs. is_right x) \<Longrightarrow> lmap unr xs = ys \<longleftrightarrow> xs = lmap Inr ys"
  apply (auto simp del: lmap.compositionality)
  apply (rule sym)
  apply (rule lmap2_id_var)
  apply auto
  by (metis is_right.simps(2) obj_sumE unr.simps(1))

lemma lmap_subid: "(\<forall>x\<in>lset xs. f x = x) \<Longrightarrow> lmap f xs = xs"
  by auto

lemma lfilter_to_lfilter_left [symmetric]: "lfilter P xs = \<ll> (lmap (\<lambda>x. if P x then Inl x else Inr x) xs)"
  apply (auto simp add: lefts_def)
  apply (rule sym)
  apply (subst lmap_unl_Inl)
  by (auto simp add: lfilter_lmap)

lemma lfilter_to_lfilter_right [symmetric]: "lfilter (Not \<circ> P) xs = \<rr> (lmap (\<lambda>x. if P x then Inl x else Inr x) xs)"
  apply (auto simp add: rights_def)
  apply (rule sym)
  apply (subst lmap_unr_Inr)
  by (auto simp add: lfilter_lmap)

lemma lfilter_interleave:
  "xs = lmap \<langle>id,id\<rangle> (lfilter P xs \<triangleright> traj (lmap (\<lambda>x. if P x then Inl () else Inr ()) xs) \<triangleleft> lfilter (Not \<circ> P) xs)"
proof -
  have traj_lmap: "traj (lmap (\<lambda>x. if P x then Inl () else Inr ()) xs) = traj (lmap (\<lambda>x. if P x then Inl x else Inr x) xs)"
    by (auto simp add: traj_def) (metis (lifting, full_types) sum.simps(5) sum.simps(6))

  have "xs = lmap \<langle>id,id\<rangle> (lmap (\<lambda>x. if P x then Inl x else Inr x) xs)"
    by (rule sym) (auto intro: lmap_subid)
  also have "... = lmap \<langle>id,id\<rangle> (\<ll> (lmap (\<lambda>x. if P x then Inl x else Inr x) xs) \<triangleright> traj (lmap (\<lambda>x. if P x then Inl x else Inr x) xs) \<triangleleft> \<rr> (lmap (\<lambda>x. if P x then Inl x else Inr x) xs))"
    by (simp only: reinterleave)
  also have "... = lmap \<langle>id,id\<rangle> (lfilter P xs \<triangleright> traj (lmap (\<lambda>x. if P x then Inl () else Inr ()) xs) \<triangleleft> lfilter (Not \<circ> P) xs)"
    by (simp only: traj_lmap lfilter_to_lfilter_left lfilter_to_lfilter_right)
  finally show ?thesis .
qed

lemma lfilter_pred_eq [intro!]: "P = Q \<Longrightarrow> lfilter P xs = lfilter Q xs"
  by auto

lemma rely_union_fin [simp]: "\<langle>R\<rangle>\<^sup>\<star> \<parallel> \<langle>S\<rangle>\<^sup>\<star> = \<langle>R \<union> S\<rangle>\<^sup>\<star>"
proof
  show "\<langle>R\<rangle>\<^sup>\<star> \<parallel> \<langle>S\<rangle>\<^sup>\<star> \<subseteq> \<langle>R \<union> S\<rangle>\<^sup>\<star>"
    by (metis rely_union1_fin)
next
  {
    fix xs
    assume assm: "xs \<in> \<langle>R \<union> S\<rangle>\<^sup>\<star>"
    hence "lfinite xs"
      by (auto simp add: fin_rely_def)
    have "xs = lmap \<langle>id,id\<rangle> (lfilter (\<lambda>x. x \<in> R) xs \<triangleright> traj (lmap (\<lambda>x. if x \<in> R then Inl () else Inr ()) xs) \<triangleleft> lfilter (\<lambda>x. x \<notin> R) xs)"
      by (subst lfilter_interleave[where P = "\<lambda>x. x \<in> R"], simp)
    also have "... \<in> lmap \<langle>id,id\<rangle> ` (lfilter (\<lambda>x. x \<in> R) xs \<sha> lfilter (\<lambda>x. x \<notin> R) xs)"
      apply (intro imageI)
      apply (simp add: tshuffle_words_def image_def)
      apply (subst lefts_interleave_llength)
      defer
      apply (subst rights_interleave_llength)
      apply auto
      apply (simp add: rights_def)
      apply (subst lfilter_lmap)
      apply (subst llength_lmap)
      apply (rule arg_cong) back
      apply (rule lfilter_pred_eq)
      apply auto
      apply (simp add: lefts_def)
      apply (subst lfilter_lmap)
      apply (subst llength_lmap)
      apply (rule arg_cong) back
      apply (rule lfilter_pred_eq)
      by (simp add: o_def)
    also have "... \<subseteq> \<langle>R\<rangle>\<^sup>\<star> \<parallel> \<langle>S\<rangle>\<^sup>\<star>"
      apply (auto simp add: fin_rely_def shuffle_def)
      apply (rule_tac x = "lmap \<langle>id,id\<rangle> ` (lfilter (\<lambda>x. x \<in> R) xs \<sha> lfilter (\<lambda>x. x \<notin> R) xs)" in exI)
      apply simp
      apply (rule_tac x = "lfilter (\<lambda>x. x \<in> R) xs" in exI)
      apply (rule_tac x = "lfilter (\<lambda>x. x \<notin> R) xs" in exI)
      apply auto
      apply (metis `lfinite xs` lfinite_lfilterI)
      apply (metis `lfinite xs` lfinite_lfilterI)
      apply (insert assm)
      by (auto simp add: fin_rely_def)
    finally have "xs \<in> \<langle>R\<rangle>\<^sup>\<star> \<parallel> \<langle>S\<rangle>\<^sup>\<star>" .
  }
  thus "\<langle>R \<union> S\<rangle>\<^sup>\<star> \<subseteq> \<langle>R\<rangle>\<^sup>\<star> \<parallel> \<langle>S\<rangle>\<^sup>\<star>"
    by blast
qed

(*
lemma "\<langle>R \<union> S\<rangle>\<^sup>\<omega> \<subseteq> \<langle>R\<rangle>\<^sup>\<omega> \<parallel> \<langle>S\<rangle>\<^sup>\<omega>"
proof -
  {
    fix xs
    assume "xs \<in> \<langle>R \<union> S\<rangle>\<^sup>\<omega>"
    hence "\<not> lfinite xs"
      by (metis atomic_omega_inf)
    have "xs = lmap \<langle>id,id\<rangle> (lfilter (\<lambda>x. x \<in> R) xs \<triangleright> traj (lmap (\<lambda>x. if x \<in> R then Inl () else Inr ()) xs) \<triangleleft> lfilter (\<lambda>x. x \<notin> R) xs)"
      by (subst lfilter_interleave[where P = "\<lambda>x. x \<in> R"], simp)
    also have "... \<in> lmap \<langle>id,id\<rangle> ` (lfilter (\<lambda>x. x \<in> R) xs \<sha> lfilter (\<lambda>x. x \<notin> R) xs)"
      apply (intro imageI)
      apply (simp add: tshuffle_words_def image_def)
      apply (subst lefts_interleave_llength)
      defer
      apply (subst rights_interleave_llength)
      apply auto
      apply (simp add: rights_def)
      apply (subst lfilter_lmap)
      apply (subst llength_lmap)
      apply (rule arg_cong) back
      apply (rule lfilter_pred_eq)
      apply auto
      apply (simp add: lefts_def)
      apply (subst lfilter_lmap)
      apply (subst llength_lmap)
      apply (rule arg_cong) back
      apply (rule lfilter_pred_eq)
      by (simp add: o_def)
    also have "... \<subseteq> \<langle>R\<rangle>\<^sup>\<omega> \<parallel> \<langle>S\<rangle>\<^sup>\<omega>"
      apply (auto simp add: inf_rely_def shuffle_def)
      apply (rule_tac x = "lmap \<langle>id,id\<rangle> ` (lfilter (\<lambda>x. x \<in> R) xs \<sha> lfilter (\<lambda>x. x \<notin> R) xs)" in exI)
      apply simp
      apply (rule_tac x = "lfilter (\<lambda>x. x \<in> R) xs" in exI)
      apply (rule_tac x = "lfilter (\<lambda>x. x \<notin> R) xs" in exI)
      apply auto
*)

lemmas [intro] = seq.star_iso[rule_format]

lemma rely_1_fin: "\<langle>R\<rangle>\<^sup>\<star> \<le> \<langle>R\<rangle>\<^sup>\<star> \<parallel> \<langle>S\<rangle>\<^sup>\<star>"
  by (auto del: subsetI)

lemma rely_1_inf: "\<langle>R\<rangle>\<^sup>\<omega> \<le> \<langle>R\<rangle>\<^sup>\<omega> \<parallel> \<langle>S\<rangle>\<^sup>\<omega>"
  sorry

lemma rely_2: "\<langle>R\<rangle>\<^sup>\<star> \<parallel> \<langle>R\<rangle>\<^sup>\<star> \<subseteq> \<langle>R\<rangle>\<^sup>\<star>"
  by auto 

lemma rely_par_idem: "\<langle>R\<rangle>\<^sup>\<star> \<parallel> \<langle>R\<rangle>\<^sup>\<star> = \<langle>R\<rangle>\<^sup>\<star>"
  by (metis rely_union_fin sup_idem)

lemma rely_inter: "\<langle>R\<rangle>\<^sup>\<star> \<inter> \<langle>S\<rangle>\<^sup>\<star> = \<langle>R \<inter> S\<rangle>\<^sup>\<star>"
  by (auto simp add: fin_rely_def)

lemma rely_lappend [simp]: "(\<exists>rs. rs \<in> \<langle>R\<rangle>\<^sup>\<star> \<and> rs = rs' \<frown> rs'') \<longleftrightarrow> (rs' \<in> \<langle>R\<rangle>\<^sup>\<star> \<and> rs'' \<in> \<langle>R\<rangle>\<^sup>\<star>)"
  by (auto simp add: fin_rely_def FIN_def)

lemma LCons_cont [simp]: "LCons x ` \<Union>{f xs ys|xs ys. P xs ys} = \<Union>{LCons x ` f xs ys|xs ys. P xs ys}"
  by (auto simp add: image_def)

lemma [simp]: "LCons x ` (ys \<cdot> zs) = LCons x ` ys \<cdot> zs"
  apply (auto simp add: l_prod_def)
  apply (metis image_eqI lappend_code(2) lfinite_LCons)
  by (metis image_eqI lappend_code(2) lfinite_LCons)

lemma set_comp_Union_iso3: "(\<And>x y z. P x y z \<Longrightarrow> f x y z \<subseteq> g x y z) \<Longrightarrow> \<Union>{f x y z |x y z. P x y z} \<subseteq> \<Union>{g x y z |x y z. P x y z}"
  by auto (metis in_mono)

lemma set_comp_Union_eq4: "(\<And>x y z w. P x y z w \<Longrightarrow> f x y z w = g x y z w) \<Longrightarrow> \<Union>{f x y z w |x y z w. P x y z w} = \<Union>{g x y z w |x y z w. P x y z w}"
  by auto metis+

lemma set_comp_Union_eq3: "(\<And>x y z. P x y z \<Longrightarrow> f x y z = g x y z) \<Longrightarrow> \<Union>{f x y z |x y z. P x y z} = \<Union>{g x y z |x y z. P x y z}"
  by auto metis+

lemma set_comp_Union_eq2: "(\<And>x y z. P x y \<Longrightarrow> f x y = g x y) \<Longrightarrow> \<Union>{f x y |x y. P x y} = \<Union>{g x y |x y. P x y}"
  by auto

lemma lappend_in_l_prod: "lfinite xs \<Longrightarrow> xs \<in> X \<Longrightarrow> ys \<in> Y \<Longrightarrow> xs \<frown> ys \<in> X \<cdot> Y"
  by (auto simp add: l_prod_def)

lemma [simp]: "lmap \<langle>id,id\<rangle> ` (x \<cdot> y) = lmap \<langle>id,id\<rangle> ` x \<cdot> lmap \<langle>id,id\<rangle> ` y"
  apply (simp add: image_def)
  apply (auto simp add: l_prod_def)
  apply (metis lfinite_lmap lmap_lappend_distrib)
  apply (metis lfinite_lmap lmap_lappend_distrib)
  by (metis l_prod_def lappend_in_l_prod lmap_lappend_distrib par.add_comm)

lemma rely_finite: "\<langle>R\<rangle>\<^sup>\<star> \<subseteq> FIN"
  by (auto simp add: fin_rely_def FIN_def)

lemma tshuffle_image1: "LCons (Inl x) ` (xs \<sha> ys) \<subseteq> LCons x xs \<sha> ys"
  by (auto simp add: tshuffle_words_def)

lemma tshuffle_image2: "LCons (Inr y) ` (xs \<sha> ys) \<subseteq> xs \<sha> LCons y ys"
  by (auto simp add: tshuffle_words_def)

lemma rely_dist: "lfinite rs \<Longrightarrow> lfinite xs \<Longrightarrow> rs \<sha> (xs \<frown> ys) \<subseteq> \<Union>{(rs' \<sha> xs) \<cdot> (rs'' \<sha> ys) |rs' rs''. rs = rs' \<frown> rs''}"
proof (induct rs arbitrary: xs rule: lfinite_induct)
  case Nil
  thus ?case
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

lemma fin_inf_split: "x \<inter> FIN \<union> x\<cdot>{} = x"
  by (auto simp add: l_prod_def FIN_def)

lemma rely_exchange: "(\<langle>R\<rangle>\<^sup>\<star> \<parallel> x) \<cdot> (\<langle>R\<rangle>\<^sup>\<star> \<parallel> y) \<subseteq> \<langle>R\<rangle>\<^sup>\<star> \<parallel> x \<cdot> y"
proof -
  have "(\<langle>R\<rangle>\<^sup>\<star> \<parallel> x) \<cdot> (\<langle>R\<rangle>\<^sup>\<star> \<parallel> y) = (\<langle>R\<rangle>\<^sup>\<star> \<parallel> (x \<inter> FIN \<union> x\<cdot>{})) \<cdot> (\<langle>R\<rangle>\<^sup>\<star> \<parallel> y)"
    by (metis fin_inf_split)
  also have "... = (\<langle>R\<rangle>\<^sup>\<star> \<parallel> (x \<inter> FIN)) \<cdot> (\<langle>R\<rangle>\<^sup>\<star> \<parallel> y) \<union> \<langle>R\<rangle>\<^sup>\<star> \<parallel> x\<cdot>{}" using rely_finite[of R]
    by simp
  also have "... \<subseteq> (x \<inter> FIN) \<cdot> y \<parallel> \<langle>R\<rangle>\<^sup>\<star> \<cdot> \<langle>R\<rangle>\<^sup>\<star> \<union> \<langle>R\<rangle>\<^sup>\<star> \<parallel> x\<cdot>{}"
    by (subst shuffle_comm) (intro Un_mono order_refl exchange rely_finite Int_lower2)
  also have "... = \<langle>R\<rangle>\<^sup>\<star> \<parallel> (x \<inter> FIN) \<cdot> y \<union> \<langle>R\<rangle>\<^sup>\<star> \<parallel> x\<cdot>{}"
    by (metis seq.star_trans_eq shuffle_comm)
  also have "... = \<langle>R\<rangle>\<^sup>\<star> \<parallel> ((x \<inter> FIN) \<cdot> y \<union> x\<cdot>{})"
    by simp
  also have "... = \<langle>R\<rangle>\<^sup>\<star> \<parallel> ((x \<inter> FIN) \<cdot> y \<union> x \<cdot> {} \<cdot> y)"
    by simp
  also have "... = \<langle>R\<rangle>\<^sup>\<star> \<parallel> x \<cdot> y"
    by (metis fin_inf_split seq.distrib_right')
  finally show ?thesis .
qed

lemma rely_l_prod1: "\<langle>R\<rangle>\<^sup>\<star> \<parallel> x \<cdot> y \<subseteq> (\<langle>R\<rangle>\<^sup>\<star> \<parallel> x) \<cdot> (\<langle>R\<rangle>\<^sup>\<star> \<parallel> y)"
proof -
  let ?lhs_inf = "\<Union>{lmap \<langle>id,id\<rangle> ` (rs \<sha> xs) |rs xs. rs \<in> \<langle>R\<rangle>\<^sup>\<star> \<and> xs \<in> x \<and> \<not> lfinite xs}"
  let ?lhs_fin = "\<Union>{lmap \<langle>id,id\<rangle> ` (rs \<sha> (xs \<frown> ys)) |rs xs ys. rs \<in> \<langle>R\<rangle>\<^sup>\<star> \<and> xs \<in> x \<and> ys \<in> y \<and> lfinite xs}"

  have inf_case: "?lhs_inf \<subseteq> \<Union>{lmap \<langle>id,id\<rangle> ` (rs \<sha> xs) |rs xs. rs \<in> \<langle>R\<rangle>\<^sup>\<star> \<and> xs \<in> x} \<cdot> \<Union>{lmap \<langle>id,id\<rangle> ` (rs \<sha> ys) |rs ys. rs \<in> \<langle>R\<rangle>\<^sup>\<star> \<and> ys \<in> y}"
    by (auto simp only: l_prod_def) (metis (lifting, full_types) lfinite_lmap lfinite_rights mem_Collect_eq tshuffle_words_def)

  have "?lhs_fin \<subseteq> \<Union>{lmap \<langle>id,id\<rangle> ` \<Union>{(rs' \<sha> xs) \<cdot> (rs'' \<sha> ys) |rs' rs''. rs = rs' \<frown> rs''} |rs xs ys. rs \<in> \<langle>R\<rangle>\<^sup>\<star> \<and> xs \<in> x \<and> ys \<in> y \<and> lfinite xs}"
    by (intro set_comp_Union_iso3 image_mono rely_dist) (auto simp add: fin_rely_def FIN_def)
  also have "... \<subseteq> \<Union>{\<Union>{lmap \<langle>id,id\<rangle> ` ((rs' \<sha> xs) \<cdot> (rs'' \<sha> ys)) |rs' rs''. rs = rs' \<frown> rs''} |rs xs ys. rs \<in> \<langle>R\<rangle>\<^sup>\<star> \<and> xs \<in> x \<and> ys \<in> y \<and> lfinite xs}"
    by (rule set_comp_Union_iso3) blast
  also have "... = \<Union>{\<Union>{lmap \<langle>id,id\<rangle> ` (rs' \<sha> xs) \<cdot> lmap \<langle>id,id\<rangle> ` (rs'' \<sha> ys) |rs' rs''. rs = rs' \<frown> rs''} |rs xs ys. rs \<in> \<langle>R\<rangle>\<^sup>\<star> \<and> xs \<in> x \<and> ys \<in> y \<and> lfinite xs}"
    by simp
  also have "... = \<Union>{lmap \<langle>id,id\<rangle> ` (rs' \<sha> xs) \<cdot> lmap \<langle>id,id\<rangle> ` (rs'' \<sha> ys) |rs' rs'' rs xs ys. rs = rs' \<frown> rs'' \<and> rs \<in> \<langle>R\<rangle>\<^sup>\<star> \<and> xs \<in> x \<and> ys \<in> y \<and> lfinite xs}"
    by blast
  also have "... = \<Union>{lmap \<langle>id,id\<rangle> ` (rs' \<sha> xs) \<cdot> lmap \<langle>id,id\<rangle> ` (rs'' \<sha> ys) |rs' rs'' xs ys. (\<exists>rs. rs \<in> \<langle>R\<rangle>\<^sup>\<star> \<and> rs = rs' \<frown> rs'') \<and> xs \<in> x \<and> ys \<in> y \<and> lfinite xs}"
    by blast
  also have "... = \<Union>{lmap \<langle>id,id\<rangle> ` (rs' \<sha> xs) \<cdot> lmap \<langle>id,id\<rangle> ` (rs'' \<sha> ys) |rs' rs'' xs ys. rs' \<in> \<langle>R\<rangle>\<^sup>\<star> \<and> rs'' \<in> \<langle>R\<rangle>\<^sup>\<star> \<and> xs \<in> x \<and> ys \<in> y \<and> lfinite xs}"
    by simp
  also have "... = \<Union>{{zs \<frown> ws |zs ws. zs \<in> lmap \<langle>id,id\<rangle> ` (rs' \<sha> xs) \<and> ws \<in> lmap \<langle>id,id\<rangle> ` (rs'' \<sha> ys)} |rs' rs'' xs ys. rs' \<in> \<langle>R\<rangle>\<^sup>\<star> \<and> rs'' \<in> \<langle>R\<rangle>\<^sup>\<star> \<and> xs \<in> x \<and> ys \<in> y \<and> lfinite xs}"
    apply (rule set_comp_Union_eq4)
    apply (erule conjE)
    apply (subst fin_l_prod)
    apply (auto simp add: FIN_def)
    by (metis (full_types) FIN_def in_mono lfinite_shuffle mem_Collect_eq rely_finite)
  also have "... = \<Union>{lmap \<langle>id,id\<rangle> ` (rs \<sha> xs) |rs xs. rs \<in> \<langle>R\<rangle>\<^sup>\<star> \<and> xs \<in> x \<and> lfinite xs} \<cdot> \<Union>{lmap \<langle>id,id\<rangle> ` (rs \<sha> ys) |rs ys. rs \<in> \<langle>R\<rangle>\<^sup>\<star> \<and> ys \<in> y}"
    apply (subst fin_l_prod)
    apply (simp add: FIN_def)
    apply clarify
    apply (metis (full_types) FIN_def lfinite_lmap lfinite_shuffle mem_Collect_eq rely_finite set_mp)
    by blast
  also have "... \<subseteq> \<Union>{lmap \<langle>id,id\<rangle> ` (rs \<sha> xs) |rs xs. rs \<in> \<langle>R\<rangle>\<^sup>\<star> \<and> xs \<in> x} \<cdot> \<Union>{lmap \<langle>id,id\<rangle> ` (rs \<sha> ys) |rs ys. rs \<in> \<langle>R\<rangle>\<^sup>\<star> \<and> ys \<in> y}"
    by (auto intro!: l_prod_isol)
  finally have fin_case: "?lhs_fin \<subseteq> \<Union>{lmap \<langle>id,id\<rangle> ` (rs \<sha> xs) |rs xs. rs \<in> \<langle>R\<rangle>\<^sup>\<star> \<and> xs \<in> x} \<cdot> \<Union>{lmap \<langle>id,id\<rangle> ` (rs \<sha> ys) |rs ys. rs \<in> \<langle>R\<rangle>\<^sup>\<star> \<and> ys \<in> y}" .

  have "\<langle>R\<rangle>\<^sup>\<star> \<parallel> x \<cdot> y = \<Union>{lmap \<langle>id,id\<rangle> ` (rs \<sha> zs) |rs zs. rs \<in> \<langle>R\<rangle>\<^sup>\<star> \<and> zs \<in> x \<cdot> y}"
    by (simp add: shuffle_def)
  also have "... = ?lhs_inf \<union> ?lhs_fin"
    by (simp add: l_prod_def) blast
  also have "... \<subseteq> \<Union>{lmap \<langle>id,id\<rangle> ` (rs \<sha> xs) |rs xs. rs \<in> \<langle>R\<rangle>\<^sup>\<star> \<and> xs \<in> x} \<cdot> \<Union>{lmap \<langle>id,id\<rangle> ` (rs \<sha> ys) |rs ys. rs \<in> \<langle>R\<rangle>\<^sup>\<star> \<and> ys \<in> y}"
    by (subst Un_absorb[symmetric], rule sup_mono[OF inf_case fin_case])
  also have "... = (\<langle>R\<rangle>\<^sup>\<star> \<parallel> x) \<cdot> (\<langle>R\<rangle>\<^sup>\<star> \<parallel> y)"
    by (simp add: shuffle_def)
  finally show ?thesis .
qed

lemma rely_l_prod [simp]: "\<langle>R\<rangle>\<^sup>\<star> \<parallel> x \<cdot> y = (\<langle>R\<rangle>\<^sup>\<star> \<parallel> x) \<cdot> (\<langle>R\<rangle>\<^sup>\<star> \<parallel> y)"
  by (metis rely_exchange rely_l_prod1 subset_antisym)

lemma rely_star: "\<langle>R\<rangle>\<^sup>\<star> \<parallel> x\<^sup>\<star> \<cdot> x = (\<langle>R\<rangle>\<^sup>\<star> \<parallel> x)\<^sup>\<star> \<cdot> (\<langle>R\<rangle>\<^sup>\<star> \<parallel> x)"
  sorry

definition stutter :: "('a \<times> 'a) lan" where
  "stutter = \<langle>Id_on UNIV\<rangle>\<^sup>\<star>"

end