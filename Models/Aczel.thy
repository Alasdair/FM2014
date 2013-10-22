theory Aczel
  imports Language
begin

coinductive consistent :: "('a \<times> 'a) llist \<Rightarrow> bool" where
  EqNil [intro!]: "consistent LNil"
| EqSingle [intro!]: "consistent (LCons \<sigma> LNil)"
| EqPair [intro!]: "snd \<sigma> = fst \<sigma>' \<Longrightarrow> consistent (LCons \<sigma>' t) \<Longrightarrow> consistent (LCons \<sigma> (LCons \<sigma>' t))"

lemma consistent_LConsD [dest]: "consistent (LCons \<sigma> t) \<Longrightarrow> consistent t"
  by (erule consistent.cases) auto

lemma consistent_LConsE [elim]: "consistent (LCons \<sigma> (LCons \<sigma>' t)) \<Longrightarrow> snd \<sigma> = fst \<sigma>'"
  by (erule consistent.cases) auto

lemma lnth_repeat [simp]: "lnth (repeat x) n = x"
  by (induct n) simp_all

lemma inf_stutter_consistent: "consistent (repeat (\<sigma>, \<sigma>))"
proof -
  have "\<forall>n. snd (lnth (repeat (\<sigma>, \<sigma>)) n) = fst (lnth (repeat (\<sigma>, \<sigma>)) (Suc n))"
    by (simp del: lnth_iterates)
  thus ?thesis
  proof coinduct
    case (consistent t)
    show ?case
    proof (cases t)
      assume "t = LNil"
      thus ?case by simp
    next
      fix \<sigma> t'
      assume [simp]: "t = LCons \<sigma> t'"
      hence "?EqSingle \<or> ?EqPair"
      proof (cases t')
        assume "t' = LNil"
        thus "?EqSingle \<or> ?EqPair" by simp
      next
        fix \<sigma>' t''
        assume [simp]: "t' = LCons \<sigma>' t''"
        from consistent
        have "?EqPair"
          by (auto, erule_tac x = 0 in allE, auto, erule_tac x = "Suc n" in allE, auto)
        thus "?EqSingle \<or> ?EqPair" by simp
      qed
      thus ?case by simp
    qed
  qed
qed

definition Con :: "('a \<times> 'a) lan" where
  "Con = Collect consistent"

definition Aczel :: "('a \<times> 'a) lan \<Rightarrow> ('a \<times> 'a) lan" ("\<pi>") where
  "\<pi> X = X \<inter> Con"

lemma inf_stutter_Con [intro!]: "repeat (\<sigma>, \<sigma>) \<in> Con"
  by (metis Con_def inf_stutter_consistent mem_Collect_eq)

lemma Aczel_continuous: "\<pi> (\<Union>\<XX>) = \<Union>{\<pi> X |X. X \<in> \<XX>}"
  by (auto simp add: Aczel_def)

lemma Aczel_inter [simp]: "\<pi> (X \<inter> Y) = \<pi> X \<inter> \<pi> Y"
  by (metis Aczel_def Int_assoc inf_commute inf_left_idem)

lemma Aczel_union [simp]: "\<pi> (X \<union> Y) = \<pi> X \<union> \<pi> Y"
  by (auto simp add: Aczel_def)

lemma Aczel_coextensive [intro!]: "\<pi> X \<subseteq> X"
  by (auto simp add: Aczel_def)

lemma Aczel_iso [intro]: "X \<subseteq> Y \<Longrightarrow> \<pi> X \<subseteq> \<pi> Y"
  by (auto simp add: Aczel_def)

lemma Aczel_idem [simp]: "\<pi> (\<pi> X) = \<pi> X"
  by (auto simp add: Aczel_def)

lemma Con_l_prod: "Con = (Con \<cdot> Con) \<inter> Con"
  by (auto simp add: Con_def l_prod_def) (metis EqNil lappend_LNil2)

lemma [simp]: "\<pi> {xs \<in> X. \<not> lfinite xs} = \<pi> X \<cdot> {}"
  by (auto simp add: l_prod_def Aczel_def)

lemma consistent_lappend1 [dest]:
  assumes "consistent (t \<frown> s)" shows "consistent t"
proof (cases "lfinite t")
  assume "lfinite t"
  from this and assms
  show "consistent t"
  proof (induct t rule: lfinite_induct)
    case Nil show ?case by blast
  next
    case (Cons \<sigma> t)
    thus ?case
      by (cases t) auto
  qed
next
  assume "\<not> lfinite t"
  from this and assms
  show "consistent t"
    by (metis lappend_inf)
qed

lemma consistent_lappend2 [dest]: "lfinite t \<Longrightarrow> consistent (t \<frown> s) \<Longrightarrow> consistent s"
proof (induct t rule: lfinite_induct)
  case Nil thus ?case by simp
next
  case (Cons \<sigma> t)
  thus ?case
    by (cases t) auto
qed

lemma [dest]: "xs \<frown> ys \<in> Con \<Longrightarrow> xs \<in> Con"
  by (auto simp add: Con_def)

lemma [dest]: "lfinite xs \<Longrightarrow> xs \<frown> ys \<in> Con \<Longrightarrow> ys \<in> Con"
  by (auto simp add: Con_def)

lemma [simp]: "X \<cdot> {} \<union> X \<inter> FIN = X"
  by (auto simp add: l_prod_def FIN_def)

lemma Aczel_l_prod [simp]: "\<pi> (\<pi> X \<cdot> \<pi> Y) = \<pi> (X \<cdot> Y)"
proof -
  have "\<pi> (X \<cdot> Y) = \<pi> {xs \<in> X. \<not> lfinite xs} \<union> \<pi> {xs \<frown> ys |xs ys. xs \<in> X \<and> lfinite xs \<and> ys \<in> Y}"
    by (simp add: l_prod_def)
  also have "... = \<pi> X \<cdot> {} \<union> \<pi> {xs \<frown> ys |xs ys. xs \<in> X \<and> lfinite xs \<and> ys \<in> Y}"
    by simp
  also have "... = \<pi> X \<cdot> {} \<union> \<pi> ((\<pi> X \<inter> FIN) \<cdot> \<pi> Y)"
    by (subst fin_l_prod, metis (mono_tags) inf.cobounded2, auto simp add: Aczel_def FIN_def)
  also have "... = \<pi> (\<pi> X \<cdot> {} \<union> (\<pi> X \<inter> FIN) \<cdot> \<pi> Y)"
    by (auto simp add: Aczel_def l_prod_def)
  also have "... = \<pi> (\<pi> X \<cdot> {} \<cdot> \<pi> Y \<union> (\<pi> X \<inter> FIN) \<cdot> \<pi> Y)"
    by (metis l_prod_zero seq.mult_assoc)
  also have "... = \<pi> ((\<pi> X \<cdot> {} \<union> (\<pi> X \<inter> FIN)) \<cdot> \<pi> Y)"
    by (metis l_prod_distr)
  also have "... = \<pi> (\<pi> X \<cdot> \<pi> Y)"
    by simp
  finally show ?thesis by blast
qed

lemma [simp]: "ltake \<infinity> xs = xs"
  apply (cases "lfinite xs")
  apply (induct xs rule: lfinite_induct)
  apply simp_all
  apply (subst eSuc_infinity[symmetric])
  apply (subst ltake_LCons)
  apply (simp del: eSuc_infinity)
  by (metis ltake_all not_lfinite_llength order_refl)

lemma llist_cases3:
  "P LNil \<Longrightarrow> (\<And>x. xs = LCons x LNil \<Longrightarrow> P xs) \<Longrightarrow> (\<And>x y ys. xs = LCons y (LCons x ys) \<Longrightarrow> P xs) \<Longrightarrow> P xs"
  by (metis (full_types) lhd_LCons_ltl) 

lemma consistent_ltake: "consistent t \<Longrightarrow> consistent (ltake n t)"
proof (induct n, simp_all)
  fix n
  assume "consistent t"
  thus "consistent (ltake (enat n) t)"
  proof (induct n arbitrary: t)
    case 0 show ?case by (auto simp: enat_0)
  next
    case (Suc n)
    show ?case
    proof (rule llist_cases3[where xs = t])
      show "consistent (ltake (enat (Suc n)) LNil)"
        by (simp add: eSuc_enat[symmetric]) blast
    next
      fix \<sigma>
      assume "t = LCons \<sigma> LNil"
      from this and Suc.prems show "consistent (ltake (enat (Suc n)) t)"
        by (cases n) (simp_all add: enat_0 eSuc_enat[symmetric])
    next
      fix \<sigma> \<sigma>' t'
      assume "t = LCons \<sigma> (LCons \<sigma>' t')"
      from this and Suc show "consistent (ltake (enat (Suc n)) t)"
        apply (cases n)
        apply (simp_all add: eSuc_enat[symmetric] enat_0)
        apply blast
        apply (rule EqPair)
        apply (erule consistent_LConsE)
        by (metis consistent_LConsD ltake_eSuc_LCons)
    qed
  qed
qed

lemma Aczel_par: "\<pi> (\<pi> X \<parallel> \<pi> Y) \<le> \<pi> (X \<parallel> Y)"
  by (metis Aczel_coextensive Aczel_iso par.mult_isol_var)

lemma Aczel_consistent [simp]: "\<pi> X \<inter> Con = \<pi> X"
  by (simp add: Aczel_def)

lemma Aczel_UNIV [simp]: "\<pi> UNIV = Con"
  by (auto simp add: Aczel_def)

lemma consistent_lappend:
  "lfinite xs \<Longrightarrow> consistent (LCons x xs \<frown> LCons y ys) \<Longrightarrow> snd (llast (LCons x xs)) = fst y"
  by (induct xs arbitrary: x rule: lfinite_induct) auto

lemma [dest!]: "consistent (LCons x xs \<frown> LCons y ys) \<Longrightarrow> lfinite xs \<longrightarrow> snd (llast (LCons x xs)) = fst y"
  by (metis consistent_lappend)

lemma [simp]: "llast (LCons (\<sigma>, \<sigma>) (llist_of (replicate n (\<sigma>, \<sigma>)))) = (\<sigma>, \<sigma>)"
  by (induct n) auto

definition Aczel_mult :: "('a \<times> 'a) lan \<Rightarrow> ('a \<times> 'a) lan \<Rightarrow> ('a \<times> 'a) lan" (infixl "\<otimes>" 75) where
  "X \<otimes> Y = \<pi> (X \<cdot> Y)"

lemma amult_distl [simp]: "X \<otimes> (Y \<union> Z) = X \<otimes> Y \<union> X \<otimes> Z"
  by (simp add: Aczel_mult_def)

lemma amult_distr [simp]: "(X \<union> Y) \<otimes> Z = X \<otimes> Z \<union> Y \<otimes> Z"
  by (simp add: Aczel_mult_def)

lemma amult_assoc: "X \<otimes> (Y \<otimes> Z) = (X \<otimes> Y) \<otimes> Z"
  by (simp add: Aczel_mult_def) (metis Aczel_def Aczel_l_prod inf_commute inf_left_idem seq.mult_assoc)

lemma consistent_replicate': "consistent (llist_of xs) \<Longrightarrow> \<forall>y\<in>set xs. \<exists>\<sigma>. y = (\<sigma>, \<sigma>) \<Longrightarrow> \<exists>n \<sigma>. xs = replicate n (\<sigma>, \<sigma>)"
proof (induct xs)
  case Nil show ?case by simp
next
  case (Cons x1 xs)
  thus ?case
  proof (induct xs)
    case Nil thus ?case
      by (rule_tac x = 1 in exI) auto
  next
    case (Cons x2 xs)
    thus ?case
      apply -
      apply simp
      apply (frule consistent_LConsD)
      apply simp
      apply (frule consistent_LConsD) back
      apply simp
      apply auto
      apply (subgoal_tac "\<exists>n \<sigma>. xs = replicate n (\<sigma>, \<sigma>)")
      apply simp
      apply (subgoal_tac "\<sigma>'' = \<sigma>'")
      apply simp
      apply (subgoal_tac "\<sigma>' = \<sigma>")
      apply simp
      apply (rule_tac x = "Suc n" in exI)
      apply simp
      apply (metis in_set_member in_set_replicate member_rec(1) prod.inject)
      apply (drule consistent_LConsE)
      apply simp
      apply (rule_tac x = "n - 1" in exI)
      by (metis tl.simps(2) tl_replicate)
  qed
qed

lemma replicate_finite_Con: "llist_of (replicate n (\<sigma>, \<sigma>)) \<in> Con"
proof (induct n)
  case 0 show ?case
    by (auto simp add: Con_def)
next
  case (Suc n) thus ?case
    by (cases n) (auto simp add: Con_def)
qed

definition atomic :: "'a rel \<Rightarrow> ('a \<times> 'a) lan" ("\<langle>_\<rangle>" [0] 1000) where
  "\<langle>R\<rangle> \<equiv> ((\<lambda>x. LCons x LNil) ` R)"

lemma [iff]: "\<langle>X\<rangle> \<subseteq> \<langle>Y\<rangle> \<longleftrightarrow> X \<subseteq> Y"
  by (auto simp add: atomic_def)

lemma rely_def: "\<langle>R\<rangle>\<^sup>\<star> = {xs. lfinite xs \<and> lset xs \<subseteq> R}"
  sorry

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

lemma rely_union1: "\<langle>R\<rangle>\<^sup>\<star> \<parallel> \<langle>S\<rangle>\<^sup>\<star> \<subseteq> \<langle>R \<union> S\<rangle>\<^sup>\<star>"
  apply (simp add: rely_def shuffle_def Sup_le_iff)
  apply clarify
  apply (intro conjI)
  apply (metis lfinite_lmap lfinite_shuffle)
  apply (simp add: tshuffle_words_def)
  by (metis llist.set_map lset_lr)

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
  sorry

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

lemma rely_union [simp]: "\<langle>R\<rangle>\<^sup>\<star> \<parallel> \<langle>S\<rangle>\<^sup>\<star> = \<langle>R \<union> S\<rangle>\<^sup>\<star>"
proof
  show "\<langle>R\<rangle>\<^sup>\<star> \<parallel> \<langle>S\<rangle>\<^sup>\<star> \<subseteq> \<langle>R \<union> S\<rangle>\<^sup>\<star>"
    apply (simp add: rely_def shuffle_def Sup_le_iff)
    apply clarify
    apply (intro conjI)
    apply (metis lfinite_lmap lfinite_shuffle)
    apply (simp add: tshuffle_words_def)
    by (metis llist.set_map lset_lr)
next
  {
    fix xs
    assume assm: "xs \<in> \<langle>R \<union> S\<rangle>\<^sup>\<star>"
    hence "lfinite xs"
      by (auto simp add: rely_def)
    have "xs = lmap \<langle>id,id\<rangle> (lfilter (\<lambda>x. x \<in> R) xs \<triangleright> traj (lmap (\<lambda>x. if x \<in> R then Inl () else Inr ()) xs) \<triangleleft> lfilter (\<lambda>x. x \<notin> R) xs)"
      by (subst lfilter_interleave[where P = "\<lambda>x. x \<in> R"], simp)
    also have "... \<in> lmap \<langle>id,id\<rangle> ` (lfilter (\<lambda>x. x \<in> R) xs \<sha> lfilter (\<lambda>x. x \<notin> R) xs)"
      apply (intro imageI)
      apply (simp add: tshuffle_words_def image_def)
      apply (subst lefts_interleave_llength)
      defer
      apply (subst rights_interleave_llength)
      apply auto
      sorry
    also have "... \<subseteq> \<langle>R\<rangle>\<^sup>\<star> \<parallel> \<langle>S\<rangle>\<^sup>\<star>"
      apply (auto simp add: rely_def shuffle_def)
      apply (rule_tac x = "lmap \<langle>id,id\<rangle> ` (lfilter (\<lambda>x. x \<in> R) xs \<sha> lfilter (\<lambda>x. x \<notin> R) xs)" in exI)
      apply simp
      apply (rule_tac x = "lfilter (\<lambda>x. x \<in> R) xs" in exI)
      apply (rule_tac x = "lfilter (\<lambda>x. x \<notin> R) xs" in exI)
      apply auto
      apply (metis `lfinite xs` lfinite_lfilterI)
      apply (metis `lfinite xs` lfinite_lfilterI)
      apply (insert assm)
      by (auto simp add: rely_def)
    finally have "xs \<in> \<langle>R\<rangle>\<^sup>\<star> \<parallel> \<langle>S\<rangle>\<^sup>\<star>" .
  }
  thus "\<langle>R \<union> S\<rangle>\<^sup>\<star> \<subseteq> \<langle>R\<rangle>\<^sup>\<star> \<parallel> \<langle>S\<rangle>\<^sup>\<star>"
    by blast
qed

lemmas [intro] = seq.star_iso[rule_format]

lemma rely_1: "\<langle>R\<rangle>\<^sup>\<star> \<le> \<langle>R\<rangle>\<^sup>\<star> \<parallel> \<langle>S\<rangle>\<^sup>\<star>"
  by (auto del: subsetI)

lemma rely_2: "\<langle>R\<rangle>\<^sup>\<star> \<parallel> \<langle>R\<rangle>\<^sup>\<star> \<subseteq> \<langle>R\<rangle>\<^sup>\<star>"
  by auto 

lemma rely_inter: "\<langle>R\<rangle>\<^sup>\<star> \<inter> \<langle>S\<rangle>\<^sup>\<star> = \<langle>R \<inter> S\<rangle>\<^sup>\<star>"
  by (auto simp add: rely_def)

lemma rely_lappend [simp]: "(\<exists>rs. rs \<in> \<langle>R\<rangle>\<^sup>\<star> \<and> rs = rs' \<frown> rs'') \<longleftrightarrow> (rs' \<in> \<langle>R\<rangle>\<^sup>\<star> \<and> rs'' \<in> \<langle>R\<rangle>\<^sup>\<star>)"
  by (auto simp add: rely_def FIN_def)

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
  by (auto simp add: rely_def FIN_def)

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

lemma rely_l_prod: "\<langle>R\<rangle>\<^sup>\<star> \<parallel> x \<cdot> y \<subseteq> (\<langle>R\<rangle>\<^sup>\<star> \<parallel> x) \<cdot> (\<langle>R\<rangle>\<^sup>\<star> \<parallel> y)"
proof -
  let ?lhs_inf = "\<Union>{lmap \<langle>id,id\<rangle> ` (rs \<sha> xs) |rs xs. rs \<in> \<langle>R\<rangle>\<^sup>\<star> \<and> xs \<in> x \<and> \<not> lfinite xs}"
  let ?lhs_fin = "\<Union>{lmap \<langle>id,id\<rangle> ` (rs \<sha> (xs \<frown> ys)) |rs xs ys. rs \<in> \<langle>R\<rangle>\<^sup>\<star> \<and> xs \<in> x \<and> ys \<in> y \<and> lfinite xs}"

  have inf_case: "?lhs_inf \<subseteq> \<Union>{lmap \<langle>id,id\<rangle> ` (rs \<sha> xs) |rs xs. rs \<in> \<langle>R\<rangle>\<^sup>\<star> \<and> xs \<in> x} \<cdot> \<Union>{lmap \<langle>id,id\<rangle> ` (rs \<sha> ys) |rs ys. rs \<in> \<langle>R\<rangle>\<^sup>\<star> \<and> ys \<in> y}"
    by (auto simp only: l_prod_def) (metis (lifting, full_types) lfinite_lmap lfinite_rights mem_Collect_eq tshuffle_words_def)

  have "?lhs_fin \<subseteq> \<Union>{lmap \<langle>id,id\<rangle> ` \<Union>{(rs' \<sha> xs) \<cdot> (rs'' \<sha> ys) |rs' rs''. rs = rs' \<frown> rs''} |rs xs ys. rs \<in> \<langle>R\<rangle>\<^sup>\<star> \<and> xs \<in> x \<and> ys \<in> y \<and> lfinite xs}"
    by (intro set_comp_Union_iso3 image_mono rely_dist) (auto simp add: rely_def FIN_def)
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

end
