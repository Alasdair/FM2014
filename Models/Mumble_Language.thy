theory Mumble_Language
  imports Aczel
begin

inductive_set mumble :: "('a \<times> 'a) llist \<Rightarrow> ('a \<times> 'a) lan" for xs where
  self [simp, intro!]: "xs \<in> mumble xs"
| mumble [dest]: "ys \<frown> LCons (\<sigma>, \<sigma>') (LCons (\<sigma>', \<sigma>'') zs) \<in> mumble xs \<Longrightarrow> ys \<frown> LCons (\<sigma>, \<sigma>'') zs \<in> mumble xs"

definition Mumble :: "('a \<times> 'a) lan \<Rightarrow> ('a \<times> 'a) lan" ("_\<^sup>\<dagger>" [1000] 1000) where
  "X\<^sup>\<dagger> = \<Union>{mumble xs |xs. xs \<in> X}"

lemma consistent_mumble: "lfinite ys \<Longrightarrow> consistent (ys \<frown> LCons (\<sigma>, \<sigma>') (LCons (\<sigma>', \<sigma>'') xs)) \<Longrightarrow> consistent (ys \<frown> LCons (\<sigma>, \<sigma>'') xs)"
proof (induct ys rule: lfinite.induct)
  case lfinite_LNil
  thus ?case
    apply (cases xs)
    apply auto
    apply (drule consistent_LConsD)
    apply (drule consistent_LConsE)
    by auto
next
  case (lfinite_LConsI xs' x')
  thus ?case
    apply simp
    apply (cases xs')
    apply auto
    by (metis consistent_LConsE fst_conv)
qed

lemma inconsistent_mumble: "lfinite ys \<Longrightarrow> \<not> consistent (ys \<frown> LCons (\<sigma>, \<sigma>') (LCons (\<sigma>', \<sigma>'') xs)) \<Longrightarrow> \<not> consistent (ys \<frown> LCons (\<sigma>, \<sigma>'') xs)"
proof (induct ys rule: lfinite.induct)
  case lfinite_LNil
  thus ?case
    apply (cases xs)
    apply auto
    apply (drule consistent_LConsE)
    by auto
next
  case (lfinite_LConsI xs' x')
  thus ?case
    apply auto
    apply (cases xs')
    apply auto
    by (metis consistent_LConsE fst_conv)
qed

lemma mumble_preserves_consistent [dest]: "xs \<in> mumble ys \<Longrightarrow> consistent xs \<longleftrightarrow> consistent ys"
proof (induct xs rule: mumble.induct)
  case self thus ?case by simp
next
  case (mumble ws \<sigma> \<sigma>' \<sigma>'' vs)
  thus ?case
  proof auto
    assume "consistent (ws \<frown> LCons (\<sigma>, \<sigma>') (LCons (\<sigma>', \<sigma>'') vs))"
    thus "consistent (ws \<frown> LCons (\<sigma>, \<sigma>'') vs)"
      by (metis consistent_mumble lappend_inf)
  next
    assume "\<not> consistent (ws \<frown> LCons (\<sigma>, \<sigma>') (LCons (\<sigma>', \<sigma>'') vs))" and "consistent (ws \<frown> LCons (\<sigma>, \<sigma>'') vs)"
    thus "False"
      by (metis inconsistent_mumble lappend_inf)
  qed
qed

lemma mumble_trans: "xs \<in> mumble ys \<Longrightarrow> ys \<in> mumble zs \<Longrightarrow> xs \<in> mumble zs"
proof (induct xs rule: mumble.induct)
  case self
  thus ?case .
next
  case (mumble ws \<sigma> \<sigma>' \<sigma>'' vs)
  from mumble(2)[OF mumble(3)]
  show ?case
    by (rule mumble.mumble)
qed

lemma mumble_lappend: "xs \<in> mumble xs' \<Longrightarrow> ys \<in> mumble ys' \<Longrightarrow> (xs \<frown> ys) \<in> mumble (xs' \<frown> ys')"
proof (induct xs rule: mumble.induct)
  case self
  thus ?case
  proof (induct ys rule: mumble.induct)
    case self
    show ?case
      by (metis mumble.self)
  next
    case (mumble ws \<sigma> \<sigma>' \<sigma>'' vs)
    thus ?case
      by (metis lappend_assoc mumble.mumble)
  qed
next
  case (mumble ws \<sigma> \<sigma>' \<sigma>'' vs)
  thus ?case
    by (metis lappend_assoc lappend_code(2) mumble.mumble)
qed

lemma Mumble_iso: "X \<subseteq> Y \<Longrightarrow> X\<^sup>\<dagger> \<subseteq> Y\<^sup>\<dagger>"
  by (auto simp add: Mumble_def)

lemma Mumble_ext: "X \<subseteq> X\<^sup>\<dagger>"
  by (auto simp add: Mumble_def)

lemma Mumble_idem [simp]: "X\<^sup>\<dagger>\<^sup>\<dagger> = X\<^sup>\<dagger>"
proof -
  have "X\<^sup>\<dagger>  \<subseteq> X\<^sup>\<dagger>\<^sup>\<dagger>"
    by (metis Mumble_ext)
  thus "X\<^sup>\<dagger>\<^sup>\<dagger> = X\<^sup>\<dagger>"
    by (auto dest: mumble_trans simp add: Mumble_def)
qed

lemma Mumble_union [simp]: "(X \<union> Y)\<^sup>\<dagger> = X\<^sup>\<dagger> \<union> Y\<^sup>\<dagger>"
  by (auto simp add: Mumble_def)

lemma Mumble_continuous: "(\<Union>\<XX>)\<^sup>\<dagger> = \<Union>{X\<^sup>\<dagger> |X. X \<in> \<XX>}"
  by (auto simp add: Mumble_def)

lemma Mumble_Con [simp]: "Con\<^sup>\<dagger> = Con"
  by (auto simp add: Mumble_def Con_def)

lemma Mumble_meet [simp]: "(X\<^sup>\<dagger> \<inter> Y\<^sup>\<dagger>)\<^sup>\<dagger> = X\<^sup>\<dagger> \<inter> Y\<^sup>\<dagger>"
  by (auto dest: mumble_trans simp add: Mumble_def)

lemma mumble_infinite [dest]: "ys \<in> mumble xs \<Longrightarrow> \<not> lfinite xs \<Longrightarrow> \<not> lfinite ys"
  by (induct ys rule: mumble.induct) auto

definition "llist_Case \<equiv> llist_case"

primrec ldeleteLeft_nat :: "nat \<Rightarrow> ('a + 'b) llist \<Rightarrow> ('a + 'b) llist" where
  "ldeleteLeft_nat 0 xs = ltakeWhile is_right xs \<frown> ltl (ldropWhile is_right xs)"
| "ldeleteLeft_nat (Suc n) xs = ltakeWhile is_right xs \<frown> llist_Case LNil (\<lambda>x' xs'. LCons x' (ldeleteLeft_nat n xs')) (ldropWhile is_right xs)"

primrec ldeleteLeft :: "enat \<Rightarrow> ('a + 'b) llist \<Rightarrow> ('a + 'b) llist" where
  "ldeleteLeft (enat n) xs = ldeleteLeft_nat n xs"
| "ldeleteLeft \<infinity> xs = xs"

primrec linsertLeft_nat :: "nat \<Rightarrow> 'a \<Rightarrow> ('a + 'b) llist \<Rightarrow> ('a + 'b) llist" where
  "linsertLeft_nat 0 x xs = ltakeWhile is_right xs \<frown> LCons (Inl x) (ldropWhile is_right xs)"
| "linsertLeft_nat (Suc n) x xs = ltakeWhile is_right xs \<frown> llist_Case LNil (\<lambda>x' xs'. LCons x' (linsertLeft_nat n x xs')) (ldropWhile is_right xs)"

primrec linsertLeft :: "enat \<Rightarrow> 'a \<Rightarrow> ('a + 'b) llist \<Rightarrow> ('a + 'b) llist" where
  "linsertLeft (enat n) x xs = linsertLeft_nat n x xs"
| "linsertLeft \<infinity> x xs = xs"

primrec linsert_nat :: "nat \<Rightarrow> 'a \<Rightarrow> 'a llist \<Rightarrow> 'a llist" where
  "linsert_nat 0 x xs = LCons x xs"
| "linsert_nat (Suc n) x xs = llist_Case LNil (\<lambda>x' xs'. LCons x' (linsert_nat n x xs')) xs"

primrec linsert :: "enat \<Rightarrow> 'a \<Rightarrow> 'a llist \<Rightarrow> 'a llist" where
  "linsert (enat n) x xs = linsert_nat n x xs"
| "linsert \<infinity> x xs = xs"

lemma "mumble xs \<cdot> mumble ys \<subseteq> mumble (xs \<frown> ys)"
  apply (auto simp add: l_prod_def)
  apply (metis lappend_inf mumble.self mumble_lappend)
  by (metis mumble_lappend)

lemma [simp]: "llength xs = \<infinity> \<Longrightarrow> xs \<frown> ys = xs"
  by (metis lappend_inf llength_eq_infty_conv_lfinite)

lemma [dest!]: "llength xs = \<infinity> \<Longrightarrow> LNil \<in> xs \<sha> ys \<Longrightarrow> False"
  by (auto simp add: tshuffle_words_def)

notation ltake ("\<up>")
  and ldrop ("\<down>")

lemma [simp]: "\<up> (llength xs) xs = xs"
  by (metis ltake_all order_refl)

lemma [simp]: "traj LNil = LNil"
  by (metis traj_LNil traj_interleave)

lemma [simp]: "traj (LCons (Inl x) xs) = LCons (Inl ()) (traj xs)"
  by (simp add: traj_def)

lemma [simp]: "traj (LCons (Inr x) xs) = LCons (Inr ()) (traj xs)"
  by (simp add: traj_def)

lemma LConsl_in_shuffle [dest]: "LCons (Inl x) (xs \<frown> ys) \<in> xs' \<sha> ys' \<Longrightarrow> xs \<frown> ys \<in> ltl xs' \<sha> ys'"
  by (auto simp add: tshuffle_words_def)

lemma LConsr_in_shuffle [dest]: "LCons (Inr y) (xs \<frown> ys) \<in> xs' \<sha> ys' \<Longrightarrow> xs \<frown> ys \<in> xs' \<sha> ltl ys'"
  by (auto simp add: tshuffle_words_def)

lemma interleave_append:
  assumes "zs \<in> xs \<sha> ys"
  and "t \<frown> t' = traj zs"
  shows "xs \<triangleright> t \<frown> t' \<triangleleft> ys = (\<up> (llength (\<ll> t)) xs \<triangleright> t \<triangleleft> \<up> (llength (\<rr> t)) ys) \<frown> (\<down> (llength (\<ll> t)) xs \<triangleright> t' \<triangleleft> \<down> (llength (\<rr> t)) ys)"
proof -
  {
    assume "\<not> lfinite t"
    moreover have "\<And>xs ys. \<not> lfinite (xs \<triangleright> t \<triangleleft> ys)"
      by (metis calculation lfinite_traj)
    ultimately have ?thesis using assms
      apply (auto simp add: lappend_inf)
      apply (subst lappend_inf)
      apply (simp add: traj_def)
      apply blast
      by (metis (lifting, full_types) dual_order.refl ltake_all mem_Collect_eq tshuffle_words_def)
  }
  moreover
  {
    assume "lfinite t"
    hence "?thesis" using assms
    proof (induct t arbitrary: xs ys zs rule: lfinite_induct)
      case Nil thus ?case by simp
    next
      case (Cons w ws)
      thus ?case
        apply (cases w)
        apply (simp add: interleave_left)
        apply (subgoal_tac "ltl zs \<in> ltl xs \<sha> ys")
        apply (subgoal_tac "ws \<frown> t' = traj (ltl zs)")
        apply (metis (hide_lams, no_types) interleave_left ldrop_ltl ltake_ltl)
        apply (metis interleave_left ltl_simps(2) reinterleave traj_interleave)
        apply (simp add: tshuffle_words_def)
        apply (metis interleave_left lefts_LConsl ltl_simps(2) reinterleave rights_LConsl)
        apply (simp add: interleave_right)
        apply (subgoal_tac "ltl zs \<in> xs \<sha> ltl ys")
        apply (subgoal_tac "ws \<frown> t' = traj (ltl zs)")
        apply (metis (hide_lams, no_types) interleave_right ldrop_ltl ltake_ltl)
        apply (metis interleave_right ltl_simps(2) reinterleave traj_interleave)
        apply (simp add: tshuffle_words_def)
        by (metis interleave_right lefts_LConsr ltl_simps(2) reinterleave rights_LConsr)
    qed
  }
  ultimately show ?thesis by auto
qed

lemma traj_to_shuffle:
  assumes "llength (\<ll> t) = llength xs"
  and "llength (\<rr> t) = llength ys"
  shows "\<exists>zs. t = traj zs \<and> zs \<in> xs \<sha> ys"
  using assms
  apply (auto simp add: tshuffle_words_def)
  apply (rule_tac x = "xs \<triangleright> t \<triangleleft> ys" in exI)
  apply auto
  apply (metis lefts_interleave_llength traj_interleave)
  by (metis rights_interleave_llength traj_interleave)

lemma interleave_append_llength:
  assumes "llength (\<ll> (t \<frown> t')) = llength xs"
  and "llength (\<rr> (t \<frown> t')) = llength ys"
  shows "xs \<triangleright> t \<frown> t' \<triangleleft> ys = (\<up> (llength (\<ll> t)) xs \<triangleright> t \<triangleleft> \<up> (llength (\<rr> t)) ys) \<frown> (\<down> (llength (\<ll> t)) xs \<triangleright> t' \<triangleleft> \<down> (llength (\<rr> t)) ys)"
  by (metis (hide_lams, no_types) assms(1) assms(2) interleave_append traj_to_shuffle)

lemma lefts_ltake_right [simp]: "\<ll> (ltakeWhile is_right xs) = LNil"
  by (auto dest: lset_ltakeWhileD simp add: lefts_def)

lemma LCons_lappend_LNil: "LCons y ys = LCons y LNil \<frown> ys"
  by (metis lappend_code(1) lappend_code(2))

lemma traj_lappend [simp]: "traj (xs \<frown> ys) = traj xs \<frown> traj ys"
  by (auto simp add: traj_def lmap_lappend_distrib)

lemma [simp]:
  fixes t :: "(unit + unit) llist"
  shows "traj t = t"
  apply (auto simp add: traj_def)
  apply (subst lmap_ident[symmetric]) back
  apply (rule lmap2_id)
proof -
  fix x :: "(unit + unit)"
  show "(case x of Inl x \<Rightarrow> Inl x | Inr x \<Rightarrow> Inr x) = x"
    by (cases x) auto
qed

lemma intro_traj: "xs \<triangleright> t \<triangleleft> ys = xs \<triangleright> traj t \<triangleleft> ys"
  by simp

lemma interleave_ldropWhile: "(\<exists>t'\<in>lset t. \<exists>a. t' = Inl a) \<Longrightarrow> ldropWhile is_right (traj t) = LCons (Inl ()) (ltl (ldropWhile is_right (traj t)))"
  by (metis interleave_ltakeWhile_is_right is_right.simps(2) lappend_LNil2 lappend_ltakeWhile_ldropWhile ldropWhile_rights_not_LNil reinterleave split_llist)

lemma shuffle_lset: "t \<in> xs \<sha> ys \<Longrightarrow> lset t = Inl ` (lset xs) \<union> Inr ` (lset ys)"
  apply (auto simp add: tshuffle_words_def lefts_def rights_def image_def)
  apply (metis is_left.simps(2) is_right.simps(2) not_is_left swap.cases unl.simps(1) unr.simps(1))
  apply (metis is_left.simps(2) obj_sumE unl.simps(1))
  by (metis is_right.simps(2) obj_sumE unr.simps(1))

lemma lappend_not_LNil_iff [simp]: "xs \<frown> ys \<noteq> LNil \<longleftrightarrow> xs \<noteq> LNil \<or> ys \<noteq> LNil"
  by (metis LNil_eq_lappend_iff)

lemma [simp]: "lmap f xs \<noteq> LNil \<longleftrightarrow> xs \<noteq> LNil"
  by (metis LNil_eq_llist_map)

lemma [simp]: "xs \<triangleright> t \<triangleleft> ys \<noteq> LNil \<longleftrightarrow> t \<noteq> LNil"
  by (metis traj_LNil traj_interleave)

(* Lemmas for simplifying trajectory based goals *)

lemma traj_not_LNil: "traj t \<noteq> LNil \<longleftrightarrow> t \<noteq> LNil"
  by (metis reinterleave traj_LNil traj_interleave)

lemma ltakeWhile_right_traj [simp]: "ltakeWhile is_right (traj t) = traj (ltakeWhile is_right t)"
  by (simp add: traj_def ltakeWhile_lmap)

lemma ltakeWhile_left_traj [simp]: "ltakeWhile is_left (traj t) = traj (ltakeWhile is_left t)"
  by (simp add: traj_def ltakeWhile_lmap)

lemma ltl_traj [simp]: "ltl (traj t) = traj (ltl t)"
  by (simp add: traj_def)

lemma ldropWhile_right_traj [simp]: "ldropWhile is_right (traj t) = traj (ldropWhile is_right t)"
  by (simp add: traj_def ldropWhile_lmap)

lemma ldropWhile_left_traj [simp]: "ldropWhile is_left (traj t) = traj (ldropWhile is_left t)"
  by (simp add: traj_def ldropWhile_lmap)  

lemma traj_LCons: "traj (LCons x xs) = LCons (\<langle>\<lambda>x. Inl (),\<lambda>x. Inr ()\<rangle> x) (traj xs)"
  by (simp add: traj_def)

lemma traj_llist_Case [simp]:
  fixes ys :: "('a + 'b) llist"
  shows "llist_Case LNil (\<lambda>x xs. xs) (traj ys) = traj (llist_Case LNil (\<lambda>x xs. xs) ys)"
  by (cases ys) (simp_all add: llist_Case_def traj_LCons)

lemma llength_traj [simp]: "llength (traj xs) = llength xs"
  by (simp add: traj_def)

lemma lfilter_right_traj [simp]: "lfilter is_right (traj xs) = traj (lfilter is_right xs)"
  by (auto simp add: traj_def lfilter_lmap)

lemma ldeleteLeft_nat_traj [simp]: "ldeleteLeft_nat n (traj t) = traj (ldeleteLeft_nat n t)"
proof (induct n arbitrary: t)
  case 0 show ?case by simp
next
  case (Suc n)
  thus ?case
    apply auto
    apply (rule arg_cong) back
    apply (simp add: llist_Case_def)
    apply (cases "ldropWhile is_right t")
    by (simp_all add: traj_LCons del: ldropWhile_eq_LNil_iff)
qed

lemma [simp]: "traj (ltakeWhile is_right t) \<frown> traj (ldropWhile is_right t) = traj t"
  by (metis lappend_ltakeWhile_ldropWhile traj_lappend)

lemma [simp]: "lfilter is_left (ltakeWhile is_right t) = LNil"
  by (metis Not_is_left lfilter_ltakeWhile)

lemma "lfilter is_right (ltakeWhile is_right t) = ltakeWhile is_right t"
  by (metis Not_is_left lfilter_left_right lfilter_ltakeWhile)

lemma [simp]: "lfilter is_right (ltl (ldropWhile is_right t)) = lfilter is_right (ldropWhile is_right t)"
  apply (cases "\<exists>t'\<in>lset t. \<exists>a. t' = Inl a")
  apply (metis is_right.simps(2) lfilter_LCons lhd_ldropWhile llist.collapse ltl_simps(1))
  apply auto
  apply (subgoal_tac "ldropWhile is_right t = LNil")
  apply simp_all
  apply auto
  by (metis is_right.simps(1) obj_sumE)

lemma ldropWhile_LConsD [dest]: "ldropWhile P xs = LCons y ys \<Longrightarrow> \<exists>zs. xs = zs \<frown> LCons y ys \<and> \<not> P y \<and> (\<forall>z\<in>lset zs. P z) \<and> lfinite zs"
  by (metis lappend_ltakeWhile_ldropWhile ldropWhile_eq_LNil_iff lfinite_ltakeWhile lhd_LCons lhd_ldropWhile llist.distinct(1) lset_ltakeWhileD)

lemma ldropWhile_right_LCons [dest!]: "ldropWhile is_right t = LCons x xs \<Longrightarrow> \<exists>x'. ldropWhile is_right t = LCons (Inl x') xs"
  apply (drule ldropWhile_LConsD)
  apply (cases x)
  apply auto
  by (metis is_right.simps(2) ldropWhile_LCons ldropWhile_lappend)

lemma [simp]: "ldeleteLeft n (traj t) = traj (ldeleteLeft n t)"
  by (cases n) simp_all

lemma tshuffle_left_LCons: "xs \<in> LCons y ys \<sha> zs \<Longrightarrow> ldeleteLeft_nat 0 xs \<in> ys \<sha> zs"
  apply simp
  apply (auto simp add: tshuffle_words_def lefts_def rights_def)
  apply (subst lfilter_lappend_lfinite)
  apply (metis lappend_inf lappend_ltakeWhile_ldropWhile lefts_def_var lefts_ltake_right llist.distinct(1))
  apply simp
  apply (metis Not_is_left ltl_lfilter ltl_lmap ltl_simps(2))
  apply (subst lfilter_lappend_lfinite)
  apply (metis lappend_inf lappend_ltakeWhile_ldropWhile lefts_def_var lefts_ltake_right llist.discI)
  apply simp
  apply (subst lfilter_lappend_lfinite[symmetric])
  apply (metis lappend_inf lappend_ltakeWhile_ldropWhile lefts_def_var lefts_ltake_right llist.discI)
  apply (cases "ldropWhile is_right xs")
  apply simp
  apply simp
  by (metis lappend_ltakeWhile_ldropWhile)

lemma [simp]: "traj (lmap Inl xs) = lmap (\<lambda>x. Inl ()) xs"
  by (simp add: traj_def)

lemma [simp]: "ltakeWhile is_right (lmap (\<lambda>x. Inl ()) xs) = LNil"
  by (metis LNil_preserve is_right.simps(2) llist.exhaust llist.simps(19) ltakeWhile_LCons ltakeWhile_LNil)

lemma [simp]: "ldropWhile is_right (lmap (\<lambda>x. Inl ()) xs) = lmap (\<lambda>x. Inl ()) xs"
  by (cases xs) simp_all

lemma interleave_only_left_var: "llength t = llength xs \<Longrightarrow> xs \<triangleright> lmap (\<lambda>x. Inl ()) t \<triangleleft> zs = lmap Inl xs"
  by (metis (full_types) interleave_only_left lmap_const_llength)

lemma [simp]: "lfilter is_right (ltakeWhile is_right xs) = ltakeWhile is_right xs"
  by (metis Not_is_left lfilter_left_right lfilter_ltakeWhile)

lemma llength_enat_0 [dest!]: "llength xs = enat 0 \<Longrightarrow> xs = LNil"
  by (metis llength_eq_0 zero_enat_def)

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

lemma [simp]: "\<forall>x\<in>lset xs. is_right x \<Longrightarrow> lfinite xs \<Longrightarrow> ldropWhile is_right (xs \<frown> ys) = ldropWhile is_right ys"
  by (simp add: ldropWhile_lappend)

lemma lefts_LCons_lfinite_rights: "\<ll> xs = LCons y ys \<Longrightarrow> lfinite (ltakeWhile is_right xs)"
  by (metis lefts_ltake_right lfinite_ltakeWhile llist.distinct(1) ltakeWhile_all)

lemma lfilter_lefts_LCons_lfinite_rights: "lfilter is_left xs = LCons (Inl y) (lmap Inl ys) \<Longrightarrow> lfinite (ltakeWhile is_right xs)"
  by (metis lefts_LCons_lfinite_rights lefts_LConsl lefts_def_var lfilter_idem)

primrec ldelete_nat :: "nat \<Rightarrow> 'a llist \<Rightarrow> 'a llist" where
  "ldelete_nat 0 xs = llist_Case LNil (\<lambda>x' xs'. xs') xs"
| "ldelete_nat (Suc n) xs = llist_Case LNil (\<lambda>x' xs'. LCons x' (ldelete_nat n xs')) xs"

primrec ldelete :: "enat \<Rightarrow> 'a llist \<Rightarrow> 'a llist" where
  "ldelete (enat n) xs = ldelete_nat n xs"
| "ldelete \<infinity> xs = xs"

lemma ldropWhile_lfilter_rl_LNil: "ldropWhile is_right xs = LNil \<longleftrightarrow> lfilter is_left xs = LNil"
  by auto

lemma ldropWhile_lfilter_LConsD: "ldropWhile P xs = LCons y ys \<Longrightarrow> lfilter (Not \<circ> P) xs = LCons y (lfilter (Not \<circ> P) ys)"
  by auto

lemma [simp]: "\<not> lfinite (ltakeWhile is_right xs) \<Longrightarrow> lfilter is_left xs = LNil"
  by (metis diverge_lfilter_LNil lfinite_ltakeWhile not_is_right)

lemma lfilter_ldeleteLeft_nat: "lfilter is_left (ldeleteLeft_nat n xs) = ldelete_nat n (lfilter is_left xs)"
proof (induct n arbitrary: xs)
  case 0
  show ?case
    apply simp
    apply (cases "lfinite (ltakeWhile is_right xs)")
    apply (simp_all add: llist_Case_def)
    apply (metis Not_is_left ltl_def ltl_lfilter)
    apply (simp add: lappend_inf)
    by (metis lset_ltakeWhileD)
next
  case (Suc n)
  thus ?case
    apply simp
    apply (cases "lfinite (ltakeWhile is_right xs)")
    apply (subst lfilter_lappend_lfinite)
    apply assumption
    apply (simp add: llist_Case_def)
    apply (cases "ldropWhile is_right xs")
    apply (frule ldropWhile_lfilter_rl_LNil[THEN iffD1])
    apply simp
    apply (frule ldropWhile_lfilter_LConsD)
    apply (frule ldropWhile_LConsD)
    apply (simp only: Not_is_right[symmetric])
    apply simp
    apply (metis not_is_right)
    by (simp add: lappend_inf llist_Case_def)
qed

lemma lfilter_ldeleteLeft: "lfilter is_left (ldeleteLeft n xs) = ldelete n (lfilter is_left xs)"
  by (metis enat.exhaust ldelete.simps(1) ldelete.simps(2) ldeleteLeft.simps(1) ldeleteLeft.simps(2) lfilter_ldeleteLeft_nat)

lemma lfilter_lefts_LCons:
  assumes "lfilter is_left xs = LCons (Inl y) (lmap Inl ys)"
  shows "lfilter is_left (ltakeWhile is_right xs \<frown> ltl (ldropWhile is_right xs)) = lmap Inl ys"
  using assms
  apply -
  apply (frule lfilter_lefts_LCons_lfinite_rights)
  apply (subst lfilter_lappend_lfinite)
  apply assumption
  apply simp
  apply (drule lfilter_eq_LCons)
  apply (erule exE)
  by (metis Not_is_left ltl_simps(2))

lemma ldelete_nat_lappend [simp]: "llength xs = enat n \<Longrightarrow> ldelete_nat n (xs \<frown> LCons y ys) = xs \<frown> ys"
proof (induct n arbitrary: xs)
  case 0 thus ?case
    by - (drule llength_enat_0, auto simp add: llist_Case_def)
next
  case (Suc n)

  from Suc(2)
  have "\<exists>x' xs'. xs = LCons x' xs'"
    by (metis Zero_not_Suc enat.inject llength_LNil llist.exhaust zero_enat_def)
  then obtain x' xs' where xs_def: "xs = LCons x' xs'" by blast

  from Suc(2)
  have "llength xs' = enat n"
    by (simp add: xs_def eSuc_enat[symmetric])

  hence [simp]: "ldelete_nat n (xs' \<frown> LCons y ys) = xs' \<frown> ys"
    by (metis Suc.hyps)

  thus ?case
    by (auto simp add: llist_Case_def xs_def)
qed

lemma ldelete_llength_lappend: "\<exists>y. zs = xs \<frown> LCons y ys \<Longrightarrow> ldelete (llength xs) zs = xs \<frown> ys"
  by (cases "llength xs") auto

lemma lfilter_ltl: "(P (lhd xs) \<Longrightarrow> lfilter P xs = LCons (lhd xs) ys) \<Longrightarrow> (\<not> P (lhd xs) \<Longrightarrow> lfilter P xs = ys) \<Longrightarrow> lfilter P (ltl xs) = ys"
  by (simp add: ltl_def, cases xs, auto)

lemma [simp]: "lfilter is_left (ldropWhile is_right t) = lfilter is_left t"
proof -
  {
    assume case1: "lfinite (ltakeWhile is_right t)"

    have "lfilter is_left t = lfilter is_left (ltakeWhile is_right t \<frown> ldropWhile is_right t)"
      by (metis lappend_ltakeWhile_ldropWhile)
    also have "... = lfilter is_left (ldropWhile is_right t)"
      by (metis Not_is_left case1 lappend_code(1) lfilter_lappend_lfinite lfilter_ltakeWhile)
    finally have "lfilter is_left (ldropWhile is_right t) = lfilter is_left t"
      by auto
  }
  moreover
  {
    assume case2: "\<not> lfinite (ltakeWhile is_right t)"
    hence "ldropWhile is_right t = LNil"
      by (metis ldropWhile_eq_LNil_iff lfinite_ltakeWhile)
    moreover from case2 have "lfilter is_left t = LNil"
      by (metis calculation ldropWhile_lfilter_rl_LNil)
    ultimately have "lfilter is_left (ldropWhile is_right t) = lfilter is_left t"
      by auto
  }
  ultimately show ?thesis by blast
qed

lemma lefts_LCons_deleteLeft:
  assumes "\<ll> t = LCons x (xs \<frown> LCons y ys)"
  shows "\<ll> (ldeleteLeft (llength xs) (ltl (ldropWhile is_right t))) = xs \<frown> ys"
  using assms
  apply -
  apply (erule rev_mp)
  apply (simp add: lefts_def)
  apply (subst lmap_unl_Inl)
  apply simp
  apply (subst lmap_unl_Inl)
  apply simp
  apply (simp add: lfilter_ldeleteLeft)
  apply (cases "llength xs")
  apply (subgoal_tac "lfinite xs")
  apply (rule impI)
  apply (subst lmap_lappend_distrib)
  apply (subgoal_tac "llength xs = llength (lmap Inl xs)")
  apply (rotate_tac 3)
  apply (erule ssubst)
  apply (rule ldelete_llength_lappend)
  apply (rule_tac x = "Inl y" in exI)
  defer
  apply force
  apply (metis enat.distinct(1) not_lfinite_llength)
  apply (subgoal_tac "\<not> lfinite xs")
  apply (erule ssubst)
  apply (simp add: lappend_inf)
  apply (metis Not_is_left ltl_lfilter ltl_simps(2))
  apply (metis llength_eq_infty_conv_lfinite)
  apply (rule lfilter_ltl)
  apply simp
  apply (intro conjI)
  apply (metis Not_is_left lhd_LCons lhd_lfilter)
  apply (metis llist.simps(19) lmap_lappend_distrib)
  apply (subgoal_tac "is_left (lhd (ldropWhile is_right t))")
  apply metis
  by (metis Not_is_left is_left.simps(1) lhd_LCons lhd_lfilter)

lemma [simp]: "\<down> (llength xs) xs = LNil"
  by (metis ldrop_eq_LNil order_refl)

lemma lfilter_ldropn: "lfilter P (ldropn n xs) = \<down> (llength (lfilter P (\<up> (enat n) xs))) (lfilter P xs)"
proof (induct n arbitrary: xs)
  case 0
  show ?case
    by (simp add: enat_0)
next
  case (Suc n)
  thus ?case
    by (cases xs) (simp_all add: eSuc_enat[symmetric])
qed

lemma lfilter_ldrop: "lfilter P (\<down> n xs) = \<down> (llength (lfilter P (\<up> n xs))) (lfilter P xs)"
  by (cases n) (simp_all add: lfilter_ldropn)

lemma [simp]: "\<rr> (ltl (ldropWhile is_right t)) = \<rr> (ldropWhile is_right t)"
  by (simp add: rights_def)

lemma mumble_LCons: "ys \<in> mumble xs \<Longrightarrow> LCons x ys \<in> mumble (LCons x xs)"
  apply (subst LCons_lappend_LNil[where ys = xs])
  apply (subst LCons_lappend_LNil[where ys = ys])
  apply (rule mumble_lappend)
  apply (rule mumble.self)
  by assumption

lemma lset_lfilter_var: "x \<in> lset (lfilter P xs) \<Longrightarrow> x \<in> lset xs"
  by (metis (lifting) lset_lfilter mem_Collect_eq)

lemma llength_lefts_lappend [simp]: "lfinite xs \<Longrightarrow> llength (\<ll> (xs \<frown> ys)) = llength (\<ll> xs) + llength (\<ll> ys)"
  by (simp add: lefts_def)

lemma llength_rights_lappend [simp]: "lfinite xs \<Longrightarrow> llength (\<rr> (xs \<frown> ys)) = llength (\<rr> xs) + llength (\<rr> ys)"
  by (simp add: rights_def)

lemma [simp]: "lfilter is_right (ldeleteLeft_nat n xs) = lfilter is_right xs"
proof (induct n arbitrary: xs)
  case 0 show ?case
    apply (auto simp add: rights_def)
    apply (cases "llength (ltakeWhile is_right xs)")
    apply (subst lappend_ltakeWhile_ldropWhile[symmetric, of xs is_right]) back back
    apply (subst lfilter_lappend_lfinite)
    apply (metis lfinite_conv_llength_enat)
    apply (subst lfilter_lappend_lfinite)
    apply (metis lfinite_conv_llength_enat)
    apply simp
    apply simp
    by (metis enat_ord_code(3) ldropWhile_eq_ldrop ldropWhile_lfilter_rl_LNil ldrop_eq_LNil lfilter_left_right llength_ltakeWhile_eq_infinity)
next
  case (Suc n)
  thus ?case
    apply simp
    apply (cases "llength (ltakeWhile is_right xs)")
    apply (subst lappend_ltakeWhile_ldropWhile[symmetric, of xs is_right]) back back
    apply (subst lfilter_lappend_lfinite)
    apply (metis lfinite_conv_llength_enat)
    apply (subst lfilter_lappend_lfinite)
    apply (metis lfinite_conv_llength_enat)
    apply (rule arg_cong) back
    apply (simp add: llist_Case_def)
    apply (cases "ldropWhile is_right xs")
    apply simp
    apply simp
    apply (metis not_is_right)
    apply simp
    by (metis enat_ord_code(3) ldropWhile_eq_ldrop ldropWhile_lfilter_rl_LNil ldrop_eq_LNil lfilter_left_right llength_ltakeWhile_eq_infinity)
qed

lemma [simp]: "\<rr> (ldeleteLeft_nat n xs) = \<rr> xs"
  by (simp add: rights_def)

lemma eSuc_move: "y \<noteq> 0 \<Longrightarrow> eSuc x = y \<longleftrightarrow> x = y - 1"
  apply default
  apply auto
  by (metis co.enat.collapse epred_conv_minus)

lemma llength_ldelete_nat: "enat n < llength xs \<Longrightarrow> llength (ldelete_nat n xs) = llength xs - 1"
proof (induct n arbitrary: xs)
  case 0 thus ?case
    by (cases xs) (simp_all add: llist_Case_def)
next
  case (Suc n) thus ?case
    apply simp
    apply (cases xs)
    apply simp
    apply (simp add: llist_Case_def)
    by (metis Suc_ile_eq eSuc_move not_iless0)
qed

lemma lmap_LConsl: "lmap \<langle>id,id\<rangle> (LCons (Inl x) xs) = LCons x (lmap \<langle>id,id\<rangle> xs)"
  by auto

lemma [simp]: "llength (\<ll> (ldropWhile is_right t)) = llength (\<ll> t)"
  by (auto simp add: lefts_def)

lemma [simp]: "lfilter is_right (linsertLeft_nat n x xs) = lfilter is_right xs"
proof (induct n arbitrary: xs)
  case 0 thus ?case
    apply auto
    apply (cases "lfinite (ltakeWhile is_right xs)")
    apply (subst lfilter_lappend_lfinite)
    apply assumption
    apply simp
    apply (subst lappend_ltakeWhile_ldropWhile[symmetric, of xs is_right]) back back
    apply (subst lfilter_lappend_lfinite)
    apply assumption
    apply simp
    apply (simp add: lappend_inf)
    by (metis diverge_lfilter_LNil lappend_inf lappend_ltakeWhile_ldropWhile lfilter_left_right lfinite_ltakeWhile not_is_right)
next
  case (Suc n)
  thus ?case
    apply simp
    apply (cases "lfinite (ltakeWhile is_right xs)")
    apply (subst lappend_ltakeWhile_ldropWhile[symmetric, of xs is_right]) back back
    apply (subst lfilter_lappend_lfinite) back
    apply simp_all
    apply (rule arg_cong) back
    apply (simp add: llist_Case_def)
    apply (cases "ldropWhile is_right xs")
    apply simp
    apply simp
    apply (metis not_is_right)
    apply (simp add: lappend_inf)
    by (metis diverge_lfilter_LNil lappend_inf lappend_ltakeWhile_ldropWhile lfilter_left_right lfinite_ltakeWhile not_is_right)
qed

lemma [simp]: "lfilter is_left (ltl (ldropWhile is_right xs)) = ltl (lfilter is_left (ldropWhile is_right xs))"
proof -
  have "lfilter is_left (ltl (ldropWhile is_right xs)) = ltl (lfilter is_left xs)"
    by (metis Not_is_left ltl_lfilter)
  also have "... = ltl (lfilter is_left (ldropWhile is_right xs))"
    by simp
  finally show ?thesis .
qed

lemma llength_ltl_not_LNil: "xs \<noteq> LNil \<Longrightarrow> llength (ltl xs) = llength xs - 1"
  by (metis epred_conv_minus epred_llength)

lemma eSuc_move2: "y \<noteq> 0 \<Longrightarrow> eSuc x < y \<longleftrightarrow> x < y - 1"
  apply default
  apply (metis co.enat.exhaust eSuc_minus_1 eSuc_mono)
  by (metis eSuc_mono eSuc_move)

lemma eSuc_minus_1_var: "n \<noteq> 0 \<Longrightarrow> eSuc (n - 1) = n"
  by (metis eSuc_move)

lemma llength_linsertLeft_nat:
  "enat n < llength (lfilter is_left xs) \<Longrightarrow> llength (lfilter is_left (linsertLeft_nat n x xs)) = eSuc (llength (lfilter is_left xs))"
proof (induct n arbitrary: xs)
  case 0
  thus ?case
    by (cases "lfinite (ltakeWhile is_right xs)") simp_all
next
  case (Suc n)

  from Suc(2)
  have "enat n < llength (lfilter is_left (ltl (ldropWhile is_right xs)))"
    apply simp
    apply (subst llength_ltl_not_LNil)
    apply (metis llength_LNil not_iless0)
    apply (simp add: eSuc_enat[symmetric])
    apply (subst eSuc_move2[symmetric])
    apply (metis not_iless0)
    by assumption
  hence "llength (lfilter is_left (linsertLeft_nat n x (ltl (ldropWhile is_right xs)))) = eSuc (llength (lfilter is_left (ltl (ldropWhile is_right xs))))"
    by (metis Suc.hyps)

  from this and Suc(2)
  show ?case
    apply simp
    apply (cases "lfinite (ltakeWhile is_right xs)")
    apply (simp add: llist_Case_def)
    apply (cases "ldropWhile is_right xs")
    apply simp
    apply (drule ldropWhile_right_LCons)
    apply (erule exE)
    apply simp
    apply (subst llength_ltl_not_LNil)
    apply (metis llength_LNil not_iless0)
    apply (subst eSuc_minus_1_var)
    apply (metis not_iless0)
    apply (rule refl)
    by (simp add: lappend_inf)
qed

lemma [simp]: "\<rr> (linsertLeft_nat n x xs) = \<rr> xs"
  by (simp add: rights_def)

lemma [simp]: "\<rr> (linsertLeft n x xs) = \<rr> xs"
  by (cases n) simp_all

lemma [simp]: "lfilter is_left (traj xs) = traj (lfilter is_left xs)"
  by (auto simp add: traj_def lfilter_lmap)

lemma [simp]: "llength (lfilter is_left (traj xs)) = llength (lfilter is_left xs)"
  by simp

lemma lfilter_all [intro]: "(\<forall>x\<in>lset xs. P x) \<Longrightarrow> lfilter P xs = xs"
proof -
  assume "\<forall>x\<in>lset xs. P x"
  hence "lfilter P xs = lfilter (\<lambda>x. True) xs"
    by (auto intro: lfilter_cong)
  also have "... = xs"
    by (metis lfilter_K_True)
  finally show ?thesis .
qed

lemma [simp]: "lfilter P (ltakeWhile P xs) = ltakeWhile P xs"
  by (auto dest: lset_ltakeWhileD)

lemma [simp]: "ltakeWhile P xs \<frown> lfilter P (ldropWhile P xs) = lfilter P xs"
  apply (subgoal_tac "ltakeWhile P xs = lfilter P (ltakeWhile P xs)")
  apply (erule ssubst)
  apply (cases "lfinite (ltakeWhile P xs)")
  apply (subst lfilter_lappend_lfinite[symmetric])
  apply assumption
  apply simp
  apply (metis (hide_lams, full_types) lappend_LNil2 lappend_ltakeWhile_ldropWhile ldropWhile_eq_LNil_iff lfilter_LNil lfinite_ltakeWhile)
  by simp

lemma mumble_in_left:
  assumes "t \<in> (xs \<frown> LCons (\<sigma>, \<sigma>'') ys) \<sha> zs"
  shows "lmap \<langle>id,id\<rangle> (xs \<frown> LCons (\<sigma>, \<sigma>'') ys \<triangleright> traj t \<triangleleft> zs) \<in> mumble (lmap \<langle>id,id\<rangle> (xs \<frown> LCons (\<sigma>,\<sigma>') (LCons (\<sigma>',\<sigma>'') ys) \<triangleright> linsertLeft (llength xs) () (traj t) \<triangleleft> zs))"
proof (cases "llength xs")
  assume "llength xs = \<infinity>"
  from this and assms show ?thesis
    by (auto intro: sumlist_cases[of t] simp add: traj_def interleave_left interleave_right)
next
  let ?TR = "ltakeWhile is_right"
  let ?DR = "ldropWhile is_right"

  fix n
  assume "llength xs = enat n"
  moreover hence "lmap \<langle>id,id\<rangle> (xs \<frown> LCons (\<sigma>, \<sigma>'') ys \<triangleright> traj t \<triangleleft> zs) \<in> mumble (lmap \<langle>id,id\<rangle> (xs \<frown> LCons (\<sigma>,\<sigma>') (LCons (\<sigma>',\<sigma>'') ys) \<triangleright> linsertLeft_nat n () (traj t) \<triangleleft> zs))"
    using assms
  proof (induct n arbitrary: xs t zs)
    case 0 note zero = this
    {
      assume zs_not_LNil: "zs \<noteq> LNil"

      from zero have [simp]: "xs = LNil"
        by (metis llength_eq_0 zero_enat_def)
      hence t_shuffle: "t \<in> LCons (\<sigma>, \<sigma>'') ys \<sha> zs"
        by (metis zero(2) lappend_code(1))
      from t_shuffle have t_not_LNil: "t \<noteq> LNil"
        by (auto simp add: tshuffle_words_def)
      from t_shuffle and zs_not_LNil have ltl_t_not_LNil: "ltl t \<noteq> LNil"
        apply (auto simp add: tshuffle_words_def rights_def lefts_def)
        by (metis (lifting) LNil_preserve lefts_def_var lefts_ltake_right lfilter_LCons lfilter_LNil llist.collapse llist.distinct(1) ltakeWhile_LCons ltakeWhile_eq_LNil_iff t_not_LNil)

      from t_shuffle
      have "?DR t = LCons (Inl (\<sigma>,\<sigma>'')) (ltl (?DR t))"
        by (auto dest: lfilter_eq_LCons simp add: tshuffle_words_def lefts_def lmap_unl_Inl)

      hence traj_DR: "?DR (traj t) = LCons (Inl ()) (ltl (ldropWhile is_right (traj t)))"
        by - (drule arg_cong[where f = traj], simp)

      have [intro]: "lfinite (traj (ltakeWhile is_right t))"
        by (metis ldropWhile_eq_LNil_iff lfinite_ltakeWhile llist.distinct(1) ltakeWhile_right_traj traj_DR)

      have "lmap \<langle>id,id\<rangle> (LCons (\<sigma>, \<sigma>'') ys \<triangleright> traj t \<triangleleft> zs) = lmap \<langle>id,id\<rangle> (LCons (\<sigma>,\<sigma>'') ys \<triangleright> ?TR (traj t) \<frown> ?DR (traj t) \<triangleleft> zs)"
        by (metis lappend_ltakeWhile_ldropWhile)
      also have "... = lmap \<langle>id,id\<rangle> ((LNil \<triangleright> ?TR (traj t) \<triangleleft> \<up> (llength (\<rr> (?TR (traj t)))) zs) \<frown>
                                    (LCons (\<sigma>,\<sigma>'') ys \<triangleright> ?DR (traj t) \<triangleleft> \<down> (llength (\<rr> (?TR (traj t)))) zs))"
        apply (subst intro_traj)
        apply (subst traj_lappend)
        apply (subst interleave_append[OF t_shuffle])
        apply (metis intro_traj lappend_ltakeWhile_ldropWhile traj_interleave)
        by simp
      also have "... = lmap \<langle>id,id\<rangle> ((LNil \<triangleright> ?TR (traj t) \<triangleleft> \<up> (llength (\<rr> (?TR (traj t)))) zs) \<frown>
                                     LCons (Inl (\<sigma>,\<sigma>'')) (ys \<triangleright> ltl (?DR (traj t)) \<triangleleft> \<down> (llength (\<rr> (?TR (traj t)))) zs))"
        apply (subst interleave_ldropWhile)
        apply (subst shuffle_lset[OF t_shuffle])
        by (simp_all add: interleave_left)
      also have "... = lmap \<langle>id,id\<rangle> (LNil \<triangleright> ?TR (traj t) \<triangleleft> \<up> (llength (\<rr> (?TR (traj t)))) zs) \<frown>
                       LCons (\<sigma>,\<sigma>'') (lmap \<langle>id,id\<rangle> (ys \<triangleright> ltl (?DR (traj t)) \<triangleleft> \<down> (llength (\<rr> (?TR (traj t)))) zs))"
        by (simp add: lmap_lappend_distrib)
      also have "... \<in> mumble (lmap \<langle>id,id\<rangle> (LCons (\<sigma>, \<sigma>') (LCons (\<sigma>', \<sigma>'') ys) \<triangleright> linsertLeft_nat 0 () (traj t) \<triangleleft> zs))"
        apply (rule mumble[where \<sigma>' = \<sigma>'])
        apply (simp only: linsertLeft_nat.simps)
        apply (subst interleave_append_llength)
        prefer 3
        apply (subst traj_DR) back
        apply (simp only: lefts_ltake_right llength_LNil ltake_0 ldrop_0 lmap_lappend_distrib interleave_left lhd_LCons lmap_LConsl ltl_simps)
        apply (rule mumble.self)
        apply simp
        using t_shuffle
        apply (auto simp add: tshuffle_words_def)
        apply (subst llength_lefts_lappend)
        apply auto
        apply (subst llength_rights_lappend)
        apply auto
        by (metis lappend_ltakeWhile_ldropWhile lefts_LCons_lfinite_rights llength_lappend rights_append)
      finally have ?case
          by auto
    }
    moreover
    {
      assume zs_LNil: "zs = LNil"
      from zero have [simp]: "xs = LNil"
        by (metis llength_eq_0 zero_enat_def)
      from zs_LNil and zero have ?case
        apply (auto simp add: interleave_left interleave_only_left)
        apply (rule mumble.mumble[where ys = LNil and \<sigma>' = \<sigma>', simplified])
        by (rule mumble.self)
    }
    ultimately show ?case
      by (cases zs) simp_all
  next
    case (Suc n)

    from Suc(2) have xs_lfinite: "lfinite xs"
      by (metis lfinite_conv_llength_enat)

    from Suc obtain x' and xs' where xs_def: "xs = LCons x' xs'"
      by (cases xs) (auto simp add: eSuc_enat[symmetric])
    hence xs'_len: "llength xs' = enat n"
      by (metis Suc.prems(1) co.enat.inject eSuc_enat llength_LCons)

    from Suc(3)
    have prem_lhd [simp]: "lhd (ldropWhile is_right t) = Inl x'"
      apply (auto simp add: tshuffle_words_def lefts_def xs_def)
      apply (erule rev_mp)
      apply (subst lmap_unl_Inl)
      apply (metis (lifting) Coinductive_List.lset_lfilter mem_Collect_eq)
      by (metis Not_is_left lhd_LCons lhd_lfilter lhd_lmap llist.distinct(1))

    from Suc(3)
    have [simp]: "lhd (ldropWhile is_right (traj t)) = Inl ()"
      apply (auto simp add: tshuffle_words_def lefts_def xs_def)
      apply (erule rev_mp)
      apply (subst lmap_unl_Inl)       
      apply (metis (lifting) Coinductive_List.lset_lfilter mem_Collect_eq)
      apply simp
      by (metis LNil_eq_llist_map ldropWhile_lfilter_rl_LNil ldropWhile_right_traj ldropWhile_rights_not_LNil lefts_def_var lhd_LCons llist.distinct(1) traj_lfilter_lefts_var)

    from Suc(3)
    have "ldropWhile is_right (traj t) \<noteq> LNil"
      apply (auto simp add: tshuffle_words_def xs_def traj_not_LNil)
      apply (rule_tac x = "Inl x'" in bexI)
      apply simp
      apply (rule lset_lfilter_var[where P = is_left])
      apply (erule rev_mp)
      apply (simp add: lefts_def)
      apply (subst lmap_unl_Inl)
      apply (metis (mono_tags) Coinductive_List.lset_lfilter mem_Collect_eq)
      apply auto
      by (metis lset_intros(1) lset_lfilter_var)

    from Suc(3)
    have ind_shuffle: "ltl (ldropWhile is_right t) \<in> (xs' \<frown> LCons (\<sigma>, \<sigma>'') ys) \<sha> \<down> (llength (\<rr> (?TR (traj t)))) zs"
      apply (auto simp add: lefts_def tshuffle_words_def xs_def)
      apply (metis ltl_lmap ltl_simps(2))
      apply (simp add: lefts_def rights_def ldropWhile_def)
      apply (rule arg_cong) back
      apply (subst lfilter_ldrop)
      apply (rule arg_cong) back
      by (metis diverge_lfilter_LNil lappend_ltakeWhile_ldropWhile lfilter_left_right lset_ltakeWhileD ltake_all ltake_lappend1 not_is_left order_refl)

    from Suc(1)[OF xs'_len ind_shuffle]
    have ih: "lmap \<langle>id,id\<rangle> (xs' \<frown> LCons (\<sigma>, \<sigma>'') ys \<triangleright> ltl (?DR (traj t)) \<triangleleft> \<down> (llength (\<rr> (?TR (traj t)))) zs)
             \<in> mumble (lmap \<langle>id,id\<rangle> (xs' \<frown> LCons (\<sigma>, \<sigma>') (LCons (\<sigma>', \<sigma>'') ys) \<triangleright> linsertLeft_nat n () (ltl (?DR (traj t))) \<triangleleft> \<down> (llength (\<rr> (?TR (traj t)))) zs))"
      by simp

    hence ih_var: "ltakeWhile is_right (traj t) = LNil \<Longrightarrow>
      lmap \<langle>id,id\<rangle> (xs' \<frown> LCons (\<sigma>, \<sigma>'') ys \<triangleright> ltl (?DR (traj t)) \<triangleleft> zs)
      \<in> mumble (lmap \<langle>id,id\<rangle> (xs' \<frown> LCons (\<sigma>, \<sigma>') (LCons (\<sigma>', \<sigma>'') ys) \<triangleright> linsertLeft_nat n () (ltl (?DR (traj t))) \<triangleleft> zs))"
      by (auto simp del: ltakeWhile_eq_LNil_iff)

    have "lmap \<langle>id,id\<rangle> (xs \<frown> LCons (\<sigma>,\<sigma>'') ys \<triangleright> traj t \<triangleleft> zs) = lmap \<langle>id,id\<rangle> (xs \<frown> LCons (\<sigma>,\<sigma>'') ys \<triangleright> ?TR (traj t) \<frown> ?DR (traj t) \<triangleleft> zs)"
      by (metis lappend_ltakeWhile_ldropWhile)
    also have "... = lmap \<langle>id,id\<rangle> ((LNil \<triangleright> ?TR (traj t) \<triangleleft> \<up> (llength (\<rr> (?TR (traj t)))) zs) \<frown>
                                  (xs \<frown> LCons (\<sigma>, \<sigma>'') ys \<triangleright> ?DR (traj t) \<triangleleft> \<down> (llength (\<rr> (?TR (traj t)))) zs))"
      by (subst interleave_append[OF Suc(3)]) simp_all
    also have "... = lmap \<langle>id,id\<rangle> ((LNil \<triangleright> ?TR (traj t) \<triangleleft> \<up> (llength (\<rr> (?TR (traj t)))) zs) \<frown>
                                  (xs \<frown> LCons (\<sigma>, \<sigma>'') ys \<triangleright> LCons (Inl ()) (ltl (?DR (traj t))) \<triangleleft> \<down> (llength (\<rr> (?TR (traj t)))) zs))"
        apply (subst interleave_ldropWhile)
        apply (subst shuffle_lset[OF Suc(3)])
        apply auto
        apply (rule_tac x = "Inl (\<sigma>,\<sigma>'')" in bexI)
        apply auto
        apply (subgoal_tac "lfinite xs")
        apply (metis imageI in_lset_lappend_iff lset_intros(1))
        by (metis xs_lfinite)
    also have "... = lmap \<langle>id,id\<rangle> ((LNil \<triangleright> ?TR (traj t) \<triangleleft> \<up> (llength (\<rr> (?TR (traj t)))) zs) \<frown>
                                  LCons (Inl x') (xs' \<frown> LCons (\<sigma>, \<sigma>'') ys \<triangleright> ltl (?DR (traj t)) \<triangleleft> \<down> (llength (\<rr> (?TR (traj t)))) zs))"
      by (metis (hide_lams, no_types) calculation interleave_left lappend_code(2) lhd_LCons ltl_simps(2) xs_def)
    also have "... = lmap \<langle>id,id\<rangle> (LNil \<triangleright> ?TR (traj t) \<triangleleft> \<up> (llength (\<rr> (?TR (traj t)))) zs) \<frown>
                     LCons x' (lmap \<langle>id,id\<rangle> (xs' \<frown> LCons (\<sigma>, \<sigma>'') ys \<triangleright> ltl (?DR (traj t)) \<triangleleft> \<down> (llength (\<rr> (?TR (traj t)))) zs))"
      by (simp add: lmap_lappend_distrib)
    also have "... \<in> mumble (lmap \<langle>id,id\<rangle> (xs \<frown> LCons (\<sigma>, \<sigma>') (LCons (\<sigma>', \<sigma>'') ys) \<triangleright> linsertLeft_nat (Suc n) () (traj t) \<triangleleft> zs))" (is ?goal)
    proof (cases "ltakeWhile is_right (traj t) = LNil")
      case True
      moreover have "traj (?DR t) = LCons (Inl ()) (traj (ltl (?DR t)))"
        by (metis (full_types) `ldropWhile is_right (traj t) \<noteq> LNil` ldropWhile_right_traj ldropWhile_rights_not_LNil ltl_traj)
      ultimately show ?goal
        by (auto intro!: ih_var[simplified] mumble_LCons simp add: xs_def llist_Case_def interleave_left)
    next
      case False
      from Suc(3)
      have "?DR t = LCons (Inl x') (ltl (?DR t))"
        by (auto dest: lfilter_eq_LCons simp add: tshuffle_words_def lefts_def lmap_unl_Inl xs_def)

      hence traj_DR: "?DR (traj t) = LCons (Inl ()) (ltl (ldropWhile is_right (traj t)))"
        by - (drule arg_cong[where f = traj], simp)

      hence DR_traj: "traj (?DR t) = LCons (Inl ()) (ltl (ldropWhile is_right (traj t)))"
        by simp

      from Suc(3)
      have [simp]: "lfilter is_left (ltl (ldropWhile is_right t)) = lmap Inl (xs' \<frown> LCons (\<sigma>, \<sigma>'') ys)"
        by (auto simp add: tshuffle_words_def lefts_def lmap_unl_Inl xs_def)

      show ?goal
        apply (simp only: linsertLeft_nat.simps)
        apply (subst interleave_append_llength)
        prefer 3
        apply (subst lmap_lappend_distrib)
        apply (rule mumble_lappend)
        apply simp
        apply (subst traj_DR) back
        apply (simp add: llist_Case_def xs_def interleave_left)
        apply (rule mumble_LCons)
        apply (rule ih[simplified])
        using Suc(3)
        apply (auto simp add: tshuffle_words_def traj_DR llist_Case_def)
        apply (subst llength_lefts_lappend)
        apply (simp add: traj_def)
        apply (metis lappend_not_LNil_iff lefts_LCons_lfinite_rights neq_LNil_conv)
        apply (subst DR_traj)
        apply auto
        apply (subst iadd_Suc_right)
        apply (rule arg_cong) back
        apply (simp add: lefts_def lmap_unl_Inl)
        apply (subst llength_linsertLeft_nat)
        apply (subst xs'_len[symmetric])
        prefer 2
        apply (subst iadd_Suc_right)
        apply (rule arg_cong) back
        apply (simp add: xs_def iadd_Suc_right eSuc_plus)
        apply (simp add: xs_def)
        apply (metis xs'_len)
        apply (subst DR_traj)
        apply simp
        apply (subst llength_rights_lappend)
        apply (simp add: traj_def)
        apply (metis lappend_not_LNil_iff lefts_LCons_lfinite_rights neq_LNil_conv)
        apply simp
        by (metis lappend_ltakeWhile_ldropWhile lappend_not_LNil_iff lefts_LCons_lfinite_rights llength_lappend llist.sel_exhaust rights_append)
    qed
    finally show ?case
      by simp
  qed
  ultimately show ?thesis
    by simp
qed

lemma tshuffle_mumble: "\<Union>{lmap \<langle>id,id\<rangle> ` (xs' \<sha> ys)|xs'. xs' \<in> mumble xs} \<subseteq> (lmap \<langle>id,id\<rangle> ` (xs \<sha> ys))\<^sup>\<dagger>"
proof -
  {
  fix xs' zs'

  assume "xs' \<in> mumble xs" and "zs' \<in> xs' \<sha> ys"

  hence "\<exists>zs\<in>xs \<sha> ys. lmap \<langle>id,id\<rangle> zs' \<in> mumble (lmap \<langle>id,id\<rangle> zs)"
  proof (induct xs' arbitrary: zs' rule: mumble.induct)
    case (self zs')
    thus ?case
      by (rule_tac x = zs' in bexI, auto)
  next
    case (mumble ws \<sigma> \<sigma>' \<sigma>'' vs zs')

    hence zs'_interleave: "zs' = (ws \<frown> LCons (\<sigma>, \<sigma>'') vs) \<triangleright> traj zs' \<triangleleft> ys"
      by (simp add: tshuffle_words_def) (metis reinterleave)

    from mumble(3)
    have "(ws \<frown> LCons (\<sigma>,\<sigma>') (LCons (\<sigma>',\<sigma>'') vs) \<triangleright> linsertLeft (llength ws) () (traj zs') \<triangleleft> ys) \<in> (ws \<frown> LCons (\<sigma>, \<sigma>') (LCons (\<sigma>', \<sigma>'') vs)) \<sha> ys"
      apply (auto simp add: tshuffle_words_def)
      apply (subgoal_tac "linsertLeft (llength ws) () (traj zs') = traj (linsertLeft (llength ws) () (traj zs'))")
      apply (rotate_tac 1)
      apply (erule ssubst)
      apply (subst lefts_interleave_llength)
      apply simp_all
      defer
      apply (subgoal_tac "linsertLeft (llength ws) () (traj zs') = traj (linsertLeft (llength ws) () (traj zs'))")
      apply (rotate_tac 1)
      apply (erule ssubst)
      apply (subst rights_interleave_llength)
      apply simp_all
      apply (simp add: lefts_def lmap_unl_Inl)
      apply (cases "llength ws")
      apply simp_all
      apply (subst llength_linsertLeft_nat)
      by (simp_all add: iadd_Suc_right)

    from this and mumble(2) obtain zs where "zs \<in> xs \<sha> ys"
    and "lmap \<langle>id,id\<rangle> (ws \<frown> LCons (\<sigma>,\<sigma>') (LCons (\<sigma>',\<sigma>'') vs) \<triangleright> linsertLeft (llength ws) () (traj zs') \<triangleleft> ys) \<in> mumble (lmap \<langle>id,id\<rangle> zs)"
      by blast

    moreover have "lmap \<langle>id,id\<rangle> zs' \<in> mumble (lmap \<langle>id,id\<rangle> (ws \<frown> LCons (\<sigma>,\<sigma>') (LCons (\<sigma>',\<sigma>'') vs) \<triangleright> linsertLeft (llength ws) () (traj zs') \<triangleleft> ys))"
      by (subst zs'_interleave) (metis (full_types) mumble.prems mumble_in_left)
 
    ultimately show ?case
      by (metis (hide_lams, no_types) mumble_trans)
  qed
  }
  thus ?thesis
    by (auto simp add: Mumble_def) (metis (full_types) imageI)
qed

lemma shuffle_mumble1: "X\<^sup>\<dagger> \<parallel> Y \<subseteq> (X \<parallel> Y)\<^sup>\<dagger>"
proof -
  have "X\<^sup>\<dagger> \<parallel> Y = \<Union>(mumble ` X) \<parallel> Y"
    by (rule arg_cong, auto simp add: Mumble_def image_def)
  also have "... = \<Union>{mumble xs \<parallel> Y|xs. xs \<in> X}"
    by (subst trans[OF shuffle_comm shuffle_inf_dist], subst shuffle_comm, auto)
  also have "... = \<Union>{\<Union>{lmap \<langle>id,id\<rangle> ` (xs' \<sha> ys) |xs' ys. xs' \<in> mumble xs \<and> ys \<in> Y}|xs. xs \<in> X}"
    by (simp add: shuffle_def)
  also have "... = \<Union>{\<Union>{lmap \<langle>id,id\<rangle> ` (xs' \<sha> ys) |xs'. xs' \<in> mumble xs}|xs ys. xs \<in> X \<and> ys \<in> Y}"
    by blast
  also have "... \<subseteq> \<Union>{(lmap \<langle>id,id\<rangle> ` (xs \<sha> ys))\<^sup>\<dagger>|xs ys. xs \<in> X \<and> ys \<in> Y}"
    by (insert tshuffle_mumble) blast
  also have "... = \<Union>{\<Union>zs\<in>xs \<sha> ys. mumble (lmap \<langle>id,id\<rangle> zs)|xs ys. xs \<in> X \<and> ys \<in> Y}"
    by (auto simp add: Mumble_def)
  also have "... = (X \<parallel> Y)\<^sup>\<dagger>"
    by (simp add: shuffle_def Mumble_def) blast
  finally show ?thesis .
qed

lemma mumble_LNil_lfinite: "ys \<in> mumble LNil \<Longrightarrow> lfinite ys"
  by (induct ys rule: mumble.induct) auto

lemma mumble_member: "xs \<in> X \<Longrightarrow> mumble xs \<subseteq> X\<^sup>\<dagger>"
  by (auto simp add: Mumble_def)

lemma set_comp_fun_sub1: "(\<And>x. x \<in> X \<Longrightarrow> f x \<subseteq> g x) \<Longrightarrow> \<Union>{f x |x. x \<in> X} \<subseteq> \<Union>{g x |x. x \<in> X}"
  by auto

lemma Mumble_shuffle_left [simp]: "(X\<^sup>\<dagger> \<parallel> Y)\<^sup>\<dagger> = (X \<parallel> Y)\<^sup>\<dagger>"
  apply (rule antisym)
  apply (metis (full_types) Mumble_idem Mumble_iso shuffle_comm shuffle_mumble1)
  by (metis Mumble_ext Mumble_iso par.mult_isor)

lemma Mumble_shuffle_right [simp]: "(X \<parallel> Y\<^sup>\<dagger>)\<^sup>\<dagger> = (X \<parallel> Y)\<^sup>\<dagger>"
  by (metis Mumble_shuffle_left shuffle_comm)

lemma mumble_infinite2: "xs \<in> mumble ys \<Longrightarrow> \<not> lfinite xs \<Longrightarrow> \<not> lfinite ys"
  by (induct xs rule: mumble.induct) auto

lemma mumble_preserves_finiteness [dest]: "xs \<in> mumble ys \<Longrightarrow> lfinite xs \<longleftrightarrow> lfinite ys"
  by (metis mumble_infinite mumble_infinite2)

lemma Mumble_l_prod [simp]: "(X\<^sup>\<dagger> \<cdot> Y\<^sup>\<dagger>)\<^sup>\<dagger> = (X \<cdot> Y)\<^sup>\<dagger>"
proof (rule antisym)
  show "(X\<^sup>\<dagger> \<cdot> Y\<^sup>\<dagger>)\<^sup>\<dagger> \<subseteq> (X \<cdot> Y)\<^sup>\<dagger>"
    apply (simp add: l_prod_def)
    apply (intro conjI)
    apply (rule le_supI1)
    defer
    apply (rule le_supI2)
    apply (auto simp add: Mumble_def)
    apply (rename_tac z xs' ys' xs ys)
    apply (rule_tac x = "mumble (xs \<frown> ys)" in exI)
    apply (intro conjI)
    apply (rule_tac x = "xs \<frown> ys" in exI)
    apply simp
    apply (rule_tac x = "xs" in exI)
    apply (rule_tac x = "ys" in exI)
    apply simp
    apply (metis mumble_infinite)
    apply (metis mumble_lappend mumble_trans)
    apply (rename_tac xs xs' xs'')
    apply (rule_tac x = "mumble xs''" in exI)
    apply (intro conjI)
    apply (rule_tac x = "xs''" in exI)
    apply auto
    by (metis mumble_trans)
  show "(X \<cdot> Y)\<^sup>\<dagger> \<subseteq> (X\<^sup>\<dagger> \<cdot> Y\<^sup>\<dagger>)\<^sup>\<dagger>"
    by (metis Mumble_ext Mumble_iso seq.mult_isol_var)
qed

lemma Mumble_l_prod1 [simp]: "(X \<cdot> Y\<^sup>\<dagger>)\<^sup>\<dagger> = (X \<cdot> Y)\<^sup>\<dagger>"
  by (metis Mumble_idem Mumble_l_prod)

lemma Mumble_l_prod2 [simp]: "(X\<^sup>\<dagger> \<cdot> Y)\<^sup>\<dagger> = (X \<cdot> Y)\<^sup>\<dagger>"
  by (metis Mumble_idem Mumble_l_prod)

lemma Mumble_empty [simp]: "{}\<^sup>\<dagger> = {}"
  by (simp add: Mumble_def)

lemma mumble_LNil: "xs \<in> mumble LNil \<Longrightarrow> xs = LNil"
  by (induct rule: mumble.induct) auto

lemma Mumble_LNil [simp]: "{LNil}\<^sup>\<dagger> = {LNil}"
  by (simp add: Mumble_def) (metis Set.set_insert ex_in_conv insertI2 mumble.self mumble_LNil)

lemma Mumble_star_lfp: "(\<mu> y. {LNil} \<union> x \<cdot> y)\<^sup>\<dagger> = (\<mu> y. {LNil} \<union> (x \<cdot> y)\<^sup>\<dagger>)"
  apply (rule fixpoint_fusion)
  apply (subst lower_is_jp)
  apply (simp add: join_preserving_def Mumble_continuous)
  apply blast
  apply (metis (lifting) insert_def insert_mono l_prod_isor monoI singleton_conv)
  apply (metis (lifting) Mumble_iso insert_def insert_mono l_prod_isor monoI singleton_conv)
  apply (simp only: o_def Mumble_union Mumble_LNil)
  apply (rule ext)
  by (metis Mumble_l_prod1)

lemma Mumble_star1: "(x\<^sup>\<dagger>\<^sup>\<star>)\<^sup>\<dagger> \<subseteq> (x\<^sup>\<star>)\<^sup>\<dagger>"
  by (simp only: star_def Mumble_star_lfp Mumble_l_prod2)

lemma Mumble_star [simp]: "((x\<^sup>\<dagger>)\<^sup>\<star>)\<^sup>\<dagger> = (x\<^sup>\<star>)\<^sup>\<dagger>"
  by (rule antisym, metis Mumble_star1, metis Mumble_ext Mumble_iso seq.star_iso)

lemma Mumble_Inter [simp]: "(\<Inter>(Mumble ` A))\<^sup>\<dagger> = \<Inter>(Mumble ` A)"
  apply (simp add: Mumble_def image_def)
  apply auto
  apply auto
  apply (erule_tac x = "xa\<^sup>\<dagger>" in allE)
  apply (auto simp add: Mumble_def)
  by (metis mumble_trans)

lemma Mumble_FIN [simp]: "(x \<inter> FIN)\<^sup>\<dagger> = (x\<^sup>\<dagger>) \<inter> FIN"
  by (auto simp add: Mumble_def FIN_def)

lemma empty_Mumble_FIN [simp]: "{}\<^sup>\<dagger> \<inter> FIN = {}\<^sup>\<dagger>"
  by (auto simp add: Mumble_def FIN_def)

definition fmumble :: "('a \<times> 'a) lan \<Rightarrow> ('a \<times> 'a) lan" ("_\<^sup>\<ddagger>" [1000] 1000) where
  "fmumble x = x\<^sup>\<dagger> \<inter> FIN"

lemma fmumble_empty [simp]: "{}\<^sup>\<ddagger> = {}"
  by (simp add: fmumble_def)

lemma fmumble_l_prod1 [simp]: "(X\<^sup>\<ddagger> \<cdot> Y)\<^sup>\<ddagger> = (X \<cdot> Y)\<^sup>\<ddagger>"
  by (metis Mumble_FIN Mumble_l_prod2 fmumble_def l_prod_FIN_simp1)

lemma fmumble_l_prod2 [simp]: "(X \<cdot> Y\<^sup>\<ddagger>)\<^sup>\<ddagger> = (X \<cdot> Y)\<^sup>\<ddagger>"
  by (metis Mumble_FIN Mumble_l_prod1 fmumble_def l_prod_FIN_simp2)

lemma fmumble_union [simp]: "(X \<union> Y)\<^sup>\<ddagger> = X\<^sup>\<ddagger> \<union> Y\<^sup>\<ddagger>"
  by (simp add: fmumble_def)

lemma fmumble_one [simp]: "{LNil}\<^sup>\<ddagger> = {LNil}"
  by (auto simp add: fmumble_def FIN_def)

lemma fmumble_idem [simp]: "X\<^sup>\<ddagger>\<^sup>\<ddagger> = X\<^sup>\<ddagger>"
  by (simp add: fmumble_def)

lemma fmumble_shuffle_left [simp]: "(X\<^sup>\<ddagger> \<parallel> Y)\<^sup>\<ddagger> = (X \<parallel> Y)\<^sup>\<ddagger>"
  by (simp add: fmumble_def) (metis Mumble_FIN Mumble_shuffle_right shuffle_FIN_simp2 shuffle_comm)

lemma fmumble_shuffle_right [simp]: "(X \<parallel> Y\<^sup>\<ddagger>)\<^sup>\<ddagger> = (X \<parallel> Y)\<^sup>\<ddagger>"
  by (metis fmumble_shuffle_left shuffle_comm)

lemma fmumble_meet [simp]: "(X\<^sup>\<ddagger> \<inter> Y\<^sup>\<ddagger>)\<^sup>\<ddagger> = X\<^sup>\<ddagger> \<inter> Y\<^sup>\<ddagger>"
  by (simp add: fmumble_def) (metis (hide_lams, no_types) Int_left_commute Mumble_FIN Mumble_meet inf_commute inf_left_idem)

lemma fmumble_star [simp]: "(X\<^sup>\<ddagger>\<^sup>\<star>)\<^sup>\<ddagger> = (X\<^sup>\<star>)\<^sup>\<ddagger>"
  apply (simp add: fmumble_def)  
  by (metis Mumble_FIN Mumble_star inf_commute inf_left_idem star_FIN)

lemma fmumble_iso [intro]: "X \<subseteq> Y \<Longrightarrow> X\<^sup>\<ddagger> \<subseteq> Y\<^sup>\<ddagger>"
  by (metis fmumble_union le_iff_sup)

lemma fmumble_ext: "X \<inter> FIN \<subseteq> X\<^sup>\<ddagger>"
  by (metis Mumble_FIN Mumble_ext fmumble_def)

lemma fmumble_continuous: "(\<Union>\<XX>)\<^sup>\<ddagger> = \<Union>{X\<^sup>\<ddagger> |X. X \<in> \<XX>}"
  by (auto simp add: fmumble_def Mumble_continuous)

lemma fmumble_star_power: "Z\<^sup>\<ddagger> \<subseteq> Y\<^sup>\<ddagger> \<Longrightarrow> (X \<cdot> Y)\<^sup>\<ddagger> \<subseteq> Y\<^sup>\<ddagger> \<Longrightarrow> (power X i \<cdot> Z)\<^sup>\<ddagger> \<subseteq> Y\<^sup>\<ddagger>"
  apply (induct i)
  apply simp_all
proof -
  fix ia :: nat
  assume a1: "(Language.power X ia \<cdot> Z)\<^sup>\<ddagger> \<subseteq> Y\<^sup>\<ddagger>"
  assume a2: "(X \<cdot> Y)\<^sup>\<ddagger> \<subseteq> Y\<^sup>\<ddagger>"
  have "Y\<^sup>\<ddagger> = Y\<^sup>\<ddagger> \<union> (Language.power X ia \<cdot> Z)\<^sup>\<ddagger>"
    using a1 by fastforce
  hence "\<exists>x\<^sub>0. X \<cdot> (Language.power X ia \<cdot> Z) \<subseteq> x\<^sub>0 \<and> x\<^sub>0\<^sup>\<ddagger> \<subseteq> Y\<^sup>\<ddagger>"
    using a2 by (metis fmumble_l_prod2 fmumble_union l_prod_isor par.add_ub2)
  hence "\<exists>x\<^sub>0. (X \<cdot> (Language.power X ia \<cdot> Z))\<^sup>\<ddagger> \<subseteq> x\<^sub>0 \<and> x\<^sub>0 \<subseteq> Y\<^sup>\<ddagger>"
    by (metis fmumble_iso)
  thus "(X \<cdot> Language.power X ia \<cdot> Z)\<^sup>\<ddagger> \<subseteq> Y\<^sup>\<ddagger>"
    by (metis order.trans seq.mult_assoc)
qed

lemma fmumble_star_inductl: "(Z \<union> X \<cdot> Y)\<^sup>\<ddagger> \<subseteq> Y\<^sup>\<ddagger> \<Longrightarrow> (X\<^sup>\<star> \<cdot> Z)\<^sup>\<ddagger> \<subseteq> Y\<^sup>\<ddagger>"
  apply (simp add: star_power l_prod_inf_distr fmumble_continuous Sup_le_iff)
  apply (intro allI impI)
  apply (erule exE)
  apply simp
  apply (erule conjE)+
  apply (erule exE)
  apply (erule conjE)
  apply simp
  apply (rename_tac A B C)
  apply (thin_tac "A = (C \<cdot> Z)\<^sup>\<ddagger>")
  apply (thin_tac "B = C \<cdot> Z")
  apply (tactic {* prune_params_tac *})
  apply (rename_tac X')
  apply (simp add: powers_def)
  apply (erule exE)
  apply simp
  apply (thin_tac "X' = Language.power X i")
  apply (tactic {* prune_params_tac *})
  apply (rule fmumble_star_power)
  by assumption+

end

