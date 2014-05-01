theory Interleaving
  imports Language
begin

section {* Interleaving lemmas *}

no_notation Cons (infixr "#" 65)
notation LCons (infixr "#" 65)

notation ltake ("\<up>") and ldrop ("\<down>")

definition Valid :: "'a llist \<Rightarrow> (unit + unit) llist \<Rightarrow> 'b llist \<Rightarrow> bool" where
  "Valid xs t ys \<equiv> llength (\<ll> t) = llength xs \<and> llength (\<rr> t) = llength ys"

text {* @{term Valid} defines the conditions under which an interleaving @{term "xs \<triangleright> t \<triangleleft> ys"}
is valid *}

lemma interleave_lappend:
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
  assumes "Valid xs t ys"
  shows "\<exists>zs. t = traj zs \<and> zs \<in> xs \<sha> ys"
  using assms
  apply (auto simp add: tshuffle_words_def)
  apply (rule_tac x = "xs \<triangleright> t \<triangleleft> ys" in exI)
  apply (auto simp add: Valid_def)
  apply (metis lefts_interleave_llength traj_interleave)
  by (metis rights_interleave_llength traj_interleave)

theorem interleave_traj_lappend:
  assumes "Valid xs (t \<frown> t') ys"
  shows "xs \<triangleright> t \<frown> t' \<triangleleft> ys = (\<up> (llength (\<ll> t)) xs \<triangleright> t \<triangleleft> \<up> (llength (\<rr> t)) ys) \<frown>
                             (\<down> (llength (\<ll> t)) xs \<triangleright> t' \<triangleleft> \<down> (llength (\<rr> t)) ys)"
  and "Valid (\<up> (llength (\<ll> t)) xs) t (\<up> (llength (\<rr> t)) ys)"
  and "lfinite t \<Longrightarrow> Valid (\<down> (llength (\<ll> t)) xs) t' (\<down> (llength (\<rr> t)) ys)"
  using assms
  apply -
  apply (metis (hide_lams, no_types) interleave_lappend traj_to_shuffle)
  apply (auto simp add: Valid_def)
  apply (metis enat_le_plus_same(1) lappend_inf lefts_append linear llength_lappend min_max.le_iff_inf)
  apply (metis dual_order.refl enat_le_plus_same(1) lappend_inf llength_lappend min_max.le_iff_inf rights_append)
  sorry

lemma lefts_ltake_right [simp]: "\<ll> (ltakeWhile is_right xs) = LNil"
  by (auto dest: lset_ltakeWhileD simp add: lefts_def)

lemma rights_ltake_left [simp]: "\<rr> (ltakeWhile is_left xs) = LNil"
  by (auto dest: lset_ltakeWhileD simp add: rights_def)

lemma lset_all_rightD [dest]: "\<forall>x\<in>lset xs. is_right x \<Longrightarrow> \<ll> xs = LNil"
  by (metis (full_types) lefts_ltake_right ltakeWhile_all)

lemma lset_all_leftD [dest]: "\<forall>x\<in>lset xs. is_left x \<Longrightarrow> \<rr> xs = LNil"
  by (metis (full_types) ltakeWhile_all rights_ltake_left)

subsection {* ldropLeft and ltakeLeft *}

primrec ldropLeft_nat :: "nat \<Rightarrow> ('a + 'b) llist \<Rightarrow> ('a + 'b) llist" where
  "ldropLeft_nat 0 xs = ldropWhile is_right xs"
| "ldropLeft_nat (Suc n) xs = (case ldropWhile is_right xs of (y # ys) \<Rightarrow> ldropLeft_nat n ys | LNil \<Rightarrow> LNil)"  

primrec ldropLeft :: "enat \<Rightarrow> ('a + 'b) llist \<Rightarrow> ('a + 'b) llist" where
  "ldropLeft \<infinity> xs = LNil"
| "ldropLeft (enat n) xs = ldropLeft_nat n xs"

lemma ldropLeft_nat_eq: "n = enat m \<Longrightarrow> ldropLeft n = ldropLeft_nat m"
  apply simp
  apply (rule ext)
  by simp

lemma ldropLeft_eSuc: "n \<noteq> \<infinity> \<Longrightarrow> ldropLeft (eSuc n) xs = (case ldropWhile is_right xs of (y # ys) \<Rightarrow> ldropLeft n ys | LNil \<Rightarrow> LNil)"
  apply (subgoal_tac "\<exists>m. eSuc n = enat (Suc m)")
  apply (erule exE)
  apply simp
  apply (metis eSuc_def enat.simps(4) ldropLeft_nat.simps(2) ldropLeft_nat_eq)
  by (metis eSuc_enat not_enat_eq)

primrec ltakeLeft_nat :: "nat \<Rightarrow> ('a + 'b) llist \<Rightarrow> ('a + 'b) llist" where
  "ltakeLeft_nat 0 xs = ltakeWhile is_right xs"
| "ltakeLeft_nat (Suc n) xs = ltakeWhile is_right xs \<frown> (case ldropWhile is_right xs of (y # ys) \<Rightarrow> y # ltakeLeft_nat n ys | LNil \<Rightarrow> LNil)"

primrec ltakeLeft :: "enat \<Rightarrow> ('a + 'b) llist \<Rightarrow> ('a + 'b) llist" where
  "ltakeLeft \<infinity> xs = xs"
| "ltakeLeft (enat n) xs = ltakeLeft_nat n xs"

lemma ltakeLeft_nat_eq: "n = enat m \<Longrightarrow> ltakeLeft n = ltakeLeft_nat m"
  apply simp
  apply (rule ext)
  by simp

lemma lappend_ltakeLeft_ldropLeft [simp]: "ltakeLeft n xs \<frown> ldropLeft n xs = xs"
proof (induct n, simp_all)
  fix n
  show "ltakeLeft_nat n xs \<frown> ldropLeft_nat n xs = xs"
  proof (induct n arbitrary: xs)
    case 0
    thus ?case
      by simp
  next
    case (Suc n)
    thus ?case
      apply simp
      apply (cases "ldropWhile is_right xs")
      apply simp_all
      by (metis lappend_assoc lappend_code(2) lappend_ltakeWhile_ldropWhile)
  qed
qed

subsection {* ldropRight and ltakeRight *}

primrec ldropRight_nat :: "nat \<Rightarrow> ('a + 'b) llist \<Rightarrow> ('a + 'b) llist" where
  "ldropRight_nat 0 xs = ldropWhile is_left xs"
| "ldropRight_nat (Suc n) xs = (case ldropWhile is_left xs of (y # ys) \<Rightarrow> ldropRight_nat n ys | LNil \<Rightarrow> LNil)"  

primrec ldropRight :: "enat \<Rightarrow> ('a + 'b) llist \<Rightarrow> ('a + 'b) llist" where
  "ldropRight \<infinity> xs = LNil"
| "ldropRight (enat n) xs = ldropRight_nat n xs"

lemma ldropRight_nat_to_ldropLeft_nat: "ldropRight_nat n xs = lmap swap (ldropLeft_nat n (lmap swap xs))"
  apply (induct n arbitrary: xs)
  apply (simp add: ldropWhile_lmap)
  apply simp
  apply (subgoal_tac "ldropWhile is_left xs = LNil \<or> (\<exists>x xs'. ldropWhile is_left xs = LCons x xs')")
  apply (erule disjE)
  apply simp
  apply (metis LNil_preserve is_right_swap ldropWhile_eq_LNil_iff ldropWhile_lmap llist.simps(4))
  apply (erule exE)+
  apply simp
  apply (simp add: ldropWhile_lmap)
  by (metis llist.exhaust)

lemma ldropLeft_nat_to_ldropRight_nat: "ldropLeft_nat n xs = lmap swap (ldropRight_nat n (lmap swap xs))"
  by (simp add: ldropRight_nat_to_ldropLeft_nat)

lemma ldropRight_to_ldropLeft: "ldropRight n xs = lmap swap (ldropLeft n (lmap swap xs))"
  by (cases n) (simp_all add: ldropRight_nat_to_ldropLeft_nat)

lemma ldropLeft_to_ldropRight: "ldropLeft n xs = lmap swap (ldropRight n (lmap swap xs))"
  by (cases n) (simp_all add: ldropLeft_nat_to_ldropRight_nat)

lemma ldropRight_nat_eq: "n = enat m \<Longrightarrow> ldropRight n = ldropRight_nat m"
  apply simp
  apply (rule ext)
  by simp

lemma ldropRight_eSuc: "n \<noteq> \<infinity> \<Longrightarrow> ldropRight (eSuc n) xs = (case ldropWhile is_left xs of (y # ys) \<Rightarrow> ldropRight n ys | LNil \<Rightarrow> LNil)"
  apply (subgoal_tac "\<exists>m. eSuc n = enat (Suc m)")
  apply (erule exE)
  apply simp
  apply (metis co.enat.inject eSuc_enat ldropRight_nat_eq)
  by (metis eSuc_enat enat_the_enat)

primrec ltakeRight_nat :: "nat \<Rightarrow> ('a + 'b) llist \<Rightarrow> ('a + 'b) llist" where
  "ltakeRight_nat 0 xs = ltakeWhile is_left xs"
| "ltakeRight_nat (Suc n) xs = ltakeWhile is_left xs \<frown> (case ldropWhile is_left xs of (y # ys) \<Rightarrow> y # ltakeRight_nat n ys | LNil \<Rightarrow> LNil)"

primrec ltakeRight :: "enat \<Rightarrow> ('a + 'b) llist \<Rightarrow> ('a + 'b) llist" where
  "ltakeRight \<infinity> xs = xs"
| "ltakeRight (enat n) xs = ltakeRight_nat n xs"

lemma ltakeRight_nat_eq: "n = enat m \<Longrightarrow> ltakeRight n = ltakeRight_nat m"
  apply simp
  apply (rule ext)
  by simp

lemma ltakeRight_nat_to_ltakeLeft_nat: "ltakeRight_nat n xs = lmap swap (ltakeLeft_nat n (lmap swap xs))"
  apply (induct n arbitrary: xs)
  apply (simp add: ltakeWhile_lmap)
  apply auto
  apply (subgoal_tac "ldropWhile is_left xs = LNil \<or> (\<exists>x xs'. ldropWhile is_left xs = LCons x xs')")
  apply (erule disjE)
  apply (simp add: ltakeWhile_lmap ldropWhile_lmap)
  apply (erule exE)+
  apply (simp add: ltakeWhile_lmap ldropWhile_lmap lmap_lappend_distrib)
  by (metis llist.exhaust)

lemma ltakeRight_to_ltakeLeft: "ltakeRight n xs = lmap swap (ltakeLeft n (lmap swap xs))"
  by (cases n) (simp_all add: ltakeRight_nat_to_ltakeLeft_nat)

lemma ltakeLeft_nat_to_ltakeRight_nat: "ltakeLeft_nat n xs = lmap swap (ltakeRight_nat n (lmap swap xs))"
  by (simp add: ltakeRight_nat_to_ltakeLeft_nat)

lemma ltakeLeft_to_ltakeRight: "ltakeLeft n xs = lmap swap (ltakeRight n (lmap swap xs))"
  by (simp add: ltakeRight_to_ltakeLeft)

lemma lappend_ltakeRight_ldropRight [simp]: "ltakeRight n xs \<frown> ldropRight n xs = xs"
  apply (subst ldropRight_to_ldropLeft)
  apply (subst ltakeRight_to_ltakeLeft)
  apply (subst lmap_lappend_distrib[symmetric])
  by (metis lappend_ltakeLeft_ldropLeft lmap2_id swap.elims swap.simps(1) swap.simps(2))

lemma interleave_left_lappend:
  assumes "Valid (xs \<frown> ys) t zs" and "lfinite xs"
  shows "xs \<frown> ys \<triangleright> t \<triangleleft> zs = (xs \<triangleright> ltakeLeft (llength xs) t \<triangleleft> \<up> (llength (\<rr> (ltakeLeft (llength xs) t))) zs) \<frown>
                             (ys \<triangleright> ldropLeft (llength xs) t \<triangleleft> \<down> (llength (\<rr> (ltakeLeft (llength xs) t))) zs)"
  and "Valid xs (ltakeLeft (llength xs) t) (\<up> (llength (\<rr> (ltakeLeft (llength xs) t))) zs)"
  and "Valid ys (ldropLeft (llength xs) t) (\<down> (llength (\<rr> (ltakeLeft (llength xs) t))) zs)"
  sorry

lemma interleave_right_lappend:
  assumes "Valid xs t (ys \<frown> zs)" and "lfinite ys"
  shows "xs \<triangleright> t \<triangleleft> ys \<frown> zs = (\<up> (llength (\<ll> (ltakeRight (llength ys) t))) xs \<triangleright> ltakeRight (llength ys) t \<triangleleft> ys) \<frown>
                             (\<down> (llength (\<ll> (ltakeRight (llength ys) t))) xs \<triangleright> ldropRight (llength ys) t \<triangleleft> zs)"
  and "Valid (\<up> (llength (\<ll> (ltakeRight (llength ys) t))) xs) (ltakeRight (llength ys) t) ys"
  and "Valid (\<down> (llength (\<ll> (ltakeRight (llength ys) t))) xs) (ldropRight (llength ys) t) zs"
  sorry

lemma
  assumes "lfinite zs" and "zs \<in> xs \<sha> ys" and "zs' \<in> xs' \<sha> ys'"
  shows "zs \<frown> zs' \<in> (xs \<frown> xs') \<sha> (ys \<frown> ys')"
  using assms by (auto simp add: tshuffle_words_def rights_def lefts_def lmap_lappend_distrib[symmetric])

lemma lmap_unl_to_lmap_Inl: "(\<forall>x\<in>lset xs. is_left x) \<Longrightarrow> lmap unl xs = ys \<longleftrightarrow> xs = lmap Inl ys"
  sorry

lemma lmap_unr_to_lmap_Inr: "(\<forall>x\<in>lset xs. is_right x) \<Longrightarrow> lmap unr xs = ys \<longleftrightarrow> xs = lmap Inr ys"
  sorry

lemma llength_strict_le: "lprefix xs ys \<Longrightarrow> xs \<noteq> ys \<Longrightarrow> llength xs < llength ys"
  by (metis le_llist_conv_lprefix less_llist_conv_lstrict_prefix lstrict_prefix_llength_less order.not_eq_order_implies_strict)

lemma lprefix_ltakeLeft_nat: "lprefix (ltakeLeft_nat n t) (ltakeLeft_nat (Suc n) t)"
  apply (induct n arbitrary: t)
  apply simp
  apply (metis lprefix_lappend)
  apply auto
  apply (subgoal_tac "ldropWhile is_right t = LNil \<or> (\<exists>x xs'. ldropWhile is_right t = LCons x xs')")
  apply (erule disjE)
  apply simp
  apply (erule exE)+
  apply simp
  by (metis neq_LNil_conv)

lemma lprefix_ltakeLeft: "lprefix (ltakeLeft n t) (ltakeLeft (eSuc n) t)"
  apply (cases n)
  apply auto
  apply (simp only: eSuc_enat ltakeLeft.simps)
  by (metis lprefix_ltakeLeft_nat)

lemma lprefix_ltakeRight_nat: "lprefix (ltakeRight_nat n t) (ltakeRight_nat (Suc n) t)"
  apply (induct n arbitrary: t)
  apply simp
  apply (metis lprefix_lappend)
  apply auto
  apply (subgoal_tac "ldropWhile is_left t = LNil \<or> (\<exists>x xs'. ldropWhile is_left t = LCons x xs')")
  apply (erule disjE)
  apply simp
  apply (erule exE)+
  apply simp
  by (metis neq_LNil_conv)

lemma lprefix_ltakeRight: "lprefix (ltakeRight n t) (ltakeRight (eSuc n) t)"
  apply (cases n)
  apply auto
  apply (simp only: eSuc_enat ltakeLeft.simps)
  by (metis lprefix_ltakeRight_nat ltakeRight.simps(2))  

lemma lprefix_not_itself: "lfinite xs \<Longrightarrow> ys \<noteq> LNil \<Longrightarrow> xs \<noteq> xs \<frown> ys"
  by (metis lstrict_prefix_def lstrict_prefix_lappend_conv)

lemma postfix_not_equal: "lfinite xs \<Longrightarrow> ys \<noteq> zs \<Longrightarrow> xs \<frown> ys \<noteq> xs \<frown> zs"
  by (metis lappend_eq_lappend_conv)

lemma tail_not_equal: "xs \<noteq> ys \<Longrightarrow> x # xs \<noteq> x # ys"
  by (metis llist.inject)

lemma lset_split_eq: "x \<in> lset xs \<longleftrightarrow> (\<exists>ys zs. xs = ys \<frown> (x # zs) \<and> lfinite ys)"
  apply default
  apply (metis split_llist)
  by (metis in_lset_lappend_iff lhd_LCons lhd_in_lset llist.distinct(1))

lemma ldropWhile_cases: "ldropWhile P xs = LNil \<or> (\<exists>y ys. ldropWhile P xs = LCons y ys \<and> \<not> P y)"
  apply (cases "\<forall>x\<in>lset xs. P x")
  apply simp
  apply (intro disjI2)
  apply auto
  apply (drule split_llist)
  apply (erule exE)+
  apply (erule conjE)
  apply (rotate_tac 1)
  apply (erule ssubst)
  apply (erule lfinite_induct)
  apply (rule_tac x = x in exI)
  apply simp
  apply (erule exE)
  apply (erule conjE)
  apply (erule exE)
  apply (subgoal_tac "P xa \<or> \<not> P xa")
  apply (erule disjE)
  apply simp
  apply simp
  by simp

lemma [simp]: "lfilter is_left (ltakeWhile is_right t) = LNil"
  by (metis Not_is_left lfilter_ltakeWhile)

lemma ltakeLeft_nat_not_equal_Suc: "enat n < llength (\<ll> t) \<Longrightarrow> ltakeLeft_nat n t \<noteq> ltakeLeft_nat (Suc n) t"
  apply (induct n arbitrary: t)
  apply (simp add: lefts_def)
  apply (subgoal_tac "ldropWhile is_right t = LNil \<or> (\<exists>x xs'. ldropWhile is_right t = LCons (Inl x) xs')")
  apply (erule disjE)
  apply simp
  apply (erule exE)+
  apply simp
  apply (subgoal_tac "lfinite (ltakeWhile is_right t)")
  apply (rule lprefix_not_itself)
  apply simp
  apply simp
  apply (metis lappend_inf lappend_ltakeWhile_ldropWhile ldropWhile_K_True ldropWhile_eq_ldrop llist.discI ltakeWhile_K_True)
  apply (subgoal_tac "ldropWhile is_right t = LNil \<or> (\<exists>y ys. ldropWhile is_right t = LCons y ys \<and> \<not> is_right y)")
  apply (erule disjE)
  apply simp
  apply (erule exE)+
  apply simp
  apply (metis is_right.simps(1) not_is_right obj_sumE)
  apply (rule ldropWhile_cases)
  apply (simp add: lefts_def)
  apply (subgoal_tac "ldropWhile is_right t = LNil \<or> (\<exists>x xs'. ldropWhile is_right t = LCons (Inl x) xs')")
  apply (erule disjE)
  apply simp
  apply (erule exE)+
  apply simp
  defer
  apply (subgoal_tac "ldropWhile is_right t = LNil \<or> (\<exists>y ys. ldropWhile is_right t = LCons y ys \<and> \<not> is_right y)")
  apply (erule disjE)
  apply simp
  apply (erule exE)+
  apply simp
  apply (metis is_right.simps(1) not_is_right obj_sumE)
  apply (rule ldropWhile_cases)
  apply (subgoal_tac "lfinite (ltakeWhile is_right t)")
  prefer 2
  apply (metis lappend_inf lappend_ltakeWhile_ldropWhile ldropWhile_eq_ldrop ldrop_eq_LConsD less_imp_not_eq)
  apply (rule postfix_not_equal)
  apply simp
  apply (rule tail_not_equal)
  apply (subgoal_tac "enat n < llength (lfilter is_left xs')")
  apply metis
  apply (subgoal_tac "enat (Suc n) < llength (lfilter is_left (ltakeWhile is_right t \<frown> ldropWhile is_right t))")
  apply simp
  apply (metis Suc_ile_eq)
  by (metis lappend_ltakeWhile_ldropWhile)

lemma lmap_swap_n_eq: "xs \<noteq> ys \<Longrightarrow> lmap swap xs \<noteq> lmap swap ys"
  by (metis lappend_ltakeRight_ldropRight ldropRight_to_ldropLeft ltakeRight_to_ltakeLeft) 

lemma lmap_swap_swap [simp]: "lmap swap (lmap swap xs) = xs"
  by (metis lappend_ltakeLeft_ldropLeft lappend_ltakeRight_ldropRight ldropLeft_to_ldropRight lmap_lappend_distrib ltakeLeft_to_ltakeRight)

lemma lefts_lmap_swap: "\<ll> (lmap swap xs) = \<rr> xs"
  apply (simp add: lefts_def rights_def)
  by (metis is_left_swap lfilter_lmap lmap.compositionality unl_swap)

lemma ltakeRight_nat_not_equal_Suc: "enat n < llength (\<rr> t) \<Longrightarrow> ltakeRight_nat n t \<noteq> ltakeRight_nat (Suc n) t"
  apply (subgoal_tac "t = lmap swap (lmap swap t)")
  apply (rotate_tac 1)
  apply (erule ssubst)
  apply (subst ltakeRight_nat_to_ltakeLeft_nat)
  apply (subst ltakeRight_nat_to_ltakeLeft_nat)
  apply (rule lmap_swap_n_eq)
  apply (simp only: lmap_swap_swap)
  apply (rule ltakeLeft_nat_not_equal_Suc)
  apply (metis lefts_lmap_swap)
  by simp

lemma ltakeLeft_not_equal_Suc: "n < llength (\<ll> t) \<Longrightarrow> ltakeLeft n t \<noteq> ltakeLeft (eSuc n) t"
  apply (cases n)
  apply auto
  by (metis eSuc_enat ltakeLeft.simps(2) ltakeLeft_nat_not_equal_Suc)

lemma ltakeRight_not_equal_Suc: "n < llength (\<rr> t) \<Longrightarrow> ltakeRight n t \<noteq> ltakeRight (eSuc n) t"
  apply (cases n)
  apply auto
  by (metis eSuc_enat ltakeRight.simps(2) ltakeRight_nat_not_equal_Suc)

lemma "t \<noteq> LNil \<longleftrightarrow> llength (ltakeWhile is_right t) \<noteq> llength (ltakeWhile is_left t)"
  apply (cases t)
  apply simp
  apply simp
  apply auto
  by (metis not_is_right)

lemma [simp]: "\<up> \<infinity> xs = xs"
  by (metis lappend_LNil2 lappend_ltake_ldrop ldrop.simps(2))

lemma non_finite_append: "ys \<noteq> LNil \<Longrightarrow> xs \<frown> ys = xs \<Longrightarrow> \<not> lfinite xs"
  apply (rule classical)
  apply simp
  apply (rotate_tac 2)
  apply (induct rule: lfinite_induct)
  apply simp
  by simp

lemma ltake_lappend_llength_enat': "\<up> (enat i) (xs \<frown> ys) = \<up> (enat i) xs \<Longrightarrow> ys \<noteq> LNil \<longrightarrow> enat i \<le> llength xs"
  apply (induct i arbitrary: xs)
  apply (simp add: enat_0)
  apply (subgoal_tac "(\<exists>x' xs'. xs = x' # xs') \<or> xs = LNil")
  apply (erule disjE)
  apply (erule exE)+
  apply (simp add: eSuc_enat[symmetric])
  apply simp
  apply (simp add: eSuc_enat[symmetric])
  by (metis neq_LNil_conv)

lemma ltake_lappend_llength': "\<up> n (xs \<frown> ys) = \<up> n xs \<Longrightarrow> ys \<noteq> LNil \<longrightarrow> n \<le> llength xs"
  apply (cases "n = \<infinity>")
  apply simp
  apply (metis llength_eq_infty_conv_lfinite lprefix_not_itself)
  apply simp
  apply (erule exE)
  apply simp
  by (metis ltake_lappend_llength_enat')

lemma ltake_lappend_llength: "ys \<noteq> LNil \<Longrightarrow> \<up> n (xs \<frown> ys) = \<up> n xs \<longleftrightarrow> n \<le> llength xs"
  by (metis ltake_lappend1 ltake_lappend_llength')

lemma just_lefts: "Valid xs t LNil \<Longrightarrow> xs \<triangleright> t \<triangleleft> LNil = lmap Inl xs"
  sorry

lemma just_rights: "Valid LNil t ys \<Longrightarrow> LNil \<triangleright> t \<triangleleft> ys = lmap Inr ys"
  sorry

lemma analyse_interleavings:
  assumes "Valid (xs \<frown> (x\<^sub>1 # x\<^sub>2 # xs')) t (ys \<frown> (y\<^sub>1 # y\<^sub>2 # ys'))"

  and "lfinite xs" and "lfinite ys"

  and "\<And>xs\<^sub>1' xs\<^sub>2' xs\<^sub>3' t\<^sub>1 t\<^sub>2 t\<^sub>3 ys\<^sub>1 ys\<^sub>2 ys\<^sub>3.
    Valid xs t\<^sub>1 ys\<^sub>1 \<Longrightarrow> Valid xs\<^sub>1' t\<^sub>2 ys\<^sub>3 \<Longrightarrow> Valid xs\<^sub>3' t\<^sub>3 ys' \<Longrightarrow>
    xs' = xs\<^sub>1' \<frown> xs\<^sub>2' \<frown> xs\<^sub>3' \<Longrightarrow>
    ys = ys\<^sub>1 \<frown> ys\<^sub>2 \<frown> ys\<^sub>3 \<Longrightarrow>
    P ((xs \<triangleright> t\<^sub>1 \<triangleleft> ys\<^sub>1) \<frown> (Inl x\<^sub>1 # LNil) \<frown> lmap Inr ys\<^sub>2 \<frown> (Inl x\<^sub>2 # LNil) \<frown> (xs\<^sub>1' \<triangleright> t\<^sub>2 \<triangleleft> ys\<^sub>3) \<frown>  (Inr y\<^sub>1 # LNil) \<frown> lmap Inl xs\<^sub>2' \<frown> (Inr y\<^sub>2 # LNil) \<frown> (xs\<^sub>3' \<triangleright> t\<^sub>3 \<triangleleft> ys'))"

  and "\<And>xs\<^sub>1' xs\<^sub>2' t\<^sub>1 t\<^sub>2 ys\<^sub>1 ys\<^sub>2.
    Valid xs t\<^sub>1 ys\<^sub>1 \<Longrightarrow> Valid xs\<^sub>2' t\<^sub>2 ys' \<Longrightarrow>
    xs' = xs\<^sub>1' \<frown> xs\<^sub>2' \<Longrightarrow>
    ys = ys\<^sub>1 \<frown> ys\<^sub>2 \<Longrightarrow>
    P ((xs \<triangleright> t\<^sub>1 \<triangleleft> ys\<^sub>1) \<frown> (Inl x\<^sub>1 # LNil) \<frown> lmap Inr ys\<^sub>2 \<frown> (Inr y\<^sub>1 # LNil) \<frown> (Inl x\<^sub>2 # LNil) \<frown> lmap Inl xs\<^sub>1' \<frown> (Inr y\<^sub>2 # LNil) \<frown> (xs\<^sub>2' \<triangleright> t\<^sub>2 \<triangleleft> ys'))"

  and "\<And>t\<^sub>1 t\<^sub>2 ys\<^sub>1 ys\<^sub>2 ys\<^sub>1' ys\<^sub>2'.
    Valid xs t\<^sub>1 ys\<^sub>1 \<Longrightarrow> Valid xs' t\<^sub>2 ys\<^sub>2' \<Longrightarrow>
    ys = ys\<^sub>1 \<frown> ys\<^sub>2 \<Longrightarrow>
    ys' = ys\<^sub>1' \<frown> ys\<^sub>2' \<Longrightarrow>
    P ((xs \<triangleright> t\<^sub>1 \<triangleleft> ys\<^sub>1) \<frown> (Inl x\<^sub>1 # LNil) \<frown> lmap Inr ys\<^sub>2 \<frown> (Inr y\<^sub>1 # LNil) \<frown> (Inr y\<^sub>2 # LNil) \<frown> lmap Inr ys\<^sub>1' \<frown> (Inr x\<^sub>2 # LNil) \<frown> (xs' \<triangleright> t\<^sub>2 \<triangleleft> ys\<^sub>2'))"

  shows "P (xs \<frown> (x\<^sub>1 # x\<^sub>2 # xs') \<triangleright> t \<triangleleft> ys \<frown> (y\<^sub>1 # y\<^sub>2 # ys'))"
proof -
  def px\<^sub>1 \<equiv> "llength (ltakeLeft (llength xs) t)"
  def px\<^sub>2 \<equiv> "llength (ltakeLeft (eSuc (llength xs)) t)"

  have "px\<^sub>1 < px\<^sub>2"
    apply (simp add: px\<^sub>1_def px\<^sub>2_def)
    apply (rule llength_strict_le)
    apply (metis lprefix_ltakeLeft)
    apply (rule ltakeLeft_not_equal_Suc)
    using assms(1)
    apply (simp add: Valid_def)
    by (metis assms(2) lfinite_conv_llength_enat)

  def py\<^sub>1 \<equiv> "llength (ltakeRight (llength ys) t)"
  def py\<^sub>2 \<equiv> "llength (ltakeRight (eSuc (llength ys)) t)"

  have "py\<^sub>1 < py\<^sub>2"
    apply (simp add: py\<^sub>1_def py\<^sub>2_def)
    apply (rule llength_strict_le)
    apply (metis lprefix_ltakeRight)
    apply (rule ltakeRight_not_equal_Suc)
    using assms(1)
    apply (simp add: Valid_def)
    by (metis assms(3) lfinite_conv_llength_enat)

  have "px\<^sub>1 \<noteq> py\<^sub>1"
    apply (simp add: px\<^sub>1_def py\<^sub>1_def)
    sorry

  have "px\<^sub>2 \<noteq> py\<^sub>2"
    sorry

  have "px\<^sub>1 \<noteq> py\<^sub>2"
    sorry

  have "px\<^sub>2 \<noteq> py\<^sub>1"
    sorry

  have "(px\<^sub>1 < px\<^sub>2 \<and> px\<^sub>2 < py\<^sub>1 \<and> py\<^sub>1 < py\<^sub>2) \<or>
        (px\<^sub>1 < py\<^sub>1 \<and> py\<^sub>1 < px\<^sub>2 \<and> px\<^sub>2 < py\<^sub>2) \<or>
        (px\<^sub>1 < py\<^sub>1 \<and> py\<^sub>1 < py\<^sub>2 \<and> py\<^sub>2 < px\<^sub>2) \<or>
        (py\<^sub>1 < py\<^sub>2 \<and> py\<^sub>2 < px\<^sub>1 \<and> px\<^sub>1 < px\<^sub>2) \<or>
        (py\<^sub>1 < px\<^sub>1 \<and> px\<^sub>1 < py\<^sub>2 \<and> py\<^sub>2 < px\<^sub>2) \<or>
        (py\<^sub>1 < px\<^sub>1 \<and> px\<^sub>1 < px\<^sub>2 \<and> px\<^sub>2 < py\<^sub>2)"
    using `px\<^sub>1 < px\<^sub>2` and `py\<^sub>1 < py\<^sub>2` and `px\<^sub>1 \<noteq> py\<^sub>1` and `px\<^sub>2 \<noteq> py\<^sub>2` and `px\<^sub>1 \<noteq> py\<^sub>2` and `px\<^sub>2 \<noteq> py\<^sub>1`
      by (metis linorder_cases)

  moreover have "?this \<Longrightarrow> ?thesis"
  proof (erule rev_mp, simp only: disj_assoc[symmetric], intro impI, (erule disjE)+)
    assume "px\<^sub>1 < px\<^sub>2 \<and> px\<^sub>2 < py\<^sub>1 \<and> py\<^sub>1 < py\<^sub>2"

    thm interleave_left_lappend[where xs = xs and ys = "x\<^sub>1 # x\<^sub>2 # xs'" and t = t and zs = "ys \<frown> (y\<^sub>1 # y\<^sub>2 # ys')"]

(*
    have step1: "?lhs =
      (xs \<triangleright> ltakeLeft (llength xs) t \<triangleleft> \<up> (llength (\<rr> (ltakeLeft (llength xs) t))) (ys \<frown> (y\<^sub>1 # y\<^sub>2 # ys'))) \<frown>
      (x\<^sub>1 # x\<^sub>2 # xs' \<triangleright> ldropLeft (llength xs) t \<triangleleft> \<down> (llength (\<rr> (ltakeLeft (llength xs) t))) (ys \<frown> (y\<^sub>1 # y\<^sub>2 # ys')))"
      apply (rule interleave_left_lappend[where xs = xs and ys = "x\<^sub>1 # x\<^sub>2 # xs'" and t = t and zs = "ys \<frown> (y\<^sub>1 # y\<^sub>2 # ys')"])
      apply (rule assms(1))
      by (rule assms(2))

    have step2: "... =
      (xs \<triangleright> ltakeLeft (llength xs) t \<triangleleft> \<up> (llength (\<rr> (ltakeLeft (llength xs) t))) (ys \<frown> (y\<^sub>1 # y\<^sub>2 # ys'))) \<frown>
      (Inl x\<^sub>1 # LNil) \<frown>
      (x\<^sub>2 # xs' \<triangleright> ltl (ldropLeft (llength xs) t) \<triangleleft> \<down> (llength (\<rr> (ltakeLeft (llength xs) t))) (ys \<frown> (y\<^sub>1 # y\<^sub>2 # ys')))"
      sorry

    have step3: "... =
      (xs \<triangleright> ltakeLeft (llength xs) t \<triangleleft> \<up> (llength (\<rr> (ltakeLeft (llength xs) t))) ys) \<frown>
      (Inl x\<^sub>1 # LNil) \<frown>
      (x\<^sub>2 # xs' \<triangleright> ltl (ldropLeft (llength xs) t) \<triangleleft> \<down> (llength (\<rr> (ltakeLeft (llength xs) t))) ys \<frown> (y\<^sub>1 # y\<^sub>2 # ys'))"
      sorry

    have step4: "... =
      (xs \<triangleright> ltakeLeft (llength xs) t \<triangleleft> \<up> (llength (\<rr> (ltakeLeft (llength xs) t))) ys) \<frown>
      (Inl x\<^sub>1 # LNil) \<frown>
      (LNil \<frown> (x\<^sub>2 # xs') \<triangleright> ltl (ldropLeft (llength xs) t) \<triangleleft> \<down> (llength (\<rr> (ltakeLeft (llength xs) t))) ys \<frown> (y\<^sub>1 # y\<^sub>2 # ys'))"
      by (metis lappend_code(1))

    have step5: "... =
      (xs \<triangleright> ltakeLeft (llength xs) t \<triangleleft> \<up> (llength (\<rr> (ltakeLeft (llength xs) t))) ys) \<frown>
      (Inl x\<^sub>1 # LNil) \<frown>
      (LNil \<triangleright> ltakeLeft 0 (ltl (ldropLeft (llength xs) t)) \<triangleleft> \<up> (llength (\<rr> (ltakeLeft 0 (ltl (ldropLeft (llength xs) t))))) (\<down> (llength (\<rr> (ltakeLeft (llength xs) t))) ys \<frown> (y\<^sub>1 # y\<^sub>2 # ys'))) \<frown>
      (x\<^sub>2 # xs' \<triangleright> ldropLeft 0 (ltl (ldropLeft (llength xs) t)) \<triangleleft> \<down> (llength (\<rr> (ltakeLeft 0 (ltl (ldropLeft (llength xs) t))))) (\<down> (llength (\<rr> (ltakeLeft (llength xs) t))) ys \<frown> (y\<^sub>1 # y\<^sub>2 # ys')))"
      apply (subst interleave_left_lappend)
      prefer 3
      apply simp
      apply (metis lappend_assoc)
      sorry

    have step6: "... =
      (xs \<triangleright> ltakeLeft (llength xs) t \<triangleleft> \<up> (llength (\<rr> (ltakeLeft (llength xs) t))) ys) \<frown>
      (Inl x\<^sub>1 # LNil) \<frown>
      (LNil \<triangleright> ltakeLeft 0 (ltl (ldropLeft (llength xs) t)) \<triangleleft> \<up> (llength (\<rr> (ltakeLeft 0 (ltl (ldropLeft (llength xs) t))))) (\<down> (llength (\<rr> (ltakeLeft (llength xs) t))) ys \<frown> (y\<^sub>1 # y\<^sub>2 # ys'))) \<frown>
      (Inl x\<^sub>2 # LNil) \<frown>
      (xs' \<triangleright> ltl (ldropLeft 0 (ltl (ldropLeft (llength xs) t))) \<triangleleft> \<down> (llength (\<rr> (ltakeLeft 0 (ltl (ldropLeft (llength xs) t))))) (\<down> (llength (\<rr> (ltakeLeft (llength xs) t))) ys \<frown> (y\<^sub>1 # y\<^sub>2 # ys')))"
      sorry

    have step7: "... =
      (xs \<triangleright> ltakeLeft (llength xs) t \<triangleleft> \<up> (llength (\<rr> (ltakeLeft (llength xs) t))) ys) \<frown>
      (Inl x\<^sub>1 # LNil) \<frown>
      lmap Inr (\<up> (llength (\<rr> (ltakeLeft 0 (ltl (ldropLeft (llength xs) t))))) (\<down> (llength (\<rr> (ltakeLeft (llength xs) t))) ys)) \<frown>
      (Inl x\<^sub>2 # LNil) \<frown>
      (xs' \<triangleright> ltl (ldropLeft 0 (ltl (ldropLeft (llength xs) t))) \<triangleleft> \<down> (llength (\<rr> (ltakeLeft 0 (ltl (ldropLeft (llength xs) t))))) (\<down> (llength (\<rr> (ltakeLeft (llength xs) t))) ys) \<frown> (y\<^sub>1 # y\<^sub>2 # ys'))"
      sorry

    have "\<up> (llength (\<rr> (ltakeLeft (llength xs) t))) (ys \<frown> (y\<^sub>1 # y\<^sub>2 # ys')) = \<up> (llength (\<rr> (ltakeLeft (llength xs) t))) ys"
      apply (subst ltake_lappend_llength)
      apply simp
      thm py\<^sub>1_def
*)

    thus ?thesis
      sorry
  next
    assume "px\<^sub>1 < py\<^sub>1 \<and> py\<^sub>1 < px\<^sub>2 \<and> px\<^sub>2 < py\<^sub>2"
    thus ?thesis
      sorry
  next
    assume "px\<^sub>1 < py\<^sub>1 \<and> py\<^sub>1 < py\<^sub>2 \<and> py\<^sub>2 < px\<^sub>2"
    thus ?thesis
      sorry
  next
    assume "py\<^sub>1 < py\<^sub>2 \<and> py\<^sub>2 < px\<^sub>1 \<and> px\<^sub>1 < px\<^sub>2"
    thus ?thesis
      sorry
  next
    assume "py\<^sub>1 < px\<^sub>1 \<and> px\<^sub>1 < py\<^sub>2 \<and> py\<^sub>2 < px\<^sub>2"
    thus ?thesis
      sorry
  next
    assume "py\<^sub>1 < px\<^sub>1 \<and> px\<^sub>1 < px\<^sub>2 \<and> px\<^sub>2 < py\<^sub>2"
    thus ?thesis
      sorry
  qed
  ultimately show "?thesis"
    by blast
qed

(* ################################## Environments ################################## *)

coinductive env :: "'a rel \<Rightarrow> ('a \<times> 'a) llist \<Rightarrow> bool" for "R" where
  EqNil [intro!,simp]: "env R LNil"
| EqSingle [intro!,simp]: "env R (LCons \<sigma> LNil)"
| EqPair [intro!]: "(snd \<sigma>, fst \<sigma>') \<in> R \<Longrightarrow> env R (LCons \<sigma>' t) \<Longrightarrow> env R (LCons \<sigma> (LCons \<sigma>' t))"

definition Env :: "'a rel \<Rightarrow> ('a \<times> 'a) lan \<Rightarrow> ('a \<times> 'a) lan" (infixr "\<Colon>" 52) where
  "R \<Colon> X \<equiv> X \<inter> Collect (env (R\<^sup>*))"

lemma env_tl [dest]: "env R (LCons \<sigma> t) \<Longrightarrow> env R t"
  by (erule env.cases) auto

lemma env_LConsD [dest]: "env R (LCons \<sigma> (LCons \<sigma>' t)) \<Longrightarrow> (snd \<sigma>, fst \<sigma>') \<in> R"
  by (erule env.cases) auto

lemma env_interE1 [elim]: "env (R \<inter> S) x \<Longrightarrow> env S x"
proof -
  assume "env (R \<inter> S) x"
  thus ?thesis
  proof coinduct
    case (env t)
    show ?case
    proof (cases t)
      assume "t = LNil"
      thus ?case
        by simp
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
        from env
        have "?EqPair"
          by auto
        thus "?EqSingle \<or> ?EqPair" by simp
      qed
      thus ?case by simp
    qed
  qed
qed

lemma env_interE2 [elim]: "env (R \<inter> S) x \<Longrightarrow> env R x"
  by (metis env_interE1 inf_commute)

lemma env_InterE: "env (\<Inter>\<RR>) x \<Longrightarrow> R \<in> \<RR> \<Longrightarrow> env R x"
proof -
  assume "env (\<Inter>\<RR>) x" and "R \<in> \<RR>"
  hence "env (\<Inter>\<RR>) x \<and> R \<in> \<RR>" by simp
  thus "env R x"
  proof coinduct
    case (env t)
    thus ?case
    proof (cases t)
      assume "t = LNil"
      thus ?case
        by simp
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
        from env
        have "?EqPair"
          by auto
        thus "?EqSingle \<or> ?EqPair"
          by auto
      qed
      thus ?case by simp
    qed
  qed
qed

lemma env_InterE_star: "env ((\<Inter>{R\<^sup>* |R. R \<in> \<RR>})\<^sup>*) x \<Longrightarrow> R \<in> \<RR> \<Longrightarrow> env (R\<^sup>*) x"
proof -
  assume "env ((\<Inter>{R\<^sup>* |R. R \<in> \<RR>})\<^sup>*) x" and "R \<in> \<RR>"
  hence "env ((\<Inter>{R\<^sup>* |R. R \<in> \<RR>})\<^sup>*) x \<and> R \<in> \<RR>" by simp
  thus "env (R\<^sup>*) x"
  proof coinduct
    case (env t)
    thus ?case
    proof (cases t)
      assume "t = LNil"
      thus ?case
        by simp
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
        from env
        have "?EqPair"
          apply auto
          apply (drule env_LConsD)
          apply (erule set_rev_mp)
          apply (subst rtrancl_idemp[symmetric]) back back
          apply (rule rtrancl_mono)
          by auto
        thus "?EqSingle \<or> ?EqPair"
          by auto
      qed
      thus ?case by simp
    qed
  qed
qed

lemma env_interI [intro]: "env R t \<Longrightarrow> env S t \<Longrightarrow> env (R \<inter> S) t"
proof -
  assume "env R t" and "env S t"
  hence "env R t \<and> env S t"
    by auto
  thus "env (R \<inter> S) t"
  proof (coinduct)
    case (env t)
    thus ?case
    proof (cases t)
      assume "t = LNil"
      thus ?case
        by simp
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
        from env
        show "?EqSingle \<or> ?EqPair"
          by auto
      qed
      thus ?case by simp
    qed
  qed
qed

lemma env_InterI [intro]: "(\<And>R. R \<in> \<RR> \<Longrightarrow> env R t) \<Longrightarrow> env (\<Inter>\<RR>) t"
proof -
  assume "(\<And>R. R \<in> \<RR> \<Longrightarrow> env R t)"
  hence "(\<forall>R. R \<in> \<RR> \<longrightarrow> env R t)"
    by auto
  thus "env (\<Inter>\<RR>) t"
  proof (coinduct)
    case (env t)
    thus ?case
    proof (cases t)
      assume "t = LNil"
      thus ?case
        by simp
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
        from env
        show "?EqSingle \<or> ?EqPair"
          by auto
      qed
      thus ?case by simp
    qed
  qed
qed

lemma contrp: "(\<not> P \<longrightarrow> Q) \<longleftrightarrow> (\<not> Q \<longrightarrow> P)"
  by blast

lemma environment_var': "\<not> env R xs \<longrightarrow> (\<exists>ys \<sigma> \<sigma>' zs. lfinite ys \<and> env R (ys \<frown> LCons \<sigma> LNil) \<and> xs = ys \<frown> LCons \<sigma> (LCons \<sigma>' zs) \<and> (snd \<sigma>, fst \<sigma>') \<notin> R)"
proof (subst contrp, auto)
  assume "\<forall>ys. lfinite ys \<longrightarrow>
               (\<forall>a b. env R (ys \<frown> LCons (a, b) LNil) \<longrightarrow>
                      (\<forall>a'. (\<forall>b' zs. xs \<noteq> ys \<frown> LCons (a, b) (LCons (a', b') zs)) \<or> (b, a') \<in> R))"
  thus "env R xs"
  proof coinduct
    case (env t)
    thus ?case
    proof (cases t)
      assume "t = LNil"
      thus ?case
        by simp
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
        from env
        have "?EqPair"
          apply (rule_tac x = \<sigma> in exI)
          apply (rule_tac x = \<sigma>' in exI)
          apply (rule_tac x = t'' in exI)
          apply (intro conjI)
          apply simp
          apply simp
          apply (erule_tac x = LNil in allE)
          apply simp
          apply (metis surjective_pairing)
          apply (subgoal_tac "(snd \<sigma>, fst \<sigma>') \<in> R")
          defer
          apply simp
          apply (erule_tac x = LNil in allE)
          apply simp
          apply (metis surjective_pairing)
          apply auto
          apply (erule_tac x = "LCons \<sigma> ys" in allE)
          apply (erule impE)
          apply simp
          apply (erule_tac x = a in allE)
          apply (erule_tac x = b in allE)
          apply (erule impE)
          apply simp
          apply (subgoal_tac "(\<exists>\<sigma>'' ys'. ys = LCons \<sigma>'' ys') \<or> ys = LNil")
          apply (erule disjE)
          apply (erule exE)+
          apply simp
          apply (metis env.EqPair)
          apply simp
          apply (metis EqPair EqSingle fst_conv)
          apply (metis neq_LNil_conv)
          apply (erule_tac x = a' in allE)
          apply (erule disjE)
          apply (metis lappend_code(2))
          by blast
        thus "?EqSingle \<or> ?EqPair"
          by auto
      qed
      thus ?case by simp
    qed
  qed
qed

lemma environment_var: "\<not> env R xs \<Longrightarrow> (\<exists>ys \<sigma> \<sigma>' zs. lfinite ys \<and> env R (ys \<frown> LCons \<sigma> LNil) \<and> xs = ys \<frown> LCons \<sigma> (LCons \<sigma>' zs) \<and> (snd \<sigma>, fst \<sigma>') \<notin> R)"
  by (metis environment_var')

lemma environment': "\<not> env R xs \<longrightarrow> (\<exists>ys \<sigma> \<sigma>' zs. lfinite ys \<and> xs = ys \<frown> LCons \<sigma> (LCons \<sigma>' zs) \<and> (snd \<sigma>, fst \<sigma>') \<notin> R)"
proof (subst contrp, auto)
  assume "\<forall>ys. lfinite ys \<longrightarrow> (\<forall>a b a'. (\<forall>b' zs. xs \<noteq> ys \<frown> LCons (a, b) (LCons (a', b') zs)) \<or> (b, a') \<in> R)"
  thus "env R xs"
  proof coinduct
    case (env t)
    thus ?case
    proof (cases t)
      assume "t = LNil"
      thus ?case
        by simp
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
        from env
        have "?EqPair"
          apply auto
          apply (metis lappend_code(1) lfinite_code(1) surjective_pairing)
          by (metis lappend_code(2) lfinite_LCons)
        thus "?EqSingle \<or> ?EqPair"
          by auto
      qed
      thus ?case by simp
    qed
  qed
qed

lemma environment: "\<not> env R xs \<Longrightarrow> (\<exists>ys \<sigma> \<sigma>' zs. lfinite ys \<and> xs = ys \<frown> LCons \<sigma> (LCons \<sigma>' zs) \<and> (snd \<sigma>, fst \<sigma>') \<notin> R)"
  by (metis environment')

lemma LCons_lappend_LNil: "LCons y ys = LCons y LNil \<frown> ys"
  by (metis lappend_code(1) lappend_code(2))

lemma gap_environment: "lfinite xs \<Longrightarrow> env R (LCons \<sigma> LNil \<frown> xs \<frown> LCons \<sigma>' LNil) \<Longrightarrow> (snd \<sigma>, fst \<sigma>') \<in> (R \<union> lset xs)\<^sup>*"
proof (induct arbitrary: \<sigma> rule: lfinite.induct)
  case lfinite_LNil thus ?case
    by simp (metis env_LConsD r_into_rtrancl)
next
  case (lfinite_LConsI xs x)
  hence "env R (LCons \<sigma> (LCons x (xs \<frown> LCons \<sigma>' LNil)))"
    by (metis LCons_lappend_LNil lappend_code(2))
  hence "env R (LCons x (xs \<frown> LCons \<sigma>' LNil))" and "(snd \<sigma>, fst x) \<in> R"
    by - (metis env_tl, metis env_LConsD)
  hence "env R (LCons x LNil \<frown> xs \<frown> LCons \<sigma>' LNil)"
    by (metis LCons_lappend_LNil lappend_code(2))
  hence "(snd x, fst \<sigma>') \<in> (R \<union> lset xs)\<^sup>*"
    by (metis lfinite_LConsI.hyps(2))
  hence "(snd x, fst \<sigma>') \<in> (R \<union> lset (LCons x xs))\<^sup>*"
    by (rule set_rev_mp) (auto intro!: rtrancl_mono)
  moreover have "(fst x, snd x) \<in> lset (LCons x xs)"
    by (metis lset_intros(1) surjective_pairing)
  ultimately show ?case using `(snd \<sigma>, fst x) \<in> R`
    apply -
    apply (rule converse_rtrancl_into_rtrancl[where b = "fst x"])
    apply simp
    apply (rule converse_rtrancl_into_rtrancl[where b = "snd x"])
    by simp_all
qed

lemma shuffle_interleaving: "zs \<in> xs \<sha> ys \<Longrightarrow> zs = xs \<triangleright> traj zs \<triangleleft> ys"
  by (auto simp add: tshuffle_words_def reinterleave)

lemma shuffle_env_left:
  assumes "zs \<in> xs \<sha> ys"
  and "env R (lmap \<langle>id,id\<rangle> zs)"
  shows "env ((R \<union> lset ys)\<^sup>*) xs"
proof (rule classical)
  assume "\<not> env ((R \<union> lset ys)\<^sup>*) xs"
  hence "\<exists>as \<sigma> \<sigma>' bs. lfinite as \<and> xs = as \<frown> LCons \<sigma> (LCons \<sigma>' bs) \<and> (snd \<sigma>, fst \<sigma>') \<notin> (R \<union> lset ys)\<^sup>*"
    by (metis environment)
  then obtain as and \<sigma> and \<sigma>' and bs
  where lfinite_as: "lfinite as" and xs_split: "xs = as \<frown> LCons \<sigma> (LCons \<sigma>' bs)" and "(snd \<sigma>, fst \<sigma>') \<notin> (R \<union> lset ys)\<^sup>*"
    by auto

  from assms(1)
  have zs_llen: "llength (\<ll> zs) = llength xs"
    by (auto simp add: tshuffle_words_def)

  have zs_interleave: "zs = as \<frown> LCons \<sigma> (LCons \<sigma>' bs) \<triangleright> traj zs \<triangleleft> ys"
    by (metis assms(1) shuffle_interleaving xs_split)
  have traj_zs_llen: "llength (\<ll> (traj zs)) = llength as + llength (LCons \<sigma> (LCons \<sigma>' bs))"
    by (simp add: zs_llen xs_split)
  have traj_zs_rlen: "llength (\<rr> (traj zs)) = llength ys"
    using assms(1) by (simp add: tshuffle_words_def) 

  from interleave_left_lappend[OF lfinite_as zs_interleave traj_zs_llen traj_zs_rlen]
  obtain ys' and ys''
  where "lfinite ys'" and ys_split: "ys = ys' \<frown> ys''"
  and zs_prefix: "zs = (as \<triangleright> \<up> (llength as + llength ys') (traj zs) \<triangleleft> ys') \<frown> (LCons \<sigma> (LCons \<sigma>' bs) \<triangleright> LCons (Inl ()) (\<down> (eSuc (llength as + llength ys')) (traj zs)) \<triangleleft> ys'')"
    by auto

  let ?prefix = "as \<triangleright> \<up> (llength as + llength ys') (traj zs) \<triangleleft> ys'"
  let ?t = "\<down> (eSuc (llength as + llength ys')) (traj zs)"

  have "zs = ?prefix \<frown> (LCons \<sigma> (LCons \<sigma>' bs) \<triangleright> LCons (Inl ()) ?t \<triangleleft> ys'')"
    by (metis zs_prefix)
  also have "... = ?prefix \<frown> LCons (Inl \<sigma>) (LCons \<sigma>' bs \<triangleright> ?t \<triangleleft> ys'')"
    by (metis zs_prefix interleave_left lhd_LCons ltl_simps(2))
  also have "... = ?prefix \<frown> LCons (Inl \<sigma>) (LCons \<sigma>' bs \<triangleright> ltakeWhile is_right ?t \<frown> LCons (Inl ()) (ltl (ldropWhile is_right ?t)) \<triangleleft> ys'')"
    sorry
  also have "... = ?prefix \<frown> LCons (Inl \<sigma>) LNil \<frown> lmap Inr (\<up> (llength (ltakeWhile is_right ?t)) ys'') \<frown> LCons (Inl \<sigma>') (bs \<triangleright> ltl (ldropWhile is_right ?t) \<triangleleft> \<down> (llength (ltakeWhile is_right ?t)) ys'')"
    sorry
  finally have "zs = ?prefix \<frown> LCons (Inl \<sigma>) LNil \<frown> lmap Inr (\<up> (llength (ltakeWhile is_right ?t)) ys'') \<frown> LCons (Inl \<sigma>') (bs \<triangleright> ltl (ldropWhile is_right ?t) \<triangleleft> \<down> (llength (ltakeWhile is_right ?t)) ys'')"
    by simp

  hence "env R (LCons \<sigma> LNil \<frown> \<up> (llength (ltakeWhile is_right ?t)) ys'' \<frown> LCons \<sigma>' LNil)"
    sorry  
  hence "(snd \<sigma>, fst \<sigma>') \<in> (R \<union> lset (\<up> (llength (ltakeWhile is_right ?t)) ys''))\<^sup>*"
    apply -
    apply (erule gap_environment[rotated 1])
    defer
    apply (rule lfinite_ltake_llength)
    sorry
  hence "(snd \<sigma>, fst \<sigma>') \<in> (R \<union> lset ys)\<^sup>*"
    apply (rule set_rev_mp)
    apply (intro rtrancl_mono Un_mono order_refl)
    by (metis Un_upper2 `lfinite ys'` lset_lappend_lfinite lset_ltake order.trans ys_split)
  from this and `(snd \<sigma>, fst \<sigma>') \<notin> (R \<union> lset ys)\<^sup>*` have False
    by blast
  thus ?thesis by blast
qed

lemma shuffle_env_right:
  assumes "zs \<in> xs \<sha> ys"
  and "env R (lmap \<langle>id,id\<rangle> zs)"
  shows "env ((R \<union> lset xs)\<^sup>*) ys"
  sorry

lemma env_lappend1: "env R (xs \<frown> ys) \<Longrightarrow> env R xs"
  sorry

lemma env_lappend2: "lfinite xs \<Longrightarrow> env R (xs \<frown> ys) \<Longrightarrow> env R ys"
  sorry

(* ################################## Rely guarantee ################################## *)

lemma tshuffle_lappend: "lfinite zs\<^sub>1 \<Longrightarrow> zs\<^sub>1 \<in> xs\<^sub>1 \<sha> ys\<^sub>1 \<Longrightarrow> zs\<^sub>2 \<in> xs\<^sub>2 \<sha> ys\<^sub>2 \<Longrightarrow> zs\<^sub>1 \<frown> zs\<^sub>2 \<in> (xs\<^sub>1 \<frown> xs\<^sub>2) \<sha> (ys\<^sub>1 \<frown> ys\<^sub>2)"
  by (auto simp add: tshuffle_words_def lefts_append rights_append)

lemma tshuffle_left_LCons: "zs \<in> xs \<sha> ys \<Longrightarrow> Inl z # zs \<in> (z # xs) \<sha> ys"
  by (auto simp add: tshuffle_words_def)

lemma llength_enat_lfinite: "\<exists>n. llength xs = enat n \<Longrightarrow> lfinite xs"
  by (metis enat.distinct(1) not_lfinite_llength)

lemma llength_interleave: "Valid xs t ys \<Longrightarrow> llength (xs \<triangleright> t \<triangleleft> ys) = llength xs + llength ys"
  sorry

definition rg'' :: "'a rel \<Rightarrow> ('a \<times> 'a) llist \<Rightarrow> ('a \<times> 'a) llist \<Rightarrow> bool" where
  "rg'' R xs xs' \<equiv> (\<exists>xs\<^sub>p \<sigma>\<^sub>1 \<sigma>\<^sub>1' \<sigma>\<^sub>2 \<sigma>\<^sub>2' \<sigma>\<^sub>2'' as bs. xs = xs\<^sub>p \<frown> ((\<sigma>\<^sub>1, \<sigma>\<^sub>1') # (\<sigma>\<^sub>2, \<sigma>\<^sub>2') # as) \<and> xs' = xs\<^sub>p \<frown> ((\<sigma>\<^sub>1, \<sigma>\<^sub>1') # (\<sigma>\<^sub>2, \<sigma>\<^sub>2'') # bs) \<and> lfinite xs\<^sub>p \<and> (\<sigma>\<^sub>1', \<sigma>\<^sub>2) \<notin> R \<and> env R (xs\<^sub>p \<frown> ((\<sigma>\<^sub>1, \<sigma>\<^sub>1') # LNil)))"

definition rg' :: "'a rel \<Rightarrow> ('a \<times> 'a) llist \<Rightarrow> ('a \<times> 'a) llist \<Rightarrow> bool" where
  "rg' R xs xs' \<equiv> (\<exists>xs\<^sub>p \<sigma>\<^sub>1 \<sigma>\<^sub>1' \<sigma>\<^sub>2 \<sigma>\<^sub>2' \<sigma>\<^sub>2'' as bs. xs = xs\<^sub>p \<frown> ((\<sigma>\<^sub>1, \<sigma>\<^sub>1') # (\<sigma>\<^sub>2, \<sigma>\<^sub>2') # as) \<and> xs' = xs\<^sub>p \<frown> ((\<sigma>\<^sub>1, \<sigma>\<^sub>1') # (\<sigma>\<^sub>2, \<sigma>\<^sub>2'') # bs) \<and> lfinite xs\<^sub>p \<and> (\<sigma>\<^sub>1', \<sigma>\<^sub>2) \<notin> R)"

definition RG :: "'a rel \<Rightarrow> ('a \<times> 'a) lan \<Rightarrow> ('a \<times> 'a) lan" (infix "\<leadsto>" 60) where
  "R \<leadsto> X = {ys. \<exists>xs\<in>X. rg' (R\<^sup>*) xs ys}"

lemma rg''_intro: "lfinite xs\<^sub>p \<Longrightarrow> (\<sigma>\<^sub>1', \<sigma>\<^sub>2) \<notin> R \<Longrightarrow>
       rg'' R (xs\<^sub>p \<frown> ((\<sigma>\<^sub>1, \<sigma>\<^sub>1') # (\<sigma>\<^sub>2, \<sigma>\<^sub>2') # as)) (xs\<^sub>p \<frown> ((\<sigma>\<^sub>1, \<sigma>\<^sub>1') # (\<sigma>\<^sub>2, \<sigma>\<^sub>2'') # bs))"
  apply (induct rule: lfinite_induct)
  apply (simp add: rg''_def)
  apply (rule_tac x = LNil in exI)
  apply simp
  apply (subgoal_tac "\<exists>\<tau>\<^sub>1 \<tau>\<^sub>1'. x = (\<tau>\<^sub>1,\<tau>\<^sub>1')")
  apply (erule exE)+
  apply simp
  prefer 2
  apply (metis surj_pair)
  apply (simp only: rg''_def)
  apply (erule exE)+
  apply (erule conjE)+
  apply simp
  apply (subgoal_tac "xs\<^sub>p = LNil \<or> (\<exists>\<tau>\<^sub>2 \<tau>\<^sub>2' xs\<^sub>p'. xs\<^sub>p = (\<tau>\<^sub>2, \<tau>\<^sub>2') # xs\<^sub>p')")
  prefer 2
  apply (metis llist.exhaust prod.exhaust)
  apply (erule disjE)
  apply simp
  apply (subgoal_tac "(\<tau>\<^sub>1',\<sigma>\<^sub>1'') \<in> R \<or> (\<tau>\<^sub>1',\<sigma>\<^sub>1'') \<notin> R")
  prefer 2
  apply metis
  apply (erule disjE)
  apply (rule_tac x = "(\<tau>\<^sub>1, \<tau>\<^sub>1') # LNil" in exI)
  apply (rule_tac x = \<sigma>\<^sub>1'' in exI, rule_tac x = \<sigma>\<^sub>1''' in exI, rule_tac x = \<sigma>\<^sub>2''' in exI)
  apply (intro conjI)
  apply simp
  apply simp
  apply simp
  apply simp
  apply simp
  apply (metis EqPair EqSingle fst_conv snd_conv)
  apply (rule_tac x = "LNil" in exI)
  apply (rule_tac x = \<tau>\<^sub>1 in exI, rule_tac x = \<tau>\<^sub>1' in exI, rule_tac x = \<sigma>\<^sub>1'' in exI)
  apply (intro conjI)
  apply simp
  apply simp
  apply simp
  apply simp
  apply simp
  apply (erule exE)+
  apply simp
  apply (subgoal_tac "(\<tau>\<^sub>1',\<tau>\<^sub>2) \<in> R \<or> (\<tau>\<^sub>1',\<tau>\<^sub>2) \<notin> R")
  apply (erule disjE)
  apply (rule_tac x = "(\<tau>\<^sub>1, \<tau>\<^sub>1') # (\<tau>\<^sub>2, \<tau>\<^sub>2') # xs\<^sub>p'" in exI)
  apply (rule_tac x = \<sigma>\<^sub>1'' in exI, rule_tac x = \<sigma>\<^sub>1''' in exI, rule_tac x = \<sigma>\<^sub>2''' in exI)
  apply (intro conjI)
  apply simp
  apply blast
  apply simp
  apply blast
  apply simp
  apply simp
  apply simp
  apply (metis EqPair fst_conv snd_conv)
  prefer 2
  apply metis
  apply (rule_tac x = "LNil" in exI)
  apply (rule_tac x = \<tau>\<^sub>1 in exI, rule_tac x = \<tau>\<^sub>1' in exI, rule_tac x = \<tau>\<^sub>2 in exI)
  apply (intro conjI)
  by simp_all

lemma rg''_is_rg': "rg'' R xs xs' \<longleftrightarrow> rg' R xs xs'"
  apply default
  apply (simp add: rg''_def rg'_def)
  apply blast
  apply (simp add: rg'_def)
  apply (erule exE)+
  apply (erule conjE)+
  apply (erule exE)+
  apply simp
  apply (rule rg''_intro)
  by auto

definition "alternate xs ys \<equiv> xs \<triangleright> (SOME t. Valid xs t ys) \<triangleleft> ys"

lemma alternate_prop: "alternate xs ys \<in> xs \<sha> ys"
  sorry

lemma test:
  assumes "zs' \<in> xs' \<sha> ys'"
  and "rg' ((R \<union> G\<^sub>2)\<^sup>*) xs xs'" and "lset xs \<subseteq> G\<^sub>1\<^sup>*"
  and "rg' ((R \<union> G\<^sub>1)\<^sup>*) ys ys'" and "lset ys \<subseteq> G\<^sub>2\<^sup>*"
  shows "\<exists>zs \<in> xs \<sha> ys. rg' (R\<^sup>*) (lmap \<langle>id,id\<rangle> zs) (lmap \<langle>id,id\<rangle> zs')"
  sorry

definition prog :: "'a rel \<Rightarrow> ('a \<times> 'a) lan" where
  "prog X = {xs. lset xs \<subseteq> X\<^sup>*}"

lemma "(R \<union> G\<^sub>2 \<leadsto> prog G\<^sub>1 \<inter> X) \<parallel> (R \<union> G\<^sub>1 \<leadsto> prog G\<^sub>2 \<inter> Y) \<subseteq> R \<leadsto> (prog G\<^sub>1 \<inter> X) \<parallel> (prog G\<^sub>2 \<inter> Y)"
  apply (auto simp add: RG_def shuffle_def prog_def)
  apply (rename_tac xs' ys' zs xs ys)
  apply (rule_tac x = "lmap \<langle>id,id\<rangle> ` (xs \<sha> ys)" in exI)
  by (metis (full_types) imageI test)

lemma
  assumes "zs' \<in> xs' \<sha> ys'"
  and "rg' ((R \<union> G\<^sub>2)\<^sup>*) xs xs'" and "lset xs \<subseteq> G\<^sub>1\<^sup>*"
  and "rg' ((R \<union> G\<^sub>1)\<^sup>*) ys ys'" and "lset ys \<subseteq> G\<^sub>2\<^sup>*"
  shows "\<exists>zs \<in> xs \<sha> ys. rg' (R\<^sup>*) (lmap \<langle>id,id\<rangle> zs) (lmap \<langle>id,id\<rangle> zs')"
proof -
  obtain xs\<^sub>p \<sigma>\<^sub>1 \<sigma>\<^sub>1' \<sigma>\<^sub>2 \<sigma>\<^sub>2' \<sigma>\<^sub>2'' xs\<^sub>t xs\<^sub>t'
  where xs_def: "xs = xs\<^sub>p \<frown> ((\<sigma>\<^sub>1, \<sigma>\<^sub>1') # (\<sigma>\<^sub>2, \<sigma>\<^sub>2') # xs\<^sub>t)"
  and xs'_def: "xs' = xs\<^sub>p \<frown> ((\<sigma>\<^sub>1, \<sigma>\<^sub>1') # (\<sigma>\<^sub>2, \<sigma>\<^sub>2'') # xs\<^sub>t')"
  and lfinite_xs\<^sub>p: "lfinite xs\<^sub>p"
  and "(\<sigma>\<^sub>1', \<sigma>\<^sub>2) \<notin> (R \<union> G\<^sub>2)\<^sup>*"
  and "env ((R \<union> G\<^sub>2)\<^sup>*) (xs\<^sub>p \<frown> ((\<sigma>\<^sub>1, \<sigma>\<^sub>1') # LNil))"
    sorry

  obtain ys\<^sub>p \<tau>\<^sub>1 \<tau>\<^sub>1' \<tau>\<^sub>2 \<tau>\<^sub>2' \<tau>\<^sub>2'' ys\<^sub>t ys\<^sub>t'
  where ys_def: "ys = ys\<^sub>p \<frown> ((\<tau>\<^sub>1, \<tau>\<^sub>1') # (\<tau>\<^sub>2, \<tau>\<^sub>2') # ys\<^sub>t)"
  and ys'_def: "ys' = ys\<^sub>p \<frown> ((\<tau>\<^sub>1, \<tau>\<^sub>1') # (\<tau>\<^sub>2, \<tau>\<^sub>2'') # ys\<^sub>t')"
  and lfinite_ys\<^sub>p: "lfinite ys\<^sub>p"
  and "(\<tau>\<^sub>1', \<tau>\<^sub>2) \<notin> (R \<union> G\<^sub>1)\<^sup>*"
  and "env ((R \<union> G\<^sub>2)\<^sup>*) (ys\<^sub>p \<frown> ((\<tau>\<^sub>1, \<tau>\<^sub>1') # LNil))"
    sorry

  def P \<equiv> "\<lambda>zs'. \<exists>zs \<in> xs \<sha> ys. rg' (R\<^sup>*) (lmap \<langle>id,id\<rangle> zs) (lmap \<langle>id,id\<rangle> zs')"

  have "P (xs\<^sub>p \<frown> ((\<sigma>\<^sub>1, \<sigma>\<^sub>1') # (\<sigma>\<^sub>2, \<sigma>\<^sub>2'') # xs\<^sub>t') \<triangleright> traj zs' \<triangleleft> ys\<^sub>p \<frown> ((\<tau>\<^sub>1, \<tau>\<^sub>1') # (\<tau>\<^sub>2, \<tau>\<^sub>2'') # ys\<^sub>t'))"
  proof (rule analyse_interleavings)
    show "Valid (xs\<^sub>p \<frown> ((\<sigma>\<^sub>1, \<sigma>\<^sub>1') # (\<sigma>\<^sub>2, \<sigma>\<^sub>2'') # xs\<^sub>t')) (traj zs') (ys\<^sub>p \<frown> ((\<tau>\<^sub>1, \<tau>\<^sub>1') # (\<tau>\<^sub>2, \<tau>\<^sub>2'') # ys\<^sub>t'))"
      using assms(1) by (simp add: Valid_def tshuffle_words_def xs'_def ys'_def)
  next
    show "lfinite xs\<^sub>p"
      by (metis lfinite_xs\<^sub>p)
  next
    show "lfinite ys\<^sub>p"
      by (metis lfinite_ys\<^sub>p)
  next
    fix xs\<^sub>1' xs\<^sub>2' xs\<^sub>3' t\<^sub>1 t\<^sub>2 t\<^sub>3 ys\<^sub>1 ys\<^sub>2 ys\<^sub>3
    assume "Valid xs\<^sub>p t\<^sub>1 ys\<^sub>1" and "Valid xs\<^sub>1' t\<^sub>2 ys\<^sub>3" and "Valid xs\<^sub>3' t\<^sub>3 ys\<^sub>t'"
    and "xs\<^sub>t' = xs\<^sub>1' \<frown> xs\<^sub>2' \<frown> xs\<^sub>3'"
    and ys\<^sub>p_def: "ys\<^sub>p = ys\<^sub>1 \<frown> ys\<^sub>2 \<frown> ys\<^sub>3"

    have "env ((R \<union> G\<^sub>2)\<^sup>*) ys\<^sub>p"
      by (metis `env ((R \<union> G\<^sub>2)\<^sup>*) (ys\<^sub>p \<frown> ((\<tau>\<^sub>1, \<tau>\<^sub>1') # LNil))` env_lappend1)
    have "env ((R \<union> G\<^sub>2)\<^sup>*) ys\<^sub>2"
      by (metis `ys\<^sub>p = ys\<^sub>1 \<frown> ys\<^sub>2 \<frown> ys\<^sub>3` `env ((R \<union> G\<^sub>2)\<^sup>*) ys\<^sub>p` env_lappend1 env_lappend2 lfinite_lappend lfinite_ys\<^sub>p)

    thus "P ((xs\<^sub>p \<triangleright> t\<^sub>1 \<triangleleft> ys\<^sub>1) \<frown> (Inl (\<sigma>\<^sub>1, \<sigma>\<^sub>1') # LNil) \<frown> lmap Inr ys\<^sub>2 \<frown> (Inl (\<sigma>\<^sub>2, \<sigma>\<^sub>2'') # LNil) \<frown>
             (xs\<^sub>1' \<triangleright> t\<^sub>2 \<triangleleft> ys\<^sub>3) \<frown> (Inr (\<tau>\<^sub>1, \<tau>\<^sub>1') # LNil) \<frown> lmap Inl xs\<^sub>2' \<frown> (Inr (\<tau>\<^sub>2, \<tau>\<^sub>2'') # LNil) \<frown> (xs\<^sub>3' \<triangleright> t\<^sub>3 \<triangleleft> ys\<^sub>t'))"
      proof (cases "ys\<^sub>2 = LNil")
        assume [simp]: "ys\<^sub>2 = LNil"

        show ?thesis
          apply simp
          apply (simp only: P_def)
          apply (rule_tac x = "(xs\<^sub>p \<triangleright> t\<^sub>1 \<triangleleft> ys\<^sub>1) \<frown> (Inl (\<sigma>\<^sub>1, \<sigma>\<^sub>1') # LNil) \<frown> (Inl (\<sigma>\<^sub>2, \<sigma>\<^sub>2') # LNil) \<frown> alternate xs\<^sub>t (ys\<^sub>3 \<frown> ((\<tau>\<^sub>1, \<tau>\<^sub>1') # (\<tau>\<^sub>2, \<tau>\<^sub>2') # ys\<^sub>t))" in bexI)
          prefer 2
          apply (simp add: xs_def ys_def ys\<^sub>p_def lappend_assoc)
          apply (rule tshuffle_lappend)
          apply (rule llength_enat_lfinite)
          apply (subst llength_interleave)
          apply (metis `Valid xs\<^sub>p t\<^sub>1 ys\<^sub>1`)
          apply (subst llength_lappend[symmetric])
          apply (subgoal_tac "lfinite (xs\<^sub>p \<frown> ys\<^sub>1)")
          apply (drule lfinite_llength_enat)
          apply assumption
          apply (metis lfinite_lappend lfinite_xs\<^sub>p lfinite_ys\<^sub>p ys\<^sub>p_def)
          apply (metis `Valid xs\<^sub>p t\<^sub>1 ys\<^sub>1` shuffle_interleaving traj_to_shuffle)
          apply (rule tshuffle_left_LCons)+
          apply (rule alternate_prop)
          apply (simp only: rg'_def)
          apply (rule_tac x = "lmap \<langle>id,id\<rangle> (xs\<^sub>p \<triangleright> t\<^sub>1 \<triangleleft> ys\<^sub>1)" in exI)
          apply (rule_tac x = \<sigma>\<^sub>1 in exI, rule_tac x = \<sigma>\<^sub>1' in exI)
          apply (rule_tac x = \<sigma>\<^sub>2 in exI, rule_tac x = \<sigma>\<^sub>2' in exI, rule_tac x = \<sigma>\<^sub>2'' in exI)
          apply (rule_tac x = "lmap \<langle>id,id\<rangle> (alternate xs\<^sub>t (ys\<^sub>3 \<frown> ((\<tau>\<^sub>1, \<tau>\<^sub>1') # (\<tau>\<^sub>2, \<tau>\<^sub>2') # ys\<^sub>t)))" in exI)
          apply (rule_tac x = "lmap \<langle>id,id\<rangle> ((xs\<^sub>1' \<triangleright> t\<^sub>2 \<triangleleft> ys\<^sub>3) \<frown> (Inr (\<tau>\<^sub>1, \<tau>\<^sub>1') # LNil) \<frown> lmap Inl xs\<^sub>2' \<frown> (Inr (\<tau>\<^sub>2, \<tau>\<^sub>2'') # LNil) \<frown> (xs\<^sub>3' \<triangleright> t\<^sub>3 \<triangleleft> ys\<^sub>t'))" in exI)
          apply (intro conjI)
          apply (simp only: lmap_lappend_distrib llist.map(2))
          apply simp
          apply (metis LCons_lappend_LNil lappend_assoc)
          apply (simp only: lmap_lappend_distrib llist.map(2))
          apply simp
          apply (metis LCons_lappend_LNil lappend_assoc)
          apply (metis `Valid xs\<^sub>p t\<^sub>1 ys\<^sub>1` lfinite_lappend lfinite_lmap lfinite_shuffle lfinite_xs\<^sub>p lfinite_ys\<^sub>p shuffle_interleaving traj_to_shuffle ys\<^sub>p_def)  
          by (metis `(\<sigma>\<^sub>1', \<sigma>\<^sub>2) \<notin> (R \<union> G\<^sub>2)\<^sup>*` in_rtrancl_UnI)
  next
    fix xs\<^sub>1' xs\<^sub>2' t\<^sub>1 t\<^sub>2 ys\<^sub>1 ys\<^sub>2
    assume "Valid xs\<^sub>p t\<^sub>1 ys\<^sub>1"
    and "Valid xs\<^sub>2' t\<^sub>2 ds"
    and "bs = xs\<^sub>1' \<frown> xs\<^sub>2'"
    and "ys\<^sub>p = ys\<^sub>1 \<frown> ys\<^sub>2"

    thus "P ((xs\<^sub>p \<triangleright> t\<^sub>1 \<triangleleft> ys\<^sub>1) \<frown>
             (Inl (\<sigma>\<^sub>1, \<sigma>\<^sub>1') # LNil) \<frown>
             lmap Inr ys\<^sub>2 \<frown>
             (Inr (\<tau>\<^sub>1, \<tau>\<^sub>1') # LNil) \<frown>
             (Inl (\<sigma>\<^sub>2, \<sigma>\<^sub>2'') # LNil) \<frown>
             lmap Inl xs\<^sub>1' \<frown>
             (Inr (\<tau>\<^sub>2, \<tau>\<^sub>2'') # LNil) \<frown>
             (xs\<^sub>2' \<triangleright> t\<^sub>2 \<triangleleft> ds))"
      apply (simp only: P_def)
      apply (simp only: rg'_def)
      apply (rule_tac x = "(xs\<^sub>p \<triangleright> t\<^sub>1 \<triangleleft> ys\<^sub>1) \<frown> (Inl (\<sigma>\<^sub>1, \<sigma>\<^sub>1') # LNil) \<frown> lmap Inr ys\<^sub>2 \<frown> (Inr (\<tau>\<^sub>1, \<tau>\<^sub>1') # LNil) \<frown> (Inl (\<sigma>\<^sub>2, \<sigma>\<^sub>2') # LNil) \<frown> alternate as ((\<tau>\<^sub>2, \<tau>\<^sub>2'') # ds)" in bexI)
      apply (simp only: rg'_def)
      apply (rule_tac x = "lmap \<langle>id,id\<rangle> ((xs\<^sub>p \<triangleright> t\<^sub>1 \<triangleleft> ys\<^sub>1) \<frown> (Inl (\<sigma>\<^sub>1, \<sigma>\<^sub>1') # LNil) \<frown> lmap Inr ys\<^sub>2)" in exI)
      apply (rule_tac x = \<tau>\<^sub>1 in exI) apply (rule_tac x = \<tau>\<^sub>1' in exI)
      apply (rule_tac x = \<sigma>\<^sub>2 in exI) apply (rule_tac x = \<sigma>\<^sub>2' in exI)
      apply (rule_tac x = \<sigma>\<^sub>2'' in exI)
      apply (rule_tac x = "lmap \<langle>id,id\<rangle> (alternate as ((\<tau>\<^sub>2, \<tau>\<^sub>2'') # ds))" in exI)
      apply (rule_tac x = "xs\<^sub>1' \<frown> ((\<tau>\<^sub>2, \<tau>\<^sub>2'') # LNil) \<frown> lmap \<langle>id,id\<rangle> (xs\<^sub>2' \<triangleright> t\<^sub>2 \<triangleleft> ds)" in exI)
      apply (intro conjI)
      
      sledgehammer
end
