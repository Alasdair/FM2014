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

find_theorems lmap "op \<frown>"

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

datatype element_spec = Nth_Left nat | Nth_Right nat

definition compare_pos :: "element_spec \<Rightarrow> element_spec \<Rightarrow> ('a + 'b) llist set" (infix "\<lless>" 90) where
  "x \<lless> y = undefined"

lemma compare_pos_total: "x \<lless> y \<union> y \<lless> x = UNIV"

lemma
  assumes "Valid (xs \<frown> (x\<^sub>1 # x\<^sub>2 # xs')) t (ys \<frown> (y\<^sub>1 # y\<^sub>2 # ys'))"
  and "lfinite xs"
  shows "xs \<frown> (x\<^sub>1 # x\<^sub>2 # xs') \<triangleright> t \<triangleleft> ys \<frown> (y\<^sub>1 # y\<^sub>2 # ys') = Z" (is "?lhs = ?rhs")
proof -
  have "?lhs = (xs \<triangleright> ltakeLeft (llength xs) t \<triangleleft> \<up> (llength (\<rr> (ltakeLeft (llength xs) t))) (ys \<frown> (y\<^sub>1 # y\<^sub>2 # ys'))) \<frown>
               (x\<^sub>1 # x\<^sub>2 # xs' \<triangleright> ldropLeft (llength xs) t \<triangleleft> \<down> (llength (\<rr> (ltakeLeft (llength xs) t))) (ys \<frown> (y\<^sub>1 # y\<^sub>2 # ys')))"
    by (simp only: interleave_left_lappend[OF assms(1) assms(2)])

  have split_Valid1:
    "Valid xs (ltakeLeft (llength xs) t) (\<up> (llength (\<rr> (ltakeLeft (llength xs) t))) (ys \<frown> (y\<^sub>1 # y\<^sub>2 # ys')))"
    by (simp only: interleave_left_lappend[OF assms(1) assms(2)])

  have split_Valid2:
    "Valid (x\<^sub>1 # x\<^sub>2 # xs') (ldropLeft (llength xs) t) (\<down> (llength (\<rr> (ltakeLeft (llength xs) t))) (ys \<frown> (y\<^sub>1 # y\<^sub>2 # ys')))"
    by (simp only: interleave_left_lappend[OF assms(1) assms(2)])

end
