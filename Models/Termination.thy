theory Termination
  imports Aczel3
begin

definition terminates :: "('a \<times> bool \<times> 'a) llist \<Rightarrow> bool" where
  "terminates xs = (\<exists>ys zs. xs = ys \<frown> zs \<and> lfinite ys \<and> (\<forall>(\<sigma>, l, \<sigma>')\<in>lset zs. l = False))"

lemma lfinite_terminates: "lfinite xs \<Longrightarrow> terminates xs"
  by (auto simp add: terminates_def) (metis in_lset_lappend_iff lappend_LNil2 split_llist_first)

definition states :: "('a \<times> bool \<times> 'a) llist \<Rightarrow> 'a set" where
  "states xs = pre ` lset xs \<union> post ` lset xs"

lemma [simp]: "(case x of (\<sigma>, l, \<sigma>') \<Rightarrow> \<not> l) \<longleftrightarrow> \<not> fst (snd x)"
  by (cases x) simp

lemma LNil_terminates: "terminates LNil"
  by (simp add: terminates_def)

lemma terminates_LCons: "terminates xs \<Longrightarrow> terminates (LCons x xs)"
  by (auto simp add: terminates_def) (metis lappend_code(2) lfinite_LCons)

lemma llength_enat_0 [simp]: "llength xs = enat 0 \<longleftrightarrow> xs = LNil"
  by (metis llength_eq_0 zero_enat_def)

lemma llength_enat_Suc: "llength xs = enat (Suc n) \<Longrightarrow> (\<exists>x' xs'. xs = LCons x' xs' \<and> llength xs' = enat n)"
  by (metis diff_Suc_Suc eSuc_enat i0_iless_eSuc idiff_enat_enat ldropn_0 ldropn_Suc_conv_ldropn llength_ldropn semiring_numeral_div_class.diff_zero zero_enat_def)

lemma right_lappend_left:
  assumes "llength xs = enat n"
  shows "lmap Inr xs \<frown> LCons (Inl x) LNil = LCons x LNil \<triangleright> llist_of (replicate n (Inr ())) \<frown> LCons (Inl ()) LNil \<triangleleft> xs"
  using assms  
  apply (induct n arbitrary: xs)
  apply simp
  apply (metis interleave_left lhd_LCons traj_LNil)
  apply (drule llength_enat_Suc)
  apply (erule exE)+
  apply (erule conjE)
  apply (subgoal_tac "lmap Inr xs' \<frown> LCons (Inl x) LNil = LCons x LNil \<triangleright> llist_of (replicate n (Inr ())) \<frown> LCons (Inl ()) LNil \<triangleleft> xs'")
  apply simp
  apply (subst interleave_right)
  by auto

find_theorems lset lnth

lemma lset_member_to_lnth: "x \<in> lset t \<Longrightarrow> (\<exists>n. lnth t n = x \<and> enat n < llength t)"
  using lset_ex_lnth[where P = "op = x", simplified]
  by (metis in_lset_conv_lnth)

lemma left_or_right: "x = Inl () \<or> x = Inr ()"
  by (cases x) auto

lemma lfinite_replicate_right: "lfinite t \<Longrightarrow> llength (\<ll> t) \<noteq> 0 \<Longrightarrow> \<exists>n t'. t = llist_of (replicate n (Inr ())) \<frown> LCons (Inl ()) t'"
  apply (induct t rule: lfinite.induct)
  apply (simp add: lefts_def)
  apply (subgoal_tac "x = Inl () \<or> x = Inr ()")
  apply (erule disjE)
  apply simp
  apply (rule_tac x = 0 in exI)
  apply simp
  apply simp
  apply (erule exE)+
  apply (rule_tac x = "Suc n" in exI)
  apply (rule_tac x = t' in exI)
  apply force
  by (metis left_or_right)

lemma llength_no_lefts_repl: "llength xs = enat n \<Longrightarrow> llength (\<ll> xs) = 0 \<Longrightarrow> xs = llist_of (replicate n (Inr ()))"
  apply (induct n arbitrary: xs)
  apply (auto simp add: lefts_def)
  apply (subgoal_tac "(\<exists>x' xs'. xs = LCons x' xs') \<or> xs = LNil")
  apply (erule disjE)
  apply (erule exE)+
  apply (simp_all add: eSuc_enat[symmetric])
  apply (metis (full_types) is_right.simps(2) swap.cases unit.exhaust)
  by (metis neq_LNil_conv)

lemma replicate_right: "llength (\<ll> t) \<noteq> 0 \<Longrightarrow> \<exists>n t'. t = llist_of (replicate n (Inr ())) \<frown> LCons (Inl ()) t'"
proof (auto simp add: lefts_def)
  fix x
  assume "x \<in> lset t" and "is_left x"
  hence "\<exists>n. lnth t n = Inl () \<and> enat n < llength t"
    by (metis (full_types) is_left.simps(2) lset_member_to_lnth swap.cases unit.exhaust)
  then obtain n where "lnth t n = Inl ()" and "enat n < llength t" by auto
  hence "t = ltake (enat n) t \<frown> LCons (Inl ()) (ldrop (enat (Suc n)) t)"
    by (metis lappend_ltake_enat_ldropn ldrop.simps(1) ldropn_Suc_conv_ldropn)
  {
    assume "llength (\<ll> (ltake (enat n) t)) = 0"
    hence "ltake (enat n) t = llist_of (replicate n (Inr ()))"
      by (rule llength_no_lefts_repl[rotated]) (metis `enat n < llength t` leD linear llength_ltake min_def)
    hence "t = llist_of (replicate n (Inr ())) \<frown> LCons (Inl ()) (ldrop (enat (Suc n)) t)"
      by (metis `t = ltake (enat n) t \<frown> LCons (Inl ()) (ldrop (enat (Suc n)) t)`)
    hence ?thesis
      by metis
  }
  moreover
  {
    assume "llength (\<ll> (ltake (enat n) t)) \<noteq> 0"
    hence "\<exists>m t'. ltake (enat n) t = llist_of (replicate m (Inr ())) \<frown> LCons (Inl ()) t'"
      by (rule lfinite_replicate_right[rotated]) simp
    hence ?thesis
      by (metis `t = ltake (enat n) t \<frown> LCons (Inl ()) (ldrop (enat (Suc n)) t)` lappend_assoc lappend_code(2))
  }
  ultimately show ?thesis
    by metis
qed

lemma
  assumes "llength (\<ll> t) = llength (LCons x xs)"
  and "llength (\<rr> t) = llength ys"
  shows "\<exists>n m. (LCons x xs \<triangleright> t \<triangleleft> ys) = (LCons x LNil \<triangleright> ltake n t \<triangleleft> ltake m ys) \<frown> (xs \<triangleright> ldrop n t \<triangleleft> ldrop m ys)"
proof -
  have "\<exists>n t'. t = llist_of (replicate n (Inr ())) \<frown> LCons (Inl ()) t'"
    by (rule replicate_right) (metis assms(1) llength_eq_0 llist.distinct(1))
  then obtain n and t' where "t = llist_of (replicate n (Inr ())) \<frown> LCons (Inl ()) t'"
    by auto
  hence "LCons x xs \<triangleright> t \<triangleleft> ys = LCons x xs \<triangleright> llist_of (replicate n (Inr ())) \<frown> LCons (Inl ()) t' \<triangleleft> ltake (enat n) ys \<frown> ldrop (enat n) ys"
    by (metis lappend_ltake_ldrop)
  also have "... = lmap Inr (ltake (enat n) ys) \<frown> (LCons x xs \<triangleright> LCons (Inl ()) t' \<triangleleft> ldrop (enat n) ys)"
    sorry
  also have "... = lmap Inr (ltake (enat n) ys) \<frown> LCons (Inl x) (xs \<triangleright> t' \<triangleleft> ldrop (enat n) ys)"
    by (subst interleave_left) auto
  also have "... = lmap Inr (ltake (enat n) ys) \<frown> LCons (Inl x) LNil \<frown> (xs \<triangleright> t' \<triangleleft> ldrop (enat n) ys)"
    by (metis lappend_snocL1_conv_LCons2)
  also have "... = (LCons x LNil \<triangleright> llist_of (replicate n (Inr ())) \<frown> LCons (Inl ()) LNil \<triangleleft> ltake (enat n) ys) \<frown> (xs \<triangleright> t' \<triangleleft> ldrop (enat n) ys)"
    apply (subst right_lappend_left)
    apply auto
    sorry
  finally show ?thesis
    sorry
qed

lemma
  assumes "lfinite xs"
  and "llength (\<ll> t) = llength (xs \<frown> ys)"
  and "llength (\<rr> t) = llength zs"
  shows "\<exists>n m. (xs \<frown> ys \<triangleright> t \<triangleleft> zs) = (xs \<triangleright> ltake n t \<triangleleft> ltake m zs) \<frown> (ys \<triangleright> ldrop n t \<triangleleft> ldrop m zs)" 
proof -
  from assms
  have ?thesis
  proof (induct rule: lfinite.induct)
    case lfinite_LNil
    show ?case
      by (rule_tac x = 0 in exI)+ simp
  next
    assume "lfinite xs"
    and "\<exists>n m. xs \<frown> ys \<triangleright> t \<triangleleft> zs = (xs \<triangleright> ltake n t \<triangleleft> ltake m zs) \<frown> (ys \<triangleright> ldrop n t \<triangleleft> ldrop m zs)"
    then obtain n and m where "xs \<frown> ys \<triangleright> t \<triangleleft> zs = (xs \<triangleright> ltake n t \<triangleleft> ltake m zs) \<frown> (ys \<triangleright> ldrop n t \<triangleleft> ldrop m zs)"

lemma terminates_shuffle:
  assumes "terminates xs"
  and "terminates ys"
  and "zs \<in> xs \<sha> ys"
  shows "terminates (lmap \<langle>id,id\<rangle> zs)"
proof -
  obtain xs1 and xs2 where "xs = xs1 \<frown> xs2" and "lfinite xs1" and "\<forall>(\<sigma>, l, \<sigma>')\<in>lset xs2. l = False"
    using assms(1) by (auto simp add: terminates_def)

  obtain ys1 and ys2 where "ys = ys1 \<frown> ys2" and "lfinite ys1" and "\<forall>(\<sigma>, l, \<sigma>')\<in>lset ys2. l = False"
    using assms(2) by (auto simp add: terminates_def)
