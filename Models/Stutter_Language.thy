theory Stutter_Language
  imports Language
begin

inductive_set stutter :: "('a \<times> 'a) llist \<Rightarrow> ('a \<times> 'a) lan" for xs where
  self [simp, intro!]: "LCons (\<sigma>, \<sigma>) xs \<in> stutter xs"
| stutter [intro]: "ys \<frown> zs \<in> stutter xs \<Longrightarrow> ys \<frown> LCons (\<sigma>, \<sigma>) zs \<in> stutter xs"
| mumble [dest]: "ys \<frown> LCons (\<sigma>, \<sigma>') (LCons (\<sigma>', \<sigma>'') zs) \<in> stutter xs \<Longrightarrow> ys \<frown> LCons (\<sigma>, \<sigma>'') zs \<in> stutter xs"

definition Stutter :: "('a \<times> 'a) lan \<Rightarrow> ('a \<times> 'a) lan" ("_\<^sup>\<dagger>" [1000] 1000) where
  "X\<^sup>\<dagger> = \<Union>{stutter xs |xs. xs \<in> X}"

lemma [dest]: "xs \<in> stutter (LCons (\<sigma>, \<sigma>) ys) \<Longrightarrow> xs \<in> stutter ys"
  apply (induct xs rule: stutter.induct)
  apply (metis lappend_code(1) stutter.self stutter.stutter)
  apply (metis stutter.stutter)
  by (metis stutter.mumble)

lemma [simp]: "Id_on UNIV = {(\<sigma>, \<sigma>'). \<sigma> = \<sigma>'}"
  by (metis Collect_mem_eq in_rel_Collect_split_eq in_rel_Id_on_UNIV split_curry)

lemma [intro]: "xs \<in> stutter LNil \<Longrightarrow> xs \<in> \<Union>{stutter xs |xs. \<exists>a. xs = LCons (a, a) LNil}"
  apply (induct xs rule: stutter.induct)
  apply auto
  apply (rule_tac x = "stutter (LCons (\<sigma>, \<sigma>) LNil)" in exI)
  apply auto
  by (metis lappend_code(1) stutter.mumble stutter.self)

definition test :: "'a set \<Rightarrow> ('a \<times> 'a) lan" ("\<langle>_\<rangle>" [0] 1000) where
  "\<langle>S\<rangle> \<equiv> ((\<lambda>x. LCons x LNil) ` Id_on S)\<^sup>\<dagger>"

(* 1\<^sup>\<dagger> is the top test element *)
lemma [simp]: "{LNil}\<^sup>\<dagger> = \<langle>top\<rangle>"
  by (auto simp add: Stutter_def test_def image_def)

(* 0\<^sup>\<dagger> is the least test element *)
lemma [simp]: "{}\<^sup>\<dagger> = \<langle>bot\<rangle>"
  by (auto simp add: Stutter_def test_def)

lemma LNil_Stutter_fin [intro!]: "{LNil}\<^sup>\<dagger> \<subseteq> FIN"
proof (auto simp add: FIN_def Stutter_def)
  fix xs :: "('a \<times> 'a) llist"
  assume "xs \<in> stutter LNil"
  thus "lfinite xs"
    by (induct xs rule: stutter.induct, auto)
qed

lemma stutter_trans: "xs \<in> stutter ys \<Longrightarrow> ys \<in> stutter zs \<Longrightarrow> xs \<in> stutter zs"
proof (induct xs rule: stutter.induct)
  case (self \<sigma>)
  thus ?case
    by (metis lappend_code(1) stutter.stutter)
next
  case (stutter ws vs \<sigma>)
  from stutter(2)[OF stutter(3)]
  show ?case
    by (rule stutter.stutter)
next
  case (mumble ws \<sigma> \<sigma>' \<sigma>'' vs)
  from mumble(2)[OF mumble(3)]
  show ?case
    by (rule stutter.mumble)
qed

lemma stutter_lappend: "xs \<in> stutter xs' \<Longrightarrow> ys \<in> stutter ys' \<Longrightarrow> (xs \<frown> ys) \<in> stutter (xs' \<frown> ys')"
proof (induct xs rule: stutter.induct)
  case (self \<sigma>)
  thus ?case
  proof (induct ys rule: stutter.induct)
    case (self \<sigma>')
    show ?case
      by (metis lappend_code(2) stutter.self stutter.stutter)
  next
    case (stutter ws vs \<sigma>')
    thus ?case
      by (metis lappend_assoc stutter.stutter)
  next
    case (mumble ws \<sigma>' \<sigma>'' \<sigma>''' vs)
    thus ?case
      by (metis lappend_assoc stutter.mumble)
  qed
next
  case (stutter ws vs \<sigma>')
  thus ?case
    by (metis lappend_assoc lappend_code(2) stutter.stutter)
next
  case (mumble ws \<sigma> \<sigma>' \<sigma>'' vs)
  thus ?case
    by (metis lappend_assoc lappend_code(2) stutter.mumble)
qed

lemma Stutter_iso: "X \<subseteq> Y \<Longrightarrow> X\<^sup>\<dagger> \<subseteq> Y\<^sup>\<dagger>"
  by (auto simp add: Stutter_def)

lemma stutter_never_LNil: "xs \<in> stutter ys \<Longrightarrow> xs = LNil \<Longrightarrow> False"
  by (induct rule: stutter.induct) auto

lemma [dest!]: "LNil \<in> stutter xs \<Longrightarrow> False"
  by (metis stutter_never_LNil)

lemma stutter_refl: "LCons x xs \<in> stutter (LCons x xs)"
proof (cases x, erule ssubst)
  fix \<sigma> \<sigma>'
  have "LCons (\<sigma>, \<sigma>) (LCons (\<sigma>, \<sigma>') xs) \<in> stutter (LCons (\<sigma>, \<sigma>') xs)"
    by (metis stutter.self)
  from stutter.mumble[where ys = "LNil", simplified, OF this]
  show "LCons (\<sigma>, \<sigma>') xs \<in> stutter (LCons (\<sigma>, \<sigma>') xs)" .
qed

lemma [dest!]: "x \<notin> stutter x \<Longrightarrow> x = LNil"
  by (metis neq_LNil_conv stutter_refl)

lemma Stutter_ext: "X - {LNil} \<subseteq> X\<^sup>\<dagger>"
  by (auto simp add: Stutter_def, erule_tac x = "stutter x" in allE, auto)

lemma Stutter_idem [simp]: "X\<^sup>\<dagger>\<^sup>\<dagger> = X\<^sup>\<dagger>"
proof -
  have "X\<^sup>\<dagger> = X\<^sup>\<dagger> - {LNil}"
    by (auto simp add: Stutter_def)
  also have "... \<subseteq> X\<^sup>\<dagger>\<^sup>\<dagger>"
    by (metis calculation Stutter_ext)
  finally show "X\<^sup>\<dagger>\<^sup>\<dagger> = X\<^sup>\<dagger>"
    by (auto dest: stutter_trans simp add: Stutter_def)
qed

lemma Stutter_union [simp]: "(X \<union> Y)\<^sup>\<dagger> = X\<^sup>\<dagger> \<union> Y\<^sup>\<dagger>"
  by (auto simp add: Stutter_def)

lemma Stutter_continuous: "(\<Union>\<XX>)\<^sup>\<dagger> = \<Union>{X\<^sup>\<dagger> |X. X \<in> \<XX>}"
  by (auto simp add: Stutter_def) 

lemma Stutter_meet [simp]: "(X\<^sup>\<dagger> \<inter> Y\<^sup>\<dagger>)\<^sup>\<dagger> = X\<^sup>\<dagger> \<inter> Y\<^sup>\<dagger>"
  apply (auto dest: stutter_trans simp add: Stutter_def)
  by (metis neq_LNil_conv stutter_never_LNil stutter_refl)

lemma stutter_infinite [dest]: "ys \<in> stutter xs \<Longrightarrow> \<not> lfinite xs \<Longrightarrow> \<not> lfinite ys"
  by (induct ys rule: stutter.induct) auto

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

lemma "stutter xs \<cdot> stutter ys \<subseteq> stutter (xs \<frown> ys)"
  apply (auto simp add: l_prod_def)
  apply (metis lappend_inf stutter.self stutter_lappend)
  by (metis stutter_lappend)

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

lemma stutter_refl_var: "xs \<noteq> LNil \<Longrightarrow> xs \<in> stutter xs"
  by (metis neq_LNil_conv stutter_refl)

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

lemma [simp]: "\<up> \<infinity> xs = xs"
  apply (cases "lfinite xs")
  apply (induct xs rule: lfinite_induct)
  apply simp_all
  apply (subst eSuc_infinity[symmetric])
  apply (subst ltake_LCons)
  apply (simp del: eSuc_infinity)
  by (metis ltake_all not_lfinite_llength order_refl)

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

lemma stutter_LCons: "ys \<in> stutter xs \<Longrightarrow> LCons x ys \<in> stutter (LCons x xs)"
  apply (subst LCons_lappend_LNil[where ys = xs])
  apply (subst LCons_lappend_LNil[where ys = ys])
  apply (rule stutter_lappend)
  apply (rule stutter_refl)
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

lemma stutter_in_left:
  assumes "t \<in> (xs \<frown> LCons (\<sigma>, \<sigma>) ys) \<sha> zs"
  shows "lmap \<langle>id,id\<rangle> (xs \<frown> LCons (\<sigma>, \<sigma>) ys \<triangleright> traj t \<triangleleft> zs) \<in> stutter (lmap \<langle>id,id\<rangle> (xs \<frown> ys \<triangleright> ldeleteLeft (llength xs) (traj t) \<triangleleft> zs))"
proof (cases "llength xs")
  assume "llength xs = \<infinity>"
  from this and assms show ?thesis
    by (auto intro: stutter_refl_var sumlist_cases[of t] simp add: traj_def interleave_left interleave_right)
next
  let ?TR = "ltakeWhile is_right"
  let ?DR = "ldropWhile is_right"

  fix n
  assume "llength xs = enat n"
  moreover hence "lmap \<langle>id,id\<rangle> (xs \<frown> LCons (\<sigma>, \<sigma>) ys \<triangleright> traj t \<triangleleft> zs) \<in> stutter (lmap \<langle>id,id\<rangle> (xs \<frown> ys \<triangleright> ldeleteLeft_nat n (traj t) \<triangleleft> zs))" using assms
  proof (induct n arbitrary: xs t zs)
    case 0 note zero = this
    {
      assume zs_not_LNil: "zs \<noteq> LNil"

      from zero have [simp]: "xs = LNil"
        by (metis llength_eq_0 zero_enat_def)
      hence t_shuffle: "t \<in> LCons (\<sigma>, \<sigma>) ys \<sha> zs"
        by (metis zero(2) lappend_code(1))
      hence t'_shuffle: "ldeleteLeft_nat 0 t \<in> ys \<sha> zs"
        by (metis tshuffle_left_LCons)
      from t_shuffle have t_not_LNil: "t \<noteq> LNil"
        by (auto simp add: tshuffle_words_def)
      from t_shuffle and zs_not_LNil have ltl_t_not_LNil: "ltl t \<noteq> LNil"
        apply (auto simp add: tshuffle_words_def rights_def lefts_def)
        by (metis (lifting) LNil_preserve lefts_def_var lefts_ltake_right lfilter_LCons lfilter_LNil llist.collapse llist.distinct(1) ltakeWhile_LCons ltakeWhile_eq_LNil_iff t_not_LNil)

      have [simp]: "llist_Case LNil (\<lambda>x' xs'. xs') (ldropWhile is_right (traj t)) = ltl (ldropWhile is_right (traj t))"
        by (simp add: llist_Case_def ltl_def)

      have "lmap \<langle>id,id\<rangle> (LCons (\<sigma>, \<sigma>) ys \<triangleright> traj t \<triangleleft> zs) = lmap \<langle>id,id\<rangle> (LCons (\<sigma>,\<sigma>) ys \<triangleright> ?TR (traj t) \<frown> ?DR (traj t) \<triangleleft> zs)"
        by (metis lappend_ltakeWhile_ldropWhile)
      also have "... = lmap \<langle>id,id\<rangle> ((LNil \<triangleright> ?TR (traj t) \<triangleleft> \<up> (llength (\<rr> (?TR (traj t)))) zs) \<frown>
                                    (LCons (\<sigma>,\<sigma>) ys \<triangleright> ?DR (traj t) \<triangleleft> \<down> (llength (\<rr> (?TR (traj t)))) zs))"
        apply (subst intro_traj)
        apply (subst traj_lappend)
        apply (subst interleave_append[OF t_shuffle])
        apply (metis intro_traj lappend_ltakeWhile_ldropWhile traj_interleave)
        by simp
      also have "... = lmap \<langle>id,id\<rangle> ((LNil \<triangleright> ?TR (traj t) \<triangleleft> \<up> (llength (\<rr> (?TR (traj t)))) zs) \<frown>
                                     LCons (Inl (\<sigma>,\<sigma>)) (ys \<triangleright> ltl (?DR (traj t)) \<triangleleft> \<down> (llength (\<rr> (?TR (traj t)))) zs))"
        apply (subst interleave_ldropWhile)
        apply (subst shuffle_lset[OF t_shuffle])
        by (simp_all add: interleave_left)
      also have "... = lmap \<langle>id,id\<rangle> (LNil \<triangleright> ?TR (traj t) \<triangleleft> \<up> (llength (\<rr> (?TR (traj t)))) zs) \<frown>
                       LCons (\<sigma>,\<sigma>) (lmap \<langle>id,id\<rangle> (ys \<triangleright> ltl (?DR (traj t)) \<triangleleft> \<down> (llength (\<rr> (?TR (traj t)))) zs))"
        by (simp add: lmap_lappend_distrib)
      also have "... \<in> stutter (lmap \<langle>id,id\<rangle> (ys \<triangleright> ldeleteLeft_nat 0 (traj t) \<triangleleft> zs))"
        apply (rule stutter)
        apply (simp only: ldeleteLeft_nat.simps)
        apply (subst interleave_append[OF t'_shuffle])
        apply simp
        apply (simp only: lefts_ltake_right llength_LNil ltake_0 ldrop_0 lmap_lappend_distrib)
        apply (rule stutter_refl_var)
        apply simp
        apply (rule sumlist_cases[of t])
        apply (simp add: traj_not_LNil)
        apply (metis ltl_simps(2) ltl_t_not_LNil)
        apply simp
        by (metis t_not_LNil)
      finally have ?case
          by auto
    }
    moreover
    {
      assume zs_LNil: "zs = LNil"
      from zero have [simp]: "xs = LNil"
        by (metis llength_eq_0 zero_enat_def)
      from zs_LNil and zero have ?case
        by (simp add: interleave_only_left interleave_left)
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
    have ind_shuffle: "ltl (ldropWhile is_right t) \<in> (xs' \<frown> LCons (\<sigma>, \<sigma>) ys) \<sha> \<down> (llength (\<rr> (?TR (traj t)))) zs"
      apply (auto simp add: lefts_def tshuffle_words_def xs_def)
      apply (metis Not_is_left ltl_lfilter ltl_lmap ltl_simps(2))
      apply (simp add: lefts_def rights_def ldropWhile_def)
      apply (rule arg_cong) back
      apply (subst lfilter_ldrop)
      apply (rule arg_cong) back
      by (metis diverge_lfilter_LNil lappend_ltakeWhile_ldropWhile lfilter_left_right lset_ltakeWhileD ltake_all ltake_lappend1 not_is_left order_refl)

    from Suc(1)[OF xs'_len ind_shuffle]
    have ih: "lmap \<langle>id,id\<rangle> (xs' \<frown> LCons (\<sigma>, \<sigma>) ys \<triangleright> ltl (?DR (traj t)) \<triangleleft> \<down> (llength (\<rr> (?TR (traj t)))) zs)
             \<in> stutter (lmap \<langle>id,id\<rangle> (xs' \<frown> ys \<triangleright> ldeleteLeft_nat n (ltl (?DR (traj t))) \<triangleleft> \<down> (llength (\<rr> (?TR (traj t)))) zs))"
      by simp

    hence ih_var: "ltakeWhile is_right (traj t) = LNil \<Longrightarrow>
      lmap \<langle>id,id\<rangle> (xs' \<frown> LCons (\<sigma>, \<sigma>) ys \<triangleright> ltl (?DR (traj t)) \<triangleleft> zs)
      \<in> stutter (lmap \<langle>id,id\<rangle> (xs' \<frown> ys \<triangleright> ldeleteLeft_nat n (ltl (?DR (traj t))) \<triangleleft> zs))"
      by (auto simp del: ltakeWhile_eq_LNil_iff)

    have "lmap \<langle>id,id\<rangle> (xs \<frown> LCons (\<sigma>,\<sigma>) ys \<triangleright> traj t \<triangleleft> zs) = lmap \<langle>id,id\<rangle> (xs \<frown> LCons (\<sigma>,\<sigma>) ys \<triangleright> ?TR (traj t) \<frown> ?DR (traj t) \<triangleleft> zs)"
      by (metis lappend_ltakeWhile_ldropWhile)
    also have "... = lmap \<langle>id,id\<rangle> ((LNil \<triangleright> ?TR (traj t) \<triangleleft> \<up> (llength (\<rr> (?TR (traj t)))) zs) \<frown>
                                  (xs \<frown> LCons (\<sigma>, \<sigma>) ys \<triangleright> ?DR (traj t) \<triangleleft> \<down> (llength (\<rr> (?TR (traj t)))) zs))"
      by (subst interleave_append[OF Suc(3)]) simp_all
    also have "... = lmap \<langle>id,id\<rangle> ((LNil \<triangleright> ?TR (traj t) \<triangleleft> \<up> (llength (\<rr> (?TR (traj t)))) zs) \<frown>
                                  (xs \<frown> LCons (\<sigma>, \<sigma>) ys \<triangleright> LCons (Inl ()) (ltl (?DR (traj t))) \<triangleleft> \<down> (llength (\<rr> (?TR (traj t)))) zs))"
        apply (subst interleave_ldropWhile)
        apply (subst shuffle_lset[OF Suc(3)])
        apply auto
        apply (rule_tac x = "Inl (\<sigma>,\<sigma>)" in bexI)
        apply auto
        apply (subgoal_tac "lfinite xs")
        apply (metis imageI in_lset_lappend_iff lset_intros(1))
        by (metis xs_lfinite)
    also have "... = lmap \<langle>id,id\<rangle> ((LNil \<triangleright> ?TR (traj t) \<triangleleft> \<up> (llength (\<rr> (?TR (traj t)))) zs) \<frown>
                                  LCons (Inl x') (xs' \<frown> LCons (\<sigma>, \<sigma>) ys \<triangleright> ltl (?DR (traj t)) \<triangleleft> \<down> (llength (\<rr> (?TR (traj t)))) zs))"
      by (metis (hide_lams, no_types) calculation interleave_left lappend_code(2) lhd_LCons ltl_simps(2) xs_def)
    also have "... = lmap \<langle>id,id\<rangle> (LNil \<triangleright> ?TR (traj t) \<triangleleft> \<up> (llength (\<rr> (?TR (traj t)))) zs) \<frown>
                     LCons x' (lmap \<langle>id,id\<rangle> (xs' \<frown> LCons (\<sigma>, \<sigma>) ys \<triangleright> ltl (?DR (traj t)) \<triangleleft> \<down> (llength (\<rr> (?TR (traj t)))) zs))"
      by (simp add: lmap_lappend_distrib)
    also have "... \<in> stutter (lmap \<langle>id,id\<rangle> (xs \<frown> ys \<triangleright> ltakeWhile is_right (traj t) \<frown> llist_Case LNil (\<lambda>x' xs'. LCons x' (ldeleteLeft_nat n xs')) (ldropWhile is_right (traj t)) \<triangleleft> zs))" (is "?goal")
    proof (cases "ltakeWhile is_right (traj t) = LNil")
      case True
      moreover have "traj (?DR t) = LCons (Inl ()) (traj (ltl (?DR t)))"
        by (metis (full_types) `ldropWhile is_right (traj t) \<noteq> LNil` ldropWhile_right_traj ldropWhile_rights_not_LNil ltl_traj)
      ultimately show ?goal
        by (auto intro!: ih_var[simplified] stutter_LCons simp add: llist_Case_def xs_def interleave_left)
    next
      case False
      have traj_DR: "traj (?DR t) = LCons (Inl ()) (traj (ltl (?DR t)))"
        by (metis (full_types) `ldropWhile is_right (traj t) \<noteq> LNil` ldropWhile_right_traj ldropWhile_rights_not_LNil ltl_traj)
      have ltl_DR: "lfilter is_left (ltl (?DR t)) = ltl (lfilter is_left t)"
        apply (subst lappend_ltakeWhile_ldropWhile[symmetric, of t is_right]) back
        apply (subst lfilter_lappend_lfinite)
        apply (metis ldropWhile_eq_LNil_iff lfinite_ltakeWhile llist.discI traj_DR traj_not_LNil)
        apply (subst lhd_LCons_ltl[symmetric, of "ldropWhile is_right t"]) back
        apply (metis `ldropWhile is_right (traj t) \<noteq> LNil` ldropWhile_right_traj traj_not_LNil)
        apply (subst prem_lhd)
        by simp
      show ?goal
        apply (subst interleave_append_llength)
        prefer 3
        apply (subst lmap_lappend_distrib)
        apply (rule stutter_lappend)
        apply simp
        apply (rule stutter_refl_var)
        apply (simp add: False[simplified])
        apply (simp add: traj_DR llist_Case_def xs_def interleave_left)
        apply (rule stutter_LCons)
        apply (rule ih[simplified])
        using Suc(3)
        apply (auto simp add: tshuffle_words_def traj_DR llist_Case_def)
        apply (subst llength_lefts_lappend)
        apply (simp add: traj_def)
        apply (metis lappend_code(2) lefts_LCons_lfinite_rights xs_def)
        apply simp
        prefer 2
        apply (subst llength_rights_lappend)
        apply (simp add: traj_def)
        apply (metis lappend_code(2) lefts_LCons_lfinite_rights xs_def)
        apply (subst lappend_ltakeWhile_ldropWhile[symmetric, of t is_right]) back back
        apply (simp del: lappend_ltakeWhile_ldropWhile)
        apply (subst llength_rights_lappend)
        apply (metis lappend_code(2) lefts_LCons_lfinite_rights xs_def)
        apply simp
        apply (simp add: lefts_def)
        apply (subst eSuc_move)
        apply (metis Suc.prems(1) Zero_not_Suc enat.inject plus_enat_eq_0_conv zero_enat_def)
        apply (subst lfilter_ldeleteLeft_nat)
        apply (erule rev_mp)
        apply (subst lmap_unl_Inl)
        apply simp
        apply (rule impI)
        apply (subst llength_ldelete_nat)
        defer
        apply (rule arg_cong) back
        apply (simp add: ltl_DR)
        apply (metis eSuc_plus iadd_Suc_right llength_LCons ltl_simps(2) xs_def)
        apply (simp add: ltl_DR xs_def)
        using xs'_len by auto
    qed
    finally show ?case
      by auto (metis (full_types) ldeleteLeft_nat.simps(2) ldeleteLeft_nat_traj ldropWhile_right_traj ltakeWhile_right_traj traj_lappend)
  qed
  ultimately show ?thesis
    by simp
qed

lemma lmap_LConsl: "lmap \<langle>id,id\<rangle> (LCons (Inl x) xs) = LCons x (lmap \<langle>id,id\<rangle> xs)"
  by auto

lemma [simp]: "llength (\<ll> (ldropWhile is_right t)) = llength (\<ll> t)"
  by (auto simp add: lefts_def)

lemma [intro]: "LCons (\<sigma>, \<sigma>'') xs \<in> stutter (LCons (\<sigma>, \<sigma>') (LCons (\<sigma>', \<sigma>'') xs))"
proof -
  have "LCons (\<sigma>, \<sigma>) (LCons (\<sigma>, \<sigma>') (LCons (\<sigma>', \<sigma>'') xs)) \<in> stutter (LCons (\<sigma>, \<sigma>') (LCons (\<sigma>', \<sigma>'') xs))"
    by (metis stutter.self)
  thus "LCons (\<sigma>,\<sigma>'') xs \<in> stutter (LCons (\<sigma>, \<sigma>') (LCons (\<sigma>', \<sigma>'') xs))"
    by (metis lappend_code(1) stutter.mumble)
qed

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
  shows "lmap \<langle>id,id\<rangle> (xs \<frown> LCons (\<sigma>, \<sigma>'') ys \<triangleright> traj t \<triangleleft> zs) \<in> stutter (lmap \<langle>id,id\<rangle> (xs \<frown> LCons (\<sigma>,\<sigma>') (LCons (\<sigma>',\<sigma>'') ys) \<triangleright> linsertLeft (llength xs) () (traj t) \<triangleleft> zs))"
proof (cases "llength xs")
  assume "llength xs = \<infinity>"
  from this and assms show ?thesis
    by (auto intro: stutter_refl_var sumlist_cases[of t] simp add: traj_def interleave_left interleave_right)
next
  let ?TR = "ltakeWhile is_right"
  let ?DR = "ldropWhile is_right"

  fix n
  assume "llength xs = enat n"
  moreover hence "lmap \<langle>id,id\<rangle> (xs \<frown> LCons (\<sigma>, \<sigma>'') ys \<triangleright> traj t \<triangleleft> zs) \<in> stutter (lmap \<langle>id,id\<rangle> (xs \<frown> LCons (\<sigma>,\<sigma>') (LCons (\<sigma>',\<sigma>'') ys) \<triangleright> linsertLeft_nat n () (traj t) \<triangleleft> zs))"
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
      also have "... \<in> stutter (lmap \<langle>id,id\<rangle> (LCons (\<sigma>, \<sigma>') (LCons (\<sigma>', \<sigma>'') ys) \<triangleright> linsertLeft_nat 0 () (traj t) \<triangleleft> zs))"
        apply (rule mumble[where \<sigma>' = \<sigma>'])
        apply (simp only: linsertLeft_nat.simps)
        apply (subst interleave_append_llength)
        prefer 3
        apply (subst traj_DR) back
        apply (simp only: lefts_ltake_right llength_LNil ltake_0 ldrop_0 lmap_lappend_distrib interleave_left lhd_LCons lmap_LConsl ltl_simps)
        apply (rule stutter_refl_var)
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
        by (auto simp add: interleave_left interleave_only_left)
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
             \<in> stutter (lmap \<langle>id,id\<rangle> (xs' \<frown> LCons (\<sigma>, \<sigma>') (LCons (\<sigma>', \<sigma>'') ys) \<triangleright> linsertLeft_nat n () (ltl (?DR (traj t))) \<triangleleft> \<down> (llength (\<rr> (?TR (traj t)))) zs))"
      by simp

    hence ih_var: "ltakeWhile is_right (traj t) = LNil \<Longrightarrow>
      lmap \<langle>id,id\<rangle> (xs' \<frown> LCons (\<sigma>, \<sigma>'') ys \<triangleright> ltl (?DR (traj t)) \<triangleleft> zs)
      \<in> stutter (lmap \<langle>id,id\<rangle> (xs' \<frown> LCons (\<sigma>, \<sigma>') (LCons (\<sigma>', \<sigma>'') ys) \<triangleright> linsertLeft_nat n () (ltl (?DR (traj t))) \<triangleleft> zs))"
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
    also have "... \<in> stutter (lmap \<langle>id,id\<rangle> (xs \<frown> LCons (\<sigma>, \<sigma>') (LCons (\<sigma>', \<sigma>'') ys) \<triangleright> linsertLeft_nat (Suc n) () (traj t) \<triangleleft> zs))" (is ?goal)
    proof (cases "ltakeWhile is_right (traj t) = LNil")
      case True
      moreover have "traj (?DR t) = LCons (Inl ()) (traj (ltl (?DR t)))"
        by (metis (full_types) `ldropWhile is_right (traj t) \<noteq> LNil` ldropWhile_right_traj ldropWhile_rights_not_LNil ltl_traj)
      ultimately show ?goal
        by (auto intro!: ih_var[simplified] stutter_LCons simp add: xs_def llist_Case_def interleave_left)
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
        apply (rule stutter_lappend)
        apply simp
        apply (rule stutter_refl_var)
        apply (simp add: False[simplified])
        apply (subst traj_DR) back
        apply (simp add: llist_Case_def xs_def interleave_left)
        apply (rule stutter_LCons)
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

lemma tshuffle_stutter: "\<Union>{lmap \<langle>id,id\<rangle> ` (xs' \<sha> ys)|xs'. xs' \<in> stutter xs} \<subseteq> (lmap \<langle>id,id\<rangle> ` (xs \<sha> ys))\<^sup>\<dagger>"
proof -
  {
  fix xs' zs'

  assume "xs' \<in> stutter xs" and "zs' \<in> xs' \<sha> ys"

  hence "\<exists>zs\<in>xs \<sha> ys. lmap \<langle>id,id\<rangle> zs' \<in> stutter (lmap \<langle>id,id\<rangle> zs)"
  proof (induct xs' arbitrary: zs' rule: stutter.induct)
    case (self \<sigma> zs')

    hence zs'_interleave: "zs' = LCons (\<sigma>, \<sigma>) xs \<triangleright> traj zs' \<triangleleft> ys"
        by (auto simp add: tshuffle_words_def) (metis reinterleave)

    {
      assume ys_not_LNil: "ys \<noteq> LNil"

      from self and ys_not_LNil
      have zs'_traj: "traj zs' = traj (ltakeWhile is_right zs') \<frown> LCons (Inl ()) (traj (ltl (ldropWhile is_right zs')))"
        apply (auto simp: tshuffle_words_def lefts_def lmap_unl_Inl rights_def lmap_unr_Inr)
        apply (subst lappend_ltakeWhile_ldropWhile[symmetric, of zs' is_right])
        apply (subst traj_lappend)
        apply (cases "lfinite (ltakeWhile is_right zs')")
        apply (rule arg_cong) back
        apply (metis (mono_tags) interleave_ldropWhile ldropWhile_right_traj lset_intros(1) lset_lfilter_var ltl_traj)
        by (metis lfilter_lefts_LCons_lfinite_rights)

      from self
      have l1: "llength (\<ll> (traj (ltakeWhile is_right zs') \<frown> LCons (Inl ()) (traj (ltl (ldropWhile is_right zs'))))) = llength (LCons (\<sigma>, \<sigma>) xs)"
        apply (auto simp add: tshuffle_words_def lefts_def rights_def lmap_unl_Inl lmap_unr_Inr)
        apply (cases "lfinite (ltakeWhile is_right zs')")
        apply (subst lfilter_lappend_lfinite)
        apply (simp add: traj_def)
        by simp_all

      from self
      have l2: "llength (\<rr> (traj (ltakeWhile is_right zs') \<frown> LCons (Inl ()) (traj (ltl (ldropWhile is_right zs'))))) = llength ys"
        apply (auto simp add: tshuffle_words_def lefts_def rights_def lmap_unl_Inl lmap_unr_Inr)
        apply (cases "lfinite (ltakeWhile is_right zs')")
        apply (metis lfilter_right_traj llength_traj lmap_const_llength lmap_override zs'_traj)
        by simp
      
      from self
      have l3: "llength (\<ll> (traj (ltakeWhile is_right zs') \<frown> traj (ltl (ldropWhile is_right zs')))) = llength xs"
        apply (auto simp add: tshuffle_words_def lefts_def rights_def lmap_unl_Inl lmap_unr_Inr)
        apply (cases "lfinite (ltakeWhile is_right zs')")
        apply (subst lfilter_lappend_lfinite)
        apply (simp add: traj_def)
        by simp_all

      from self
      have l4: "llength (\<rr> (traj (ltakeWhile is_right zs') \<frown> traj (ltl (ldropWhile is_right zs')))) = llength ys"
        apply (auto simp add: tshuffle_words_def lefts_def rights_def lmap_unl_Inl lmap_unr_Inr)
        apply (cases "lfinite (ltakeWhile is_right zs')")
        apply (subst lfilter_lappend_lfinite)
        apply (simp add: traj_def)
        apply simp_all
        apply (subgoal_tac "llength ys = llength (lfilter is_right zs')")
        apply (rotate_tac 3)
        apply (erule ssubst)
        apply (subst llength_lappend[symmetric])
        apply (rule arg_cong) back
        by simp_all

      have "\<exists>zs\<in>xs \<sha> ys. lmap \<langle>id,id\<rangle> zs' \<in> stutter (lmap \<langle>id,id\<rangle> zs)"
      proof (rule_tac x = "xs \<triangleright> traj (ldeleteLeft 0 zs') \<triangleleft> ys" in bexI)
        have "lmap \<langle>id,id\<rangle> (LCons (\<sigma>, \<sigma>) xs \<triangleright> traj zs' \<triangleleft> ys) \<in> stutter (lmap \<langle>id,id\<rangle> (xs \<triangleright> traj (ldeleteLeft 0 zs') \<triangleleft> ys))"
          apply (simp add: enat_0[symmetric])
          apply (subst zs'_traj)
          apply (cases "ltakeWhile is_right zs' = LNil")
          apply (simp add: interleave_left del: ltakeWhile_eq_LNil_iff)
          apply (simp only: interleave_append_llength[OF l1 l2] interleave_append_llength[OF l3 l4] lmap_lappend_distrib)
          apply (rule stutter_lappend)
          apply simp
          apply (rule stutter_refl_var)
          apply simp
          apply (metis ltakeWhile_eq_LNil_iff traj_not_LNil)
          by (simp add: interleave_left)
        thus "lmap \<langle>id,id\<rangle> zs' \<in> stutter (lmap \<langle>id,id\<rangle> (xs \<triangleright> traj (ldeleteLeft 0 zs') \<triangleleft> ys))"
          by (subst zs'_interleave) simp
        from self
        show "xs \<triangleright> traj (ldeleteLeft 0 zs') \<triangleleft> ys \<in> xs \<sha> ys"
          apply (auto simp add: tshuffle_words_def)
          apply (subst lefts_interleave_llength)
          apply simp_all
          defer
          apply (subst rights_interleave_llength)
          apply (simp_all add: enat_0[symmetric])
          apply (cases "lfinite (ltakeWhile is_right zs')")
          apply (subst llength_rights_lappend)
          apply auto
          apply (metis lfinite_traj reinterleave)
          apply (metis lappend_ltakeWhile_ldropWhile llength_rights_lappend)
          apply (metis lefts_LCons_lfinite_rights)
          by (metis (lifting, full_types) ldeleteLeft_nat.simps(1) mem_Collect_eq self.prems tshuffle_left_LCons tshuffle_words_def)
      qed
    }
    moreover
    {
      assume "ys = LNil"

      from this and self
      have [simp]: "traj zs' = LCons (Inl ()) (lmap (\<lambda>x. Inl ()) xs)"
        by (auto simp add: tshuffle_words_def lefts_def rights_def lmap_unl_Inl)

      from `ys = LNil` and zs'_interleave[simplified]
      have "\<exists>zs\<in>xs \<sha> ys. lmap \<langle>id,id\<rangle> zs' \<in> stutter (lmap \<langle>id,id\<rangle> zs)"
        by (simp add: interleave_left interleave_only_left)
    }
    ultimately show ?case
      by (cases ys) simp_all
  next
    case (stutter ws vs \<sigma> zs')

    from stutter(3)
    have zs'_interleave: "zs' = ws \<frown> LCons (\<sigma>, \<sigma>) vs \<triangleright> traj zs' \<triangleleft> ys"
      by (simp add: tshuffle_words_def) (metis reinterleave)

    from stutter(3)
    have "ws \<frown> vs \<triangleright> ldeleteLeft (llength ws) (traj zs') \<triangleleft> ys \<in> (ws \<frown> vs) \<sha> ys"
      apply (auto simp add: tshuffle_words_def)
      apply (subst lefts_interleave_llength)
      apply simp_all
      apply (simp add: lefts_def)
      apply (subst lfilter_ldeleteLeft)
      apply (erule rev_mp)
      apply (subst lmap_unl_Inl)
      apply simp
      apply (rule impI)
      apply simp
      apply (metis (hide_lams, no_types) ldelete_llength_lappend llcp_lappend_same llcp_same_conv_length llength_lmap llist.simps(19) lmap_lappend_distrib)
      apply (subst rights_interleave_llength)
      apply (simp_all add: rights_def)
      apply (cases "llength ws")
      by simp_all

    from this and stutter(2) obtain zs where "zs \<in> xs \<sha> ys"
    and "lmap \<langle>id,id\<rangle> (ws \<frown> vs \<triangleright> ldeleteLeft (llength ws) (traj zs') \<triangleleft> ys) \<in> stutter (lmap \<langle>id,id\<rangle> zs)"
      by blast

    moreover have "lmap \<langle>id,id\<rangle> zs' \<in> stutter (lmap \<langle>id,id\<rangle> (ws \<frown> vs \<triangleright> ldeleteLeft (llength ws) (traj zs') \<triangleleft> ys))"
      by (subst zs'_interleave) (rule stutter_in_left[OF stutter(3)])

    ultimately show ?case
      by (metis (hide_lams, no_types) stutter_trans)
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
    and "lmap \<langle>id,id\<rangle> (ws \<frown> LCons (\<sigma>,\<sigma>') (LCons (\<sigma>',\<sigma>'') vs) \<triangleright> linsertLeft (llength ws) () (traj zs') \<triangleleft> ys) \<in> stutter (lmap \<langle>id,id\<rangle> zs)"
      by blast

    moreover have "lmap \<langle>id,id\<rangle> zs' \<in> stutter (lmap \<langle>id,id\<rangle> (ws \<frown> LCons (\<sigma>,\<sigma>') (LCons (\<sigma>',\<sigma>'') vs) \<triangleright> linsertLeft (llength ws) () (traj zs') \<triangleleft> ys))"
      by (subst zs'_interleave) (metis (full_types) mumble.prems mumble_in_left)
 
    ultimately show ?case
      by (metis (hide_lams, no_types) stutter_trans)
  qed
  }
  thus ?thesis
    by (auto simp add: Stutter_def) (metis (full_types) imageI)
qed

lemma shuffle_stutter1: "X\<^sup>\<dagger> \<parallel> Y \<subseteq> (X \<parallel> Y)\<^sup>\<dagger>"
proof -
  have "X\<^sup>\<dagger> \<parallel> Y = \<Union>(stutter ` X) \<parallel> Y"
    by (rule arg_cong, auto simp add: Stutter_def image_def)
 also have "... = \<Union>{stutter xs \<parallel> Y|xs. xs \<in> X}"
    by (subst trans[OF shuffle_comm shuffle_inf_dist], subst shuffle_comm, auto)
  also have "... = \<Union>{\<Union>{lmap \<langle>id,id\<rangle> ` (xs' \<sha> ys) |xs' ys. xs' \<in> stutter xs \<and> ys \<in> Y}|xs. xs \<in> X}"
    by (simp add: shuffle_def)
  also have "... = \<Union>{\<Union>{lmap \<langle>id,id\<rangle> ` (xs' \<sha> ys) |xs'. xs' \<in> stutter xs}|xs ys. xs \<in> X \<and> ys \<in> Y}"
    by blast
  also have "... \<subseteq> \<Union>{(lmap \<langle>id,id\<rangle> ` (xs \<sha> ys))\<^sup>\<dagger>|xs ys. xs \<in> X \<and> ys \<in> Y}"
    by (insert tshuffle_stutter) blast
  also have "... = \<Union>{\<Union>zs\<in>xs \<sha> ys. stutter (lmap \<langle>id,id\<rangle> zs)|xs ys. xs \<in> X \<and> ys \<in> Y}"
    by (auto simp add: Stutter_def)
  also have "... = (X \<parallel> Y)\<^sup>\<dagger>"
    by (simp add: shuffle_def Stutter_def) blast
  finally show ?thesis .
qed

lemma stutter_LNil_lfinite: "ys \<in> stutter LNil \<Longrightarrow> lfinite ys"
  by (induct ys rule: stutter.induct) auto

lemma stutter_in_LNil: "stutter xs \<subseteq> (\<Union>{lmap \<langle>id,id\<rangle> ` (xs' \<sha> ys') |xs' ys'. xs' \<in> stutter xs \<and> ys' \<in> stutter LNil})\<^sup>\<dagger>"
proof
  fix zs
  assume "zs \<in> stutter xs"
  also have "... \<subseteq> {LCons (fst (lhd zs), fst (lhd zs)) zs |zs. zs \<in> stutter xs}\<^sup>\<dagger>"
  proof
    fix zs
    assume "zs \<in> stutter xs"
    thus "zs \<in> {LCons (fst (lhd zs), fst (lhd zs)) zs |zs. zs \<in> stutter xs}\<^sup>\<dagger>"
      apply (induct zs rule: stutter.induct)
      apply (auto simp add: Stutter_def)
      apply (rule_tac x = "stutter (LCons (\<sigma>,\<sigma>) (LCons (\<sigma>,\<sigma>) xs))" in exI)
      by (auto intro: stutter_refl)
  qed
  also have "... = {LCons (fst (lhd zs), fst (lhd zs)) zs |zs. zs \<in> stutter xs \<and> LCons (fst (lhd zs), fst (lhd zs)) LNil \<in> stutter LNil}\<^sup>\<dagger>"
    by (metis stutter.self)
  also have "... \<subseteq> {LCons (\<sigma>,\<sigma>) zs |\<sigma> zs. zs \<in> stutter xs \<and> LCons (\<sigma>,\<sigma>) LNil \<in> stutter LNil}\<^sup>\<dagger>"
    by (rule Stutter_iso) blast
  also have "... = {LCons (\<sigma>,\<sigma>) LNil \<frown> zs |\<sigma> zs. zs \<in> stutter xs \<and> LCons (\<sigma>,\<sigma>) LNil \<in> stutter LNil}\<^sup>\<dagger>"
    by (metis lappend_code(1) lappend_code(2) stutter.self)
  also have "... \<subseteq> {ys \<frown> zs |ys zs. zs \<in> stutter xs \<and> ys \<in> stutter LNil}\<^sup>\<dagger>"
    by (rule Stutter_iso) blast
  also have "... \<subseteq> (\<Union>{lmap \<langle>id,id\<rangle> ` (xs' \<sha> ys') |xs' ys'. xs' \<in> stutter xs \<and> ys' \<in> stutter LNil})\<^sup>\<dagger>"
    apply (rule Stutter_iso)
    apply auto
    apply (rule_tac x = "lmap \<langle>id,id\<rangle> ` (zs \<sha> ys)" in exI)
    apply (intro conjI)
    apply (rule_tac x = zs in exI)
    apply (rule_tac x = ys in exI)
    apply (auto dest!: stutter_LNil_lfinite)
    by (metis lfinite_lappend_shuffle tshuffle_words_comm)
  finally show "zs \<in> (\<Union>{lmap \<langle>id,id\<rangle> ` (xs' \<sha> ys') |xs' ys'. xs' \<in> stutter xs \<and> ys' \<in> stutter LNil})\<^sup>\<dagger>" .
qed

lemma stutter_in_LNil_var: "stutter xs \<subseteq> (\<Union>{lmap \<langle>id,id\<rangle> ` (xs \<sha> ys) |ys. ys \<in> stutter LNil})\<^sup>\<dagger>"
  sorry

lemma set_comp_fun_sub1: "(\<And>x. x \<in> X \<Longrightarrow> f x \<subseteq> g x) \<Longrightarrow> \<Union>{f x |x. x \<in> X} \<subseteq> \<Union>{g x |x. x \<in> X}"
  by auto

lemma LNil_Stutter: "X\<^sup>\<dagger> \<subseteq> ({LNil}\<^sup>\<dagger> \<parallel> X\<^sup>\<dagger>)\<^sup>\<dagger>"
proof -
  have "X\<^sup>\<dagger> = \<Union>{stutter xs |xs. xs \<in> X}"
    by (simp add: Stutter_def)
  also have "... \<subseteq> \<Union>{(\<Union>{lmap \<langle>id,id\<rangle> ` (xs' \<sha> ys') |xs' ys'. xs' \<in> stutter xs \<and> ys' \<in> stutter LNil})\<^sup>\<dagger> |xs. xs \<in> X}"
    by (rule set_comp_fun_sub1) (metis stutter_in_LNil)
  also have "... = (\<Union>{\<Union>{lmap \<langle>id,id\<rangle> ` (xs' \<sha> ys') |xs' ys'. xs' \<in> stutter xs \<and> ys' \<in> stutter LNil} |xs. xs \<in> X})\<^sup>\<dagger>"
    by (subst Stutter_continuous, blast)
  also have "... = (\<Union>{lmap \<langle>id,id\<rangle> ` (xs' \<sha> ys') |xs' ys' xs. xs' \<in> stutter xs \<and> ys' \<in> stutter LNil \<and>  xs \<in> X})\<^sup>\<dagger>"
    by (rule arg_cong, blast)
  also have "... = (\<Union>{lmap \<langle>id,id\<rangle> ` (xs' \<sha> ys') |xs' ys'. xs' \<in> X\<^sup>\<dagger> \<and> ys' \<in> {LNil}\<^sup>\<dagger>})\<^sup>\<dagger>"
    apply (rule arg_cong) back by (simp add: Stutter_def, blast)
  also have "... = (X\<^sup>\<dagger> \<parallel> {LNil}\<^sup>\<dagger>)\<^sup>\<dagger>"
    by (rule arg_cong, simp add: shuffle_def)
  finally show ?thesis
    by (metis shuffle_comm)
qed

lemma LNil_Stutter: "X\<^sup>\<dagger> \<subseteq> ({LNil}\<^sup>\<dagger> \<parallel> X)\<^sup>\<dagger>"
proof -
  have "X\<^sup>\<dagger> = \<Union>{stutter xs |xs. xs \<in> X}"
    by (simp add: Stutter_def)
  also have "... \<subseteq> \<Union>{(\<Union>{lmap \<langle>id,id\<rangle> ` (xs' \<sha> ys') |xs' ys'. xs' \<in> stutter xs \<and> ys' \<in> stutter LNil})\<^sup>\<dagger> |xs. xs \<in> X}"
    by (rule set_comp_fun_sub1) (metis stutter_in_LNil)
  also have "... = \<Union>{(X \<parallel> )\<^sup>\<dagger> |xs. xs \<in> X}"
  also have "... = (\<Union>{\<Union>{lmap \<langle>id,id\<rangle> ` (xs' \<sha> ys') |xs' ys'. xs' \<in> stutter xs \<and> ys' \<in> stutter LNil} |xs. xs \<in> X})\<^sup>\<dagger>"
    by (subst Stutter_continuous, blast)
  also have "... = (\<Union>{lmap \<langle>id,id\<rangle> ` (xs' \<sha> ys') |xs' ys' xs. xs' \<in> stutter xs \<and> ys' \<in> stutter LNil \<and>  xs \<in> X})\<^sup>\<dagger>"
    by (rule arg_cong, blast)
  also have "... = (\<Union>{lmap \<langle>id,id\<rangle> ` (xs' \<sha> ys') |xs' ys'. xs' \<in> X\<^sup>\<dagger> \<and> ys' \<in> {LNil}\<^sup>\<dagger>})\<^sup>\<dagger>"
    apply (rule arg_cong) back by (simp add: Stutter_def, blast)
  also have "... = (X\<^sup>\<dagger> \<parallel> {LNil}\<^sup>\<dagger>)\<^sup>\<dagger>"
    by (rule arg_cong, simp add: shuffle_def)
  finally show ?thesis
    by (metis shuffle_comm)
qed

lemma Stutter_ext_var: "(X - {LNil}) \<subseteq> (X - {LNil})\<^sup>\<dagger>"
  by (auto simp add: Stutter_def, erule_tac x = "stutter x" in allE, auto)

lemma Stutter_shuffle [simp]: "(X\<^sup>\<dagger> \<parallel> Y)\<^sup>\<dagger> = (X \<parallel> Y)\<^sup>\<dagger>"
  apply (rule antisym)
  apply (metis (full_types) Stutter_idem Stutter_iso shuffle_comm shuffle_stutter1)
  apply (cases "LNil \<in> X")
  apply (subgoal_tac "X = (X - {LNil}) \<union> {LNil}")
  apply (rotate_tac 1)
  apply (erule ssubst)
  apply (simp only: par.distrib_left par.distrib_right par.mult_onel shuffle_one shuffle_one[symmetric] Stutter_union Un_assoc)
  apply (rule Un_mono)
  apply (intro Stutter_iso par.mult_isol_var[rule_format] Stutter_ext_var conjI order_refl)
  apply (rule Un_mono)
  apply (intro Stutter_iso par.mult_isol_var[rule_format] Stutter_ext_var conjI)
  apply (rule order_trans[OF Stutter_ext_var])
  sledgehammer


lemma [simp]: "\<langle>top\<rangle> \<cdot> X\<^sup>\<dagger> = X\<^sup>\<dagger>"
  sorry

lemma [simp]: "X\<^sup>\<dagger> \<cdot> \<langle>top\<rangle> = X\<^sup>\<dagger>"
  sorry

lemma Stutter_l_prod [simp]: "(X \<cdot> Y)\<^sup>\<dagger> = (X\<^sup>\<dagger> \<cdot> Y\<^sup>\<dagger>)\<^sup>\<dagger>"
  sorry

end

