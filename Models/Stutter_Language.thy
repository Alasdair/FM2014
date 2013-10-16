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

lemma [simp]: "\<langle>top\<rangle> \<cdot> X\<^sup>\<dagger> = X\<^sup>\<dagger>"
  sorry

lemma [simp]: "X\<^sup>\<dagger> \<cdot> \<langle>top\<rangle> = X\<^sup>\<dagger>"
  sorry

lemma Stutter_union [simp]: "(X \<union> Y)\<^sup>\<dagger> = X\<^sup>\<dagger> \<union> Y\<^sup>\<dagger>"
  by (auto simp add: Stutter_def)

lemma Stutter_continuous: "(\<Union>\<XX>)\<^sup>\<dagger> = \<Union>{X\<^sup>\<dagger> |X. X \<in> \<XX>}"
  by (auto simp add: Stutter_def) 

lemma Stutter_meet [simp]: "(X\<^sup>\<dagger> \<inter> Y\<^sup>\<dagger>)\<^sup>\<dagger> = X\<^sup>\<dagger> \<inter> Y\<^sup>\<dagger>"
  apply (auto dest: stutter_trans simp add: Stutter_def)
  by (metis neq_LNil_conv stutter_never_LNil stutter_refl)

lemma stutter_infinite [dest]: "ys \<in> stutter xs \<Longrightarrow> \<not> lfinite xs \<Longrightarrow> \<not> lfinite ys"
  by (induct ys rule: stutter.induct) auto

lemma Stutter_l_prod [simp]: "(X \<cdot> Y)\<^sup>\<dagger> = (X\<^sup>\<dagger> \<cdot> Y\<^sup>\<dagger>)\<^sup>\<dagger>"
  sorry

definition "llist_Case \<equiv> llist_case"

primrec ldeleteLeft_nat :: "nat \<Rightarrow> ('a + 'b) llist \<Rightarrow> ('a + 'b) llist" where
  "ldeleteLeft_nat 0 xs = ltakeWhile is_right xs \<frown> ltl (ldropWhile is_right xs)"
| "ldeleteLeft_nat (Suc n) xs = ltakeWhile is_right xs \<frown> llist_Case LNil(\<lambda>x' xs'. LCons x' (ldeleteLeft_nat n xs')) (ldropWhile is_right xs)"

primrec ldeleteLeft :: "enat \<Rightarrow> ('a + 'b) llist \<Rightarrow> ('a + 'b) llist" where
  "ldeleteLeft (enat n) xs = ldeleteLeft_nat n xs"
| "ldeleteLeft \<infinity> xs = xs"

definition linsertLeft :: "enat \<Rightarrow> 'a \<Rightarrow> ('a + 'b) llist \<Rightarrow> ('a + 'b) llist" where
  "linsertLeft n x xs = undefined"

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

lemma [simp]: "traj t \<noteq> LNil \<longleftrightarrow> t \<noteq> LNil"
  by (metis reinterleave traj_LNil traj_interleave)

lemma [simp]: "traj (ltakeWhile is_right t) = ltakeWhile is_right (traj t)"
  by (simp add: traj_def ltakeWhile_lmap)

lemma [simp]: "traj (ltakeWhile is_left t) = ltakeWhile is_left (traj t)"
  by (simp add: traj_def ltakeWhile_lmap)

lemma [simp]: "traj (ltl t) = ltl (traj t)"
  by (simp add: traj_def)

lemma [simp]: "traj (ldropWhile is_right t) = ldropWhile is_right (traj t)"
  by (simp add: traj_def ldropWhile_lmap)

lemma [simp]: "traj (ldropWhile is_left t) = ldropWhile is_left (traj t)"
  by (simp add: traj_def ldropWhile_lmap)  

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


lemma [simp]: "traj (LCons x xs) = LCons (\<langle>\<lambda>x. Inl (),\<lambda>x. Inr ()\<rangle> x) (traj xs)"
  by (simp add: traj_def)

lemma traj_llist_Case [simp]:
  fixes ys :: "('a + 'b) llist"
  shows "traj (llist_Case LNil (\<lambda>x xs. xs) ys) = llist_Case LNil (\<lambda>x xs. xs) (traj ys)"
  by (cases ys) (simp_all add: llist_Case_def)
lemma [simp]: "traj (llist_Case LNil (\<lambda>x xs. f xs) ys) = llist_Case LNil (\<lambda>x xs. f xs) (traj ys)"
  by (cases ys) simp_all

lemma [simp]: "traj (ldeleteLeft_nat 0 t) = ldeleteLeft_nat 0 (traj t)"
  by simp

lemma llength_ldropWhile_traj [simp]: "llength (ldropWhile is_right (traj xs)) = llength (ldropWhile is_right xs)"
  sorry

lemma ldropWhile_right_LCons [dest!]: "ldropWhile is_right t = LCons x xs \<Longrightarrow> \<exists>x'. ldropWhile is_right t = LCons (Inl x') xs"
  sorry

lemma [simp]: "traj (ldeleteLeft_nat n t) = ldeleteLeft_nat n (traj t)"
proof (induct n arbitrary: t)
  case 0 show ?case by simp
next
  case (Suc n)
  thus ?case
    apply auto
    apply (rule arg_cong) back
    apply (simp add: llist_Case_def)
    apply (cases "ldropWhile is_right t")
    apply (simp del: ldropWhile_eq_LNil_iff)
    apply (metis llength_eq_0 llength_ldropWhile_traj llist.simps(4))
    apply (drule ldropWhile_right_LCons)
    apply (erule exE)
    apply simp
    sorry
qed

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

lemma [simp]: "llength (ltakeWhile is_right (traj t)) = llength (ltakeWhile is_right t)"
  sorry

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
  sorry

lemma lmap_unl_Inl: "(\<forall>x\<in>lset xs. is_left x) \<Longrightarrow> lmap unl xs = ys \<longleftrightarrow> xs = lmap Inl ys"
  apply (auto simp del: lmap.compositionality)
  apply (rule sym)
  apply (rule lmap2_id_var)
  apply auto
  by (metis is_left.simps(2) obj_sumE unl.simps(1))

lemma lset_lfilter: "x \<in> lset (lfilter P xs) \<Longrightarrow> x \<in> lset xs"
  sorry

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
        apply simp
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
    have [simp]: "lhd (ldropWhile is_right t) = Inl x'"
      apply (auto simp add: tshuffle_words_def lefts_def xs_def)
      sorry

    hence [simp]: "lhd (ldropWhile is_right (traj t)) = Inl ()"
      sorry

    from Suc(3)
    have "ldropWhile is_right (traj t) \<noteq> LNil"
      apply (auto simp add: tshuffle_words_def xs_def)
      apply (rule_tac x = "Inl ()" in bexI)
      apply simp
      apply (simp add: lefts_def traj_def image_def)
      apply (rule_tac x = "Inl x'" in bexI)
      apply simp
      apply (rule lset_lfilter[where P = is_left])
      apply (erule rev_mp)
      apply (subst lmap_unl_Inl)
      apply (metis (mono_tags) Coinductive_List.lset_lfilter mem_Collect_eq)
      by simp

    from Suc(3)
    have ind_shuffle': "ltakeWhile is_right t \<frown> LCons (Inl x') (ldeleteLeft_nat n (ltl (ldropWhile is_right t))) \<in> (xs \<frown> ys) \<sha> zs"
      apply (auto simp add: tshuffle_words_def xs_def)
      sorry

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
    also have "... \<in> stutter (lmap \<langle>id,id\<rangle> (xs \<frown> ys \<triangleright> ldeleteLeft_nat (Suc n) (traj t) \<triangleleft> zs))"
      apply (simp only: ldeleteLeft_nat.simps)
      apply (cases "ltakeWhile is_right (traj t) = LNil")
      apply (simp del: ltakeWhile_eq_LNil_iff)
      defer
      apply (subst interleave_append[OF ind_shuffle'])
      prefer 2
      apply (simp only: lmap_lappend_distrib)
      apply (rule stutter_lappend)
      defer
      apply (simp add: xs_def)
      apply (simp add: llist_Case_def)
      apply (subgoal_tac "ldropWhile is_right (traj t) = LCons (Inl ()) (ltl (ldropWhile is_right (traj t)))")
      apply (erule ssubst)
      apply (simp add: interleave_left)
      apply (rule stutter_LCons)
      apply (rule ih[simplified])
      apply (subst lhd_LCons_ltl[symmetric])
      apply (metis `ldropWhile is_right (traj t) \<noteq> LNil`)
      apply simp
      prefer 2
      apply (simp add: xs_def del: ltakeWhile_eq_LNil_iff)
      apply (simp add: llist_Case_def del: ltakeWhile_eq_LNil_iff)
      apply (subgoal_tac "ldropWhile is_right (traj t) = LCons (Inl ()) (ltl (ldropWhile is_right (traj t)))")
      apply (rotate_tac 1)
      apply (erule ssubst)
      apply (simp add: interleave_left del: ltakeWhile_eq_LNil_iff)
      apply (metis ih_var stutter_LCons)
      apply (subst lhd_LCons_ltl[symmetric])
      apply (metis `ldropWhile is_right (traj t) \<noteq> LNil`)
      apply simp
      prefer 2
      apply simp
      apply (rule stutter_refl_var)
      apply (metis (hide_lams, no_types) llist.distinct(1) llist.sel_exhaust llist.simps(19) ltakeWhile_eq_LNil_iff reinterleave traj_LNil traj_interleave)
      apply (simp add: llist_Case_def)
      apply (rule arg_cong) back
      apply (subgoal_tac "ldropWhile is_right (traj t) = LCons (Inl ()) (ltl (ldropWhile is_right (traj t)))")
      apply (erule ssubst)
      apply simp
      apply (subst lhd_LCons_ltl[symmetric])
      apply (metis `ldropWhile is_right (traj t) \<noteq> LNil`)
      by simp
    finally show ?case
      by auto
  qed
  ultimately show ?thesis
    by simp
qed

lemma [simp]: "\<rr> (ldeleteLeft n xs) = \<rr> xs"
  sorry

lemma tshuffle_stutter: "\<Union>{lmap \<langle>id,id\<rangle> ` (xs' \<sha> ys)|xs'. xs' \<in> stutter xs} \<subseteq> (lmap \<langle>id,id\<rangle> ` (xs \<sha> ys))\<^sup>\<dagger>"
proof -
  {
  fix xs' zs'

  assume "xs' \<in> stutter xs" and "zs' \<in> xs' \<sha> ys"

  hence "\<exists>zs\<in>xs \<sha> ys. lmap \<langle>id,id\<rangle> zs' \<in> stutter (lmap \<langle>id,id\<rangle> zs)"
  proof (induct xs' arbitrary: zs' rule: stutter.induct)
    case (self \<sigma> zs')
    thus "\<exists>zs\<in>xs \<sha> ys. lmap \<langle>id,id\<rangle> zs' \<in> stutter (lmap \<langle>id,id\<rangle> zs)"
      sorry
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
      sorry

    from this and stutter(2) obtain zs where "zs \<in> xs \<sha> ys"
    and "lmap \<langle>id,id\<rangle> (ws \<frown> vs \<triangleright> ldeleteLeft (llength ws) (traj zs') \<triangleleft> ys) \<in> stutter (lmap \<langle>id,id\<rangle> zs)"
      by blast

    moreover have "lmap \<langle>id,id\<rangle> zs' \<in> stutter (lmap \<langle>id,id\<rangle> (ws \<frown> vs \<triangleright> ldeleteLeft (llength ws) (traj zs') \<triangleleft> ys))"
      by (subst zs'_interleave) (rule stutter_in_left[OF stutter(3)])

    ultimately show ?case
      by (metis (hide_lams, no_types) stutter_trans)
  next
    case (mumble ws \<sigma> \<sigma>' \<sigma>'' vs zs')

    have zs'_interleave: "zs' = (ws \<frown> LCons (\<sigma>, \<sigma>'') vs) \<triangleright> traj zs' \<triangleleft> ys"
      sorry

    have "(ws \<frown> LCons (\<sigma>,\<sigma>') (LCons (\<sigma>',\<sigma>'') vs) \<triangleright> linsertLeft (llength ws + 1) () (traj zs') \<triangleleft> ys) \<in> (ws \<frown> LCons (\<sigma>, \<sigma>') (LCons (\<sigma>', \<sigma>'') vs)) \<sha> ys"
      sorry

    from this and mumble(2) obtain zs where "zs \<in> xs \<sha> ys"
    and "lmap \<langle>id,id\<rangle> (ws \<frown> LCons (\<sigma>,\<sigma>') (LCons (\<sigma>',\<sigma>'') vs) \<triangleright> linsertLeft (llength ws + 1) () (traj zs') \<triangleleft> ys) \<in> stutter (lmap \<langle>id,id\<rangle> zs)"
      by blast

    moreover have "lmap \<langle>id,id\<rangle> zs' \<in> stutter (lmap \<langle>id,id\<rangle> (ws \<frown> LCons (\<sigma>,\<sigma>') (LCons (\<sigma>',\<sigma>'') vs) \<triangleright> linsertLeft (llength ws + 1) () (traj zs') \<triangleleft> ys))"
      apply (subst zs'_interleave)
      sorry
 
    ultimately show ?case
      by (metis (hide_lams, no_types) stutter_trans)
  qed
  }
  thus ?thesis
    by (auto simp add: Stutter_def) (metis (full_types) imageI)
qed

lemma shuffle_stutter: "X\<^sup>\<dagger> \<parallel> Y \<subseteq> (X \<parallel> Y)\<^sup>\<dagger>"
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

lemma Stutter_shuffle [simp]: "(X\<^sup>\<dagger> \<parallel> Y\<^sup>\<dagger>)\<^sup>\<dagger> = (X \<parallel> Y)\<^sup>\<dagger>"
  sorry

end

