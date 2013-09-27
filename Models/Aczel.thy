theory Aczel
  imports Language
begin

coinductive transitions :: "'a llist \<Rightarrow> 'a set llist \<Rightarrow> bool" where
  tr_LNil [intro!]: "transitions LNil LNil"
| tr_LConsI [intro!]: "t \<in> x \<Longrightarrow> transitions ts xs \<Longrightarrow> transitions (LCons t ts) (LCons x xs)"

lemma tr_LConsE [dest]: "transitions (LCons t ts) (LCons x xs) \<Longrightarrow> transitions ts xs"
  by (metis LNil_not_LCons transitions.simps ltl_LCons)

lemma [elim]: "transitions (LCons t ts) (LCons x xs) \<Longrightarrow> t \<in> x"
  by (metis LCons_inject LNil_not_LCons transitions.simps)

lemma [iff]: "transitions t LNil \<longleftrightarrow> t = LNil"
  by (metis LNil_not_LCons transitions.simps)

lemma [iff]: "transitions LNil xs \<longleftrightarrow> xs = LNil"
  by (metis LNil_not_LCons transitions.simps)

lemma transitions_llength: "transitions t xs \<Longrightarrow> llength t = llength xs"
proof -
  assume "transitions t xs"
  hence "(llength t, llength xs) \<in> {(llength t, llength xs)|t xs::'a set llist. transitions t xs}"
    by auto
  thus ?thesis
  proof (coinduct rule: enat_equalityI)
    case (Eqenat n m) note q = this[simplified]
    then obtain t and xs :: "'a set llist"
    where n_def: "n = llength t" and m_def: "m = llength xs" and transitions: "transitions t xs"
      by blast
    {
      assume "t = LNil"
      moreover hence "xs = LNil"
        by (metis LNil_not_LCons transitions transitions.cases)
      ultimately have ?zero
        by (metis llength_LNil m_def n_def)
    }
    moreover
    {
      assume "xs = LNil"
      moreover hence "t = LNil"
        by (metis LNil_not_LCons transitions transitions.cases)
      ultimately have ?zero
        by (metis llength_LNil m_def n_def)
    }
    moreover
    {
      assume "\<exists>x' xs'. xs = LCons x' xs'" and "\<exists>\<sigma> t'. t = LCons \<sigma> t'"
      from this and n_def and m_def and transitions
      have ?eSuc
        by (auto, rule_tac x = t' in exI, auto)
    }
    ultimately show ?case
      by (cases t, simp) (cases xs, simp_all)
  qed
qed

coinductive consistent :: "('a \<times> 'a) llist \<Rightarrow> bool" where
  EqNil [intro!]: "consistent LNil"
| EqSingle [intro!]: "consistent (LCons \<sigma> LNil)"
| EqPair [intro!]: "snd \<sigma> = fst \<sigma>' \<Longrightarrow> consistent (LCons \<sigma>' t) \<Longrightarrow> consistent (LCons \<sigma> (LCons \<sigma>' t))"

thm consistent.coinduct

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

abbreviation tr' :: "'a rel llist \<Rightarrow> ('a \<times> 'a) lan" where
  "tr' xs \<equiv> {t. transitions t xs}" 

definition tr :: "'a rel llist \<Rightarrow> ('a \<times> 'a) lan" where
  "tr xs = tr' xs \<inter> Con"

definition Tr :: "'a rel lan \<Rightarrow> ('a \<times> 'a) lan" where
  "Tr X = (\<Union>xs\<in>X. tr xs)"

lemma tr'_LCons: "tr' (LCons x xs) = {LCons t ts |t ts. transitions (LCons t ts) (LCons x xs)}"
proof auto
  fix t
  assume "transitions t (LCons x xs)"
  thus "\<exists>\<sigma> \<sigma>' t'. t = LCons (\<sigma>, \<sigma>') t' \<and> transitions (LCons (\<sigma>, \<sigma>') t') (LCons x xs)"
    by (cases t) auto
qed

lemma tr'_ind: "tr' (LCons x xs) = {LCons t ts |t ts. t \<in> x \<and> ts \<in> tr' xs}"
  by (simp add: tr'_LCons) auto

lemma [simp]: "{LNil} \<inter> Con = {LNil}"
  by (auto simp add: Con_def)

lemma consistent_LConsD [dest]: "consistent (LCons \<sigma> t) \<Longrightarrow> consistent t"
  by (erule consistent.cases) auto

lemma consistent_LConsE [elim]: "consistent (LCons \<sigma> (LCons \<sigma>' t)) \<Longrightarrow> snd \<sigma> = fst \<sigma>'"
  by (erule consistent.cases) auto

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
    thus ?case
      apply -
      apply (rule llist_cases3[where xs = t])
      apply (simp_all add: eSuc_enat[symmetric])
      apply blast
      apply (cases n)
      apply (simp add: enat_0)
      apply blast
      apply (simp add: eSuc_enat[symmetric])
      apply (rule EqPair)
      apply (erule consistent_LConsE)
      by (metis consistent_LConsD ltake_eSuc_LCons)
  qed
qed

lemma transitions_lappend:
  assumes "transitions t xs" and "transitions s ys"
  shows "transitions (t \<frown> s) (xs \<frown> ys)"
proof (cases "lfinite xs")
  assume "lfinite xs"
  from this and assms
  show "transitions (t \<frown> s) (xs \<frown> ys)"
  proof (induct xs arbitrary: t rule: lfinite_induct)
    case Nil thus ?case by (cases t) auto
  next
    case (Cons x xs) thus ?case by (cases t) auto
  qed
next
  assume "\<not> lfinite xs"
  moreover hence "\<not> lfinite t" using assms
    by (auto dest!: transitions_llength simp: lfinite_conv_llength_enat)
  ultimately show "transitions (t \<frown> s) (xs \<frown> ys)"
    by (metis assms(1) lappend_inf)
qed

lemma tr'_l_prod: "lfinite xs \<Longrightarrow> tr' xs \<cdot> tr' ys \<inter> Con \<subseteq> (tr' xs \<inter> Con) \<cdot> (tr' ys \<inter> Con) \<inter> Con"
proof (induct xs rule: lfinite_induct)
  case Nil show ?case by simp
next
  case (Cons x xs)
  thus ?case
    apply (auto simp add: tr'_ind)
    apply (auto simp add: l_prod_def Con_def)
    by (metis consistent_lappend1 consistent_lappend2 lappend_LCons lfinite_LCons)+
qed

lemma tr_FIN: "lfinite xs \<Longrightarrow> tr xs \<subseteq> FIN"
  by (auto dest!: transitions_llength simp add: FIN_def tr_def lfinite_conv_llength_enat)

lemma tr'_FIN: "lfinite xs \<Longrightarrow> tr' xs \<subseteq> FIN"
  by (auto dest!: transitions_llength simp add: FIN_def lfinite_conv_llength_enat)

lemma tr_infinite: "\<not> lfinite xs \<Longrightarrow> tr xs \<cdot> {} = tr xs"
  apply (auto simp add: l_prod_def tr_def)
  apply (drule transitions_llength)
  by (metis lfinite_conv_llength_enat)

lemma tr'_infinite: "\<not> lfinite xs \<Longrightarrow> tr' xs \<cdot> {} = tr' xs"
  apply (auto simp add: l_prod_def tr_def)
  apply (drule transitions_llength)
  by (metis lfinite_conv_llength_enat)

lemma transitions_lappend_ltake1: "transitions t (xs \<frown> ys) \<Longrightarrow> transitions (ltake (llength xs) t) xs"
proof (cases "lfinite xs")
  assume "lfinite xs" and "transitions t (xs \<frown> ys)"
  thus "transitions (ltake (llength xs) t) xs"
  proof (induct xs arbitrary: t rule: lfinite_induct)
    case Nil show ?case by auto
  next
    case (Cons x xs)
    thus ?case
      by (cases t) auto
  qed
next
  assume "\<not> lfinite xs" and "transitions t (xs \<frown> ys)"
  thus "transitions (ltake (llength xs) t) xs"
    by (metis lappend_inf ltake_all order_refl transitions_llength)
qed

lemma transitions_lappend_ltake2:
  "lfinite xs \<Longrightarrow> transitions t (xs \<frown> ys) \<Longrightarrow> transitions (ldrop (llength xs) t) ys"
proof (induct xs arbitrary: t rule: lfinite_induct)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  thus ?case
    by (cases t) auto
qed

lemma tr'_lappend: "tr' (xs \<frown> ys) = tr' xs \<cdot> tr' ys"
  apply (cases "lfinite xs")
  apply (frule tr'_FIN)
  apply (simp add: fin_l_prod)
  defer
  apply (metis l_prod_assoc lappend_inf seq.annil tr'_infinite)
  apply auto
  apply (rename_tac t)
  apply (rule_tac x = "ltake (llength xs) t" in exI)
  apply (rule_tac x = "ldrop (llength xs) t" in exI)
  apply (intro conjI)
  apply (simp add: lappend_ltake_ldrop)
  apply (metis transitions_lappend_ltake1)
  apply (metis transitions_lappend_ltake2)
  by (metis transitions_lappend)

lemma tr_append: "tr (xs \<frown> ys) = (tr xs \<cdot> tr ys) \<inter> Con"
proof (cases "lfinite xs")
  assume "lfinite xs"
  hence "tr (xs \<frown> ys) \<subseteq> (tr xs \<cdot> tr ys) \<inter> Con" unfolding tr_def
    by (metis tr'_l_prod tr'_lappend)
  moreover have "(tr xs \<cdot> tr ys) \<inter> Con \<subseteq> tr (xs \<frown> ys)"
    by (simp add: tr_def tr'_lappend) (metis Int_commute inf_le2 le_infI2 seq.mult_isol_var)
  ultimately show "tr (xs \<frown> ys) = (tr xs \<cdot> tr ys) \<inter> Con"
    by (rule antisym)
next
  assume "\<not> lfinite xs"
  thus "tr (xs \<frown> ys) = (tr xs \<cdot> tr ys) \<inter> Con"
    by (metis (full_types) Int_commute inf.left_idem l_prod_assoc l_prod_zero lappend_inf tr_def tr_infinite)
qed

lemma Tr_union [simp]: "Tr (X \<union> Y) = Tr X \<union> Tr Y"
  by (simp add: Tr_def)

lemma l_prod_inf_distl: "X \<subseteq> FIN \<Longrightarrow> X \<cdot> \<Union>\<YY> = \<Union>{X \<cdot> Y |Y. Y \<in> \<YY>}"
  by (auto simp add: l_prod_def FIN_def)

lemma set_comp_fun_eq1: "(\<And>x. P x \<Longrightarrow> f x = g x) \<Longrightarrow> {f x |x. P x} = {g x |x. P x}"
  by auto metis

lemma [simp]: "Tr {xs \<in> X. \<not> lfinite xs} = Tr X \<cdot> {}"
  apply (simp add: l_prod_def)
  apply (auto simp add: Tr_def tr_def)
  apply (drule transitions_llength)
  apply (auto simp: lfinite_conv_llength_enat)
  by (metis transitions_llength)

lemma [simp]: "\<Union>{tr xs |xs. xs \<in> X \<and> lfinite xs} = Tr X \<inter> FIN"
  apply (auto simp add: FIN_def Tr_def tr_def)
  apply (metis lfinite_conv_llength_enat transitions_llength)
  apply (rule_tac x = "tr xs" in exI)
  apply (simp add: tr_def)
  apply (rule_tac x = xs in exI)
  apply auto
  by (metis lfinite_conv_llength_enat transitions_llength)

lemma Tr_consistent [simp]: "Tr X \<inter> Con = Tr X"
  by (simp add: Tr_def tr_def)

lemma [simp]: "X \<cdot> {} \<union> X \<inter> FIN = X"
  by (auto simp add: l_prod_def FIN_def)

lemma Tr_l_prod: "Tr (X \<cdot> Y) = (Tr X \<cdot> Tr Y) \<inter> Con"
proof -
  have "Tr (X \<cdot> Y) = Tr {xs \<in> X. \<not> lfinite xs} \<union> Tr {xs \<frown> ys |xs ys. xs \<in> X \<and> lfinite xs \<and> ys \<in> Y}"
    by (simp add: l_prod_def)
  also have "... = Tr X \<cdot> {} \<union> Tr {xs \<frown> ys |xs ys. xs \<in> X \<and> lfinite xs \<and> ys \<in> Y}"
    by simp
  also have "... = Tr X \<cdot> {} \<union> \<Union>{tr (xs \<frown> ys) |xs ys. xs \<in> X \<and> lfinite xs \<and> ys \<in> Y}"
    by (auto simp add: Tr_def)
  also have "... = Tr X \<cdot> {} \<union> \<Union>{tr xs \<cdot> tr ys \<inter> Con |xs ys. xs \<in> X \<and> lfinite xs \<and> ys \<in> Y}"
    by (simp add: tr_append)
  also have "... = Tr X \<cdot> {} \<union> \<Union>{tr xs \<cdot> tr ys |xs ys. xs \<in> X \<and> lfinite xs \<and> ys \<in> Y} \<inter> Con"
    by auto
  also have "... = Tr X \<cdot> {} \<inter> Con \<union> \<Union>{tr xs \<cdot> tr ys |xs ys. xs \<in> X \<and> lfinite xs \<and> ys \<in> Y} \<inter> Con"
    apply (rule arg_cong) back
    by (metis Tr_consistent le_iff_inf seq.mult_oner seq.subdistl subset_trans sup_bot_left)
  also have "... = (Tr X \<cdot> {} \<union> \<Union>{tr xs \<cdot> tr ys |xs ys. xs \<in> X \<and> lfinite xs \<and> ys \<in> Y}) \<inter> Con"
    by auto
  also have "... = (Tr X \<cdot> {} \<union> \<Union>{\<Union>{tr xs \<cdot> tr ys |ys. ys \<in> Y} |xs. xs \<in> X \<and> lfinite xs}) \<inter> Con"
    by blast
  also have "... = (Tr X \<cdot> {} \<union> \<Union>{tr xs \<cdot> \<Union>{tr ys |ys. ys \<in> Y} |xs. xs \<in> X \<and> lfinite xs}) \<inter> Con"
    by (rule arg_cong, rule set_comp_fun_eq1) (auto simp: tr_FIN[THEN l_prod_inf_distl])
  also have "... = (Tr X \<cdot> {} \<union> \<Union>{tr xs |xs. xs \<in> X \<and> lfinite xs} \<cdot> \<Union>{tr ys |ys. ys \<in> Y}) \<inter> Con"
    by (rule arg_cong, subst l_prod_inf_distr, blast)
  also have "... = (Tr X \<cdot> {} \<union> \<Union>{tr xs |xs. xs \<in> X \<and> lfinite xs} \<cdot> Tr Y) \<inter> Con"
    by (rule arg_cong, auto simp add: Tr_def)
  also have "... = (Tr X \<cdot> {} \<union> (Tr X \<inter> FIN) \<cdot> Tr Y) \<inter> Con"
    by simp
  also have "... = (Tr X \<cdot> {} \<cdot> Tr Y \<union> (Tr X \<inter> FIN) \<cdot> Tr Y) \<inter> Con"
    by (metis l_prod_zero seq.mult_assoc)
  also have "... = (Tr X \<cdot> {} \<union> (Tr X \<inter> FIN)) \<cdot> Tr Y \<inter> Con"
    by (metis l_prod_distr)
  also have "... = (Tr X \<cdot> Tr Y) \<inter> Con"
    by simp
  finally show ?thesis .
qed

lemma transitions_self: "transitions t (lmap (\<lambda>x. {x}) t)"
proof -
  have "(\<forall>n. enat n < llength t \<longrightarrow> lnth t n \<in> lnth (lmap (\<lambda>x. {x}) t) n) \<and> llength t = llength (lmap (\<lambda>x. {x}) t)"
    by auto
  thus ?thesis
  proof (coinduct)
    case (transitions t xs)
    thus ?case
      apply (cases t)
      apply simp
      apply (subgoal_tac "\<exists>y ys. xs = LCons y ys")
      apply auto
      apply (erule_tac x = 0 in allE)
      apply (simp add: enat_0)
      apply (erule_tac x = "Suc n" in allE)
      apply simp
      apply (metis Suc_ile_eq)
      by (metis llength_eq_0 neq_LNil_conv zero_ne_eSuc)
  qed
qed 

lemma Tr_UNIV [simp]: "Tr UNIV = Con"
  apply (auto simp add: Tr_def tr_def Con_def)
  apply (rule_tac x = "lmap (\<lambda>x. {x}) x" in exI)
  by (metis transitions_self)

lemma "Tr (X\<^sup>\<omega>) \<subseteq> (Tr X)\<^sup>\<omega> \<inter> Con"
proof -
  have "Tr (X\<^sup>\<omega>) \<subseteq> (Tr X)\<^sup>\<omega>"
    by (rule seq.omega_coinduct_var2, subst seq.omega_unfold_eq[symmetric], auto simp only: Tr_l_prod)
  thus "Tr (X\<^sup>\<omega>) \<subseteq> (Tr X)\<^sup>\<omega> \<inter> Con"
    by (metis Int_lower1 Tr_consistent le_inf_iff)
qed

lemma [simp]: "X \<cdot> (Y \<inter> Con) \<inter> Con = X \<cdot> Y \<inter> Con"
  by (auto simp add: l_prod_def Con_def)

lemma [simp]: "(X \<inter> Con) \<cdot> Y \<inter> Con = X \<cdot> Y \<inter> Con"
  by (auto simp add: l_prod_def Con_def)

lemma "(Tr X)\<^sup>\<omega> \<inter> Con = (\<nu> Y. Tr X \<cdot> Y \<inter> Con)"
  apply (rule antisym)
  apply (rule gfp_induct)
  apply (simp add: isotone_def)
  apply (metis inf_commute le_infI2 seq.mult_isol)
  apply (subst seq.omega_unfold_eq[symmetric])
  apply simp
  apply (simp only: le_inf_iff)
  apply (intro conjI)
  apply (rule seq.omega_coinduct_var2)
  apply (subst gfp_compute[symmetric])
  apply (simp add: isotone_def)
  apply (metis inf_commute le_infI2 seq.mult_isol)
  apply simp
  apply (simp add: greatest_fixpoint_def)
  apply (rule the1I2)
  apply (rule knaster_tarski_gfp)
  apply (simp add: isotone_def)
  apply (metis inf_commute le_infI2 seq.mult_isol)
  apply (simp add: is_gfp_def)
  by auto

lemma [simp]: "\<not> lfinite xs \<Longrightarrow> {xs}\<^sup>\<omega> = {xs}"
  apply (simp add: omega_def)
  apply (rule gfp_equality)
  apply (simp add: is_gfp_def)
  by (auto simp add: l_prod_def)

lemma "lfinite xs \<Longrightarrow> {lconcat (repeat xs)} \<le> {xs}\<^sup>\<omega>"
  apply (rule seq.omega_coinduct_var2)
  apply (auto simp: l_prod_def)
  apply (metis Coinductive_List.iterates lconcat_LCons)
  by (metis Coinductive_List.iterates lconcat_LCons)

lemma l_prod_zero_omega: "(x \<cdot> {})\<^sup>\<omega> = x \<cdot> {}"
  by (metis l_prod_zero seq.wagner_2)

lemma tr_infinite_zero: "\<not> lfinite xs \<Longrightarrow> tr xs = tr xs \<cdot> {}"
  by (metis tr_infinite)

lemma [simp]: "tr LNil = {LNil}"
  by (simp add: tr_def)

lemma [simp]: "{LNil}\<^sup>\<omega> = UNIV"
  by (metis seq.max_element top_unique)

no_notation l_prod (infixl "\<cdot>" 80)
notation Groups.times_class.times (infixl "\<cdot>" 70)

typedef 'a trace = "Pow (Con::('a \<times> 'a) lan)"
  by (auto simp add: Con_def)

setup_lifting type_definition_trace

lemma [dest!]: "Domainp (set_rel cr_trace) A \<Longrightarrow> A \<subseteq> Pow Con"
  apply (auto simp add: cr_trace_def set_rel_def Con_def)
  apply (erule_tac x = x in ballE)
  apply (metis Con_def Pow_def mem_Collect_eq set_mp Rep_trace)
  by blast

instantiation trace :: (type) dioid_one_zerol begin

  lift_definition less_eq_trace :: "'a trace \<Rightarrow> 'a trace \<Rightarrow> bool" is "op \<subseteq>"
    by auto

  lift_definition less_trace :: "'a trace \<Rightarrow> 'a trace \<Rightarrow> bool" is "op \<subset>"
    by auto

  lift_definition zero_trace :: "'a trace" is "{}"
    by auto

  lift_definition one_trace :: "'a trace" is "{LNil}"
    by (auto simp add: Con_def)

  lift_definition plus_trace :: "'a trace \<Rightarrow> 'a trace \<Rightarrow> 'a trace" is union
    by simp

  lift_definition times_trace :: "'a trace \<Rightarrow> 'a trace \<Rightarrow> 'a trace" is "\<lambda>X Y. l_prod X Y \<inter> Con"
    by auto

  instance
  proof
    fix x y z :: "'a trace"
    show "(x + y) + z = x + (y + z)"
      by transfer auto
    show "x + y = y + x"
      by transfer auto
    show "(x \<cdot> y) \<cdot> z = x \<cdot> (y \<cdot> z)"
      by transfer (simp add: l_prod_assoc)
    show "(x + y) \<cdot> z = x \<cdot> z + y \<cdot> z"
      by transfer auto
    show "x \<cdot> (y + z) = x \<cdot> y + x \<cdot> z"
      by transfer auto
    show "x + x = x"
      by transfer simp
    show "1 \<cdot> x = x"
      by transfer auto
    show "x \<cdot> 1 = x"
      by transfer auto
    show "0 + x = x"
      by transfer simp
    show "0 \<cdot> x = 0"
      by transfer simp
    show "x \<le> y \<longleftrightarrow> x + y = y"
      by transfer auto
    show "x < y \<longleftrightarrow> x \<le> y \<and> x \<noteq> y"
      by transfer auto
  qed
end

instantiation trace :: (type) lattice begin

  lift_definition sup_trace :: "'a trace \<Rightarrow> 'a trace \<Rightarrow> 'a trace" is union
    by simp

  lift_definition inf_trace :: "'a trace \<Rightarrow> 'a trace \<Rightarrow> 'a trace" is inter
    by auto

  instance by default (transfer, auto)+
end

instantiation trace :: (type) complete_lattice begin

  lift_definition top_trace :: "'a trace" is Con
    by simp

  lift_definition bot_trace :: "'a trace" is "{}"
    by simp

  lift_definition Sup_trace :: "'a trace set \<Rightarrow> 'a trace" is Union
    by auto

  lift_definition Inf_trace :: "'a trace set \<Rightarrow> 'a trace" is "\<lambda>X. Inter X \<inter> Con"
    by (simp add: Con_def)

  instance by default (transfer, auto)+
end

end
