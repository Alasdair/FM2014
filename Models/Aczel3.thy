theory Aczel3
  imports Language
begin

fun pre :: "'a \<times> 'b \<times> 'c \<Rightarrow> 'a" where
  "pre (x, y, z) = x"

fun post :: "'a \<times> 'b \<times> 'c \<Rightarrow> 'c" where
  "post (x, y, z) = z"

coinductive consistent :: "('a \<times> 'b \<times> 'a) llist \<Rightarrow> bool" where
  EqNil [intro!]: "consistent LNil"
| EqSingle [intro!]: "consistent (LCons \<sigma> LNil)"
| EqPair [intro!]: "post \<sigma> = pre \<sigma>' \<Longrightarrow> consistent (LCons \<sigma>' t) \<Longrightarrow> consistent (LCons \<sigma> (LCons \<sigma>' t))"

lemma consistent_LConsD [dest]: "consistent (LCons \<sigma> t) \<Longrightarrow> consistent t"
  by (erule consistent.cases) auto

lemma consistent_LConsE [elim]: "consistent (LCons \<sigma> (LCons \<sigma>' t)) \<Longrightarrow> post \<sigma> = pre \<sigma>'"
  by (erule consistent.cases) auto

lemma lnth_repeat [simp]: "lnth (repeat x) n = x"
  by (induct n) simp_all

lemma inf_stutter_consistent: "consistent (repeat (\<sigma>, l, \<sigma>))"
proof -
  have "\<forall>n. post (lnth (repeat (\<sigma>, l, \<sigma>)) n) = pre (lnth (repeat (\<sigma>, l, \<sigma>)) (Suc n))"
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
        thus "?EqSingle \<or> ?EqPair"
          by auto (metis prod_cases3)
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

definition Con :: "('a \<times> 'b \<times> 'a) lan" where
  "Con = Collect consistent"

definition Aczel :: "('a \<times> 'b \<times> 'a) lan \<Rightarrow> ('a \<times> 'b \<times> 'a) lan" ("\<pi>") where
  "\<pi> X = X \<inter> Con"

lemma inf_stutter_Con [intro!]: "repeat (\<sigma>, l, \<sigma>) \<in> Con"
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

lemma Aczel_zero [simp]: "\<pi> {} = {}"
  by (simp add: Aczel_def)

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

lemma lappend_consistent:
  "lfinite xs \<Longrightarrow> consistent (LCons x xs \<frown> LCons y ys) \<Longrightarrow> post (llast (LCons x xs)) = pre y"
  by (induct xs arbitrary: x rule: lfinite_induct) auto

lemma [dest!]: "consistent (LCons x xs \<frown> LCons y ys) \<Longrightarrow> lfinite xs \<longrightarrow> post (llast (LCons x xs)) = pre y"
  by (metis lappend_consistent)

lemma [simp]: "llast (LCons (\<sigma>, \<sigma>) (llist_of (replicate n (\<sigma>, \<sigma>)))) = (\<sigma>, \<sigma>)"
  by (induct n) auto

definition Aczel_mult :: "('a \<times> 'b \<times> 'a) lan \<Rightarrow> ('a \<times> 'b \<times> 'a) lan \<Rightarrow> ('a \<times> 'b \<times> 'a) lan" (infixl "\<otimes>" 75) where
  "X \<otimes> Y = \<pi> (X \<cdot> Y)"

lemma amult_distl [simp]: "X \<otimes> (Y \<union> Z) = X \<otimes> Y \<union> X \<otimes> Z"
  by (simp add: Aczel_mult_def)

lemma amult_distr [simp]: "(X \<union> Y) \<otimes> Z = X \<otimes> Z \<union> Y \<otimes> Z"
  by (simp add: Aczel_mult_def)

lemma amult_assoc: "X \<otimes> (Y \<otimes> Z) = (X \<otimes> Y) \<otimes> Z"
  by (simp add: Aczel_mult_def) (metis Aczel_def Aczel_l_prod inf_commute inf_left_idem seq.mult_assoc)

lemma consistent_replicate': "consistent (llist_of xs) \<Longrightarrow> \<forall>y\<in>set xs. \<exists>\<sigma>. y = (\<sigma>, l, \<sigma>) \<Longrightarrow> \<exists>n \<sigma>. xs = replicate n (\<sigma>, l, \<sigma>)"
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
      apply (subgoal_tac "\<exists>n \<sigma>. xs = replicate n (\<sigma>, l, \<sigma>)")
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

lemma replicate_finite_Con: "llist_of (replicate n (\<sigma>, l, \<sigma>)) \<in> Con"
proof (induct n)
  case 0 show ?case
    by (auto simp add: Con_def)
next
  case (Suc n) thus ?case
    by (cases n) (auto simp add: Con_def)
qed

lemma Aczel_inf [simp]: "\<pi> (x\<cdot>{}) = (\<pi> x)\<cdot>{}"
  by (auto simp add: l_prod_def Con_def)

lemma Aczel_one [simp]: "\<pi> {LNil} = {LNil}"
  by (auto simp add: Aczel_def Con_def)

primrec proj_power :: "('a \<times> 'b \<times> 'a) lan \<Rightarrow> nat \<Rightarrow> ('a \<times> 'b \<times> 'a) lan" where
  "proj_power x 0 = {LNil}"
| "proj_power x (Suc n) = \<pi> (x \<cdot> proj_power x n)"

definition proj_powers :: "('a \<times> 'b \<times> 'a) lan \<Rightarrow> ('a \<times> 'b \<times> 'a) lan set" where
  "proj_powers x  = {y. (\<exists>i. y = proj_power x i)}"

lemma power_to_proj: "\<pi> (power x i) = proj_power x i"
  apply (induct i)
  apply simp_all
  by (metis Aczel_idem Aczel_l_prod)

lemma proj_power_proj: "proj_power x i = proj_power (\<pi> x) i"
  apply (induct i)
  apply simp_all
  by (metis Aczel_l_prod Language.power.simps(2) power_to_proj proj_power.simps(2))

lemma powers_to_proj: "\<pi> ` powers x = proj_powers x"
  apply (auto simp add: proj_powers_def powers_def image_def)
  apply (metis power_to_proj)
  by (metis power_to_proj)

lemma proj_powers_proj: "proj_powers x = proj_powers (\<pi> x)"
  apply (auto simp add: proj_powers_def)
  apply (metis proj_power_proj)
  by (metis proj_power_proj)

lemma "\<Union>{\<pi> X |X. X \<in> powers (x \<inter> FIN)} = \<Union>{X. X \<in> \<pi> ` powers (x \<inter> FIN)}"
  by (auto simp add: image_def)

lemma Aczel_fin_star_lem: "\<Union>{\<pi> X |X. X \<in> powers (x \<inter> FIN)} = \<Union>{\<pi> X |X. X \<in> powers (\<pi> (x \<inter> FIN))}"
proof -
  have "\<Union>{\<pi> X |X. X \<in> powers (x \<inter> FIN)} = \<Union>{X. X \<in> \<pi> ` powers (x \<inter> FIN)}"
    by (auto simp add: image_def)
  also have "... = \<Union>{X. X \<in> proj_powers (x \<inter> FIN)}"
    by (metis powers_to_proj)
  also have "... = \<Union>{X. X \<in> proj_powers (\<pi> (x \<inter> FIN))}"
    by (metis proj_powers_proj)
  also have "... =  \<Union>{X. X \<in> \<pi> ` powers (\<pi> (x \<inter> FIN))}"
    by (metis powers_to_proj)
  also have "... = \<Union>{\<pi> X |X. X \<in> powers (\<pi> (x \<inter> FIN))}"
    by (auto simp add: image_def)
  finally show ?thesis .
qed

lemma Aczel_fin_star: "\<pi> ((x \<inter> FIN)\<^sup>\<star>) \<le> \<pi> ((\<pi> (x \<inter> FIN))\<^sup>\<star>)"
  apply (subst star_power_fin)
  apply simp
  apply (subst star_power_fin)
  apply (metis Aczel_coextensive inf.bounded_iff)
  apply (subst Aczel_continuous)+
  by (metis Aczel_fin_star_lem subset_refl)

lemma Aczel_star1: "\<pi> (x\<^sup>\<star>) \<le> \<pi> (\<pi> x\<^sup>\<star>)"
proof -
  have "\<pi> (x\<^sup>\<star>) = \<pi> ((x \<inter> FIN \<union> x\<cdot>{})\<^sup>\<star>)"
    by simp
  also have "... = \<pi> ((x \<inter> FIN)\<^sup>\<star>\<cdot>x\<cdot>{} \<union> (x \<inter> FIN)\<^sup>\<star>)"
    by (simp only: seq.inf_part_star)
  also have "... = \<pi> ((x \<inter> FIN)\<^sup>\<star> \<cdot> (x\<cdot>{} \<union> {LNil}))"
    by (metis seq.distrib_left seq.mult.right_neutral seq.mult_assoc)
  also have "... = \<pi> (\<pi> ((x \<inter> FIN)\<^sup>\<star>) \<cdot> \<pi> (x\<cdot>{} \<union> {LNil}))"
    by (metis Aczel_l_prod)
  also have "... \<le> \<pi> (\<pi> ((\<pi> (x \<inter> FIN))\<^sup>\<star>) \<cdot> \<pi> (x\<cdot>{} \<union> {LNil}))"
    by (metis (hide_lams, no_types) Aczel_fin_star Aczel_iso seq.mult_isor)
  also have "... = \<pi> (\<pi> (\<pi> (x \<inter> FIN)\<^sup>\<star>) \<cdot> (\<pi> x \<cdot> {} \<union> {LNil}))"
    by (simp only: Aczel_union Aczel_inf Aczel_one)
  also have "... = \<pi> (\<pi> (\<pi> (x \<inter> FIN)\<^sup>\<star>) \<cdot> \<pi> x \<cdot> {} \<union> \<pi> (\<pi> (x \<inter> FIN)\<^sup>\<star>))"
    by (metis seq.distrib_left seq.mult.right_neutral seq.mult_assoc)
  also have "... = \<pi> (\<pi> (x \<inter> FIN)\<^sup>\<star> \<cdot> \<pi> x \<cdot> {} \<union> \<pi> (x \<inter> FIN)\<^sup>\<star>)"
    by (metis Aczel_idem Aczel_l_prod Aczel_union)
  also have "... = \<pi> ((\<pi> (x \<inter> FIN) \<union> \<pi> x \<cdot> {})\<^sup>\<star>)"
    by (simp only: seq.inf_part_star)
  also have "... = \<pi> ((\<pi> (x \<inter> FIN \<union> x\<cdot>{}))\<^sup>\<star>)"
    by (simp only: Aczel_union Aczel_inf Aczel_idem)
  also have "... = \<pi> (\<pi> x\<^sup>\<star>)"
    by simp
  finally show ?thesis .
qed

lemma Aczel_star [simp]: "\<pi> (\<pi> x\<^sup>\<star>) = \<pi> (x\<^sup>\<star>)"
  by (metis Aczel_def Aczel_iso Aczel_star1 par.add_ub2 seq.star_iso subset_antisym sup_inf_absorb)

end

