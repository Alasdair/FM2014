theory Aczel
  imports Stutter_Language
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

lemma test_replicate: "\<langle>S\<rangle> = {xs. \<exists>n \<sigma>. \<sigma> \<in> S \<and> xs = llist_of ((\<sigma>, \<sigma>) # replicate n (\<sigma>, \<sigma>))}"
  apply (auto simp add: test_def Stutter_def)
  sorry

lemma finite_stutter [intro]: "xs \<in> stutter ys \<Longrightarrow> lfinite ys \<Longrightarrow> lfinite xs"
  by (induct xs rule: stutter.induct) auto

lemma [simp, intro!]: "\<langle>R\<rangle> \<subseteq> FIN"
  by (auto simp add: Stutter_def test_def FIN_def)

lemma consistent_lappend:
  "lfinite xs \<Longrightarrow> consistent (LCons x xs \<frown> LCons y ys) \<Longrightarrow> snd (llast (LCons x xs)) = fst y"
  by (induct xs arbitrary: x rule: lfinite_induct) auto

lemma [dest!]: "consistent (LCons x xs \<frown> LCons y ys) \<Longrightarrow> lfinite xs \<longrightarrow> snd (llast (LCons x xs)) = fst y"
  by (metis consistent_lappend)

lemma [simp]: "llast (LCons (\<sigma>, \<sigma>) (llist_of (replicate n (\<sigma>, \<sigma>)))) = (\<sigma>, \<sigma>)"
  by (induct n) auto

lemma [intro]: "consistent (xs \<frown> ys) \<Longrightarrow> xs \<in> \<langle>R\<rangle> \<Longrightarrow> ys \<in> \<langle>S\<rangle> \<Longrightarrow> xs \<frown> ys \<in> \<langle>R \<inter> S\<rangle>"
  apply (auto simp add: test_replicate)
  apply (rename_tac n m \<sigma>)
  apply (rule_tac x = "n + Suc m" in exI)
  apply (simp only: replicate_add lappend_llist_of_llist_of[symmetric])
  by simp

lemma [intro]: "zs \<in> stutter (xs \<frown> ys) \<Longrightarrow> consistent zs \<Longrightarrow> xs \<in> \<langle>R\<rangle> \<Longrightarrow> ys \<in> \<langle>S\<rangle> \<Longrightarrow> zs \<in> \<langle>R \<inter> S\<rangle>"
  sorry

lemma "\<pi> (\<langle>R\<rangle> \<cdot> \<langle>S\<rangle>)\<^sup>\<dagger> = \<pi> \<langle>R \<inter> S\<rangle>"
proof -
  have "\<pi> (\<langle>R\<rangle> \<cdot> \<langle>S\<rangle>)\<^sup>\<dagger> = \<pi> {xs \<frown> ys |xs ys. xs \<in> \<langle>R\<rangle> \<and> ys \<in> \<langle>S\<rangle>}\<^sup>\<dagger>"
    by (subst fin_l_prod) simp_all
  also have "... = {zs. \<exists>xs ys. consistent zs \<and> zs \<in> stutter (xs \<frown> ys) \<and> xs \<in> \<langle>R\<rangle> \<and> ys \<in> \<langle>S\<rangle>}"
    by (simp add: Aczel_def Stutter_def Con_def) auto
  also have "... = {zs'. \<exists>zs. consistent zs' \<and> zs' \<in> stutter zs \<and> zs \<in> \<langle>R \<inter> S\<rangle>}"
    apply auto
    apply (rule_tac x = x in exI)
    apply (intro conjI)
    apply (metis llist.exhaust stutter_never_LNil stutter_refl)
    apply auto
    sorry
  also have "... = \<pi> \<langle>R \<inter> S\<rangle>"
    sorry
  finally show ?thesis .
qed

lemma "\<pi> (\<langle>P\<rangle> \<union> \<langle>Q\<rangle>) = \<pi> \<langle>P \<union> Q\<rangle>"
  by (auto simp add: Aczel_def test_def Stutter_def) (metis Id_on_eqI imageI)

lemma "\<pi> (\<langle>P\<rangle> \<cdot> X\<^sup>\<dagger>) \<subseteq> \<pi> X\<^sup>\<dagger>"
  sorry

definition Aczel_mult :: "('a \<times> 'a) lan \<Rightarrow> ('a \<times> 'a) lan \<Rightarrow> ('a \<times> 'a) lan" (infixl "\<otimes>" 75) where
  "X \<otimes> Y = \<pi> (X \<cdot> Y)"

lemma amult_distl [simp]: "X \<otimes> (Y \<union> Z) = X \<otimes> Y \<union> X \<otimes> Z"
  by (simp add: Aczel_mult_def)

lemma amult_distr [simp]: "(X \<union> Y) \<otimes> Z = X \<otimes> Z \<union> Y \<otimes> Z"
  by (simp add: Aczel_mult_def)

lemma amult_assoc: "X \<otimes> (Y \<otimes> Z) = (X \<otimes> Y) \<otimes> Z"
  by (simp add: Aczel_mult_def) (metis Aczel_def Aczel_l_prod inf_commute inf_left_idem seq.mult_assoc)

lemma "\<langle>R\<rangle> \<otimes> \<langle>- R\<rangle> = {}"
  by (auto dest!: consistent_LConsE simp add: Aczel_def test_def l_prod_def Con_def Aczel_mult_def)

lemma "\<langle>R\<rangle> \<union> \<langle>- R\<rangle> = \<langle>UNIV\<rangle>"
  by (auto simp add: Aczel_def test_def)

lemma "xs \<in> stutter ys \<Longrightarrow> LCons (\<sigma>, \<sigma>) xs \<in> stutter ys" 
  by (metis lappend_code(1) stutter.stutter)

lemma stutter_LNil_lset: "xs \<in> stutter LNil \<Longrightarrow> \<forall>x\<in>lset xs. \<exists>\<sigma>. x = (\<sigma>, \<sigma>)"
  apply (induct xs rule: stutter.induct)
  apply simp
  by (metis in_lset_lappend_iff lmember_code(2) lset_lmember)

lemma stutter_LNil_lfinite: "xs \<in> stutter LNil \<Longrightarrow> lfinite xs"
  sorry

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

lemma stutter_LNil_replicate: "xs \<in> stutter LNil \<Longrightarrow> xs \<in> Con \<Longrightarrow> \<exists>n \<sigma>. xs = llist_of (replicate n (\<sigma>, \<sigma>))"
  apply (frule stutter_LNil_lfinite)
  apply (drule stutter_LNil_lset)
  apply (simp add: Con_def)
  apply (subgoal_tac "\<exists>xs'. xs = llist_of xs'")
  apply (erule exE)
  apply simp
  apply (metis consistent_replicate')
  by (metis llist_of_list_of)

lemma replicate_stutter_LNil: "llist_of (replicate n (\<sigma>, \<sigma>)) \<in> stutter LNil"
proof (induct n)
  case 0 show ?case
    by auto
next
  case (Suc n) thus ?case
    by auto (metis lappend_code(1) stutter.stutter)
qed

lemma replicate_finite_Con: "llist_of (replicate n (\<sigma>, \<sigma>)) \<in> Con"
proof (induct n)
  case 0 show ?case
    by (auto simp add: Con_def)
next
  case (Suc n) thus ?case
    by (cases n) (auto simp add: Con_def)
qed

lemma Aczel_LNil_Stutter: "\<pi> ({LNil}\<^sup>\<dagger>) = {llist_of (replicate n (\<sigma>, \<sigma>)) |n \<sigma>. True}"
  by (auto intro: stutter_LNil_replicate replicate_stutter_LNil replicate_finite_Con simp add: Stutter_def Aczel_def)

lemma Aczel_LNil_Stutter_var: "\<pi> ({LNil}\<^sup>\<dagger>) = {xs. \<exists>n \<sigma>. xs = llist_of (replicate n (\<sigma>, \<sigma>))}"
  by (auto simp add: Aczel_LNil_Stutter)

lemma "\<pi> (\<langle>R\<rangle>\<^sup>\<dagger>) \<subseteq> \<pi> ({LNil}\<^sup>\<dagger>)"
  apply (auto simp add: Aczel_LNil_Stutter_var)
  apply (auto simp add: Aczel_def Stutter_def test_def)
  by (metis lappend_code(1) stutter_LNil_replicate stutter_trans stutterp.simps stutterp_stutter_eq)

end
