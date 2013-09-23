theory Aczel
  imports Language
begin

coinductive transitions :: "'a llist \<Rightarrow> 'a set llist \<Rightarrow> bool" where
  tr_LNil [intro!]: "transitions LNil LNil"
| tr_LCons [intro]: "t \<in> x \<Longrightarrow> transitions ts xs \<Longrightarrow> transitions (LCons t ts) (LCons x xs)"

lemma [elim]: "transitions (LCons t ts) (LCons x xs) \<Longrightarrow> transitions ts xs"
  by (metis LNil_not_LCons transitions.simps ltl_LCons)

lemma [elim]: "transitions (LCons t ts) (LCons x xs) \<Longrightarrow> t \<in> x"
  by (metis LCons_inject LNil_not_LCons transitions.simps)

lemma [simp]: "transitions t LNil \<longleftrightarrow> t = LNil"
  by (metis LNil_not_LCons transitions.simps)

lemma [simp]: "transitions LNil xs \<longleftrightarrow> xs = LNil"
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
| EqPair [intro]: "snd \<sigma> = fst \<sigma>' \<Longrightarrow> consistent (LCons \<sigma>' t) \<Longrightarrow> consistent (LCons \<sigma> (LCons \<sigma>' t))"

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

lemma "lfinite xs \<Longrightarrow> (tr' xs \<inter> Con) \<cdot> (tr' ys \<inter> Con) = tr' xs \<cdot> tr' ys \<inter> Con"
proof (induct xs rule: lfinite_induct)
  case Nil show ?case by simp
next
  case (Cons x xs)
  thus ?case
    sorry
qed

lemma tr_FIN: "lfinite xs \<Longrightarrow> tr xs \<subseteq> FIN"
  by (auto dest!: transitions_llength simp add: FIN_def tr_def lfinite_conv_llength_enat)

lemma tr_infinite: "\<not> lfinite xs \<Longrightarrow> tr xs \<cdot> {} = tr xs"
  apply (auto simp add: l_prod_def tr_def)
  apply (drule transitions_llength)
  by (metis lfinite_conv_llength_enat)

lemma tr_append: "tr (xs \<frown> ys) = (tr xs \<cdot> tr ys) \<inter> Con"
  sorry
(*
proof (cases "lfinite xs")
  assume "lfinite xs"
  hence "tr xs \<subseteq> FIN"
    by (metis tr_FIN)
  hence "tr (xs \<frown> ys) = (tr xs \<cdot> tr ys) \<inter> Con"
    apply (simp add: fin_l_prod)
    apply (subst tr_def)
*)

lemma Tr_l_prod: "Tr (X \<cdot> Y) = (Tr X \<cdot> Tr Y) \<inter> Con"
  sorry

lemma Tr_union: "Tr (X \<union> Y) = Tr X \<union> Tr Y"
  by (simp add: Tr_def)

end
