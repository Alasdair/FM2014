theory Trace
  imports Aczel Mumble_Language Rely_Guarantee Algebra
begin        

no_notation shuffle (infixl "\<parallel>" 75)
no_notation l_prod (infixl "\<cdot>" 80)
no_notation Aczel ("\<pi>")

quotient_type 'a trace = "('a \<times> 'a) lan" / "\<lambda>X Y. (X \<inter> FIN)\<^sup>\<dagger> = (Y \<inter> FIN)\<^sup>\<dagger>"
  by (intro equivpI reflpI sympI transpI) auto

(* traces form a dioid *)

instantiation trace :: (type) dioid_one_zerol
begin

  lift_definition less_eq_trace :: "'a trace \<Rightarrow> 'a trace \<Rightarrow> bool" is "\<lambda>X Y. (X \<inter> FIN)\<^sup>\<dagger> \<subseteq> (Y \<inter> FIN)\<^sup>\<dagger>"
    by simp

  lift_definition less_trace :: "'a trace \<Rightarrow> 'a trace \<Rightarrow> bool" is "\<lambda>X Y. (X \<inter> FIN)\<^sup>\<dagger> \<subset> (Y \<inter> FIN)\<^sup>\<dagger>"
    by simp

  lift_definition zero_trace :: "'a trace" is "{}" done

  lift_definition one_trace :: "'a trace" is "{LNil}" done

  lift_definition times_trace :: "'a trace \<Rightarrow> 'a trace \<Rightarrow> 'a trace" is "\<lambda>X Y. l_prod (X \<inter> FIN)\<^sup>\<dagger> (Y \<inter> FIN)\<^sup>\<dagger>"
    by simp

  lift_definition plus_trace :: "'a trace \<Rightarrow> 'a trace \<Rightarrow> 'a trace" is "op \<union>"
    by (metis Mumble_union distrib_lattice_class.inf_sup_distrib2)

  instance
  proof
    fix x y z :: "'a trace"
    show "(x + y) + z = x + (y + z)"
      by transfer (simp only: Un_assoc)
    show "x + y = y + x"
      by transfer simp
    show "(x \<cdot> y) \<cdot> z = x \<cdot> (y \<cdot> z)"
      by transfer (simp add: l_prod_assoc)
    show "(x + y) \<cdot> z = x \<cdot> z + y \<cdot> z"
      by transfer simp
    show "1 \<cdot> x = x"
      by transfer simp
    show "x \<cdot> 1 = x"
      by transfer simp
    show "0 + x = x"
      by transfer simp
    show "0 \<cdot> x = 0"
      by transfer simp
    show "(x \<le> y) = (x + y = y)"
      by transfer auto
    show "(x < y) = (x \<le> y \<and> x \<noteq> y)"
      by transfer (metis par.less_def)
    show "x + x = x"
      by transfer simp
    show "x \<cdot> (y + z) = x \<cdot> y + x \<cdot> z"
      by transfer simp
  qed
end

(* traces form a dioid w.r.t. parallel composition *)

lemma [simp]: "(shuffle (x\<^sup>\<dagger> \<inter> FIN) (y\<^sup>\<dagger> \<inter> FIN))\<^sup>\<dagger> \<inter> FIN = (shuffle x y)\<^sup>\<dagger> \<inter> FIN"
  apply (subst Mumble_FIN[symmetric]) back back by simp

lemma [simp]: "{LNil} \<inter> FIN = {LNil}"
  by (simp add: FIN_def)

instantiation trace :: (type) par_dioid
begin

  lift_definition par_trace :: "'a trace \<Rightarrow> 'a trace \<Rightarrow> 'a trace" is "\<lambda>X Y. (shuffle (X \<inter> FIN)\<^sup>\<dagger> (Y \<inter> FIN)\<^sup>\<dagger>)\<^sup>\<dagger>"
    by simp

  instance proof
    fix x y z :: "'a trace"
    show "x \<parallel> (y \<parallel> z) = (x \<parallel> y) \<parallel> z"
      by transfer (simp add: shuffle_assoc)
    show "x \<parallel> y = y \<parallel> x"
      by transfer (metis shuffle_comm)
    show "x \<parallel> (y + z) = x \<parallel> y + x \<parallel> z"
      by transfer simp
    show "1 \<parallel> x = x"
      by transfer simp
    show "0 \<parallel> x = 0"
      by transfer simp
  qed
end

instance trace :: (type) weak_trioid by default

instantiation trace :: (type) lattice
begin

  lift_definition inf_trace :: "'a trace \<Rightarrow> 'a trace \<Rightarrow> 'a trace" is "\<lambda>X Y. (X \<inter> FIN)\<^sup>\<dagger> \<inter> (Y \<inter> FIN)\<^sup>\<dagger>"
    by simp

  lift_definition sup_trace :: "'a trace \<Rightarrow> 'a trace \<Rightarrow> 'a trace" is "op \<union>"
    by simp

  instance proof
    fix x y z :: "'a trace"
    show "x \<sqinter> y \<le> x"
      apply transfer
      apply simp
      by (metis Mumble_idem Mumble_iso inf.cobounded2 inf.coboundedI2 inf_commute)
    show "x \<sqinter> y \<le> y"
      apply transfer
      apply simp
      by (metis Mumble_idem Mumble_iso inf.cobounded2 inf.coboundedI2 inf_commute)
    show "x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> y \<sqinter> z"
      apply transfer
      by (metis (hide_lams, no_types) Mumble_FIN Mumble_meet inf.bounded_iff)
    show "x \<le> x \<squnion> y"
      by transfer simp
    show "y \<le> x \<squnion> y"
      by transfer simp
    show "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y \<squnion> z \<le> x"
      by transfer simp
  qed
end

instance trace :: (type) distrib_lattice
  apply default
  apply transfer
  apply simp
  by (metis (lifting, no_types) Int_commute Mumble_FIN Mumble_idem Mumble_union Un_commute distrib_lattice_class.sup_inf_distrib1 lattice_class.sup_inf_absorb)

no_notation Language.star ("_\<^sup>\<star>" [101] 100)

instantiation trace :: (type) left_kleene_algebra
begin

  lift_definition star_trace :: "'a trace \<Rightarrow> 'a trace" is "\<lambda>x. Language.star (x\<^sup>\<dagger>"
    by simp

  instance
  proof
    fix x y z :: "'a trace"
    show "1 + x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
      by transfer (metis Mumble_l_prod Mumble_star Mumble_union par.less_eq_def seq.add_idem' seq.star_unfoldl_eq)
    show "z + x \<cdot> y \<le> y \<longrightarrow> x\<^sup>\<star> \<cdot> z \<le> y"
      by transfer (metis Mumble_ext Mumble_idem Mumble_iso Mumble_l_prod order.trans seq.star_inductl)
  qed
end

lemma [dest!]: "ys \<frown> LCons z (LCons z' zs) = LCons x LNil \<Longrightarrow> False"
  apply (cases "lfinite ys")
  apply (rotate_tac 1)
  apply (induct ys rule: lfinite.induct)
  by (simp_all add: lappend_inf)

lemma [dest!]: "xs \<in> mumble (LCons x LNil) \<Longrightarrow> xs = LCons x LNil"
  by (induct xs rule: mumble.induct) auto

lemma Mumble_atomic [simp]: "(atomic X)\<^sup>\<dagger> = atomic X"
  by (auto simp add: Mumble_def atomic_def image_def)

lemma join_is_plus [simp]:
  fixes x y :: "'a trace"
  shows "x \<squnion> y = x + y"
  by transfer simp

lemma [simp]: "set_rel (llist_all2 (prod_rel op = op =)) x y \<longleftrightarrow> x = y"
  by (auto simp add: prod_rel_eq set_rel_def)

lemma [simp]: "pcr_trace op = x y \<longleftrightarrow> abs_trace x = y"
  by (simp add: pcr_trace_def OO_def cr_trace_def)

lemma [simp]: "abs_trace X = Abs_trace {Y. X\<^sup>\<dagger> = Y\<^sup>\<dagger>}"
  apply (auto simp add: abs_trace_def)
  apply (subst quot_type.abs_def[of _ _ Rep_trace])
  apply (auto simp add: quot_type_def)
  apply (metis equivp_implies_part_equivp trace_equivp)
  defer
  apply (metis Rep_trace_inverse)
  apply (erule rev_mp)+
  apply (subst Abs_trace_inverse)
  apply auto
  apply (erule rev_mp)+
  apply (subst Abs_trace_inverse)
  apply auto
  apply (subst Abs_trace_inverse)
  apply auto
  apply (metis Rep_trace_inject)
  apply (insert Rep_trace)
  by auto

lemma [transfer_rule]: "(pcr_trace op = ===> set_rel (pcr_trace op =) ===> op =) (\<lambda>X Y. X\<^sup>\<dagger> \<in> Mumble ` Y) op \<in>"
  apply (auto simp add: fun_rel_def set_rel_def image_def)
  apply (erule_tac x = "Abs_trace {Y. x\<^sup>\<dagger> = Y\<^sup>\<dagger>}" in ballE)
  apply auto
  apply (rule_tac x = xb in bexI)
  apply simp_all
  apply (erule rev_mp)+
  apply (subst Abs_trace_inject)
  by auto

lemma [transfer_rule]: "(op = ===> pcr_trace op = ===> op =) (\<lambda>x y. x = Abs_trace {Y. y\<^sup>\<dagger> = Y\<^sup>\<dagger>}) op ="
  by (auto simp add: fun_rel_def)

lemma atomic_star_lfinite: "xs \<in> star (atomic R) \<Longrightarrow> lfinite xs"
  apply (erule rev_mp)
  apply (subst star_power_fin)
  apply (auto simp add: powers_def)
  by (metis rely_power1)

lemma atomic_star_lset: "xs \<in> star (atomic R) \<Longrightarrow> lset xs \<subseteq> R"
  by (metis (lifting) mem_Collect_eq rely_def)

lemma atomic_star_elemI [intro]: "lfinite xs \<Longrightarrow> lset xs \<subseteq> R \<Longrightarrow> xs \<in> star (atomic R)"
proof (induct xs rule: lfinite.induct)
  case lfinite_LNil
  thus ?case
    by (metis (lifting) lfinite_LNil.prems lfinite_code(1) mem_Collect_eq rely_def)
next
  case (lfinite_LConsI xs x)
  thus ?case
    apply auto
    apply (erule rev_mp)+
    apply (subst star_power_fin, metis atom_finite)+
    apply (auto simp add: powers_def)
    apply (rule_tac x = "Language.power (atomic R) (Suc i)" in exI)
    apply auto
    apply (rule_tac x = "Suc i" in exI)
    apply (auto simp add: l_prod_def)
    apply (rule_tac x = "LCons x LNil" in exI)
    apply (rule_tac x = xs in exI)
    by (auto simp add: atomic_def)
qed

lemma mumble_star1: "ys \<in> mumble xs \<Longrightarrow> xs \<in> star (atomic R) \<Longrightarrow> ys \<in> star (atomic (trancl R))"
  apply (induct ys rule: mumble.induct)
  apply (erule set_rev_mp)
  apply (rule seq.star_iso[rule_format])
  apply simp
  apply (metis r_into_trancl' subsetI)
  apply auto
  apply (frule atomic_star_lfinite)
  apply simp
  apply (erule conjE)
  apply (drule atomic_star_lset)
  apply (rule atomic_star_elemI)
  by auto

lemma O_member: "x \<in> (R O S) \<Longrightarrow> (\<exists>\<sigma> \<sigma>' \<sigma>''. (\<sigma>, \<sigma>') \<in> R \<and> (\<sigma>', \<sigma>'') \<in> S)"
  by auto

lemma mumble_head [intro!]: "LCons (\<sigma>, \<sigma>'') xs \<in> mumble (LCons (\<sigma>, \<sigma>') (LCons (\<sigma>', \<sigma>'') xs))"
proof -
  have "LCons (\<sigma>, \<sigma>') (LCons (\<sigma>', \<sigma>'') xs) \<in> mumble (LCons (\<sigma>, \<sigma>') (LCons (\<sigma>', \<sigma>'') xs))"
    by (metis mumble.self)
  thus "LCons (\<sigma>, \<sigma>'') xs \<in> mumble (LCons (\<sigma>, \<sigma>') (LCons (\<sigma>', \<sigma>'') xs))"
    by (rule mumble[where ys = LNil, simplified])
qed

lemma trancl_to_llist: "x \<in> trancl R \<Longrightarrow> \<exists>xs. lfinite xs \<and> lset xs \<subseteq> R \<and> LCons x LNil \<in> mumble xs"
proof (auto simp add: trancl_power)
  fix n
  assume "x \<in> R ^^ n" and "0 < n"
  then obtain m where "n = Suc m"
    by (metis gr_implies_not0 list_decode.cases)
  hence "x \<in> R ^^ Suc m"
    by (metis `x \<in> R ^^ n`)
  thus "\<exists>xs. lfinite xs \<and> lset xs \<subseteq> R \<and> LCons x LNil \<in> mumble xs"
  proof (induct m arbitrary: x)
    case 0 thus ?case
      by (rule_tac x = "LCons x LNil" in exI) auto
  next
    case (Suc n) note ih = this[simplified]
    then obtain \<sigma> \<sigma>' \<sigma>'' where split1: "(\<sigma>, \<sigma>') \<in> R ^^ n O R" and split2: "(\<sigma>', \<sigma>'') \<in> R" and x_def [simp]: "x = (\<sigma>, \<sigma>'')"
      by auto
    show ?case using ih(1)[OF split1] and split2
      apply auto
      apply (rule_tac x = "xs \<frown> LCons (\<sigma>', \<sigma>'') LNil" in exI)
      apply auto
      apply (rule mumble_trans[of _ "LCons (\<sigma>, \<sigma>') LNil \<frown> LCons (\<sigma>', \<sigma>'') LNil"])
      defer
      apply (rule mumble_lappend)
      by auto
  qed
qed

lemma mumble_LNil [iff]: "xs \<in> mumble LNil \<longleftrightarrow> xs = LNil"
  apply auto
  apply (induct xs rule: mumble.induct)
  by auto

lemma mumble_star2: "lfinite xs \<Longrightarrow> lset xs \<subseteq> R\<^sup>+ \<Longrightarrow> \<exists>X. (\<exists>xs. X = mumble xs \<and> lfinite xs \<and> lset xs \<subseteq> R) \<and> xs \<in> X"
proof (induct xs rule: lfinite.induct)
  case lfinite_LNil
  thus ?case
    by (rule_tac x = "{LNil}" in exI) auto
next
  case (lfinite_LConsI xs x)
  thus ?case
    apply auto
    apply (drule trancl_to_llist)
    apply auto
    apply (rename_tac xs ys)
    apply (rule_tac x = "mumble (ys \<frown> xs)" in exI)
    apply (intro conjI)
    apply (rule_tac x = "ys \<frown> xs" in exI)
    apply auto
    by (metis LCons_lappend_LNil mumble_lappend)
qed

lemma Mumble_atomic_star: "(star (atomic R))\<^sup>\<dagger> = star (atomic (trancl R))"
  apply (auto simp add: Mumble_def)
  apply (metis mumble_star1)
  by (metis atomic_star_elemI atomic_star_lfinite atomic_star_lset mumble_star2)

lemma Mumble_Inter_Con [simp]: "x\<^sup>\<dagger> \<inter> Con = (x \<inter> Con)\<^sup>\<dagger>"
  by (auto simp add: Con_def Mumble_def)

instantiation trace :: (type) rely_guarantee_trioid
begin

  lift_definition RG_trace :: "'a trace set" is "{x. \<exists>R. x = Language.star (atomic R)}" done

  lift_definition C_trace :: "'a trace" is Aczel.Con done

  instance
  proof
    fix r s x y z :: "'a trace"
    show "(1::'a trace) \<in> RG"
      by transfer (auto intro: exI[of _ "{LNil}"] exI[of _ "{}"] simp add: image_def)

    show "x \<cdot> y \<sqinter> C \<le> (x \<sqinter> C) \<cdot> (y \<sqinter> C) \<sqinter> C"
      apply transfer using Aczel_l_prod by (auto intro!: Mumble_iso simp add: Aczel_def)
      
    show "x\<^sup>\<star> \<sqinter> C \<le> (x \<sqinter> C)\<^sup>\<star> \<sqinter> C"
      apply transfer
      apply (auto intro!: Mumble_iso)
      by (metis Aczel_def Aczel_star Int_iff)

    show "x + y \<sqinter> z = (x + y) \<sqinter> (x + z)"
      apply transfer
      apply simp
      by (metis Mumble_meet Mumble_union Un_Int_distrib inf_sup_absorb)

    assume r_rg: "r \<in> RG"

    from r_rg show "r \<parallel> r \<le> r"
      apply transfer
      apply (simp add: image_def)
      apply (erule exE)
      apply (erule conjE)
      apply (erule exE)
      by (metis Mumble_shuffle_right Un_absorb order_refl rely_union shuffle_comm)

    from r_rg show "r \<parallel> x \<cdot> y = (r \<parallel> x) \<cdot> (r \<parallel> y)"
      apply transfer
      apply (simp add: image_def)
      apply (erule exE)
      apply (erule conjE)
      apply (erule exE)
      apply simp
      apply (subst Mumble_shuffle_left[symmetric])
      apply (subst Mumble_l_prod[symmetric])
      apply (subst Mumble_shuffle_left[symmetric]) back
      apply (subst Mumble_shuffle_left[symmetric]) back back
      apply (erule ssubst)
      by simp

    from r_rg show "r \<parallel> x\<^sup>\<star> \<cdot> x \<le> (r \<parallel> x)\<^sup>\<star> \<cdot> (r \<parallel> x)"
      apply transfer
      apply (simp add: image_def)
      apply (erule exE)
      apply (erule conjE)
      apply (erule exE)
      apply simp
      apply (subst Mumble_l_prod[symmetric])
      apply (subst Mumble_shuffle_left[symmetric])
      apply (subst Mumble_shuffle_left[symmetric]) back
      apply (subst Mumble_star[symmetric])
      apply (subst Mumble_shuffle_left[symmetric]) back
      apply (erule ssubst)
      apply simp
      apply (rule Mumble_iso)
      by (metis eq_iff rely_l_prod rely_star)

    from r_rg show "r \<parallel> x\<^sup>\<star>\<cdot>x \<le> (r \<parallel> x) \<cdot> (r \<parallel> x)\<^sup>\<star>"
      sorry

    assume s_rg: "s \<in> RG"

    from r_rg and s_rg show "r \<parallel> s \<in> RG"
      apply transfer
      apply (auto simp add: image_def)
      by (metis Mumble_shuffle_left rely_union shuffle_comm)

    from r_rg and s_rg show "r \<sqinter> s \<in> RG"
      apply transfer
      apply (auto simp add: image_def)
      apply (rename_tac r s R S)
      apply (rule_tac x = "star (atomic (R\<^sup>+ \<inter> S\<^sup>+))" in exI)
      apply (intro conjI)
      apply blast
      by (metis Mumble_meet Mumble_atomic_star rely_inter)

    from r_rg and s_rg show "r \<le> r \<parallel> s"
      apply transfer
      apply (auto simp add: image_def)
      by (metis (hide_lams, no_types) Mumble_shuffle_right Mumble_atomic_star in_mono rely_1 shuffle_mumble1)
  qed
end

no_notation atomic ("\<langle>_\<rangle>" [0] 1000)

lift_definition atomic_trace :: "'a rel \<Rightarrow> 'a trace" ("\<langle>_\<rangle>" [0] 1000) is "\<lambda>S. atomic S" by simp

definition test :: "'a set \<Rightarrow> 'a trace" where
  "test X = \<langle>Id_on X\<rangle>"

lemma atomic_test: "atomic (Id_on X) = {LCons (\<sigma>, \<sigma>') LNil |\<sigma> \<sigma>'. \<sigma> \<in> X \<and> \<sigma> = \<sigma>'}"
  by (auto simp add: atomic_def image_def Id_on_def)

lemma "\<pi> (test (X \<inter> Y)) \<le> \<pi> (test X \<cdot> test Y)"
  apply (simp only: test_def proj_def)
  apply transfer
  apply (simp add: atomic_test)
  apply (subst fin_l_prod)
  apply (force simp add: FIN_def)
  apply (auto simp add: Aczel_def Con_def Mumble_def)
  apply (rule_tac x = "mumble (LCons (\<sigma>, \<sigma>) (LCons (\<sigma>, \<sigma>) LNil))" in exI)
  apply (intro conjI)
  apply (rule_tac x = "LCons (\<sigma>, \<sigma>) (LCons (\<sigma>, \<sigma>) LNil)" in exI)
  apply (metis LCons_lappend_LNil inconsistent_mumble lappend_code(1) lfinite.simps)
  by (metis lappend_code(1) mumble.mumble mumble.self)

lemma "\<langle>X\<rangle> + \<langle>Y\<rangle> = \<langle>X \<union> Y\<rangle>"
  by transfer (metis Mumble_atomic atomic_def image_Un)

lift_definition stuttering :: "'a trace" is stutter done

instantiation trace :: (type) complete_lattice
begin

  lift_definition Sup_trace :: "'a trace set \<Rightarrow> 'a trace" is "Union"
    by (auto simp add: Mumble_continuous set_rel_def) metis+
 
  lift_definition Inf_trace :: "'a trace set \<Rightarrow> 'a trace" is "\<lambda>X. Inter (Mumble ` X)"
    apply (rule arg_cong) back
    apply (simp add: set_rel_def)
    apply safe
    by (metis INT_iff)+

  lift_definition bot_trace :: "'a trace" is "{}" done

  lift_definition top_trace :: "'a trace" is "UNIV" done

  instance
  proof
    fix x :: "'a trace" and A :: "'a trace set"
    assume "x \<in> A"
    thus "\<Sqinter>A \<le> x"
      by (transfer, simp only: Mumble_Inter, auto simp add: image_def Mumble_def)
  next
    fix x :: "'a trace" and A :: "'a trace set"
    assume "x \<in> A"
    thus "x \<le> \<Squnion>A"
      by transfer (auto simp add: Mumble_continuous)
  next
    fix z :: "'a trace" and A :: "'a trace set"
    assume "\<And>x. x \<in> A \<Longrightarrow> z \<le> x"
    thus "z \<le> \<Sqinter>A"
      by transfer (simp only: Mumble_Inter, auto)
  next
    fix z :: "'a trace" and A :: "'a trace set"
    assume "\<And>x. x \<in> A \<Longrightarrow> x \<le> z"
    thus "\<Squnion>A \<le> z"
      by transfer (auto simp add: Mumble_continuous)
  next
    show "\<Sqinter>({}::'a trace set) = \<top>"
      by transfer simp
  next
    show "\<Squnion>({}::'a trace set) = \<bottom>"
      by transfer simp
  qed
end

end