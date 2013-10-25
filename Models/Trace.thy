theory Trace
  imports Aczel Mumble_Language Rely_Guarantee Algebra
begin

no_notation shuffle (infixl "\<parallel>" 75)
no_notation l_prod (infixl "\<cdot>" 80)

quotient_type 'a trace = "('a \<times> 'a) lan" / "\<lambda>X Y. X\<^sup>\<dagger> = Y\<^sup>\<dagger>"
  by (intro equivpI reflpI sympI transpI) auto

(* traces form a dioid *)

instantiation trace :: (type) dioid_one_zerol
begin

  lift_definition less_eq_trace :: "'a trace \<Rightarrow> 'a trace \<Rightarrow> bool" is "\<lambda>X Y. X\<^sup>\<dagger> \<subseteq> Y\<^sup>\<dagger>"
    by simp

  lift_definition less_trace :: "'a trace \<Rightarrow> 'a trace \<Rightarrow> bool" is "\<lambda>X Y. X\<^sup>\<dagger> \<subset> Y\<^sup>\<dagger>"
    by simp

  lift_definition zero_trace :: "'a trace" is "{}" done

  lift_definition one_trace :: "'a trace" is "{LNil}" done

  lift_definition times_trace :: "'a trace \<Rightarrow> 'a trace \<Rightarrow> 'a trace" is "\<lambda>X Y. l_prod X\<^sup>\<dagger> Y\<^sup>\<dagger>"
    by simp

  lift_definition plus_trace :: "'a trace \<Rightarrow> 'a trace \<Rightarrow> 'a trace" is "op \<union>"
    by simp

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
      by transfer (metis Mumble_union par.add_commute sup.order_iff)
    show "(x < y) = (x \<le> y \<and> x \<noteq> y)"
      by transfer (metis par.less_def)
    show "x + x = x"
      by transfer simp
    show "x \<cdot> (y + z) = x \<cdot> y + x \<cdot> z"
      by transfer simp
  qed
end

no_notation Aczel ("\<pi>")

lift_definition Aczel_trace :: "'a trace \<Rightarrow> 'a trace" ("\<pi>") is "\<lambda>X. Aczel X\<^sup>\<dagger>" by simp

(* \<pi> is an interior operator *)

lemma proj_coextensive [intro!]: "\<pi> x \<le> x"
  by transfer (metis Aczel_coextensive Mumble_idem Mumble_iso)

lemma proj_iso [intro]: "x \<le> y \<Longrightarrow> \<pi> x \<le> \<pi> y"
  by transfer (metis Aczel_iso Mumble_iso)

lemma [simp]: "(Aczel x\<^sup>\<dagger>)\<^sup>\<dagger> = (Aczel x)\<^sup>\<dagger>"
  by (auto simp add: Aczel_def Con_def Mumble_def) (metis mumble_preserves_consistent mumble_trans)

lemma proj_idem [simp]: "\<pi> (\<pi> x) = \<pi> x"
  by transfer simp

lemma proj_plus [simp]: "\<pi> x + \<pi> y = \<pi> (x + y)"
  by transfer (metis Aczel_union Mumble_union)

lemma proj_mult [simp]: "\<pi> (\<pi> x \<cdot> \<pi> y) = \<pi> (x \<cdot> y)"
  by transfer simp

lemma proj_mult2 [simp]: "\<pi> (\<pi> x \<cdot> y) = \<pi> (x \<cdot> y)"
  by transfer (metis Aczel_trace.abs_eq proj_idem proj_mult times_trace.abs_eq trace.abs_eq_iff)

lemma proj_mult3 [simp]: "\<pi> (x \<cdot> \<pi> y) = \<pi> (x \<cdot> y)"
  by (metis proj_mult proj_mult2)

(* Tests *)

no_notation atomic ("\<langle>_\<rangle>" [0] 1000)

lift_definition atomic_trace :: "'a rel \<Rightarrow> 'a trace" ("\<langle>_\<rangle>" [0] 1000) is "\<lambda>S. atomic S" by simp

definition test :: "'a set \<Rightarrow> 'a trace" where
  "test X = \<langle>Id_on X\<rangle>"

lemma atomic_test: "atomic (Id_on X) = {LCons (\<sigma>, \<sigma>') LNil |\<sigma> \<sigma>'. \<sigma> \<in> X \<and> \<sigma> = \<sigma>'}"
  sorry

lemma "\<pi> (test (X \<inter> Y)) \<le> \<pi> (test X \<cdot> test Y)"
  apply (simp only: test_def)
  apply transfer
  apply (simp add: atomic_test)
  apply (subst fin_l_prod)
  apply (force simp add: FIN_def)
  apply (auto simp add: Aczel_def Con_def Mumble_def)
  apply (rule_tac x = "mumble (LCons (\<sigma>, \<sigma>) (LCons (\<sigma>, \<sigma>) LNil))" in exI)
  apply (intro conjI)
  apply (rule_tac x = "LCons (\<sigma>, \<sigma>) (LCons (\<sigma>, \<sigma>) LNil)" in exI)
  apply (metis LCons_lappend_LNil inconsistent_mumble lappend_code(1) lfinite.simps)
  by (metis lappend_code(1) mumble.mumble mumble.self mumble_trans)

lemma [dest!]: "ys \<frown> LCons z (LCons z' zs) = LCons x LNil \<Longrightarrow> False"
  apply (cases "lfinite ys")
  apply (rotate_tac 1)
  apply (induct ys rule: lfinite.induct)
  by (simp_all add: lappend_inf)

lemma [dest!]: "xs \<in> mumble (LCons x LNil) \<Longrightarrow> xs = LCons x LNil"
  by (induct xs rule: mumble.induct) auto

lemma Mumble_atomic [simp]: "(atomic X)\<^sup>\<dagger> = atomic X"
  by (auto simp add: Mumble_def atomic_def image_def)

lemma "\<langle>X\<rangle> + \<langle>Y\<rangle> = \<langle>X \<union> Y\<rangle>"
  by transfer (metis Mumble_atomic atomic_def image_Un)

(* traces form a dioid w.r.t. parallel composition *)

instantiation trace :: (type) par_dioid
begin

  lift_definition par_trace :: "'a trace \<Rightarrow> 'a trace \<Rightarrow> 'a trace" is "\<lambda>X Y. (shuffle X\<^sup>\<dagger> Y\<^sup>\<dagger>)\<^sup>\<dagger>"
    by simp

  instance proof
    fix x y z :: "'a trace"
    show "x \<parallel> (y \<parallel> z) = x \<parallel> y \<parallel> z"
      by transfer (simp add: shuffle_assoc)
    show "x \<parallel> y = y \<parallel> x"
      by transfer (metis shuffle_comm)
    show "x \<parallel> (y + z) = x \<parallel> y + x \<parallel> z"
      by transfer (metis Mumble_union par.distrib_left)
    show "1 \<parallel> x = x"
      by transfer (metis Mumble_shuffle_left par.mult.right_neutral shuffle_comm)
    show "0 \<parallel> x = 0"
      by transfer simp
  qed
end

instance trace :: (type) weak_trioid by default

instantiation trace :: (type) lattice
begin

  lift_definition inf_trace :: "'a trace \<Rightarrow> 'a trace \<Rightarrow> 'a trace" is "\<lambda>X Y. X\<^sup>\<dagger> \<inter> Y\<^sup>\<dagger>"
    by simp

  lift_definition sup_trace :: "'a trace \<Rightarrow> 'a trace \<Rightarrow> 'a trace" is "op \<union>"
    by simp

  instance proof
    fix x y z :: "'a trace"
    show "x \<sqinter> y \<le> x"
      by transfer simp
    show "x \<sqinter> y \<le> y"
      by transfer simp
    show "x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> y \<sqinter> z"
      by transfer simp
    show "x \<le> x \<squnion> y"
      by transfer simp
    show "y \<le> x \<squnion> y"
      by transfer simp
    show "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y \<squnion> z \<le> x"
      by transfer simp
  qed
end

lift_definition stuttering :: "'a trace" is stutter done

lemma join_is_plus [simp]:
  fixes x y :: "'a trace"
  shows "x \<squnion> y = x + y"
  by transfer simp

instance trace :: (type) distrib_lattice
  by (default, transfer, simp, metis Mumble_idem Mumble_meet Mumble_union Un_Int_distrib)

no_notation Language.star ("_\<^sup>\<star>" [101] 100)

instantiation trace :: (type) left_kleene_algebra
begin

  lift_definition star_trace :: "'a trace \<Rightarrow> 'a trace" is "\<lambda>x. Language.star x\<^sup>\<dagger>"
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

instantiation trace :: (type) rely_guarantee_trioid
begin

  lift_definition RG_trace :: "'a trace set" is "{x. \<exists>R. x = Language.star (atomic R)}" done

  lift_definition \<C>_trace :: "'a trace" is Aczel.Con done

  instance
  proof
    fix r s x y :: "'a trace"
    show "(1::'a trace) \<in> RG"
      by transfer (auto intro: exI[of _ "{LNil}"] exI[of _ "{}"] simp add: image_def)



lemma "\<pi> (test X \<cdot> test Y \<parallel> stuttering) = \<pi> (test (X \<inter> Y) \<parallel> stuttering)"
  sorry

definition proj_eq :: "'a trace \<Rightarrow> 'a trace \<Rightarrow> bool" (infix "=\<^sub>\<pi>" 55) where
  "x =\<^sub>\<pi> y \<equiv> \<pi> x = \<pi> y"

lemma proj_eq_trans [trans]: "x =\<^sub>\<pi> y \<Longrightarrow> y =\<^sub>\<pi> z \<Longrightarrow> x =\<^sub>\<pi> z"
  by (simp add: proj_eq_def)

no_notation Aczel_mult (infixl "\<otimes>" 75)

definition pmult :: "'a trace \<Rightarrow> 'a trace \<Rightarrow> 'a trace" (infixl "\<otimes>" 75) where
  "x \<otimes> y = \<pi> (x \<cdot> y)"

lemma [simp]: "\<pi> (x \<otimes> y) = x \<otimes> y"
  by (simp add: pmult_def)

lemma pmult_onel [simp]: "1 \<otimes> x = \<pi> x"
  by (metis mult_onel pmult_def)

lemma pmult_oner [simp]: "x \<otimes> 1 = \<pi> x"
  by (metis mult_oner pmult_def)

lemma proj_zero [simp]: "\<pi> 0 = 0"
  by transfer simp

lemma pmult_zero [simp]: "0 \<otimes> x = 0"
  by (simp add: pmult_def)

interpretation proj!: dioid "op +" "op \<otimes>" "op \<le>" "op <"
proof
  fix x y z :: "'a trace"
  show "(x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"
    by (simp add: pmult_def mult_assoc)
  show "(x + y) \<otimes> z = x \<otimes> z + y \<otimes> z"
    by (simp add: pmult_def distrib_right)
  show "x \<otimes> (y + z) = x \<otimes> y + x \<otimes> z"
    by (simp add: pmult_def distrib_left)
  show "x + x = x"
    by (metis add_idem)
qed

definition proj_leq :: "'a trace \<Rightarrow> 'a trace \<Rightarrow> bool" (infixl "\<le>\<^sub>\<pi>" 55) where
  "x \<le>\<^sub>\<pi> y \<equiv> (\<pi> x \<le> \<pi> y)"

lemma proj_leq_trans [trans]: "x \<le>\<^sub>\<pi> y \<Longrightarrow> y \<le>\<^sub>\<pi> z \<Longrightarrow> x \<le>\<^sub>\<pi> z"
  by (auto simp add: proj_leq_def)

lemma proj_leq_trans2 [trans]: "x \<le> y \<Longrightarrow> y \<le>\<^sub>\<pi> z \<Longrightarrow> x \<le>\<^sub>\<pi> z"
  by (auto simp add: proj_leq_def) (metis dual_order.trans proj_iso)

lemma proj_leq_trans3 [trans]: "x \<le>\<^sub>\<pi> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le>\<^sub>\<pi> z"
  by (metis proj_iso proj_leq_def proj_leq_trans)

lemma proj_leq_trans4 [trans]: "x \<le>\<^sub>\<pi> y \<Longrightarrow> y =\<^sub>\<pi> z \<Longrightarrow> x \<le>\<^sub>\<pi> z"
  by (auto simp add: proj_leq_def proj_eq_def)

lemma proj_leq_trans5 [trans]: "x =\<^sub>\<pi> y \<Longrightarrow> y \<le>\<^sub>\<pi> z \<Longrightarrow> x \<le>\<^sub>\<pi> z"
  by (auto simp add: proj_leq_def proj_eq_def)

lemma proj_meet [simp]: "\<pi> x \<sqinter> \<pi> y = \<pi> (x \<sqinter> y)"
  apply transfer
  apply (simp add: Aczel_def)
  by (metis Aczel_def Int_assoc Mumble_Con Mumble_meet inf_commute inf_left_idem)

lemma proj_leq_meet [simp]: "\<pi> x \<sqinter> \<pi> y \<le>\<^sub>\<pi> x \<sqinter> y"
  by (metis inf_mono proj_coextensive proj_iso proj_leq_def)

lemma [iff]: "x \<le>\<^sub>\<pi> y \<sqinter> z \<longleftrightarrow> x \<le>\<^sub>\<pi> y \<and> x \<le>\<^sub>\<pi> z"
  by (simp add: proj_leq_def) (metis inf.bounded_iff proj_meet)

end