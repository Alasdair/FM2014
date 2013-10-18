theory Trace
  imports Stutter_Language Algebra
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

  lift_definition one_trace :: "'a trace" is "{LNil}\<^sup>\<dagger>" done

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
      by transfer (simp only: Stutter_idem Stutter_l_prod l_prod_one)
    show "x \<cdot> 1 = x"
      by transfer (simp only: Stutter_idem Stutter_l_prod l_prod_one)
    show "0 + x = x"
      by transfer simp
    show "0 \<cdot> x = 0"
      by transfer simp
    show "(x \<le> y) = (x + y = y)"
      by transfer (metis Stutter_union par.add_commute sup.order_iff)
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
  by transfer (metis Aczel_coextensive Stutter_idem Stutter_iso)

lemma proj_iso [intro]: "x \<le> y \<Longrightarrow> \<pi> x \<le> \<pi> y"
  by transfer (metis Aczel_iso Stutter_iso)

lemma proj_idem [simp]: "\<pi> (\<pi> x) = \<pi> x"
  by transfer (metis Aczel_idem Stutter_proj)

lemma proj_plus [simp]: "\<pi> (x + y) = \<pi> x + \<pi> y"
  by transfer (metis Aczel_union Stutter_union)

lemma proj_mult [simp]: "\<pi> (\<pi> x \<cdot> \<pi> y) = \<pi> (x \<cdot> y)"
  by transfer (metis Aczel_l_prod Stutter_l_prod Stutter_proj)

lemma proj_mult2 [simp]: "\<pi> (\<pi> x \<cdot> y) = \<pi> (x \<cdot> y)"
  by transfer (metis Aczel_idem Aczel_l_prod Stutter_l_prod Stutter_proj)

lemma proj_mult3 [simp]: "\<pi> (x \<cdot> \<pi> y) = \<pi> (x \<cdot> y)"
  by (metis proj_mult proj_mult2)

(* Tests *)

no_notation test ("\<langle>_\<rangle>" [0] 1000)

lift_definition test_trace :: "'a set \<Rightarrow> 'a trace" ("\<langle>_\<rangle>" [0] 1000) is "\<lambda>S. test S" by simp

lemma "\<langle>X\<rangle> \<le> 1"
  by transfer (simp, intro Stutter_iso test_iso subset_UNIV)

lemma "\<pi> (\<langle>X\<rangle> \<cdot> \<langle>Y\<rangle>) = \<pi> (\<langle>X \<inter> Y\<rangle>)"
  by transfer (metis Aczel_mult_def Stutter_l_prod Stutter_proj test_l_prod)

lemma "\<langle>X\<rangle> + \<langle>Y\<rangle> = \<langle>X \<union> Y\<rangle>"
  by transfer (metis test_union)

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
      by transfer (metis Stutter_union par.distrib_left)
    show "1 \<parallel> x = x"
      by transfer (metis Stutter_shuffle_left par.mult.right_neutral shuffle_comm)
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

lemma join_is_plus [simp]:
  fixes x y :: "'a trace"
  shows "x \<squnion> y = x + y"
  by transfer simp

instance trace :: (type) distrib_lattice
  by (default, transfer, simp, metis Stutter_idem Stutter_meet Stutter_union Un_Int_distrib)

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
  by transfer (simp add: Aczel_def)

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

abbreviation proj_eq :: "'a trace \<Rightarrow> 'a trace \<Rightarrow> bool" (infixl "=\<^sub>\<pi>" 55) where
  "x =\<^sub>\<pi> y \<equiv> (\<pi> x = \<pi> y)"

definition proj_leq :: "'a trace \<Rightarrow> 'a trace \<Rightarrow> bool" (infixl "\<le>\<^sub>\<pi>" 55) where
  "x \<le>\<^sub>\<pi> y \<equiv> (\<pi> x \<le> \<pi> y)"

lemma proj_leq_trans [trans]: "x \<le>\<^sub>\<pi> y \<Longrightarrow> y \<le>\<^sub>\<pi> z \<Longrightarrow> x \<le>\<^sub>\<pi> z"
  by (auto simp add: proj_leq_def)

lemma proj_leq_trans2 [trans]: "x \<le> y \<Longrightarrow> y \<le>\<^sub>\<pi> z \<Longrightarrow> x \<le>\<^sub>\<pi> z"
  by (auto simp add: proj_leq_def) (metis dual_order.trans proj_iso)

lemma proj_leq_trans3 [trans]: "x \<le>\<^sub>\<pi> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le>\<^sub>\<pi> z"
  by (metis proj_iso proj_leq_def proj_leq_trans)

find_theorems Aczel "op \<inter>"
find_theorems Stutter "op \<inter>"

lemma Stutter_Con: "(X \<inter> Con)\<^sup>\<dagger> = (X \<inter> Con\<^sup>\<dagger>)\<^sup>\<dagger>"
  sorry

lemma proj_meet [simp]: "\<pi> x \<sqinter> \<pi> y = \<pi> (x \<sqinter> y)"
  apply transfer
  apply (simp add: Aczel_def)
  by (metis Aczel_def Int_assoc Stutter_Con Stutter_meet inf_commute inf_left_idem)

lemma proj_leq_meet [simp]: "\<pi> x \<sqinter> \<pi> y \<le>\<^sub>\<pi> x \<sqinter> y"
  by (metis inf_mono proj_coextensive proj_iso proj_leq_def)

lemma [iff]: "x \<le>\<^sub>\<pi> y \<sqinter> z \<longleftrightarrow> x \<le>\<^sub>\<pi> y \<and> x \<le>\<^sub>\<pi> z"
  apply (simp add: proj_leq_def)
  sledgehammer
  apply transfer

end