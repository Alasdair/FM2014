theory Quantale
  imports Omega_Algebra Fixpoint
begin

notation inf (infixl "\<sqinter>" 70)
and sup (infixl "\<squnion>" 65)
and Inf ("\<Sqinter>_" [900] 900)
and Sup ("\<Squnion>_" [900] 900)

class weak_left_quantale = complete_boolean_algebra + dioid_one_zerol +
  assumes sup_is_plus [simp]: "x \<squnion> y = x + y"
  and bot_is_zero [simp]: "bot = 0"
  and inf_distr: "\<Squnion>X \<cdot> y = \<Squnion>{x \<cdot> y |x. x \<in> X}"

context weak_left_quantale
begin

no_notation
  Signatures.star_op_class.star ("_\<^sup>\<star>" [101] 100) and
  Signatures.omega_op_class.omega ("_\<^sup>\<omega>" [101] 100)

definition omega :: "'a \<Rightarrow> 'a" ("_\<^sup>\<omega>" [101] 100) where
  "x\<^sup>\<omega> = (\<nu> y. x\<cdot>y)"

definition star :: "'a \<Rightarrow> 'a" ("_\<^sup>\<star>" [101] 100) where
  "x\<^sup>\<star> = (\<mu> y. 1 + x\<cdot>y)"

definition loop :: "'a \<Rightarrow> 'a" ("_\<^sup>\<infinity>" [101] 100) where
  "X\<^sup>\<infinity> = X\<^sup>\<star> + X\<^sup>\<omega>"

end

sublocale weak_left_quantale \<subseteq> left_kleene_algebra_zerol "op +" "op \<cdot>" 1 0 "op \<le>" "op <" star
proof
  fix x y z :: "'a"
  show "1 + x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
    unfolding star_def
    by (subst fp_compute[symmetric], auto) (metis add_iso_var eq_refl mult_isol)

  show "z + x \<cdot> y \<le> y \<longrightarrow> x\<^sup>\<star> \<cdot> z \<le> y"
  proof
    assume "z + x \<cdot> y \<le> y"
    hence "(\<mu> y. z + x \<cdot> y) \<le> y"
      by (rule fp_induct[rotated 1]) (metis add_iso_var eq_refl mult_isol)
    moreover have "x\<^sup>\<star> \<cdot> z = (\<mu> y. z + x \<cdot> y)"
      unfolding star_def
      apply (rule endo_fixpoint_fusion)
      apply (auto intro!: arg_cong[where f = Sup] simp add: endo_lower_is_jp endo_join_preserving_def image_def inf_distr isotone_def)
      apply (metis add_iso_var eq_refl mult_isol)
      apply (metis add_iso_var eq_refl mult_isol)
      by (auto simp: o_def distrib_right mult_assoc)
    ultimately show "x\<^sup>\<star> \<cdot> z \<le> y"
      by simp
  qed
qed

lemma (in boolean_algebra) inf_galois: "x \<sqinter> y \<le> z \<longleftrightarrow> x \<le> -y \<squnion> z"
proof
  assume left: "x \<sqinter> y \<le> z"
  have "x \<le> (-y \<squnion> y) \<sqinter> (-y \<squnion> x)"
    by (metis compl_sup_top inf_top_left sup_ge2)
  also have "... = -y \<squnion> (y \<sqinter> x)"
    by (metis sup.commute sup_inf_distrib2)
  also have "... \<le> -y \<squnion> z"
    by (metis inf_commute le_iff_sup left sup_idem sup_mono)
  finally show "x \<le> -y \<squnion> z" .
next
  assume right: "x \<le> -y \<squnion> z"
  have "x \<sqinter> y \<le> (-y \<squnion> z) \<sqinter> y"
    by (metis inf_mono order_refl right)
  also have "... \<le> z"
    by (simp add: inf_sup_distrib2 inf_compl_bot)
  finally show "x \<sqinter> y \<le> z" .
qed

lemma (in boolean_algebra) diff_galois: "x - y \<le> z \<longleftrightarrow> x \<le> y \<squnion> z" 
  by (subst double_compl[symmetric, of y], simp only: inf_galois[symmetric] diff_eq)

lemma (in dioid) [intro!]: "isotone (op \<cdot> x)"
  by (metis isotone_def mult_isol)

lemma (in dioid) [intro!]: "isotone f \<Longrightarrow> isotone (\<lambda>y. z + f y)"
  by (auto simp: isotone_def) (metis add_iso_var eq_refl)

sublocale weak_left_quantale \<subseteq> left_omega_algebra_zerol "op +" "op \<cdot>" "1" "0" "op \<le>" "op <" star omega
proof
  fix x y z :: "'a"
  show omega_unfold: "x\<^sup>\<omega> \<le> x \<cdot> x\<^sup>\<omega>"
    unfolding omega_def by (subst gfp_compute[symmetric], auto) (metis mult_isol)

  have omega_coinduct: "\<And>x y z. y \<le> x\<cdot>y \<Longrightarrow> y \<le> x\<^sup>\<omega>"
    unfolding omega_def by (rule gfp_induct, auto) (metis mult_isol)

  have omega_star_fuse: "x\<^sup>\<omega> + x\<^sup>\<star>\<cdot>z = (\<nu> y. z + x \<cdot> y)" unfolding omega_def
  proof (rule endo_greatest_fixpoint_fusion, auto simp add: o_def)
    show "endo_upper_adjoint (\<lambda>y. y + x\<^sup>\<star> \<cdot> z)" using diff_galois[simplified]
      by (simp add: endo_upper_adjoint_def endo_galois_connection_def) (rule_tac x = "\<lambda>y. y - x\<^sup>\<star> \<cdot> z" in exI, metis add_commute)
  next
    show "(\<lambda>y. x \<cdot> y + x\<^sup>\<star> \<cdot> z) = (\<lambda>y. z + x \<cdot> (y + x\<^sup>\<star> \<cdot> z))"
      apply (rule ext)
      apply (simp add: distrib_left)
      apply (subst star_unfoldl_eq[symmetric])
      apply (subst distrib_right)
      apply simp
      apply (simp only: mult_assoc add_assoc[symmetric])
      apply (subst add_commute)
      by simp
  qed

  show "x\<^sup>\<star> \<cdot> 0 \<le> x\<^sup>\<omega>"
    by (rule omega_coinduct, subst star_unfoldl_eq[symmetric])
       (metis add_0_left distrib_left mult_assoc order_prop star_slide_var star_unfoldl_eq)

  assume "y \<le> z + x\<cdot>y" thus "y \<le> x\<^sup>\<omega> + x\<^sup>\<star>\<cdot>z"
    by - (simp only: omega_star_fuse, rule gfp_induct, auto, metis add_iso_var eq_refl mult_isol)
qed

locale weak_left_quantale_hom =
  fixes hom :: "'a::weak_left_quantale \<Rightarrow> 'b::weak_left_quantale"
  assumes hom_continuous: "hom (\<Squnion>X) = \<Squnion>(hom`X)"
  and hom_mult: "hom (x \<cdot> y) = hom x \<cdot> hom y"
  and hom_one: "hom 1 = 1"

begin

  lemma hom_plus: "hom (x + y) = hom x + hom y"
  proof -
    have "hom (x + y) = hom (\<Squnion>{x,y})"
      by (simp del: sup_is_plus bot_is_zero add: sup_is_plus[symmetric] bot_is_zero[symmetric])
    also have "... = \<Squnion>{hom x, hom y}"
      by (simp only: hom_continuous) (rule arg_cong, auto simp add: image_def)
    also have "... = hom x + hom y"
      by simp
    finally show ?thesis .
  qed

  lemma hom_iso: "x \<le> y \<Longrightarrow> hom x \<le> hom y"
    by (metis hom_plus less_eq_def)

  lemma hom_star: "hom (x\<^sup>\<star>) = (hom x)\<^sup>\<star>"
  proof -
    have "hom (\<mu> y. 1 + x \<cdot> y) = (\<mu> y. 1 + hom x \<cdot> y)"
    proof (rule fixpoint_fusion[where f = hom])
      have "join_preserving hom"
        by (simp add: join_preserving_def hom_continuous)
      thus "lower_adjoint hom"
        by (metis lower_is_jp)
    next
      show "mono (\<lambda>y. 1 + x \<cdot> y)"
        by (simp add: mono_def) (metis add_iso_var mult_isol order_refl)
    next
      show "mono (\<lambda>y. 1 + hom x \<cdot> y)"
        by (simp add: mono_def) (metis add_iso_var mult_isol order_refl)
    next
      show "hom \<circ> (\<lambda>y. 1 + x \<cdot> y) = (\<lambda>y. 1 + hom x \<cdot> y) \<circ> hom"
        by (auto intro!: ext simp add: o_def hom_plus hom_mult hom_one)
    qed
    thus "hom (x\<^sup>\<star>) = (hom x)\<^sup>\<star>"
      by (simp add: star_def)
  qed

  lemma hom_omega: "hom (x\<^sup>\<omega>) \<le> (hom x)\<^sup>\<omega>"
    by (rule omega_coinduct_var2, subst omega_unfold_eq[symmetric], simp only: hom_mult)
end

end
