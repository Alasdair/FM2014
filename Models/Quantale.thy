theory Quantale
  imports Omega_Algebra Fixpoint
begin

notation inf (infixl "\<sqinter>" 70)
and sup (infixl "\<squnion>" 65)
and Inf ("\<Sqinter>_" [900] 900)
and Sup ("\<Squnion>_" [900] 900)

class par_dioid = dioid_one_zerol +
  fixes par :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<parallel>" 69)
  assumes par_assoc: "(x\<parallel>y)\<parallel>z = x\<parallel>(y\<parallel>z)"
  and par_comm: "x\<parallel>y = y\<parallel>x"
  and par_distl: "x\<parallel>(y+z) = x\<parallel>y+x\<parallel>z"
  and par_unitl [simp]: "1\<parallel>x = x"
  and par_annil [simp]: "0\<parallel>x = 0"

begin

  lemma par_distr: "(x + y)\<parallel>z = x\<parallel>z+y\<parallel>z"
    by (metis par_comm par_distl)

  lemma par_isol: "x \<le> y \<Longrightarrow> x\<parallel>z \<le> y\<parallel>z"
    by (metis less_eq_def par_distr)

  lemma par_isor: "x \<le> y \<Longrightarrow> z\<parallel>x \<le> z\<parallel>y"
    by (metis less_eq_def par_distl)

  lemma par_unitr [simp]: "x\<parallel>1 = x"
    by (metis par_comm par_unitl)

  lemma par_annir [simp]: "x\<parallel>0 = 0"
    by (metis par_annil par_comm)

  lemma par_subdistl: "x\<parallel>z \<le> (x + y)\<parallel>z"
    by (metis order_prop par_distr)

  lemma par_subdistr: "z\<parallel>x \<le> z\<parallel>(x + y)"
    by (metis par_comm par_subdistl)

  lemma par_double_iso: "w \<le> x \<Longrightarrow> y \<le> z \<Longrightarrow> w\<parallel>y \<le> x\<parallel>z"
    by (metis order_trans par_isol par_isor)
end

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

definition (in order) interior :: "('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "interior f \<longleftrightarrow> (\<forall>x. f x \<le> x) \<and> isotone f \<and> idempotent f"

class atomic_quantale = weak_left_quantale + par_dioid +
  fixes atomic :: "'a \<Rightarrow> 'a" ("\<langle>_\<rangle>")
  assumes atomic_interior: "interior atomic"
  and atomic_star: "\<langle>x\<rangle> \<parallel> \<langle>y\<rangle>\<^sup>\<star> = \<langle>y\<rangle>\<^sup>\<star> \<cdot> \<langle>x\<rangle> \<cdot> \<langle>y\<rangle>\<^sup>\<star>"
  and atomic_omega: "\<langle>x\<rangle> \<parallel> \<langle>y\<rangle>\<^sup>\<omega> = \<langle>y\<rangle>\<^sup>\<star> \<cdot> \<langle>x\<rangle> \<cdot> \<langle>y\<rangle>\<^sup>\<omega>"
  and atomic_star2: "\<langle>x\<rangle>\<^sup>\<star> \<parallel> \<langle>y\<rangle>\<^sup>\<star> = \<langle>x + y\<rangle>\<^sup>\<star>"
  and atomic_star3 [simp]: "\<langle>x\<rangle>\<^sup>\<star> \<sqinter> \<langle>y\<rangle>\<^sup>\<star> = \<langle>x \<sqinter> y\<rangle>\<^sup>\<star>"
  and atomic_omega3 [simp]: "\<langle>x\<rangle>\<^sup>\<omega> \<sqinter> \<langle>y\<rangle>\<^sup>\<omega> = \<langle>x \<sqinter> y\<rangle>\<^sup>\<omega>"
  and atomic_omega2: "\<langle>x\<rangle>\<^sup>\<omega> \<parallel> \<langle>y\<rangle>\<^sup>\<omega> = \<langle>x + y\<rangle>\<^sup>\<omega>"
  and atomic_star_omega: "\<langle>x\<rangle>\<^sup>\<star> \<parallel> \<langle>y\<rangle>\<^sup>\<omega> = \<langle>x + y\<rangle>\<^sup>\<star> \<cdot> \<langle>y\<rangle>\<^sup>\<omega>"
  and rely_dist: "\<langle>x\<rangle>\<^sup>\<infinity> \<parallel> y \<cdot> z \<le> (\<langle>x\<rangle>\<^sup>\<infinity> \<parallel> y) \<cdot> (\<langle>x\<rangle>\<^sup>\<infinity> \<parallel> z)"

begin

  find_theorems "omega" "op \<cdot>"

  lemma atomic_loop: "\<langle>x\<rangle> \<parallel> \<langle>y\<rangle>\<^sup>\<infinity> = \<langle>y\<rangle>\<^sup>\<star> \<cdot> \<langle>x\<rangle> \<cdot> \<langle>y\<rangle>\<^sup>\<infinity>"
    by (simp add: loop_def par_distl atomic_star atomic_omega distrib_left)

  lemma atomic_star_omega2: "\<langle>x\<rangle>\<^sup>\<omega> \<parallel> \<langle>y\<rangle>\<^sup>\<star> = \<langle>x + y\<rangle>\<^sup>\<star> \<cdot> \<langle>x\<rangle>\<^sup>\<omega>"
    by (metis add_commute atomic_star_omega par_comm)

  lemma atomic_loop2: "\<langle>x\<rangle>\<^sup>\<infinity> \<parallel> \<langle>y\<rangle>\<^sup>\<infinity> = \<langle>x + y\<rangle>\<^sup>\<infinity>"
  proof (rule antisym)
    have unfold: "\<langle>x\<rangle>\<^sup>\<infinity> \<parallel> \<langle>y\<rangle>\<^sup>\<infinity> = \<langle>x + y\<rangle>\<^sup>\<star> + \<langle>x + y\<rangle>\<^sup>\<star> \<cdot> \<langle>y\<rangle>\<^sup>\<omega> + \<langle>x + y\<rangle>\<^sup>\<star> \<cdot> \<langle>x\<rangle>\<^sup>\<omega> + \<langle>x + y\<rangle>\<^sup>\<omega>"
      apply (simp add: loop_def par_distl par_distr atomic_star2 atomic_omega2 atomic_star_omega atomic_star_omega2)
      by (metis add_commute add_left_commute)

    have "\<langle>x\<rangle>\<^sup>\<infinity> \<parallel> \<langle>y\<rangle>\<^sup>\<infinity> = \<langle>x + y\<rangle>\<^sup>\<star> + \<langle>x + y\<rangle>\<^sup>\<star> \<cdot> \<langle>y\<rangle>\<^sup>\<omega> + \<langle>x + y\<rangle>\<^sup>\<star> \<cdot> \<langle>x\<rangle>\<^sup>\<omega> + \<langle>x + y\<rangle>\<^sup>\<omega>"
      by (simp add: unfold)
    also have "... \<le> \<langle>x + y\<rangle>\<^sup>\<omega> + \<langle>x + y\<rangle>\<^sup>\<star>\<cdot>1"
      apply (rule omega_coinduct)
      by (metis add_0_left add_0_right atomic_interior atomic_omega2 atomic_star2 calculation eq_iff interior_def loop_def par_annil star_unfoldl_eq zero_omega zero_unique)
    also have "... \<le> \<langle>x + y\<rangle>\<^sup>\<infinity>"
      by (metis add_commute loop_def mult_1_right order_refl)
    finally show "\<langle>x\<rangle>\<^sup>\<infinity> \<parallel> \<langle>y\<rangle>\<^sup>\<infinity> \<le> \<langle>x + y\<rangle>\<^sup>\<infinity>" .

    have "\<langle>x + y\<rangle>\<^sup>\<infinity> \<le> \<langle>x + y\<rangle>\<^sup>\<star> + \<langle>x + y\<rangle>\<^sup>\<star> \<cdot> \<langle>y\<rangle>\<^sup>\<omega> + \<langle>x + y\<rangle>\<^sup>\<star> \<cdot> \<langle>x\<rangle>\<^sup>\<omega> + \<langle>x + y\<rangle>\<^sup>\<omega>"
      by (smt add_assoc add_commute loop_def order_prop)
    also have "... = \<langle>x\<rangle>\<^sup>\<infinity> \<parallel> \<langle>y\<rangle>\<^sup>\<infinity>"
      by (simp add: unfold)
    finally show "\<langle>x + y\<rangle>\<^sup>\<infinity> \<le> \<langle>x\<rangle>\<^sup>\<infinity> \<parallel> \<langle>y\<rangle>\<^sup>\<infinity>" .
  qed

  lemma atomic_iso: "x \<le> y \<Longrightarrow> \<langle>x\<rangle> \<le> \<langle>y\<rangle>"
    by (metis atomic_interior interior_def isotone_def)

  lemma atomic_idem [simp]: "\<langle>\<langle>x\<rangle>\<rangle> = \<langle>x\<rangle>"
    by (metis Fixpoint.idempotent_def atomic_interior comp_apply interior_def)

  definition RG :: "'a set" where
    "RG \<equiv> {r. \<exists>r'. r = \<langle>r'\<rangle>\<^sup>\<infinity>}"

  lemma loop_idem [simp]: "x\<^sup>\<infinity> \<cdot> x\<^sup>\<infinity> = x\<^sup>\<infinity>"
    apply (simp add: loop_def distrib_right distrib_left)
    apply (simp only: add_assoc[symmetric])
    by (metis (full_types) add_commute add_ub1 less_eq_def omega_1 omega_sup_id star_unfoldl_eq)

  lemma rg_mult_idem: "r \<in> RG \<Longrightarrow> r \<cdot> r = r"
    apply (simp add: RG_def)
    apply (erule exE)
    apply (erule ssubst)
    by simp

  lemma rg_par_idem: "r \<in> RG \<Longrightarrow> r \<parallel> r = r"
    apply (simp add: RG_def)
    apply (erule exE)
    apply simp
    by (simp add: atomic_loop2)

  lemma rg_par_closed: "r \<in> RG \<Longrightarrow> s \<in> RG \<Longrightarrow> r \<parallel> s \<in> RG"
    apply (simp add: RG_def)
    apply (erule exE)+
    apply (erule ssubst)+
    apply (simp add: atomic_loop2)
    by auto

  lemma [simp]: "(x + y) \<sqinter> z = x \<sqinter> z + y \<sqinter> z"
    by (simp only: sup_is_plus[symmetric]) (metis inf_sup_distrib2)

  lemma [simp]: "x \<sqinter> (y + z) = x \<sqinter> y + x \<sqinter> z"
    by (simp only: sup_is_plus[symmetric]) (metis inf_sup_distrib1)

  lemma atomic_loop3': "\<langle>x \<sqinter> y\<rangle>\<^sup>\<infinity> \<le> \<langle>x\<rangle>\<^sup>\<infinity> \<sqinter> \<langle>y\<rangle>\<^sup>\<infinity>"
    apply (simp add: loop_def)
    by (metis add_iso_var add_left_commute add_ub1 order_refl)

  lemma loop_coinduct: "y \<le> 1 + x \<cdot> y \<Longrightarrow> y \<le> x\<^sup>\<infinity>"
    sorry

  lemma loop_unfoldl_eq: "1 + x \<cdot> x\<^sup>\<infinity> = x\<^sup>\<infinity>"
    sorry

  lemma loop_iso: "x \<le> y \<Longrightarrow> x\<^sup>\<infinity> \<le> y\<^sup>\<infinity>"
    sorry

  lemma atomic_loop3: "\<langle>x\<rangle>\<^sup>\<infinity> \<sqinter> \<langle>y\<rangle>\<^sup>\<infinity> = \<langle>x \<sqinter> y\<rangle>\<^sup>\<infinity>"
    sorry

  lemma rg_meet_closed: "r \<in> RG \<Longrightarrow> s \<in> RG \<Longrightarrow> r \<sqinter> s \<in> RG"
    apply (simp add: RG_def)
    apply (erule exE)+
    apply (erule ssubst)+
    apply (simp add: atomic_loop3)
    by auto
end

class rg_quantale = weak_left_quantale + par_dioid +
  fixes RG :: "'a set"
  assumes rg_meet_closed: "r \<in> RG \<Longrightarrow> s \<in> RG \<Longrightarrow> r \<sqinter> s \<in> RG"
  and rg_par_closed: "r \<in> RG \<Longrightarrow> s \<in> RG \<Longrightarrow> r \<parallel> s \<in> RG"
  and rg_mult_idem: "r \<in> RG \<Longrightarrow> r \<cdot> r = r"
  and rg_par_idem: "r \<in> RG \<Longrightarrow> r \<parallel> r = r"
  and rg_leq: "r \<in> RG \<Longrightarrow> s \<in> RG \<Longrightarrow> r \<le> r \<parallel> s"
  and rg_dist: "r \<in> RG \<Longrightarrow> r \<parallel> (x \<cdot> y) \<le> (r \<parallel> x) \<cdot> (r \<parallel> y)"
  and rg_one: "r \<in> RG \<Longrightarrow> 1 \<le> r"

lemma (in boolean_algebra) uminus_top: "- x = top - x"
  by (metis diff_eq inf_top_left)

locale weak_left_quantale_hom =
  fixes hom :: "'a::rg_quantale \<Rightarrow> 'b::weak_left_quantale" ("\<lbrakk>_\<rbrakk>")
  assumes hom_continuous: "\<lbrakk>\<Squnion>X\<rbrakk> = \<Squnion>(hom`X)"
  and hom_mult: "\<lbrakk>x \<cdot> y\<rbrakk> = \<lbrakk>x\<rbrakk> \<cdot> \<lbrakk>y\<rbrakk>"
  and hom_one: "\<lbrakk>1\<rbrakk> = 1"

begin

  lemma hom_plus: "\<lbrakk>x + y\<rbrakk> = \<lbrakk>x\<rbrakk> + \<lbrakk>y\<rbrakk>"
  proof -
    have "\<lbrakk>x + y\<rbrakk> = \<lbrakk>\<Squnion>{x,y}\<rbrakk>"
      by (simp del: sup_is_plus bot_is_zero add: sup_is_plus[symmetric] bot_is_zero[symmetric])
    also have "... = \<Squnion>{\<lbrakk>x\<rbrakk>, \<lbrakk>y\<rbrakk>}"
      by (simp only: hom_continuous) (rule arg_cong, auto simp add: image_def)
    also have "... = \<lbrakk>x\<rbrakk> + \<lbrakk>y\<rbrakk>"
      by simp
    finally show ?thesis .
  qed

  lemma hom_iso: "x \<le> y \<Longrightarrow> \<lbrakk>x\<rbrakk> \<le> \<lbrakk>y\<rbrakk>"
    by (metis hom_plus less_eq_def)

  lemma hom_star: "\<lbrakk>x\<^sup>\<star>\<rbrakk> = \<lbrakk>x\<rbrakk>\<^sup>\<star>"
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

  lemma hom_omega: "\<lbrakk>x\<^sup>\<omega>\<rbrakk> \<le> \<lbrakk>x\<rbrakk>\<^sup>\<omega>"
    by (rule omega_coinduct_var2, subst omega_unfold_eq[symmetric], simp only: hom_mult)

  lemma hom_meet: "\<lbrakk>x \<sqinter> y\<rbrakk> \<le> \<lbrakk>x\<rbrakk> \<sqinter> \<lbrakk>y\<rbrakk>"
    by (metis hom_iso inf_sup_ord(1) inf_sup_ord(2) le_inf_iff)

  definition quintuple :: "'a \<Rightarrow> 'a \<Rightarrow> 'b  \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool" ("_, _ \<turnstile> \<lbrace>_\<rbrace> _ \<lbrace>_\<rbrace>") where
    "r, g \<turnstile> \<lbrace>p\<rbrace> c \<lbrace>q\<rbrace> \<longleftrightarrow> p \<cdot> \<lbrakk>(r \<parallel> c)\<rbrakk> \<le> q \<and> c \<le> g \<and> r \<in> RG \<and> g \<in> RG" 

  theorem weakening:
    assumes "r, g \<turnstile> \<lbrace>p\<rbrace> c1 \<lbrace>q\<rbrace>"
    and "r' \<le> r" and "r' \<in> RG" and "g \<le> g'" and "g' \<in> RG"
    and "p' \<le> p" and "q \<le> q'"
    shows "r', g' \<turnstile> \<lbrace>p'\<rbrace> c1 \<lbrace>q'\<rbrace>"
  proof (simp add: quintuple_def, intro conjI)
    show "r' \<in> RG" and "g' \<in> RG"
      by (metis assms(3)) (metis assms(5))

    have "p' \<cdot> \<lbrakk>r' \<parallel> c1\<rbrakk> \<le> p \<cdot> \<lbrakk>r \<parallel> c1\<rbrakk>"
      by (intro mult_isol_var[rule_format] conjI assms hom_iso par_double_iso order_refl)
    also have "... \<le> q"
      by (metis assms(1) quintuple_def)
    also have "... \<le> q'"
      by (metis assms(7))
    finally show "p' \<cdot> \<lbrakk>r' \<parallel> c1\<rbrakk> \<le> q'" .

    have "c1 \<le> g"
      by (metis assms(1) quintuple_def)
    also have "... \<le> g'"
      by (metis assms(4) hom_iso)
    finally show "c1 \<le> g'" .
  qed

  theorem sequential:
    assumes "r, g \<turnstile> \<lbrace>p\<rbrace> c1 \<lbrace>q\<rbrace>" and "r, g \<turnstile> \<lbrace>q\<rbrace> c2 \<lbrace>s\<rbrace>"
    shows "r, g \<turnstile> \<lbrace>p\<rbrace> c1 \<cdot> c2 \<lbrace>s\<rbrace>"
  proof (simp add: quintuple_def, intro conjI)
    show "r \<in> RG" and "g \<in> RG"
      by (metis assms(1) quintuple_def)+

    hence "p \<cdot> \<lbrakk>r \<parallel> c1 \<cdot> c2\<rbrakk> \<le> p \<cdot> \<lbrakk>(r \<parallel> c1) \<cdot> (r \<parallel> c2)\<rbrakk>"
      by (intro mult_isol_var[rule_format] conjI order_refl hom_iso rg_dist)
    also have "... \<le> q \<cdot> \<lbrakk>r \<parallel> c2\<rbrakk>"
      apply (subst hom_mult)
      apply (simp only: mult_assoc[symmetric])
      apply (intro mult_isol_var[rule_format] conjI)
      apply (metis assms(1) quintuple_def)
      by (rule order_refl)
    also have "... \<le> s"
      by (metis assms(2) quintuple_def)
    finally show "p \<cdot> \<lbrakk>r \<parallel> c1 \<cdot> c2\<rbrakk> \<le> s" .

    have "c1 \<cdot> c2 \<le> g \<cdot> g"
      apply (intro mult_isol_var[rule_format] conjI)
      apply (metis assms(1) quintuple_def)
      by (metis assms(2) quintuple_def)
    also have "... = g"
      by (metis `g \<in> RG` rg_quantale_class.rg_mult_idem)
    finally show "c1 \<cdot> c2 \<le> g" .
  qed

  corollary weakened_sequential:
    assumes "r1, g1 \<turnstile> \<lbrace>p\<rbrace> c1 \<lbrace>q\<rbrace>" and "r2, g2 \<turnstile> \<lbrace>q\<rbrace> c2 \<lbrace>s\<rbrace>"
    shows "(r1 \<sqinter> r2), (g1 \<parallel> g2) \<turnstile> \<lbrace>p\<rbrace> c1 \<cdot> c2 \<lbrace>s\<rbrace>"
    apply (rule sequential[where q = q])
    apply (rule weakening[OF assms(1)])
    apply (metis inf_sup_ord(1))
    apply (metis assms(1) assms(2) quintuple_def rg_meet_closed)
    apply (metis assms(1) assms(2) quintuple_def rg_leq)
    apply (metis assms(1) assms(2) quintuple_def rg_quantale_class.rg_par_closed)
    apply (rule order_refl)+
    apply (rule weakening[OF assms(2)])
    apply (metis inf_sup_ord(2))
    apply (metis assms(1) assms(2) quintuple_def rg_meet_closed)
    apply (metis assms(1) assms(2) par_comm quintuple_def rg_leq)
    apply (metis assms(1) assms(2) quintuple_def rg_quantale_class.rg_par_closed)
    by (rule order_refl)+

  theorem parallel:
    assumes "r1, g1 \<turnstile> \<lbrace>p1\<rbrace> c1 \<lbrace>q1\<rbrace>" and "g2 \<le> r1"
    and "r2, g2 \<turnstile> \<lbrace>p2\<rbrace> c2 \<lbrace>q2\<rbrace>" and "g1 \<le> r2"
    shows "(r1 \<sqinter> r2), (g1 \<parallel> g2) \<turnstile> \<lbrace>p1 \<sqinter> p2\<rbrace> c1 \<parallel> c2 \<lbrace>q1 \<sqinter> q2\<rbrace>" 
  proof (simp add: quintuple_def, intro conjI)
    have "r1 \<in> RG" and "r2 \<in> RG" and "g1 \<in> RG" and "g2 \<in> RG"
      by (metis assms(1) assms(3) quintuple_def)+

    have "p1 \<sqinter> p2 \<cdot> \<lbrakk>r1 \<sqinter> r2 \<parallel> (c1 \<parallel> c2)\<rbrakk> \<le> p1 \<cdot> \<lbrakk>r1 \<sqinter> r2 \<parallel> (c1 \<parallel> c2)\<rbrakk>"
      by (metis inf_le1 mult_isor)
    also have "... \<le> p1 \<cdot> \<lbrakk>r1 \<sqinter> r2 \<parallel> (c1 \<parallel> g2)\<rbrakk>"
      by (intro mult_isol_var[rule_format] conjI order_refl hom_iso par_double_iso) (metis assms(3) quintuple_def)
    also have "... \<le> p1 \<cdot> \<lbrakk>r1 \<parallel> (c1 \<parallel> r1)\<rbrakk>"
      by (intro mult_isol_var[rule_format] conjI order_refl) (metis assms(2) hom_iso inf_le1 par_double_iso par_isor)
    also have "... \<le> p1 \<cdot> \<lbrakk>r1 \<parallel> c1\<rbrakk>"
      by (intro mult_isol_var[rule_format] conjI order_refl) (metis `r1 \<in> RG` eq_iff par_assoc par_comm rg_par_idem)
    also have "... \<le> q1"
      by (metis assms(1) quintuple_def)
    finally show "p1 \<sqinter> p2 \<cdot> \<lbrakk>r1 \<sqinter> r2 \<parallel> (c1 \<parallel> c2)\<rbrakk> \<le> q1" .

    have "p1 \<sqinter> p2 \<cdot> \<lbrakk>r1 \<sqinter> r2 \<parallel> (c1 \<parallel> c2)\<rbrakk> \<le> p2 \<cdot> \<lbrakk>r1 \<sqinter> r2 \<parallel> (c1 \<parallel> c2)\<rbrakk>"
      by (metis inf_le2 mult_isor)
    also have "... \<le> p2 \<cdot> \<lbrakk>r1 \<sqinter> r2 \<parallel> (g1 \<parallel> c2)\<rbrakk>"
      by (intro mult_isol_var[rule_format] conjI order_refl hom_iso par_double_iso) (metis assms(1) quintuple_def)
    also have "... \<le> p2 \<cdot> \<lbrakk>r2 \<parallel> (r2 \<parallel> c2)\<rbrakk>"
      by (intro mult_isol_var[rule_format] conjI order_refl) (metis add_idem assms(4) hom_iso inf_sup_ord(2) less_eq_def par_double_iso)
    also have "... \<le> p2 \<cdot> \<lbrakk>r2 \<parallel> c2\<rbrakk>"
      by (intro mult_isol_var[rule_format] conjI order_refl) (metis `r2 \<in> RG` eq_iff par_assoc rg_par_idem)
    also have "... \<le> q2"
      by (metis assms(3) quintuple_def)
    finally show "p1 \<sqinter> p2 \<cdot> \<lbrakk>r1 \<sqinter> r2 \<parallel> (c1 \<parallel> c2)\<rbrakk> \<le> q2" .

    show "c1 \<parallel> c2 \<le> g1 \<parallel> g2"
      by (rule par_double_iso) (metis assms(1) quintuple_def, metis assms(3) quintuple_def)

    show "r1 \<sqinter> r2 \<in> RG"
      by (metis `r1 \<in> RG` `r2 \<in> RG` rg_meet_closed)
    show "g1 \<parallel> g2 \<in> RG"
      by (metis `g1 \<in> RG` `g2 \<in> RG` rg_par_closed)
  qed

  lemma skip: "r \<in> RG \<Longrightarrow> g \<in> RG \<Longrightarrow> 1, top \<turnstile> \<lbrace>p\<rbrace> r \<lbrace>q\<rbrace> \<Longrightarrow> r, g \<turnstile> \<lbrace>p\<rbrace> 1 \<lbrace>q\<rbrace>"
    by (auto simp add: quintuple_def) (metis rg_one)

end

end
