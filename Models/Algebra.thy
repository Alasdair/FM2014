theory Algebra
  imports "$AFP/Kleene_Algebra/Kleene_Algebra" Omega_Algebra
begin

notation inf (infixl "\<sqinter>" 70)

class par_dioid = join_semilattice_zero + one +
  fixes par :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<parallel>" 69)
  assumes par_assoc [simp]: "x \<parallel> (y \<parallel> z) = (x \<parallel> y) \<parallel> z"
  and par_comm: "x \<parallel> y = y \<parallel> x"
  and par_distl [simp]: "x \<parallel> (y + z) = x \<parallel> y + x \<parallel> z"
  and par_unitl [simp]: "1 \<parallel> x = x"
  and par_annil [simp]: "0 \<parallel> x = 0"

begin

  lemma par_distr [simp]: "(x+y) \<parallel> z = x \<parallel> z + y \<parallel> z" 
    by (metis par_comm par_distl)

  lemma par_isol [intro]: "x \<le> y \<Longrightarrow> x \<parallel> z \<le> y \<parallel> z"
    by (metis order_prop par_distr)
 
  lemma par_isor [intro]: "x \<le> y \<Longrightarrow> z \<parallel> x \<le> z \<parallel> y"
    by (metis par_comm par_isol)

  lemma par_unitr [simp]: "x \<parallel> 1 = x"
    by (metis par_comm par_unitl)

  lemma par_annir [simp]: "x \<parallel> 0 = 0"
    by (metis par_annil par_comm)

  lemma par_subdistl: "x \<parallel> z \<le> (x + y) \<parallel> z"
    by (metis order_prop par_distr)

  lemma par_subdistr: "z \<parallel> x \<le> z \<parallel> (x + y)"
    by (metis par_comm par_subdistl)

  lemma par_double_iso [intro]: "w \<le> x \<Longrightarrow> y \<le> z \<Longrightarrow> w \<parallel> y \<le> x \<parallel> z"
    by (metis order_trans par_isol par_isor)

end

class weak_trioid = par_dioid + dioid_one_zerol

class trioid = par_dioid + dioid_one_zero

class weak_star_trioid = weak_trioid + left_kleene_algebra_zerol

begin

end

class weak_omega_trioid = weak_trioid + left_omega_algebra_zerol

class rely_guarantee_trioid = weak_star_trioid + semilattice_inf +
  fixes RG :: "'a set"
  and C :: "'a"
  assumes rg1: "r \<in> RG \<Longrightarrow> r \<parallel> r \<le> r"
  and rg2: "r \<in> RG \<Longrightarrow> s \<in> RG \<Longrightarrow> r \<le> r \<parallel> s"
  and rg3: "r \<in> RG \<Longrightarrow> r\<parallel>(x\<cdot>y) = (r\<parallel>x)\<cdot>(r\<parallel>y)"
  and rg4: "r \<in> RG \<Longrightarrow> r\<parallel>(x\<^sup>\<star>\<cdot>x) \<le> (r\<parallel>x)\<^sup>\<star>\<cdot>(r\<parallel>x)"
  and rg5: "r \<in> RG \<Longrightarrow> r\<parallel>(x\<^sup>\<star>\<cdot>x) \<le> (r\<parallel>x)\<cdot>(r\<parallel>x)\<^sup>\<star>"
  and rg_unit: "1 \<in> RG"
  and rg_meet_closed: "\<lbrakk>r \<in> RG; s \<in> RG\<rbrakk> \<Longrightarrow> (r \<sqinter> s) \<in> RG"
  and rg_par_closed: "\<lbrakk>r \<in> RG; s \<in> RG\<rbrakk> \<Longrightarrow> (r \<parallel> s) \<in> RG"

  and Con_mult: "x\<cdot>y \<sqinter> C \<le> (x \<sqinter> C)\<cdot>(y \<sqinter> C) \<sqinter> C"
  and Con_star: "x\<^sup>\<star> \<sqinter> C \<le> (x \<sqinter> C)\<^sup>\<star> \<sqinter> C"

  and plus_meet_distrib: "x + y \<sqinter> z = (x + y) \<sqinter> (x + z)"

begin

  declare mult_onel [simp]
    and mult_oner [simp]
    and par_unitl [simp]
    and par_unitr [simp]

  definition proj :: "'a \<Rightarrow> 'a" ("\<pi>") where
    "\<pi> x = x \<sqinter> C"

  lemma proj_mult [simp]: "\<pi> (\<pi> x \<cdot> \<pi> y) = \<pi> (x\<cdot>y)"
    by (auto intro!: antisym Con_mult simp add: proj_def) (metis inf_commute inf_le2 le_infI2 mult_isol_var)

  lemma proj_mult2 [simp]: "\<pi> (\<pi> x \<cdot> y) = \<pi> (x\<cdot>y)"
    by (metis inf_commute inf_left_idem proj_def proj_mult)

  lemma proj_mult3 [simp]: "\<pi> (x \<cdot> \<pi> y) = \<pi> (x\<cdot>y)"
    by (metis proj_mult proj_mult2)

  lemma proj_coextensive [intro!]: "\<pi> x \<le> x"
    by (metis inf_le1 proj_def)

  lemma proj_iso [intro]: "x \<le> y \<Longrightarrow> \<pi> x \<le> \<pi> y"
    by (metis inf_mono order_refl proj_def)

  lemma proj_idem [simp]: "\<pi> (\<pi> x) = \<pi> x"
    by (metis inf_commute inf_left_idem proj_def)

  sublocale distrib_lattice "op \<sqinter>" "op \<le>" "op <" "op +"
  proof
    fix x y z
    show "x \<le> x + y"
      by (metis add_ub1)
    show "y \<le> x + y"
      by (metis add_ub2)
    show "x + y \<sqinter> z = (x + y) \<sqinter> (x + z)"
      by (metis plus_meet_distrib)
    assume "y \<le> x" and "z \<le> x"
    thus "y + z \<le> x"
      by (metis add_lub)
  qed

  lemma "(x \<sqinter> C) \<le> (y \<sqinter> C) \<longleftrightarrow> ((x + y) \<sqinter> C) = (y \<sqinter> C)"
    apply default
    defer
    apply (metis eq_refl inf_mono sup_ge1)
    by (metis inf_commute inf_sup_distrib1 sup_absorb2)

  lemma proj_plus [simp]: "\<pi> (x + y) = \<pi> x + \<pi> y"
    by (simp add: proj_def) (metis inf_commute inf_sup_distrib1)

  lemma proj_meet [simp]: "\<pi> (x \<sqinter> y) = \<pi> x \<sqinter> \<pi> y"
    by (metis inf_commute inf_left_commute inf_left_idem proj_def)

  definition pmult :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<otimes>" 70) where
    "x \<otimes> y = \<pi> (x \<cdot> y)"

  lemma [simp]: "\<pi> (x \<otimes> y) = x \<otimes> y"
    by (metis inf_commute inf_left_idem pmult_def proj_def)

  lemma pmult_onel [simp]: "1 \<otimes> x = \<pi> x"
    by (metis mult_onel pmult_def)

  lemma pmult_oner [simp]: "x \<otimes> 1 = \<pi> x"
    by (metis mult_oner pmult_def)

  lemma proj_zero [simp]: "\<pi> 0 = 0"
    by (metis add_zerol inf_sup_absorb proj_def)

  lemma pmult_zero: "0 \<otimes> x = 0"
    by (simp add: pmult_def)

  abbreviation proj_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "=\<^sub>\<pi>" 55) where
    "x =\<^sub>\<pi> y \<equiv> (\<pi> x = \<pi> y)"

  definition proj_leq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<le>\<^sub>\<pi>" 55) where
    "x \<le>\<^sub>\<pi> y \<equiv> (\<pi> x \<le> \<pi> y)"

  lemma proj_leq_trans [trans]: "x \<le>\<^sub>\<pi> y \<Longrightarrow> y \<le>\<^sub>\<pi> z \<Longrightarrow> x \<le>\<^sub>\<pi> z"
    by (auto simp add: proj_leq_def)

  lemma proj_leq_trans2 [trans]: "x \<le> y \<Longrightarrow> y \<le>\<^sub>\<pi> z \<Longrightarrow> x \<le>\<^sub>\<pi> z"
    by (auto simp add: proj_leq_def) (metis dual_order.trans proj_iso)

  lemma proj_leq_trans3 [trans]: "x \<le>\<^sub>\<pi> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le>\<^sub>\<pi> z"
    by (metis proj_iso proj_leq_def proj_leq_trans)

  lemma proj_leq_iso: "x \<le> y \<Longrightarrow> x \<le>\<^sub>\<pi> y"
    by (metis proj_iso proj_leq_def)

  sublocale proj!: dioid "op +" "op \<otimes>" "op \<le>" "op <"
  proof
    fix x y z
    show "(x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"
      by (simp add: pmult_def mult_assoc)
    show "(x + y) \<otimes> z = x \<otimes> z + y \<otimes> z"
      by (simp add: pmult_def distrib_right)
    show "x \<otimes> (y + z) = x \<otimes> y + x \<otimes> z"
      by (metis distrib_left inf_commute inf_sup_distrib1 pmult_def proj_def)
    show "x + x = x"
      by (metis sup_idem)
  qed

  definition quintuple :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("_,// _// \<turnstile> \<lbrace>_\<rbrace> _ \<lbrace>_\<rbrace>" [20,20,20,20,20] 1000) where
    "r, g \<turnstile> \<lbrace>p\<rbrace> c \<lbrace>q\<rbrace> \<equiv> p\<cdot>(r\<parallel>c) \<le>\<^sub>\<pi> q \<and> c \<le> g \<and> r \<in> RG \<and> g \<in> RG"

  lemma rg_idem_mult [simp]: "r \<in> RG \<Longrightarrow> r\<cdot>r = r"
    using rg3[where x = 1 and y = 1 and r = r, simplified] ..

  lemma rg_idem_par : "r \<in> RG \<Longrightarrow> r \<parallel> r = r"
    by (metis eq_iff rg1 rg2)

  lemma [simp]: "x \<le> \<pi> (y \<sqinter> z) \<longleftrightarrow> x \<le> \<pi> y \<and> x \<le> \<pi> z"
    by (metis le_infE le_infI proj_def)

  lemma meet_iso [intro]: "x \<le> z \<Longrightarrow> y \<le> w \<Longrightarrow> x \<sqinter> y \<le> z \<sqinter> w"
    by (metis le_infI1 le_infI2 le_inf_iff)

  lemma proj_seq_leq: "\<pi> w \<cdot> \<pi> x \<le> \<pi> y \<cdot> \<pi> z \<Longrightarrow> \<pi> (w \<cdot> x) \<le> \<pi> (y \<cdot> z)"
    by (subst proj_mult[symmetric], subst proj_mult[symmetric], rule proj_iso, assumption)

  lemma proj_mult_iso: "w \<le>\<^sub>\<pi> y \<Longrightarrow> x \<le>\<^sub>\<pi> z \<Longrightarrow> w \<cdot> x \<le>\<^sub>\<pi> y \<cdot> z"
    apply (simp add: proj_leq_def)
    apply (rule proj_seq_leq)
    apply (rule mult_isol_var[rule_format])
    by auto

  theorem sequential:
    assumes "r, g \<turnstile> \<lbrace>p\<rbrace> c1 \<lbrace>q\<rbrace>" and "r, g \<turnstile> \<lbrace>q\<rbrace> c2 \<lbrace>s\<rbrace>"
    shows "r, g \<turnstile> \<lbrace>p\<rbrace> c1 \<cdot> c2 \<lbrace>s\<rbrace>"
  proof (simp add: quintuple_def, intro conjI)
    show "r \<in> RG" and "g \<in> RG"
      by (metis assms(1) quintuple_def)+

    hence "p \<cdot> (r \<parallel> c1 \<cdot> c2) \<le> p \<cdot> ((r \<parallel> c1) \<cdot> (r \<parallel> c2))"
      by (metis order_refl rg3 mult_isol)
    also have "... \<le> p \<cdot> (r \<parallel> c1) \<cdot> (r \<parallel> c2)"
      by (metis mult_assoc order_refl)
    also have "... \<le>\<^sub>\<pi> q \<cdot> (r \<parallel> c2)"
      by (subst proj_leq_def, intro proj_seq_leq mult_isor[rule_format]) (metis assms(1) proj_leq_def quintuple_def)
    also have "... \<le>\<^sub>\<pi> s"
      by (metis assms(2) quintuple_def)
    finally show "p \<cdot> (r \<parallel> c1 \<cdot> c2) \<le>\<^sub>\<pi> s" .

    have "c1 \<cdot> c2 \<le> g \<cdot> g" using assms(1) and assms(2)
      by (auto intro!: mult_isol_var[rule_format] simp add: quintuple_def simp del: rg_idem_mult)
    also have "... = g"
      by (metis `g \<in> RG` rg_idem_mult)
    finally show "c1 \<cdot> c2 \<le> g" .
  qed

  lemma [simp]: "x \<le>\<^sub>\<pi> y \<sqinter> z \<longleftrightarrow> x \<le>\<^sub>\<pi> y \<and> x \<le>\<^sub>\<pi> z"
    by (simp add: proj_leq_def)

  lemma proj_star: "\<pi> ((\<pi> x)\<^sup>\<star>) = \<pi> (x\<^sup>\<star>)"
    apply (rule antisym)
    apply (metis inf_commute inf_le2 meet_iso order_refl proj_def star_iso)
    by (metis Con_star proj_def)

  lemma proj_star_inductl_nc: "\<pi> z + \<pi> x \<cdot> \<pi> y \<le> \<pi> y \<Longrightarrow> x\<^sup>\<star>\<cdot>z \<le>\<^sub>\<pi> y"
    apply (auto simp add: proj_leq_def)
    apply (subst proj_mult[symmetric])
    apply (subst proj_star[symmetric])
    apply (subst proj_idem[symmetric]) back back back
    apply (subst proj_mult)
    apply (subst proj_idem[symmetric]) back back back
    apply (rule proj_iso)
    apply (rule star_inductl[rule_format])
    by auto

  theorem parallel:
    assumes "r1, g1 \<turnstile> \<lbrace>p1\<rbrace> c1 \<lbrace>q1\<rbrace>" and "g2 \<le> r1"
    and "r2, g2 \<turnstile> \<lbrace>p2\<rbrace> c2 \<lbrace>q2\<rbrace>" and "g1 \<le> r2"
    shows "(r1 \<sqinter> r2), (g1 \<parallel> g2) \<turnstile> \<lbrace>p1 \<sqinter> p2\<rbrace> c1 \<parallel> c2 \<lbrace>q1 \<sqinter> q2\<rbrace>"
  proof (simp add: quintuple_def, intro conjI)
    have "r1 \<in> RG" and "r2 \<in> RG" and "g1 \<in> RG" and "g2 \<in> RG"
      by (metis assms(1) assms(3) quintuple_def)+

    have "(p1 \<sqinter> p2) \<cdot> (r1 \<sqinter> r2 \<parallel> c1 \<parallel> c2) \<le> p1 \<cdot> (r1 \<sqinter> r2 \<parallel> c1 \<parallel> c2)"
      by (metis inf_le1 mult_isor)
    also have "... \<le> p1 \<cdot> (r1 \<sqinter> r2 \<parallel> c1 \<parallel> g2)"
      by (intro mult_isol_var[rule_format] par_double_iso[rule_format] conjI order_refl) (metis assms(3) quintuple_def)
    also have "... \<le> p1 \<cdot> (r1 \<parallel> (c1 \<parallel> r1))"
      by (intro mult_isol_var[rule_format] conjI order_refl) (metis assms(2) inf_le1 par_comm par_double_iso par_isol)
    also have "... \<le> p1 \<cdot> (r1 \<parallel> c1)"
      by (intro  mult_isol[rule_format]) (metis `r1 \<in> RG` eq_iff par_assoc par_comm rg_idem_par)
    also have "... \<le>\<^sub>\<pi> q1"
      by (metis assms(1) quintuple_def)
    finally show "(p1 \<sqinter> p2) \<cdot> (r1 \<sqinter> r2 \<parallel> c1 \<parallel> c2) \<le>\<^sub>\<pi> q1" .

    have "(p1 \<sqinter> p2) \<cdot> (r1 \<sqinter> r2 \<parallel> c1 \<parallel> c2) \<le> p2 \<cdot> (r1 \<sqinter> r2 \<parallel> c1 \<parallel> c2)"
     by (metis inf_le2 mult_isor)
    also have "... \<le> p2 \<cdot> (r1 \<sqinter> r2 \<parallel> g1 \<parallel> c2)"
      by (intro mult_isol_var[rule_format] conjI order_refl par_double_iso[rule_format]) (metis assms(1) quintuple_def)
    also have "... \<le> p2 \<cdot> (r2 \<parallel> r2 \<parallel> c2)"
      by (intro mult_isol_var[rule_format] conjI order_refl) (metis assms(4) inf_le2 par_comm par_double_iso par_isor)
    also have "... \<le> p2 \<cdot> (r2 \<parallel> c2)"
      by (intro mult_isol[rule_format]) (metis `r2 \<in> RG` eq_refl rg_idem_par)
    also have "... \<le>\<^sub>\<pi> q2"
      by (metis assms(3) quintuple_def)
    finally show "(p1 \<sqinter> p2) \<cdot> (r1 \<sqinter> r2 \<parallel> c1 \<parallel> c2) \<le>\<^sub>\<pi> q2" .

    show "c1 \<parallel> c2 \<le> g1 \<parallel> g2" using assms(1) and assms(3)
      by (auto simp: quintuple_def)

    show "r1 \<sqinter> r2 \<in> RG"
      by (metis `r1 \<in> RG` `r2 \<in> RG` rg_meet_closed)
    show "g1 \<parallel> g2 \<in> RG"
      by (metis `g1 \<in> RG` `g2 \<in> RG` rg_par_closed)
  qed

  lemma proj_add_lub [simp]: "x + y \<le>\<^sub>\<pi> z \<longleftrightarrow> x \<le>\<^sub>\<pi> z \<and> y \<le>\<^sub>\<pi> z"
    by (auto simp add: proj_leq_def)

  lemma helper: "r\<parallel>x\<^sup>\<star> = r + r\<parallel>x\<cdot>x\<^sup>\<star>"
    by (metis par_distl par_unitr star_unfoldl_eq)

  thm star_inductr

  lemma proj_star_inductl: "\<pi> (z + y \<cdot> x) \<le> \<pi> y \<Longrightarrow> \<pi> (z \<cdot> x\<^sup>\<star>) \<le> \<pi> y"
    sorry

  lemma star_rule: "p\<cdot>r \<le>\<^sub>\<pi> p \<Longrightarrow> r, g \<turnstile> \<lbrace>p\<rbrace> c \<lbrace>p\<rbrace> \<Longrightarrow> r, g \<turnstile> \<lbrace>p\<rbrace> c\<^sup>\<star> \<lbrace>p\<rbrace>"
    apply (auto simp add: quintuple_def proj_leq_def)
    defer
    apply (metis boffa par_unitl rg2 rg_idem_mult rg_unit star_rtc_least_eq sup_absorb1 sup_commute sup_id_star2 sup_left_commute)
    apply (subst helper)
    apply (simp add: distrib_left)
    apply (rule order_trans[of _ "\<pi> (p \<cdot> (r \<parallel> c) \<cdot> (r \<parallel> c)\<^sup>\<star>)"])
    apply (metis mult_assoc pmult_def proj.mult_isol rg5 star_slide_var)
    apply (rule order_trans[of _ "\<pi> (p \<cdot> (r \<parallel> c)\<^sup>\<star>)"])
    apply (metis mult_assoc pmult_def proj.mult_isol star_1l)
    apply (rule proj_star_inductl)
    by (metis eq_iff inf_commute inf_sup_distrib1 proj_def sup_absorb2 sup_commute)

end

end
