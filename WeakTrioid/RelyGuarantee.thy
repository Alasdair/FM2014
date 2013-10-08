theory RelyGuarantee
  imports WeakTrioid HoareLogic
begin

class rg_algebra = weak_trioid + meet_semilattice +
  fixes RG :: "'a set"
  and hom :: "'a \<Rightarrow> 'a" ("\<lbrakk>_\<rbrakk>")
  assumes rg1: "r \<in> RG \<Longrightarrow> r \<parallel> r \<le> r"
  and rg2: "r \<in> RG \<Longrightarrow> s \<in> RG \<Longrightarrow> r \<le> r \<parallel> s"
  and rg3: "r \<in> RG \<Longrightarrow> r\<parallel>(x\<cdot>y) = (r\<parallel>x)\<cdot>(r\<parallel>y)"
  and rg4: "r \<in> RG \<Longrightarrow> r\<parallel>x\<^sup>+ \<le> (r\<parallel>x)\<^sup>+"
  and rg_unit: "1 \<in> RG"
  and rg_meet_closed: "\<lbrakk>r \<in> RG; s \<in> RG\<rbrakk> \<Longrightarrow> (r \<sqinter> s) \<in> RG"
  and rg_par_closed: "\<lbrakk>r \<in> RG; s \<in> RG\<rbrakk> \<Longrightarrow> (r \<parallel> s) \<in> RG"

  and hom_iso: "x \<le> y \<Longrightarrow> \<lbrakk>x\<rbrakk> \<le> \<lbrakk>y\<rbrakk>"
  and hom_meet: "\<lbrakk>x \<sqinter> y\<rbrakk> = \<lbrakk>x\<rbrakk> \<sqinter> \<lbrakk>y\<rbrakk>"
  and hom_join [simp]: "\<lbrakk>x + y\<rbrakk> = \<lbrakk>x\<rbrakk> + \<lbrakk>y\<rbrakk>"
  and hom_mult: "\<lbrakk>x\<cdot>y\<rbrakk> = \<lbrakk>\<lbrakk>x\<rbrakk>\<cdot>\<lbrakk>y\<rbrakk>\<rbrakk>"
  and hom_trancl_inductr: "\<lbrakk>z + y\<cdot>x\<rbrakk> \<le> \<lbrakk>y\<rbrakk> \<Longrightarrow> \<lbrakk>z\<cdot>x\<^sup>+\<rbrakk> \<le> \<lbrakk>y\<rbrakk>"

begin

  declare mult_onel [simp]
    and mult_oner [simp]
    and par_unitl [simp]
    and par_unitr [simp]

  definition quintuple :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("_, _ \<turnstile> \<lbrace>_\<rbrace> _ \<lbrace>_\<rbrace>") where
    "r, g \<turnstile> \<lbrace>p\<rbrace> c \<lbrace>q\<rbrace> \<equiv> \<lbrakk>p\<cdot>(r\<parallel>c)\<rbrakk> \<le> \<lbrakk>q\<rbrakk> \<and> c \<le> g \<and> r \<in> RG \<and> g \<in> RG"

  lemma rg_idem_mult [simp]: "r \<in> RG \<Longrightarrow> r\<cdot>r = r"
    using rg3[where x = 1 and y = 1 and r = r, simplified] ..

  lemma rg_idem_par : "r \<in> RG \<Longrightarrow> r \<parallel> r = r"
    by (metis eq_iff rg1 rg2)

  lemma [simp]: "x \<le> \<lbrakk>y \<sqinter> z\<rbrakk> \<longleftrightarrow> x \<le> \<lbrakk>y\<rbrakk> \<and> x \<le> \<lbrakk>z\<rbrakk>"
    by (simp add: hom_meet bin_glb_var)

  lemma meet_iso: "x \<le> z \<Longrightarrow> y \<le> w \<Longrightarrow> x \<sqinter> y \<le> z \<sqinter> w"
    by (metis (full_types) bin_glb_var order_refl order_trans)

  theorem sequential:
    assumes "r, g \<turnstile> \<lbrace>p\<rbrace> c1 \<lbrace>q\<rbrace>" and "r, g \<turnstile> \<lbrace>q\<rbrace> c2 \<lbrace>s\<rbrace>"
    shows "r, g \<turnstile> \<lbrace>p\<rbrace> c1 \<cdot> c2 \<lbrace>s\<rbrace>"
  proof (simp add: quintuple_def, intro conjI)
    show "r \<in> RG" and "g \<in> RG"
      by (metis assms(1) quintuple_def)+

    hence "\<lbrakk>p \<cdot> (r \<parallel> c1 \<cdot> c2)\<rbrakk> \<le> \<lbrakk>p \<cdot> ((r \<parallel> c1) \<cdot> (r \<parallel> c2))\<rbrakk>"
      by (intro hom_iso mult_isol[rule_format]) (metis order_refl rg3)
    also have "... \<le> \<lbrakk>p \<cdot> (r \<parallel> c1) \<cdot> (r \<parallel> c2)\<rbrakk>"
      by (metis mult_assoc order_refl)
    also have "... \<le> \<lbrakk>q \<cdot> (r \<parallel> c2)\<rbrakk>"
      by (subst hom_mult, subst hom_mult, rule hom_iso, rule mult_isol[rule_format], metis assms(1) quintuple_def)
    also have "... \<le> \<lbrakk>s\<rbrakk>"
      by (metis assms(2) quintuple_def)
    finally show "\<lbrakk>p \<cdot> (r \<parallel> c1 \<cdot> c2)\<rbrakk> \<le> \<lbrakk>s\<rbrakk>" .

    have "c1 \<cdot> c2 \<le> g \<cdot> g"
      apply (intro mult_isol_var[rule_format] conjI)
      apply (metis assms(1) quintuple_def)
      by (metis assms(2) quintuple_def)
    also have "... = g"
      by (metis `g \<in> RG` rg_idem_mult)
    finally show "c1 \<cdot> c2 \<le> g" .
  qed

  theorem parallel:
    assumes "r1, g1 \<turnstile> \<lbrace>p1\<rbrace> c1 \<lbrace>q1\<rbrace>" and "g2 \<le> r1"
    and "r2, g2 \<turnstile> \<lbrace>p2\<rbrace> c2 \<lbrace>q2\<rbrace>" and "g1 \<le> r2"
    shows "(r1 \<sqinter> r2), (g1 \<parallel> g2) \<turnstile> \<lbrace>p1 \<sqinter> p2\<rbrace> c1 \<parallel> c2 \<lbrace>q1 \<sqinter> q2\<rbrace>"
  proof (simp add: quintuple_def, intro conjI)
    have "r1 \<in> RG" and "r2 \<in> RG" and "g1 \<in> RG" and "g2 \<in> RG"
      by (metis assms(1) assms(3) quintuple_def)+

    have "\<lbrakk>(p1 \<sqinter> p2) \<cdot> ((r1 \<sqinter> r2) \<parallel> (c1 \<parallel> c2))\<rbrakk> \<le> \<lbrakk>p1 \<cdot> ((r1 \<sqinter> r2) \<parallel> (c1 \<parallel> c2))\<rbrakk>"
      by (metis bin_glb_var hom_iso mult_isol order_refl par_comm)
    also have "... \<le> \<lbrakk>p1 \<cdot> ((r1 \<sqinter> r2) \<parallel> (c1 \<parallel> g2))\<rbrakk>"
      by (intro hom_iso mult_isol_var[rule_format] par_double_iso[rule_format] conjI order_refl) (metis assms(3) quintuple_def)
    also have "... \<le> \<lbrakk>p1 \<cdot> (r1 \<parallel> (c1 \<parallel> r1))\<rbrakk>"
      by (intro hom_iso mult_isol_var[rule_format] conjI order_refl) (metis assms(2) bin_glb_var eq_refl par_double_iso)
    also have "... \<le> \<lbrakk>p1 \<cdot> (r1 \<parallel> c1)\<rbrakk>"
      by (intro hom_iso mult_isor[rule_format])  (metis `r1 \<in> RG` eq_iff par_assoc par_comm rg_idem_par)
    also have "... \<le> \<lbrakk>q1\<rbrakk>"
      by (metis assms(1) quintuple_def)
    finally show "\<lbrakk>(p1 \<sqinter> p2) \<cdot> (r1 \<sqinter> r2 \<parallel> (c1 \<parallel> c2))\<rbrakk> \<le> \<lbrakk>q1\<rbrakk>" .

    have "\<lbrakk>(p1 \<sqinter> p2) \<cdot> (r1 \<sqinter> r2 \<parallel> (c1 \<parallel> c2))\<rbrakk> \<le> \<lbrakk>p2 \<cdot> (r1 \<sqinter> r2 \<parallel> (c1 \<parallel> c2))\<rbrakk>"
      by (metis bin_glb_var hom_iso mult_isol order_refl)
    also have "... \<le> \<lbrakk>p2 \<cdot> (r1 \<sqinter> r2 \<parallel> (g1 \<parallel> c2))\<rbrakk>"
      by (intro mult_isol_var[rule_format] conjI order_refl hom_iso par_double_iso[rule_format]) (metis assms(1) quintuple_def)
    also have "... \<le> \<lbrakk>p2 \<cdot> (r2 \<parallel> (r2 \<parallel> c2))\<rbrakk>"
      by (intro mult_isol_var[rule_format] hom_iso conjI order_refl) (metis assms(4) bin_glb_var order_refl par_double_iso)
    also have "... \<le> \<lbrakk>p2 \<cdot> (r2 \<parallel> c2)\<rbrakk>"
      by (intro hom_iso mult_isor[rule_format]) (metis `r2 \<in> RG` eq_iff par_comm par_comml rg_idem_par)
    also have "... \<le> \<lbrakk>q2\<rbrakk>"
      by (metis assms(3) quintuple_def)
    finally show "\<lbrakk>(p1 \<sqinter> p2) \<cdot> (r1 \<sqinter> r2 \<parallel> (c1 \<parallel> c2))\<rbrakk> \<le> \<lbrakk>q2\<rbrakk>" .

    show "c1 \<parallel> c2 \<le> g1 \<parallel> g2"
      by (rule par_double_iso[rule_format]) (metis assms(1) quintuple_def assms(3))

    show "r1 \<sqinter> r2 \<in> RG"
      by (metis `r1 \<in> RG` `r2 \<in> RG` rg_meet_closed)
    show "g1 \<parallel> g2 \<in> RG"
      by (metis `g1 \<in> RG` `g2 \<in> RG` rg_par_closed)
  qed

  theorem rg_star: "\<lbrakk>\<lbrakk>p\<cdot>r\<rbrakk> \<le> \<lbrakk>p\<rbrakk>; r, g \<turnstile> \<lbrace>p\<rbrace> c \<lbrace>p\<rbrace>\<rbrakk> \<Longrightarrow> r, g \<turnstile> \<lbrace>p\<rbrace> c\<^sup>* \<lbrace>p\<rbrace>"
    apply (simp add: quintuple_def)
    apply (intro conjI)
    apply (erule conjE)+
    apply (simp add: star_trancl2 par_distl mult_distl add_lub)
    apply (rule order_trans[where y = "\<lbrakk>p \<cdot> (r \<parallel> c)\<^sup>+\<rbrakk>"])
    apply (metis hom_iso mult_isor rg4)
    apply (rule hom_trancl_inductr)
    apply (simp add: add_lub)
    by (metis leq_def par_unitl rg2 rg_idem_mult rg_unit star_iso star_rtc3)

end

locale rg_module =
  fixes mod :: "'a::rg_algebra \<Rightarrow> 'b::boolean_algebra \<Rightarrow> 'b" (infixr "\<Colon>" 60)
  assumes mod_mult: "x \<cdot> y \<Colon> p \<le> y \<Colon> x \<Colon> p"
  and mod_isor: "p \<le> q \<Longrightarrow> x \<Colon> p \<le> x \<Colon> q"
  and mod_isol: "x \<le> y \<Longrightarrow> x \<Colon> p \<le> y \<Colon> p"

begin

definition quintuple :: "'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool" ("_, _ \<turnstile> \<lbrace>_\<rbrace> _ \<lbrace>_\<rbrace>") where
  "r, g \<turnstile> \<lbrace>p\<rbrace> c \<lbrace>q\<rbrace> \<longleftrightarrow> r \<parallel> c \<Colon> p \<le> q \<and> c \<le> g \<and> r \<in> I \<and> g \<in> I"

lemma inv_dist: "r \<in> I \<Longrightarrow> r\<parallel>(x\<cdot>y) \<le> (r\<parallel>x)\<cdot>(r\<parallel>y)"
  by (metis rg_algebra_class.inv_def)

lemma sequential:
  assumes "r, g1 \<turnstile> \<lbrace>p\<rbrace> c1 \<lbrace>q\<rbrace>" and "r, g2 \<turnstile> \<lbrace>q\<rbrace> c2 \<lbrace>s\<rbrace>"
  shows "r, (g1 \<parallel> g2) \<turnstile> \<lbrace>p\<rbrace> c1 \<cdot> c2 \<lbrace>s\<rbrace>"
proof -
  have r_inv: "r \<in> I"
    by (metis assms(1) quintuple_def)

  {
    have "r \<parallel> (c1 \<cdot> c2) \<Colon> p \<le> (r \<parallel> c1) \<cdot> (r \<parallel> c2) \<Colon> p"
      by (metis inv_dist mod_isol r_inv)
    also have "... \<le> r \<parallel> c2 \<Colon> r \<parallel> c1 \<Colon> p"
      by (metis mod_mult)
    also have "... \<le> r \<parallel> c2 \<Colon> q"
      by (metis assms(1) mod_isor quintuple_def)
    also have "... \<le> s"
      by (metis assms(2) quintuple_def)
    finally have "r \<parallel> (c1 \<cdot> c2) \<Colon> p \<le> s" .
  }
  moreover
  {
    have "c1 \<cdot> c2 \<le> g1 \<cdot> g2"
      by (metis assms(1) assms(2) mult_isol_var quintuple_def)
    also have "... \<le> g1 \<parallel> g2"
      by (metis assms(1) assms(2) inv_mult_par quintuple_def)
    finally have "c1 \<cdot> c2 \<le> g1 \<parallel> g2" .
  }
  ultimately show ?thesis
    by (metis assms(1) assms(2) inv_par_closed quintuple_def)
qed

end

end
