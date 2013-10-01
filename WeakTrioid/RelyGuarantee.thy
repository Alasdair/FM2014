theory RelyGuarantee
  imports WeakTrioid HoareLogic
begin

declare mult_onel [simp]
  and mult_oner [simp]
  and par_unitl [simp]
  and par_unitr [simp]

class rg_algebra = weak_trioid + meet_semilattice +
  fixes I :: "'a set"
  assumes inv1: "r \<in> I \<Longrightarrow> r \<parallel> r \<le> r"
  and inv2: "r \<in> I \<Longrightarrow> s \<in> I \<Longrightarrow> r \<le> r \<parallel> s"
  and inv3: "r \<in> I \<Longrightarrow> r\<parallel>(x\<cdot>y) = (r\<parallel>x)\<cdot>(r\<parallel>y)"
  (* and inv4: "r \<in> I \<Longrightarrow> r\<parallel>x\<^sup>+ \<le> (r\<parallel>x)\<^sup>+" *)
  and inv_unit: "1 \<in> I"
  and inv_meet_closed: "\<lbrakk>r \<in> I; s \<in> I\<rbrakk> \<Longrightarrow> (r \<sqinter> s) \<in> I"
  and inv_par_closed: "\<lbrakk>r \<in> I; s \<in> I\<rbrakk> \<Longrightarrow> (r \<parallel> s) \<in> I"

begin

lemma "r \<in> I \<Longrightarrow> r \<parallel> r \<le> r" oops
lemma "r \<in> I \<Longrightarrow> s \<in> I \<Longrightarrow> r \<le> r \<parallel> s" oops
lemma "r \<in> I \<Longrightarrow> r\<parallel>(x\<cdot>y) = (r\<parallel>x)\<cdot>(r\<parallel>y)" oops
lemma "r \<in> I \<Longrightarrow> r\<parallel>x\<^sup>+ \<le> (r\<parallel>x)\<^sup>+" oops

definition guarantee_relation :: "'a \<Rightarrow> 'a \<Rightarrow> bool" ("_ guar _" [99, 99] 100) where
  "b guar g \<equiv> g \<in> I \<and> b \<le> g"

definition jones_quintuples :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("\<lbrace>_,_\<rbrace>_\<lbrace>_,_\<rbrace>") where
  "\<lbrace>a, r\<rbrace> b \<lbrace>c, g\<rbrace> \<equiv> \<lbrace>a\<rbrace> r\<parallel>b \<lbrace>c\<rbrace> \<and> r \<in> I \<and> b guar g"

declare mult_onel [simp]
  and mult_oner [simp]
  and par_unitl [simp]
  and par_unitr [simp]

lemma inv_idem_mult [simp]: "r \<in> I \<Longrightarrow> r\<cdot>r = r"
  using inv3[where x = 1 and y = 1 and r = r, simplified] ..

lemma inv_idem_par : "r \<in> I \<Longrightarrow> r \<parallel> r = r"
  by (metis eq_iff inv1 inv2)

lemma guar_par: "\<lbrakk>b guar g; b' guar g'\<rbrakk> \<Longrightarrow> (b \<parallel> b') guar (g \<parallel> g')"
  by (metis par_comm par_isol inv_par_closed guarantee_relation_def order_trans)

theorem paralel_composition:
  assumes "\<lbrace>a, r\<rbrace> b \<lbrace>c, g\<rbrace>" and "\<lbrace>a', r'\<rbrace> b' \<lbrace>c', g'\<rbrace>"
  and "g' guar r" and "g guar r'"
  shows "\<lbrace>a \<sqinter> a', r \<sqinter> r'\<rbrace> b\<parallel>b' \<lbrace>c \<sqinter> c', g\<parallel>g'\<rbrace>"
proof -
  have "a\<cdot>(r\<parallel>b) \<le> c" 
    by (metis assms(1) hoare_triple_def jones_quintuples_def)
  hence "a\<cdot>((r\<parallel>r)\<parallel>b) \<le> c" 
    by (metis (full_types) assms(3) par_comm guarantee_relation_def inv_idem_par)
  hence "a\<cdot>(r\<parallel>(r\<parallel>b)) \<le> c" 
    by (metis par_comm par_comml)
  moreover have "b' \<le> r"
    by (metis assms(2) assms(3) guarantee_relation_def jones_quintuples_def order_trans)
  ultimately have "a\<cdot>(r\<parallel>(b\<parallel>b')) \<le> c" 
    by (metis par_assoc par_comm par_isol mult_isor order_trans)
  hence "(a \<sqinter> a')\<cdot>(r\<parallel>(b\<parallel>b')) \<le> c"
    by (metis bin_glb_var mult_isol order_refl order_trans)
  hence one: "(a \<sqinter> a')\<cdot>((r \<sqinter> r')\<parallel>(b\<parallel>b')) \<le> c" 
    by (metis bin_glb_var par_comm par_isor dual.order_trans eq_refl mult_isor)

  have "a'\<cdot>(r'\<parallel>b') \<le> c'" 
    by (metis assms(2) hoare_triple_def jones_quintuples_def)
  hence "a'\<cdot>((r'\<parallel>r')\<parallel>b') \<le> c'" 
    by (metis (full_types) assms(2) inv_idem_par jones_quintuples_def)
  hence "a'\<cdot>(r'\<parallel>(r'\<parallel>b')) \<le> c'"
    by (metis par_comm par_comml)
  moreover have "b \<le> r'"
    by (metis assms(1) assms(4) guarantee_relation_def jones_quintuples_def order_trans)
  ultimately have "a'\<cdot>(r'\<parallel>(b\<parallel>b')) \<le> c'" 
    by (metis par_assoc par_comm par_isol mult_isor order_trans)
  hence "(a \<sqinter> a')\<cdot>(r'\<parallel>(b\<parallel>b')) \<le> c'"
    by (metis bin_glb_var mult_isol order_refl order_trans)
  hence two: "(a \<sqinter> a')\<cdot>((r \<sqinter> r')\<parallel>(b\<parallel>b')) \<le> c'"
    by (metis bin_glb_var par_comm par_isor dual.order_trans eq_refl mult_isor)
  
  from one and two have "(a \<sqinter> a')\<cdot>((r \<sqinter> r')\<parallel>(b\<parallel>b')) \<le> c \<sqinter> c'"
    by (metis bin_glb_var)
  moreover have "(b\<parallel>b') guar (g\<parallel>g')"
    by (metis assms(1) assms(2) guar_par jones_quintuples_def)
  ultimately show ?thesis
    by (metis (full_types) assms(1) assms(2) hoare_triple_def jones_quintuples_def inv_meet_closed)
qed

theorem sequential_composition:
  assumes "\<lbrace>a, r\<rbrace> b \<lbrace>c, g\<rbrace>" and "\<lbrace>c, r'\<rbrace> b' \<lbrace>c', g'\<rbrace>"
  shows "\<lbrace>a, r \<sqinter> r'\<rbrace> b\<cdot>b' \<lbrace>c', g\<parallel>g'\<rbrace>"
proof -
  have "b\<cdot>b' \<le> g\<cdot>g'"
    by (metis assms(1) assms(2) guarantee_relation_def jones_quintuples_def mult_isol_var)
  hence guarantee: "(b\<cdot>b') guar (g\<parallel>g')"
    by (metis (full_types) assms(1) assms(2) guarantee_relation_def inv_mult_par inv_par_closed jones_quintuples_def order_trans)
  have "(r \<sqinter> r') \<in> I"
    by (metis assms(1) assms(2) jones_quintuples_def inv_meet_closed)
  hence "(r \<sqinter> r')\<parallel>(b\<cdot>b') \<le> ((r \<sqinter> r')\<parallel>b)\<cdot>((r \<sqinter> r')\<parallel>b')"
    by (insert inv_def[of "r \<sqinter> r'" b "b'"], simp)
  also have "... \<le> (r\<parallel>b)\<cdot>(r'\<parallel>b')"
    by (metis bin_glb_var par_comm par_isor dual.order_trans eq_refl mult_isol mult_isor)
  finally have "(r \<sqinter> r')\<parallel>(b\<cdot>b') \<le> (r\<parallel>b)\<cdot>(r'\<parallel>b')"
    by (metis)
  hence "\<lbrace>a\<rbrace>(r \<sqinter> r')\<parallel>(b\<cdot>b')\<lbrace>c'\<rbrace>"
    by (metis assms(1) assms(2) comp_antitony jones_quintuples_def)
  thus ?thesis using guarantee
    by (metis assms(1) assms(2) jones_quintuples_def inv_meet_closed)
qed

theorem rg_one: "\<lbrace>a, r\<rbrace> 1 \<lbrace>c, g\<rbrace> \<longleftrightarrow> \<lbrace>a\<rbrace> r \<lbrace>c\<rbrace> \<and> r \<in> I \<and> g \<in> I"
  by (metis par_unitr guarantee_relation_def inv_def jones_quintuples_def)

theorem rg_add: "\<lbrace>a, r\<rbrace> b + b' \<lbrace>c, g\<rbrace> \<longleftrightarrow> \<lbrace>a, r\<rbrace> b \<lbrace>c, g\<rbrace> \<and> \<lbrace>a, r\<rbrace> b' \<lbrace>c, g\<rbrace>"
proof (default, metis (full_types) add_lub par_distl choice guarantee_relation_def jones_quintuples_def)
  assume assms: "\<lbrace>a, r\<rbrace> b \<lbrace>c, g\<rbrace> \<and> \<lbrace>a, r\<rbrace> b' \<lbrace>c, g\<rbrace>"
  hence "r \<in> I \<and> (b + b') guar g"
    by (metis (full_types) add_lub guarantee_relation_def jones_quintuples_def)
  moreover have "\<lbrace>a\<rbrace> r \<parallel> (b + b') \<lbrace>c\<rbrace>"
    by (metis assms par_distl choice jones_quintuples_def)
  ultimately show "\<lbrace>a, r\<rbrace> b + b' \<lbrace>c, g\<rbrace>"
    by (metis jones_quintuples_def)
qed

lemma one_trancl: "1\<^sup>+ = 1"
  by (metis mult_oner star_one star_trancl)

lemma inv_plus_eq: "r \<in> I \<Longrightarrow> r = r\<^sup>+"
  by (metis inv_idem_mult star_inductr_var_eq2 star_trancl)

lemma inv_def_var: "r \<in> I \<Longrightarrow> (r\<parallel>x)\<^sup>+ = r\<parallel>x\<^sup>+"
  by (metis inv_def)

lemma guar_trancl: "b guar g \<Longrightarrow> b\<^sup>+ guar g"
  apply (simp only: guarantee_relation_def)
  apply (subgoal_tac "1 + g \<cdot> b \<le> g")
  apply (metis mult_onel trancl_inductr)
  by (metis add_commute add_iso inv_def inv_idem_mult leq_def mult_isor)

theorem rg_transcl: "\<lbrace>a, r\<rbrace> b \<lbrace>a, g\<rbrace> \<Longrightarrow> \<lbrace>a, r\<rbrace> b\<^sup>+ \<lbrace>a, g\<rbrace>"
  by (metis guar_trancl inv_def iteration2 jones_quintuples_def)

theorem rg_star: "\<lbrakk>\<lbrace>a\<rbrace> r \<lbrace>a\<rbrace>; \<lbrace>a, r\<rbrace> b \<lbrace>a, g\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>a, r\<rbrace> b\<^sup>* \<lbrace>a, g\<rbrace>"
  by (metis star_trancl2 guarantee_relation_def jones_quintuples_def rg_add rg_one rg_transcl)

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
