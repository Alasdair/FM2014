theory RelyGuarantee
  imports HoareLogic
begin

class rg_algebra = ckat +
  fixes I :: "'a set"
  assumes inv_def: "r \<in> I \<longleftrightarrow>  1 \<le> r \<and> r \<parallel> r = r \<and> r\<parallel>(x\<cdot>y) \<le> (r\<parallel>x)\<cdot>(r\<parallel>y) \<and> (r\<parallel>x)\<^sup>+ = r\<parallel>x\<^sup>+"
  and inv_add_closed: "\<lbrakk>r \<in> I; s \<in> I\<rbrakk> \<Longrightarrow> (r+s) \<in> I"
  and inv_mult_closed: "\<lbrakk>r \<in> I; s \<in> I\<rbrakk> \<Longrightarrow> (r\<cdot>s) \<in> I"
  and inv_par_closed: "\<lbrakk>r \<in> I; s \<in> I\<rbrakk> \<Longrightarrow> (r\<parallel>s) \<in> I"
begin

definition guarantee_relation :: "'a \<Rightarrow> 'a \<Rightarrow> bool" ("_ guar _" [99, 99] 100) where
  "b guar g \<equiv> g \<in> I \<and> b \<le> g"

definition jones_quintuples :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("\<lbrace>_,_\<rbrace>_\<lbrace>_,_\<rbrace>") where
  "\<lbrace>a, r\<rbrace> b \<lbrace>c, g\<rbrace> \<equiv> \<lbrace>a\<rbrace> r\<parallel>b \<lbrace>c\<rbrace> \<and> r \<in> I \<and> b guar g"

lemma inv_refl: "r \<in> I \<Longrightarrow> 1 \<le> r"
  by (metis inv_def)

lemma inv_unit: "1 \<in> I"
  by (metis eq_refl inv_def par_unitl)

lemma inv_idem_mult: "r \<in> I \<Longrightarrow> r\<cdot>r = r"
  by (metis boffa_var inv_def less_eq_def mult_incl sup_id_star1)

lemma inv_idem_par : "r \<in> I \<Longrightarrow> r \<parallel> r = r"
  by (metis inv_def)

lemma inv_exchange: "r \<in> I \<Longrightarrow> r\<parallel>(x\<cdot>y) = (r\<parallel>x)\<cdot>(r\<parallel>y)"
  by (smt eq_iff exchange inv_def inv_idem_mult)

lemma guar_par: "\<lbrakk>b guar g; b' guar g'\<rbrakk> \<Longrightarrow> (b \<parallel> b') guar (g \<parallel> g')"
  by (metis guarantee_relation_def inv_par_closed par_double_iso)

theorem paralel_composition_basic:
  assumes "\<lbrace>p, r\<rbrace> x \<lbrace>q, g\<rbrace>" and "\<lbrace>p, r\<rbrace> y \<lbrace>q, g\<rbrace>"
  shows "\<lbrace>p, r\<rbrace> x\<parallel>y \<lbrace>q, g\<rbrace>"
proof -
  have guar: "x\<parallel>y \<le> g"
    by (metis (full_types) assms(1) assms(2) par_isol par_isor guarantee_relation_def inv_idem_par jones_quintuples_def order_trans)
  have a: "p\<cdot>(r\<parallel>(x\<parallel>y)) = p\<cdot>((r\<parallel>x)\<parallel>(r\<parallel>y))"
    by (metis assms(1) inv_idem_par jones_quintuples_def par_assoc par_comml)
  also have b: "... = (p\<cdot>(r\<parallel>x))\<parallel>(p\<cdot>(r\<parallel>y))"
    by (metis assms(1) hoare_triple_def jones_quintuples_def test_assocl)
  also have "... = (p\<cdot>(r\<parallel>x)\<cdot>q)\<parallel>(p\<cdot>(r\<parallel>y)\<cdot>q)"
    by (metis assms(1) assms(2) hoare_triple_def jones_quintuples_def)
  also have "... = ((p\<cdot>(r\<parallel>x))\<parallel>(p\<cdot>(r\<parallel>y)))\<cdot>q"
    by (metis assms(2) hoare_triple_def jones_quintuples_def test_assocr)
  also have "... = p\<cdot>(r\<parallel>(x\<parallel>y))\<cdot>q"
    by (metis a b)
  finally show ?thesis
    by (metis assms(2) guar guarantee_relation_def hoare_triple_def jones_quintuples_def)
qed

theorem paralel_composition_post:
  assumes "\<lbrace>p, r\<rbrace> x \<lbrace>q, g\<rbrace>" and "\<lbrace>p, r\<rbrace> y \<lbrace>q', g\<rbrace>"
  shows "\<lbrace>p, r\<rbrace> x\<parallel>y \<lbrace>q + q', g\<rbrace>"
proof -
  have guar: "x\<parallel>y \<le> g"
    by (metis (full_types) assms(1) assms(2) par_isol par_isor guarantee_relation_def inv_idem_par jones_quintuples_def order_trans)
  have a: "p\<cdot>(r\<parallel>(x\<parallel>y)) = p\<cdot>((r\<parallel>x)\<parallel>(r\<parallel>y))"
    by (metis assms(1) inv_idem_par jones_quintuples_def par_assoc par_comml)
  also have b: "... = (p\<cdot>(r\<parallel>x))\<parallel>(p\<cdot>(r\<parallel>y))"
    by (metis assms(1) hoare_triple_def jones_quintuples_def test_assocl)
  also have "... = (p\<cdot>(r\<parallel>x)\<cdot>q)\<parallel>(p\<cdot>(r\<parallel>y)\<cdot>q')"
    by (metis assms(1) assms(2) hoare_triple_def jones_quintuples_def)
  also have "... \<le> (p\<cdot>(r\<parallel>x)\<cdot>(q + q'))\<parallel>(p\<cdot>(r\<parallel>y)\<cdot>(q + q'))"
    by (metis add_ub2 mult_isol par_double_iso subdistl)
  also have "... = ((p\<cdot>(r\<parallel>x))\<parallel>(p\<cdot>(r\<parallel>y)))\<cdot>(q + q')"
    by (metis assms(1) assms(2) b hoare_equiv jones_quintuples_def test_add_closed test_assocr)
  also have "... = p\<cdot>(r\<parallel>(x\<parallel>y))\<cdot>(q + q')"
    by (metis a b)
  finally show ?thesis
    by (metis assms hoare_equiv guar guarantee_relation_def jones_quintuples_def test_add_closed)
qed

theorem paralel_composition_post_guar:
  assumes "\<lbrace>p, r\<rbrace> x \<lbrace>q, g\<rbrace>" and "\<lbrace>p, r\<rbrace> y \<lbrace>q', g'\<rbrace>"
  shows "\<lbrace>p, r\<rbrace> x\<parallel>y \<lbrace>q + q', g\<parallel>g'\<rbrace>"
proof -
  have guar: "x\<parallel>y \<le> g\<parallel>g'"
   by (metis (full_types) assms(1) assms(2) par_isol par_isor guarantee_relation_def jones_quintuples_def order_trans)
  have a: "p\<cdot>(r\<parallel>(x\<parallel>y)) = p\<cdot>((r\<parallel>x)\<parallel>(r\<parallel>y))"
    by (metis assms(1) inv_idem_par jones_quintuples_def par_assoc par_comml)
  also have b: "... = (p\<cdot>(r\<parallel>x))\<parallel>(p\<cdot>(r\<parallel>y))"
    by (metis assms(1) hoare_triple_def jones_quintuples_def test_assocl)
  also have "... = (p\<cdot>(r\<parallel>x)\<cdot>q)\<parallel>(p\<cdot>(r\<parallel>y)\<cdot>q')"
    by (metis assms(1) assms(2) hoare_triple_def jones_quintuples_def)
  also have "... \<le> (p\<cdot>(r\<parallel>x)\<cdot>(q + q'))\<parallel>(p\<cdot>(r\<parallel>y)\<cdot>(q + q'))"
    by (metis add_ub2 mult_isol par_double_iso subdistl)
  also have "... = ((p\<cdot>(r\<parallel>x))\<parallel>(p\<cdot>(r\<parallel>y)))\<cdot>(q + q')"
    by (metis assms(1) assms(2) b hoare_equiv jones_quintuples_def test_add_closed test_assocr)
  also have "... = p\<cdot>(r\<parallel>(x\<parallel>y))\<cdot>(q + q')"
    by (metis a b)
  finally show ?thesis
    by (metis assms hoare_equiv guar guarantee_relation_def jones_quintuples_def test_add_closed inv_par_closed)
qed

theorem paralel_composition_post_par:
  assumes "\<lbrace>p, r\<rbrace> x \<lbrace>q, g\<rbrace>" and "\<lbrace>p, r\<rbrace> y \<lbrace>q', g'\<rbrace>"
  shows "\<lbrace>p, r\<rbrace> x\<parallel>y \<lbrace>q\<parallel>q', g\<parallel>g'\<rbrace>"
proof -
  have guar: "x\<parallel>y \<le> g\<parallel>g'"
   by (metis (full_types) assms(1) assms(2) par_isol par_isor guarantee_relation_def jones_quintuples_def order_trans)
  have a: "p\<cdot>(r\<parallel>(x\<parallel>y)) = p\<cdot>((r\<parallel>x)\<parallel>(r\<parallel>y))"
    by (metis assms(1) inv_idem_par jones_quintuples_def par_assoc par_comml)
  also have b: "... = (p\<cdot>(r\<parallel>x))\<parallel>(p\<cdot>(r\<parallel>y))"
    by (metis assms(1) hoare_triple_def jones_quintuples_def test_assocl)
  also have "... =((p\<cdot>(r\<parallel>x))\<cdot>q)\<parallel>((p\<cdot>(r\<parallel>y))\<cdot>q')"
    by (metis assms(1) assms(2) hoare_triple_def jones_quintuples_def)
  also have "... = ((p\<cdot>(r\<parallel>x))\<parallel>(p\<cdot>(r\<parallel>y)))\<cdot>(q\<parallel>q')"
    by (metis assms(1) assms(2) test_exchanger hoare_triple_def jones_quintuples_def)
  also have "... = p\<cdot>(r\<parallel>(x\<parallel>y))\<cdot>(q\<parallel>q')"
    by (metis a b)
  finally show ?thesis
    by (metis assms hoare_triple_def guar guarantee_relation_def jones_quintuples_def test_par_closed inv_par_closed)
qed

lemma consequence_rule_pre:
  assumes "p' \<le> p" and "p' \<in> B" and "\<lbrace>p, r\<rbrace> x \<lbrace>q, g\<rbrace>"
  shows "\<lbrace>p', r\<rbrace> x \<lbrace>q, g\<rbrace>"
  by (metis assms(1) assms(2) assms(3) jones_quintuples_def weakening_rule)

lemma consequence_rule_rely:
  assumes "r' \<le> r" and "r' \<in> I" and "\<lbrace>p, r\<rbrace> x \<lbrace>q, g\<rbrace>" and "r\<parallel>x \<le> x"
  shows "\<lbrace>p, r'\<rbrace> x \<lbrace>q, g\<rbrace>"
  by (metis antisym assms(1) assms(2) assms(3) assms(4) inv_refl jones_quintuples_def less_eq_def par_subdistl par_unitl)

lemma consequence_rule_guar:
  assumes "g \<le> g'" and "g' \<in> I" and "\<lbrace>p, r\<rbrace> x \<lbrace>q, g\<rbrace>" and "g\<parallel>x \<le> x"
  shows "\<lbrace>p, r\<rbrace> x \<lbrace>q, g'\<rbrace>"
  by (metis (full_types) assms(1) assms(2) assms(3) guarantee_relation_def jones_quintuples_def order_trans)

lemma consequence_rule_post:
  assumes "q \<le> q'" and "q' \<in> B" and "\<lbrace>p, r\<rbrace> x \<lbrace>q, g\<rbrace>"
  shows "\<lbrace>p, r\<rbrace> x \<lbrace>q', g\<rbrace>"
  by (metis assms(1) assms(2) assms(3) jones_quintuples_def weakening_rule2)

theorem consequence_rule:
  assumes "p' \<le> p" "r' \<le> r" "g \<le> g'" "q \<le> q'" "\<lbrace>p, r\<rbrace> x \<lbrace>q, g\<rbrace>" "p' \<in> B" "r' \<in> I" "g' \<in> I" "q' \<in> B" "r\<parallel>x \<le> x" "g\<parallel>x \<le> x"
  shows "\<lbrace>p', r'\<rbrace> x \<lbrace>q', g'\<rbrace>"
  by (metis assms consequence_rule_pre consequence_rule_rely consequence_rule_guar consequence_rule_post)

theorem sequential_composition:
  assumes a: "\<lbrace>p, r\<rbrace> x \<lbrace>m, g\<rbrace>" and b: "\<lbrace>m, r\<rbrace> y \<lbrace>q, g\<rbrace>"
  shows "\<lbrace>p, r\<rbrace> x\<cdot>y \<lbrace>q, g\<rbrace>"
proof -
  have "x \<le> g \<and> y \<le> g"
    by (metis a b guarantee_relation_def jones_quintuples_def)
  also have "x\<cdot>y \<le> g\<cdot>g"
    by (metis calculation mult_isol mult_isor order_trans)
  ultimately have c: "x\<cdot>y \<le> g"
    by (metis (full_types) b guarantee_relation_def inv_idem_mult jones_quintuples_def)
  have d: "p\<cdot>((x\<cdot>y)\<parallel>r) = p\<cdot>(x\<parallel>r)\<cdot>(y\<parallel>r)"
    by (metis b par_comm inv_exchange jones_quintuples_def mult_assoc)
  also have e: "... = p\<cdot>(x\<parallel>r)\<cdot>m\<cdot>(y\<parallel>r)"
    by (metis a par_comm hoare_triple_def jones_quintuples_def)
  also have "... = p\<cdot>(x\<parallel>r)\<cdot>m\<cdot>(y\<parallel>r)\<cdot>q"
    by (metis b par_comm mult_assoc hoare_triple_def jones_quintuples_def)
  also have "... = p\<cdot>((x\<cdot>y)\<parallel>r)\<cdot>q"
    by (metis d e)
  finally show ?thesis
    by (metis a b c par_comm guarantee_relation_def hoare_triple_def jones_quintuples_def)
qed

theorem rg_one: "\<lbrace>p, r\<rbrace> 1 \<lbrace>q, g\<rbrace> \<longleftrightarrow> \<lbrace>p\<rbrace> r \<lbrace>q\<rbrace> \<and> r \<in> I \<and> g \<in> I"
  by (metis guarantee_relation_def inv_refl jones_quintuples_def par_unitr)

theorem rg_add: 
  assumes "\<lbrace>p, r\<rbrace> x \<lbrace>q, g\<rbrace>" and "\<lbrace>p, r\<rbrace> y \<lbrace>q, g\<rbrace>"
  shows "\<lbrace>p, r\<rbrace> x + y \<lbrace>q, g\<rbrace>"
proof -
  have "p\<cdot>(r\<parallel>(x + y)) = p\<cdot>(r\<parallel>x) + p\<cdot>(r\<parallel>y)"
    by (metis distrib_left par_distl)
  also have "... = p\<cdot>(r\<parallel>x)\<cdot>q + p\<cdot>(r\<parallel>y)\<cdot>q"
    by (metis assms hoare_triple_def jones_quintuples_def)
  also have "... = p\<cdot>(r\<parallel>(x + y))\<cdot>q"
    by (metis distrib_left distrib_right par_distl)
  finally show ?thesis
    by (metis add_lub assms(1) assms(2) guarantee_relation_def hoare_triple_def jones_quintuples_def)
qed

lemma one_transcl: "1\<^sup>+ = 1"
  by (metis mult_1_right star_one star_trancl)

lemma inv_plus_eq: "r \<in> I \<Longrightarrow> r = r\<^sup>+"
  by (metis par_comm par_unitl inv_def one_transcl)

lemma inv_def_var: "r \<in> I \<Longrightarrow> (r\<parallel>x)\<^sup>+ = r\<parallel>x\<^sup>+"
  by (metis inv_def)

lemma guar_transcl: "b guar g \<Longrightarrow> b\<^sup>+ guar g"
  by (metis add_lub guarantee_relation_def inv_def inv_idem_mult less_eq_def star_slide_var star_subdist_var star_trancl star_unfoldl_eq tc)

theorem rg_transcl: "\<lbrace>p, r\<rbrace> x \<lbrace>p, g\<rbrace> \<Longrightarrow> \<lbrace>p, r\<rbrace> x\<^sup>+ \<lbrace>p, g\<rbrace>"
  by (metis (full_types) guar_transcl inv_def iteration2 jones_quintuples_def)

theorem rg_star: "\<lbrakk>\<lbrace>p\<rbrace> r \<lbrace>p\<rbrace>; \<lbrace>p, r\<rbrace> x \<lbrace>p, g\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>p, r\<rbrace> x\<^sup>\<star> \<lbrace>p, g\<rbrace>"
  by (metis star_trancl2 guarantee_relation_def jones_quintuples_def rg_add rg_one rg_transcl)

end

end
