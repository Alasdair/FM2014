theory RelyGuarantee
  imports WeakTrioid HoareLogic
begin

class rg_algebra = weak_trioid + meet_semilattice +
  fixes I :: "'a set"
  assumes inv_def: "r \<in> I \<longleftrightarrow>  1 \<le> r \<and> r \<parallel> r = r \<and> r\<parallel>(x\<cdot>y) \<le> (r\<parallel>x)\<cdot>(r\<parallel>y) \<and> (r\<parallel>x)\<^sup>+ = r\<parallel>x\<^sup>+"
  and inv_add_closed: "\<lbrakk>r \<in> I; s \<in> I\<rbrakk> \<Longrightarrow> (r+s) \<in> I"
  and inv_mult_closed: "\<lbrakk>r \<in> I; s \<in> I\<rbrakk> \<Longrightarrow> (r\<cdot>s) \<in> I"
  and inv_par_closed: "\<lbrakk>r \<in> I; s \<in> I\<rbrakk> \<Longrightarrow> (r\<parallel>s) \<in> I"
  and inv_meet_closed: "\<lbrakk>r \<in> I; s \<in> I\<rbrakk> \<Longrightarrow> (r \<sqinter> s) \<in> I"
begin

definition guarantee_relation :: "'a \<Rightarrow> 'a \<Rightarrow> bool" ("_ guar _" [99, 99] 100) where
  "b guar g \<equiv> g \<in> I \<and> b \<le> g"

definition jones_quintuples :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("\<lbrace>_,_\<rbrace>_\<lbrace>_,_\<rbrace>") where
  "\<lbrace>a, r\<rbrace> b \<lbrace>c, g\<rbrace> \<equiv> \<lbrace>a\<rbrace> r\<parallel>b \<lbrace>c\<rbrace> \<and> r \<in> I \<and> b guar g"

lemma inv_unit: "1 \<in> I"
  by (metis eq_refl inv_def par_unitl)

lemma inv_idem_mult: "r \<in> I \<Longrightarrow> r\<cdot>r = r"
  by (metis inv_def join_plus_equiv leq_def_join mult_oner par_unitr star_one star_trancl star_unfoldl_eq)

lemma inv_idem_par : "r \<in> I \<Longrightarrow> r \<parallel> r = r"
  by (metis inv_def)

lemma inv_exchange: "r \<in> I \<Longrightarrow> r\<parallel>(x\<cdot>y) = (r\<parallel>x)\<cdot>(r\<parallel>y)"
  nitpick oops

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
  shows "\<lbrace>a, r \<sqinter> r'\<rbrace> b\<cdot>b' \<lbrace>c', g\<cdot>g'\<rbrace>"
proof -
  have "b\<cdot>b' \<le> g\<cdot>g'"
    by (metis assms(1) assms(2) guarantee_relation_def jones_quintuples_def mult_isol_var)
  hence guarantee: "(b\<cdot>b') guar (g\<cdot>g')"
    by (metis assms(1) assms(2) inv_mult_closed guarantee_relation_def jones_quintuples_def)
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
  by (metis add_comm add_iso inv_def inv_idem_mult leq_def mult_isor)

theorem rg_transcl: "\<lbrace>a, r\<rbrace> b \<lbrace>a, g\<rbrace> \<Longrightarrow> \<lbrace>a, r\<rbrace> b\<^sup>+ \<lbrace>a, g\<rbrace>"
  by (metis guar_trancl inv_def iteration2 jones_quintuples_def)

theorem rg_star: "\<lbrakk>\<lbrace>a\<rbrace> r \<lbrace>a\<rbrace>; \<lbrace>a, r\<rbrace> b \<lbrace>a, g\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>a, r\<rbrace> b\<^sup>* \<lbrace>a, g\<rbrace>"
  by (metis star_trancl2 guarantee_relation_def jones_quintuples_def rg_add rg_one rg_transcl)

end


end
