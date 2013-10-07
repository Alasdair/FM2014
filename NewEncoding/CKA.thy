theory CKA
  imports "$AFP/Kleene_Algebra/Kleene_Algebra"
begin

no_notation
  Transitive_Closure.trancl ("(_\<^sup>+)" [1000] 999)

context kleene_algebra begin

definition trancl :: "'a \<Rightarrow> 'a" ("_\<^sup>+" [101] 100) where
  "x\<^sup>+ \<equiv> x\<^sup>\<star>\<cdot>x"

lemma trancl_ext: "x \<le> x\<^sup>+"
  by (metis mult_oner star_slide_var star_unfoldl_eq subdistl trancl_def)

lemma trancl_unfoldr: "x + x\<^sup>+\<cdot>x = x\<^sup>+"
  by (metis add_0_left add_commute mult_onel star_slide_var star_zero trancl_def troeger)

lemma trancl_inductr: "z + y\<cdot>x \<le> y \<Longrightarrow> z\<cdot>x\<^sup>+ \<le> y"
  by (metis add_ub2 distrib_left order_trans star_inductr star_slide_var star_unfoldl_eq trancl_def)

lemma trancl_unfoldl: "x + x\<cdot>x\<^sup>+ = x\<^sup>+"
  by (metis mult_assoc star_slide_var trancl_def trancl_unfoldr)

lemma trancl_inductl: "z + x\<cdot>y \<le> y \<Longrightarrow> x\<^sup>+\<cdot>z \<le> y"
  by (metis add_lub mult_assoc order_prop star_inductl subdistl trancl_def)

lemma star_trancl: "x\<^sup>+ = x \<cdot> x\<^sup>\<star>"
  by (metis star_slide_var trancl_def)

lemma star_trancl2: "x\<^sup>\<star> = 1 + x\<^sup>+"
  by (metis star_trancl star_unfoldl_eq)

end

class par_dioid = join_semilattice_zero + one +
  fixes par :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<parallel>" 70)
  assumes par_assoc: "(x\<parallel>y)\<parallel>z = x\<parallel>(y\<parallel>z)"
  and par_comm: "x\<parallel>y = y\<parallel>x"
  and par_distl: "x\<parallel>(y+z) = x\<parallel>y+x\<parallel>z"
  and par_unitl: "1\<parallel>x = x"
  and par_annil: "0\<parallel>x = 0"
begin

(* Parallel operator *)
lemma par_comml: "y\<parallel>(x\<parallel>z) = x\<parallel>(y\<parallel>z)"
  by (metis par_assoc par_comm)

lemma par_distr: "(x+y)\<parallel>z = x\<parallel>z+y\<parallel>z" 
  by (metis par_comm par_distl)

lemma par_isor: "x \<le> y \<Longrightarrow> x\<parallel>z \<le> y\<parallel>z"
  by (metis less_eq_def par_distr)

lemma par_isol: "x \<le> y \<Longrightarrow> z\<parallel>x \<le> z\<parallel>y"
  by (metis less_eq_def par_distl)

lemma par_unitr: "x\<parallel>1 = x"
  by (metis par_comm par_unitl)

lemma par_annir: "x\<parallel>0 = 0"
  by (metis par_annil par_comm)

lemma par_subdistl: "x\<parallel>z \<le> (x + y)\<parallel>z"
  by (metis order_prop par_distr)

lemma par_subdistr: "z\<parallel>x \<le> z\<parallel>(x + y)"
  by (metis par_comm par_subdistl)

lemma par_double_iso: "w \<le> x \<and> y \<le> z \<longrightarrow> w\<parallel>y \<le> x\<parallel>z"
  by (metis order_trans par_isol par_isor)

end

class trioid = dioid + par_dioid

class cka = trioid + kleene_algebra + 
  assumes exchange: "(w\<parallel>x)\<cdot>(y\<parallel>z) \<le> (w\<cdot>y)\<parallel>(x\<cdot>z)"
begin

lemma mult_incl: "x\<cdot>y \<le> x\<parallel>y"
  by (metis par_unitl par_unitr exchange mult_onel mult_oner)

lemma small_exchange1: "(x\<parallel>y)\<cdot>z \<le> x\<parallel>(y\<cdot>z)"
  by (metis par_unitl exchange mult_oner)

lemma small_exchange2: "x\<cdot>(y\<parallel>z) \<le> (x\<cdot>y)\<parallel>z"
  by (metis par_unitr exchange mult_onel)

end

class ckat = cka + 
  fixes B :: "'a set"
  assumes test_idem:     "p \<in> B \<Longrightarrow> p\<cdot>p = p"
  and test_top:      "p \<in> B \<Longrightarrow> p \<le> 1"

  and test_exchangel: "\<lbrakk>p \<in> B; q \<in> B\<rbrakk> \<Longrightarrow> (p\<parallel>q)\<cdot>(x\<parallel>y) = (p\<cdot>x)\<parallel>(q\<cdot>y)" 
  and test_exchanger: "\<lbrakk>p \<in> B; q \<in> B\<rbrakk> \<Longrightarrow> (x\<parallel>y)\<cdot>(p\<parallel>q) = (x\<cdot>p)\<parallel>(y\<cdot>q)"

  and test_eq:        "\<lbrakk>p \<in> B; q \<in> B\<rbrakk> \<Longrightarrow> p\<parallel>q = p\<cdot>q"

  and test_add_closed:  "\<lbrakk>p \<in> B; q \<in> B\<rbrakk> \<Longrightarrow> (p + q) \<in> B"
  and test_mult_closed: "\<lbrakk>p \<in> B; q \<in> B\<rbrakk> \<Longrightarrow> (p \<cdot> q) \<in> B"
  and test_par_closed:  "\<lbrakk>p \<in> B; q \<in> B\<rbrakk> \<Longrightarrow> (p \<parallel> q) \<in> B"
begin

  lemma everything_preserves_tests:
    assumes test_one_closed: "1 \<in> B"
    and p_test: "p \<in> B"
    shows "p\<cdot>x = x\<cdot>p"
  proof -
    have "p\<cdot>x = (1\<parallel>p)\<cdot>(x\<parallel>1)"
      by (metis par_unitl par_unitr)
    also have "... = (1\<cdot>x)\<parallel>(p\<cdot>1)"
      by (metis p_test test_exchangel test_one_closed)
    also have "... = (1\<cdot>p)\<parallel>(x\<cdot>1)"
      by (metis mult_onel mult_oner par_comm)
    also have "... = x\<cdot>p"
      by (metis p_test par_unitl par_unitr test_exchanger test_one_closed)
    finally show ?thesis .
  qed

  lemma "p\<cdot>x \<le> x\<cdot>q"

lemma "p \<in> B \<Longrightarrow> p\<parallel>p = p"
  by (metis test_eq test_idem)

lemma test_comm: "\<lbrakk>p \<in> B; q \<in> B\<rbrakk> \<Longrightarrow> p\<cdot>q = q\<cdot>p"
  by (metis par_comm test_eq)

lemma "\<lbrakk>p \<in> B; q \<in> B; p\<cdot>x = p\<cdot>x\<cdot>q\<rbrakk> \<Longrightarrow> p\<cdot>x \<le> q"
  nitpick oops

lemma test_assocl: "p \<in> B \<Longrightarrow> p\<cdot>(x\<parallel>y) \<le> (p\<cdot>x)\<parallel>(p\<cdot>y)" 
  by (metis test_eq test_exchangel test_idem)

lemma test_assocr: "p \<in> B \<Longrightarrow> (x\<parallel>y)\<cdot>p \<le> (x\<cdot>p)\<parallel>(y\<cdot>p)"
  by (metis test_eq test_exchanger test_idem)

lemma encoding_eq: "\<lbrakk>p \<in> B; q \<in> B\<rbrakk> \<Longrightarrow> p\<cdot>x = p\<cdot>x\<cdot>q \<longleftrightarrow> p\<cdot>x \<le> x\<cdot>q"
proof (default, metis mult_assoc mult_isor mult_onel test_top)
  assume assm: "p \<in> B" "q \<in> B" "p\<cdot>x \<le> x\<cdot>q"
  have "p\<cdot>x \<le> p\<cdot>x\<cdot>q"
    by (metis assm(1) assm(3) mult_assoc mult_isol test_idem)
  moreover have "p\<cdot>x\<cdot>q \<le> p\<cdot>x"
    by (metis (full_types) assm(2) mult_isol mult_oner test_top)
  finally show "p \<in> B \<Longrightarrow> q \<in> B \<Longrightarrow> p \<cdot> x \<le> x \<cdot> q \<Longrightarrow> p \<cdot> x = p \<cdot> x \<cdot> q"
    by metis
qed

end
end
