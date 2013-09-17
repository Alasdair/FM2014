theory WeakTrioid
  imports OrderTheory
begin

text {*
  Weak trioid is a double dioid wihtout the following axiom:
    mult_annir: "x\<cdot>0 = 0"
*}

class idem_monoid = comm_monoid_add + order +
  assumes leq_def: "x \<le> y \<longleftrightarrow> x + y = y"
  and strict_leq_def: "x < y \<longleftrightarrow> x \<le> y \<and> \<not>(y \<le> x)"

context idem_monoid
begin

lemma add_idem: "x + x = x" using iffD1[OF leq_def order_refl] .

(* Join semilattice *)
lemma ex_lub_dioid: "is_lub (x + y) {x, y}"
  apply (simp add: is_lub_def is_ub_def leq_def)
  by (metis add_assoc add_commute add_idem)

subclass join_semilattice
  by (unfold_locales, metis ex_lub_dioid)

lemma join_plus_equiv [simp]: "x \<squnion> y = x + y"
  by (metis ex_lub_dioid join_def lub_is_lub)

lemma order_prop: "(x \<le> y) \<longleftrightarrow> (\<exists>z. (x + z = y))"
  by (metis add_assoc add_idem leq_def)

lemma add_ub1 [simp]: "x \<le> x + y"
  by (metis add_assoc add_idem leq_def)

lemma add_ub2 [simp]: "y \<le> x + y"
  by (metis add_assoc add_commute add_idem leq_def)

lemma add_lub_var: "x \<le> z \<longrightarrow> y \<le> z \<longrightarrow> x + y \<le> z"
  by (metis add_assoc leq_def)

lemma add_lub: "x + y \<le> z \<longleftrightarrow> x \<le> z \<and> y \<le> z"
  by (metis add_assoc add_ub2 leq_def)

lemma add_iso: "x \<le> y \<longrightarrow> x + z \<le> y + z"
  by (metis add_lub leq_def order_refl)

lemma add_iso_var: "x \<le> y \<longrightarrow> u \<le> v \<longrightarrow> x + u \<le> y + v"
  by (metis add_commute add_iso add_lub)

lemma zero_least [simp]: "0 \<le> x"
  by (metis add_0_left join_plus_equiv leq_def_join)

lemma zero_unique [simp]: "x \<le> 0 \<longleftrightarrow> x = 0"
  by (metis zero_least eq_iff)

lemma no_trivial_inverse: "x \<noteq> 0 \<longrightarrow> \<not>(\<exists>y. x + y = 0)"
  by (metis zero_unique order_prop)

end

class weak_dioid = idem_monoid + one +
  fixes mult :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<cdot>" 70)
  assumes mult_assoc: "(x\<cdot>y)\<cdot>z = x\<cdot>(y\<cdot>z)"
  and mult_onel: "1\<cdot>x = x"
  and mult_oner: "x\<cdot>1 = x"
  and mult_distl: "x\<cdot>(y+z) = x\<cdot>y+x\<cdot>z"
  and mult_distr: "(x+y)\<cdot>z = x\<cdot>z+y\<cdot>z" 
  and mult_annil: "0\<cdot>x = 0"

begin

(* Mult operator *)
lemma mult_isor: "x \<le> y \<Longrightarrow> z\<cdot>x \<le> z\<cdot>y"
  by (metis leq_def mult_distl)

lemma mult_isol: "x \<le> y \<Longrightarrow> x\<cdot>z \<le> y\<cdot>z"
  by (metis leq_def mult_distr)

lemma mult_isol_var: "u \<le> x \<and> v \<le> y \<longrightarrow> u \<cdot> v \<le> x \<cdot> y"
  by (metis mult_isol mult_isor order_trans)

lemma mult_double_iso: "x \<le> y \<longrightarrow> w \<cdot> x \<cdot> z \<le> w \<cdot> y \<cdot> z"
  by (metis mult_isol mult_isor)

lemma subdistl: "x\<cdot>z \<le> (x + y)\<cdot>z"
  by (metis mult_distr order_prop)

lemma subdistr: "z\<cdot>x \<le> z\<cdot>(x + y)"
  by (metis mult_distl order_prop)

end

class par_dioid = idem_monoid + one +
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

lemma par_isol: "x \<le> y \<Longrightarrow> x\<parallel>z \<le> y\<parallel>z"
  by (metis leq_def par_distr)

lemma par_isor: "x \<le> y \<Longrightarrow> z\<parallel>x \<le> z\<parallel>y"
  by (metis leq_def par_distl)

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

no_notation
  Transitive_Closure.trancl ("(_\<^sup>+)" [1000] 999) and
  Transitive_Closure.rtrancl ("(_\<^sup>*)" [1000] 999)

(* Weak Kleene Algebra, formed from a weak dioid *)
class wka = weak_dioid + 
  fixes star :: "'a \<Rightarrow> 'a" ("_\<^sup>*" [101] 100)
  assumes star_unfoldl: "1 + x\<cdot>x\<^sup>* \<le> x\<^sup>*"
  and star_unfoldr: "1 + x\<^sup>*\<cdot>x \<le> x\<^sup>*"
  and star_inductl: "z + x\<cdot>y \<le> y \<longrightarrow> x\<^sup>*\<cdot>z \<le> y"
  and star_inductr: "z + y\<cdot>x \<le> y \<longrightarrow> z\<cdot>x\<^sup>* \<le> y"

begin

lemma star_ref: "1 \<le> x\<^sup>*"
  by (metis add_lub star_unfoldr)

lemma star_plus_one [simp]: "1 + x\<^sup>* = x\<^sup>*"
  by (metis leq_def star_ref)

lemma star_1l: "x\<cdot>x\<^sup>* \<le> x\<^sup>*"
  by (metis add_lub star_unfoldl)

lemma star_1r: "x\<^sup>*\<cdot>x \<le> x\<^sup>*"
  by (metis add_lub star_unfoldr)

lemma star_trans_eq: "x\<^sup>*\<cdot>x\<^sup>* = x\<^sup>*"
  apply (rule antisym,metis add_commute eq_iff leq_def star_1l star_inductl)
  by (metis mult_onel star_plus_one subdistl)

lemma star_trans: "x\<^sup>* \<cdot> x\<^sup>* \<le> x\<^sup>*"
  by (metis eq_refl star_trans_eq)

lemma star_inductl_var: "x\<cdot>y \<le> y \<longrightarrow> x\<^sup>*\<cdot>y \<le> y"
  by (metis add_commute eq_refl leq_def star_inductl)

lemma star_inductr_var: "y\<cdot>x \<le> y \<longrightarrow> y\<cdot>x\<^sup>* \<le> y"
  by (metis add_commute eq_iff leq_def star_inductr)

lemma star_inductl_var_eq:  "x \<cdot> y = y \<longrightarrow> x\<^sup>* \<cdot> y \<le> y"
  by (metis eq_iff star_inductl_var)

lemma star_inductl_var_eq2: "y = x \<cdot> y \<longrightarrow> y = x\<^sup>* \<cdot> y"
  by (metis antisym mult_onel star_inductl_var_eq star_plus_one subdistl)

lemma star_inductl_one: "1 + x \<cdot> y \<le> y \<longrightarrow> x\<^sup>* \<le> y"
  by (metis mult_oner star_inductl)

lemma star_inductl_star: "x \<cdot> y\<^sup>* \<le> y\<^sup>* \<longrightarrow> x\<^sup>* \<le> y\<^sup>*"
  by (metis add_lub star_inductl_one star_ref)

lemma star_inductl_eq:  "z + x \<cdot> y = y \<longrightarrow> x\<^sup>* \<cdot> z \<le> y"
  by (metis eq_iff star_inductl)

lemma star_subid: "x \<le> 1 \<longrightarrow> x\<^sup>* = 1"
  by (metis add_commute eq_iff leq_def mult_isol mult_onel star_inductl_one star_ref)

lemma star_one [simp]: "1\<^sup>* = 1"
  by (metis eq_refl star_subid)

lemma star_subdist:  "x\<^sup>* \<le> (x + y)\<^sup>*"
  by (metis order_trans star_1l star_inductl_star subdistl)

lemma star_subdist_var:  "x\<^sup>* + y\<^sup>* \<le> (x + y)\<^sup>*"
  by (metis add_commute add_lub star_subdist)

lemma star_iso: "x \<le> y \<Longrightarrow> x\<^sup>* \<le> y\<^sup>*"
  by (metis leq_def star_subdist)

lemma star_invol: "x\<^sup>* = (x\<^sup>*)\<^sup>*"
  by (metis antisym mult_oner star_1r star_inductl_var_eq2 star_plus_one star_trans_eq subdistr)

lemma star2: "(1 + x)\<^sup>* = x\<^sup>*"
  apply(rule antisym, metis add_lub mult_oner order_trans star_1l star_invol star_iso star_plus_one subdistr)
  by (metis add_ub2 star_iso)

lemma sum_star_closure: "x \<le> z\<^sup>* \<and> y \<le> z\<^sup>* \<longrightarrow> x + y \<le> z\<^sup>*"
  by (metis add_lub)

lemma prod_star_closure: "x \<le> z\<^sup>* \<and> y \<le> z\<^sup>* \<longrightarrow> x \<cdot> y \<le> z\<^sup>*"
  by (metis mult_isol mult_isor order_trans star_trans_eq)

lemma star_star_closure: "x\<^sup>* \<le> z\<^sup>* \<longrightarrow> (x\<^sup>*)\<^sup>* \<le> z\<^sup>*"
  by (metis star_invol)

lemma star_closed_unfold: "x\<^sup>* = x \<longrightarrow> x = 1 + x \<cdot> x"
  by (metis star_plus_one star_trans_eq)

lemma star_ext: "x \<le> x\<^sup>*"
  by (metis mult_onel order_trans star_1r star_plus_one subdistl)

lemma star_sim1: "x\<cdot>z \<le> z\<cdot>y \<Longrightarrow> x\<^sup>*\<cdot>z \<le> z\<cdot>y\<^sup>*"
proof -
  assume assm: "x\<cdot>z \<le> z\<cdot>y"
  hence "(x\<cdot>z)\<cdot>y\<^sup>* \<le> (z\<cdot>y)\<cdot>y\<^sup>*"
    by (metis assm mult_isol)
  hence "(x\<cdot>z)\<cdot>y\<^sup>* \<le> z\<cdot>y\<^sup>*"
    by (metis mult_assoc mult_isor order_trans star_1l)
  hence "z + (x\<cdot>z)\<cdot>y\<^sup>* \<le> z\<cdot>y\<^sup>*"
    by (metis add_lub_var mult_oner star_plus_one subdistr)
  thus ?thesis
    by (metis mult_assoc star_inductl)
qed

lemma star_sim2: "z\<cdot>x \<le> y\<cdot>z \<Longrightarrow> z\<cdot>x\<^sup>* \<le> y\<^sup>*\<cdot>z"
proof -
  assume assm: "z\<cdot>x \<le> y\<cdot>z"
  hence "y\<^sup>*\<cdot>(z\<cdot>x) \<le> y\<^sup>*\<cdot>(y\<cdot>z)"
    by (metis assm mult_isor)
  hence "y\<^sup>*\<cdot>(z\<cdot>x) \<le> y\<^sup>*\<cdot>z"
    by (metis mult_assoc mult_isol mult_isor order_trans star_ext star_trans_eq)
  hence "z + y\<^sup>*\<cdot>(z\<cdot>x) \<le> y\<^sup>*\<cdot>z"
    by (metis add_lub mult_onel star_plus_one subdistl)
  thus ?thesis
    by (metis mult_assoc star_inductr)
qed

lemma star_slide1: "(x\<cdot>y)\<^sup>*\<cdot>x \<le> x\<cdot>(y\<cdot>x)\<^sup>*"
  by (metis mult_assoc order_refl star_sim1)

lemma star_slide_var1: "x\<^sup>* \<cdot> x \<le> x \<cdot> x\<^sup>*"
  by (metis eq_refl star_sim1)

lemma star_unfoldl_eq: "x\<^sup>* = 1 + x\<cdot>x\<^sup>*"
  by (metis antisym add_iso_var mult_isor order_refl star_inductl_one star_unfoldl)

lemma star_rtc1_eq [simp]: "1 + x + x\<^sup>* \<cdot> x\<^sup>* = x\<^sup>*"
  by (metis add_assoc leq_def star_ext star_plus_one star_trans_eq)

lemma star_rtc1: "1 + x + x\<^sup>* \<cdot> x\<^sup>* \<le> x\<^sup>*"
  by (metis eq_refl star_rtc1_eq)

lemma star_rtc2: "1 + x \<cdot> x \<le> x \<longleftrightarrow> x = x\<^sup>*"
  by (metis antisym star_ext star_inductl_one star_plus_one star_trans_eq)

lemma star_rtc3: "1 + x \<cdot> x = x \<longleftrightarrow> x = x\<^sup>*"
  by (metis order_refl star_plus_one star_rtc2 star_trans_eq)

lemma star_rtc_least: "1 + x + y \<cdot> y \<le> y \<longrightarrow> x\<^sup>* \<le> y"
  by (metis add_commute add_lub leq_def mult_isol mult_onel star_iso star_rtc3)

lemma star_rtc_least_eq: "1 + x + y \<cdot> y = y \<longrightarrow> x\<^sup>* \<le> y"
  by (metis eq_refl star_rtc_least)

lemma star_subdist_var_1: "x \<le> (x + y)\<^sup>*"
  by (metis add_lub star_ext)

lemma star_subdist_var_2: "x \<cdot> y \<le> (x + y)\<^sup>*"
  by (metis add_lub prod_star_closure star_ext)

lemma star_subdist_var_3: "x\<^sup>* \<cdot> y\<^sup>* \<le> (x + y)\<^sup>*"
  by (metis add_commute prod_star_closure star_subdist)

lemma star_denest [simp]: "(x + y)\<^sup>* = (x\<^sup>* \<cdot> y\<^sup>*)\<^sup>*"
proof (rule antisym)
  have "x + y \<le> x\<^sup>* \<cdot> y\<^sup>*"
    by (metis add_lub_var mult_isol_var mult_onel mult_oner star_ext star_ref)
  thus "(x + y)\<^sup>* \<le> (x\<^sup>* \<cdot> y\<^sup>*)\<^sup>*"
    by (metis star_iso)
  have "x\<^sup>* \<cdot> y\<^sup>* \<le> (x + y)\<^sup>*"
    by (metis star_subdist_var_3)
  thus "(x\<^sup>* \<cdot> y\<^sup>*)\<^sup>* \<le> (x + y)\<^sup>*"
    by (metis star_invol star_iso)
qed

lemma star_sum_var [simp]: "(x\<^sup>* + y\<^sup>*)\<^sup>* = (x + y)\<^sup>*"
  by (metis star_denest star_invol)

lemma star_denest_var [simp]: "(x + y)\<^sup>* = x\<^sup>* \<cdot> (y \<cdot> x\<^sup>*)\<^sup>*"
proof (rule antisym)
  have "1 \<le> x\<^sup>* \<cdot> (y \<cdot> x\<^sup>*)\<^sup>*"
    by (metis add_lub mult_onel star_plus_one subdistl)
  moreover have "x \<cdot> x\<^sup>* \<cdot> (y \<cdot> x\<^sup>*)\<^sup>* \<le> x\<^sup>* \<cdot> (y \<cdot> x\<^sup>*)\<^sup>*"
    by (metis mult_isol star_1l)
  moreover have "y \<cdot> x\<^sup>* \<cdot> (y \<cdot> x\<^sup>*)\<^sup>* \<le> x\<^sup>* \<cdot> (y \<cdot> x\<^sup>*)\<^sup>*"
    by (metis mult_isol_var mult_onel star_1l star_ref)
  hence "1 + (x + y) \<cdot> x\<^sup>* \<cdot> (y \<cdot> x\<^sup>*)\<^sup>* \<le> x\<^sup>* \<cdot> (y \<cdot> x\<^sup>*)\<^sup>*"
    by (metis (full_types) add_lub calculation(1) calculation(2) mult_distr)
  thus "(x + y)\<^sup>* \<le> x\<^sup>* \<cdot> (y \<cdot> x\<^sup>*)\<^sup>*"
    by (metis mult_assoc star_inductl_one)
  have "(y \<cdot> x\<^sup>*)\<^sup>* \<le> (y\<^sup>* \<cdot> x\<^sup>*)\<^sup>*"
    by (metis mult_isol star_ext star_iso)
  moreover have "... = (x + y)\<^sup>*"
    by (metis add_commute star_denest)
  moreover have "x\<^sup>* \<le> (x + y)\<^sup>*"
    by (metis star_subdist)
  thus "x\<^sup>* \<cdot> (y \<cdot> x\<^sup>*)\<^sup>* \<le> (x + y)\<^sup>*"
    by (metis calculation prod_star_closure)
qed

lemma star_denest_var_2: "(x\<^sup>* \<cdot> y\<^sup>*)\<^sup>* = x\<^sup>* \<cdot> (y \<cdot> x\<^sup>*)\<^sup>*"
  by (metis star_denest star_denest_var)

lemma star_denest_var_3 [simp]: "x\<^sup>* \<cdot> (y\<^sup>* \<cdot> x\<^sup>*)\<^sup>* = (x\<^sup>* \<cdot> y\<^sup>*)\<^sup>*"
  by (metis star_denest star_denest_var star_invol)

lemma star_denest_var_4 [simp]: "(y\<^sup>* \<cdot> x\<^sup>*)\<^sup>* = (x\<^sup>* \<cdot> y\<^sup>*)\<^sup>*"
  by (metis add_commute star_denest)

lemma star_denest_var_5: "x\<^sup>* \<cdot> (y \<cdot> x\<^sup>*)\<^sup>* = y\<^sup>* \<cdot> (x \<cdot> y\<^sup>*)\<^sup>*"
  by (metis add_commute star_denest_var)

lemma star_unfoldr_eq: "1 + x\<^sup>*\<cdot>x = x\<^sup>*"
  by (smt mult_distl mult_distr mult_assoc mult_onel mult_oner star_unfoldl_eq star_inductl eq_iff star_unfoldr)

lemma star_slide: "(x\<cdot>y)\<^sup>*\<cdot>x = x\<cdot>(y\<cdot>x)\<^sup>*"
  by (smt add_commute mult_assoc star_unfoldr_eq star_slide1 mult_isor add_iso mult_isol mult_distl mult_oner mult_distr mult_onel star_unfoldl_eq eq_iff star_slide1)

lemma star_slide_var: "x\<^sup>*\<cdot>x = x\<cdot>x\<^sup>*"
  by (metis mult_onel mult_oner star_slide)

lemma star_prod_unfold [simp]: "1 + x \<cdot> (y \<cdot> x)\<^sup>* \<cdot> y = (x \<cdot> y)\<^sup>*"
  by (metis mult_assoc star_slide star_unfoldl_eq)

lemma star_sum_unfold_var [simp]: "1 + x\<^sup>* \<cdot> (x + y)\<^sup>* \<cdot> y\<^sup>* = (x + y)\<^sup>*"
  by (metis star_denest star_denest_var_3 star_denest_var_4 star_plus_one star_slide)

lemma star_sum_unfold [simp]: "x\<^sup>* + x\<^sup>* \<cdot> y \<cdot> (x + y)\<^sup>* = (x + y)\<^sup>*"
  by (metis mult_assoc mult_distl mult_oner star_denest_var star_prod_unfold star_slide)

lemma star_square: "(x \<cdot> x)\<^sup>* \<le> x\<^sup>*"
  by (metis (full_types) prod_star_closure star_ext star_invol star_iso)

lemma star_zero [simp]: "0\<^sup>* = 1"
  by (metis star_subid zero_least)

lemma star_sim3: "z \<cdot> x = y \<cdot> z \<longrightarrow> z \<cdot> x\<^sup>* = y\<^sup>* \<cdot> z"
  by (metis eq_iff star_sim1 star_sim2)

lemma star_sim4: "x \<cdot> y \<le>  y \<cdot> x \<longrightarrow> x\<^sup>* \<cdot> y\<^sup>* \<le> y\<^sup>* \<cdot> x\<^sup>*"
  by (metis star_sim1 star_sim2)

lemma star_inductr_eq: "z + y \<cdot> x = y \<longrightarrow> z \<cdot> x\<^sup>* \<le> y"
  by (metis eq_iff star_inductr)

lemma star_inductr_var_eq: "y \<cdot> x = y \<longrightarrow> y \<cdot> x\<^sup>* \<le> y"
  by (metis eq_iff star_inductr_var)

lemma star_inductr_var_eq2: "y \<cdot> x = y \<longrightarrow> y \<cdot> x\<^sup>* = y"
  by (metis mult_onel star_one star_sim3)

definition trancl :: "'a \<Rightarrow> 'a" ("_\<^sup>+" [101] 100) where
  "x\<^sup>+ \<equiv> x\<^sup>*\<cdot>x"

lemma trancl_ext: "x \<le> x\<^sup>+"
  by (metis mult_oner star_slide_var star_unfoldl_eq subdistr trancl_def)

lemma trancl_unfoldr: "x + x\<^sup>+\<cdot>x = x\<^sup>+"
  by (metis mult_assoc mult_distl mult_oner star_slide_var star_unfoldl_eq trancl_def)

lemma trancl_inductr: "z + y\<cdot>x \<le> y \<Longrightarrow> z\<cdot>x\<^sup>+ \<le> y"
  by (metis add_ub2 mult_distl order_trans star_inductr star_slide_var star_unfoldl_eq trancl_def)

lemma trancl_unfoldl: "x + x\<cdot>x\<^sup>+ = x\<^sup>+"
  by (metis mult_assoc star_slide_var trancl_def trancl_unfoldr)

lemma trancl_inductl: "z + x\<cdot>y \<le> y \<Longrightarrow> x\<^sup>+\<cdot>z \<le> y"
  by (metis add_lub mult_assoc order_prop star_inductl subdistr trancl_def)

lemma star_trancl: "x\<^sup>+ = x \<cdot> x\<^sup>*"
  by (metis star_slide_var trancl_def)

lemma star_trancl2: "x\<^sup>* = 1 + x\<^sup>+"
  by (metis star_trancl star_unfoldl_eq)

end

class weak_trioid = weak_dioid + par_dioid + wka

class weak_cka = weak_trioid +
  assumes exchange: "(w\<parallel>x)\<cdot>(y\<parallel>z) \<le> (w\<cdot>y)\<parallel>(x\<cdot>z)"
begin

lemma mult_incl: "x\<cdot>y \<le> x\<parallel>y"
  by (metis par_unitl par_unitr exchange mult_onel mult_oner)

lemma small_exchange1: "(x\<parallel>y)\<cdot>z \<le> x\<parallel>(y\<cdot>z)"
  by (metis exchange mult_oner par_unitl)

lemma small_exchange2: "x\<cdot>(y\<parallel>z) \<le> (x\<cdot>y)\<parallel>z"
  by (metis exchange mult_onel par_comm par_unitl)

end

end
