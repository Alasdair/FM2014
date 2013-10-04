theory OrderTheory
  imports Main
begin

declare [[ smt_solver = z3]]
declare [[ smt_timeout = 60 ]]
declare [[ z3_options = "-memory:500" ]]

context order
begin

(* Pointfree ordering *)

definition pleq :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" (infix "\<sqsubseteq>" 50) where
  "pleq f g \<equiv> \<forall>x. f x \<le> g x"

definition isotone :: "('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "isotone f \<equiv> \<forall>x y. x \<le> y \<longrightarrow> f x \<le> f y"

lemma isotoneD: "\<lbrakk>isotone f; x \<le> y\<rbrakk> \<Longrightarrow> f x \<le> f y"
  by (metis isotone_def)

definition idempotent :: "('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "idempotent f \<equiv> f \<circ> f = f"

(* Lub *)

definition is_ub :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_ub x A \<longleftrightarrow> (\<forall>y\<in>A. y \<le> x)"

definition is_lub :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_lub x A \<longleftrightarrow> is_ub x A \<and> (\<forall>y.(\<forall>z\<in>A. z \<le> y) \<longrightarrow> x \<le> y)"

lemma is_lub_equiv: "is_lub x A \<longleftrightarrow> (\<forall>z. (x \<le> z \<longleftrightarrow> (\<forall>y\<in>A. y \<le> z)))"
  by (metis is_lub_def is_ub_def order_refl order_trans)

lemma is_lub_unique: "is_lub x A \<longrightarrow> is_lub y A \<longrightarrow> x = y"
  by (metis antisym is_lub_def is_ub_def)

definition lub :: "'a set \<Rightarrow> 'a" ("\<Sigma>") where
  "\<Sigma> A = (THE x. is_lub x A)"

lemma the_lub_leq: "\<lbrakk>\<exists>z. is_lub z X; \<And>z. is_lub z X \<longrightarrow> z \<le> x\<rbrakk> \<Longrightarrow> \<Sigma> X \<le> x"
  by (metis is_lub_unique lub_def the_equality)

lemma the_lub_geq: "\<lbrakk>\<exists>z. is_lub z X; \<And>z. is_lub z X \<Longrightarrow> x \<le> z\<rbrakk> \<Longrightarrow> x \<le> \<Sigma> X"
  by (metis is_lub_unique lub_def the_equality)

lemma singleton_lub: "\<Sigma> {y} = y"
  by (simp only: lub_def, rule the_equality, simp_all add: is_lub_def is_ub_def, metis eq_iff)

lemma surjective_lub: "surj \<Sigma>"
  by (metis singleton_lub surj_def)

lemma lub_subset: "\<lbrakk>X \<subseteq> Y; is_lub x X; is_lub y Y\<rbrakk> \<Longrightarrow> x \<le> y" by (metis in_mono is_lub_def is_ub_def)

lemma lub_is_lub [elim?]: "is_lub w A \<Longrightarrow> \<Sigma> A = w"
  by (metis is_lub_unique lub_def the_equality)

definition is_lb :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_lb x A \<longleftrightarrow> (\<forall>y\<in>A. x \<le> y)"

definition is_glb :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_glb x A \<longleftrightarrow> is_lb x A \<and> (\<forall>y.(\<forall>z\<in>A. y \<le> z) \<longrightarrow> y \<le> x)"

lemma is_glb_equiv: "is_glb x A \<longleftrightarrow> (\<forall>z. (z \<le> x \<longleftrightarrow> (\<forall>y\<in>A. z \<le> y)))"
  by (metis is_glb_def is_lb_def order_refl order_trans)

lemma is_glb_unique: "is_glb x A \<longrightarrow> is_glb y A \<longrightarrow> x = y"
  by (metis antisym is_glb_def is_lb_def)

definition glb :: "'a set \<Rightarrow> 'a" ("\<Pi>") where
  "\<Pi> A = (THE x. is_glb x A)"

lemma the_glb_leq: "\<lbrakk>\<exists>z. is_glb z X; \<And>z. is_glb z X \<longrightarrow> x \<le> z\<rbrakk> \<Longrightarrow> x \<le> \<Pi> X"
  by (metis glb_def is_glb_unique the_equality)

lemma glb_is_glb [elim?]: "is_glb w A \<Longrightarrow> \<Pi> A = w"
  by (metis is_glb_unique glb_def the_equality)

lemma is_glb_from_is_lub: "\<lbrakk>is_lub x {b. \<forall>a\<in>A. b \<le> a}\<rbrakk> \<Longrightarrow> is_glb x A"
  by (smt mem_Collect_eq is_glb_def is_lb_def is_lub_equiv order_refl)

lemma is_lub_from_is_glb: "\<lbrakk>is_glb x {b. \<forall>a\<in>A. a \<le> b}\<rbrakk> \<Longrightarrow> is_lub x A"
  by (smt mem_Collect_eq is_lub_def is_ub_def is_glb_equiv order_refl)

definition join :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<squnion>" 70) where
  "x \<squnion> y = \<Sigma> {x,y}"

definition meet :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<sqinter>" 70) where
  "x \<sqinter> y = \<Pi> {x,y}"

(* Join and meet preserving maps *)

definition ex_join_preserving :: "('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "ex_join_preserving f \<equiv> \<forall>X\<subseteq>UNIV. (\<exists>x. is_lub x X) \<longrightarrow> \<Sigma> (f ` X) = f (\<Sigma> X)"

definition ex_meet_preserving :: "('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "ex_meet_preserving g \<equiv> \<forall>X\<subseteq>UNIV. (\<exists>x. is_glb x X) \<longrightarrow> \<Pi> (g ` X) = g (\<Pi> X)"

definition join_preserving :: "('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "join_preserving f \<equiv> \<forall>X\<subseteq>UNIV. \<Sigma> (f ` X) = f (\<Sigma> X)"

definition meet_preserving :: "('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "meet_preserving g \<equiv> \<forall>X\<subseteq>UNIV. \<Pi> (g ` X) = g (\<Pi> X)"

lemma is_lub_to_is_glb_var: "order.is_lub (\<lambda>x y. y \<le> x) z {x, y} = is_glb z {x, y}"
proof -
  interpret int: order "\<lambda>(x::'a) y. y \<le> x" "\<lambda>x y. y < x" apply unfold_locales
    apply (metis less_le_not_le)
    apply (metis eq_refl)
    apply (metis order_trans)
    by (metis eq_iff)
  show ?thesis by (simp add: int.is_lub_def int.is_ub_def is_glb_def is_lb_def)
qed

end

(* Join and meet semilattices *)

class join_semilattice = order +
  assumes join_ex: "\<forall>x y. \<exists>z. is_lub z {x,y}"

begin

  lemma leq_def_join: "x \<le> y \<longleftrightarrow> x\<squnion>y = y"
    by (smt emptyE insertCI insertE is_lub_def is_ub_def join_ex le_less less_le_not_le lub_is_lub ord_eq_le_trans join_def)

  lemma join_idem: "x \<squnion> x = x" by (metis leq_def_join order_refl)

  lemma join_comm: "x \<squnion> y = y \<squnion> x" by (metis insert_commute join_def)

  lemma join_assoc: "(x \<squnion> y) \<squnion> z = x \<squnion> (y \<squnion> z)"
  proof -
    have "(x \<squnion> y) \<squnion> z \<le> x \<squnion> (y \<squnion> z)"
      by (simp add: join_def, smt insertCI insertE is_lub_def is_lub_equiv is_ub_def join_ex lub_is_lub singletonE)
    thus ?thesis
      by (simp add: join_def, smt insertCI insertE is_lub_def is_ub_def join_ex lub_is_lub order_trans singletonE eq_iff)
  qed

  lemma ex_join_preserving_iso: "ex_join_preserving f \<Longrightarrow> isotone f"
  proof (rule classical)
    assume not_iso: "\<not> isotone f" and join_pres: "ex_join_preserving f"
    obtain x and y where xy: "x \<le> y \<and> \<not> (f x \<le> f y)" by (metis isotone_def not_iso)
    have "\<exists>z. is_lub z {x,y}" by (metis join_ex)
    hence "f (\<Sigma> {x,y}) = \<Sigma> {f x, f y}"
      by (smt ex_join_preserving_def join_pres subset_UNIV image_empty image_insert)
    hence "x = y" by (metis join_def leq_def_join xy)
    thus "isotone f" by (metis order_refl xy)
  qed

end

class meet_semilattice = order +
  assumes meet_ex: "\<forall>x y. \<exists>z. is_glb z {x,y}"

sublocale meet_semilattice \<subseteq> dual!: join_semilattice
  "op \<ge>" "op >"
proof
  fix x y z :: 'a
  show "(y < x) = (y \<le> x \<and> \<not> x \<le> y)" using less_le_not_le .
  show "x \<le> x" by simp
  show "\<lbrakk>y \<le> x; z \<le> y\<rbrakk> \<Longrightarrow> z \<le> x" by simp
  show "\<lbrakk>y \<le> x; x \<le> y\<rbrakk> \<Longrightarrow> x = y" by simp
  have "\<forall>x y. \<exists>z. order.is_glb (\<lambda>x y. x \<le> y) z {x, y}" by (metis meet_ex)
  thus "\<forall>x y. \<exists>z. order.is_lub (\<lambda>x y. y \<le> x) z {x, y}" by (metis is_lub_to_is_glb_var)
qed

context meet_semilattice
begin

  lemma leq_def2: "x \<le> y \<longleftrightarrow> y\<sqinter>x = x"
    by (smt antisym emptyE glb_is_glb insertCI insertE is_glb_def is_lb_def meet_def meet_ex ord_le_eq_trans order_refl)

  lemma mult_idem: "x \<sqinter> x = x"
    by (metis leq_def2 order_refl)

  lemma mult_comm: "x \<sqinter> y = y \<sqinter> x"
    by (metis insert_commute meet_def)

  lemma bin_glb_var: "x\<sqinter>y \<ge> z \<longleftrightarrow> x \<ge> z \<and> y \<ge> z"
  proof
    assume a: "z \<le> x\<sqinter>y"
    hence "\<Pi> {x,z} = z" by (metis leq_def2 glb_is_glb insertI1 is_glb_equiv meet_ex meet_def)
    moreover have "\<Pi> {y,z} = z" by (metis a leq_def2 glb_is_glb insertI1 is_glb_equiv meet_ex mult_comm meet_def)
    ultimately show "z \<le> x \<and> z \<le> y" by (metis leq_def2 meet_def)
  next
    assume "z \<le> x \<and> z \<le> y"
    thus "z \<le> x \<sqinter> y"
      by (smt emptyE glb_is_glb insertE is_glb_equiv meet_ex meet_def ord_le_eq_trans)
  qed

  lemma mult_assoc: "(x \<sqinter> y) \<sqinter> z = x \<sqinter> (y \<sqinter> z)"
  proof -
    have "(x \<sqinter> y) \<sqinter> z \<le> x \<sqinter> (y \<sqinter> z)"
      by (metis eq_refl bin_glb_var)
    thus ?thesis
      by (metis antisym bin_glb_var order_refl)
  qed

  lemma ex_meet_preserving_iso: "ex_meet_preserving f \<Longrightarrow> isotone f"
  proof (rule classical)
    assume not_iso: "\<not> isotone f" and meet_pres: "ex_meet_preserving f"
    obtain x and y where xy: "x \<le> y \<and> \<not> (f x \<le> f y)" by (metis isotone_def not_iso)
    have "\<exists>z. is_glb z {x,y}" by (metis meet_ex)
    hence "f (\<Pi> {x,y}) = \<Pi> {f x, f y}"
      by (smt ex_meet_preserving_def meet_pres subset_UNIV image_empty image_insert)
    hence "x = y" by (metis leq_def2 meet_def mult_comm xy)
    thus "isotone f" by (metis order_refl xy)
  qed

end

(* Lattices *)

class lattice = join_semilattice + meet_semilattice

begin

  lemma absorb1: "x \<squnion> (x \<sqinter> y) = x" by (metis join_comm leq_def2 leq_def_join mult_assoc mult_idem)

  lemma absorb2: "x \<sqinter> (x \<squnion> y) = x" by (metis join_assoc join_idem leq_def2 leq_def_join mult_comm)

  lemma order_change: "x\<sqinter>y = y \<longleftrightarrow> y\<squnion>x = x" by (metis leq_def2 leq_def_join)

end

(* Complete join semilattices *)

class complete_join_semilattice = order +
  assumes  lub_ex: "\<exists>x. is_lub x A"

sublocale complete_join_semilattice \<subseteq> join_semilattice
  by (unfold_locales, metis lub_ex)

context complete_join_semilattice
begin

  lemma bot_ax: "\<exists>!b. \<forall>x. b \<le> x" by (metis empty_iff eq_iff is_lub_def lub_ex)

  definition bot :: "'a" ("\<bottom>") where "\<bottom> \<equiv> THE x. \<forall> y. x \<le> y"

  lemma prop_bot: "\<forall>x. \<bottom> \<le> x"
    by (simp only: bot_def, rule the1I2, smt bot_ax, metis)

  lemma is_lub_lub [intro?]: "is_lub (\<Sigma> X) X"
    by (metis lub_ex lub_is_lub)

  lemma lub_greatest [intro?]: "(\<And>y. y \<in> X \<Longrightarrow> y \<le> x) \<Longrightarrow> \<Sigma> X \<le> x"
    by (metis is_lub_equiv is_lub_lub)

  lemma lub_least [intro?]: "x \<in> X \<Longrightarrow> x \<le> \<Sigma> X"
    by (metis is_lub_def is_lub_lub is_ub_def)

  lemma empty_lub [simp]: "\<Sigma> {} = \<bottom>" by (metis emptyE is_lub_equiv lub_is_lub prop_bot)

  lemma bot_oner [simp]: "x \<squnion> \<bottom> = x" by (metis join_comm leq_def_join prop_bot)
  lemma bot_onel [simp]: "\<bottom> \<squnion> x = x" by (metis leq_def_join prop_bot)

end


(* Complete meet semilattice *)

class complete_meet_semilattice = order +
  assumes glb_ex: "\<exists>x. is_glb x A"

sublocale complete_meet_semilattice \<subseteq> meet_semilattice
  by (unfold_locales, metis glb_ex)

context complete_meet_semilattice
begin

  lemma top_ax: "\<exists>!t. \<forall>x. x \<le> t" by (metis empty_iff eq_iff glb_ex is_glb_def)

  definition top :: "'a" ("\<top>") where "\<top> \<equiv> THE x. \<forall> y. y \<le> x"

  lemma prop_top: "\<forall>x. x \<le> \<top>"
    by (simp only: top_def, rule the1I2, metis top_ax, metis)

 lemma is_glb_glb [intro?]: "is_glb (\<Pi> X) X"
   by (metis glb_ex glb_is_glb)

  lemma glb_greatest [intro?]: "(\<And>y. y \<in> X \<Longrightarrow> x \<le> y) \<Longrightarrow> x \<le> \<Pi> X"
    by (metis is_glb_def is_glb_glb)

  lemma glb_least [intro?]: "x \<in> X \<Longrightarrow> \<Pi> X \<le> x"
    by (metis is_glb_def is_glb_glb is_lb_def)

  lemma empty_glb [simp]: "\<Pi> {} = \<top>" by (metis empty_iff glb_is_glb is_glb_def is_lb_def prop_top)

end

class complete_lattice = complete_join_semilattice + complete_meet_semilattice

begin

  lemma univ_lub: "\<Sigma> UNIV = \<top>" by (metis eq_iff is_lub_equiv iso_tuple_UNIV_I lub_is_lub prop_top)

  lemma univ_glb: "\<Pi> UNIV = \<bottom>" by (metis eq_iff glb_is_glb is_glb_equiv iso_tuple_UNIV_I prop_bot)

end

sublocale complete_lattice \<subseteq> lattice
  by unfold_locales

(*
sublocale complete_join_semilattice \<subseteq> complete_lattice
  by (unfold_locales, smt is_lub_lub mem_Collect_eq is_glb_from_is_lub)

sublocale complete_meet_semilattice \<subseteq> complete_lattice
  by (unfold_locales, smt is_glb_glb mem_Collect_eq is_lub_from_is_glb)
*)

definition order_monomorphism :: "('a::order \<Rightarrow> 'b::order) \<Rightarrow> bool" where
  "order_monomorphism f \<equiv> \<forall>x y. (f x \<le> f y) \<longleftrightarrow> (x \<le> y)"

definition order_isomorphism :: "('a::order \<Rightarrow> 'b::order) \<Rightarrow> bool" where
  "order_isomorphism f \<equiv> order_monomorphism f \<and> surj f"

lemma order_monomorphism_inj: "order_monomorphism f \<Longrightarrow> inj f"
  by (simp add: order_monomorphism_def inj_on_def order_eq_iff)

lemma order_monomorphism_iso: "order_monomorphism f \<Longrightarrow> isotone f"
  by (simp add: order_monomorphism_def isotone_def)

(* +------------------------------------------------------------------------+
   | Fixpoints and Prefix Points                                            |
   +------------------------------------------------------------------------+ *)

context complete_lattice
begin

definition is_pre_fp :: "'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "is_pre_fp x f \<equiv> f x \<le> x"

definition is_post_fp :: "'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "is_post_fp x f \<equiv> x \<le> f x"

definition is_fp :: "'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "is_fp x f \<equiv> f x = x"

lemma is_fp_def_var: "is_fp x f = (is_pre_fp x f \<and> is_post_fp x f)"
  by (metis antisym eq_refl is_fp_def is_post_fp_def is_pre_fp_def)

definition is_lpp :: "'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "is_lpp x f \<equiv> (is_pre_fp x f) \<and> (\<forall>y. f y \<le> y \<longrightarrow> x \<le> y)"

lemma is_lpp_def_var: "is_lpp x f = (f x \<le> x \<and> (\<forall>y. f y \<le> y \<longrightarrow> x \<le> y))"
  by (metis is_lpp_def is_pre_fp_def)

definition is_gpp :: "'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "is_gpp x f \<equiv> (is_post_fp x f) \<and> (\<forall>y. y \<le> f y \<longrightarrow> y \<le> x)"

lemma is_gpp_def_var: "is_gpp x f = (x \<le> f x \<and> (\<forall>y. y \<le> f y \<longrightarrow> y \<le> x))"
  by (metis is_gpp_def is_post_fp_def)

definition is_lfp :: "'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "is_lfp x f \<equiv> is_fp x f \<and> (\<forall>y. is_fp y f \<longrightarrow> x \<le> y)"

definition is_gfp :: "'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "is_gfp x f \<equiv> is_fp x f \<and> (\<forall>y. is_fp y f \<longrightarrow> y \<le> x)"

definition least_prefix_point :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a" ("\<mu>\<^sub>\<le>") where
  "least_prefix_point f \<equiv> THE x. is_lpp x f"

definition greatest_postfix_point :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a" ("\<nu>\<^sub>\<le>") where
  "greatest_postfix_point f \<equiv> THE x. is_gpp x f"

definition least_fixpoint :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a" ("\<mu>") where
  "least_fixpoint f \<equiv> THE x. is_lfp x f"

definition greatest_fixpoint :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a" ("\<nu>") where
  "greatest_fixpoint f \<equiv> THE x. is_gfp x f"

lemma lpp_unique: "\<lbrakk>is_lpp x f; is_lpp y f\<rbrakk> \<Longrightarrow> x = y"
  by (metis eq_iff is_lpp_def_var)

lemma gpp_unique: "\<lbrakk>is_gpp x f; is_gpp y f\<rbrakk> \<Longrightarrow> x = y"
  by (metis eq_iff is_gpp_def_var)

lemma lpp_equality [intro?]: "is_lpp x f \<Longrightarrow> \<mu>\<^sub>\<le> f = x"
  by (simp add: least_prefix_point_def, rule the_equality, auto, metis antisym is_lpp_def is_pre_fp_def)

lemma gpp_equality [intro?]: "is_gpp x f \<Longrightarrow> \<nu>\<^sub>\<le> f = x"
  by (simp add: greatest_postfix_point_def, rule the_equality, auto, metis antisym is_gpp_def is_post_fp_def)

lemma lfp_equality: "is_lfp x f \<Longrightarrow> \<mu> f = x"
  by (simp add: least_fixpoint_def, rule the_equality, auto, metis antisym is_lfp_def)

lemma lfp_equality_var [intro?]: "\<lbrakk>f x = x; \<And>y. f y = y \<Longrightarrow> x \<le> y\<rbrakk> \<Longrightarrow> x = \<mu> f"
by (metis is_fp_def is_lfp_def lfp_equality)

lemma gfp_equality: "is_gfp x f \<Longrightarrow> \<nu> f = x"
  by (simp add: greatest_fixpoint_def, rule the_equality, auto, metis antisym is_gfp_def)

lemma gfp_equality_var [intro?]: "\<lbrakk>f x = x; \<And>y. f y = y \<Longrightarrow> y \<le> x\<rbrakk> \<Longrightarrow> x = \<nu> f"
by (metis gfp_equality is_fp_def is_gfp_def)

lemma lpp_is_lfp: "\<lbrakk>isotone f; is_lpp x f\<rbrakk> \<Longrightarrow> is_lfp x f"
by (metis dual.antisym dual.eq_refl is_fp_def is_lfp_def is_lpp_def_var isotoneD)

lemma gpp_is_gfp: "\<lbrakk>isotone f; is_gpp x f\<rbrakk> \<Longrightarrow> is_gfp x f"
by (metis dual.antisym dual.order_refl is_fp_def is_gfp_def is_gpp_def_var isotoneD)

(* +------------------------------------------------------------------------+
   | Knaster-Tarski                                                         |
   +------------------------------------------------------------------------+ *)

(* Modified version of Wenzel's proof of the Knaster-Tarski theorem *)

theorem knaster_tarski_lpp:
  assumes fmon: "isotone f"
  obtains a where "is_lpp a f"
proof
  let ?H = "{u. f u \<le> u}"
  let ?a = "\<Pi> ?H"
  have "is_pre_fp ?a f"
  proof -
    have "\<forall>x\<in>?H. ?a \<le> x" by (metis glb_least)
    hence "\<forall>x\<in>?H. f ?a \<le> f x" by (metis assms glb_least isotoneD)
    hence "\<forall>x\<in>?H. f ?a \<le> x" by (metis mem_Collect_eq order_trans)
    hence "f ?a \<le> \<Pi> ?H" by (smt glb_greatest)
    thus ?thesis by (metis is_pre_fp_def)
  qed
  moreover have "f y \<le> y \<Longrightarrow> ?a \<le> y"
    by (metis mem_Collect_eq glb_least)
  ultimately show "is_lpp ?a f"
    by (smt is_lpp_def mem_Collect_eq glb_least)
qed

corollary is_lpp_lpp [intro?]: "isotone f \<Longrightarrow> is_lpp (\<mu>\<^sub>\<le> f) f"
  using knaster_tarski_lpp by (metis lpp_equality)

theorem knaster_tarski:
  assumes fmon: "isotone f"
  obtains a where "is_lfp a f"
  by (metis assms is_lpp_lpp lpp_is_lfp)

corollary knaster_tarski_var: "isotone f \<Longrightarrow> \<exists>!x. is_lfp x f"
  using knaster_tarski by (metis lfp_equality)

corollary is_lfp_lfp [intro?]: "isotone f \<Longrightarrow> is_lfp (\<mu> f) f"
  using knaster_tarski by (metis lfp_equality)

(* Knaster-Tarski for greatest fixpoints *)

theorem knaster_tarski_gpp:
  assumes fmon: "isotone f"
  obtains a :: "'a" where "is_gpp a f"
proof
  let ?H = "{u. u \<le> f u}"
  let ?a = "\<Sigma> ?H"
  have "is_post_fp ?a f"
  proof -
    have "\<forall>x\<in>?H. x \<le> ?a" by (metis lub_least)
    hence "\<forall>x\<in>?H. x \<le> f ?a"
      by (metis (full_types) mem_Collect_eq assms lub_least isotoneD order_trans)
    hence "\<Sigma> ?H \<le> f ?a" by (smt lub_greatest)
    thus ?thesis by (metis is_post_fp_def)
  qed
  moreover have "y \<le> f y \<Longrightarrow> y \<le> ?a"
    by (metis mem_Collect_eq lub_least order_refl)
  ultimately show "is_gpp ?a f"
    by (smt is_gpp_def mem_Collect_eq lub_least)
qed

corollary is_gpp_gpp [intro?]: "isotone f \<Longrightarrow> is_gpp (\<nu>\<^sub>\<le> f) f"
by (metis gpp_equality knaster_tarski_gpp)

theorem knaster_tarski_greatest:
  assumes fmon: "isotone f"
  obtains a :: "'a" where "is_gfp a f"
  by (metis assms is_gpp_gpp gpp_is_gfp)

corollary knaster_tarski_greatest_var: "isotone f \<Longrightarrow> \<exists>!x. is_gfp x f"
by (metis gfp_equality knaster_tarski_greatest)

corollary is_gfp_gfp [intro?]: "isotone f \<Longrightarrow> is_gfp (\<nu> f) f"
by (metis gfp_equality knaster_tarski_greatest_var)

lemma lfp_is_lpp: "\<lbrakk>isotone f; is_lfp x f\<rbrakk> \<Longrightarrow>  is_lpp x f"
  by (metis lfp_equality lpp_is_lfp is_lpp_lpp)

lemma lfp_is_lpp_var: "isotone f \<Longrightarrow> \<mu> f = \<mu>\<^sub>\<le> f"
  by (metis lfp_is_lpp lpp_equality is_lfp_lfp)

lemma gfp_is_gpp: "\<lbrakk>isotone f; is_gfp x f\<rbrakk> \<Longrightarrow>  is_gpp x f"
  by (metis gfp_equality gpp_is_gfp is_gpp_gpp)

lemma gfp_is_gpp_var: "isotone f \<Longrightarrow> \<nu> f = \<nu>\<^sub>\<le> f"
  by (metis gfp_is_gpp gpp_equality is_gfp_gfp)

(* We now show some more properties of fixpoints *)

(* +------------------------------------------------------------------------+
   | Fixpoint Computation                                                   |
   +------------------------------------------------------------------------+ *)

lemma prefix_point_computation [simp]: "isotone f \<Longrightarrow> f (\<mu>\<^sub>\<le> f) = \<mu>\<^sub>\<le> f"
  by (metis is_lpp_lpp lpp_is_lfp is_lfp_def is_fp_def)

lemma fixpoint_computation [simp]: "isotone f \<Longrightarrow> f (\<mu> f) = \<mu> f"
  by (metis is_lpp_lpp lfp_equality lpp_is_lfp prefix_point_computation)

lemma greatest_prefix_point_computation [simp]: "isotone f \<Longrightarrow> f (\<nu>\<^sub>\<le> f) = \<nu>\<^sub>\<le> f"
  by (metis is_gpp_gpp gpp_is_gfp is_gfp_def is_fp_def)

lemma greatest_fixpoint_computation [simp]: "isotone f \<Longrightarrow> f (\<nu> f) = \<nu> f"
  by (metis is_gpp_gpp gfp_equality gpp_is_gfp greatest_prefix_point_computation)

(* +------------------------------------------------------------------------+
   | Fixpoint Induction                                                     |
   +------------------------------------------------------------------------+ *)

lemma prefix_point_induction [intro?]:
  assumes fmon: "isotone f"
  and pp: "f x \<le> x"
  shows "\<mu>\<^sub>\<le> f \<le> x"
  by (metis fmon is_lpp_def_var is_lpp_lpp pp)

lemma fixpoint_induction [intro?]:
  assumes fmon: "isotone f"
  and fp: "f x \<le> x" shows "\<mu> f \<le> x"
by (metis fmon fp lfp_is_lpp_var prefix_point_induction)


lemma greatest_postfix_point_induction [intro?]:
  assumes fmon: "isotone f"
  and pp: "x \<le> f x" shows "x \<le> \<nu>\<^sub>\<le> f"
  by (metis fmon is_gpp_def is_gpp_gpp pp)

lemma greatest_fixpoint_induction [intro?]:
  assumes fmon: "isotone f"
  and fp: "x \<le> f x" shows "x \<le> \<nu> f"
  by (metis fmon fp gfp_is_gpp_var greatest_postfix_point_induction)

lemma fixpoint_compose:
  assumes kmon: "isotone k" and comp: "g\<circ>k = k\<circ>h" and fp: "is_fp x h"
  shows "is_fp (k x) g"
  by (metis comp fp is_fp_def o_apply)

lemma fixpoint_mono:
  assumes fmon: "isotone f" and gmon: "isotone g"
  and fg: "f \<sqsubseteq> g" shows "\<mu> f \<le> \<mu> g"
  by (metis fg fixpoint_induction fmon gmon lfp_is_lpp_var pleq_def prefix_point_computation)

lemma greatest_fixpoint_mono:
  assumes fmon: "isotone f" and gmon: "isotone g"
  and fg: "f \<sqsubseteq> g" shows "\<nu> f \<le> \<nu> g"
  by (metis fg fmon gfp_is_gpp_var gmon greatest_fixpoint_induction greatest_prefix_point_computation pleq_def)

end

(* +------------------------------------------------------------------------+
   | Galois Connections                                                     |
   +------------------------------------------------------------------------+ *)

context order
begin

definition galois_connection :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "galois_connection f g \<equiv> \<forall>x y. (f x \<le> y) \<longleftrightarrow> (x \<le> g y)"

definition dual_galois_connection :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "dual_galois_connection f g \<equiv> \<forall>x y. (f x \<ge> y) \<longleftrightarrow> (x \<ge> g y)"

definition lower_adjoint :: "('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "lower_adjoint f \<equiv> \<exists>g. galois_connection f g"

definition upper_adjoint :: "('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "upper_adjoint g \<equiv> \<exists>f. galois_connection f g"

lemma deflation: "galois_connection f g \<Longrightarrow> f (g y) \<le> y"
  by (metis galois_connection_def le_less)

lemma inflation: "galois_connection f g \<Longrightarrow> x \<le> g (f x)"
  by (metis galois_connection_def le_less)

lemma lower_iso: "galois_connection f g \<Longrightarrow> isotone f"
  by (metis galois_connection_def inflation isotone_def order_trans)


lemma upper_iso: "galois_connection f g \<Longrightarrow> isotone g"
  by (metis deflation galois_connection_def isotone_def order_trans)

lemma lower_comp: "galois_connection f g \<Longrightarrow> f \<circ> g \<circ> f = f"
proof
  fix x
  assume "galois_connection f g"
  thus "(f \<circ> g \<circ> f) x = f x"
    by (metis (full_types) antisym deflation inflation isotone_def lower_iso o_apply)
qed

lemma upper_comp: "galois_connection f g \<Longrightarrow> g \<circ> f \<circ> g = g"
proof
  fix x
  assume "galois_connection f g"
  thus "(g \<circ> f \<circ> g) x = g x"
    by (metis (full_types) antisym deflation inflation isotone_def o_apply upper_iso)
qed

lemma upper_idempotency1: "galois_connection f g \<Longrightarrow> idempotent (f \<circ> g)"
  by (metis idempotent_def o_assoc upper_comp)

lemma upper_idempotency2: "galois_connection f g \<Longrightarrow> idempotent (g \<circ> f)"
  by (metis idempotent_def o_assoc lower_comp)

lemma galois_dual: "galois_connection f g \<Longrightarrow> dual_galois_connection g f"
  by (metis dual_galois_connection_def galois_connection_def)

lemma dual_galois_dual: "dual_galois_connection f g \<Longrightarrow> galois_connection g f"
  by (metis dual_galois_connection_def galois_connection_def)

lemma galois_dualize: "\<lbrakk>galois_connection F G \<Longrightarrow> P F G; dual_galois_connection G F\<rbrakk> \<Longrightarrow> P F G"
  by (metis dual_galois_dual)

lemma dual_galois_dualize: "\<lbrakk>dual_galois_connection F G \<Longrightarrow> P F G; galois_connection G F\<rbrakk> \<Longrightarrow> P F G"
  by (metis galois_dual)

lemma galois_comp: assumes g1: "galois_connection F G" and g2 :"galois_connection H K"
  shows "galois_connection (F \<circ> H) (K \<circ> G)"
  by (smt g1 g2 galois_connection_def o_apply)

lemma galois_id: "galois_connection id id" by (metis galois_connection_def id_def)

lemma galois_isotone1: "galois_connection f g \<Longrightarrow> isotone (g \<circ> f)"
  by (smt galois_connection_def inflation isotoneD isotone_def o_apply order_trans upper_iso)

lemma galois_isotone2: "galois_connection f g \<Longrightarrow> isotone (f \<circ> g)"
by (metis isotone_def lower_iso o_apply upper_iso)

lemma point_id1: "galois_connection f g \<Longrightarrow> id \<sqsubseteq> g \<circ> f"
  by (metis inflation id_apply o_apply pleq_def)

lemma point_id2: "galois_connection f g \<Longrightarrow> f \<circ> g \<sqsubseteq> id"
  by (metis deflation id_apply o_apply pleq_def)

lemma point_cancel: assumes g: "galois_connection f g" shows "f \<circ> g \<sqsubseteq> g \<circ> f"
by (metis assms order_trans pleq_def point_id1 point_id2)

lemma cancel: assumes g: "galois_connection f g" shows "f (g x) \<le> g (f x)"
by (metis assms deflation inflation order_trans)

lemma cancel_cor1: assumes g: "galois_connection f g"
  shows "(g x = g y) \<longleftrightarrow> (f (g x) = f (g y))"
  by (metis assms upper_comp o_apply)

lemma cancel_cor2: assumes g: "galois_connection f g"
  shows "(f x = f y) \<longleftrightarrow> (g (f x) = g (f y))"
  by (metis assms lower_comp o_apply)

lemma semi_inverse1: "galois_connection f g \<Longrightarrow> f x = f (g (f x))"
  by (metis o_def lower_comp)

lemma semi_inverse2: "galois_connection f g \<Longrightarrow> g x = g (f (g x))"
  by (metis o_def upper_comp)

lemma universal_mapping_property1:
  assumes a: "isotone g" and b: "\<forall>x. x \<le> g (f x)"
  and c: "\<forall>x y. (x \<le> g y) \<longrightarrow> (f x \<le> y)"
  shows "galois_connection f g"
  by (metis a b c galois_connection_def isotoneD order_trans)

lemma universal_mapping_property2:
  assumes a: "isotone f" and b: "\<forall>x. f (g x) \<le> x"
  and c: "\<forall>x y. (f x \<le> y) \<longrightarrow> (x \<le> g y)"
  shows "galois_connection f g"
  by (metis a b c galois_connection_def isotoneD order_trans)

lemma galois_ump2: "galois_connection f g = (isotone f \<and> (\<forall>y. f (g y) \<le> y) \<and> (\<forall>x y. f x \<le> y \<longrightarrow> x \<le> g y))"
  by (metis deflation dual_galois_connection_def galois_dual lower_iso universal_mapping_property2)

lemma galois_ump1: "galois_connection f g = (isotone g \<and> (\<forall>x. x \<le> g (f x)) \<and> (\<forall>x y. x \<le> g y \<longrightarrow> f x \<le> y))"
  by (metis galois_connection_def inflation universal_mapping_property1 upper_iso)

(* +------------------------------------------------------------------------+
   | Theorem 4.10(a)                                                        |
   +------------------------------------------------------------------------+ *)

lemma ore_galois:
  assumes"\<forall>x. x \<le> g (f x)" and "\<forall>x. f (g x) \<le> x"
  and "isotone f" and  "isotone g"
  shows "galois_connection f g"
  by (metis assms isotoneD order_trans universal_mapping_property1)

(* +------------------------------------------------------------------------+
   | Theorems 4.32(a) and 4.32(b)                                           |
   +------------------------------------------------------------------------+ *)

lemma perfect1: "galois_connection f g \<Longrightarrow> g (f x) = x \<longleftrightarrow> x \<in> range g"
  by (metis (full_types) image_iff range_eqI semi_inverse2)

lemma perfect2: "galois_connection f g \<Longrightarrow> f (g x) = x \<longleftrightarrow> x \<in> range f"
  by (metis (full_types) image_iff range_eqI semi_inverse1)

(* +------------------------------------------------------------------------+
   | Theorems 4.20(a) and 4.20(b)                                           |
   +------------------------------------------------------------------------+ *)

definition is_max :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_max x X \<equiv> x \<in> X \<and> is_lub x X"

definition is_min :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_min x X \<equiv> x \<in> X \<and> is_glb x X"

lemma galois_max: assumes conn: "galois_connection f g" shows "is_max (g y) {x. f x \<le> y}"
  by (simp add: is_max_def is_lub_equiv, metis assms galois_ump2 order_trans)

lemma galois_min: assumes conn: "galois_connection f g" shows "is_min (f x) {y. x \<le> g y}"
  by (simp add: is_min_def is_glb_equiv, metis assms galois_ump1 order_trans)

theorem max_galois: "galois_connection f g = (isotone f \<and> (\<forall>y. is_max (g y) {x. f x \<le> y}))"
proof
  assume conn: "galois_connection f g"
  show "isotone f \<and> (\<forall>y. is_max (g y) {x. f x \<le> y})"
  proof
    show "isotone f" by (metis conn lower_iso)
  next
    show "\<forall>y. is_max (g y) {x. f x \<le> y}" by (metis conn galois_max)
  qed
next
  assume "isotone f \<and> (\<forall>y. is_max (g y) {x. f x \<le> y})"
  hence fmon: "isotone f" and max: "\<forall>y. is_max (g y) {x. f x \<le> y}" by auto+
  show "galois_connection f g"
  proof (rule universal_mapping_property2)
    show "isotone f" by (metis fmon)
  next
    have max2: "\<forall>y. g y \<in> {x. f x \<le> y}" by (smt is_max_def max)
    hence "(g y \<in> {x. f x \<le> y}) = (f (g y) \<le> y)" by (simp only: mem_Collect_eq)
    thus p: "\<forall>y. f (g y) \<le> y" using max2 by auto
  next
    show "\<forall>x y. f x \<le> y \<longrightarrow> x \<le> g y"
    proof clarify
      fix x and y
      have lub1: "is_lub (g y) {x. f x \<le> y}"
        by (smt is_max_def max mem_Collect_eq is_lub_equiv)
      assume "f x \<le> y"
      thus "x \<le> g y" by (metis lub1 mem_Collect_eq is_lub_equiv order_refl)
    qed
  qed
qed

corollary max_galois_rule: "\<lbrakk>isotone f; \<forall>y. is_max (g y) {x. f x \<le> y}\<rbrakk> \<Longrightarrow> galois_connection f g"
  by (metis max_galois)

theorem min_galois: "galois_connection f g = (isotone g \<and> (\<forall>x. is_min (f x) {y. x \<le> g y}))"
proof
  assume conn: "galois_connection f g"
  show "isotone g \<and> (\<forall>x. is_min (f x) {y. x \<le> g y})"
  proof
    show "isotone g" by (metis conn upper_iso)
  next
    show "\<forall>x. is_min (f x) {y. x \<le> g y}" by (metis conn galois_min)
  qed
next
  assume "isotone g \<and> (\<forall>x. is_min (f x) {y. x \<le> g y})"
  hence gmon: "isotone g" and min: "\<forall>x. is_min (f x) {y. x \<le> g y}" by auto+
  show "galois_connection f g"
  proof (rule universal_mapping_property1)
    show "isotone g" by (metis gmon)
  next
    have "\<forall>x. f x \<in> {y. x \<le> g y}" by (smt is_min_def min)
    moreover have "(f x \<in> {y. x \<le> g y}) = (x \<le> g (f x))" by (simp only: mem_Collect_eq)
    ultimately show "\<forall>x. x \<le> g (f x)" by auto
  next
    show "\<forall>x y. x \<le> g y \<longrightarrow> f x \<le> y"
    proof clarify
      fix x and y
      have glb1: "is_glb (f x) {y. x \<le> g y}" using is_min_def min
        by (smt mem_Collect_eq is_glb_equiv)
      assume "x \<le> g y"
      thus "f x \<le> y" by (metis glb1 mem_Collect_eq is_glb_equiv order_refl)
    qed
  qed
qed

corollary min_galois_rule: "\<lbrakk>isotone g; \<forall>x. is_min (f x) {y. x \<le> g y}\<rbrakk> \<Longrightarrow> galois_connection f g"
  by (metis min_galois)

(* Corollary 4.21 *)

lemma galois_lub: "galois_connection f g \<Longrightarrow> is_lub (g y) {x. f x \<le> y}"
  by (metis galois_max is_max_def)

lemma galois_glb: "galois_connection f g \<Longrightarrow> is_glb (f x) {y. x \<le> g y}"
  by (metis galois_min is_min_def)

lemma galois_lub_var: "galois_connection f g \<Longrightarrow> g y = \<Sigma> {x. f x \<le> y}"
  by (metis galois_lub lub_is_lub)

lemma galois_glb_var: "galois_connection f g \<Longrightarrow> f x = \<Pi> {y. x \<le> g y}"
  by (metis galois_glb glb_is_glb)

(* +------------------------------------------------------------------------+
   | Lemma 4.24(a) and 4.24(b)                                              |
   +------------------------------------------------------------------------+ *)

lemma lower_lub: "\<lbrakk>is_lub x X; lower_adjoint f\<rbrakk> \<Longrightarrow> is_lub (f x) (f ` X)"
  by (smt galois_ump1 galois_ump2 image_iff is_lub_equiv lower_adjoint_def)

lemma upper_glb: "\<lbrakk>is_glb x X; upper_adjoint g\<rbrakk> \<Longrightarrow> is_glb (g x) (g ` X)"
  apply (simp add: is_glb_def upper_adjoint_def is_lb_def galois_connection_def)
  by (metis order_refl order_trans)

lemma lower_preserves_joins: assumes lower: "lower_adjoint f" shows "ex_join_preserving f"
  by (metis assms ex_join_preserving_def lower_lub lub_is_lub)

lemma upper_preserves_meets: assumes upper: "upper_adjoint g" shows "ex_meet_preserving g"
  by (metis assms ex_meet_preserving_def upper_glb glb_is_glb)

end

(* +------------------------------------------------------------------------+
   | Theorems 4.25(a) and 4.25(b)                                           |
   +------------------------------------------------------------------------+ *)

context complete_lattice
begin

theorem suprema_galois: "galois_connection f g = (ex_join_preserving f \<and> (\<forall>y. is_lub (g y) {x. f x \<le> y}))"
proof
  assume "galois_connection f g"
  thus "ex_join_preserving f \<and> (\<forall>y. is_lub (g y) {x. f x \<le> y})"
    by (metis galois_lub lower_adjoint_def lower_preserves_joins)
next
  assume assms: "ex_join_preserving f \<and> (\<forall>y. is_lub (g y) {x. f x \<le> y})"
  hence elj: "ex_join_preserving f" and a2: "\<forall>y. is_lub (g y) {x. f x \<le> y}" by metis+
  hence fmon: "isotone f" by (metis ex_join_preserving_iso)
  thus "galois_connection f g"
  proof (simp add: galois_connection_def)
    have left: "\<forall>x y. (f x \<le> y) \<longrightarrow> (x \<le> g y)"
      by (metis mem_Collect_eq a2 is_lub_equiv order_refl)
    moreover have "\<forall>x y. (x \<le> g y) \<longrightarrow> (f x \<le> y)"
    proof clarify
      fix x and y
      assume gr: "x \<le> g y"
      show "f x \<le> y"
      proof -
        have lem: "\<Sigma> (f ` {x. f x \<le> y}) \<le> y"
        proof (rule the_lub_leq)
          show "\<exists>z. is_lub z (f ` {x\<Colon>'a. f x \<le> y})" by (metis lub_ex)
        next
          fix z
          show "is_lub z (f ` {x\<Colon>'a. f x \<le> y}) \<longrightarrow> z \<le> y"
            by (smt mem_Collect_eq imageE is_lub_equiv)
        qed

        have "f x \<le> y \<Longrightarrow> x \<le> \<Sigma> {z. f z \<le> y}" by (metis a2 gr lub_is_lub)
        moreover have "x \<le> \<Sigma> {z. f z \<le> y} \<Longrightarrow> f x \<le> f (\<Sigma> {z. f z \<le> y})" by (metis fmon isotoneD)
        moreover have "(f x \<le> f (\<Sigma> {z. f z \<le> y})) = (f x \<le> \<Sigma> (f ` {z. f z \<le> y}))"
          by (metis a2 elj ex_join_preserving_def top_greatest)
        moreover have "... \<Longrightarrow> f x \<le> y" using lem by (metis order_trans)
        ultimately show ?thesis by (metis a2 gr lub_is_lub)
      qed
    qed
    ultimately show "\<forall>x y. (f x \<le> y) = (x \<le> g y)" by auto
  qed
qed

corollary suprema_galois_rule:
  "\<lbrakk>ex_join_preserving f; \<forall>y. is_lub (g y) {x. f x \<le> y}\<rbrakk> \<Longrightarrow> galois_connection f g"
  by (metis suprema_galois)

theorem infima_galois: "galois_connection f g = (ex_meet_preserving g \<and> (\<forall>x. is_glb (f x) {y. x \<le> g y}))"
proof
  assume "galois_connection f g"
  thus "ex_meet_preserving g \<and> (\<forall>x. is_glb (f x) {y. x \<le> g y})"
    by (metis galois_glb upper_adjoint_def upper_preserves_meets)
next
  assume assms: "ex_meet_preserving g \<and> (\<forall>x. is_glb (f x) {y. x \<le> g y})"
  hence elj: "ex_meet_preserving g" and a2: "\<forall>x. is_glb (f x) {y. x \<le> g y}"  by auto+
  hence gmon: "isotone g" by (metis ex_meet_preserving_iso)
  thus "galois_connection f g"
  proof (simp add: galois_connection_def)
    have right: "\<forall>x y. (x \<le> g y) \<longrightarrow> (f x \<le> y)"
      by (metis mem_Collect_eq a2 is_glb_equiv order_refl)
    moreover have "\<forall>x y. (f x \<le> y) \<longrightarrow> (x \<le> g y)"
    proof clarify
      fix x and y
      assume gr: "f x \<le> y"
      show "x \<le> g y"
      proof -
        have lem: "x \<le> \<Pi> (g ` {y. x \<le> g y})"
        proof (rule the_glb_leq)
          show "\<exists>z. is_glb z (g ` {y. x \<le> g y})" by (metis glb_ex)
        next
          fix z
          show "is_glb z (g ` {y. x \<le> g y}) \<longrightarrow> x \<le> z"
            by (smt mem_Collect_eq imageE is_glb_equiv)
        qed

        have "x \<le> g y \<Longrightarrow> \<Pi> {z. x \<le> g z} \<le> y" by (metis a2 gr glb_is_glb)
        moreover have "\<Pi> {z. x \<le> g z} \<le> y \<Longrightarrow> g (\<Pi> {z. x \<le> g z}) \<le> g y" by (metis gmon isotoneD)
        moreover have "(g (\<Pi> {z. x \<le> g z}) \<le> g y) = (\<Pi> (g ` {z. x \<le> g z}) \<le> g y)"
          by (metis a2 elj ex_meet_preserving_def top_greatest)
        moreover have "... \<Longrightarrow> x \<le> g y" using lem by (metis order_trans)
        ultimately show ?thesis by (metis a2 gr glb_is_glb)
      qed
    qed
    ultimately show "\<forall>x y. (f x \<le> y) = (x \<le> g y)" by auto
  qed
qed

corollary infima_galois_rule:
  "\<lbrakk>ex_meet_preserving g; \<forall>x. is_glb (f x) {y. x \<le> g y}\<rbrakk> \<Longrightarrow> galois_connection f g"
  by (metis infima_galois)

(* +------------------------------------------------------------------------+
   | Theorems 4.26 and 4.27                                                 |
   +------------------------------------------------------------------------+ *)

theorem cl_lower_join_preserving: "lower_adjoint f = ex_join_preserving f"
proof
  assume "lower_adjoint f" thus "ex_join_preserving f"
    by (metis lower_adjoint_def lower_iso lower_preserves_joins)
next
  assume ejp: "ex_join_preserving f"
  have "\<exists>g. \<forall>y. is_lub (g y) {x. f x \<le> y}"
  proof
    show "\<forall>y. is_lub (\<Sigma> {x. f x \<le> y}) {x. f x \<le> y}" by (metis lub_ex lub_is_lub)
  qed
  thus "lower_adjoint f" by (metis lower_adjoint_def ejp suprema_galois)
qed

theorem cl_upper_join_preserving: "upper_adjoint g = ex_meet_preserving g"
proof
  assume "upper_adjoint g" thus "ex_meet_preserving g"
    by (metis upper_preserves_meets)
next
  assume emp: "ex_meet_preserving g"
  have "\<exists>f. \<forall>x. is_glb (f x) {y. x \<le> g y}"
  proof
    show "\<forall>x. is_glb (\<Pi> {y. x \<le> g y}) {y. x \<le> g y}" by (metis glb_ex glb_is_glb)
  qed
  thus "upper_adjoint g" by (metis emp infima_galois upper_adjoint_def)
qed

lemma join_preserving_is_ex: "join_preserving f \<Longrightarrow> ex_join_preserving f"
  by (metis ex_join_preserving_def join_preserving_def)

lemma join_pres2: "ex_join_preserving f = join_preserving f"
  by (metis lub_ex ex_join_preserving_def subset_UNIV join_preserving_def)

lemma meet_preserving_is_ex: "meet_preserving f = ex_meet_preserving f"
  by (metis glb_ex ex_meet_preserving_def subset_UNIV meet_preserving_def)

lemma galois_join_preserving: "galois_connection f g \<Longrightarrow> join_preserving f"
  by (metis ex_join_preserving_def lub_ex subset_UNIV suprema_galois join_preserving_def)

lemma galois_meet_preserving: "galois_connection f g \<Longrightarrow> meet_preserving g"
  by (metis ex_meet_preserving_def glb_ex subset_UNIV infima_galois meet_preserving_def)

(* +------------------------------------------------------------------------+
   | Theorems 4.36 and 4.37                                                 |
   +------------------------------------------------------------------------+ *)

theorem upper_exists: "lower_adjoint f = join_preserving f"
  by (metis lower_adjoint_def cl_lower_join_preserving galois_join_preserving join_preserving_is_ex)

theorem lower_exists: "upper_adjoint g = meet_preserving g"
  by (metis cl_upper_join_preserving meet_preserving_is_ex)

(* +------------------------------------------------------------------------+
   | Fixpoints and Galois connections                                       |
   +------------------------------------------------------------------------+ *)

lemma fixpoint_rolling: assumes conn: "galois_connection f g"
  shows "f (\<mu> (g \<circ> f)) = \<mu> (f \<circ> g)"
proof
  show "(f \<circ> g) (f (\<mu> (g \<circ> f))) = f (\<mu> (g \<circ> f))"
    by (metis assms o_def semi_inverse1)
next
  fix y assume fgy: "(f \<circ> g) y = y"
  have "\<mu> (g \<circ> f) \<le> g y"
    by (metis assms dual.order_refl fgy fixpoint_induction galois_isotone1 o_eq_dest_lhs)
  thus "f (\<mu> (g \<circ> f)) \<le> y" by (metis conn galois_connection_def)
qed

lemma greatest_fixpoint_rolling: assumes conn: "galois_connection f g"
  shows "g (\<nu> (f \<circ> g)) = \<nu> (g \<circ> f)"
proof
  show "(g \<circ> f) (g (\<nu> (f \<circ> g))) = g (\<nu> (f \<circ> g))" by (metis assms o_def semi_inverse2)
next
  fix y assume gfy: "(g \<circ> f) y = y"
  have "f y \<le> \<nu> (f \<circ> g)"
by (metis assms dual.order_refl galois_isotone2 gfy greatest_fixpoint_induction o_eq_dest_lhs)
  thus "y \<le> g (\<nu> (f \<circ> g))" by (metis conn galois_connection_def)
qed

(* +------------------------------------------------------------------------+
   | Fixpoint Fusion                                                        |
   +------------------------------------------------------------------------+ *)

(* uses lfp_equality_var then fixpoint_induction *)

theorem fixpoint_fusion [simp]:
  assumes upper_ex: "lower_adjoint f"
  and hiso: "isotone h" and kiso: "isotone k"
  and comm: "f\<circ>h = k\<circ>f"
  shows "f (\<mu> h) = \<mu> k"
proof
  show "k (f (\<mu> h)) = f (\<mu> h)" by (metis comm fixpoint_computation hiso o_def)
next
  fix y assume ky: "k y = y"
  obtain g where conn: "galois_connection f g" by (metis lower_adjoint_def upper_ex)
  have "\<mu> h \<le> g y" using hiso
  proof (rule fixpoint_induction)
    have "f (g y) \<le> y" by (metis conn deflation)
    hence "f (h (g y)) \<le> y" by (metis comm kiso ky isotoneD o_def)
    thus "h (g y) \<le> g y" by (metis conn galois_connection_def)
  qed
  thus "f (\<mu> h) \<le> y" by (metis conn galois_connection_def)
qed

theorem greatest_fixpoint_fusion [simp]:
  assumes lower_ex: "upper_adjoint g"
  and hiso: "isotone h" and kiso: "isotone k"
  and comm: "g\<circ>h = k\<circ>g"
  shows "g (\<nu> h) = \<nu> k"
proof
  show "k (g (\<nu> h)) = g (\<nu> h)" by (metis comm greatest_fixpoint_computation hiso o_def)
next
  fix y assume ky: "k y = y"
  obtain f where conn: "galois_connection f g" by (metis lower_ex upper_adjoint_def)
  have "f y \<le> \<nu> h" using hiso
  proof (rule greatest_fixpoint_induction)
    have "y \<le> g (f y)" by (metis conn inflation)
    hence "y \<le> g (h (f y))" by (metis comm kiso ky isotoneD o_def)
    thus "f y \<le> h (f y)" by (metis conn galois_connection_def)
  qed
  thus "y \<le> g (\<nu> h)" by (metis conn galois_connection_def)
qed

end

(* +------------------------------------------------------------------------+
   | Join semilattices with zero                              |
   +------------------------------------------------------------------------+ *)

class join_semilattice_zero = join_semilattice + zero +
  assumes join_zerol: "0 \<squnion> x = x"

begin

  lemma join_iso: "x \<le> y \<longrightarrow> x\<squnion>z \<le> y\<squnion>z"
    by (smt join_assoc join_comm join_idem leq_def_join)

  lemma join_ub: "x \<le> x\<squnion>y"
    by (metis join_assoc join_idem leq_def_join)

  lemma join_lub: "x\<squnion>y \<le> z \<longleftrightarrow> x \<le> z \<and> y \<le> z"
    by (metis join_comm join_iso join_ub leq_def_join)

  lemma min_zero: "0 \<le> x"
    by (metis join_zerol leq_def_join)

  lemma lub_un: "is_lub w A \<Longrightarrow> is_lub (x\<squnion>w) ({x}\<union>A)"
    by (simp add: is_lub_equiv join_lub)

end

end
