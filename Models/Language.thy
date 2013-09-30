theory Language
  imports "$AFP/Kleene_Algebra/Kleene_Algebra" LazySumList Fixpoint Omega_Algebra
begin

section {* Potentially infinite languages with shuffle product *}

notation lappend (infixl "\<frown>" 75)

type_synonym 'a lan = "'a llist set"

subsection {* Language product *}

no_notation Groups.times_class.times (infixl "\<cdot>" 70)

definition l_prod :: "'a lan \<Rightarrow> 'a lan \<Rightarrow> 'a lan" (infixl "\<cdot>" 80) where
  "l_prod X Y = {xs \<frown> ys|xs ys. xs \<in> X \<and> lfinite xs \<and> ys \<in> Y} \<union> {xs. xs \<in> X \<and> \<not> lfinite xs}"

lemma l_prod_def_var: "X \<cdot> Y = {xs \<frown> ys|xs ys. xs \<in> X \<and> ys \<in> Y} \<union> {xs. xs \<in> X \<and> \<not> lfinite xs}"
  by (auto simp add: l_prod_def) (metis lappend_inf)

lemma l_prod_assoc: "(X \<cdot> Y) \<cdot> Z = X \<cdot> (Y \<cdot> Z)"
  apply (simp add: l_prod_def)
  apply safe
  by (metis lappend_assoc lfinite_lappend)+

lemma l_prod_isol: "X \<subseteq> Y \<Longrightarrow> X \<cdot> Z \<subseteq> Y \<cdot> Z"
  by (auto simp add: l_prod_def)

lemma l_prod_isor: "X \<subseteq> Y \<Longrightarrow> Z \<cdot> X \<subseteq> Z \<cdot> Y"
  by (auto simp add: l_prod_def)

lemma l_prod_one [simp]: shows "{LNil} \<cdot> X = X" and "X \<cdot> {LNil} = X"
  by (auto simp add: l_prod_def)

lemma l_prod_inf_distr: "\<Union>\<XX> \<cdot> Y = \<Union>{X \<cdot> Y|X. X \<in> \<XX>}"
  by (auto simp add: l_prod_def)

lemma l_prod_distr [simp]: "(X \<union> Y) \<cdot> Z = X \<cdot> Z \<union> Y \<cdot> Z"
  by (insert l_prod_inf_distr[of "{X, Y}" Z]) auto

lemma l_prod_distl [simp]: "X \<cdot> (Y \<union> Z) = X \<cdot> Y \<union> X \<cdot> Z"
  by (auto simp add: l_prod_def)

lemma l_prod_zero [simp]: shows "{} \<cdot> X = {}"
  by (simp add: l_prod_def)

subsection {* Shuffling words *}

text {* The \sha\ operator generates a language by shuffling two words together. *}

definition tshuffle_words :: "'a llist \<Rightarrow> 'b llist \<Rightarrow> ('a + 'b) lan" (infix "\<sha>" 75) where
  "tshuffle_words xs ys = {zs. lefts zs = xs \<and> rights zs = ys}"

text {* The resulting language contains strings where each symbol is labelled by either @{term Inl} or @{term Inr},
depending on which input it came from. This means that @{prop "\<forall>zs \<in> (xs \<sha> ys). \<ll> zs = xs \<and> \<rr> zs = ys"}.
If a function @{term f} has type @{typ "'a \<Rightarrow> 'c"} and @{term g} has type @{typ "'b \<Rightarrow> 'c"}, then the sum elimination function @{term "\<langle>f,g\<rangle>"}
can be used to eliminate values of @{typ "('a,'b) sum"} by transforming them to values of type @{typ "'c"}.
The function @{term "\<langle>id,id\<rangle>"} is therefore often used when both components of the sum have the same type. *}

text {* When both words are infinite, this definition results in a fair shuffle. *}

lemma lfinite_lfilter_prop: "P (lnth zs n) \<Longrightarrow> \<forall>m>n. \<not> P (lnth zs m) \<Longrightarrow> lfinite (lfilter P zs)"
  apply (simp add: lfinite_lfilter)
  apply (intro disjI2)
  by (metis finite_Int infinite_nat_iff_unbounded mem_Collect_eq)

lemma shuffle_fair: "\<not> lfinite xs \<Longrightarrow> \<not> lfinite ys \<Longrightarrow> zs \<in> xs \<sha> ys \<Longrightarrow> fair zs"
  apply (auto simp add: tshuffle_words_def fair_def rights_def lefts_def)
  apply (metis infinite_lfilter)
  apply (metis infinite_lfilter)
  apply (rule ccontr)
  apply simp
  apply (subgoal_tac "lfinite (lfilter is_right zs)")
  apply simp
  apply (metis lfinite_lfilter_prop not_is_right)
  apply (rule ccontr)
  apply simp
  apply (subgoal_tac "lfinite (lfilter is_left zs)")
  apply simp
  by (metis (full_types) lfinite_lfilter_prop not_is_right)

lemma tshuffle_words_comm: "lmap \<langle>id,id\<rangle> ` (x \<sha> y) = lmap \<langle>id,id\<rangle> ` (y \<sha> x)"
  by (auto simp add: tshuffle_words_def image_def) (rule_tac x = "lmap swap xa" in exI, simp)+

lemma tshuffle_words_assoc:
  "lmap \<langle>id,\<langle>id,id\<rangle>\<rangle> ` {ws. \<ll> ws = xs \<and> \<ll> (\<rr> ws) = ys \<and> \<rr> (\<rr> ws) = zs} = lmap \<langle>\<langle>id,id\<rangle>,id\<rangle> ` {ws. \<ll> (\<ll> ws) = xs \<and> \<rr> (\<ll> ws) = ys \<and> \<rr> ws = zs}"
  apply (auto simp add: image_def)
  apply (rule_tac x = "lmap rbr1 xa" in exI)
  apply simp
  defer
  apply (rule_tac x = "lmap rbr2 xa" in exI)
  apply simp
  by (simp add: lmap_compose[symmetric] o_def del: lmap_compose)+

subsection {* Typed shuffle product *}

definition tshuffle :: "'a lan \<Rightarrow> 'b lan \<Rightarrow> ('a + 'b) lan" (infixl "\<Sha>" 75) where
  "X \<Sha> Y \<equiv> \<Union>{x \<sha> y|x y. x \<in> X \<and> y \<in> Y}"

lemma tshuffle_lr: "xs \<in> X \<Sha> Y \<longleftrightarrow> \<ll> xs \<in> X \<and> \<rr> xs \<in> Y"
  by (auto simp add: tshuffle_def tshuffle_words_def)

lemma tshuffle_comm: "lmap \<langle>id,id\<rangle> ` (X \<Sha> Y) = lmap \<langle>id,id\<rangle> ` (Y \<Sha> X)"
proof -
  have "lmap \<langle>id,id\<rangle> ` (X \<Sha> Y) = \<Union>{lmap \<langle>id,id\<rangle> ` (x \<sha> y)|x y. x \<in> X \<and> y \<in> Y}"
    by (auto simp add: tshuffle_def)
  also have "... = \<Union>{lmap \<langle>id,id\<rangle> ` (y \<sha> x)|x y. x \<in> X \<and> y \<in> Y}"
    by (simp add: tshuffle_words_comm)
  also have "... = lmap \<langle>id,id\<rangle> ` (Y \<Sha> X)"
    by (auto simp add: tshuffle_def)
  finally show ?thesis .
qed

lemma tshuffle3_right:
  "X \<Sha> (Y \<Sha> Z) = \<Union>{{w. \<ll> w = x \<and> \<ll> (\<rr> w) = y \<and> \<rr> (\<rr> w) = z}|x y z. x \<in> X \<and> y \<in> Y \<and> z \<in> Z}"
  by (simp only: tshuffle_def tshuffle_words_def) blast

lemma tshuffle3_left:
  "(X \<Sha> Y) \<Sha> Z = \<Union>{{w. \<ll> (\<ll> w) = x \<and> \<rr> (\<ll> w) = y \<and> \<rr> w = z}|x y z. x \<in> X \<and> y \<in> Y \<and> z \<in> Z}"
 by (simp only: tshuffle_def tshuffle_words_def) blast

lemma tshuffle_assoc: "lmap \<langle>\<langle>id,id\<rangle>,id\<rangle> ` ((X \<Sha> Y) \<Sha> Z) = lmap \<langle>id,\<langle>id,id\<rangle>\<rangle> ` (X \<Sha> (Y \<Sha> Z))"
proof -
  have "lmap \<langle>\<langle>id,id\<rangle>,id\<rangle> ` ((X \<Sha> Y) \<Sha> Z) = lmap \<langle>\<langle>id,id\<rangle>,id\<rangle> ` \<Union>{{w. \<ll> (\<ll> w) = x \<and> \<rr> (\<ll> w) = y \<and> \<rr> w = z}|x y z. x \<in> X \<and> y \<in> Y \<and> z \<in> Z}"
    by (simp add: tshuffle3_left)
  also have "... = \<Union>{lmap \<langle>\<langle>id,id\<rangle>,id\<rangle> ` {w. \<ll> (\<ll> w) = x \<and> \<rr> (\<ll> w) = y \<and> \<rr> w = z}|x y z. x \<in> X \<and> y \<in> Y \<and> z \<in> Z}"
    by (auto simp add: image_def)
  also have "... = \<Union>{lmap \<langle>id,\<langle>id,id\<rangle>\<rangle> ` {w. \<ll> w = x \<and> \<ll> (\<rr> w) = y \<and> \<rr> (\<rr> w) = z}|x y z. x \<in> X \<and> y \<in> Y \<and> z \<in> Z}"
    by (simp add: tshuffle_words_assoc)
  also have "... = lmap \<langle>id,\<langle>id,id\<rangle>\<rangle> ` \<Union>{{w. \<ll> w = x \<and> \<ll> (\<rr> w) = y \<and> \<rr> (\<rr> w) = z}|x y z. x \<in> X \<and> y \<in> Y \<and> z \<in> Z}"
    by (auto simp add: image_def)
  also have "... = lmap \<langle>id,\<langle>id,id\<rangle>\<rangle> ` (X \<Sha> (Y \<Sha> Z))"
    by (simp add: tshuffle3_right)
  finally show ?thesis .
qed

subsection {* Shuffle product *}

no_notation Sublist.parallel (infixl "\<parallel>" 50)

definition shuffle :: "'a lan \<Rightarrow> 'a lan \<Rightarrow> 'a lan" (infixl "\<parallel>" 75) where
  "shuffle X Y \<equiv> \<Union>{lmap \<langle>id,id\<rangle> ` (x \<sha> y)|x y. x \<in> X \<and> y \<in> Y}"

lemma shuffle_to_tshuffle: "X \<parallel> Y = lmap \<langle>id,id\<rangle> ` (X \<Sha> Y)"
  by (auto simp add: shuffle_def tshuffle_def image_def)

lemma shuffle_comm: "X \<parallel> Y = Y \<parallel> X"
  by (metis shuffle_to_tshuffle tshuffle_comm)

definition traj :: "('a + 'b) llist \<Rightarrow> (unit + unit) llist" where
  "traj \<equiv> lmap \<langle>(\<lambda>x. Inl ()), (\<lambda>x. Inr ())\<rangle>"

text {* The @{term traj} function takes an @{typ "('a + 'b) llist"} and returns a lazy list which contains either @{term "Inl ()"} or
@{term "Inr ()"} if the original list contained @{term Inl} and @{term Inr} anything respectively. *} 

lemma [simp]: "(case x of () \<Rightarrow> y) = y"
  by (metis (full_types) unit.cases unit.exhaust)

definition interleave :: "(unit + unit) llist \<Rightarrow> 'a llist \<Rightarrow> 'b llist \<Rightarrow> ('a + 'b) llist" where
  "interleave t l r \<equiv> llist_corec (t, l, r)
                        (\<lambda>(t, l, r). llist_case None
                          (\<lambda>t ts. Some (case t of (Inl ()) \<Rightarrow> (Inl (lhd l), (ts, ltl l, r))
                                                | (Inr ()) \<Rightarrow> (Inr (lhd r), (ts, l, ltl r)))) t)"

text {* The @{term interleave} function takes a trajectory (as returned by @{term traj}) and combines two lists by picking elements according
to the trajectory. *}

abbreviation interleave' ("_ \<triangleright> _ \<triangleleft> _" [55,55,55] 55) where "xs \<triangleright> t \<triangleleft> ys \<equiv> interleave t xs ys"

lemma interleave_LCons [simp]: "\<ll> (LCons z zs) \<triangleright> traj (LCons z zs) \<triangleleft> \<rr> (LCons z zs) = LCons z (\<ll> zs \<triangleright> traj zs \<triangleleft> \<rr> zs)"
  by (cases z, simp) (subst interleave_def, subst llist_corec, simp add: traj_def interleave_def[symmetric])+

lemma reinterleave: "\<ll> zs \<triangleright> traj zs \<triangleleft> \<rr> zs = zs"
proof (coinduct zs rule: llist_fun_equalityI)
  case LNil show ?case
    by (simp add: interleave_def traj_def llist_corec)
next
  case (LCons z zs)
  have ?EqLCons
  proof (intro exI conjI)
    show "(\<ll> (LCons z zs) \<triangleright> traj (LCons z zs) \<triangleleft> \<rr> (LCons z zs), LCons z zs) = (LCons z (\<ll> zs \<triangleright> traj zs \<triangleleft> \<rr> zs), LCons z zs)"
      by simp
    have "(\<ll> zs \<triangleright> traj zs \<triangleleft> \<rr> zs, zs) \<in> {(\<ll> u \<triangleright> traj u \<triangleleft> \<rr> u, u) |u. True}"
      by auto
    thus "(\<ll> zs \<triangleright> traj zs \<triangleleft> \<rr> zs, zs) \<in> {(\<ll> u \<triangleright> traj u \<triangleleft> \<rr> u, u) |u. True} \<or> \<ll> zs \<triangleright> traj zs \<triangleleft> \<rr> zs = zs"
      by blast
  qed simp
  thus ?case
    by auto
qed

text {* Two values of type @{typ "('a + 'b) llist"} are equal if they have the same left values, right values, and trajectory *}

lemma traj_equality: "traj xs = traj ys \<Longrightarrow> \<ll> xs = \<ll> ys \<Longrightarrow> \<rr> xs = \<rr> ys \<Longrightarrow> xs = ys"
  by (metis reinterleave)

lemma traj_LNil [simp]: "xs \<triangleright> LNil \<triangleleft> ys = LNil"
  by (simp add: interleave_def llist_corec)

lemma interleave_only_left: "interleave (lmap (\<lambda>x. Inl ()) xs) xs ys = lmap Inl xs"
proof (coinduct xs rule: llist_fun_equalityI)
  case LNil show ?case by simp
next
  case (LCons x xs)
  have ?EqLCons
  proof (intro exI conjI)
    show "(interleave (lmap (\<lambda>x. Inl ()) (LCons x xs)) (LCons x xs) ys, lmap Inl (LCons x xs))
        = (LCons (Inl x) (interleave (lmap (\<lambda>x. Inl ()) xs) xs ys), LCons (Inl x) (lmap Inl xs))"
      by (subst interleave_def, subst llist_corec, simp add: interleave_def[symmetric])
    show "(interleave (lmap (\<lambda>x. Inl ()) xs) xs ys, lmap Inl xs) \<in> {(interleave (lmap (\<lambda>x. Inl ()) u) u ys, lmap Inl u) |u. True}
        \<or> interleave (lmap (\<lambda>x. Inl ()) xs) xs ys = lmap Inl xs"
      by auto
  qed simp
  thus ?case by auto
qed

lemma interleave_only_right: "interleave (lmap (\<lambda>x. Inr ()) ys) xs ys = lmap Inr ys"
proof (coinduct ys rule: llist_fun_equalityI)
  case LNil show ?case by simp
next
  case (LCons y ys)
  have ?EqLCons
  proof (intro exI conjI)
    show "(interleave (lmap (\<lambda>x. Inr ()) (LCons y ys)) xs (LCons y ys), lmap Inr (LCons y ys))
        = (LCons (Inr y) (interleave (lmap (\<lambda>x. Inr ()) ys) xs ys), LCons (Inr y) (lmap Inr ys))"
      by (subst interleave_def, subst llist_corec, simp add: interleave_def[symmetric])
    show "(interleave (lmap (\<lambda>x. Inr ()) ys) xs ys, lmap Inr ys) \<in> {(interleave (lmap (\<lambda>x. Inr ()) u) xs u, lmap Inr u)|u. True}
        \<or> interleave (lmap (\<lambda>x. Inr ()) ys) xs ys = lmap Inr ys"
      by auto
  qed simp
  thus ?case by auto
qed

inductive_set ltls :: "'a llist \<Rightarrow> 'a llist set" for xs :: "'a llist" where
  "xs \<in> ltls xs"
| "xs' \<in> ltls xs \<Longrightarrow> ltl xs' \<in> ltls xs"

lemma sum_list_cases: "\<lbrakk>ys = LNil \<Longrightarrow> P ys; \<And>x xs. ys = LCons (Inl x) xs \<Longrightarrow> P ys; \<And>x xs. ys = LCons (Inr x) xs \<Longrightarrow> P ys\<rbrakk> \<Longrightarrow> P ys"
  apply (cases ys)
  apply auto
  by (metis sumE)

lemma lfinite_induct [consumes 1, case_names Nil Cons]:
  assumes fin: "lfinite xs"
  and Nil: "P LNil"
  and Cons: "\<And>x xs. \<lbrakk>lfinite xs; P xs\<rbrakk> \<Longrightarrow> P (LCons x xs)"
  shows "P xs"
proof -
  from fin obtain xs' where xs: "xs = llist_of xs'"
    unfolding lfinite_eq_range_llist_of by blast
  show ?thesis unfolding xs
    by (induct xs') (auto simp add: Nil Cons)
qed

lemma helper1: "lfinite ys \<Longrightarrow> xs' \<triangleright> ltakeWhile is_right t \<triangleleft> ys' = ys \<frown> LCons x zs \<longrightarrow> is_right x"
proof (induct ys arbitrary: xs' t ys' rule: lfinite_induct)
  case Nil show ?case
  proof (cases t, simp_all)
    fix t :: "unit + unit" and ts :: "(unit + unit) llist"
    have "xs' \<triangleright> LCons (Inr (unr t)) (ltakeWhile is_right ts) \<triangleleft> ys' = LCons x zs \<longrightarrow> is_right x"
        apply (subst interleave_def)
        apply (subst llist_corec)
        apply simp
        apply (subst interleave_def[symmetric])
        by (metis is_right.simps(1))
    thus "is_right t \<longrightarrow> xs' \<triangleright> LCons t (ltakeWhile is_right ts) \<triangleleft> ys' = LCons x zs \<longrightarrow> is_right x"
      by (metis is_left.simps(1) not_is_left sum.exhaust unr.simps(1))
  qed
next
  case (Cons y ys) thus ?case
    apply (cases t)
    apply simp
    apply (simp only: mp)
  proof -
    fix t ts
    assume ys_fin: "lfinite ys"
    and "\<And>t xs' ys'. xs' \<triangleright> ltakeWhile is_right t \<triangleleft> ys' = ys \<frown> LCons x zs \<longrightarrow> is_right x"
    hence ih: "\<And>t xs' ys'. xs' \<triangleright> ltakeWhile is_right t \<triangleleft> ys' = ys \<frown> LCons x zs \<Longrightarrow> is_right x"
      by auto
    show "xs' \<triangleright> ltakeWhile is_right (LCons t ts) \<triangleleft> ys' = LCons y ys \<frown> LCons x zs \<longrightarrow> is_right x"
      apply (cases t)
      apply simp
      apply (subst interleave_def)
      apply (subst llist_corec)
      apply simp
      apply (subst interleave_def[symmetric])
      by (auto intro: ih)
  qed
qed

lemma llist_of_replicate:
  assumes "lfinite xs" and "(\<forall>x\<in>lset xs. x = y)"
  shows "\<exists>n. xs = llist_of (replicate n y)"
proof -
  obtain xs' where "xs = llist_of xs'"
    by (metis assms(1) llist_of_list_of)
  hence "\<forall>x\<in>set xs'. x = y"
    by (metis assms(2) lset_llist_of)
  hence "xs' = replicate (length xs') y"
    by (simp add: map_replicate_const[symmetric]) (metis map_idI)
  thus ?thesis
    by (metis `xs = llist_of xs'`)
qed

lemma lfilter_left_traj1:
  assumes "ldropWhile is_right t \<noteq> LNil"
  shows "lfilter is_left (xs \<triangleright> t \<triangleleft> ys) = lfilter is_left (xs \<triangleright> ldropWhile is_right t \<triangleleft> ldrop (llength (ltakeWhile is_right t)) ys)"
proof -
  have "\<exists>n. ltakeWhile is_right t = llist_of (replicate n (Inr ()))"
    apply (rule llist_of_replicate)
    apply (metis assms(1) lappend_inf lappend_ltakeWhile_ldropWhile ldropWhile_eq_LNil_iff lset_ltakeWhileD)
    by (metis (full_types) is_left.simps(1) lset_ltakeWhileD not_is_right swap.cases unit.exhaust)
  then obtain n where rights: "ltakeWhile is_right t = llist_of (replicate n (Inr ()))" by auto
  hence n_def: "enat n = llength (ltakeWhile is_right t)"
    by (metis length_replicate llength_llist_of)

  have "lfilter is_left (xs \<triangleright> t \<triangleleft> ys) = lfilter is_left (xs \<triangleright> ltakeWhile is_right t \<frown> ldropWhile is_right t \<triangleleft> ys)"
    by (metis lappend_ltakeWhile_ldropWhile)
  also have "... = lfilter is_left (xs \<triangleright> llist_of (replicate n (Inr ())) \<frown> ldropWhile is_right t \<triangleleft> ys)"
    by (simp only: rights)
  also have "... = lfilter is_left (xs \<triangleright> ldropWhile is_right t \<triangleleft> ldrop (enat n) ys)"
  proof (induct n arbitrary: ys)
    case 0 show ?case by simp
  next
    case (Suc n)
    let ?lhs =  "lfilter is_left (xs \<triangleright> llist_of (replicate (Suc n) (Inr ())) \<frown> ldropWhile is_right t \<triangleleft> ys)"
    have "?lhs = lfilter is_left (xs \<triangleright> LCons (Inr ()) (llist_of (replicate n (Inr ())) \<frown> ldropWhile is_right t) \<triangleleft> ys)"
      by simp
    also have "... = lfilter is_left (xs \<triangleright> llist_of (replicate n (Inr ())) \<frown> ldropWhile is_right t \<triangleleft> ltl ys)"
      by (subst interleave_def, subst llist_corec, simp add: interleave_def[symmetric])      
    also have "... = lfilter is_left (xs \<triangleright> ldropWhile is_right t \<triangleleft> ldrop (enat n) (ltl ys))"
      by (simp add: Suc)
    also have "... = lfilter is_left (xs \<triangleright> ldropWhile is_right t \<triangleleft> ldrop (enat (Suc n)) ys)"
      by (metis eSuc_enat ldrop_eSuc_ltl)
    finally show ?case .
  qed
  also have "... = lfilter is_left (xs \<triangleright> ldropWhile is_right t \<triangleleft> ldrop (llength (ltakeWhile is_right t)) ys)"
    by (metis n_def)
  finally show ?thesis .
qed

lemma lfilter_left_traj2:
  assumes "ldropWhile is_right t \<noteq> LNil"
  shows "xs \<triangleright> lfilter is_left t \<triangleleft> ys = xs \<triangleright> lfilter is_left (ldropWhile is_right t) \<triangleleft> ys" (is "?lhs = ?rhs")
proof -
  have lfinite_rights: "lfinite (ltakeWhile is_right t)"
    by (metis assms(1) lappend_inf lappend_ltakeWhile_ldropWhile ldropWhile_eq_LNil_iff lset_ltakeWhileD)

  have "?lhs = xs \<triangleright> lfilter is_left (ltakeWhile is_right t \<frown> ldropWhile is_right t) \<triangleleft> ys"
    by (metis lappend_ltakeWhile_ldropWhile)
  also have "... = xs \<triangleright> lfilter is_left (ltakeWhile is_right t) \<frown> lfilter is_left (ldropWhile is_right t) \<triangleleft> ys"
    by (metis lfilter_lappend_lfinite lfinite_rights)
  also have "... = xs \<triangleright> LNil \<frown> lfilter is_left (ldropWhile is_right t) \<triangleleft> ys"
    by (metis Not_is_left lfilter_ltakeWhile)
  also have "... = xs \<triangleright> lfilter is_left (ldropWhile is_right t) \<triangleleft> ys"
    by simp
  finally show ?thesis .
qed

lemma ldropWhile_rights_not_LNil:
  fixes t :: "(unit + unit) llist"
  assumes "ldropWhile is_right t \<noteq> LNil"
  shows "ldropWhile is_right t = LCons (Inl ()) (ltl (ldropWhile is_right t))" (is "?lhs = ?rhs")
proof -
  have "?lhs = LCons (lhd (ldropWhile is_right t)) (ltl (ldropWhile is_right t))"
    by (metis assms lhd_LCons_ltl)
  also have "... = ?rhs"
    by (rule arg_cong) (metis (hide_lams, mono_tags) assms is_right.simps(1) lhd_ldropWhile sum.exhaust unit.exhaust)
  finally show ?thesis .
qed

lemma only_left_traj: "xs \<triangleright> lfilter is_left t \<triangleleft> ys = xs \<triangleright> lfilter is_left t \<triangleleft> ys'"
proof -
  have "(xs \<triangleright> lfilter is_left t \<triangleleft> ys, xs \<triangleright> lfilter is_left t \<triangleleft> ys')
      \<in> {(xs' \<triangleright> lfilter is_left t \<triangleleft> ys, xs' \<triangleright> lfilter is_left t \<triangleleft> ys')|xs' t ys ys'. xs' \<in> ltls xs}"
    by auto (metis ltls.intros(1))
  thus ?thesis
  proof (coinduct rule: llist_equalityI)
    case (Eqllist q) note q = this[simplified]
    then obtain t xs' ys ys' where q_def: "q = (xs' \<triangleright> lfilter is_left t \<triangleleft> ys, xs' \<triangleright> lfilter is_left t \<triangleleft> ys')"
    and xs_tl: "xs' \<in> ltls xs"
      by auto
    {
      assume all_right: "ldropWhile is_right t = LNil"
      have ?EqLNil
      proof (auto simp add: q_def)
        show "xs' \<triangleright> lfilter is_left t \<triangleleft> ys = LNil"
          apply (subst lappend_ltakeWhile_ldropWhile[symmetric, of t is_right])
          apply (simp add: all_right)
          apply (subgoal_tac "lfilter is_left (ltakeWhile is_right t) = LNil")
          apply simp
          apply (simp add: lfilter_empty_conv)
          by (metis lset_ltakeWhileD)
        show "xs' \<triangleright> lfilter is_left t \<triangleleft> ys' = LNil"
          apply (subst lappend_ltakeWhile_ldropWhile[symmetric, of t is_right])
          apply (simp add: all_right)
          apply (subgoal_tac "lfilter is_left (ltakeWhile is_right t) = LNil")
          apply simp
          apply (simp add: lfilter_empty_conv)
          by (metis lset_ltakeWhileD)
      qed
    }
    moreover
    {
      assume not_all_right: "ldropWhile is_right t \<noteq> LNil"
      hence finite_rights: "lfinite (ltakeWhile is_right t)"
        by (metis lappend_inf lappend_ltakeWhile_ldropWhile ldropWhile_eq_LNil_iff lset_ltakeWhileD)
      have ldropWhile_right_LCons: "ldropWhile is_right t = LCons (Inl ()) (ltl (ldropWhile is_right t))"
        by (metis ldropWhile_rights_not_LNil not_all_right)
      have ?EqLCons
      proof (intro exI conjI)
        show "q = (LCons (Inl (lhd xs')) (ltl xs' \<triangleright> lfilter is_left (ltl (ldropWhile is_right t)) \<triangleleft> ys),
                   LCons (Inl (lhd xs')) (ltl xs' \<triangleright> lfilter is_left (ltl (ldropWhile is_right t)) \<triangleleft> ys'))"
        proof (auto simp add: q_def)
          show "xs' \<triangleright> lfilter is_left t \<triangleleft> ys = LCons (Inl (lhd xs')) (ltl xs' \<triangleright> lfilter is_left (ltl (ldropWhile is_right t)) \<triangleleft> ys)"
            apply (subst lfilter_left_traj2[OF not_all_right])
            apply (subst ldropWhile_right_LCons)
            apply (subst interleave_def)
            apply (subst llist_corec)
            by (simp add: interleave_def[symmetric])
          show "xs' \<triangleright> lfilter is_left t \<triangleleft> ys' = LCons (Inl (lhd xs')) (ltl xs' \<triangleright> lfilter is_left (ltl (ldropWhile is_right t)) \<triangleleft> ys')"
            apply (subst lfilter_left_traj2[OF not_all_right])
            apply (subst ldropWhile_right_LCons)
            apply (subst interleave_def)
            apply (subst llist_corec)
            by (simp add: interleave_def[symmetric])
        qed
        have "(ltl xs' \<triangleright> lfilter is_left (ltl (ldropWhile is_right t)) \<triangleleft> ys, ltl xs' \<triangleright> lfilter is_left (ltl (ldropWhile is_right t)) \<triangleleft> ys')
            \<in> {(xs' \<triangleright> lfilter is_left t \<triangleleft> ys, xs' \<triangleright> lfilter is_left t \<triangleleft> ys') |xs' t ys ys'. xs' \<in> ltls xs}"
          apply auto
          by (metis ltls.intros(2) xs_tl)
        thus "(ltl xs' \<triangleright> lfilter is_left (ltl (ldropWhile is_right t)) \<triangleleft> ys, ltl xs' \<triangleright> lfilter is_left (ltl (ldropWhile is_right t)) \<triangleleft> ys')
            \<in> {(xs' \<triangleright> lfilter is_left t \<triangleleft> ys, xs' \<triangleright> lfilter is_left t \<triangleleft> ys') |xs' t ys ys'. xs' \<in> ltls xs}
          \<or> ltl xs' \<triangleright> lfilter is_left (ltl (ldropWhile is_right t)) \<triangleleft> ys = ltl xs' \<triangleright> lfilter is_left (ltl (ldropWhile is_right t)) \<triangleleft> ys'"
          by auto
      qed auto
    }
    ultimately show ?case
      by auto
  qed
qed

lemma ldrop_ltls: "ys' \<in> ltls ys \<Longrightarrow> ldrop (enat n) ys' \<in> ltls ys"
  by (induct n, auto, metis ldropn_Suc ltl_ldropn ltls.simps)

lemma lfilter_left_interleave: "lfilter is_left (interleave t xs ys) = interleave (lfilter is_left t) xs ys"
proof -
  let ?f = "\<lambda>t xs ys. lfilter is_left (interleave t xs ys)"
  let ?g = "\<lambda>t xs ys. interleave (lfilter is_left t) xs ys"

  have "(?f t xs ys, ?g t xs ys) \<in> {(?f t xs' ys', ?g t xs' ys')|t xs' ys'. xs' \<in> ltls xs \<and> ys' \<in> ltls ys}"
    by auto (metis ltls.intros(1))
  thus "?f t xs ys = ?g t xs ys"
  proof (coinduct rule: llist_equalityI)
    case (Eqllist q) note q = this[simplified]
    then obtain t xs' ys' where q_def: "q = (lfilter is_left (interleave t xs' ys'), interleave (lfilter is_left t) xs' ys')"
    and xs_tl: "xs' \<in> ltls xs"
    and ys_tl: "ys' \<in> ltls ys"
      by auto
    {
      assume all_right: "ldropWhile is_right t = LNil"
      have ?EqLNil
      proof (auto simp add: q_def)
        show "lfilter is_left (xs' \<triangleright> t \<triangleleft> ys') = LNil"
          apply (subst lappend_ltakeWhile_ldropWhile[symmetric, of t is_right])
          apply (simp add: all_right)
          apply (simp add: lfilter_empty_conv)
          apply auto
          apply (drule split_llist)
          apply auto
          by (metis helper1)
        show "xs' \<triangleright> lfilter is_left t \<triangleleft> ys' = LNil"
          apply (subst lappend_ltakeWhile_ldropWhile[symmetric, of t is_right])
          apply (simp add: all_right)
          apply (subst Not_is_left)
          apply (subst lfilter_ltakeWhile)
          by simp
      qed
    }
    moreover
    {
      assume not_all_right: "ldropWhile is_right t \<noteq> LNil"
      hence finite_rights: "lfinite (ltakeWhile is_right t)"
        by (metis lappend_inf lappend_ltakeWhile_ldropWhile ldropWhile_eq_LNil_iff lset_ltakeWhileD)
      have ldropWhile_right_LCons: "ldropWhile is_right t = LCons (Inl ()) (ltl (ldropWhile is_right t))"
        by (metis (full_types) ldropWhile_rights_not_LNil not_all_right)
      have ?EqLCons
      proof (intro exI conjI)
        show "q = (LCons (Inl (lhd xs')) (lfilter is_left (ltl xs' \<triangleright> ltl (ldropWhile is_right t) \<triangleleft> ldrop (llength (ltakeWhile is_right t)) ys')),
                   LCons (Inl (lhd xs')) (ltl xs' \<triangleright> lfilter is_left (ltl (ldropWhile is_right t)) \<triangleleft> ldrop (llength (ltakeWhile is_right t)) ys'))"
        proof (auto simp add: q_def)
          show "lfilter is_left (xs' \<triangleright> t \<triangleleft> ys')
              = LCons (Inl (lhd xs')) (lfilter is_left (ltl xs' \<triangleright> ltl (ldropWhile is_right t) \<triangleleft> ldrop (llength (ltakeWhile is_right t)) ys'))"
            apply (subst lfilter_left_traj1[OF not_all_right])
            apply (subst ldropWhile_right_LCons)
            apply (subst interleave_def)
            apply (subst llist_corec)
            by (simp add: interleave_def[symmetric])
          show "interleave (lfilter is_left t) xs' ys'
              = LCons (Inl (lhd xs')) (ltl xs' \<triangleright> lfilter is_left (ltl (ldropWhile is_right t)) \<triangleleft> ldrop (llength (ltakeWhile is_right t)) ys')"
            apply (subst lappend_ltakeWhile_ldropWhile[symmetric, of t is_right])
            apply (subst Not_is_left)
            apply (subst lfilter_lappend_lfinite)
            apply (simp add: finite_rights)
            apply (subst lfilter_ltakeWhile)
            apply simp
            apply (subst only_left_traj[where ys' = "ldrop (llength (ltakeWhile is_right t)) ys'"])
            apply (subgoal_tac "\<exists>z zs. ldropWhile is_right t = LCons (Inl z) zs")
            apply auto
            apply (subst interleave_def)
            apply (subst llist_corec)
            apply simp
            apply (simp only: interleave_def[symmetric])
            apply (rule sum_list_cases)
            apply (insert not_all_right)
            apply simp
            apply simp
            apply simp
            by (metis LNil_not_LCons is_right.simps(1) lhd_LCons lhd_ldropWhile)
        qed
        have "(lfilter is_left (ltl xs' \<triangleright> ltl (ldropWhile is_right t) \<triangleleft> ldrop (llength (ltakeWhile is_right t)) ys'),
               ltl xs' \<triangleright> lfilter is_left (ltl (ldropWhile is_right t)) \<triangleleft> ldrop (llength (ltakeWhile is_right t)) ys')
            \<in> {(lfilter is_left (interleave t xs' ys'), interleave (lfilter is_left t) xs' ys')|t xs' ys'. xs' \<in> ltls xs \<and> ys' \<in> ltls ys}"
          apply auto
          apply (rule_tac x = "ltl (ldropWhile is_right t)" in exI)
          apply (rule_tac x = "ltl xs'" in exI)
          apply (rule_tac x = "ldrop (llength (ltakeWhile is_right t)) ys'" in exI)
          apply auto
          apply (metis ltls.intros(2) xs_tl)
          by (metis (full_types) finite_rights ldrop_ltls lfinite_llength_enat ys_tl)
        thus "(lfilter is_left (ltl xs' \<triangleright> ltl (ldropWhile is_right t) \<triangleleft> ldrop (llength (ltakeWhile is_right t)) ys'),
               ltl xs' \<triangleright> lfilter is_left (ltl (ldropWhile is_right t)) \<triangleleft> ldrop (llength (ltakeWhile is_right t)) ys')
            \<in> {(lfilter is_left (interleave t xs' ys'), interleave (lfilter is_left t) xs' ys')|t xs' ys'. xs' \<in> ltls xs \<and> ys' \<in> ltls ys}
          \<or> lfilter is_left (ltl xs' \<triangleright> ltl (ldropWhile is_right t) \<triangleleft> ldrop (llength (ltakeWhile is_right t)) ys') =
             ltl xs' \<triangleright> lfilter is_left (ltl (ldropWhile is_right t)) \<triangleleft> ldrop (llength (ltakeWhile is_right t)) ys'"
          by blast
      qed auto
    }
    ultimately show ?case
      by auto
  qed
qed

hide_fact helper1

lemma interleave_swap: "ys \<triangleright> lmap swap t \<triangleleft> xs = lmap swap (xs \<triangleright> t \<triangleleft> ys)"
proof -
  have "(ys \<triangleright> lmap swap t \<triangleleft> xs, lmap swap (xs \<triangleright> t \<triangleleft> ys)) \<in> {(ys' \<triangleright> lmap swap t \<triangleleft> xs', lmap swap (xs' \<triangleright> t \<triangleleft> ys'))|xs' ys' t. xs' \<in> ltls xs \<and> ys' \<in> ltls ys}"
    by auto (metis ltls.intros(1))
  thus ?thesis
  proof (coinduct rule: llist_equalityI)
    case (Eqllist q) note q = this[simplified]
    then obtain t xs' ys' where q_def: "q = (ys' \<triangleright> lmap swap t \<triangleleft> xs', lmap swap (xs' \<triangleright> t \<triangleleft> ys'))"
    and xs_tl: "xs' \<in> ltls xs"
    and ys_tl: "ys' \<in> ltls ys"
      by auto
   {
      assume "t = LNil"
      hence ?EqLNil
        by (simp add: q_def)
    }
    moreover
    {
      fix v t' assume t_def: "t = LCons v t'"
      moreover hence "v = Inl () \<or> v = Inr ()"
        by (metis (full_types) sumE unit.exhaust)
      moreover
      {
        assume t_def: "t = LCons (Inl ()) t'"
        have ?EqLCons
        proof (intro exI conjI)
          show "q = (LCons (Inr (lhd xs')) (ys' \<triangleright> lmap swap t' \<triangleleft> ltl xs'), LCons (Inr (lhd xs')) (lmap swap (ltl xs' \<triangleright> t' \<triangleleft> ys')))"
            by (simp add: q_def t_def, intro conjI) (subst interleave_def, subst llist_corec, simp add: interleave_def[symmetric])+
          show "(ys' \<triangleright> lmap swap t' \<triangleleft> ltl xs', lmap swap (ltl xs' \<triangleright> t' \<triangleleft> ys')) \<in> {(ys' \<triangleright> lmap swap t \<triangleleft> xs', lmap swap (xs' \<triangleright> t \<triangleleft> ys'))|xs' ys' t. xs' \<in> ltls xs \<and> ys' \<in> ltls ys}
              \<or> ys' \<triangleright> lmap swap t' \<triangleleft> ltl xs' = lmap swap (ltl xs' \<triangleright> t' \<triangleleft> ys')"
            apply (intro disjI1)
            apply auto
            by (metis (full_types) ltls.intros(2) xs_tl ys_tl)
        qed auto
      }
      moreover
      {
        assume t_def: "t = LCons (Inr ()) t'"
        have ?EqLCons
        proof (intro exI conjI)
          show "q = (LCons (Inl (lhd ys')) (ltl ys' \<triangleright> lmap swap t' \<triangleleft> xs'), LCons (Inl (lhd ys')) (lmap swap (xs' \<triangleright> t' \<triangleleft> ltl ys')))"
            by (simp add: q_def t_def, intro conjI) (subst interleave_def, subst llist_corec, simp add: interleave_def[symmetric])+
          show "(ltl ys' \<triangleright> lmap swap t' \<triangleleft> xs', lmap swap (xs' \<triangleright> t' \<triangleleft> ltl ys')) \<in> {(ys' \<triangleright> lmap swap t \<triangleleft> xs', lmap swap (xs' \<triangleright> t \<triangleleft> ys'))|xs' ys' t. xs' \<in> ltls xs \<and> ys' \<in> ltls ys}
              \<or> ltl ys' \<triangleright> lmap swap t' \<triangleleft> xs' = lmap swap (xs' \<triangleright> t' \<triangleleft> ltl ys')"
            apply (intro disjI1)
            apply auto
            by (metis (full_types) ltls.intros(2) xs_tl ys_tl)
        qed auto
      }
      ultimately have ?EqLCons
        by (cases v) auto
    }
    ultimately show ?case
      apply (simp add: q_def)
      apply (cases t)
      by auto
  qed
qed

lemma [simp]: "swap (swap x) = x"
  by (cases x) auto

lemma [simp]: "swap \<circ> swap = id"
  by auto

lemma lfilter_right_interleave: "lfilter is_right (xs \<triangleright> t \<triangleleft> ys) = xs \<triangleright> lfilter is_right t \<triangleleft> ys" (is "?lhs = ?rhs")
proof -
  have "?lhs = lmap swap (lfilter is_left (lmap swap (xs \<triangleright> t \<triangleleft> ys)))"
    by (simp add: lfilter_lmap lmap_compose[symmetric] lmap_id del: lmap_compose)
  also have "... = lmap swap (lfilter is_left (ys \<triangleright> lmap swap t \<triangleleft> xs))"
    by (simp add: interleave_swap[symmetric])
  also have "... = lmap swap (ys \<triangleright> lfilter is_left (lmap swap t) \<triangleleft> xs)"
    by (metis lfilter_left_interleave)
  also have "... = xs \<triangleright> lmap swap (lfilter is_left (lmap swap t)) \<triangleleft> ys"
    by (simp add: interleave_swap[symmetric])
  also have "... = ?rhs"
    by (simp add: lfilter_lmap lmap_compose[symmetric] lmap_id del: lmap_compose)
  finally show ?thesis .
qed

lemma [simp]: "is_left (\<langle>\<lambda>x. Inl (f x),\<lambda>x. Inr (g x)\<rangle> x) = is_left x"
  by (cases x) auto

lemma [simp]: "is_left \<circ> \<langle>\<lambda>x. Inl (f x),\<lambda>x. Inr (g x)\<rangle> = is_left"
  by (simp add: o_def)

lemma [simp]: "is_left \<circ> \<langle>Inl \<circ> f, Inr \<circ> g\<rangle> = is_left"
  by (simp add: o_def)

lemma [simp]: "is_right (\<langle>\<lambda>x. Inl (f x),\<lambda>x. Inr (g x)\<rangle> x) = is_right x"
  by (cases x) auto

lemma [simp]: "is_right \<circ> \<langle>\<lambda>x. Inl (f x),\<lambda>x. Inr (g x)\<rangle> = is_right"
  by (simp add: o_def)

lemma [simp]: "is_right \<circ> \<langle>Inl \<circ> f, Inr \<circ> g\<rangle> = is_right"
  by (simp add: o_def)

lemma lmap_override [simp]: "lmap (\<lambda>x. y) (lmap f xs) = lmap (\<lambda>x. y) xs"
  by (simp add: lmap_compose[symmetric] o_def)

lemma lmap_lfilter_left: "lmap \<langle>f,g\<rangle> (lfilter is_left zs) = lmap (\<lambda>x. f x) (lmap unl (lfilter is_left zs))"
  apply (subst lmap_compose[symmetric])
  apply (rule lmap_lfilter_left_eq)
  by auto

lemma lmap_lfilter_right: "lmap \<langle>f,g\<rangle> (lfilter is_right zs) = lmap (\<lambda>x. g x) (lmap unr (lfilter is_right zs))"
  apply (subst lmap_compose[symmetric])
  apply (rule lmap_lfilter_right_eq)
  by auto

lemma traj_lfilter_lefts: "\<ll> zs = lmap f xs \<Longrightarrow> lfilter is_left (traj zs) = lmap (\<lambda>x. Inl ()) xs"
  by (simp add: lefts_def traj_def lfilter_lmap lmap_lfilter_left)

lemma lmap_const_llength [iff]: "lmap (\<lambda>x. c) xs = lmap (\<lambda>x. c) ys \<longleftrightarrow> llength xs = llength ys"
proof
  assume "lmap (\<lambda>x. c) xs = lmap (\<lambda>x. c) ys" thus "llength xs = llength ys"
    by (metis llength_lmap)
next
  assume "llength xs = llength ys"
  hence "(lmap (\<lambda>x. c) xs, lmap (\<lambda>x. c) ys) \<in> {(lmap (\<lambda>x. c) xs, lmap (\<lambda>x. c) ys) |(xs::'b llist) (ys::'c llist). llength xs = llength ys}"
    by auto
  thus "lmap (\<lambda>x. c) xs = lmap (\<lambda>x. c) ys"
  proof (coinduct rule: llist_equalityI)
    case (Eqllist q) note q = this[simplified]
    then obtain xs :: "'b llist" and ys :: "'c llist"
    where q_def: "q = (lmap (\<lambda>x. c) xs, lmap (\<lambda>x. c) ys)" and same_llength: "llength xs = llength ys" by blast
    {
      assume "xs = LNil"
      moreover hence "ys = LNil"
        by (metis llength_eq_0 same_llength)
      ultimately have ?EqLNil using q_def
        by simp
      hence ?case by blast
    }
    moreover
    {
      fix x' xs'
      assume xs_def: "xs = LCons x' xs'"
      then obtain y' and ys' where ys_def: "ys = LCons y' ys'"
        by (metis llength_eq_0 neq_LNil_conv same_llength)
      have ?EqLCons
        apply (rule_tac x = "lmap (\<lambda>x. c) xs'" in exI)
        apply (rule_tac x = "lmap (\<lambda>x. c) ys'" in exI)
        apply (rule_tac x = c in exI)+
        apply (intro conjI)
        apply (auto simp add: q_def xs_def ys_def)
        by (metis eSuc_inject llength_LCons same_llength xs_def ys_def)
      hence ?case by blast
    }
    ultimately show ?case
      by (cases xs) auto
  qed
qed

lemma traj_lfilter_lefts_var: "llength (\<ll> zs) = llength xs \<Longrightarrow> lfilter is_left (traj zs) = lmap (\<lambda>x. Inl ()) xs"
  by (simp add: lefts_def traj_def lfilter_lmap lmap_lfilter_left)

lemma traj_lfilter_rights_var: "llength (\<rr> zs) = llength ys \<Longrightarrow> lfilter is_right (traj zs) = lmap (\<lambda>x. Inr ()) ys"
  by (simp add: rights_def traj_def lfilter_lmap lmap_lfilter_right)

lemma lefts_interleave [simp]:
  assumes "\<ll> zs = lmap f xs"
  shows "\<ll> (interleave (traj zs) xs ys) = xs"
proof -
  have "\<ll> (interleave (traj zs) xs ys) = lmap unl (interleave (lfilter is_left (traj zs)) xs ys)"
    by (metis comp_apply lefts_def lfilter_left_interleave)
  also have "... = lmap unl (interleave (lmap (\<lambda>x. Inl ()) xs) xs ys)"
    by (simp only: traj_lfilter_lefts[OF assms(1)])
  also have "... = xs"
    by (metis interleave_only_left lmap2_id unl.simps(1))
  finally show ?thesis .
qed

lemma [simp]: "llength (\<ll> (traj zs)) = llength (\<ll> zs)"
  apply (simp add: traj_def)
  by (metis interleave_only_left lfilter_left_interleave llength_lmap reinterleave traj_def traj_lfilter_lefts_var)

lemma [simp]: "llength (\<rr> (traj zs)) = llength (\<rr> zs)"
  apply (simp add: traj_def)
  by (metis interleave_only_right lfilter_right_interleave llength_lmap reinterleave traj_def traj_lfilter_rights_var)

lemma lefts_interleave_llength [simp]:
  assumes "llength (\<ll> (traj zs)) = llength xs"
  shows "\<ll> (xs \<triangleright> traj zs \<triangleleft> ys) = xs"
proof -
  have "\<ll> (xs \<triangleright> traj zs \<triangleleft> ys) = lmap unl (xs \<triangleright> lfilter is_left (traj zs) \<triangleleft> ys)"
    by (metis comp_apply lefts_def lfilter_left_interleave)
  also have "... = lmap unl (xs \<triangleright> lmap (\<lambda>x. Inl ()) xs \<triangleleft> ys)" using assms
    by (subst traj_lfilter_lefts_var[where xs = xs]) simp_all
  also have "... = xs"
    by (metis interleave_only_left lmap2_id unl.simps(1))
  finally show ?thesis .
qed    


lemma traj_lfilter_rights: "\<rr> zs = lmap f xs \<Longrightarrow> lfilter is_right (traj zs) = lmap (\<lambda>x. Inr ()) xs"
  by (simp add: rights_def traj_def lfilter_lmap lmap_lfilter_right)

lemma rights_interleave [simp]:
  assumes "\<rr> zs = lmap g ys"
  shows "\<rr> (interleave (traj zs) xs ys) = ys"
proof -
  have "\<rr> (interleave (traj zs) xs ys) = lmap unr (interleave (lfilter is_right (traj zs)) xs ys)"
    by (metis comp_apply rights_def lfilter_right_interleave)
  also have "... = lmap unr (interleave (lmap (\<lambda>x. Inr ()) ys) xs ys)"
    by (simp only: traj_lfilter_rights[OF assms(1)])
  also have "... = ys"
    by (metis interleave_only_right lmap2_id unr.simps(1))
  finally show ?thesis .
qed

lemma rights_interleave_llength [simp]:
  assumes "llength (\<rr> (traj zs)) = llength ys"
  shows "\<rr> (interleave (traj zs) xs ys) = ys"
proof -
  have "\<rr> (interleave (traj zs) xs ys) = lmap unr (interleave (lfilter is_right (traj zs)) xs ys)"
    by (metis comp_apply rights_def lfilter_right_interleave)
  also have "... = lmap unr (interleave (lmap (\<lambda>x. Inr ()) ys) xs ys)" using assms
    by (subst traj_lfilter_rights_var) simp_all
  also have "... = ys"
    by (metis interleave_only_right lmap2_id unr.simps(1))
  finally show ?thesis .
qed


lemma lefts_def_var: "lmap unl (lfilter is_left xs) = \<ll> xs"
  by (auto simp add: lefts_def)

lemma rights_def_var: "lmap unr (lfilter is_right xs) = \<rr> xs"
  by (auto simp add: rights_def)

lemma traj_interleave [simp]: "traj (xs \<triangleright> t \<triangleleft> ys) = t"
proof -
  have "(traj (xs \<triangleright> t \<triangleleft> ys), t) \<in> {(traj (xs' \<triangleright> t \<triangleleft> ys'), t)|xs' ys' t. xs' \<in> ltls xs \<and> ys' \<in> ltls ys}"
    by auto (metis ltls.intros(1))
  thus ?thesis
  proof (coinduct rule: llist_equalityI)
    case (Eqllist q) note q = this[simplified]
    then obtain t xs' ys' where q_def: "q = (traj (xs' \<triangleright> t \<triangleleft> ys'), t)"
    and xs_tl: "xs' \<in> ltls xs"
    and ys_tl: "ys' \<in> ltls ys"
      by auto
    {
      assume "t = LNil"
      hence ?EqLNil
        by (simp add: q_def traj_def)
    }
    moreover
    {
      fix v t' assume t_def: "t = LCons v t'"
      have ?EqLCons
        apply (simp add: q_def t_def)
        apply (cases v)
        apply simp_all
        apply (subst interleave_def)
        apply (subst llist_corec)
        apply simp
        apply (subst interleave_def[symmetric])
        apply (auto simp add: traj_def)
        apply (metis ltls.intros(2) xs_tl ys_tl)
        apply (subst interleave_def)
        apply (subst llist_corec)
        apply simp
        apply (subst interleave_def[symmetric])
        apply (auto simp add: traj_def)
        by (metis ltls.intros(2) xs_tl ys_tl)
    }
    ultimately show ?case
      apply (simp add: q_def)
      apply (cases t)
      by auto
  qed
qed   

lemma [simp]: "unl (\<langle>Inl \<circ> f,Inr \<circ> g\<rangle> (Inl x)) = f x"
  by simp

lemma [simp]: "unl \<circ> (\<langle>Inl \<circ> f,Inr \<circ> g\<rangle> \<circ> Inl) = f"
  by auto 

lemma [simp]: "unr (\<langle>Inl \<circ> f,Inr \<circ> g\<rangle> (Inr x)) = g x"
  by simp

lemma [simp]: "unr \<circ> (\<langle>Inl \<circ> f,Inr \<circ> g\<rangle> \<circ> Inr) = g"
  by auto 

lemma [simp]: "\<langle>\<lambda>x. Inl (),\<lambda>x. Inr ()\<rangle> (\<langle>Inl \<circ> f,Inr \<circ> g\<rangle> x) = \<langle>\<lambda>x. Inl (),\<lambda>x. Inr ()\<rangle> x"
  by (cases x) auto

lemma [simp]: "\<langle>\<lambda>x. Inl (),\<lambda>x. Inr ()\<rangle> \<circ> \<langle>Inl \<circ> f,Inr \<circ> g\<rangle> = \<langle>\<lambda>x. Inl (),\<lambda>x. Inr ()\<rangle>"
  by auto

lemma lmap_interleave: "\<ll> zs = lmap f xs \<Longrightarrow> \<rr> zs = lmap g ys \<Longrightarrow> lmap \<langle>Inl \<circ> f,Inr \<circ> g\<rangle> (xs \<triangleright> traj zs \<triangleleft> ys) = lmap f xs \<triangleright> traj zs \<triangleleft> lmap g ys"
  apply (rule traj_equality)
  defer
  apply (simp (no_asm) add: lefts_def)
  apply (simp add: lfilter_lmap)
  apply (subst lefts_def_var)+
  apply (subst lefts_interleave[where f = id])
  apply (simp add: lmap_id)
  apply (subst lfilter_left_interleave)
  apply (subgoal_tac "lfilter is_left (traj zs) = lmap (\<lambda>x. Inl ()) xs")
  apply (rotate_tac 2)
  apply (erule ssubst)
  apply (subst interleave_only_left)
  apply (simp add: lmap_compose[symmetric] del: lmap_compose)
  apply (metis traj_lfilter_lefts)
  apply (simp (no_asm) add: rights_def)
  apply (simp add: lfilter_lmap)
  apply (subst rights_def_var)+
  apply (subst rights_interleave[where g = id])
  apply (simp add: lmap_id)
  apply (subst lfilter_right_interleave)
  apply (subgoal_tac "lfilter is_right (traj zs) = lmap (\<lambda>x. Inr ()) ys")
  apply (rotate_tac 2)
  apply (erule ssubst)
  apply (subst interleave_only_right)
  apply (simp add: lmap_compose[symmetric] del: lmap_compose)
  apply (metis traj_lfilter_rights)
  apply (simp add: traj_def)
  apply (simp add: lmap_compose[symmetric] del: lmap_compose)
  by (simp add: traj_def [symmetric])

lemma [simp]: "\<ll> zs = lmap f xs \<Longrightarrow> \<rr> zs = lmap g ys \<Longrightarrow> lmap \<langle>Inl \<circ> f,Inr \<circ> g\<rangle> (interleave (traj zs) xs ys) = zs"
  by (subst reinterleave[symmetric, where t = zs], simp add: lmap_interleave)

lemma [simp]: "is_left \<circ> \<langle>\<lambda>x. Inl (f x),\<lambda>x. Inr (g x)\<rangle> = is_left"
proof -
  {
    fix x :: "'a + 'b"
    have "(is_left \<circ> \<langle>\<lambda>x. Inl (f x),\<lambda>x. Inr (g x)\<rangle>) x = is_left x"
      by (cases x) auto
  }
  thus ?thesis by auto
qed

lemma [simp]: "is_left (\<langle>Inl \<circ> f,Inr \<circ> g\<rangle> x) = is_left x"
  by (cases x) auto

lemma [simp]: "is_left \<circ> \<langle>Inl \<circ> f,Inr \<circ> g\<rangle> = is_left"
  by (subst o_def) simp

lemma [simp]: "is_right (\<langle>Inl \<circ> f,Inr \<circ> g\<rangle> x) = is_right x"
  by (cases x) auto

lemma [simp]: "is_right \<circ> \<langle>Inl \<circ> f,Inr \<circ> g\<rangle> = is_right"
  by (subst o_def) simp

lemma tshuffle_words_map:
  fixes f :: "'a \<Rightarrow> 'b"
  and g :: "'c \<Rightarrow> 'd"
  shows "lmap f xs \<sha> lmap g ys = lmap \<langle>Inl \<circ> f, Inr \<circ> g\<rangle> ` (xs \<sha> ys)"
proof (auto simp add: tshuffle_words_def image_def)
  fix zs
  assume "\<ll> zs = lmap f xs" and "\<rr> zs = lmap g ys"
  thus "\<exists>zs'. \<ll> zs' = xs \<and> \<rr> zs' = ys \<and> zs = lmap \<langle>Inl \<circ> f,Inr \<circ> g\<rangle> zs'"
    by (rule_tac x = "interleave (traj zs) xs ys" in exI) (auto intro: traj_equality)
next
  fix zs
  show "\<ll> (lmap \<langle>Inl \<circ> f,Inr \<circ> g\<rangle> zs) = lmap f (\<ll> zs)"
    apply (simp add: lefts_def lfilter_lmap lmap_compose[symmetric] del: lmap_compose)
    apply (rule lmap_lfilter_eq)
    by (metis is_right.simps(1) not_is_left o_eq_dest_lhs sum.simps(5) sumE unl.simps(1))
  show "\<rr> (lmap \<langle>Inl \<circ> f,Inr \<circ> g\<rangle> zs) = lmap g (\<rr> zs)"
    apply (simp add: rights_def lfilter_lmap lmap_compose[symmetric] del: lmap_compose)
    apply (rule lmap_lfilter_eq)
    by (metis comp_apply is_left.simps(1) not_is_left sum.simps(6) sumE unr.simps(1))
qed

declare lmap_id[simp]
  
lemma [simp]: "\<langle>id,id\<rangle> \<circ> \<langle>Inl \<circ> \<langle>id,id\<rangle>,Inr\<rangle> = \<langle>\<langle>id,id\<rangle>,id\<rangle>"
proof -
  {
    fix x :: "('a + 'a) + 'a"
    have "(\<langle>id,id\<rangle> \<circ> \<langle>Inl \<circ> \<langle>id,id\<rangle>,Inr\<rangle>) x = \<langle>\<langle>id,id\<rangle>,id\<rangle> x"
      by (cases x) auto
  }
  thus ?thesis by auto
qed

lemma [simp]: "\<langle>id,id\<rangle> \<circ> \<langle>Inl,Inr \<circ> \<langle>id,id\<rangle>\<rangle> = \<langle>id,\<langle>id,id\<rangle>\<rangle>"
proof -
  {
    fix x :: "'a + ('a + 'a)"
    have "(\<langle>id,id\<rangle> \<circ> \<langle>Inl,Inr \<circ> \<langle>id,id\<rangle>\<rangle>) x = \<langle>id,\<langle>id,id\<rangle>\<rangle> x"
      by (cases x) auto
  }
  thus ?thesis by auto
qed

lemma lmap_sum_elim_simp1: "lmap \<langle>id,id\<rangle> \<circ> lmap \<langle>Inl \<circ> \<langle>id,id\<rangle>, Inr\<rangle> = lmap \<langle>\<langle>id,id\<rangle>,id\<rangle>"
proof -
  {
    fix xs :: "(('a + 'a) + 'a) llist"
    have "(lmap \<langle>id,id\<rangle> \<circ> lmap \<langle>Inl \<circ> \<langle>id,id\<rangle>, Inr\<rangle>) xs = lmap \<langle>\<langle>id,id\<rangle>,id\<rangle> xs"
      by (subst o_def) (simp add: lmap_compose[symmetric])
  }
  thus ?thesis by auto
qed

lemma lmap_sum_elim_simp2: "lmap \<langle>id,id\<rangle> \<circ> lmap \<langle>Inl, Inr \<circ> \<langle>id,id\<rangle>\<rangle> = lmap \<langle>id,\<langle>id,id\<rangle>\<rangle>"
proof -
  {
    fix xs :: "('a + ('a + 'a)) llist"
    have "(lmap \<langle>id,id\<rangle> \<circ> lmap \<langle>Inl, Inr \<circ> \<langle>id,id\<rangle>\<rangle>) xs = lmap \<langle>id,\<langle>id,id\<rangle>\<rangle> xs"
      by (subst o_def) (simp add: lmap_compose[symmetric])
  }
  thus ?thesis by auto
qed

lemma shuffle_assoc: "(X \<parallel> Y) \<parallel> Z = X \<parallel> (Y \<parallel> Z)"
proof -
  have "(X \<parallel> Y) \<parallel> Z = lmap \<langle>id,id\<rangle> ` ((lmap \<langle>id,id\<rangle> ` (X \<Sha> Y)) \<Sha> Z)"
    by (simp add: shuffle_to_tshuffle)
  also have "... = lmap \<langle>id,id\<rangle> ` \<Union>{x \<sha> y |x y. x \<in> lmap \<langle>id,id\<rangle> ` (X \<Sha> Y) \<and> y \<in> Z}"
    by (simp add: tshuffle_def)
  also have "... = lmap \<langle>id,id\<rangle> ` \<Union>{lmap \<langle>id,id\<rangle> x \<sha> y|x y. x \<in> (X \<Sha> Y) \<and> y \<in> Z}"
    by (auto simp add: image_def)
  also have "... = lmap \<langle>id,id\<rangle> ` \<Union>{lmap \<langle>Inl \<circ> \<langle>id,id\<rangle>, Inr\<rangle> ` (x \<sha> y)|x y. x \<in> (X \<Sha> Y) \<and> y \<in> Z}"
    by (simp add: tshuffle_words_map[where g = id, simplified])
  also have "... = lmap \<langle>id,id\<rangle> ` lmap \<langle>Inl \<circ> \<langle>id,id\<rangle>, Inr\<rangle> ` \<Union>{x \<sha> y|x y. x \<in> (X \<Sha> Y) \<and> y \<in> Z}"
    by (auto simp add: image_def)
  also have "... = (lmap \<langle>id,id\<rangle> \<circ> lmap \<langle>Inl \<circ> \<langle>id,id\<rangle>, Inr\<rangle>) ` ((X \<Sha> Y) \<Sha> Z)"
    by (metis image_compose tshuffle_def)
  also have "... = lmap \<langle>\<langle>id,id\<rangle>,id\<rangle> ` ((X \<Sha> Y) \<Sha> Z)"
    by (simp only: lmap_sum_elim_simp1)
  also have "... = lmap \<langle>id,\<langle>id,id\<rangle>\<rangle> ` (X \<Sha> (Y \<Sha> Z))"
    by (metis tshuffle_assoc)
  also have "... = (lmap \<langle>id,id\<rangle> \<circ> lmap \<langle>Inl, Inr \<circ> \<langle>id,id\<rangle>\<rangle>) ` (X \<Sha> (Y \<Sha> Z))"
    by (simp only: lmap_sum_elim_simp2)
  also have "... = lmap \<langle>id,id\<rangle> ` lmap \<langle>Inl, Inr \<circ> \<langle>id,id\<rangle>\<rangle> ` \<Union>{x \<sha> y|x y. x \<in> X \<and> y \<in> (Y \<Sha> Z)}"
    by (metis image_compose tshuffle_def)
  also have "... = lmap \<langle>id,id\<rangle> ` \<Union>{lmap \<langle>Inl, Inr \<circ> \<langle>id,id\<rangle>\<rangle> ` (x \<sha> y)|x y. x \<in> X \<and> y \<in> (Y \<Sha> Z)}"
    by (auto simp add: image_def)
  also have "... = lmap \<langle>id,id\<rangle> ` \<Union>{x \<sha> lmap \<langle>id,id\<rangle> y|x y. x \<in> X \<and> y \<in> (Y \<Sha> Z)}"
    by (simp add: tshuffle_words_map[where f = id, simplified])
  also have "... = lmap \<langle>id,id\<rangle> ` \<Union>{x \<sha> y|x y. x \<in> X \<and> y \<in> lmap \<langle>id,id\<rangle> ` (Y \<Sha> Z)}"
    by (auto simp add: image_def)
  also have "... = lmap \<langle>id,id\<rangle> ` (X \<Sha> (lmap \<langle>id,id\<rangle> ` (Y \<Sha> Z)))"
    by (simp add: tshuffle_def)
  also have "... = X \<parallel> (Y \<parallel> Z)"
    by (simp add: shuffle_to_tshuffle)
  finally show ?thesis .
qed

definition FIN where "FIN = {xs. lfinite xs}"

lemma is_right_nth_traj: "\<not> lfinite xs \<Longrightarrow> is_right (lnth xs n) \<Longrightarrow> is_right (lnth (lmap \<langle>\<lambda>x. Inl (),\<lambda>x. Inr ()\<rangle> xs) n)"
  apply (subst lnth_lmap)
  apply (metis enat_ile llength_eq_enat_lfiniteD not_less)
  apply (cases "lnth xs n")
  by simp_all

lemma is_left_nth_traj: "\<not> lfinite xs \<Longrightarrow> is_left (lnth xs n) \<Longrightarrow> is_left (lnth (lmap \<langle>\<lambda>x. Inl (),\<lambda>x. Inr ()\<rangle> xs) n)"
  apply (subst lnth_lmap)
  apply (metis enat_ile llength_eq_enat_lfiniteD not_less)
  apply (cases "lnth xs n")
  by simp_all

lemma fair_traj: "\<not> lfinite xs \<Longrightarrow> fair xs \<Longrightarrow> fair (traj xs)"
  apply (auto simp add: traj_def fair_def)
  apply (metis is_right_nth_traj)
  apply (metis is_left_nth_traj)
  by (metis (full_types) is_left_nth_traj is_right_nth_traj not_is_right)+

lemma one_elem_llist:
  assumes inf_xs: "\<not> lfinite xs" and inf_ys: "\<not> lfinite ys"
  shows "lmap (\<lambda>x. z) xs = lmap (\<lambda>x. z) ys"
proof -
  have "(lmap (\<lambda>x. z) xs, lmap (\<lambda>x. z) ys) \<in> {(lmap (\<lambda>x. z) xs', lmap (\<lambda>x. z) ys')|xs' ys'. \<not> lfinite xs' \<and> \<not> lfinite ys' \<and> xs' \<in> ltls xs \<and> ys' \<in> ltls ys}"
    apply auto
    by (metis inf_xs inf_ys ltls.intros(1))
  thus ?thesis
  proof (coinduct rule: llist_equalityI)
    case (Eqllist q) note q = this[simplified]
    then obtain xs' and ys' where q_def: "q = (lmap (\<lambda>x. z) xs', lmap (\<lambda>x. z) ys')"
    and inf_xs': "\<not> lfinite xs'" and inf_ys': "\<not> lfinite ys'" and xs'_tl: "xs' \<in> ltls xs" and ys'_tl: "ys' \<in> ltls ys"
      by auto
    have ?EqLCons
      apply (rule_tac x = "lmap (\<lambda>x. z) (ltl xs')" in exI)
      apply (rule_tac x = "lmap (\<lambda>x. z) (ltl ys')" in exI)
      apply (rule_tac x = z in exI)+
      apply (auto simp add: q_def)
      apply (metis (full_types) inf_xs' lfinite.simps lhd_LCons_ltl lmap_LCons)
      apply (metis (full_types) inf_ys' lfinite.simps lhd_LCons_ltl lmap_LCons)
      apply (rule_tac x = "ltl xs'" in exI)
      apply auto
      apply (rule_tac x = "ltl ys'" in exI)
      by (metis (full_types) inf_xs' inf_ys' lfinite_ltl ltls.intros(2) xs'_tl ys'_tl)
    thus ?case
      by auto
  qed
qed

lemma infinite_fair_shuffle:
  assumes inf_xs: "\<not> lfinite xs" and inf_ys: "\<not> lfinite ys"
  shows "(xs \<sha> ys) \<subseteq> {xs \<triangleright> t \<triangleleft> ys|t. fair t}"
proof (auto simp add: FIN_def)
  fix zs
  assume "zs \<in> xs \<sha> ys"
  hence "zs = xs \<triangleright> traj zs \<triangleleft> ys" and "fair (traj zs)"
    by - (metis (lifting, full_types) mem_Collect_eq reinterleave tshuffle_words_def, metis fair_non_empty fair_traj inf_xs inf_ys shuffle_fair)
  thus "\<exists>t. zs = xs \<triangleright> t \<triangleleft> ys \<and> fair t"
    by blast
qed

lemma interleave_left: "xs \<triangleright> LCons (Inl ()) ts \<triangleleft> ys = LCons (Inl (lhd xs)) (ltl xs \<triangleright> ts \<triangleleft> ys)"
  by (simp add: llist_corec interleave_def)

lemma interleave_right: "xs \<triangleright> LCons (Inr ()) ts \<triangleleft> ys = LCons (Inr (lhd ys)) (xs \<triangleright> ts \<triangleleft> ltl ys)"
  by (simp add: llist_corec interleave_def)

lemma lfinite_lefts: "lfinite xs \<Longrightarrow> lfinite (\<ll> xs)"
  by (simp add: lefts_def)

lemma lfinite_rights: "lfinite xs \<Longrightarrow> lfinite (\<rr> xs)"
  by (simp add: rights_def)

lemma lfinite_traj': "lfinite zs \<Longrightarrow> zs = xs \<triangleright> t \<triangleleft> ys \<Longrightarrow> lfinite t"
proof (induct zs arbitrary: t xs ys rule: lfinite_induct)
  fix t and xs :: "'a llist" and ys :: "'b llist"
  case Nil thus ?case
    by (auto intro: sum_list_cases simp add: interleave_def llist_corec)
next
  fix t xs ys
  case (Cons z zs)
  thus ?case
    by (auto intro: sum_list_cases simp add: interleave_left interleave_right)
qed

lemma lfinite_traj: "lfinite (xs \<triangleright> t \<triangleleft> ys) \<Longrightarrow> lfinite t"
  by (metis lfinite_traj')

lemma shuffle_dist: "X \<parallel> (Y \<union> Z) = X \<parallel> Y \<union> X \<parallel> Z"
  by (simp only: shuffle_def Union_Un_distrib[symmetric]) (rule arg_cong, fast)

lemma lfilter_right_left: "lfilter is_right x = LNil \<Longrightarrow> lfilter is_left x = x"
  by (auto simp add: lfilter_empty_conv)  (metis (full_types) lfilter_K_True lfilter_cong)

lemma lfilter_left_right: "lfilter is_left x = LNil \<Longrightarrow> lfilter is_right x = x"
  by (auto simp add: lfilter_empty_conv)  (metis (full_types) lfilter_K_True lfilter_cong)

lemma lmap2_id_var: "(\<And>x. x \<in> lset xs \<Longrightarrow> f (g x) = x) \<Longrightarrow> lmap f (lmap g xs) = xs"
  apply (subst lmap_compose[symmetric])
  apply (subst id_apply[symmetric, of xs]) back
  apply (subst lmap_id[symmetric])
  apply (rule lmap_eq)
  by (simp add: o_def)

lemma [simp]: "lmap \<langle>id,id\<rangle> (lmap Inl xs) = xs"
  by (metis all_lefts id_def lefts_def_var lefts_mapl lmap.id lmap_lfilter_left)

lemma [simp]: "lmap \<langle>id,id\<rangle> (lmap Inr xs) = xs"
  by (metis all_rights id_def lmap.id lmap_lfilter_right rights_def_var rights_mapr)

lemma tshuffle_LNil [simp]: "xs \<sha> LNil = {lmap Inl xs}"
  apply (simp add: tshuffle_words_def)
  apply (auto simp add: lefts_def rights_def)
  apply (subst lfilter_right_left)
  apply assumption
  apply (rule sym)
  apply (rule lmap2_id_var)
  apply (simp only: lfilter_empty_conv)
  apply (metis (full_types) is_left.simps(2) not_is_left sumE unl.simps(1))
  apply (metis all_lefts lefts_def_var lefts_mapl)  
  apply (subst lfilter_lmap)
  apply (subgoal_tac "lfilter (is_right \<circ> Inl) xs = LNil")
  apply simp
  apply (subst lfilter_empty_conv)
  by auto

lemma tshuffle_LNil_sym [simp]: "LNil \<sha> ys = {lmap Inr ys}"
  apply (simp add: tshuffle_words_def)
  apply (auto simp add: lefts_def rights_def)
  apply (subst lfilter_left_right)
  apply assumption
  apply (rule sym)
  apply (rule lmap2_id_var)
  apply (simp only: lfilter_empty_conv)
  apply (metis (full_types) is_right.simps(2) not_is_left sumE unr.simps(1))
  apply (subst lfilter_lmap)
  apply (subgoal_tac "lfilter (is_left \<circ> Inr) ys = LNil")
  apply simp
  apply (subst lfilter_empty_conv)
  apply auto
  by (metis lmap2_id unr.simps(1))

lemma shuffle_one: "X \<parallel> {LNil} = X"
  by (auto simp add: shuffle_def)

interpretation par!: dioid_one_zero "op \<union>" "op \<parallel>" "{LNil}" "{}" "op \<subseteq>" "op \<subset>"
  apply default
  apply (rule Un_assoc)
  apply (rule Un_commute)
  apply (rule shuffle_assoc)
  apply (metis shuffle_dist shuffle_comm)
  apply (metis shuffle_comm shuffle_one)
  apply (metis shuffle_one)
  apply simp
  apply (simp add: shuffle_def)
  apply (simp add: shuffle_def)
  apply (metis Un_upper1 sup_absorb1 sup_commute)
  apply (metis psubset_eq)
  apply simp
  by (rule shuffle_dist)

interpretation seq!: dioid_one_zerol "op \<union>" "op \<cdot>" "{LNil}" "{}" "op \<subseteq>" "op \<subset>"
  apply default
  apply (metis l_prod_assoc)
  apply (metis l_prod_distr)
  apply (metis l_prod_one(1))
  apply (metis l_prod_one(2))
  apply (metis par.add.left_neutral)
  apply (metis l_prod_zero)
  apply (metis par.add_idem')
  by (metis l_prod_distl)

no_notation
  Signatures.star_op_class.star ("_\<^sup>\<star>" [101] 100) and
  Signatures.omega_op_class.omega ("_\<^sup>\<omega>" [101] 100)

definition omega :: "'a lan \<Rightarrow> 'a lan" ("_\<^sup>\<omega>" [101] 100) where
  "X\<^sup>\<omega> = (\<nu> Y. X\<cdot>Y)"

definition star :: "'a lan \<Rightarrow> 'a lan" ("_\<^sup>\<star>" [101] 100) where
  "X\<^sup>\<star> = (\<mu> Y. {LNil} \<union> X\<cdot>Y)"

definition loop :: "'a lan \<Rightarrow> 'a lan" ("_\<^sup>\<infinity>" [101] 100) where
  "X\<^sup>\<infinity> = X\<^sup>\<star> \<union> X\<^sup>\<omega>"

lemma [simp,intro!]: "mono (op \<cdot> x)"
  by (metis mono_def seq.mult_isol)

lemma iso_Un1 [intro!]: "mono (\<lambda>Y. f Y) \<Longrightarrow> mono (\<lambda>Y. X \<union> f Y)"
  by (auto simp add: mono_def)

lemma iso_Un2 [intro!]: "mono (\<lambda>Y. f Y) \<Longrightarrow> mono (\<lambda>Y. f Y \<union> X)"
  by (auto simp add: mono_def)

interpretation seq!: left_kleene_algebra_zerol "op \<union>" "op \<cdot>" "{LNil}" "{}" "op \<subseteq>" "op \<subset>" star
proof
  fix X Y Z :: "'a lan"
  show "{LNil} \<union> X \<cdot> X\<^sup>\<star> \<subseteq> X\<^sup>\<star>"
    unfolding star_def
    by (subst fp_compute[symmetric], metis (lifting) insert_is_Un insert_mono mono_def seq.mult_isol, blast)

  show "Z \<union> X \<cdot> Y \<subseteq> Y \<longrightarrow> X\<^sup>\<star> \<cdot> Z \<subseteq> Y"
  proof
    assume "Z \<union> X \<cdot> Y \<subseteq> Y"
    hence "(\<mu> Y. Z \<union> X \<cdot> Y) \<subseteq> Y"
      by (rule fp_induct[rotated 1]) (metis (lifting) mono_def l_prod_isor subset_refl sup_mono)
    moreover have "X\<^sup>\<star> \<cdot> Z = (\<mu> Y. Z \<union> X \<cdot> Y)"
      unfolding star_def
      by (rule fixpoint_fusion) (auto simp only: lower_is_jp join_preserving_def l_prod_inf_distr o_def l_prod_distr l_prod_one l_prod_assoc)
    ultimately show "X\<^sup>\<star> \<cdot> Z \<subseteq> Y"
      by simp
  qed
qed

interpretation seq!: left_omega_algebra_zerol "op \<union>" "op \<cdot>" "{LNil}" "{}" "op \<subseteq>" "op \<subset>" star omega
proof
  fix X Y Z :: "'a lan"
  show omega_unfold: "X\<^sup>\<omega> \<subseteq> X \<cdot> X\<^sup>\<omega>"
    unfolding omega_def by (subst gfp_compute[symmetric]) (auto simp: seq.mult_isol)

  have omega_coinduct: "\<And>X Y Z. Y \<subseteq> X\<cdot>Y \<Longrightarrow> Y \<subseteq> X\<^sup>\<omega>"
    unfolding omega_def by (rule gfp_induct) (auto simp: seq.mult_isol)

  have omega_star_fuse: "X\<^sup>\<omega> \<union> X\<^sup>\<star>\<cdot>Z = (\<nu> Y. Z \<union> X \<cdot> Y)" unfolding omega_def
  proof (rule greatest_fixpoint_fusion, auto simp add: o_def)
    show "upper_adjoint (\<lambda>Y. Y \<union> X\<^sup>\<star> \<cdot> Z)"
      apply (simp add: upper_adjoint_def galois_connection_def)
      apply (subst Un_commute)
      apply (subst Diff_subset_conv[symmetric])
      apply (rule_tac x = "\<lambda>x. x - X\<^sup>\<star> \<cdot> Z" in exI)
      by simp
  next
    show "(\<lambda>Y. X \<cdot> Y \<union> X\<^sup>\<star> \<cdot> Z) = (\<lambda>Y. Z \<union> (X \<cdot> Y \<union> X \<cdot> (X\<^sup>\<star> \<cdot> Z)))"
      apply (rule ext)
      apply (subst seq.star_unfoldl_eq[symmetric])
      apply (subst l_prod_distr)
      apply simp
      apply (simp only: l_prod_assoc Un_assoc[symmetric])
      apply (subst Un_commute)
      by simp
  qed

  show "X\<^sup>\<star> \<cdot> {} \<subseteq> X\<^sup>\<omega>"
    by (rule omega_coinduct, subst seq.star_unfoldl_eq[symmetric])
       (simp only: l_prod_distr l_prod_one par.add_zerol l_prod_assoc)

  assume "Y \<subseteq> Z \<union> X\<cdot>Y" thus "Y \<subseteq> X\<^sup>\<omega> \<union> X\<^sup>\<star>\<cdot>Z"
    by - (simp only: omega_star_fuse, rule gfp_induct, auto, metis set_mp seq.mult_isol)
qed

lemma sumlist_cases [case_names LConsl LConsr LNil]:
  assumes c1: "(\<And>z zs. xs = LCons (Inl z) zs \<Longrightarrow> P)"
  and c2: "(\<And>z zs. xs = LCons (Inr z) zs \<Longrightarrow> P)"
  and c3: "xs = LNil \<Longrightarrow> P"
  shows "P"
proof (cases xs)
  case LNil from this and c3 show P by blast
next
  case (LCons x xs) from this and c1 c2 show P by (cases x) auto
qed

lemma llength_lr: "llength xs = llength (lfilter is_left xs) + llength (lfilter is_right xs)"
proof -
  have "(llength xs, llength (lfilter is_left xs) + llength (lfilter is_right xs)) \<in>
        {(llength xs, llength (lfilter is_left xs) + llength (lfilter is_right xs)) |xs::('a + 'b) llist. True}"
    by auto
  thus ?thesis
  proof(coinduct rule: enat_equalityI)
    case (Eqenat n m)
    from this[simplified] obtain xs :: "('a + 'b) llist"
    where [simp]: "n = llength xs"
    and [simp]: "m = llength (lfilter is_left xs) + llength (lfilter is_right xs)"
      by blast
    show ?case
      by (rule sumlist_cases[of xs]) (auto simp add: eSuc_plus iadd_Suc_right)
  qed
qed

lemma lfinite_lr: "lfinite (\<ll> zs) \<Longrightarrow> lfinite (\<rr> zs) \<Longrightarrow> lfinite zs"
  apply (drule lfinite_llength_enat)+
  apply (erule exE)+
  apply (rename_tac n m)
  apply (rule_tac n = "n + m" in llength_eq_enat_lfiniteD)
  apply (subst llength_lr)
  by (simp add: rights_def lefts_def)

lemma lfinite_shuffle: "lfinite xs \<Longrightarrow> lfinite ys \<Longrightarrow> zs \<in> xs \<sha> ys \<Longrightarrow> lfinite zs"
  by (auto intro: lfinite_lr simp add: tshuffle_words_def)

lemma LCons_tshuffle: "LCons x xs \<sha> LCons y ys = LCons (Inl x) ` (xs \<sha> LCons y ys) \<union> LCons (Inr y) ` (LCons x xs \<sha> ys)"
proof (auto simp add: tshuffle_words_def image_def)
  fix zs 
  assume zs_not_r: "\<forall>xa. \<rr> xa = ys \<longrightarrow>  \<ll> xa = LCons x xs \<longrightarrow> zs \<noteq> LCons (Inr y) xa"
  and zsl: "\<ll> zs = LCons x xs" and zsr: "\<rr> zs = LCons y ys"
  let ?goal = "\<exists>ws. \<ll> ws = xs \<and> \<rr> ws = LCons y ys \<and> zs = LCons (Inl x) ws"
  show ?goal
  proof (cases zs rule: sumlist_cases)
    case LNil
    from this and zsl
    have False
      by (metis LNil_not_LCons rights_LNil zsr)
    thus ?goal by blast
  next
    case (LConsl z' zs')
    from this and zsl zsr
    show ?goal
      by simp
  next
    case (LConsr z' zs')
    from this and zsl zsr zs_not_r
    have False
      by auto
    thus ?goal by blast
  qed
qed

lemma [simp]: "lmap \<langle>id,id\<rangle> ` LCons (Inl x) ` X = LCons x ` lmap \<langle>id,id\<rangle> ` X"
  by (auto simp add: image_def)

lemma [simp]: "lmap \<langle>id,id\<rangle> ` LCons (Inr x) ` X = LCons x ` lmap \<langle>id,id\<rangle> ` X"
  by (auto simp add: image_def)

lemma [simp]: "lmap \<langle>id,id\<rangle> ` (LCons (Inl x) ` (xs \<sha> LCons y ys) \<union> LCons (Inr y) ` (LCons x xs \<sha> ys))
              = (LCons x ` lmap \<langle>id,id\<rangle> ` (xs \<sha> LCons y ys) \<union> LCons y ` lmap \<langle>id,id\<rangle> ` (LCons x xs \<sha> ys))"
  by (simp add: image_Un)

lemma lfinite_lappend_shuffle: "lfinite xs \<Longrightarrow> xs \<frown> ys \<in> lmap \<langle>id,id\<rangle> ` (xs \<sha> ys)"
proof (induct xs arbitrary: ys rule: lfinite_induct)
  case Nil show ?case by simp
next
  case (Cons x xs) note ih_xs = this
  show ?case
  proof (cases ys, simp)
    fix z zs assume [simp]: "ys = LCons z zs"
    show "?case" using ih_xs
      by (simp add: LCons_tshuffle)
  qed
qed

lemma fin_l_prod: "X \<subseteq> FIN \<Longrightarrow> X \<cdot> Y = {xs \<frown> ys|xs ys. xs \<in> X \<and> ys \<in> Y}"
  by (auto simp add: FIN_def l_prod_def)

lemma fin_l_prod_le_shuffle: "X \<subseteq> FIN \<Longrightarrow> X \<cdot> Y \<subseteq> X \<parallel> Y"
  by (auto simp add: fin_l_prod shuffle_def FIN_def) (metis lfinite_lappend_shuffle mem_Collect_eq set_mp)

lemma fin_shuffle: "X \<subseteq> FIN \<Longrightarrow> Y \<subseteq> FIN \<Longrightarrow> X \<parallel> Y \<subseteq> FIN"
  by (auto simp add: shuffle_def FIN_def) (metis in_mono lfinite_shuffle mem_Collect_eq)

lemma word_exchange:
  assumes "lfinite a" and "lfinite b"
  shows "(lmap \<langle>id,id\<rangle> ` (a \<sha> b)) \<cdot> (lmap \<langle>id,id\<rangle> ` (c \<sha> d)) \<subseteq> lmap \<langle>id, id\<rangle> ` ((b \<frown> c) \<sha> (a \<frown> d))"
proof -
  have a: "lmap \<langle>id,id\<rangle> ` (a \<sha> b) \<subseteq> FIN"
    by (auto intro!: lfinite_shuffle assms simp add: FIN_def)
  have b: "\<And>z. {y. \<exists>x. \<ll> x = \<ll> z \<and> \<rr> x = \<rr> z \<and> y = lmap \<langle>id,id\<rangle> x} \<subseteq> FIN \<Longrightarrow> lfinite z"
    by (auto simp add: FIN_def)
  from a show ?thesis
    apply (auto dest!: b simp add: fin_l_prod tshuffle_words_def image_def)
    apply (rule_tac x = "lmap swap xa \<frown> xb" in exI)
    by (simp_all add: lefts_append rights_append lmap_lappend_distrib)
qed

lemma set_comp_mono4:
  assumes fg: "\<And>a b c d. a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> c \<in> C \<Longrightarrow> d \<in> D \<Longrightarrow> f a b c d \<subseteq> g a b c d"
  shows "\<Union>{f a b c d|a b c d. a \<in> A \<and> b \<in> B \<and> c \<in> C \<and> d \<in> D} \<subseteq> \<Union>{g a b c d|a b c d. a \<in> A \<and> b \<in> B \<and> c \<in> C \<and> d \<in> D}"
  using assms by blast

lemma exchange:
  assumes "A \<subseteq> FIN" and "B \<subseteq> FIN"
  shows "(A \<parallel> B) \<cdot> (C \<parallel> D) \<subseteq> (B \<cdot> C) \<parallel> (A \<cdot> D)"
proof -
  have "(A \<parallel> B) \<cdot> (C \<parallel> D) = {x \<frown> y|x y. x \<in> lmap \<langle>id, id\<rangle> ` (A \<Sha> B) \<and> y \<in> lmap \<langle>id, id\<rangle> ` (C \<Sha> D)}"
    by (simp add: fin_l_prod[OF fin_shuffle[OF assms(1) assms(2)]]) (simp add: shuffle_to_tshuffle)
  also have "... = {lmap \<langle>id,id\<rangle> x \<frown> lmap \<langle>id,id\<rangle> y|x y. x \<in> (A \<Sha> B) \<and> y \<in> (C \<Sha> D)}"
    by blast
  also have "... = \<Union>{{lmap \<langle>id,id\<rangle> x \<frown> lmap \<langle>id,id\<rangle> y|x y. x \<in> (a \<sha> b) \<and> y \<in> (c \<sha> d)}|a b c d. a \<in> A \<and> b \<in> B \<and> c \<in> C \<and> d \<in> D}"
    by (simp add: tshuffle_def) blast
  also have "... \<subseteq> \<Union>{(lmap \<langle>id,id\<rangle> ` (a \<sha> b)) \<cdot> (lmap \<langle>id,id\<rangle> ` (c \<sha> d))|a b c d. a \<in> A \<and> b \<in> B \<and> c \<in> C \<and> d \<in> D}"
    apply (rule set_comp_mono4)
    apply (subst fin_l_prod)
    apply (auto simp add: FIN_def)
    by (metis FIN_def assms(1) assms(2) lfinite_shuffle mem_Collect_eq set_mp)
  also have "... \<subseteq> \<Union>{lmap \<langle>id, id\<rangle> ` ((b \<frown> c) \<sha> (a \<frown> d))|a b c d. a \<in> A \<and> b \<in> B \<and> c \<in> C \<and> d \<in> D}"
     apply (rule set_comp_mono4)
     apply (rule word_exchange)
     apply (metis FIN_def assms(1) mem_Collect_eq set_mp)
     by (metis (full_types) FIN_def assms(2) mem_Collect_eq set_mp)
  also have "... = \<Union>{lmap \<langle>id, id\<rangle> ` (bc \<sha> ad)|bc ad. bc \<in> (B \<cdot> C) \<and> ad \<in> (A \<cdot> D)}"
    by (simp add: fin_l_prod[OF assms(2)] fin_l_prod[OF assms(1)]) blast
  also have "... = (B \<cdot> C) \<parallel> (A \<cdot> D)"
    by (simp add: shuffle_def)
  finally show ?thesis .
qed

lemma shuffle_inf_dist: "X \<parallel> (\<Union>\<YY>) = \<Union>{X \<parallel> Y |Y. Y \<in> \<YY>}"
  by (auto simp add: shuffle_def)

end
