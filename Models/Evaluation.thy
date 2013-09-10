theory Evaluation
  imports Language
begin

definition pow_inv :: "'a set \<Rightarrow> 'a lan" ("\<iota>") where
  "pow_inv X \<equiv> {xs. lset xs \<subseteq> X}"

definition symbols :: "'a lan \<Rightarrow> 'a set" ("\<rho>") where
  "symbols X \<equiv> \<Union>xs\<in>X. lset xs"

lemma galois_connection: "\<rho> X \<subseteq> Y \<longleftrightarrow> X \<subseteq> \<iota> Y"
  by (auto simp add: pow_inv_def symbols_def)

lemma \<rho>_iso: "X \<subseteq> Y \<Longrightarrow> \<rho> X \<subseteq> \<rho> Y"
  by (metis Int_absorb1 galois_connection le_infI1 order_refl)

lemma \<iota>_iso: "X \<subseteq> Y \<Longrightarrow> \<iota> X \<subseteq> \<iota> Y"
  by (metis galois_connection order_refl order_trans)

lemma (in complete_lattice) Inf_singleton: "Inf {x} = x"
  by (smt Inf_empty Inf_insert inf_top_right)

lemma lfinite_or_linfinite: "lfinite xs \<or> \<not> lfinite xs"
  by metis

lemma [simp]: "(R O S) `` X = S `` (R `` X)"
  by (auto simp add: image_def)

(* Evaluating finite words *)

definition eval_finite_word :: "'a rel list \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "eval_finite_word xs H \<equiv> foldr op O xs Id `` H"

lemma Inf_conj: "(\<And>n. P xs n \<Longrightarrow> Q xs n) \<Longrightarrow> Inf {enat n |n. P xs n \<and> Q xs n} = Inf {enat n |n. P xs n}"
  by (metis (hide_lams, mono_tags))

(* Lemmas about eval_finite_word *)

lemma efw_cons [simp]: "eval_finite_word (x # xs) X = eval_finite_word xs (x `` X)"
  by (auto simp add: eval_finite_word_def)

lemma efw_Nil [simp]: "eval_finite_word [] X = X"
  by (simp add: eval_finite_word_def)

lemma efw_empty [simp]: "eval_finite_word X {} = {}"
  by (simp add: eval_finite_word_def)

lemma efw_union [simp]: "eval_finite_word w (p \<union> q) = eval_finite_word w p \<union> eval_finite_word w q"
  by (auto simp add: eval_finite_word_def)

lemma efw_append [simp]: "eval_finite_word (xs @ ys) X = eval_finite_word ys (eval_finite_word xs X)"
  by (induct xs arbitrary: X) simp_all

lemma efw_append_empty: "eval_finite_word xs X = {} \<Longrightarrow> eval_finite_word (xs @ ys) X = {}"
  by simp

lemma efw_iso: "P \<subseteq> Q \<Longrightarrow> eval_finite_word xs P \<le> eval_finite_word xs Q"
  by (simp add: eval_finite_word_def) (metis Image_mono order_refl)

lemma Inf_enat_prop: "Inf {enat n|n. P n} = enat n \<Longrightarrow> P n"
  apply (subgoal_tac "{enat n|n. P n} \<noteq> {}")
  apply (smt Inf_empty Inf_enat_def Inf_mono LeastI_ex infinity_ileE mem_Collect_eq the_enat.simps)
  by (metis Inf_empty enat.distinct(1) top_enat_def)

lemma Inf_enat_pred_conj: "Inf {enat n|n. P n} \<le> Inf {enat n|n. P n \<and> Q n}"
  by (auto intro: Least_le LeastI2 simp add: Inf_enat_def)

definition steps :: "'a rel llist \<Rightarrow> 'a set \<Rightarrow> enat" where
  "steps xs H \<equiv> min (llength xs) (Inf {enat n|n. eval_finite_word (list_of (ltake (enat n) xs)) H = {}})"

lemma empty_eval_non_empty: "p \<noteq> {} \<Longrightarrow> eval_finite_word xs p = {} \<Longrightarrow> \<exists>x xs'. xs = x # xs'"
  by (cases xs) simp_all

lemma ltake_append_Suc [simp]: "ltake (enat n) (ltake (enat (Suc n)) xs) = ltake (enat n) xs"
  by (metis eSuc_enat ile_eSuc lappend_ltake_enat_ldropn le_cases ltake_all ltake_eq_ltake_antimono ltake_lappend1)

find_theorems "list_of" "op \<frown>"
  

lemma [simp]: "min n (Suc n) = n"
  by (simp add: min_def)

lemma efw_Suc:
  assumes "eval_finite_word (list_of (ltake (enat n) xs)) p = {}"
  shows "eval_finite_word (list_of (ltake (enat (Suc n)) xs)) p = {}"
proof -
  from assms
  have "eval_finite_word (list_of (ltake (enat n) (ltake (enat (Suc n)) xs))) p = {}"
    by simp
  hence "eval_finite_word (list_of (ltake (enat n) (ltake (enat (Suc n)) xs)) @ list_of (ldrop (enat n) (ltake (enat (Suc n)) xs))) p = {}"
    by (rule efw_append_empty)
  hence "eval_finite_word (list_of (ltake (enat n) (ltake (enat (Suc n)) xs) \<frown> ldrop (enat n) (ltake (enat (Suc n)) xs))) p = {}"
    by (simp add: list_of_lappend)
  thus "eval_finite_word (list_of (ltake (enat (Suc n)) xs)) p = {}"
    by (metis lappend_ltake_enat_ldropn ldrop.simps(1))
qed

lemma efw_plus_n:
  assumes "eval_finite_word (list_of (ltake (enat n) xs)) p = {}"
  shows "eval_finite_word (list_of (ltake (enat (n + n')) xs)) p = {}"  
proof (induct n')
  case 0 show ?case by (simp add: assms)
next
  case (Suc n) thus ?case by (metis add_Suc_right efw_Suc)
qed

definition true_above :: "(nat \<Rightarrow> bool) \<Rightarrow> bool" where
  "true_above P = (\<forall>n. P n \<longrightarrow> P (Suc n))"

lemma ta_pairs: "true_above P \<Longrightarrow> true_above Q \<Longrightarrow> (\<forall>n. P n \<longrightarrow> Q n) \<or> (\<forall>n. Q n \<longrightarrow> P n)"
  apply (auto simp add: true_above_def)
  apply (rename_tac m)
  apply (subgoal_tac "n \<le> m")
  apply (metis dec_induct)
  by (metis (full_types) dec_induct le_cases)

lemma conj_simpN1: "(\<forall>n. P n \<longrightarrow> Q n) \<Longrightarrow> P n \<and> Q n \<longleftrightarrow> P n" by auto
lemma conj_simpN2: "(\<forall>n. Q n \<longrightarrow> P n) \<Longrightarrow> P n \<and> Q n \<longleftrightarrow> Q n" by auto

lemma true_above_Inf:
  assumes "true_above P" and "true_above Q"
  shows "Inf {enat n|n. P n \<and> Q n} = Inf {enat n|n. P n} \<or> Inf {enat n|n. P n \<and> Q n} = Inf {enat n|n. Q n}"
  apply (rule disjE[OF ta_pairs[OF assms(1) assms(2)]])
  apply (subst conj_simpN1[where P = P and Q = Q])
  apply simp
  apply simp
  apply (subst conj_simpN2[where P = P and Q = Q]) back
  by auto

lemma true_above_Inf1:
  assumes "true_above P" and "true_above Q"
  and "Inf {enat n |n. P n} \<le> Inf {enat n |n. Q n}"
  shows "Inf {enat n|n. P n \<and> Q n} = Inf {enat n|n. Q n}"
proof -
  {
    assume "Inf {enat n|n. P n \<and> Q n} = Inf {enat n|n. Q n}"
    hence ?thesis
      by simp
  }
  moreover
  {
    assume case2: "Inf {enat n|n. P n \<and> Q n} = Inf {enat n|n. P n}"
    have "Inf {enat n |n. Q n} \<le> Inf {enat n|n. Q n \<and> P n}"
      by (rule Inf_enat_pred_conj)
    also have "... = Inf {enat n|n. P n}"
      by (simp add: case2 conj_commute)
    finally have ?thesis using case2 assms(3)
      by simp
  }
  ultimately show ?thesis
    using true_above_Inf[OF assms(1) assms(2)] by blast
qed

lemma true_above_Inf2:
  assumes "true_above P" and "true_above Q"
  and "Inf {enat n |n. Q n} \<le> Inf {enat n |n. P n}"
  shows "Inf {enat n|n. P n \<and> Q n} = Inf {enat n|n. P n}"
proof -
  {
    assume "Inf {enat n|n. P n \<and> Q n} = Inf {enat n|n. P n}"
    hence ?thesis
      by simp
  }
  moreover
  {
    assume case2: "Inf {enat n|n. P n \<and> Q n} = Inf {enat n|n. Q n}"
    have "Inf {enat n |n. P n} \<le> Inf {enat n|n. P n \<and> Q n}"
      by (rule Inf_enat_pred_conj)
    also have "... = Inf {enat n|n. Q n}"
      by (simp add: case2 conj_commute)
    finally have ?thesis using case2 assms(3)
      by simp
  }
  ultimately show ?thesis
    using true_above_Inf[OF assms(1) assms(2)] by blast
qed

lemma efw_true_above: "true_above (\<lambda>n. eval_finite_word (list_of (ltake (enat n) xs)) p = {})"
  by (auto simp add: true_above_def efw_Suc)

lemma steps_union:
  assumes "steps xs p = n" and "steps xs q = m"
  shows "steps xs (p \<union> q) = max n m"
proof -
  {
    assume "n \<le> m" and "Inf {enat n |n. eval_finite_word (list_of (ltake (enat n) xs)) p = {}} \<le> llength xs"
    hence "steps xs q = steps xs (p \<union> q)"
      apply (simp add: steps_def assms(1)[symmetric] assms(2)[symmetric])
      apply (rule arg_cong) back
      apply (subst true_above_Inf1[OF efw_true_above efw_true_above])
      apply simp_all
      by (metis (lifting) min_max.inf_absorb1 min_max.inf_commute)
    hence ?thesis
      by (metis `n \<le> m` assms(2) min_max.sup_absorb2)
  }
  moreover
  {
    assume "m \<le> n" and "Inf {enat n |n. eval_finite_word (list_of (ltake (enat n) xs)) q = {}} \<le> llength xs"
    hence "steps xs p = steps xs (p \<union> q)"
      apply (simp add: steps_def assms(1)[symmetric] assms(2)[symmetric])
      apply (rule arg_cong) back
      apply (subst true_above_Inf2[OF efw_true_above efw_true_above])
      apply simp_all
      by (metis (lifting) min_absorb2)
    hence ?thesis
      by (metis `m \<le> n` assms(1) min_max.sup_absorb1)
  }
  moreover
  {
    assume case3: "llength xs \<le> Inf {enat n |n. eval_finite_word (list_of (ltake (enat n) xs)) p = {}}"
    and "llength xs \<le> Inf {enat n |n. eval_finite_word (list_of (ltake (enat n) xs)) q = {}}"
    hence "n = llength xs" and "m = llength xs"
      using assms(1) assms(2)
      apply -
      apply (simp_all add: steps_def)
      by (metis (lifting) min_max.inf_absorb1)+
    moreover have "steps xs (p \<union> q) = llength xs"
      apply (simp add: steps_def)
      apply (rule min_absorb1)
      apply (rule order_trans[OF case3])
      by (rule Inf_enat_pred_conj)
    ultimately have ?thesis
      by simp
  }
  moreover have "n \<le> m \<and> Inf {enat n |n. eval_finite_word (list_of (ltake (enat n) xs)) p = {}} \<le> llength xs \<or>
    m \<le> n \<and> Inf {enat n |n. eval_finite_word (list_of (ltake (enat n) xs)) q = {}} \<le> llength xs \<or>
    llength xs \<le> Inf {enat n |n. eval_finite_word (list_of (ltake (enat n) xs)) p = {}} \<and>
    llength xs \<le> Inf {enat n |n. eval_finite_word (list_of (ltake (enat n) xs)) q = {}}"
    by (simp only: assms(1)[symmetric] assms(2)[symmetric] steps_def) (metis (lifting) min_def min_max.inf_le1)
  ultimately show ?thesis
    by blast
qed

lemma steps_LNil [simp]: "steps LNil H = 0"
  by (simp add: steps_def)

lemma steps_empty [simp]: "steps xs {} = 0"
  apply (simp add: steps_def eval_finite_word_def)
  apply (subgoal_tac "0 \<in> {n'. \<exists>n. n' = enat n}")
  apply (metis (mono_tags) Inf_insert inf_enat_def insert_absorb min_enat_simps(2) min_enat_simps(3))
  by (simp add: zero_enat_def)

lemma steps_mono: "P \<subseteq> Q \<Longrightarrow> steps xs P \<le> steps xs Q"
  by (auto intro!: order_trans[OF min_max.inf_le2] Inf_superset_mono simp add: steps_def eval_finite_word_def)

lemma finite_steps:
  assumes "steps xs H = enat n"
  shows "(llength xs = enat n) \<or> (eval_finite_word (list_of (ltake (enat n) xs)) H = {})"
proof (cases "llength xs \<le> Inf {enat n |n. eval_finite_word (list_of (ltake (enat n) xs)) H = {}}")
  case True note c = this
  hence "steps xs H = llength xs"
    by (simp add: steps_def min_absorb1[OF c])
  thus ?thesis
    by (metis assms)
next
  case False
  hence c: "Inf {enat n |n. eval_finite_word (list_of (ltake (enat n) xs)) H = {}} \<le> llength xs"
    by (metis (lifting, no_types) le_cases)
  hence "Inf {enat n |n. eval_finite_word (list_of (ltake (enat n) xs)) H = {}} = enat n"
    by (simp add: steps_def min_absorb2[OF c] assms(1)[symmetric])
  note this = Inf_enat_prop[OF this]
  thus ?thesis
    by auto
qed 

lemma assumes "steps xs p = n" and "steps ys p = m" shows "steps (xs \<frown> ys) p \<le> n + m"
  sorry

datatype 'a top = Top | NotTop 'a

abbreviation bind :: "'a top \<Rightarrow> ('a \<Rightarrow> 'b top) \<Rightarrow> 'b top" where
  "bind x f \<equiv> case x of Top \<Rightarrow> Top | NotTop x \<Rightarrow> f x"

lemma top_left_id: "bind (NotTop x) f = f x"
  by auto

lemma top_right_id: "bind x NotTop = x"
  by (cases x) auto

lemma top_assoc: "bind (bind x f) g = bind x (\<lambda>x. bind (f x) g)"
  by (cases x) auto

instantiation top :: (ord) ord
begin
  definition less_eq_top :: "'a top \<Rightarrow> 'a top \<Rightarrow> bool" where
    "x \<le> y \<equiv> case y of Top \<Rightarrow> True | NotTop y \<Rightarrow> case x of Top \<Rightarrow> False | NotTop x \<Rightarrow> x \<le> y"

  definition less_top :: "'a top \<Rightarrow> 'a top \<Rightarrow> bool" where
    "less_top x y \<equiv> x \<le> y \<and> \<not> (y \<le> x)"

  instance by default
end

instance top :: (order) order
proof
  fix x y z :: "'a top"
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (simp add: less_top_def)
  show "x \<le> x"
    by (cases x) (auto simp add: less_eq_top_def)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    apply (cases x)
    apply (cases y, cases z, (force simp add: less_eq_top_def)+)
    apply (cases y, cases z, (force simp add: less_eq_top_def)+)
    by (cases z, (force simp add: less_eq_top_def)+)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (cases x) (cases y, (force simp add: less_eq_top_def)+)+
qed

lemma NotTop_mono [intro!]: "x \<le> y \<Longrightarrow> NotTop x \<le> NotTop y"
  by (auto simp add: less_eq_top_def)

instantiation top :: (lattice) lattice
begin
  definition sup_top :: "'a top \<Rightarrow> 'a top \<Rightarrow> 'a top" where
    "sup_top x y \<equiv> case x of Top \<Rightarrow> Top | NotTop x \<Rightarrow> (case y of Top \<Rightarrow> Top | NotTop y \<Rightarrow> NotTop (sup x y))"

  definition inf_top :: "'a top \<Rightarrow> 'a top \<Rightarrow> 'a top" where
    "inf_top x y \<equiv> case x of Top \<Rightarrow> y | NotTop x \<Rightarrow> (case y of Top \<Rightarrow> NotTop x | NotTop y \<Rightarrow> NotTop (inf x y))"  

  instance
  proof
    fix x y z :: "'a top"
    show "inf x y \<le> x"
      sorry
    show "inf x y \<le> y"
      sorry
    show "x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> inf y z"
      sorry
    show "x \<le> sup x y"
      sorry
    show "y \<le> sup x y"
      sorry
    show "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> sup y z \<le> x"
      sorry
  qed
end

instantiation top :: (complete_lattice) complete_lattice
begin
  definition Inf_top :: "'a top set \<Rightarrow> 'a top" where "Inf_top \<equiv> undefined"

  definition Sup_top :: "'a top set \<Rightarrow> 'a top" where "Sup_top X \<equiv> if Top \<in> X then Top else NotTop (Sup {x. NotTop x \<in> X})"

  definition top_top :: "'a top" where "top_top = Top"

  definition bot_top :: "'a top" where "bot_top = NotTop bot"

  instance
  proof
    fix a :: "'a top"
    show "a \<le> top"
      by (cases a) (auto simp add: top_top_def less_eq_top_def)
    show "bot \<le> a"
      by (cases a) (auto simp add: bot_top_def less_eq_top_def)
  next
    fix x :: "'a top" and A :: "'a top set"
    assume xA: "x \<in> A"
    show "Inf A \<le> x"
      sorry
    show "x \<le> Sup A"
      by (insert xA, cases x, auto intro: Sup_upper simp add: Sup_top_def less_eq_top_def) 
  next
    fix z :: "'a top" and A :: "'a top set"
    assume "\<And>x. x \<in> A \<Longrightarrow> z \<le> x"
    thus "z \<le> Inf A"
      sorry
  next
    fix z :: "'a top" and A :: "'a top set"
    assume "\<And>x. x \<in> A \<Longrightarrow> x \<le> z"
    thus "Sup A \<le> z"
      apply (cases z)
      apply (auto intro!: Sup_least simp add: Sup_top_def less_eq_top_def)
      apply (metis top.simps(4))
      by (metis (full_types) top.simps(5))
  qed
end

lemma [simp]: "bind top x = top" sorry

definition eval_word :: "'a rel llist \<Rightarrow> 'a set \<Rightarrow> 'a set top" where
  "eval_word xs H \<equiv> case steps xs H of \<infinity> \<Rightarrow> top | enat n \<Rightarrow> NotTop (eval_finite_word (list_of (ltake (enat n) xs)) H)"

definition module :: "'a rel lan \<Rightarrow> 'a set top \<Rightarrow> 'a set top" (infix "\<Colon>" 60) where
  "x \<Colon> h \<equiv> Sup {bind h (eval_word w)|w. w \<in> x}"

definition llist_nabla :: "'a rel llist \<Rightarrow> 'a set" where
  "llist_nabla xs \<equiv> {\<sigma>. steps xs {\<sigma>} = \<infinity>}"

definition nabla :: "'a rel lan \<Rightarrow> 'a set top" ("\<nabla>_" [1000] 1000)  where
  "\<nabla>X = NotTop (\<Union>{llist_nabla xs|xs. xs \<in> X})"

lemma eval_word_iso:
  assumes "P \<subseteq> Q"
  shows "eval_word xs P \<le> eval_word xs Q"
proof (cases "steps xs Q")
  case (enat n) note Q_steps[simp] = this
  hence "steps xs P \<le> enat n"
    by (metis (full_types) assms steps_mono)
  then obtain m where P_steps[simp]: "steps xs P = enat m" and "enat m \<le> enat n"
    by (metis enat_ile)
  thus ?thesis
    apply (simp add: eval_word_def)
    by (metis (full_types) NotTop_mono P_steps `steps xs P \<le> enat n` assms bot_least efw_iso finite_steps ltake_all order_refl)
next
  case infinity
  thus ?thesis
    by (simp add: eval_word_def)
qed

thm inf_sup_ord(2)
find_theorems "min ?x ?y \<le> ?y"

lemma steps_singleton: "\<sigma> \<in> P \<Longrightarrow> steps xs {\<sigma>} = n \<Longrightarrow> n \<le> steps xs P"
  apply (auto simp add: steps_def)
  apply (rule order_trans[OF min_max.inf_le2])
  apply (rule Inf_superset_mono)
  apply safe
  apply (rule_tac x = n in exI)
  apply (intro conjI)
  apply simp
  by (metis empty_subsetI efw_iso insert_absorb insert_mono subset_empty)

lemma non_terminating_word: "\<nabla>X \<noteq> bot \<Longrightarrow> \<exists>xs\<in>X. \<exists>\<sigma>. steps xs {\<sigma>} = \<infinity>" 
  by (auto simp add: nabla_def llist_nabla_def bot_top_def)

lemma (in complete_lattice) Sup_top_eq_top: "top \<in> A \<Longrightarrow> Sup A = top"
  by (metis Sup_upper top_unique)

lemma eval_word_top: "eval_word xs H = top \<longleftrightarrow> steps xs H = \<infinity>"
  apply (auto simp add: eval_word_def)
  apply (cases "steps xs H")
  apply auto
  by (metis top.distinct(1) top_top_def)

lemma "\<nabla>x \<noteq> bot \<Longrightarrow> x \<Colon> \<nabla>x = top"
proof -
  assume nabla_non_empty: "\<nabla>x \<noteq> bot"
  have "Sup {bind \<nabla>x (eval_word w) |w. w \<in> x} = top"
  proof (auto intro!: Sup_top_eq_top, subst eq_commute)
    obtain w and \<sigma> where wx: "w \<in> x" and w_steps: "steps w {\<sigma>} = \<infinity>"
      by (metis nabla_non_empty non_terminating_word)
    have "\<infinity> \<le> steps w (\<Union>{{\<sigma>. steps w {\<sigma>} = \<infinity>}|w. w \<in> x})"
      apply (rule steps_singleton[OF _ w_steps])
      apply auto
      by (metis (lifting, full_types) mem_Collect_eq w_steps wx)
    hence "bind \<nabla>x (eval_word w) = top"
      by (auto simp add: nabla_def llist_nabla_def eval_word_top)
    thus "\<exists>w. bind \<nabla>x (eval_word w) = top \<and> w \<in> x"
      by (metis wx)
  qed
  thus ?thesis
    by (simp add: nabla_def module_def)
qed

lemmas Top_top = top_top_def[symmetric]

lemma [simp]: "Top \<le> NotTop x \<longleftrightarrow> False"
  by (simp add: less_eq_top_def)

lemma [simp]: "NotTop x \<le> NotTop y \<longleftrightarrow> x \<subseteq> y"
  by (simp add: less_eq_top_def)

notation sup (infixl "\<squnion>" 60)

lemma mod_isol: "p \<le> q \<Longrightarrow> x \<Colon> p \<le> x \<Colon> q"
  apply (cases q)
  apply (auto simp add: module_def)
  apply (rule Sup_mono)
  apply (auto simp add: Top_top)
  apply (cases p)
  apply auto
  apply (rule Sup_mono)
  apply auto
  apply (rule_tac x = "eval_word w a" in exI)
  apply (intro conjI)
  apply auto
  by (metis eval_word_iso)

lemma "(x \<Colon> p) \<squnion> (x \<Colon> q) \<le> x \<Colon> (p \<squnion> q)"
  by (rule mono_sup) (auto intro: mod_isol simp add: mono_def)

lemma [simp]: "bind top (eval_word w) = top"
  by (simp add: Top_top[symmetric])

declare Top_top[simp]

lemma [simp]: "x \<noteq> {} \<Longrightarrow> x \<Colon> top = top"
  by (auto intro!: Sup_top_eq_top simp add: module_def)

lemma [simp]: "{} \<Colon> p = bot"
  by (simp add: module_def)

lemma [simp]: "NotTop x \<squnion> NotTop y = NotTop (x \<union> y)"
  by (simp add: sup_top_def)

lemma ltake_llength [simp]: "ltake (llength w) w = w"
  by (metis ltake_all order_refl)

lemma (in linorder) linearD: "\<not> m \<le> n \<Longrightarrow> n \<le> m"
  by (metis linear)

(* FIXME: Isarify *)

lemma efw_steps: "steps w p = enat n \<Longrightarrow> eval_finite_word (list_of (ltake (enat (max n m)) w)) p = eval_finite_word (list_of (ltake (enat n) w)) p"
  apply (cases "m \<le> n")
  apply (drule max_absorb1)
  apply (rotate_tac 1)
  apply (erule ssubst)
  apply (rule refl)
  apply (subst max_absorb2)
  apply (erule linearD)
  apply (drule linearD)
  apply (subst lappend_ltake_ldrop[where n = "enat n" and xs = "ltake (enat m) w", symmetric])
  apply (subst list_of_lappend)
  apply (subst lfinite_ltake)
  apply (rule disjI2)
  apply (subst enat_ord_code(4))
  apply (rule TrueI)
  apply (subst ldrop.simps(1))
  apply (subst lfinite_ldropn)
  apply (subst lfinite_ltake)
  apply (rule disjI2)
  apply (subst enat_ord_code(4))
  apply (rule TrueI)
  apply (drule finite_steps)
  apply (erule disjE)
  apply (subst ltake_all)
  apply (metis llength_lsublist_ile lsublist_upt_eq_ltake)
  apply (subst ltake_all)
  apply (metis enat_ord_simps(1))
  apply (subst ltake_all)
  apply (metis enat_ord_simps(1))
  apply (subst ldrop_all)
  apply (metis order_refl)
  apply (subst ltake_all)
  apply (metis order_refl)
  apply simp
  apply (subst efw_append_empty)
  apply (subst ltake_ltake)
  apply (subst min_absorb1)
  apply (subst enat_ord_simps(1))
  apply assumption
  apply simp_all
  done

lemma eval_word_union [simp]: "eval_word w (p \<union> q) = eval_word w p \<squnion> eval_word w q"
proof -
  {
    assume [simp]: "steps w p = \<infinity>"
    hence [simp]: "steps w (p \<union> q) = \<infinity>"
      apply (subgoal_tac "steps w p \<le> steps w (p \<union> q)")
      apply (metis enat_ord_simps(5))
      apply (rule steps_mono)
      by auto
    have ?thesis
      by (auto simp add: eval_word_def)
  }
  moreover
  {
    assume [simp]: "steps w q = \<infinity>"
    hence [simp]: "steps w (p \<union> q) = \<infinity>"
      apply (subgoal_tac "steps w q \<le> steps w (p \<union> q)")
      apply (metis enat_ord_simps(5))
      apply (rule steps_mono)
      by auto
    have ?thesis
      by (auto simp add: eval_word_def)
  }
  moreover
  {
    fix n m
    assume [simp]: "steps w p = enat n" and [simp]: "steps w q = enat m"
    hence [simp]: "steps w (p \<union> q) = enat (max n m)"
      by (metis max_enat_simps(1) steps_union)
    have ?thesis
      apply (simp add: eval_word_def)
      apply (subst efw_steps, simp)
      apply (subst min_max.sup.commute)
      apply (subst efw_steps, simp)
      by simp
  }
  ultimately show ?thesis
    by (metis not_enat_eq)
qed
  
lemma [simp]: "top \<le> NotTop x \<longleftrightarrow> False"
  by (metis top.distinct(1) top_top_def top_unique)

lemma eval_word_sup [simp]: "bind (sup p q) (eval_word w) = sup (bind p (eval_word w)) (bind q (eval_word w))"
  apply (cases p)
  apply (simp add: Top_top)
  apply (cases q)
  by (simp_all add: Top_top eval_word_union)

find_theorems "_ \<le> Sup _"
find_theorems "Sup _ \<in> _"
thm bind_def



lemma "(\<And>x. x \<in> X \<Longrightarrow> f x \<le> g x) \<Longrightarrow> Sup {f x |x. x \<in> X} \<le> Sup {g x |x. x \<in> X}"
  sorry

lemma "top \<notin> X" sorry

lemma steps_super_inf: "steps w p = \<infinity> \<Longrightarrow> p \<subseteq> q \<Longrightarrow> steps w q = \<infinity>"
  by (metis enat_ord_code(3) steps_mono top_le)

lemma [simp]: "NotTop x = top \<longleftrightarrow> False"
  by (metis top.distinct(1) top_top_def)

lemma assumes "eval_word w x = top" and "x \<in> X" shows "steps w (\<Union>X) = \<infinity>"
proof -
  {
    assume "steps w x = \<infinity>"
    from this and assms have ?thesis
      by (auto elim: steps_super_inf)
  }
  moreover
  {
    fix n
    assume "steps w x = enat n"
    from this and assms have ?thesis
      by (simp add: eval_word_def)
  }
  ultimately show ?thesis
    by (metis not_enat_eq)
qed

lemma "eval_word w (\<Union>X) = Sup (eval_word w ` X)"
  apply (simp add: Sup_top_def)
  apply auto
  apply (subgoal_tac "steps w (\<Union>X) = \<infinity>")
  apply (simp add: eval_word_def)
  apply (simp add: eval_word_def)

lemma "join_preserving (\<lambda>x. bind x (eval_word w))"
  apply (simp add: join_preserving_def image_def Sup_top_def)
  apply auto

lemma "(x \<Colon> NotTop p) \<squnion> (x \<Colon> NotTop q) \<le> x \<Colon> (NotTop p \<squnion> NotTop q)"
proof (auto simp add: module_def)
  {
    assume "eval_word w p \<le> eval_word w q"

lemma "x \<cdot> y \<Colon> h = y \<Colon> (x \<Colon> h)"
proof -
  have "x \<cdot> y \<Colon> h = Sup {bind h (eval_word w) |w. w \<in> x \<cdot> y}"
    by (simp add: module_def)
  also have "... = Sup {bind h (eval_word (xw \<frown> yw))|xw yw. xw \<in> x \<and> yw \<in> y}"
    apply (auto simp add: l_prod_def)
    apply (rule antisym)
    apply (rule Sup_mono)
    apply auto
    apply (rule_tac x = "bind h (eval_word w)" in exI)
    apply (intro conjI)
    apply (rule_tac x = w in exI)
    sledgehammer
end

end
