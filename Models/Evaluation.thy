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

abbreviation "eval_prefix n xs \<equiv> eval_finite_word (list_of (ltake (enat n) xs))"

definition steps2 :: "'a rel llist \<Rightarrow> 'a set \<Rightarrow> enat" where
  "steps2 xs H = Inf {enat n |n. eval_prefix n xs H = eval_prefix (Suc n) xs H}" 

lemma empty_eval_non_empty: "p \<noteq> {} \<Longrightarrow> eval_finite_word xs p = {} \<Longrightarrow> \<exists>x xs'. xs = x # xs'"
  by (cases xs) simp_all

lemma ltake_append_Suc [simp]: "ltake (enat n) (ltake (enat (Suc n)) xs) = ltake (enat n) xs"
  by (metis eSuc_enat ile_eSuc lappend_ltake_enat_ldropn le_cases ltake_all ltake_eq_ltake_antimono ltake_lappend1)

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

lemma steps_singleton: "\<sigma> \<in> P \<Longrightarrow> steps xs {\<sigma>} = n \<Longrightarrow> n \<le> steps xs P"
  apply (auto simp add: steps_def)
  apply (rule order_trans[OF min_max.inf_le2])
  apply (rule Inf_superset_mono)
  apply safe
  apply (rule_tac x = n in exI)
  apply (intro conjI)
  apply simp
  by (metis empty_subsetI efw_iso insert_absorb insert_mono subset_empty)

datatype 'a top = Top | NotTop 'a

abbreviation bind :: "('a \<Rightarrow> 'b top) \<Rightarrow> 'a top \<Rightarrow> 'b top" (infixr "\<hookleftarrow>" 56)  where
  "bind f x \<equiv> case x of Top \<Rightarrow> Top | NotTop x \<Rightarrow> f x"

lemma top_left_id: "f \<hookleftarrow> NotTop x = f x"
  by auto

lemma top_right_id: "NotTop \<hookleftarrow> x = x"
  by (cases x) auto

lemma top_assoc: "g \<hookleftarrow> f \<hookleftarrow> x = (\<lambda>x. g \<hookleftarrow> (f x)) \<hookleftarrow> x"
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

lemma [simp]: "f \<hookleftarrow> top = top" by (simp add: top_top_def)

definition eval_word :: "'a rel llist \<Rightarrow> 'a set \<Rightarrow> 'a set top" where
  "eval_word xs H \<equiv> case steps xs H of \<infinity> \<Rightarrow> top | enat n \<Rightarrow> NotTop (eval_finite_word (list_of (ltake (enat n) xs)) H)"

definition module :: "'a rel lan \<Rightarrow> 'a set top \<Rightarrow> 'a set top" (infix "\<Colon>" 60) where
  "x \<Colon> h \<equiv> Sup {eval_word w \<hookleftarrow> h|w. w \<in> x}"

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

lemma non_terminating_word: "\<nabla>X \<noteq> bot \<longleftrightarrow> (\<exists>xs\<in>X. \<exists>\<sigma>. steps xs {\<sigma>} = \<infinity>)" 
  by (auto simp add: nabla_def llist_nabla_def bot_top_def)

lemma all_terminating_word1: "\<nabla>X = bot \<longleftrightarrow> \<not> (\<exists>xs\<in>X. \<exists>\<sigma>. steps xs {\<sigma>} = \<infinity>)"
  by (simp add: arg_cong[OF non_terminating_word, of Not, simplified])

lemmas all_terminating_word = all_terminating_word1[simplified]

lemma [simp]: "inf (NotTop x) (NotTop y) = NotTop (x \<inter> y)"
  by (simp add: inf_top_def)

lemma [simp]: "NotTop x = bot \<longleftrightarrow> x = {}"
  by (simp add: bot_top_def)

lemma non_terminating_word_var: "inf (\<nabla>X) (NotTop Y) \<noteq> bot \<longleftrightarrow> (\<exists>xs\<in>X. \<exists>\<sigma>\<in>Y. steps xs {\<sigma>} = \<infinity>)" 
  by (auto simp add: nabla_def llist_nabla_def)

lemma all_terminating_word_var1: "inf (\<nabla>X) (NotTop Y) = bot \<longleftrightarrow> \<not> (\<exists>xs\<in>X. \<exists>\<sigma>\<in>Y. steps xs {\<sigma>} = \<infinity>)" 
  by (simp add: arg_cong[OF non_terminating_word_var, of Not, simplified])

lemmas all_terminating_word_var = all_terminating_word_var1[simplified]

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
  have "Sup {eval_word w \<hookleftarrow> \<nabla>x |w. w \<in> x} = top"
  proof (auto intro!: Sup_top_eq_top, subst eq_commute)
    obtain w and \<sigma> where wx: "w \<in> x" and w_steps: "steps w {\<sigma>} = \<infinity>"
      by (metis nabla_non_empty non_terminating_word)
    have "\<infinity> \<le> steps w (\<Union>{{\<sigma>. steps w {\<sigma>} = \<infinity>}|w. w \<in> x})"
      apply (rule steps_singleton[OF _ w_steps])
      apply auto
      by (metis (lifting, full_types) mem_Collect_eq w_steps wx)
    hence "eval_word w \<hookleftarrow> \<nabla>x = top"
      by (auto simp add: nabla_def llist_nabla_def eval_word_top)
    thus "\<exists>w. eval_word w \<hookleftarrow> \<nabla>x = top \<and> w \<in> x"
      by (metis wx)
  qed
  thus ?thesis
    apply (cases "\<nabla>x = NotTop {}")
    by (simp_all add: nabla_def module_def)
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

lemma mod_isor: "x \<le> y \<Longrightarrow> x \<Colon> p \<le> y \<Colon> p"
  apply (simp add: module_def)
  apply (rule Sup_mono)
  by auto

lemma mod_distl: "(x \<Colon> p) \<squnion> (x \<Colon> q) \<le> x \<Colon> (p \<squnion> q)"
  by (rule mono_sup) (auto intro: mod_isol simp add: mono_def)

lemma mod_distr: "(x \<union> y) \<Colon> p = (x \<Colon> p) \<squnion> (y \<Colon> p)"
  by (auto intro: arg_cong[where f = Sup] simp add: module_def Sup_union_distrib[symmetric])

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

lemma eval_word_sup [simp]: "eval_word w \<hookleftarrow> sup p q = sup (eval_word w \<hookleftarrow> p) (eval_word w \<hookleftarrow> q)"
  apply (cases p)
  apply simp
  apply (cases q)
  by simp_all

lemma steps_super_inf: "steps w p = \<infinity> \<Longrightarrow> p \<subseteq> q \<Longrightarrow> steps w q = \<infinity>"
  by (metis enat_ord_code(3) steps_mono top_le)

lemma [simp]: "NotTop x = top \<longleftrightarrow> False"
  by (metis top.distinct(1) top_top_def)

lemma eval_word_super_top: "eval_word w p = top \<Longrightarrow> p \<subseteq> q \<Longrightarrow> steps w q = \<infinity>"
  by (metis eval_word_top steps_super_inf)

lemma efw_continuous: "eval_finite_word w (\<Union>X) = \<Union>(eval_finite_word w ` X)"
  by (auto simp add: eval_finite_word_def Image_def)

lemma NT_eq_simp [simp]: "NotTop x = (case m of enat n \<Rightarrow> NotTop (f n) | \<infinity> \<Rightarrow> top) \<longleftrightarrow> (\<exists>n. m = enat n \<and> x = f n)"
  apply default
  apply (cases m)
  apply simp
  apply simp
  apply (erule exE)
  apply (erule conjE)
  by simp

lemma finite_steps_super: "steps w p = enat n \<Longrightarrow> q \<subseteq> p \<Longrightarrow> steps w q \<le> enat n"
  by (metis (full_types) steps_mono)

lemma finite_steps_super_var: "steps w p = enat n \<Longrightarrow> q \<subseteq> p \<Longrightarrow> \<exists>m. steps w q = enat m \<and> m \<le> n"
  by (metis enat.exhaust enat_ord_simps(1) enat_ord_simps(5) steps_mono)

lemma [simp]: "top \<noteq> (case m of enat n \<Rightarrow> NotTop (g n) | \<infinity> \<Rightarrow> top) \<longleftrightarrow> m \<noteq> \<infinity>"
  apply (cases m)
  apply simp
  apply (metis top.distinct(1) top_top_def)
  by simp

lemma [simp]: "top = (case m of enat n \<Rightarrow> NotTop (g n) | \<infinity> \<Rightarrow> top) \<longleftrightarrow> m = \<infinity>"
  apply (cases m)
  apply simp
  apply (metis top.distinct(1) top_top_def)
  by simp

lemma (in complete_lattice) Sup_or [simp]: "Sup {f x|x. P x \<or> Q x} = (Sup {f x|x. P x} \<squnion> Sup {f x|x. Q x})"
  apply (subst Sup_union_distrib[symmetric])
  apply (rule arg_cong) back
  apply auto
  done

lemma fin_inf_split: "x = x \<cdot> {} \<union> (x \<inter> FIN)"
  by (auto simp add: l_prod_def FIN_def)

lemma (in complete_lattice) Sup_single_var: "X \<noteq> {} \<Longrightarrow> (\<forall>x'\<in>X. x' = x) \<Longrightarrow> Sup X = x"
  apply (subgoal_tac "X = {x}")
  apply (metis Sup_eq_equiv equals0I)
  by auto

lemma "(\<exists>xs\<in>X. \<forall>n. steps xs h \<noteq> enat n) \<longleftrightarrow> (\<exists>xs\<in>X. steps xs h = \<infinity>)"
  by auto

lemma INF_part_mod1: assumes "X \<cdot> {} \<noteq> {}" shows "(X \<cdot> {} \<Colon> (NotTop h) = top) \<or> (X \<cdot> {} \<Colon> (NotTop h) = NotTop {})" 
proof -
  {
    assume "\<forall>xs\<in>(X \<cdot> {}). \<exists>n. steps xs h = enat n" and "X \<cdot> {} \<noteq> {}"
    hence "X \<cdot> {} \<Colon> (NotTop h) = NotTop {}"
      apply (simp add: l_prod_def module_def eval_word_def)
      apply (rule Sup_single_var)
      apply simp
      apply (erule exE)+
      apply (erule conjE)
      by (smt enat.distinct(1) enat.simps(4) finite_steps mem_Collect_eq not_lfinite_llength)
  }
  moreover
  {
    assume "\<not> (\<forall>xs\<in>(X \<cdot> {}). \<exists>n. steps xs h = enat n)" and "X \<cdot> {} \<noteq> {}"
    hence "X \<cdot> {} \<Colon> (NotTop h) = top"
      apply (simp add: l_prod_def module_def eval_word_def)
      apply (rule Sup_top_eq_top)
      by auto
  }
  ultimately show ?thesis
    by (metis assms)
qed

lemma mod_top [simp]: "X \<noteq> {} \<Longrightarrow> X \<Colon> top = top"
  by (auto intro: Sup_top_eq_top simp: module_def)

lemma [simp]: "X \<Colon> bot = bot"
  apply (auto simp add: module_def bot_top_def eval_word_def enat_0[symmetric])
  apply (cases "X = {}")
  apply (simp add: bot_top_def)
  apply (rule Sup_single_var)
  apply (subgoal_tac "\<exists>w. w \<in> X")
  apply simp
  apply (metis all_not_in_conv assms)
  by auto

lemma infinite_eval_cases: "X \<cdot> {} \<Colon> h = top \<or> X \<cdot> {} \<Colon> h = bot"
  apply (cases "X \<cdot> {} = {}")
  apply simp
  apply (cases h)
  apply simp
  apply (simp add: bot_top_def)
  apply (rule INF_part_mod1)
  by auto

lemma "y \<noteq> {} \<Longrightarrow> (x \<cdot> {} \<Colon> h) = y \<Colon> (x \<cdot> {} \<Colon> h)"
  by (rule disjE[OF infinite_eval_cases[of x h]]) simp_all

lemma eval_word_finite: "lfinite w \<Longrightarrow> eval_word w h = NotTop (eval_finite_word (list_of w) h)"
  apply (simp add: eval_word_def)
  apply (rule sym)
  apply simp
  apply (simp add: steps_def)
  apply (cases "llength w \<le> Inf {enat n |n. eval_finite_word (list_of (ltake (enat n) w)) h = {}}")
  apply (subst min_max.inf_absorb1)
  apply assumption
  apply (metis lfinite_llength_enat ltake_llength)
  apply (drule linearD)
  apply (subst min_max.inf_absorb2)
  apply simp
  apply (simp add: lfinite_conv_llength_enat)
  apply (erule exE)
  sorry

lemma helper: "(\<And>x. P x \<Longrightarrow> f x = g x) \<Longrightarrow> (\<And>x. Q x \<Longrightarrow> P x) \<Longrightarrow> {f x |x. Q x} = {g x |x. Q x}"
  by auto metis

lemma NotTop_continuous: "NotTop (\<Union>X) = Sup (NotTop ` X)"
  by (auto simp add: Sup_top_def) (metis top.distinct(1) top_top_def)

lemma [simp]: "f ` {g x |x. P x} = {f (g x) |x. P x}"
  by (auto simp add: image_def)

thm arg_cong

lemma "x \<inter> FIN \<Colon> (NotTop h) = NotTop (\<Union>{eval_finite_word (list_of w) h |w. w \<in> x \<and> w \<in> FIN})"
  by (auto intro: arg_cong[where f = Sup] eval_word_finite eval_word_finite[symmetric] simp: module_def FIN_def NotTop_continuous)

lemma (in complete_lattice) Sup_eq_bot: "X = {} \<Longrightarrow> Sup X = bot"
  by simp

lemma [simp]: "inf (NotTop p) (NotTop q) = NotTop (p \<inter> q)"
  by (simp add: inf_top_def)

lemma [simp]: "\<Union>X \<inter> Y = {} \<longleftrightarrow> (\<forall>X'\<in>X. X' \<inter> Y = {})"
  by auto

lemma [simp]: "top = bot \<longleftrightarrow> False"
  sorry

lemma [intro!]: "\<exists>m'. m = enat m' \<and> f m' = Y \<Longrightarrow> (case m of enat n \<Rightarrow> NotTop (f n) | \<infinity> \<Rightarrow> top) = NotTop Y"
  apply (cases m)
  by auto

lemma Sup_steps: "Sup (steps w ` X) \<le> steps w (\<Union>X)"
  apply (auto simp add: steps_def image_def Sup_le_iff le_Inf_iff efw_continuous)
  apply (erule_tac x = "eval_finite_word (list_of (ltake (enat n) w)) x" in allE)
  apply (erule impE)
  apply (rule_tac x = x in bexI)
  apply simp_all
  apply (subst min_le_iff_disj)
  apply (rule disjI2)
  apply (rule Inf_lower)
  by simp

lemma steps_Union_infinity: "\<exists>x\<in>X. steps w x = \<infinity> \<Longrightarrow> steps w (\<Union>X) = \<infinity>"
  apply (subst enat_ord_simps(5)[symmetric])
  apply (rule order_trans[OF _ Sup_steps])
  apply (rule Sup_upper)
  by (auto intro!: bexI simp add: image_def)

lemma [iff]: "min (x::enat) y = \<infinity> \<longleftrightarrow> x = \<infinity> \<and> y = \<infinity>"
  apply auto
  apply (metis enat_ord_simps(5) min_enat_simps(4) min_max.inf_le2)
  by (metis enat_ord_simps(5) min_max.inf_le2)

lemma (in complete_lattice) Inf_eq_top: "X = {} \<Longrightarrow> Inf X = top"
  by auto

lemma Inf_eq_infinity: "X = {} \<Longrightarrow> Inf X = (\<infinity>::enat)"
  by (auto simp: top_enat_def)

lemma Inf_eq_infinity_bexI: "\<exists>x\<in>X. f x = {} \<Longrightarrow> \<exists>x\<in>X. Inf (f x) = (\<infinity>::enat)"
  apply auto
  apply (rule_tac x = x in bexI)
  by (simp_all add: top_enat_def)

lemma [iff]: "Inf X = (\<infinity>::enat) \<longleftrightarrow> (X = {} \<or> X = {\<infinity>})"
  apply (auto simp add: top_enat_def Inf_enat_def)
  apply (metis enat_ord_simps(6) neq_iff not_less_Least)
  apply (metis LeastI)
  by (metis (lifting, full_types) Least_equality order_refl)

lemma steps_Union_enat: "steps w (\<Union>X) = enat n \<Longrightarrow> \<forall>x\<in>X. \<exists>m. steps w x = enat m"
  by (metis not_infinity_eq steps_Union_infinity)

lemma steps_Union_enat_le: "steps w (\<Union>X) = enat n \<Longrightarrow> \<forall>x\<in>X. \<exists>m\<le>n. steps w x = enat m"
  by (metis Sup_upper finite_steps_super_var)

lemma [intro!]: "(m = \<infinity> \<Longrightarrow> x \<le> y) \<Longrightarrow> (\<And>n. m = enat n \<Longrightarrow> x \<le> f n) \<Longrightarrow> x \<le> (case m of enat n \<Rightarrow> f n | \<infinity> \<Rightarrow> y)"
  by (cases m) auto

lemma "steps w (\<Union>X) = \<infinity> \<Longrightarrow> llength w = \<infinity>"
  by (simp add: steps_def)

find_theorems name:finite name:induct name:set

find_theorems "_ \<subseteq> UNIV"

lemma steps_infinite_insert: "steps w {\<sigma>} = \<infinity> \<Longrightarrow> steps w x = enat n \<Longrightarrow> steps w (insert \<sigma> x) = \<infinity>"
  by (metis (mono_tags) bot_least insertI1 insert_subset steps_super_inf)

lemma eval_word_cont: "steps w (\<Union>X) = enat n \<Longrightarrow> eval_word w (\<Union>X) \<le> Sup (eval_word w ` X)"
proof -
  assume hyp: "steps w (\<Union>X) = enat n"
  hence "eval_word w (\<Union>X) = NotTop (eval_finite_word (list_of (ltake (enat n) w)) (\<Union>X))"
    by (simp add: eval_word_def image_def)
  also have "... \<le> Sup {y. \<exists>x\<in>X. y = NotTop (eval_finite_word (list_of (ltake (enat n) w)) x)}"
    apply (simp add: efw_continuous NotTop_continuous)
    apply (subst SUP_def)
    apply (simp only: NotTop_continuous)
    apply (rule Sup_mono)
    by auto
  also have "... \<le> Sup (eval_word w ` X)"
    apply (simp add: eval_word_def image_def)
    apply (rule Sup_mono)
    apply auto
    apply (rule_tac x = "NotTop (eval_finite_word (list_of (ltake (enat n) w)) x)" in exI)
    apply simp
    apply (rule_tac x = x in bexI)
    using steps_Union_enat_le[OF hyp]
    apply (erule_tac x = x in ballE)
    apply (erule exE)
    apply (erule conjE)
    apply (rule_tac x = m in exI)
    apply simp_all
    by (metis efw_steps max_absorb2)
  finally show "eval_word w (\<Union>X) \<le> Sup (eval_word w ` X)" .
qed

lemma "Sup (eval_word w ` X) \<le> eval_word w (\<Union>X)"
  by (smt Sup_le_iff Sup_upper eval_word_iso image_iff)

lemma "eval_word w \<hookleftarrow> Sup X \<le> Sup {eval_word w \<hookleftarrow> x |x. x \<in> X}"
  sledgehammer

lemma "y \<Colon> (x \<Colon> h) \<le> x \<cdot> y \<Colon> h"
proof -
  have "y \<Colon> (x \<Colon> h) = Sup {eval_word \<hookleftarrow> x \<Colon> h |w. w \<in> y}"
    by (simp add: module_def)
  have "... = Sup {eval_word w \<hookleftarrow> Sup {eval_word w \<hookleftarrow> h |w. w \<in> x}) |w. w \<in> y}"
    by (simp add: module_def)


proof -
  have "x \<cdot> y \<Colon> h = Sup {bind h (eval_word w) |w. w \<in> x \<cdot> y}"
    by (simp add: module_def)
  also have "... = Sup {bind h (eval_word w) |w. w \<in> x \<and> \<not> lfinite w} \<squnion> Sup {bind h (eval_word w) |w. \<exists>xs ys. w = xs \<frown> ys \<and> xs \<in> x \<and> lfinite xs \<and> ys \<in> y}"
    by (simp add: l_prod_def)
  also have "... = Sup {bind h (eval_word w) |w. w \<in> x \<and> \<not> lfinite w} \<squnion> Sup {bind h (eval_word (xs \<frown> ys)) |xs ys. xs \<in> x \<and> lfinite xs \<and> ys \<in> y}"
    by (rule arg_cong, blast)
  also have "... = 
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
