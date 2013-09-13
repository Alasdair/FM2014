theory RelyGuarantee2
  imports Language
begin

datatype 'a top = Top | NotTop 'a

abbreviation bind :: "('a \<Rightarrow> 'b top) \<Rightarrow> 'a top \<Rightarrow> 'b top" (infixr "\<hookleftarrow>" 56) where
  "bind f x \<equiv> case x of Top \<Rightarrow> Top | NotTop x \<Rightarrow> f x"

lemma top_left_id: "f \<hookleftarrow> (NotTop x) = f x"
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

datatype 'a act = Act "'a set" "'a rel"

definition sync_free_list :: "'a act list \<Rightarrow> bool" where
  "sync_free_list = undefined"

fun eval_word :: "'a act list \<Rightarrow> 'a set \<Rightarrow> 'a set top" where
  "eval_word [] p = NotTop p"
| "eval_word (Act q x # xs) p = (if p \<subseteq> q then eval_word xs (x `` p) else top)"

lemma eval_word_empty [simp]: "eval_word xs {} = NotTop {}"
proof (induct xs)
  case Nil show ?case by simp
next
  case (Cons x xs) thus ?case by (cases x) simp
qed

lemma [simp]: "f \<hookleftarrow> top = top"
  by (simp add: bind_def top_top_def)

lemma eval_append_word: "eval_word (xs @ ys) h = eval_word ys \<hookleftarrow> eval_word xs h"
proof (induct xs arbitrary: h)
  case Nil show ?case by simp
next
  case (Cons x xs) thus ?case
    by (cases x) simp
qed

lemma eval_append_word_bind: "eval_word (xs @ ys) \<hookleftarrow> h = eval_word ys \<hookleftarrow> eval_word xs \<hookleftarrow> h"
  by (cases h) (simp_all add: eval_append_word)

lemma Image_continuous: "x `` (\<Union>X) = \<Union>Image x ` X"
  by auto

lemma NotTop_continuous: "NotTop (\<Union>X) = Sup (NotTop ` X)"
  by (auto simp add: Sup_top_def)

lemma top_in_Sup: "top \<in> X \<Longrightarrow> Sup X = top" sorry

lemma eval_word_continuous: "eval_word w (Sup X) = Sup (eval_word w ` X)"
proof (induct w arbitrary: X)
  case Nil show ?case by(simp add: NotTop_continuous)
next
  case (Cons x xs)
  show ?case
  proof (induct x)
    fix p x
    {
      assume "\<Union>X \<subseteq> p"
      hence "eval_word (Act p x # xs) (\<Union>X) = Sup (eval_word (Act p x # xs) ` X)"
        apply (simp add: image_def)
        apply (subst Image_continuous)
        apply (subst Cons.hyps)
        apply (rule arg_cong) back
        by auto
    }
    moreover
    {
      assume "\<not> (\<Union>X \<subseteq> p)"
      hence "eval_word (Act p x # xs) (\<Union>X) = Sup (eval_word (Act p x # xs) ` X)"
        apply (simp add: image_def)
        apply (rule sym)
        apply (rule top_in_Sup)
        by auto
    }
    ultimately show "eval_word (Act p x # xs) (\<Union>X) = Sup (eval_word (Act p x # xs) ` X)"
      by blast
  qed
qed

lemma eval_word_bind_continuous: "eval_word w \<hookleftarrow> (Sup X) = Sup {eval_word w \<hookleftarrow> x |x. x \<in> X}"
  apply (auto simp add: Sup_top_def eval_word_continuous image_def)
  apply (metis top.simps(5))
  apply (metis (full_types) top.exhaust top.simps(5))
  apply (metis top.simps(5))
  by (metis (full_types) top.exhaust top.simps(4) top.simps(5))

definition module :: "'a act lan \<Rightarrow> 'a set top \<Rightarrow> 'a set top" (infix "\<Colon>" 60) where
  "x \<Colon> h = Sup {eval_word w \<hookleftarrow> h|w. w \<in> x}"

lemma set_comp_f_eq: "(\<And>x. P x \<Longrightarrow> f x = g x) \<Longrightarrow> {f x |x. P x} = {g x |x. P x}"
  by auto metis

lemma (in complete_lattice) Sup_comp_mono [intro]: "(\<And>x. P x \<Longrightarrow> f x \<le> g x) \<Longrightarrow> Sup {f x |x. P x} \<le> Sup {g x |x. P x}"
  by (auto intro: Sup_mono)

lemma (in complete_lattice) Sup_comp_conj: "Sup {f x y |x y. P x \<and> Q y} = Sup {Sup {f x y |x. P x} |y. Q y}"
  apply (rule antisym)
  apply (simp_all add: Sup_le_iff)
  apply auto
  defer
  apply (rule Sup_mono)
  apply auto
  apply (subgoal_tac "f x y \<le> Sup {f x y |y. Q y}")
  apply (erule order_trans)
  defer
  apply (metis (lifting, full_types) Sup_upper mem_Collect_eq)
  apply (rule Sup_comp_mono)
  by (metis (lifting, full_types) Sup_upper mem_Collect_eq)

lemma mod_mult: "x\<cdot>y \<Colon> h = y \<Colon> (x \<Colon> h)"
proof -
  have "x\<cdot>y \<Colon> h = Sup {eval_word w \<hookleftarrow> h|w. w \<in> x\<cdot>y}"
    by (simp add: module_def)
  also have "... = Sup {eval_word (xw @ yw) \<hookleftarrow> h|xw yw. xw \<in> x \<and> yw \<in> y}"
    by (rule arg_cong, auto simp: in_l_prod)
  also have "... = Sup {eval_word yw \<hookleftarrow> eval_word xw \<hookleftarrow> h|xw yw. xw \<in> x \<and> yw \<in> y}"
    by (simp add: eval_append_word_bind)
  also have "... = Sup {Sup {eval_word yw \<hookleftarrow> eval_word xw \<hookleftarrow> h|xw. xw \<in> x}|yw. yw \<in> y}"
    by (simp add: Sup_comp_conj)
  also have "... = Sup {eval_word yw \<hookleftarrow> (Sup {eval_word xw \<hookleftarrow> h|xw. xw \<in> x})|yw. yw \<in> y}"
    by (auto intro!: arg_cong[where f = Sup] simp add: eval_word_bind_continuous)
  also have "... = Sup {eval_word yw \<hookleftarrow> (x \<Colon> h)|yw. yw \<in> y}"
    by (simp add: module_def)
  also have "... = y \<Colon> (x \<Colon> h)"
    by (simp add: module_def)
  finally show ?thesis .
qed

lemma mod_one [simp]: "{[]} \<Colon> h = h"
  by (cases h) (simp_all add: module_def)

lemma mod_zero [simp]: "{} \<Colon> h = bot"
  by (simp add: module_def)


lemma mod_empty [simp]: "x \<Colon> bot = bot"
proof (cases "x = {}", simp)
  assume "x \<noteq> {}"
  have "x \<Colon> bot = Sup {eval_word w \<hookleftarrow> bot |w. w \<in> x}"
    by (simp add: module_def)
  also have "... = Sup {p. p = NotTop {} \<and> (\<exists>w. w \<in> x)}"
    by (simp add: bot_top_def)

lemma mod_distl: "(x \<union> y) \<Colon> h = (x \<Colon> h) \<union> (y \<Colon> h)"
proof -
  have "(x \<union> y) \<Colon> h = \<Union>{eval_word w h|w. w \<in> x \<union> y}"
    by (simp add: module_def)
  also have "... = \<Union>{eval_word w h|w. w \<in> x \<or> w \<in> y}"
    by blast
  also have "... = \<Union>{eval_word w h|w. w \<in> x} \<union> \<Union>{eval_word w h|w. w \<in> y}"
    by blast
  also have "... = (x \<Colon> h) \<union> (y \<Colon> h)"
    by (simp add: module_def)
  finally show ?thesis .
qed

lemma mod_distr: "x \<Colon> (h \<union> g) = (x \<Colon> h) \<union> (x \<Colon> g)"
proof -
  have "x \<Colon> (h \<union> g) = \<Union>{eval_word w (h \<union> g)|w. w \<in> x}"
    by (simp add: module_def)
  also have "... = \<Union>{eval_word w h \<union> eval_word w g|w. w \<in> x}"
    by (simp add: eval_word_def) blast
  also have "... = \<Union>{eval_word w h|w. w \<in> x} \<union> \<Union>{eval_word w g|w. w \<in> x}"
    by blast
  also have "... = (x \<Colon> h) \<union> (x \<Colon> g)"
    by (simp add: module_def)
  finally show ?thesis .
qed

lemma mod_isol: "x \<subseteq> y \<Longrightarrow> x \<Colon> p \<subseteq> y \<Colon> p"
  by (auto simp add: module_def)

lemma mod_isor: "p \<subseteq> q \<Longrightarrow> x \<Colon> p \<subseteq> x \<Colon> q"
  by (metis mod_distr subset_Un_eq)

lemma mod_continuous: "\<Union>X \<Colon> p = \<Union>{x \<Colon> p|x. x \<in> X}"
  by (simp add: module_def) blast

lemma mod_continuous_var: "\<Union>{f x|x. P x} \<Colon> p = \<Union>{f x \<Colon> p|x. P x}"
  by (simp add: mod_continuous) blast

definition mod_test :: "('a set) \<Rightarrow> 'a act lan" ("_?" [101] 100) where
  "p? \<equiv> {[Act (\<lambda>x. {x} \<inter> p)]}"

lemma mod_test: "p? \<Colon> q = p \<inter> q"
  by (auto simp add: module_def mod_test_def)

lemma test_true: "q \<subseteq> p \<Longrightarrow> p? \<Colon> q = q"
  by (metis Int_absorb1 mod_test)

lemma test_false: "q \<subseteq> -p \<Longrightarrow> p? \<Colon> q = {}"
  by (metis Int_commute disjoint_eq_subset_Compl mod_test)

lemma l_prod_distr: "(X \<union> Y) \<cdot> Z = X \<cdot> Z \<union> Y \<cdot> Z"
  by (insert l_prod_inf_distr[of "{X, Y}" Z]) auto

lemma l_prod_distl: "X \<cdot> (Y \<union> Z) = X \<cdot> Y \<union> X \<cdot> Z"
  by (insert l_prod_inf_distl[of "X" "{Y, Z}"]) auto

no_notation
  Transitive_Closure.trancl ("(_\<^sup>+)" [1000] 999)

definition l_plus :: "'a lan \<Rightarrow> 'a lan" ("_\<^sup>+" [101] 100) where
  "X\<^sup>+ = X\<cdot>X\<^sup>*"

lemma l_plus_unfold: "X\<^sup>+ = X \<union> X\<^sup>+"
  sorry

lemma "q \<subseteq> p \<Longrightarrow> (p?)\<^sup>+\<cdot>x \<Colon> q = (x \<Colon> q) \<union> ((p?)\<^sup>+\<cdot>x \<Colon> q)"
  by (smt l_plus_unfold l_prod_distr mod_distl mod_mult test_true)

lemma "(p?)\<^sup>+\<cdot>x \<Colon> q = (x \<Colon> q \<inter> p) \<union> ((p?)\<^sup>+\<cdot>x \<Colon> q)"
  by (metis inf.commute l_plus_unfold mod_distl mod_distr mod_mult mod_test)

lemma "q \<subseteq> p \<Longrightarrow> (p?)\<^sup>+\<cdot>x \<Colon> q = (x \<Colon> q)"
  nitpick

lemma "p?\<cdot>x \<Colon> q = x\<cdot>q"

lemma "q \<subseteq> -p \<Longrightarrow> p? \<Colon> q = {}"
  by (metis Int_commute disjoint_eq_subset_Compl mod_test)

lemma [simp]: "map \<langle>id,id\<rangle> ` (x \<union> y) = map \<langle>id,id\<rangle> ` x \<union> map \<langle>id,id\<rangle> ` y"
  by (auto simp add: image_def)

lemma image_InL [simp]: "map \<langle>id,id\<rangle> ` op # (InL x) ` X = op # x ` map \<langle>id,id\<rangle> ` X"
  by (auto simp add: image_def)

lemma image_InR [simp]: "map \<langle>id,id\<rangle> ` op # (InR x) ` X = op # x ` map \<langle>id,id\<rangle> ` X"
  by (auto simp add: image_def)

lemma image_singleton: "op # x ` X = {[x]} \<cdot> X"
  by (auto simp add: image_def l_prod_def complex_product_def)

lemma tshuffle_await_cons: 
  "q \<subseteq> - p \<Longrightarrow> map \<langle>id,id\<rangle> ` ((Act (\<lambda>x. {x} \<inter> p) # ys) \<sha> (x # xs)) \<Colon> q = op # x ` (map \<langle>id,id\<rangle> ` ((Act (\<lambda>x. {x} \<inter> p) # ys) \<sha> xs)) \<Colon> q"
  apply (subst tshuffle_ind)
  apply (simp add: mod_distl)
  apply (simp add: image_singleton mod_mult)
  apply (subst module_def) back
  apply (subgoal_tac "q \<inter> p = {}")
  apply simp
  by blast

definition to_rel :: "('a \<Rightarrow> 'a set) \<Rightarrow> 'a rel" where
  "to_rel f = {(x, y)|x y. y \<in> f x}"

definition to_fun :: "'a rel \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "to_fun R x = {y. (x, y) \<in> R}"

lemma rel_fun_inv [simp]: "to_rel (to_fun R) = R"
  by (auto simp add: to_fun_def to_rel_def)

lemma fun_rel_inv [simp]: "to_fun (to_rel f) = f"
  by (auto simp add: to_fun_def to_rel_def)

lemma [simp]: "to_fun {} = (\<lambda>x. {})"
  apply (rule ext)
  by (simp add: to_fun_def)

definition \<iota> :: "'a act lan \<Rightarrow> 'a rel" where
  "\<iota> X = \<Union>{to_rel (runAct x)|x. x \<in> symbols X}"

definition \<rho> :: "'a rel \<Rightarrow> 'a act lan" where
  "\<rho> R = pow_inv {Act (to_fun S)|S. S \<subseteq> R}"

lemma \<iota>_iso: "X \<subseteq> Y \<Longrightarrow> \<iota> X \<subseteq> \<iota> Y"
  apply (simp add: \<iota>_def symbols_def)
  by blast

lemma \<rho>_iso: "X \<subseteq> Y \<Longrightarrow> \<rho> X \<subseteq> \<rho> Y"
  apply (simp add: \<rho>_def)
  apply (rule pow_inv_iso)
  by blast

lemma [simp]: "symbols (pow_inv Z) = Z"
proof -
  {
    fix x
    assume "x \<in> Z"
    hence "[x] \<in> pow_inv Z"
      by (metis pow_inv.pinv_cons pow_inv.pinv_empty)
    hence "x \<in> symbols (pow_inv Z)"
      by (metis symbol_cons)
  }
  moreover
  have "symbols (pow_inv Z) \<subseteq> Z"
  proof (auto simp add: symbols_def)
    fix x xs
    assume "xs \<in> pow_inv Z" and "x \<in> set xs"
    thus "x \<in> Z"
      by (induct xs rule: pow_inv.induct) auto
  qed
  ultimately show ?thesis
    by auto
qed

lemma [simp]: "\<Union>{to_rel (runAct xa)|xa. \<exists>S. xa = Act (to_fun S) \<and> S \<subseteq> x} = \<Union>{S|S. S \<subseteq> x}"
  apply (rule arg_cong) back
  apply auto
  apply (rule_tac x = "Act (to_fun xa)" in exI)
  apply simp
  apply (rule_tac x = "xa" in exI)
  by auto

lemma \<iota>_\<rho>_eq: "\<iota> (\<rho> x) = x"
  by (simp add: \<iota>_def \<rho>_def, auto)

lemma \<rho>_\<iota>_eq: "x \<subseteq> \<rho> (\<iota> x)"
  apply (simp add: \<iota>_def \<rho>_def)
  apply (rule order_trans[of _ "pow_inv (symbols x)"])
  apply (metis inv_sym_extensive)
  apply (rule pow_inv_iso)
  apply auto
  apply (rule_tac x = "to_rel (runAct xa)" in exI)
  by auto

lemma galois_connection: "\<iota> x \<subseteq> y \<longleftrightarrow> x \<subseteq> \<rho> y"
  apply default
  apply (metis \<rho>_\<iota>_eq \<rho>_iso subset_trans)
  by (metis \<iota>_\<rho>_eq \<iota>_iso)

definition "preserves b \<equiv> {(\<sigma>,\<sigma>'). \<sigma> \<in> b \<longrightarrow> \<sigma>' \<in> b}"

lemma \<iota>_tl: "\<iota> {x # xs} \<subseteq> preserves p \<Longrightarrow> \<iota> {xs} \<subseteq> preserves p"
  by (auto simp add: preserves_def \<iota>_def symbols_def)

lemma \<iota>_hd: "\<iota> {x # xs} \<subseteq> preserves p \<Longrightarrow> \<iota> {[x]} \<subseteq> preserves p"
  by (auto simp add: preserves_def \<iota>_def symbols_def)

lemma \<iota>_member: "\<iota> x \<subseteq> preserves p \<Longrightarrow> xw \<in> x \<Longrightarrow> \<iota> {xw} \<subseteq> preserves p"
  by (auto simp add: preserves_def \<iota>_def symbols_def Sup_le_iff)

lemma \<iota>_singleton_preserves: "\<iota> {[x]} \<subseteq> preserves p \<longleftrightarrow> (\<forall>q. q \<subseteq> p \<longrightarrow> {[x]} \<Colon> q \<subseteq> p)"
  by (auto simp add: preserves_def module_def \<iota>_def symbols_def to_rel_def)

lemma tshuffle_await_append:
  "\<iota> {xs} \<subseteq> preserves (- p) \<Longrightarrow>
  q \<subseteq> -p \<Longrightarrow>
  map \<langle>id,id\<rangle> ` ((Act (\<lambda>x. {x} \<inter> p) # zs) \<sha> (xs @ ys)) \<Colon> q = op @ xs ` (map \<langle>id,id\<rangle> ` ((Act (\<lambda>x. {x} \<inter> p) # zs) \<sha> ys)) \<Colon> q"
proof (induct xs arbitrary: q)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  assume ih: "\<And>q. \<iota> {xs} \<subseteq> preserves (- p) \<Longrightarrow>
                  q \<subseteq> - p \<Longrightarrow>
                  map \<langle>id,id\<rangle> ` ((Act (\<lambda>x. {x} \<inter> p) # zs) \<sha> (xs @ ys)) \<Colon> q = op @ xs ` map \<langle>id,id\<rangle> ` ((Act (\<lambda>x. {x} \<inter> p) # zs) \<sha> ys) \<Colon> q"
  and x_xs_preserves_not_p: "\<iota> {x # xs} \<subseteq> preserves (- p)"
  and not_p: "q \<subseteq> - p"

  hence not_p': "{[x]} \<Colon> q \<subseteq> -p"
    by (metis (hide_lams, no_types) \<iota>_hd \<iota>_singleton_preserves)

  have "map \<langle>id,id\<rangle> ` ((Act (\<lambda>x. {x} \<inter> p) # zs) \<sha> ((x # xs) @ ys)) \<Colon> q = map \<langle>id,id\<rangle> ` ((Act (\<lambda>x. {x} \<inter> p) # zs) \<sha> (x # xs @ ys)) \<Colon> q"
    by simp
  also have "... = op # x ` map \<langle>id,id\<rangle> ` ((Act (\<lambda>x. {x} \<inter> p) # zs) \<sha> (xs @ ys)) \<Colon> q"
    by (simp only: tshuffle_await_cons[OF not_p])
  also have "... =  map \<langle>id,id\<rangle> ` ((Act (\<lambda>x. {x} \<inter> p) # zs) \<sha> (xs @ ys)) \<Colon> ({[x]} \<Colon> q)"
    by (simp only: image_singleton mod_mult)
  also have "... = op @ xs ` map \<langle>id,id\<rangle> ` ((Act (\<lambda>x. {x} \<inter> p) # zs) \<sha> ys) \<Colon> ({[x]} \<Colon> q)"
    by (simp only: ih[OF \<iota>_tl[OF x_xs_preserves_not_p] not_p'])
  also have "... = op # x ` op @ xs ` map \<langle>id,id\<rangle> ` ((Act (\<lambda>x. {x} \<inter> p) # zs) \<sha> ys) \<Colon> q"
    by (simp only: mod_mult[symmetric] image_singleton[symmetric])
  also have "... = op @ (x # xs) ` map \<langle>id,id\<rangle> ` ((Act (\<lambda>x. {x} \<inter> p) # zs) \<sha> ys) \<Colon> q"
    by (simp only: image_compose[symmetric] o_def append.simps)
  finally show ?case .
qed

lemma set_comp_3_eq: "(\<And>x y z. Q x y z \<Longrightarrow> P x y z = P' x y z) \<Longrightarrow> {P x y z|x y z. Q x y z} = {P' x y z|x y z. Q x y z}"
  by auto metis+

lemma helper: "\<Union>{{xw} \<cdot> P y z|y xw z. Q y z \<and> xw \<in> x \<and> Q y z} = \<Union>{x \<cdot> P y z|y z. Q y z}"
  by (auto simp add: l_prod_def complex_product_def)

lemma image_append: "op @ xs ` X = {xs} \<cdot> X"
  by (auto simp add: l_prod_def complex_product_def)

lemma await_par:
  assumes x_preserves_not_p: "\<iota> x \<subseteq> preserves (- p)"
  and not_p: "q \<subseteq> -p"
  shows "p?\<cdot>z \<parallel> x\<cdot>y \<Colon> q = x\<cdot>(p?\<cdot>z \<parallel> y) \<Colon> q"
proof -
  have "p?\<cdot>z \<parallel> x\<cdot>y \<Colon> q = \<Union>{map \<langle>id,id\<rangle> ` (pzw \<sha> xyw)|pzw xyw. pzw \<in> p? \<cdot> z \<and> xyw \<in> x \<cdot> y} \<Colon> q"
    by (simp add: shuffle_def)
  also have "... = \<Union>{map \<langle>id,id\<rangle> ` (pzw \<sha> xyw) \<Colon> q|pzw xyw. pzw \<in> p? \<cdot> z \<and> xyw \<in> x \<cdot> y}"
    by (subst mod_continuous) blast
  also have "... = \<Union>{map \<langle>id,id\<rangle> ` ((Act (\<lambda>x. {x} \<inter> p) # zw) \<sha> (xw @ yw)) \<Colon> q|zw xw yw. zw \<in> z \<and> xw \<in> x \<and> yw \<in> y}"
    by (simp add: l_prod_def complex_product_def mod_test_def, rule arg_cong, blast)
  also have "... = \<Union>{op @ xw ` map \<langle>id,id\<rangle> ` ((Act (\<lambda>x. {x} \<inter> p) # zw) \<sha> yw) \<Colon> q|zw xw yw. zw \<in> z \<and> xw \<in> x \<and> yw \<in> y}"
    apply (rule arg_cong) back
    apply (rule set_comp_3_eq)
    apply (subst tshuffle_await_append)
    apply (metis \<iota>_member x_preserves_not_p)
    apply (metis not_p)
    by simp
  also have "... = \<Union>{op @ xw ` map \<langle>id,id\<rangle> ` ((Act (\<lambda>x. {x} \<inter> p) # zw) \<sha> yw)|zw xw yw. zw \<in> z \<and> xw \<in> x \<and> yw \<in> y} \<Colon> q"
    by (subst mod_continuous) blast
  also have "... = \<Union>{{xw} \<cdot> map \<langle>id,id\<rangle> ` ((Act (\<lambda>x. {x} \<inter> p) # zw) \<sha> yw)|zw xw yw. zw \<in> z \<and> xw \<in> x \<and> yw \<in> y} \<Colon> q"
    by (simp only: image_append)
  also have "... = \<Union>{x \<cdot> map \<langle>id,id\<rangle> ` ((Act (\<lambda>x. {x} \<inter> p) # zw) \<sha> yw)|zw yw. zw \<in> z \<and> yw \<in> y} \<Colon> q"
    by (rule arg_cong, auto simp add: l_prod_def complex_product_def)
  also have "... = x \<cdot> \<Union>{map \<langle>id,id\<rangle> ` ((Act (\<lambda>x. {x} \<inter> p) # zw) \<sha> yw)|zw yw. zw \<in> z \<and> yw \<in> y} \<Colon> q"
    by (subst l_prod_inf_distl, rule arg_cong, blast)
  also have "... = x \<cdot> \<Union>{map \<langle>id,id\<rangle> ` (pzw \<sha> yw)|pzw yw. pzw \<in> p? \<cdot> z \<and> yw \<in> y} \<Colon> q"
    by (simp add: l_prod_def complex_product_def mod_test_def, rule arg_cong, blast)
  also have "... = x\<cdot>(p?\<cdot>z \<parallel> y) \<Colon> q"
    by (simp add: shuffle_def)
  finally show ?thesis .
qed

(*
primrec splittings_ind :: "'a list \<Rightarrow> 'a list \<Rightarrow> ('a list \<times> 'a list) set" where
  "splittings_ind ys [] = {(ys, [])}"
| "splittings_ind ys (x#xs) = {(ys, x#xs)} \<union> (splittings_ind (ys @ [x]) xs)"

definition splittings where "splittings xs = {(ys,zs). ys @ zs = xs}"

definition add_first where "add_first xs X = (\<lambda>x. (xs @ fst x, snd x)) ` X"

lemma afs: "add_first ws (splittings xs) = {(ws @ ys,zs)|ys zs. ys @ zs = xs}"
  by (auto simp add: add_first_def splittings_def image_def)

lemma l1: "splittings_ind ys xs = add_first ys (splittings xs)"
  apply (simp add: afs)
  apply (induct xs arbitrary: ys)
  apply simp
  apply auto
  apply (metis Cons_eq_append_conv)
  by (metis (hide_lams, no_types) append_eq_Cons_conv)

lemma [simp]: "add_first [] (splittings xs) = splittings xs"
  by (simp add: splittings_def add_first_def)

lemma l2: "splittings_ind [] xs = splittings xs"
  by (insert l1[of "[]"], simp)
*)

type_synonym mem = "nat \<Rightarrow> nat option"

datatype atoms =
    Assign nat nat
  | Pred "mem set"

primrec atoms_interp :: "atoms \<Rightarrow> mem act" where
  "atoms_interp (Assign x v) = Act (\<lambda>mem. {\<lambda>y. if x = y then Some v else mem y})"
| "atoms_interp (Pred p) = Act (\<lambda>mem. if mem \<in> p then {mem} else {})"

definition domain :: "mem \<Rightarrow> nat set" where
  "domain f \<equiv> {x. f x \<noteq> None}"

definition disjoint :: "mem \<Rightarrow> mem \<Rightarrow> bool" where
  "disjoint f g \<equiv> domain f \<inter> domain g = {}"

definition merge :: "mem \<Rightarrow> mem \<Rightarrow> mem" where
  "merge \<sigma> \<sigma>' = (\<lambda>v. if \<sigma> v = None then \<sigma>' v else \<sigma> v)"

definition sep_conj :: "mem set \<Rightarrow> mem set \<Rightarrow> mem set" (infixr "**" 45) where
  "p ** q \<equiv> {\<sigma>''. \<exists>\<sigma> \<sigma>'. disjoint \<sigma> \<sigma>' \<and> \<sigma>'' = merge \<sigma> \<sigma>' \<and> \<sigma> \<in> p \<and> \<sigma>' \<in> q}"

definition quintuple :: "'b rel \<Rightarrow> 'b rel \<Rightarrow> ('a \<Rightarrow> 'b act) \<Rightarrow> 'b set \<Rightarrow> ('a, 'b) stmt \<Rightarrow> 'b set \<Rightarrow> bool"
  ("_, _ \<turnstile>\<^bsub>_\<^esub> \<lbrace>_\<rbrace> _ \<lbrace>_\<rbrace>" [20,20,0,20,20,20] 100) where
  "r, g \<turnstile>\<^bsub>\<Gamma>\<^esub> \<lbrace>p\<rbrace> c \<lbrace>q\<rbrace> \<equiv> (\<rho> r \<parallel> semantics \<Gamma> c \<Colon> p \<subseteq> q) \<and> (\<iota> (semantics \<Gamma> c) \<subseteq> g)"

definition stable :: "'b rel \<Rightarrow> 'b set \<Rightarrow> bool" where
  "stable r p \<equiv> \<rho> r \<Colon> p \<subseteq> p"

lemma SKIP: "stable r p \<Longrightarrow> r, g \<turnstile>\<^bsub>\<Gamma>\<^esub> \<lbrace>p\<rbrace> Skip \<lbrace>p\<rbrace>"
  by (simp add: quintuple_def \<iota>_def symbols_def stable_def)

lemma inv_exchange: "\<rho> r \<parallel> x \<cdot> y = (\<rho> r \<parallel> x) \<cdot> (\<rho> r \<parallel> y)"
  sorry

lemma inv_join: "\<iota>(x \<parallel> y) = \<iota> x \<union> \<iota> y"
  sorry

lemma SEQ:
  assumes "r, g \<turnstile>\<^bsub>\<Gamma>\<^esub> \<lbrace>p\<rbrace> C1 \<lbrace>q\<rbrace>" and "r, g \<turnstile>\<^bsub>\<Gamma>\<^esub> \<lbrace>q\<rbrace> C2 \<lbrace>s\<rbrace>"
  shows "r, g \<turnstile>\<^bsub>\<Gamma>\<^esub> \<lbrace>p\<rbrace> C1; C2 \<lbrace>s\<rbrace>"
  using assms
  apply (simp add: quintuple_def inv_exchange mod_mult)
  apply (intro conjI)
  apply (metis mod_isor order_trans)
  by (metis Un_upper2 \<iota>_iso empty_subsetI inv_join shuffle_zerol subset_antisym)

lemma rely_dup: "\<rho> r = \<rho> r \<parallel> \<rho> r"
  by (metis (full_types) \<iota>_\<rho>_eq empty_subsetI galois_connection inv_join inv_shuffle inv_sym_extensive shuffle_zeror sup_top_left top_unique)
  
lemma shuffle_isor: "X \<subseteq> Y \<Longrightarrow> Z \<parallel> X \<subseteq> Z \<parallel> Y"
  by (metis shuffle_comm shuffle_iso)

lemma PAR:
  assumes "g1 \<subseteq> r2" and "r1, g1 \<turnstile>\<^bsub>\<Gamma>\<^esub> \<lbrace>p1\<rbrace> C1 \<lbrace>q1\<rbrace>"
  and "g2 \<subseteq> r1" and "r2, g2 \<turnstile>\<^bsub>\<Gamma>\<^esub> \<lbrace>p2\<rbrace> C2 \<lbrace>q2\<rbrace>"
  shows "(r1 \<inter> r2), (g1 \<union> g2) \<turnstile>\<^bsub>\<Gamma>\<^esub> \<lbrace>p1 \<inter> p2\<rbrace> Par C1 C2 \<lbrace>q1 \<inter> q2\<rbrace>"
proof (simp add: quintuple_def, intro conjI)
  let ?c1 = "semantics \<Gamma> C1"
  let ?c2 = "semantics \<Gamma> C2"

  have "\<rho> (r1 \<inter> r2) \<parallel> (?c1 \<parallel> ?c2) \<Colon> p1 \<inter> p2 = (\<rho> (r1 \<inter> r2) \<parallel> ?c1) \<parallel> (\<rho> (r1 \<inter> r2) \<parallel> ?c2) \<Colon> p1 \<inter> p2"
    by (smt rely_dup shuffle_assoc shuffle_comm)
  also have "... \<subseteq> (\<rho> (r1 \<inter> r2) \<parallel> ?c1) \<parallel> (\<rho> (r1 \<inter> r2) \<parallel> ?c2) \<Colon> p1"
    by (metis Int_lower1 mod_isor)
  also have "... \<subseteq> (\<rho> (r1 \<inter> r2) \<parallel> ?c1) \<parallel> (\<rho> (r1 \<inter> r2) \<parallel> \<rho> (\<iota> ?c2)) \<Colon> p1"
    by (intro mod_isol shuffle_isor) (metis \<rho>_\<iota>_eq)
  also have "... \<subseteq> (\<rho> (r1 \<inter> r2) \<parallel> ?c1) \<parallel> (\<rho> (r1 \<inter> r2) \<parallel> \<rho> g2) \<Colon> p1"
    by (intro mod_isol shuffle_isor) (metis \<rho>_iso assms(4) quintuple_def)
  also have "... \<subseteq> (\<rho> (r1 \<inter> r2) \<parallel> ?c1) \<parallel> \<rho> (r1 \<inter> r2) \<Colon> p1"
    by (intro mod_isol shuffle_isor) (metis empty_subsetI galois_connection inf_absorb2 inv_join le_inf_iff shuffle_zeror sup_ge1)
  also have "... \<subseteq> (\<rho> r1 \<parallel> ?c1) \<parallel> \<rho> r1 \<Colon> p1"
    by (metis \<iota>_\<rho>_eq galois_connection inf_le1 mod_isol rely_dup shuffle_assoc shuffle_comm shuffle_iso)
  also have "... = \<rho> r1 \<parallel> ?c1 \<Colon> p1"
    by (metis rely_dup shuffle_assoc shuffle_comm)
  also have "... \<subseteq> q1"
    by (metis assms(2) quintuple_def)
  finally show "\<rho> (r1 \<inter> r2) \<parallel> (semantics \<Gamma> C1 \<parallel> semantics \<Gamma> C2) \<Colon> p1 \<inter> p2 \<subseteq> q1" .

  have "\<rho> (r1 \<inter> r2) \<parallel> (?c1 \<parallel> ?c2) \<Colon> p1 \<inter> p2 = \<rho> (r1 \<inter> r2) \<parallel> (?c2 \<parallel> ?c1) \<Colon> p1 \<inter> p2"
    by (metis shuffle_comm)
  also have "... = (\<rho> (r1 \<inter> r2) \<parallel> ?c2) \<parallel> (\<rho> (r1 \<inter> r2) \<parallel> ?c1) \<Colon> p1 \<inter> p2"
    by (smt rely_dup shuffle_assoc shuffle_comm)
  also have "... \<subseteq> (\<rho> (r1 \<inter> r2) \<parallel> ?c2) \<parallel> (\<rho> (r1 \<inter> r2) \<parallel> ?c1) \<Colon> p2"
    by (metis Int_lower2 mod_isor)
  also have "... \<subseteq> (\<rho> (r1 \<inter> r2) \<parallel> ?c2) \<parallel> (\<rho> (r1 \<inter> r2) \<parallel> \<rho> (\<iota> ?c1)) \<Colon> p2"
    by (intro mod_isol shuffle_isor) (metis \<rho>_\<iota>_eq)
  also have "... \<subseteq> (\<rho> (r1 \<inter> r2) \<parallel> ?c2) \<parallel> (\<rho> (r1 \<inter> r2) \<parallel> \<rho> g1) \<Colon> p2"
    by (intro mod_isol shuffle_isor) (metis \<rho>_iso assms(2) quintuple_def)
  also have "... \<subseteq> (\<rho> (r1 \<inter> r2) \<parallel> ?c2) \<parallel> \<rho> (r1 \<inter> r2) \<Colon> p2"
    by (intro mod_isol shuffle_isor) (metis empty_subsetI galois_connection inf_absorb2 inv_join shuffle_zeror sup_inf_absorb)
  also have "... \<subseteq> (\<rho> r2 \<parallel> ?c2) \<parallel> \<rho> r2 \<Colon> p2"
    by (metis \<rho>_iso inf_le2 mod_isol rely_dup shuffle_assoc shuffle_comm shuffle_iso)
  also have "... = \<rho> r2 \<parallel> ?c2 \<Colon> p2"
    by (metis rely_dup shuffle_assoc shuffle_comm)
  also have "... \<subseteq> q2"
    by (metis assms(4) quintuple_def)
  finally show "\<rho> (r1 \<inter> r2) \<parallel> (semantics \<Gamma> C1 \<parallel> semantics \<Gamma> C2) \<Colon> p1 \<inter> p2 \<subseteq> q2" .

  show "\<iota> (?c1 \<parallel> ?c2) \<subseteq> g1 \<union> g2"
    by (metis assms(2) assms(4) inv_join quintuple_def sup_mono)
qed

lemma CHOICE:
  assumes "r, g \<turnstile>\<^bsub>\<Gamma>\<^esub> \<lbrace>p\<rbrace> C1 \<lbrace>q\<rbrace>" and "r, g \<turnstile>\<^bsub>\<Gamma>\<^esub> \<lbrace>p\<rbrace> C2 \<lbrace>q\<rbrace>"
  shows "r, g \<turnstile>\<^bsub>\<Gamma>\<^esub> \<lbrace>p\<rbrace> Choice C1 C2 \<lbrace>q\<rbrace>"
  using assms
  apply (simp add: quintuple_def)
  apply (intro conjI)
  apply (metis le_sup_iff mod_distl shuffle_distl)
  by (metis galois_connection le_sup_iff)

definition Await :: "mem set \<Rightarrow> (atoms, mem) stmt \<Rightarrow> (atoms, mem) stmt" where
  "Await b C = Seq (Atom (Pred b)) C"

lemma helper2: "x \<subseteq> y \<Longrightarrow> y \<union> z \<subseteq> w \<Longrightarrow> x \<union> z \<subseteq> w"
  by (metis le_sup_iff order_trans)

lemma helper3: "x \<subseteq> y \<Longrightarrow> x \<union> y \<subseteq> y"
  by (metis le_sup_iff order_refl)

lemma test: "{(\<sigma>, \<sigma>'). \<sigma>' \<in> runAct a \<sigma>} \<subseteq> {(\<sigma>, \<sigma>'). \<sigma> \<in> p \<longrightarrow> \<sigma>' \<in> p} \<Longrightarrow> \<sigma> \<in> p \<longrightarrow> runAct a \<sigma> \<subseteq> p"
  by auto

lemma test_comm: "\<iota> {[x]} \<subseteq> preserves p \<Longrightarrow> {[Act (\<lambda>x. {x} \<inter> p)]} \<cdot> {[x]} \<Colon> q \<subseteq> {[x]} \<cdot> {[Act (\<lambda>x. {x} \<inter> p)]} \<Colon> q"
  by (auto simp add: l_prod_def complex_product_def module_def preserves_def \<iota>_def symbols_def to_rel_def)

lemma tshuffle_left_leq: "{[x]} \<cdot> map \<langle>id,id\<rangle> ` (xs \<sha> ys) \<subseteq> map \<langle>id,id\<rangle> ` ((x # xs) \<sha> ys)"
  apply (induct ys)
  apply (simp add: l_prod_def complex_product_def)
  apply (simp only: tshuffle_ind image_Un image_InL)
  apply (simp only: image_singleton)
  by (metis Un_upper1)

lemma tshuffle_right_leq: "{[y]} \<cdot> map \<langle>id,id\<rangle> ` (xs \<sha> ys) \<subseteq> map \<langle>id,id\<rangle> ` (xs \<sha> (y # ys))"
  by (metis (hide_lams, no_types) tshuffle_left_leq tshuffle_words_comm)

lemma mod_isol_var: "z \<subseteq> y \<Longrightarrow> x \<Colon> p \<subseteq> z \<Colon> p \<Longrightarrow> x \<Colon> p \<subseteq> y \<Colon> p"
  by (metis mod_isol subset_trans)

lemma preserve_test_tshuffle:
  "\<iota> {xs} \<subseteq> preserves p \<Longrightarrow> map \<langle>id,id\<rangle> ` (xs \<sha> (Act (\<lambda>x. {x} \<inter> p) # ys)) \<Colon> q = {[Act (\<lambda>x. {x} \<inter> p)]} \<cdot> map \<langle>id,id\<rangle> ` (xs \<sha> ys) \<Colon> q"
  apply default
  defer
  apply (rule mod_isol)
  apply (rule tshuffle_right_leq)
proof (induct xs arbitrary: q)
  case Nil
  show ?case by (simp add: l_prod_def complex_product_def)
next
  case (Cons x xs)
  assume "\<And>q. \<iota> {xs} \<subseteq> preserves p \<Longrightarrow>
              map \<langle>id,id\<rangle> ` (xs \<sha> (Act (\<lambda>x. {x} \<inter> p) # ys)) \<Colon> q \<subseteq> {[Act (\<lambda>x. {x} \<inter> p)]} \<cdot> map \<langle>id,id\<rangle> ` (xs \<sha> ys) \<Colon> q"
  and x_xs_preserves_p: "\<iota> {x # xs} \<subseteq> preserves p"
  note ih = this(1)[OF \<iota>_tl[OF this(2)]]

  show ?case
    apply (simp only: tshuffle_ind image_Un image_InL image_InR mod_distl)
    apply (simp only: image_singleton)
    apply (subst mod_mult)
    apply (rule helper2[OF ih])
    apply (subst mod_mult[symmetric])
    apply (rule helper3)
    apply (subst l_prod_assoc[symmetric])
    apply (rule mod_isol_var[OF l_prod_isor[OF tshuffle_left_leq]])
    apply (subst l_prod_assoc[symmetric])
    apply (subst mod_mult)
    apply (subst mod_mult) back
    apply (rule mod_isor)
    apply (subst mod_mult)
    apply (subst test_comm[OF q_satisfies_p \<iota>_hd[OF x_xs_preserves_p]])
    apply (subst mod_mult[symmetric])
    apply (subst l_prod_assoc)
    apply (rule mod_isol)
    apply (rule l_prod_isor)
    by (rule tshuffle_left_leq)
qed
*)

lemma preserve_test:
  assumes "r \<subseteq> preserves s" and "q \<subseteq> p"
  shows "(\<rho> r \<parallel> p? \<cdot> x) \<Colon> q = p? \<cdot> (\<rho> r \<parallel> x) \<Colon> q"
  sorry

lemma AWAIT1: "r \<subseteq> preserves s \<Longrightarrow> p \<subseteq> s \<Longrightarrow> r, g \<turnstile>\<^bsub>\<Gamma>\<^esub> \<lbrace>s\<rbrace> C \<lbrace>q\<rbrace> \<Longrightarrow> r, g \<turnstile>\<^bsub>\<Gamma>\<^esub> \<lbrace>p\<rbrace> Await s C \<lbrace>q\<rbrace>" sorry

lemma AWAIT:
  assumes "g1 \<subseteq> r2" and "r1, g1 \<turnstile>\<^bsub>\<Gamma>\<^esub> \<lbrace>p1 \<inter> t\<rbrace> C1 \<lbrace>q1\<rbrace>"
  and "g2 \<subseteq> r1" and "r2, g2 \<inter> preserves t \<turnstile>\<^bsub>\<Gamma>\<^esub> \<lbrace>p2\<rbrace> C2 \<lbrace>t \<inter> q2\<rbrace>"
  shows "(r1 \<inter> r2), (g1 \<union> g2) \<turnstile>\<^bsub>\<Gamma>\<^esub> \<lbrace>p1 \<inter> p2\<rbrace> Par (Await t C1) C2 \<lbrace>q1 \<inter> q2\<rbrace>"
  apply (rule PAR)
  sorry

lemma Sup_image_le_iff: "(\<Union>{f x|x. P x} \<subseteq> Y) \<longleftrightarrow> (\<forall>x. P x \<longrightarrow> f x \<subseteq> Y)"
  by blast

lemma mod_forall: "X \<Colon> p \<subseteq> q \<longleftrightarrow> (\<forall>x\<in>X. {x} \<Colon> p \<subseteq> q)"
  by (auto simp add: module_def)

lemma pow_inv_singleton: "x \<in> X \<Longrightarrow> [x] \<in> pow_inv X"
  by (metis pow_inv.pinv_cons pow_inv.pinv_empty)

lemma stable_forall: "stable r p \<longleftrightarrow> (\<forall>xs\<in>(pow_inv {Act (to_fun S) |S. S \<subseteq> r}). {xs} \<Colon> p \<subseteq> p)"
  apply (simp add: stable_def \<rho>_def)
  apply (subst mod_forall)
  by simp

lemma singleton_stable: "stable r p \<Longrightarrow> x \<in> {Act (to_fun S) |S. S \<subseteq> r} \<Longrightarrow> {[x]} \<Colon> p \<subseteq> p"
  apply (simp only: stable_forall \<rho>_def)
  apply (drule pow_inv_singleton)
  by auto

lemma mod_cons: "op # x ` X \<Colon> p = {[x]} \<cdot> X \<Colon> p"
  by (simp add: image_def complex_product_def l_prod_def, rule arg_cong, blast)

lemma [simp]: "map \<langle>id,id\<rangle> ` op # (InL x) ` X = op # x ` map \<langle>id,id\<rangle> ` X"
  by (auto simp add: image_def)

lemma mod_cons_var: "{x # xs} \<Colon> p = {[x]} \<cdot> {xs} \<Colon> p"
  by (auto simp add: l_prod_def complex_product_def)

lemma ATOM:
  assumes atom: "\<forall>\<sigma>\<in>p. runAct (\<Gamma> a) \<sigma> \<subseteq> q"
  and p_stable: "stable r p"
  and q_stable: "stable r q"
  shows "r, {(\<sigma>,\<sigma>'). \<sigma>' \<in> runAct (\<Gamma> a) \<sigma>}  \<turnstile>\<^bsub>\<Gamma>\<^esub> \<lbrace>p\<rbrace> Atom a \<lbrace>q\<rbrace>"
proof -
  from assms have atom': "({[\<Gamma> a]} \<Colon> p) \<subseteq> q"
    by (auto simp add: module_def)

  {
    fix xs
    assume "xs \<in> pow_inv {Act (to_fun S) |S. S \<subseteq> r}"
    hence "map \<langle>id,id\<rangle> ` (xs \<sha> [\<Gamma> a]) \<Colon> p \<subseteq> q"
    proof (induct xs, simp add: atom')
      fix x and xs
      assume x_set: "x \<in> {Act (to_fun S) |S. S \<subseteq> r}"
      and xs_set: "xs \<in> pow_inv {Act (to_fun S) |S. S \<subseteq> r}"
      and ih: "map \<langle>id,id\<rangle> ` (xs \<sha> [\<Gamma> a]) \<Colon> p \<subseteq> q"

      have "{[x]} \<Colon> p \<subseteq> p"
        by (rule singleton_stable[OF p_stable x_set])

      hence x_first: "op # x ` map \<langle>id,id\<rangle> ` (xs \<sha> [\<Gamma> a]) \<Colon> p \<subseteq> q"
        by (simp add: mod_cons mod_mult) (metis (hide_lams, no_types) ih mod_isor subset_trans)

      have "x # xs \<in> pow_inv {Act (to_fun S) |S. S \<subseteq> r}"
        by (smt pow_inv.pinv_cons x_set xs_set)
      hence "{x#xs} \<Colon> q \<subseteq> q"
        by (metis \<rho>_def mod_forall q_stable stable_def)

      from x_first and this show "map \<langle>id,id\<rangle> ` ((x # xs) \<sha> [\<Gamma> a]) \<Colon> p \<subseteq> q"
        apply (simp only: tshuffle_ind image_Un mod_distl, simp, subst mod_cons_var, subst mod_mult)
        by (metis atom' mod_isor subset_trans)
    qed
  }

  thus "r, {(\<sigma>,\<sigma>'). \<sigma>' \<in> runAct (\<Gamma> a) \<sigma>}  \<turnstile>\<^bsub>\<Gamma>\<^esub> \<lbrace>p\<rbrace> Atom a \<lbrace>q\<rbrace>"
    apply (simp add: quintuple_def)
    apply (intro conjI)
    apply (insert p_stable)
    defer
    apply (simp add: to_rel_def \<iota>_def symbols_def)
    apply (simp add: stable_def)
    apply (simp add: \<rho>_def shuffle_def)
    apply (subst mod_continuous_var)
    apply (subst Sup_image_le_iff)
    by auto
qed

lemma WEAKEN: "r' \<subseteq> r \<Longrightarrow> g \<subseteq> g' \<Longrightarrow> p' \<subseteq> p \<Longrightarrow> q \<subseteq> q' \<Longrightarrow> r, g \<turnstile>\<^bsub>\<Gamma>\<^esub> \<lbrace>p\<rbrace> C \<lbrace>q\<rbrace> \<Longrightarrow> r', g' \<turnstile>\<^bsub>\<Gamma>\<^esub> \<lbrace>p'\<rbrace> C \<lbrace>q'\<rbrace>"
  apply (simp add: quintuple_def)
  by (metis \<rho>_iso mod_isol mod_isor order_trans shuffle_iso)

lemmas WEAKEN_RELY = WEAKEN[OF _ subset_refl subset_refl subset_refl]
  and STRENGTHEN_GUAR = WEAKEN[OF subset_refl _ subset_refl subset_refl]
  and WEAKEN_PRE = WEAKEN[OF subset_refl subset_refl _ subset_refl]
  and STRENGTHEN_POST = WEAKEN[OF subset_refl subset_refl subset_refl _]

lemma ATOM_VAR:
  assumes atom: "\<forall>\<sigma>\<in>p. runAct (\<Gamma> a) \<sigma> \<subseteq> q"
  and p_stable: "stable r p"
  and q_stable: "stable r q"
  and guar: "{(\<sigma>,\<sigma>'). \<sigma>' \<in> runAct (\<Gamma> a) \<sigma>} \<subseteq> g"
  shows "r, g  \<turnstile>\<^bsub>\<Gamma>\<^esub> \<lbrace>p\<rbrace> Atom a \<lbrace>q\<rbrace>"
  apply (rule STRENGTHEN_GUAR[OF guar])
  apply (rule ATOM)
  apply (metis atom)
  apply (metis p_stable)
  by (metis q_stable)

abbreviation quintuple' :: "mem rel \<Rightarrow> mem rel \<Rightarrow> mem set \<Rightarrow> (atoms, mem) stmt \<Rightarrow> mem set \<Rightarrow> bool"
  ("_, _ \<turnstile>// \<lbrace>_\<rbrace>// _// \<lbrace>_\<rbrace>" [20,20,20,20,20] 100) where
  "r, g \<turnstile> \<lbrace>p\<rbrace> c \<lbrace>q\<rbrace> \<equiv> r, g \<turnstile>\<^bsub>atoms_interp\<^esub> \<lbrace>p\<rbrace> c \<lbrace>q\<rbrace>"

definition maps_to :: "nat \<Rightarrow> nat \<Rightarrow> mem set" (infix "\<mapsto>" 95) where
  "v \<mapsto> n \<equiv> {\<sigma>. \<sigma> v = Some n}"

definition maps_to_any :: "nat \<Rightarrow> mem set" ("_ \<mapsto> -" [96] 95) where
  "v \<mapsto> - = {\<sigma>. \<exists>n. \<sigma> v = Some n}"

abbreviation assignment :: "nat \<Rightarrow> nat \<Rightarrow> (atoms, mem) stmt" (infix ":=" 95) where
  "assignment v n \<equiv> Atom (Assign v n)"

abbreviation Test :: "mem set \<Rightarrow> (atoms, mem) stmt" where "Test t \<equiv> Atom (Pred t)"

lemma [simp]: "semantics atoms_interp (Test t) \<Colon> h = h \<inter> t"
  by (auto simp add: module_def)

definition Await :: "mem set \<Rightarrow> (atoms, mem) stmt \<Rightarrow> (atoms, mem) stmt" where
  "Await b C = Seq (Test b) C"

definition "unchanged V \<equiv> {(\<sigma>,\<sigma>'). \<forall>v\<in>V. \<sigma> v = \<sigma>' v}"

definition "preserves b \<equiv> {(\<sigma>,\<sigma>'). \<sigma> \<in> b \<longrightarrow> \<sigma>' \<in> b}"

lemma AWAIT:
  assumes "\<exists>C11 C12 C13."
  shows "r, g \<turnstile> \<lbrace>p\<rbrace> Par C1 (Await b C2) \<lbrace>q1 \<inter> q2\<rbrace>"

lemma ASSIGN:
  shows "unchanged {v}, {(\<sigma>,\<sigma>'). \<sigma>' v = Some n \<and> (\<forall>v'. v' \<noteq> v \<longrightarrow> \<sigma> v' = \<sigma>' v')} \<turnstile> \<lbrace>v \<mapsto> -\<rbrace> v := n \<lbrace>v \<mapsto> n\<rbrace>"
  sorry

abbreviation K :: "bool \<Rightarrow> 'a set" where "K t \<equiv> {s. t}"

lemma disj1: "(x \<mapsto> - ** y \<mapsto> -) = (K (x \<noteq> y) \<inter> x \<mapsto> - ** K (x \<noteq> y) \<inter> y \<mapsto> -)"
  by (auto simp add: sep_conj_def maps_to_any_def disjoint_def domain_def)

lemma empty_mod: "x \<Colon> {} = {}"
  by (simp add: module_def eval_word_def)

lemma CONST: "(p' \<Longrightarrow> r, g \<turnstile> \<lbrace>p\<rbrace> C1 \<lbrace>q\<rbrace>) \<Longrightarrow> r, g \<turnstile> \<lbrace>K p' \<inter> p\<rbrace> C1 \<lbrace>q\<rbrace>"
  apply (simp add: quintuple_def empty_mod)
  by (metis Un_empty_left empty_subsetI galois_connection inv_join shuffle_zerol subset_empty)

lemma "x \<mapsto> n \<subseteq> x \<mapsto> -"
  by (auto simp add: maps_to_def maps_to_any_def)

lemma empty_rely1: "\<rho> {} \<Colon> p \<subseteq> p"
proof (auto simp add: \<rho>_def module_def eval_word_def)
  fix w x \<sigma>
  assume "w \<in> pow_inv {Act (\<lambda>x. {})}" and "x \<in> runAct (listsum w) \<sigma>"
  and "\<sigma> \<in> p"
  thus "x \<in> p"
    by (induct w rule: pow_inv.induct) (simp_all add: zero_act_def plus_act_def)
qed

lemma empty_rely2: "p \<subseteq> \<rho> {} \<Colon> p"
  apply (simp add: \<rho>_def module_def eval_word_def)
  apply auto
  apply (rule_tac x = p in exI)
  apply (intro conjI)
  apply auto
  apply (rule_tac x = "[]" in exI)
  by (auto simp add: zero_act_def)

lemma empty_rely [simp]: "\<rho> {} \<Colon> p = p"
  by (metis empty_rely1 empty_rely2 subset_antisym)

lemma "{}, UNIV \<turnstile> \<lbrace>x \<mapsto> n\<rbrace> Skip \<lbrace>x \<mapsto> -\<rbrace>"
  by (auto simp add: quintuple_def maps_to_any_def maps_to_def)

datatype ('a, 'b) rg_block =
    RGPar "('a, 'b) stmt" "('a, 'b) rg_block"
  | RGEnd "('a, 'b) stmt"

definition rg_block :: "'b rel \<Rightarrow> ('a, 'b) stmt \<Rightarrow> 'b rel \<Rightarrow> ('a, 'b) rg_block \<Rightarrow> ('a, 'b) rg_block" ("//  RELY _//    DO _//  GUAR _; _" [31,31,31,30] 30) where
  "RELY r DO C GUAR g; prog \<equiv> RGPar C prog"

definition rg_block_end :: "'b rel \<Rightarrow> ('a, 'b) stmt \<Rightarrow> 'b rel \<Rightarrow> ('a, 'b) rg_block" ("//  RELY _//    DO _//  GUAR _//COEND" [31,31,31] 30) where
  "RELY r DO C GUAR g COEND \<equiv> RGEnd C"

primrec cobegin :: "('a, 'b) rg_block \<Rightarrow> ('a, 'b) stmt" ("COBEGIN _" [30] 30) where
  "cobegin (RGPar c rg) = Par c (cobegin rg)"
| "cobegin (RGEnd c) = c"

abbreviation triple' :: "mem set \<Rightarrow> (atoms, mem) stmt \<Rightarrow> mem set \<Rightarrow> bool"
  ("\<lbrace>_\<rbrace>// _// \<lbrace>_\<rbrace>" [20,20,20] 100) where
  "\<lbrace>p\<rbrace> c \<lbrace>q\<rbrace> \<equiv> {}, UNIV \<turnstile>\<^bsub>atoms_interp\<^esub> \<lbrace>p\<rbrace> c \<lbrace>q\<rbrace>"

lemma COBEGIN:
  assumes "r1, g1 \<turnstile>\<^bsub>\<Gamma>\<^esub> \<lbrace>p1\<rbrace> C1 \<lbrace>q1\<rbrace>"
  and "r2, g2 \<turnstile>\<^bsub>\<Gamma>\<^esub> \<lbrace>p2\<rbrace> C2 \<lbrace>q2\<rbrace>"
  and "g1 \<subseteq> r2" and "g2 \<subseteq> r1"
  and "r \<subseteq> r1 \<inter> r2" and "g1 \<union> g2 \<subseteq> g"
  shows "r, g \<turnstile>\<^bsub>\<Gamma>\<^esub> \<lbrace>p1 \<inter> p2\<rbrace> COBEGIN RELY r1 DO C1 GUAR g1; RELY r2 DO C2 GUAR g2 COEND \<lbrace>q1 \<inter> q2\<rbrace>"
  apply (rule WEAKEN[OF assms(5) assms(6) subset_refl subset_refl])
  using assms
  by (auto simp add: rg_block_def rg_block_end_def intro: PAR)

definition PAR_ASSIGN :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (atoms, mem) stmt" ("_, _ := _, _" [96,96,96,96] 95) where
  "PAR_ASSIGN x y n m \<equiv>
    COBEGIN
      RELY unchanged {x}
      DO x := n
      GUAR unchanged (- {x});
      RELY unchanged {y}
      DO y := m
      GUAR unchanged (- {y})
    COEND"  

lemma PAR_ASSIGN:
  "x \<noteq> y \<Longrightarrow> unchanged {x, y}, unchanged (- {x, y}) \<turnstile> \<lbrace>x \<mapsto> - \<inter> y \<mapsto> -\<rbrace> x, y :=  n, m \<lbrace>x \<mapsto> n \<inter> y \<mapsto> m\<rbrace>"
  apply (simp add: PAR_ASSIGN_def)
  apply (rule COBEGIN)
  apply (rule WEAKEN[OF _ _ subset_refl subset_refl])
  prefer 3
  apply (rule ASSIGN)
  prefer 3
  apply (rule WEAKEN[OF _ _ subset_refl subset_refl])
  prefer 3
  apply (rule ASSIGN)
  by (auto simp add: unchanged_def)

lemma PAR_ASSIGN: "x \<noteq> y \<Longrightarrow> {}, UNIV \<turnstile> \<lbrace>x \<mapsto> - \<inter> y \<mapsto> -\<rbrace> Par (x := n) (y := m) \<lbrace>x \<mapsto> n \<inter> y \<mapsto> m\<rbrace>"
  apply (rule STRENGTHEN_GUAR[of "unchanged (- {x}) \<union> unchanged (- {y})"])
  apply simp
  apply (rule WEAKEN_RELY[of _ "unchanged (- {y}) \<inter> unchanged (- {x})"])
  apply simp
  apply (rule PAR)
  apply simp
  apply (rule WEAKEN[OF _ _ subset_refl subset_refl])
  prefer 3
  apply (rule ASSIGN)
  apply (force simp add: unchanged_def)+
  apply (rule WEAKEN[OF _ _ subset_refl subset_refl])
  prefer 3
  apply (rule ASSIGN)
  by (force simp add: unchanged_def)+

end
