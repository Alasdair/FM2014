theory Language
  imports SumList Groups
begin

section {* Languages with shuffle product *}

subsection {* Complex product and language product *}

definition complex_product :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "complex_product f X Y = {f x y|x y. x \<in> X \<and> y \<in> Y}"

lemma complex_comm: "(\<And>x y. f x y = f y x) \<Longrightarrow> complex_product f X Y = complex_product f Y X"
  by (auto simp add: complex_product_def)

lemma complex_assoc: "(\<And>x y z. f (f x y) z = f x (f y z)) \<Longrightarrow>
  complex_product f (complex_product f X Y) Z = complex_product f X (complex_product f Y Z)"
  by (auto simp add: complex_product_def) metis+

type_synonym 'a lan = "'a list set"

definition l_prod :: "'a lan \<Rightarrow> 'a lan \<Rightarrow> 'a lan" (infixl "\<cdot>" 80) where
  "l_prod = complex_product op @"

lemma l_prod_assoc: "(X \<cdot> Y) \<cdot> Z = X \<cdot> (Y \<cdot> Z)"
  by (metis append_assoc complex_assoc l_prod_def)

lemma l_prod_isol: "X \<subseteq> Y \<Longrightarrow> X \<cdot> Z \<subseteq> Y \<cdot> Z"
  by (auto simp add: l_prod_def complex_product_def)

lemma l_prod_isor: "X \<subseteq> Y \<Longrightarrow> Z \<cdot> X \<subseteq> Z \<cdot> Y"
  by (auto simp add: l_prod_def complex_product_def)

lemma l_prod_one [simp]: shows "{[]} \<cdot> X = X" and "X \<cdot> {[]} = X"
  by (simp_all add: l_prod_def complex_product_def)

lemma l_prod_inf_distl: "X \<cdot> \<Union>\<YY> = \<Union>{X \<cdot> Y|Y. Y \<in> \<YY>}"
  by (auto simp add: l_prod_def complex_product_def)

lemma l_prod_inf_distr: "\<Union>\<XX> \<cdot> Y = \<Union>{X \<cdot> Y|X. X \<in> \<XX>}"
  by (auto simp add: l_prod_def complex_product_def)

lemma l_prod_distr: "(X \<union> Y) \<cdot> Z = X \<cdot> Z \<union> Y \<cdot> Z"
  by (insert l_prod_inf_distr[of "{X, Y}" Z]) auto

lemma l_prod_distl: "X \<cdot> (Y \<union> Z) = X \<cdot> Y \<union> X \<cdot> Z"
  by (insert l_prod_inf_distl[of "X" "{Y, Z}"]) auto

lemma l_prod_zero [simp]: shows "{} \<cdot> X = {}" and "X \<cdot> {} = {}"
  by (simp add: l_prod_def complex_product_def)+

text {* The \sha\ operator generates a language by shuffling two words together. *}

definition tshuffle_words :: "'a list \<Rightarrow> 'b list \<Rightarrow> ('a + 'b) lan" (infix "\<sha>" 75) where
  "tshuffle_words xs ys = {zs. lefts zs = xs \<and> rights zs = ys}"

text {* The resulting language contains strings where each symbol is labelled by either @{term Inl} or @{term Inr},
depending on which input it came from. This means that @{prop "\<forall>zs \<in> (xs \<sha> ys). \<ll> zs = xs \<and> \<rr> zs = ys"}.
If a function @{term f} has type @{typ "'a \<Rightarrow> 'c"} and @{term g} has type @{typ "'b \<Rightarrow> 'c"}, then the sum elimination function @{term "\<langle>f,g\<rangle>"}
can be used to eliminate values of @{typ "('a,'b) sum"} by transforming them to values of type @{typ "'c"}.
The function @{term "\<langle>id,id\<rangle>"} is therefore used when both components of the sum have the same type. *}

lemma tshuffle_words_comm: "map \<langle>id,id\<rangle> ` (x \<sha> y) = map \<langle>id,id\<rangle> ` (y \<sha> x)"
  by (auto simp add: tshuffle_words_def image_def) (rule_tac x = "map swap xa" in exI, simp)+

lemma tshuffle_word_assoc:
  "map \<langle>id,\<langle>id,id\<rangle>\<rangle> ` {ws. \<ll> ws = xs \<and> \<ll> (\<rr> ws) = ys \<and> \<rr> (\<rr> ws) = zs} = map \<langle>\<langle>id,id\<rangle>,id\<rangle> ` {ws. \<ll> (\<ll> ws) = xs \<and> \<rr> (\<ll> ws) = ys \<and> \<rr> ws = zs}"
  by (auto simp add: image_def, rule_tac x = "map rbr1 xa" in exI, simp, rule_tac x = "map rbr2 xa" in exI, simp)

definition tshuffle :: "'a lan \<Rightarrow> 'b lan \<Rightarrow> ('a + 'b) lan" (infixl "\<Sha>" 75) where
  "X \<Sha> Y \<equiv> \<Union>{x \<sha> y|x y. x \<in> X \<and> y \<in> Y}"

lemma tshuffle_lr: "xs \<in> X \<Sha> Y \<longleftrightarrow> \<ll> xs \<in> X \<and> \<rr> xs \<in> Y"
  by (auto simp add: tshuffle_def tshuffle_words_def)

lemma tshuffle_comm: "map \<langle>id,id\<rangle> ` (X \<Sha> Y) = map \<langle>id,id\<rangle> ` (Y \<Sha> X)"
proof -
  have "map \<langle>id,id\<rangle> ` (X \<Sha> Y) = \<Union>{map \<langle>id,id\<rangle> ` (x \<sha> y)|x y. x \<in> X \<and> y \<in> Y}"
    by (auto simp add: tshuffle_def)
  also have "... = \<Union>{map \<langle>id,id\<rangle> ` (y \<sha> x)|x y. x \<in> X \<and> y \<in> Y}"
    by (simp add: tshuffle_words_comm)
  also have "... = map \<langle>id,id\<rangle> ` (Y \<Sha> X)"
    by (auto simp add: tshuffle_def)
  finally show ?thesis .
qed

definition shuffle :: "'a lan \<Rightarrow> 'a lan \<Rightarrow> 'a lan" (infixl "\<parallel>" 75) where
  "shuffle X Y \<equiv> \<Union>{map \<langle>id,id\<rangle> ` (x \<sha> y)|x y. x \<in> X \<and> y \<in> Y}"

lemma shuffle_to_tshuffle: "X \<parallel> Y = map \<langle>id,id\<rangle> ` (X \<Sha> Y)"
  by (auto simp add: shuffle_def tshuffle_def image_def)

lemma shuffle_comm: "X \<parallel> Y = Y \<parallel> X"
  by (metis shuffle_to_tshuffle tshuffle_comm)

lemma tshuffle3_right:
  "X \<Sha> (Y \<Sha> Z) = \<Union>{{w. \<ll> w = x \<and> \<ll> (\<rr> w) = y \<and> \<rr> (\<rr> w) = z}|x y z. x \<in> X \<and> y \<in> Y \<and> z \<in> Z}"
  by (simp only: tshuffle_def tshuffle_words_def) blast

lemma tshuffle3_left:
  "(X \<Sha> Y) \<Sha> Z = \<Union>{{w. \<ll> (\<ll> w) = x \<and> \<rr> (\<ll> w) = y \<and> \<rr> w = z}|x y z. x \<in> X \<and> y \<in> Y \<and> z \<in> Z}"
 by (simp only: tshuffle_def tshuffle_words_def) blast

lemma tshuffle_assoc: "map \<langle>\<langle>id,id\<rangle>,id\<rangle> ` ((X \<Sha> Y) \<Sha> Z) = map \<langle>id,\<langle>id,id\<rangle>\<rangle> ` (X \<Sha> (Y \<Sha> Z))"
proof -
  have "map \<langle>\<langle>id,id\<rangle>,id\<rangle> ` ((X \<Sha> Y) \<Sha> Z) = map \<langle>\<langle>id,id\<rangle>,id\<rangle> ` \<Union>{{w. \<ll> (\<ll> w) = x \<and> \<rr> (\<ll> w) = y \<and> \<rr> w = z}|x y z. x \<in> X \<and> y \<in> Y \<and> z \<in> Z}"
    by (simp add: tshuffle3_left)
  also have "... = \<Union>{map \<langle>\<langle>id,id\<rangle>,id\<rangle> ` {w. \<ll> (\<ll> w) = x \<and> \<rr> (\<ll> w) = y \<and> \<rr> w = z}|x y z. x \<in> X \<and> y \<in> Y \<and> z \<in> Z}"
    by (auto simp add: image_def)
  also have "... = \<Union>{map \<langle>id,\<langle>id,id\<rangle>\<rangle> ` {w. \<ll> w = x \<and> \<ll> (\<rr> w) = y \<and> \<rr> (\<rr> w) = z}|x y z. x \<in> X \<and> y \<in> Y \<and> z \<in> Z}"
    by (simp add: tshuffle_word_assoc)
  also have "... = map \<langle>id,\<langle>id,id\<rangle>\<rangle> ` \<Union>{{w. \<ll> w = x \<and> \<ll> (\<rr> w) = y \<and> \<rr> (\<rr> w) = z}|x y z. x \<in> X \<and> y \<in> Y \<and> z \<in> Z}"
    by (auto simp add: image_def)
  also have "... = map \<langle>id,\<langle>id,id\<rangle>\<rangle> ` (X \<Sha> (Y \<Sha> Z))"
    by (simp add: tshuffle3_right)
  finally show ?thesis .
qed

lemma tshuffle_words_emptyl [simp]: "[] \<sha> xs = {map Inr xs}"
  by (auto simp add: tshuffle_words_def no_lefts)

lemma tshuffle_words_emptyr [simp]: "xs \<sha> [] = {map Inl xs}"
  by (auto simp add: tshuffle_words_def no_rights)

lemma tshuffle_ind: "(x#xs) \<sha> (y#ys) = (op # (Inl x) ` (xs \<sha> (y#ys))) \<union> (op # (Inr y) ` ((x#xs) \<sha> ys))"
proof
  show "(op # (Inl x) ` (xs \<sha> (y#ys))) \<union> (op # (Inr y) ` ((x#xs) \<sha> ys)) \<subseteq> (x#xs) \<sha> (y#ys)"
    by (auto simp add: tshuffle_words_def)
  show "(x#xs) \<sha> (y#ys) \<subseteq> (op # (Inl x) ` (xs \<sha> (y#ys))) \<union> (op # (Inr y) ` ((x#xs) \<sha> ys))"
  proof (auto simp add: tshuffle_words_def image_def, rule_tac x = "rfl xa" in exI, intro conjI)
    fix z
    assume "\<forall>w. \<rr> w = ys \<longrightarrow> \<ll> w = x # xs \<longrightarrow> z \<noteq> Inr y # w" and zl: "\<ll> z = x # xs" and zr: "\<rr> z = y # ys"
    hence zny: "z \<noteq> Inr y # rfr z"
      by (metis lefts.simps(3) rights.simps(3) tl.simps(2))
    show "\<ll> (rfl z) = xs"
      by (metis rfl1 zl)
    from zny zr show "\<rr> (rfl z) = y # ys"
      by (induct z rule: sum_list_induct) auto
    from zny zl zr show "z = Inl x # rfl z"
      by (induct z rule: sum_list_induct) auto
  qed
qed

lemma tshuffle_words_map:
  fixes f :: "'a \<Rightarrow> 'b"
  and g :: "'c \<Rightarrow> 'd"
  shows "map f xs \<sha> map g ys = map \<langle>Inl \<circ> f, Inr \<circ> g\<rangle> ` (xs \<sha> ys)"
proof
  show "map f xs \<sha> map g ys \<subseteq> map \<langle>Inl \<circ> f, Inr \<circ> g\<rangle> ` (xs \<sha> ys)"
  proof (induct xs arbitrary: ys, simp_all)
    fix x xs and ys :: "'c list"

    assume ih_xs: "\<And>ys::'c list. (map f xs) \<sha> (map g ys) \<subseteq> map \<langle>Inl \<circ> f, Inr \<circ> g\<rangle> ` (xs \<sha> ys)"

    show "(f x # map f xs) \<sha> (map g ys) \<subseteq> map \<langle>Inl \<circ> f, Inr \<circ> g\<rangle> ` ((x # xs) \<sha> ys)"
    proof (induct ys, simp)
      fix y and ys :: "'c list"

      assume ih_ys: "(f x # map f xs) \<sha> (map g ys) \<subseteq> map \<langle>Inl \<circ> f, Inr \<circ> g\<rangle> ` ((x # xs) \<sha> ys)"

      have "op # (Inl (f x)) ` (map f xs \<sha> map g (y # ys)) \<subseteq> map \<langle>Inl \<circ> f, Inr \<circ> g\<rangle> ` ((x # xs) \<sha> (y # ys))"
      proof -
        have "op # (Inl (f x)) ` (map f xs \<sha> map g (y # ys)) \<subseteq> op # (Inl (f x)) ` map \<langle>Inl \<circ> f, Inr \<circ> g\<rangle> ` (xs \<sha> (y # ys))"
          by (rule image_mono, rule ih_xs)
        also have "... \<subseteq> map \<langle>Inl \<circ> f, Inr \<circ> g\<rangle> ` op # (Inl x) ` (xs \<sha> (y # ys))"
          by (auto simp add: image_def)
        also have "... \<subseteq> map \<langle>Inl \<circ> f, Inr \<circ> g\<rangle> ` ((x # xs) \<sha> (y # ys))"
          by (metis (hide_lams, no_types) image_mono le_sup_iff tshuffle_ind eq_refl)
        finally show ?thesis .
      qed

      moreover have "op # (Inr (g y)) ` ((f x # map f xs) \<sha> (map g ys)) \<subseteq> map \<langle>Inl \<circ> f, Inr \<circ> g\<rangle> ` ((x # xs) \<sha> (y # ys))"
      proof -
        have "op # (Inr (g y)) ` ((f x # map f xs) \<sha> (map g ys)) \<subseteq> op # (Inr (g y)) ` map \<langle>Inl \<circ> f, Inr \<circ> g\<rangle> ` ((x # xs) \<sha> ys)"
          by (rule image_mono, rule ih_ys)
        also have "... \<subseteq> map \<langle>Inl \<circ> f, Inr \<circ> g\<rangle> ` op # (Inr y) ` ((x # xs) \<sha> ys)"
          by (auto simp add: image_def)
        also have "... \<subseteq> map \<langle>Inl \<circ> f, Inr \<circ> g\<rangle> ` ((x # xs) \<sha> (y # ys))"
          by (metis (hide_lams, no_types) image_mono le_sup_iff tshuffle_ind eq_refl)
        finally show ?thesis .
      qed

      ultimately show "((f x # map f xs) \<sha> (map g (y # ys))) \<subseteq> map \<langle>Inl \<circ> f, Inr \<circ> g\<rangle> ` ((x # xs) \<sha> (y # ys))"
        by (simp, subst tshuffle_ind, auto)
    qed
  qed

  show "map \<langle>Inl \<circ> f, Inr \<circ> g\<rangle> ` (xs \<sha> ys) \<subseteq> map f xs \<sha> map g ys"
  proof (auto simp add: tshuffle_words_def)
    fix x :: "('a, 'c) sum list"
    show "\<ll> (map \<langle>Inl \<circ> f, Inr \<circ> g\<rangle> x) = map f (\<ll> x)"
      by (induct x rule: sum_list_induct, auto)
    show "\<rr> (map \<langle>Inl \<circ> f, Inr \<circ> g\<rangle> x) = map g (\<rr> x)"
      by (induct x rule: sum_list_induct, auto)
  qed
qed

lemma shuffle_assoc: "(X \<parallel> Y) \<parallel> Z = X \<parallel> (Y \<parallel> Z)"
proof -
  have "(X \<parallel> Y) \<parallel> Z = map \<langle>id,id\<rangle> ` ((map \<langle>id,id\<rangle> ` (X \<Sha> Y)) \<Sha> Z)"
    by (simp add: shuffle_to_tshuffle)
  also have "... = map \<langle>id,id\<rangle> ` \<Union>{x \<sha> y |x y. x \<in> map \<langle>id,id\<rangle> ` (X \<Sha> Y) \<and> y \<in> Z}"
    by (simp add: tshuffle_def)
  also have "... = map \<langle>id,id\<rangle> ` \<Union>{map \<langle>id,id\<rangle> x \<sha> y|x y. x \<in> (X \<Sha> Y) \<and> y \<in> Z}"
    by (auto simp add: image_def)
  also have "... = map \<langle>id,id\<rangle> ` \<Union>{map \<langle>Inl \<circ> \<langle>id,id\<rangle>, Inr\<rangle> ` (x \<sha> y)|x y. x \<in> (X \<Sha> Y) \<and> y \<in> Z}"
    by (simp add: tshuffle_words_map[where g = id, simplified])
  also have "... = map \<langle>id,id\<rangle> ` map \<langle>Inl \<circ> \<langle>id,id\<rangle>, Inr\<rangle> ` \<Union>{x \<sha> y|x y. x \<in> (X \<Sha> Y) \<and> y \<in> Z}"
    by (auto simp add: image_def)
  also have "... = (map \<langle>id,id\<rangle> \<circ> map \<langle>Inl \<circ> \<langle>id,id\<rangle>, Inr\<rangle>) ` ((X \<Sha> Y) \<Sha> Z)"
    by (metis image_compose tshuffle_def)
  also have "... = map \<langle>\<langle>id,id\<rangle>,id\<rangle> ` ((X \<Sha> Y) \<Sha> Z)"
    by (simp only: map_sum_elim_simp1)
  also have "... = map \<langle>id,\<langle>id,id\<rangle>\<rangle> ` (X \<Sha> (Y \<Sha> Z))"
    by (metis tshuffle_assoc)
  also have "... = (map \<langle>id,id\<rangle> \<circ> map \<langle>Inl, Inr \<circ> \<langle>id,id\<rangle>\<rangle>) ` (X \<Sha> (Y \<Sha> Z))"
    by (simp only: map_sum_elim_simp2)
  also have "... = map \<langle>id,id\<rangle> ` map \<langle>Inl, Inr \<circ> \<langle>id,id\<rangle>\<rangle> ` \<Union>{x \<sha> y|x y. x \<in> X \<and> y \<in> (Y \<Sha> Z)}"
    by (metis image_compose tshuffle_def)
  also have "... = map \<langle>id,id\<rangle> ` \<Union>{map \<langle>Inl, Inr \<circ> \<langle>id,id\<rangle>\<rangle> ` (x \<sha> y)|x y. x \<in> X \<and> y \<in> (Y \<Sha> Z)}"
    by (auto simp add: image_def)
  also have "... = map \<langle>id,id\<rangle> ` \<Union>{x \<sha> map \<langle>id,id\<rangle> y|x y. x \<in> X \<and> y \<in> (Y \<Sha> Z)}"
    by (simp add: tshuffle_words_map[where f = id, simplified])
  also have "... = map \<langle>id,id\<rangle> ` \<Union>{x \<sha> y|x y. x \<in> X \<and> y \<in> map \<langle>id,id\<rangle> ` (Y \<Sha> Z)}"
    by (auto simp add: image_def)
  also have "... = map \<langle>id,id\<rangle> ` (X \<Sha> (map \<langle>id,id\<rangle> ` (Y \<Sha> Z)))"
    by (simp add: tshuffle_def)
  also have "... = X \<parallel> (Y \<parallel> Z)"
    by (simp add: shuffle_to_tshuffle)
  finally show ?thesis .
qed

lemma set_comp_mono4:
  assumes fg: "\<And>a b c d. f a b c d \<subseteq> g a b c d"
  shows "\<Union>{f a b c d|a b c d. a \<in> A \<and> b \<in> B \<and> c \<in> C \<and> d \<in> D} \<subseteq> \<Union>{g a b c d|a b c d. a \<in> A \<and> b \<in> B \<and> c \<in> C \<and> d \<in> D}"
  using assms by blast

lemma word_exchange: "(map \<langle>id,id\<rangle> ` (a \<sha> b)) \<cdot> (map \<langle>id,id\<rangle> ` (c \<sha> d)) \<subseteq> map \<langle>id, id\<rangle> ` ((b @ c) \<sha> (a @ d))"
  by (auto simp add: tshuffle_words_def l_prod_def complex_product_def image_def, rule_tac x = "map swap xb @ xc" in exI, simp)

lemma exchange: "(A \<parallel> B) \<cdot> (C \<parallel> D) \<subseteq> (B \<cdot> C) \<parallel> (A \<cdot> D)"
proof -
  have "(A \<parallel> B) \<cdot> (C \<parallel> D) = {x @ y|x y. x \<in> map \<langle>id, id\<rangle> ` (A \<Sha> B) \<and> y \<in> map \<langle>id, id\<rangle> ` (C \<Sha> D)}"
    by (simp add: shuffle_to_tshuffle complex_product_def l_prod_def)
  also have "... = {map \<langle>id,id\<rangle> x @ map \<langle>id,id\<rangle> y|x y. x \<in> (A \<Sha> B) \<and> y \<in> (C \<Sha> D)}"
    by blast
  also have "... = \<Union>{{map \<langle>id,id\<rangle> x @ map \<langle>id,id\<rangle> y|x y. x \<in> (a \<sha> b) \<and> y \<in> (c \<sha> d)}|a b c d. a \<in> A \<and> b \<in> B \<and> c \<in> C \<and> d \<in> D}"
    by (simp add: tshuffle_def) blast
  also have "... = \<Union>{(map \<langle>id,id\<rangle> ` (a \<sha> b)) \<cdot> (map \<langle>id,id\<rangle> ` (c \<sha> d))|a b c d. a \<in> A \<and> b \<in> B \<and> c \<in> C \<and> d \<in> D}"
    by (simp add: l_prod_def complex_product_def) blast
  also have "... \<subseteq> \<Union>{map \<langle>id, id\<rangle> ` ((b @ c) \<sha> (a @ d))|a b c d. a \<in> A \<and> b \<in> B \<and> c \<in> C \<and> d \<in> D}"
    by (rule set_comp_mono4) (rule word_exchange)
  also have "... = \<Union>{map \<langle>id, id\<rangle> ` (bc \<sha> ad)|bc ad. bc \<in> (B \<cdot> C) \<and> ad \<in> (A \<cdot> D)}"
    by (simp add: l_prod_def complex_product_def) blast
  also have "... = (B \<cdot> C) \<parallel> (A \<cdot> D)"
    by (simp add: shuffle_def)
  finally show ?thesis .
qed

hide_fact set_comp_mono4

lemma shuffle_distl: "X \<parallel> (Y \<union> Z) = (X \<parallel> Y) \<union> (X \<parallel> Z)"
  by (simp add: shuffle_def) blast

lemma shuffle_distr: "(X \<union> Y) \<parallel> Z = (X \<parallel> Z) \<union> (Y \<parallel> Z)"
  by (simp add: shuffle_def) blast

lemma shuffle_inf_distl: "X \<parallel> \<Union>\<YY> = \<Union>{X \<parallel> Y|Y. Y \<in> \<YY>}"
  by (simp add: shuffle_def) blast

lemma shuffle_inf_distr: "\<Union>\<XX> \<parallel> Y = \<Union>{X \<parallel> Y|X. X \<in> \<XX>}"
  by (simp add: shuffle_def) blast

lemma shuffle_one [simp]: shows "X \<parallel> {[]} = X" and "{[]} \<parallel> X = X"
proof -
  {
    fix x :: "'a list"
    have "map (\<langle>id,id\<rangle> \<circ> Inl) x = x"
      by (induct x) auto
  }
  thus "X \<parallel> {[]} = X"
    by (simp add: shuffle_def) blast
  thus "{[]} \<parallel> X = X"
    by (metis shuffle_comm)
qed

lemma shuffle_zeror [simp]: "X \<parallel> {} = {}"
  by (simp add: shuffle_def)

lemma shuffle_zerol [simp]: "{} \<parallel> X = {}"
  by (simp add: shuffle_def)

lemma shuffle_iso: "X \<subseteq> Y \<Longrightarrow> X \<parallel> Z \<subseteq> Y \<parallel> Z"
  by (metis shuffle_distr subset_Un_eq)

lemma l_prod_leq_shuffle: "X \<cdot> Y \<subseteq> X \<parallel> Y"
  by (insert exchange[where A = "X" and B = "{[]}" and C = "Y" and D = "{[]}"]) (simp add: shuffle_comm)

lemma meet_dist1: "(X \<inter> Y) \<parallel> Z \<subseteq> (X \<parallel> Z) \<inter> (Y \<parallel> Z)"
  by (metis Int_lower1 Int_lower2 le_inf_iff shuffle_iso)

lemma in_l_prod: "w \<in> X \<cdot> Y \<longleftrightarrow> (\<exists>x y. w = x @ y \<and> x \<in> X \<and> y \<in> Y)"
  by (auto simp add: l_prod_def complex_product_def)

section {* Stutter/mumble closure *}

subsection {* List monoid *}

instantiation list :: (type) monoid_add
begin
  definition plus_list :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
    "plus_list \<equiv> op @"

  definition zero_list :: "'a list" where "zero_list \<equiv> []"

  instance by default (auto simp add: plus_list_def zero_list_def)
end

subsection {* Definition of stutter/mumble closure *}

text {*
Define a \textit{monoidal language} as a language $L$ over an alphabet
$\Sigma$ with a binary operator $+$ and unital element $0 \in
\Sigma$, such that $(\Sigma, +, 0)$ is a monoid. For these
languages we can define closure operators inspired by Brookes's work
on full abstraction~\cite{} and futher work by Dingel~\cite{}. The
stutter/mumble language $\gamma^\ddagger$ for a word $\gamma$ in such a
language is inductively generated as follows, assuming $x,y,z \in
\Sigma$ and $\alpha,\beta,\gamma \in \Sigma^*$: Firstly, $0\gamma \in
\gamma^\ddagger$. Secondly, if $\alpha x \beta \in \gamma^\ddagger$
then $\alpha 0x\beta \in \gamma^\ddagger$ and $\alpha x0\beta \in
\gamma^\ddagger$ (\textit{stuttering}). Thirdly, if $\alpha xy\beta
\in \gamma^\ddagger$ then $\alpha(x + y)\beta \in
\gamma^\ddagger$ (\textit{mumbling}). The stutter/mumble closure for a
language $X$ is then simply defined as $X^\ddagger =
\bigcup\{\alpha^\ddagger|\alpha \in X\}$.
*}

inductive_set sm_set :: "'a::monoid_add list \<Rightarrow> 'a::monoid_add lan" for T where
  self [intro!]: "0 # T \<in> sm_set T"
| stutter: "as @ bs \<in> sm_set T \<Longrightarrow> as @ [0] @ bs \<in> sm_set T"
| mumble: "as @ [bs] @ [cs] @ ds \<in> sm_set T \<Longrightarrow> as @ [bs + cs] @ ds \<in> sm_set T"

text {*
The reason why we have $0\gamma \in \gamma^\ddagger$, rather than $\gamma \in \gamma^\ddagger$
is that this rule ensures that no stutter/mumble closed language contains the empty word.
The reason for this is as follows; If stutter/mumble closed languages are allowed to contain the empty word,
one ends up with two distinct units for shuffle and language product, $\{\epsilon,0,00,000,\dots\}$ and $\{0,00,000,\dots\}$.
Unfortunately this means the extensiveness property $X \subseteq X^\ddagger$ no longer holds for arbitrary languages,
but only those without the empty word property. The restriction on this property makes certain proofs more complicated,
but the problems caused by having two distinct units makes the tradeoff worthwhile.
*}

definition sm_closure :: "'a::monoid_add lan \<Rightarrow> 'a::monoid_add lan" ("_\<^sup>\<ddagger>" [101] 100) where
  "X\<^sup>\<ddagger> \<equiv> \<Union>(sm_set ` X)"

definition ewp :: "'a lan \<Rightarrow> bool" where
  "ewp X \<equiv> [] \<in> X"

lemma ewp_union [simp]: "ewp (X \<union> Y) \<longleftrightarrow> ewp X \<or> ewp Y"
  by (auto simp add: ewp_def)

lemma ewp_l_prod [simp]: "ewp (X \<cdot> Y) \<longleftrightarrow> ewp X \<and> ewp Y"
  by (auto simp add: ewp_def l_prod_def complex_product_def)

lemma word_shuffle_subset: "\<lbrakk>xs \<in> X; ys \<in> Y\<rbrakk> \<Longrightarrow> map \<langle>id,id\<rangle> ` (xs \<sha> ys) \<subseteq> (X \<parallel> Y)"
  by (auto simp add: shuffle_def)

lemma ewp_shuffle [simp]: "ewp (X \<parallel> Y) \<longleftrightarrow> ewp X \<and> ewp Y"
  apply default
  apply (simp add: ewp_def shuffle_def tshuffle_words_def image_def)
  apply auto
  apply (simp add: ewp_def)
  by (metis (hide_lams, full_types) empty_subsetI insert_subset set_mp shuffle_iso shuffle_one(2))

lemma sm_set_append: "xs \<in> sm_set xs' \<Longrightarrow> ys \<in> sm_set ys' \<Longrightarrow> (xs @ ys) \<in> sm_set (xs' @ ys')"
  apply (induct xs rule: sm_set.induct)
  apply (induct ys rule: sm_set.induct)
  apply auto
  apply (metis (full_types) append_Cons append_Nil sm_set.self sm_set.stutter)
  apply (metis append_Cons append_Nil append_assoc sm_set.stutter)
  apply (metis append_Cons append_Nil append_assoc sm_set.mumble)
  apply (metis append_Cons eq_Nil_appendI sm_set.stutter)
  by (metis append_Cons eq_Nil_appendI sm_set.mumble)

lemma sm_set_self_var: "x # xs \<in> sm_set (x # xs)"
proof -
  have "0 # x # xs \<in> sm_set (x # xs)"
    by (metis sm_set.self)
  hence "[] @ [0] @ [x] @ xs \<in> sm_set (x # xs)"
    by simp
  hence "[] @ [0 + x] @ xs \<in> sm_set (x # xs)"
    by (rule sm_set.mumble)
  thus "x # xs \<in> sm_set (x # xs)"
    by simp
qed

lemma sm_set_cons: "xs \<in> sm_set ys \<Longrightarrow> (x#xs) \<in> sm_set (x#ys)"
  by (metis (hide_lams, no_types) Cons_eq_appendI append_Nil sm_set_self_var sm_set_append)

lemma sm_set_self_rev [intro]: "xs @ [0] \<in> sm_set xs"
proof -
  have "0 # xs \<in> sm_set xs"
    by (metis sm_set.self)
  thus ?thesis
    apply (induct xs)
    apply auto
    by (metis sm_set.self sm_set_cons)
qed

lemma sm_set_pair: "[x + y] \<in> sm_set [x, y]"
  by (metis append_Cons append_Nil sm_set.mumble sm_set_self_var)

lemma sm_set_trans: "xs \<in> sm_set ys \<Longrightarrow> ys \<in> sm_set zs \<Longrightarrow> xs \<in> sm_set zs"
  apply (induct xs rule: sm_set.induct)
  apply auto
  apply (metis (full_types) append_Cons append_Nil sm_set.stutter)
  apply (metis append_Cons eq_Nil_appendI sm_set.stutter)
  by (metis append_Cons eq_Nil_appendI sm_set.mumble)

lemma sm_set_empty [intro]: "[] \<notin> sm_set xs"
proof -
  {
    fix ys
    assume "ys \<in> sm_set xs" hence "ys \<noteq> []"
      by (induct ys rule: sm_set.induct) auto
  }
  thus ?thesis by auto
qed

lemma [simp]: "listsum (xs @ 0 # ys) = listsum (xs @ ys)"
  by (induct xs) auto 

lemma [simp]: "listsum (xs @ (y + y') # ys) = listsum (xs @ y # y' # ys)"
  by (induct xs) (auto intro: add_assoc)

lemma sm_set_listsum: "xs \<in> sm_set ys \<Longrightarrow> [listsum xs] \<in> sm_set [listsum ys]"
  apply (induct xs rule: sm_set.induct)
  apply auto
  apply (metis sm_set_self_var)
  by (metis add_assoc)

lemma sm_set_cons_unit: "xs \<in> sm_set ys \<Longrightarrow> xs \<in> sm_set (0 # ys)"
  apply (induct xs rule: sm_set.induct)
  apply (rule sm_set_self_var)
  apply (rule stutter)
  apply assumption
  apply (rule mumble)
  apply assumption
  done

subsection {* Mumbling sequences of symbols *}

lemma mumble_many': "length bs = n \<and> as @ bs @ cs \<in> sm_set T \<longrightarrow> as @ [listsum bs] @ cs \<in> sm_set T"
  apply (induct n arbitrary: as bs cs)
  apply (metis append_Nil length_0_conv listsum_simps(1) sm_set.stutter)
proof
  fix n as bs cs
  assume "\<And>as bs cs. length bs = n \<and> as @ bs @ cs \<in> sm_set T \<longrightarrow> as @ [listsum bs] @ cs \<in> sm_set T"
  and "length bs = Suc n \<and> as @ bs @ cs \<in> sm_set T"
  then moreover obtain z and zs where "bs = z#zs" by (metis Suc_length_conv)
  ultimately have "(as @ [z]) @ [listsum zs] @ cs \<in> sm_set T"
    by (metis append_Cons append_Nil append_assoc diff_Suc_1 drop_1_Cons length_drop)
  hence "as @ [listsum (z#zs)] @ cs \<in> sm_set T"
    by (simp only: listsum_simps(2)) (metis mumble append_assoc)
  thus "as @ [listsum bs] @ cs \<in> sm_set T"
    by (metis `bs = z # zs`)
qed

lemma mumble_many: "as @ bs @ cs \<in> sm_set T \<Longrightarrow> as @ [listsum bs] @ cs \<in> sm_set T"
  by (metis mumble_many')

hide_fact mumble_many'

subsection {* Lifted operators and properties *}

text {*
The definitions below lift the shuffle and language product operations to stutter/mumble closed
languages. Most of the following properties show that $(\mathcal{P}(\Sigma^*)^\ddagger, \cup, \cdot^\ddagger, \|^\ddagger,\emptyset,\mathbf{1})$ is
a concurrent Kleene algebra.
*}

definition sm_shuffle :: "'a::monoid_add lan \<Rightarrow> 'a::monoid_add lan \<Rightarrow> 'a::monoid_add lan" (infixl "\<parallel>\<^sup>\<ddagger>" 75) where
  "X \<parallel>\<^sup>\<ddagger> Y \<equiv> (X \<parallel> Y)\<^sup>\<ddagger>"

definition sm_l_prod :: "'a::monoid_add lan \<Rightarrow> 'a::monoid_add lan \<Rightarrow> 'a::monoid_add lan" (infixl "\<cdot>\<^sup>\<ddagger>" 75) where
  "X \<cdot>\<^sup>\<ddagger> Y \<equiv> (X \<cdot> Y)\<^sup>\<ddagger>"

definition sm_one :: "'a::monoid_add lan" ("\<one>") where
  "sm_one = {[]}\<^sup>\<ddagger>"

definition atomic :: "'a::monoid_add list set \<Rightarrow> 'a::monoid_add list set" ("\<langle>_\<rangle>" [0] 1000) where
  "atomic X = {[listsum xs]|xs. xs \<in> X}\<^sup>\<ddagger>"

text {* It is straightforward to show that $^\ddagger$ is a closure operator on the set of languages 
without the empty word. *}

lemma sm_ewp: "\<not> ewp (X\<^sup>\<ddagger>)"
  by (simp add: sm_closure_def ewp_def sm_set_empty)

lemma sm_closure_extensive [intro]: "\<not> ewp X \<Longrightarrow> X \<subseteq> X\<^sup>\<ddagger>"
  apply (auto simp add: sm_closure_def)
  apply (rule_tac x = x in bexI)
  apply auto
  by (metis (full_types) ewp_def neq_Nil_conv sm_set_self_var)

lemma sm_closure_iso: "X \<subseteq> Y \<Longrightarrow> X\<^sup>\<ddagger> \<subseteq> Y\<^sup>\<ddagger>"
  by (auto simp add: sm_closure_def)

lemma sm_closure_idem: "(X\<^sup>\<ddagger>)\<^sup>\<ddagger> = X\<^sup>\<ddagger>"
  apply default
  defer
  apply (metis sm_closure_extensive sm_ewp)
  apply (auto simp add: sm_closure_def)
  apply (rule_tac x = xa in bexI)
  by (auto intro: sm_set_trans)

lemma sm_closure_closure: "\<not> ewp X \<Longrightarrow> X \<subseteq> Y\<^sup>\<ddagger> \<longleftrightarrow> X\<^sup>\<ddagger> \<subseteq> Y\<^sup>\<ddagger>"
  by (metis sm_closure_extensive sm_closure_idem sm_closure_iso subset_trans)

text {* The atomicity brackets are an interior (or coclosure) operator on the set of stutter/mumble
closed languages. *}

lemma atomic_ewp: "\<not> ewp \<langle>X\<rangle>"
  by (simp add: atomic_def sm_ewp)

lemma atomic_coextensive: "\<langle>X\<^sup>\<ddagger>\<rangle> \<subseteq> X\<^sup>\<ddagger>"
proof -
  have "{[listsum x]|x. x \<in> X\<^sup>\<ddagger>} \<subseteq> X\<^sup>\<ddagger>"
    apply (simp add: sm_closure_def atomic_def)
    apply auto
    apply (rule_tac x = xb in bexI)
    apply (metis append_Nil append_Nil2 mumble_many)
    by auto
  thus ?thesis
    apply (simp add: atomic_def)
    apply (subst sm_closure_closure[symmetric])
    by (auto simp add: ewp_def)
qed

lemma atomic_iso: "X \<subseteq> Y \<Longrightarrow> \<langle>X\<rangle> \<subseteq> \<langle>Y\<rangle>"
  by (simp add: atomic_def, rule sm_closure_iso, auto)

lemma atomic_closure: "\<langle>X\<rangle> = \<langle>X\<rangle>\<^sup>\<ddagger>"
  by (simp add: atomic_def sm_closure_idem)

lemma atomic_idem: "\<langle>\<langle>X\<rangle>\<rangle> = \<langle>X\<rangle>"
  apply (simp add: atomic_def)
  apply default
  apply (metis (mono_tags) atomic_coextensive atomic_def)
  apply (rule sm_closure_iso)
  apply (auto simp add: sm_closure_def)
  by (metis append_Nil2 listsum_append listsum_simps(2) sm_set_self_var)

lemma atomic_interior: "\<langle>X\<^sup>\<ddagger>\<rangle> \<subseteq> Y\<^sup>\<ddagger> \<longleftrightarrow> \<langle>X\<^sup>\<ddagger>\<rangle> \<subseteq> \<langle>Y\<^sup>\<ddagger>\<rangle>"
  by (metis atomic_coextensive atomic_idem atomic_iso subset_trans)

lemma "{}\<^sup>\<ddagger> = {}"
  by (auto simp add: sm_closure_def)

lemma sm_one_closed: "\<one>\<^sup>\<ddagger> = \<one>"
  by (metis sm_closure_idem sm_one_def)

lemma sm_union: "(X \<union> Y)\<^sup>\<ddagger> = X\<^sup>\<ddagger> \<union> Y\<^sup>\<ddagger>"
  by (simp add: sm_closure_def)

lemma ewp_sm_one:
  assumes ewp_X: "ewp X"
  shows "X\<^sup>\<ddagger> = \<one> \<union> (X - {[]})\<^sup>\<ddagger>"
proof -
  have "X\<^sup>\<ddagger> = ({[]} \<union> (X - {[]}))\<^sup>\<ddagger>"
    by (metis ewp_X ewp_def insert_Diff_single insert_absorb insert_is_Un)
  also have "... = {[]}\<^sup>\<ddagger> \<union> (X - {[]})\<^sup>\<ddagger>"
    by (metis sm_union)
  also have "... = \<one> \<union> (X - {[]})\<^sup>\<ddagger>"
    by (metis sm_one_def)
  finally show ?thesis .
qed

lemma sm_set_one: "\<one> = sm_set []"
  by (auto simp add: sm_one_def sm_closure_def)

lemma atomic_sm_set: "\<langle>sm_set xs\<rangle> = {[listsum xs]}\<^sup>\<ddagger>"
  by (auto simp add: atomic_def sm_closure_def) (metis sm_set_listsum sm_set_trans)

lemma "\<langle>{}\<rangle> = {}"
  by (simp add: atomic_def sm_closure_def)

lemma inits_last [simp]: "rev (tl (rev (x#xs))) @ [hd (rev (x#xs))] = x#xs"
  by (metis Nil_is_append_conv hd.simps list.exhaust rev.simps(2) rev_rev_ident tl.simps(2))

lemma sm_set_unit: "xs \<in> sm_set (ys @ zs) \<Longrightarrow> xs \<in> sm_set (ys @ 0 # zs)"
proof (induct xs rule: sm_set.induct)
  have "0 # (ys @ 0 # zs) \<in> sm_set (ys @ 0 # zs)"
    by (metis sm_set.self)
  hence "(0 # ys) @ [0] @ zs \<in> sm_set (ys @ 0 # zs)"
    by (metis append_Cons append_Nil)
  hence "(rev (tl (rev (0 # ys))) @ [hd (rev (0 # ys))]) @ [0] @ zs \<in> sm_set (ys @ 0 # zs)"
    by (simp only: inits_last)
  hence "rev (tl (rev (0 # ys))) @ [hd (rev (0 # ys))] @ [0] @ zs \<in> sm_set (ys @ 0 # zs)"
    by (metis append_Cons append_Nil append_assoc)
  hence "rev (tl (rev (0 # ys))) @ [hd (rev (0 # ys))] @ zs \<in> sm_set (ys @ 0 # zs)"
    by (metis monoid_add_class.add.right_neutral sm_set.simps)
  hence "(rev (tl (rev (0 # ys))) @ [hd (rev (0 # ys))]) @ zs \<in> sm_set (ys @ 0 # zs)"
    by (metis append_Cons append_Nil append_assoc)
  hence "(0 # ys) @ zs \<in> sm_set (ys @ 0 # zs)"
    by (simp only: inits_last)
  thus "0 # ys @ zs \<in> sm_set (ys @ 0 # zs)"
    by simp
qed (metis stutter, metis mumble)

hide_fact inits_last

lemma sm_l_prodl: "(X \<cdot> Y)\<^sup>\<ddagger> \<subseteq> (X \<cdot> Y\<^sup>\<ddagger>)\<^sup>\<ddagger>"
  apply (simp add: sm_closure_def l_prod_def complex_product_def)
  apply auto
  apply (rule_tac x = "xb @ 0 # y" in exI)
  apply auto
  by (metis sm_set_unit)

lemma sm_l_prodr: "(X \<cdot> Y)\<^sup>\<ddagger> \<subseteq> (X\<^sup>\<ddagger> \<cdot> Y)\<^sup>\<ddagger>"
  apply (simp add: sm_closure_def l_prod_def complex_product_def)
  apply auto
  apply (rule_tac x = "xb @ 0 # y" in exI)
  apply auto
  apply (rule_tac x = "xb @ [0]" in exI)
  apply auto
  by (metis sm_set_unit)

lemma sm_l_prod_closure: "X\<^sup>\<ddagger> \<cdot>\<^sup>\<ddagger> Y\<^sup>\<ddagger> = X \<cdot>\<^sup>\<ddagger> Y"
proof (simp add: sm_l_prod_def, default)
  show "(X \<cdot> Y)\<^sup>\<ddagger> \<subseteq> (X\<^sup>\<ddagger> \<cdot> Y\<^sup>\<ddagger>)\<^sup>\<ddagger>"
    by (metis order_trans sm_l_prodl sm_l_prodr)
next
  {
    fix xs
    assume "xs \<in> (X\<^sup>\<ddagger> \<cdot> Y\<^sup>\<ddagger>)\<^sup>\<ddagger>"
    hence "xs \<in> (X \<cdot> Y)\<^sup>\<ddagger>"
      apply (auto simp add: sm_closure_def complex_product_def l_prod_def)
      apply (rule_tac x = "xb @ xc" in exI)
      apply auto
      by (metis sm_set_append sm_set_trans)
  }
  thus "(X\<^sup>\<ddagger> \<cdot> Y\<^sup>\<ddagger>)\<^sup>\<ddagger> \<subseteq> (X \<cdot> Y)\<^sup>\<ddagger>" by auto
qed

lemma sm_l_prod_isol: "X \<subseteq> Y \<Longrightarrow> X \<cdot>\<^sup>\<ddagger> Z \<subseteq> Y \<cdot>\<^sup>\<ddagger> Z"
  by (metis l_prod_isol sm_closure_iso sm_l_prod_def)

lemma sm_l_prod_isor: "X \<subseteq> Y \<Longrightarrow> Z \<cdot>\<^sup>\<ddagger> X \<subseteq> Z \<cdot>\<^sup>\<ddagger> Y"
  by (metis l_prod_isor sm_closure_iso sm_l_prod_def)

lemma tshuffle_sm: "\<Union>{map \<langle>id,id\<rangle> ` (xs' \<sha> ys)|xs'. xs' \<in> sm_set xs} \<subseteq> (map \<langle>id,id\<rangle> ` (xs \<sha> ys))\<^sup>\<ddagger>"
proof (auto simp add: sm_closure_def)
  fix xs' zs'

  assume "xs' \<in> sm_set xs" and "zs' \<in> xs' \<sha> ys"

  thus "\<exists>zs\<in>xs \<sha> ys. map \<langle>id,id\<rangle> zs' \<in> sm_set (map \<langle>id,id\<rangle> zs)"
  proof (induct xs' arbitrary: zs' rule: sm_set.induct)
    fix zs' :: "('a, 'a) sum list"
    assume zs'_set: "zs' \<in> (0 # xs) \<sha> ys"

    thus "\<exists>zs\<in>xs \<sha> ys. map \<langle>id,id\<rangle> zs' \<in> sm_set (map \<langle>id,id\<rangle> zs)"
    proof (cases "ys = []", simp, metis sm_set.self)
      assume ys_not_empty: "ys \<noteq> []"

      from zs'_set
      have zs'_lefts: "\<ll> zs' = 0 # xs"
      and zs'_rights: "\<rr> zs' = ys"
        by (metis (lifting, full_types) mem_Collect_eq tshuffle_words_def)+

      hence delete_left_non_empty: "delete_left 0 zs' \<noteq> []"
      proof -
        have "\<rr> zs' \<noteq> []"
          by (metis `\<rr> zs' = ys` ys_not_empty)
        hence "\<rr> (delete_left 0 zs') \<noteq> []"
          by (induct zs' rule: sum_list_induct) auto
        hence "\<not> (\<ll> (delete_left 0 zs') = [] \<and> \<rr> (delete_left 0 zs') = [])"
          by blast
        thus ?thesis
          by simp
      qed

      have zs'_split: "zs' = take_left 0 zs' @ [Inl 0] @ tl (drop_left 0 zs')"
        by (rule lefts_insert) (auto intro: zs'_lefts)

      from delete_left_non_empty
      have "map \<langle>id,id\<rangle> (delete_left 0 zs') \<in> sm_set (map \<langle>id,id\<rangle> (delete_left 0 zs'))"
        by (metis (full_types) Nil_is_map_conv neq_Nil_conv sm_set_self_var)

      hence "map \<langle>id,id\<rangle> (take_left 0 zs') @ map \<langle>id,id\<rangle> (tl (drop_left 0 zs')) \<in> sm_set (map \<langle>id,id\<rangle> (delete_left 0 zs'))"
        by (metis delete_left_def map_append)

      hence "map \<langle>id,id\<rangle> (take_left 0 zs') @ [0] @ map \<langle>id,id\<rangle> (tl (drop_left 0 zs')) \<in> sm_set (map \<langle>id,id\<rangle> (delete_left 0 zs'))"
        by (metis Cons_eq_appendI eq_Nil_appendI sm_set.stutter)

      hence "map \<langle>id,id\<rangle> (take_left 0 zs' @ [Inl 0] @ tl (drop_left 0 zs')) \<in> sm_set (map \<langle>id,id\<rangle> (delete_left 0 zs'))"
        by (metis left_singleton map_append)

      hence "map \<langle>id,id\<rangle> zs' \<in> sm_set (map \<langle>id,id\<rangle> (delete_left 0 zs'))"
        by (subst zs'_split, assumption)

      thus "\<exists>zs\<in>xs \<sha> ys. map \<langle>id,id\<rangle> zs' \<in> sm_set (map \<langle>id,id\<rangle> zs)"
        by (rule_tac x = "delete_left 0 zs'" in bexI) (auto simp add: tshuffle_words_def zs'_rights zs'_lefts)
    qed
  next
    fix as :: "'a list" and bs :: "'a list" and zs' :: "('a, 'a) sum list"

    assume "as @ bs \<in> sm_set xs"
    and ih: "\<And>zs'. zs' \<in> (as @ bs) \<sha> ys \<Longrightarrow> \<exists>zs\<in>xs \<sha> ys. map \<langle>id,id\<rangle> zs' \<in> sm_set (map \<langle>id,id\<rangle> zs)"
    and zs'_set: "zs' \<in> (as @ [0] @ bs) \<sha> ys"

    have zs'_split: "zs' = take_left (length as) zs' @ [Inl 0] @ tl (drop_left (length as) zs')"
      by (rule lefts_insert, insert zs'_set, simp_all add: tshuffle_words_def)

    from zs'_set have "delete_left (length as) zs' \<in> (as @ bs) \<sha> ys"
      by (auto simp add: tshuffle_words_def intro: delete_left_lefts)

    then obtain zs where zs_set: "zs \<in> xs \<sha> ys"
    and "map \<langle>id,id\<rangle> (delete_left (length as) zs') \<in> sm_set (map \<langle>id,id\<rangle> zs)"
      by (metis ih)

    hence "map \<langle>id,id\<rangle> (take_left (length as) zs') @ map \<langle>id,id\<rangle> (tl (drop_left (length as) zs')) \<in> sm_set (map \<langle>id,id\<rangle> zs)"
      by (metis delete_left_def map_append)

    hence "map \<langle>id,id\<rangle> (take_left (length as) zs') @ [0] @ map \<langle>id,id\<rangle> (tl (drop_left (length as) zs')) \<in> sm_set (map \<langle>id,id\<rangle> zs)"
      by (metis sm_set.stutter)

    hence "map \<langle>id,id\<rangle> (take_left (length as) zs' @ [Inl 0] @ tl (drop_left (length as) zs')) \<in> sm_set (map \<langle>id,id\<rangle> zs)"
      by simp

    hence "map \<langle>id,id\<rangle> zs' \<in> sm_set (map \<langle>id,id\<rangle> zs)"
      by (metis zs'_split)

    thus "\<exists>zs\<in>xs \<sha> ys. map \<langle>id,id\<rangle> zs' \<in> sm_set (map \<langle>id,id\<rangle> zs)"
      by (metis zs_set)
  next
    fix as :: "'a::monoid_add list" and b :: "'a" and c :: "'a" and ds :: "'a list"
    and zs' :: "('a, 'a) sum list"

    assume ih: "\<And>zs'. zs' \<in> (as @ [b] @ [c] @ ds) \<sha> ys \<Longrightarrow> \<exists>zs\<in>xs \<sha> ys. map \<langle>id,id\<rangle> zs' \<in> sm_set (map \<langle>id,id\<rangle> zs)"
    and zs'_set: "zs' \<in> (as @ [b + c] @ ds) \<sha> ys"

    have zs'_split: "zs' = take_left (length as) zs' @ [Inl (b + c)] @ tl (drop_left (length as) zs')"
      by (rule lefts_insert, insert zs'_set, simp_all add: tshuffle_words_def)

    from zs'_set have "take_left (length as) zs' @ [Inl b] @ [Inl c] @ tl (drop_left (length as) zs') \<in> (as @ [b] @ [c] @ ds) \<sha> ys"
      apply (auto simp add: tshuffle_words_def)
      apply (metis drop_lefts_is_append take_lefts_is_append)
      by (metis delete_left_def delete_left_rights right_append)

    then obtain zs where zs_set: "zs \<in> xs \<sha> ys"
    and "map \<langle>id,id\<rangle> (take_left (length as) zs' @ [Inl b] @ [Inl c] @ tl (drop_left (length as) zs')) \<in> sm_set (map \<langle>id,id\<rangle> zs)"
      by (metis ih)

    hence "map \<langle>id,id\<rangle> (take_left (length as) zs') @ [b] @ [c] @ map \<langle>id,id\<rangle> (tl (drop_left (length as) zs')) \<in> sm_set (map \<langle>id,id\<rangle> zs)"
      by simp

    hence "map \<langle>id,id\<rangle> (take_left (length as) zs') @ [b + c] @ map \<langle>id,id\<rangle> (tl (drop_left (length as) zs')) \<in> sm_set (map \<langle>id,id\<rangle> zs)"
      by (metis sm_set.mumble)

    hence "map \<langle>id,id\<rangle> (take_left (length as) zs' @ [Inl (b + c)] @ tl (drop_left (length as) zs')) \<in> sm_set (map \<langle>id,id\<rangle> zs)"
      by simp

    hence "map \<langle>id,id\<rangle> zs' \<in> sm_set (map \<langle>id,id\<rangle> zs)"
      by (metis zs'_split)

    thus "\<exists>zs\<in>xs \<sha> ys. map \<langle>id,id\<rangle> zs' \<in> sm_set (map \<langle>id,id\<rangle> zs)"
      by (metis zs_set)
  qed
qed

lemma shuffle_sm: "X\<^sup>\<ddagger> \<parallel> Y \<subseteq> (X \<parallel> Y)\<^sup>\<ddagger>"
proof -
  have "X\<^sup>\<ddagger> \<parallel> Y = \<Union>sm_set ` X \<parallel> Y"
    by (simp add: sm_closure_def)
  also have "... = \<Union>{sm_set xs \<parallel> Y|xs. xs \<in> X}"
    by (subst shuffle_inf_distr) (auto simp add: image_def)
  also have "... = \<Union>{\<Union>{map \<langle>id,id\<rangle> ` (xs' \<sha> ys) |xs' ys. xs' \<in> sm_set xs \<and> ys \<in> Y}|xs. xs \<in> X}"
    by (simp add: shuffle_def)
  also have "... = \<Union>{\<Union>{map \<langle>id,id\<rangle> ` (xs' \<sha> ys) |xs'. xs' \<in> sm_set xs}|xs ys. xs \<in> X \<and> ys \<in> Y}"
    by blast
  also have "... \<subseteq> \<Union>{(map \<langle>id,id\<rangle> ` (xs \<sha> ys))\<^sup>\<ddagger>|xs ys. xs \<in> X \<and> ys \<in> Y}"
    by (insert tshuffle_sm) blast
  also have "... = \<Union>{\<Union>zs\<in>xs \<sha> ys. sm_set (map \<langle>id,id\<rangle> zs)|xs ys. xs \<in> X \<and> ys \<in> Y}"
    by (simp add: sm_closure_def)
  also have "... = (X \<parallel> Y)\<^sup>\<ddagger>"
    by (auto simp add: shuffle_def sm_closure_def)
  finally show ?thesis .
qed

lemma tshuffle_sm2: "(map \<langle>id,id\<rangle> ` (xs \<sha> ys))\<^sup>\<ddagger> \<subseteq> (\<Union>{map \<langle>id,id\<rangle> ` (xs \<sha> ys')|ys'. ys' \<in> sm_set ys})\<^sup>\<ddagger>"
proof -
  have  "(map \<langle>id,id\<rangle> ` (xs \<sha> []))\<^sup>\<ddagger> \<subseteq> (\<Union>{map \<langle>id,id\<rangle> ` (xs \<sha> ys')|ys'. ys' \<in> sm_set []})\<^sup>\<ddagger>"
    apply (auto simp add: sm_closure_def)
    apply (rule_tac x = "map \<langle>id,id\<rangle> ` (xs \<sha> [0])" in exI)
    apply (intro conjI)
    defer
    apply (rule_tac x = "map \<langle>id,id\<rangle> (Inr 0 # map Inl xs)" in bexI)
    apply simp
    apply (metis sm_set_cons_unit)
    defer
    apply (rule_tac x = "[0]" in exI)
    apply simp
    apply (metis sm_set.self)
    apply (auto simp add: tshuffle_words_def image_def)
    apply (rule_tac x = "Inr 0 # map Inl xs" in exI)
    by simp

  moreover {
    fix y ys
    have "(map \<langle>id,id\<rangle> ` (xs \<sha> (y#ys)))\<^sup>\<ddagger> \<subseteq> (\<Union>{map \<langle>id,id\<rangle> ` (xs \<sha> ys')|ys'. ys' \<in> sm_set (y#ys)})\<^sup>\<ddagger>"
      apply (auto simp add: sm_closure_def)
      apply (rule_tac x = "map \<langle>id,id\<rangle> ` (xs \<sha> (y#ys))" in exI)
      apply (intro conjI)
      defer
      apply (rule_tac x = "map \<langle>id,id\<rangle> a" in bexI)
      apply simp
      apply (metis image_iff)
      apply (rule_tac x = "y#ys" in exI)
      apply simp
      by (metis sm_set_self_var)
  }

  ultimately show ?thesis
    by (cases ys) auto
qed

lemma shuffle_sm_var: "(X \<parallel> Y)\<^sup>\<ddagger> \<subseteq> (X \<parallel> Y\<^sup>\<ddagger>)\<^sup>\<ddagger>"
proof -
  have "(X \<parallel> Y)\<^sup>\<ddagger> = \<Union>sm_set ` (X \<parallel> Y)"
    by (simp add: sm_closure_def)
  also have "... = \<Union>sm_set ` \<Union>{map \<langle>id,id\<rangle> ` (xs \<sha> ys)|xs ys. xs \<in> X \<and> ys \<in> Y}"
    by (simp add: shuffle_def)
  also have "... = \<Union>{\<Union>sm_set ` map \<langle>id,id\<rangle> ` (xs \<sha> ys)|xs ys. xs \<in> X \<and> ys \<in> Y}"
    by (auto simp add: image_def)
  also have "... = \<Union>{(map \<langle>id,id\<rangle> ` (xs \<sha> ys))\<^sup>\<ddagger>|xs ys. xs \<in> X \<and> ys \<in> Y}"
    by (auto simp add: sm_closure_def)
  also have "... \<subseteq> \<Union>{(\<Union>{map \<langle>id,id\<rangle> ` (xs \<sha> ys')|ys'. ys' \<in> sm_set ys})\<^sup>\<ddagger>|xs ys. xs \<in> X \<and> ys \<in> Y}"
    by (insert tshuffle_sm2) blast
  also have "... = \<Union>{\<Union>sm_set ` \<Union>{map \<langle>id,id\<rangle> ` (xs \<sha> ys') |ys'. ys' \<in> sm_set ys} |xs ys. xs \<in> X \<and> ys \<in> Y}"
    by (simp only: sm_closure_def)
  also have "... = \<Union>sm_set ` \<Union>{map \<langle>id,id\<rangle> ` (xs \<sha> ys)|xs ys. xs \<in> X \<and> ys \<in> \<Union>(sm_set ` Y)}"
    by (simp add: image_def) blast
  also have "... = (\<Union>{map \<langle>id,id\<rangle> ` (xs \<sha> ys)|xs ys. xs \<in> X \<and> ys \<in> Y\<^sup>\<ddagger>})\<^sup>\<ddagger>"
    by (simp add: sm_closure_def)
  also have "... = (X \<parallel> Y\<^sup>\<ddagger>)\<^sup>\<ddagger>"
    by (simp add: shuffle_def)
  finally show ?thesis .
qed

lemma shuffle_closure: "X \<parallel>\<^sup>\<ddagger> Y = X\<^sup>\<ddagger> \<parallel>\<^sup>\<ddagger> Y\<^sup>\<ddagger>"
  by (metis (hide_lams, no_types) shuffle_comm shuffle_sm shuffle_sm_var sm_closure_idem sm_closure_iso sm_shuffle_def subset_antisym)

lemma sm_shuffle_assoc: "(X \<parallel>\<^sup>\<ddagger> Y) \<parallel>\<^sup>\<ddagger> Z = X \<parallel>\<^sup>\<ddagger> (Y \<parallel>\<^sup>\<ddagger> Z)"
  by (metis (hide_lams, no_types) shuffle_assoc shuffle_closure sm_closure_idem sm_shuffle_def)

lemma sm_shuffle_comm: "X \<parallel>\<^sup>\<ddagger> Y = Y \<parallel>\<^sup>\<ddagger> X"
  by (metis sm_shuffle_def shuffle_comm)

lemma sm_exchange: "(A \<parallel>\<^sup>\<ddagger> B) \<cdot>\<^sup>\<ddagger> (C \<parallel>\<^sup>\<ddagger> D) \<subseteq> (B \<cdot>\<^sup>\<ddagger> C) \<parallel>\<^sup>\<ddagger> (A \<cdot>\<^sup>\<ddagger> D)"
  by (metis (hide_lams, no_types) exchange shuffle_closure sm_closure_iso sm_l_prod_closure sm_l_prod_def sm_shuffle_def)

lemma sm_par_iso: "X \<subseteq> Y \<Longrightarrow> X \<parallel>\<^sup>\<ddagger> Z \<subseteq> Y \<parallel>\<^sup>\<ddagger> Z"
  by (metis sm_shuffle_def sm_closure_iso shuffle_iso)

lemma atomic_sm_closure: "\<langle>X\<rangle> = \<langle>X\<^sup>\<ddagger>\<rangle>"
  apply (auto simp add: atomic_def sm_closure_def)
  apply (metis listsum_simps(2) monoid_add_class.add.left_neutral sm_set.self)
  by (metis sm_set_listsum sm_set_trans)

lemma atomic_l_prod: "\<langle>X \<cdot> Y\<rangle> = \<langle>X \<cdot>\<^sup>\<ddagger> Y\<rangle>"
  by (metis atomic_sm_closure sm_l_prod_def)

lemma atomic_split_l_prod: "\<langle>X \<cdot> Y\<rangle> \<subseteq> \<langle>X\<rangle> \<cdot>\<^sup>\<ddagger> \<langle>Y\<rangle>"
proof -
  have "\<langle>X \<cdot> Y\<rangle> = {[listsum (x @ y)]|x y. x \<in> X \<and> y \<in> Y}\<^sup>\<ddagger>"
    apply (simp add: l_prod_def complex_product_def atomic_def)
    apply (rule arg_cong) back
    by (auto, metis, metis listsum_append)
  also have "... \<subseteq> {[listsum x] @ [listsum y]|x y. x \<in> X \<and> y \<in> Y}\<^sup>\<ddagger>"
  proof (auto simp add: sm_closure_def)
    fix x y z
    assume "z \<in> sm_set [listsum x + listsum y]" and xX: "x \<in> X" and yY: "y \<in> Y"
    hence "z \<in> sm_set [listsum (x @ y)]"
      by (metis listsum_append)
    hence "z \<in> sm_set ([listsum x, listsum y])"
      apply (induct z rule: sm_set.induct)
      apply (metis listsum_append sm_set.self sm_set_pair sm_set_trans)
      apply (metis sm_set.stutter)
      by (metis sm_set.mumble)
    thus "\<exists>z'. (\<exists>x y. z' = [listsum x, listsum y] \<and> x \<in> X \<and> y \<in> Y) \<and> z \<in> sm_set z'"
      by (metis xX yY)
  qed
  also have "... = {x @ y |x y. x \<in> {[listsum x] |x. x \<in> X} \<and> y \<in> {[listsum x] |x. x \<in> Y}}\<^sup>\<ddagger>"
    by (rule arg_cong, blast)
  also have "... \<subseteq> \<langle>X\<rangle> \<cdot>\<^sup>\<ddagger> \<langle>Y\<rangle>"
    by (simp only: atomic_def) (metis (no_types) complex_product_def eq_iff l_prod_def sm_l_prod_closure sm_l_prod_def)
  finally show ?thesis .
qed

lemma atomic_l_prod_idem: "\<langle>X \<cdot> \<langle>Y\<rangle> \<cdot> Z\<rangle> = \<langle>X \<cdot> Y \<cdot> Z\<rangle>"
proof
  have "\<langle>X \<cdot> \<langle>Y\<rangle> \<cdot> Z\<rangle> \<subseteq> \<langle>X \<cdot> Y\<^sup>\<ddagger> \<cdot> Z\<rangle>"
    by (metis atomic_sm_closure atomic_iso l_prod_isol l_prod_isor atomic_coextensive)
  also have "... =  \<langle>X \<cdot> Y \<cdot> Z\<rangle>"
    by (metis (hide_lams, no_types) atomic_l_prod sm_closure_idem sm_l_prod_closure sm_l_prod_def)
  finally show "\<langle>X \<cdot> \<langle>Y\<rangle> \<cdot> Z\<rangle> \<subseteq> \<langle>X \<cdot> Y \<cdot> Z\<rangle>" .

  have "\<langle>X \<cdot> Y \<cdot> Z\<rangle> = \<langle>\<langle>X \<cdot> Y \<cdot> Z\<rangle>\<rangle>"
    by (metis atomic_idem)
  also have "... = \<langle>\<langle>X\<^sup>\<ddagger> \<cdot> Y\<^sup>\<ddagger> \<cdot> Z\<^sup>\<ddagger>\<rangle>\<rangle>"
    by (metis (hide_lams, no_types) atomic_sm_closure sm_closure_idem sm_l_prod_closure sm_l_prod_def)
  also have "... \<subseteq> \<langle>\<langle>X\<^sup>\<ddagger> \<cdot> Y\<^sup>\<ddagger>\<rangle> \<cdot>\<^sup>\<ddagger> \<langle>Z\<^sup>\<ddagger>\<rangle>\<rangle>"
    by (metis atomic_iso atomic_split_l_prod)
  also have "... \<subseteq> \<langle>\<langle>X\<^sup>\<ddagger>\<rangle> \<cdot>\<^sup>\<ddagger> \<langle>Y\<^sup>\<ddagger>\<rangle> \<cdot>\<^sup>\<ddagger> \<langle>Z\<^sup>\<ddagger>\<rangle>\<rangle>"
    by (metis (mono_tags) atomic_iso atomic_sm_closure atomic_split_l_prod l_prod_isol sm_l_prod_def)
  also have "... = \<langle>\<langle>X\<^sup>\<ddagger>\<rangle> \<cdot> \<langle>Y\<^sup>\<ddagger>\<rangle> \<cdot> \<langle>Z\<^sup>\<ddagger>\<rangle>\<rangle>"
    by (metis (hide_lams, no_types) atomic_sm_closure sm_closure_idem sm_l_prod_closure sm_l_prod_def)
  also have "... \<subseteq> \<langle>X\<^sup>\<ddagger> \<cdot> \<langle>Y\<^sup>\<ddagger>\<rangle> \<cdot> Z\<^sup>\<ddagger>\<rangle>"
    by (metis (hide_lams, no_types) atomic_coextensive atomic_iso l_prod_isol l_prod_isor order_trans)
  also have "... = \<langle>X \<cdot> \<langle>Y\<rangle> \<cdot> Z\<rangle>"
    by (metis (hide_lams, no_types) atomic_sm_closure sm_closure_idem sm_l_prod_closure sm_l_prod_def)
  finally show "\<langle>X \<cdot> Y \<cdot> Z\<rangle> \<subseteq> \<langle>X \<cdot> \<langle>Y\<rangle> \<cdot> Z\<rangle>" .
qed

lemma atomic_union: "\<langle>X \<union> Y\<rangle> = \<langle>X\<rangle> \<union> \<langle>Y\<rangle>"
  by (auto simp add: atomic_def sm_closure_def)

lemma sm_join_preserving: "\<Union>{X\<^sup>\<ddagger>|X. X \<in> \<XX>} = (\<Union>\<XX>)\<^sup>\<ddagger>"
  by (auto simp add: sm_closure_def)

lemma sm_join_preserving_var: "\<Union>{(f X)\<^sup>\<ddagger>|X. X \<in> \<XX>} = (\<Union>f`\<XX>)\<^sup>\<ddagger>"
  by (auto simp add: sm_closure_def)

lemma sm_shuffle_inf_distl: "X \<parallel>\<^sup>\<ddagger> \<Union>\<YY> = \<Union>{X \<parallel>\<^sup>\<ddagger> Y|Y. Y \<in> \<YY>}"
proof -
  have "X \<parallel>\<^sup>\<ddagger> \<Union>\<YY> = (\<Union>{X \<parallel> Y|Y. Y \<in> \<YY>})\<^sup>\<ddagger>"
    by (metis shuffle_inf_distl sm_shuffle_def)
  also have "... = \<Union>{X \<parallel>\<^sup>\<ddagger> Y|Y. Y \<in> \<YY>}"
    by (simp add: sm_shuffle_def sm_join_preserving_var, rule arg_cong, blast)
  finally show ?thesis .
qed

lemma sm_shuffle_inf_distr: "\<Union>\<XX> \<parallel>\<^sup>\<ddagger> Y = \<Union>{X \<parallel>\<^sup>\<ddagger> Y|X. X \<in> \<XX>}"
  by (subst sm_shuffle_comm, subst sm_shuffle_comm, rule sm_shuffle_inf_distl)

lemma sm_l_prod_inf_distl: "X \<cdot>\<^sup>\<ddagger> \<Union>\<YY> = \<Union>{X \<cdot>\<^sup>\<ddagger> Y|Y. Y \<in> \<YY>}"
proof -
  have "X \<cdot>\<^sup>\<ddagger> \<Union>\<YY> = (\<Union>{X \<cdot> Y|Y. Y \<in> \<YY>})\<^sup>\<ddagger>"
    by (metis l_prod_inf_distl sm_l_prod_def)
  also have "... = \<Union>{X \<cdot>\<^sup>\<ddagger> Y|Y. Y \<in> \<YY>}"
    by (simp add: sm_l_prod_def sm_join_preserving_var, rule arg_cong, blast)
  finally show ?thesis .
qed

lemma sm_l_prod_inf_distr: "\<Union>\<XX> \<cdot>\<^sup>\<ddagger> Y = \<Union>{X \<cdot>\<^sup>\<ddagger> Y|X. X \<in> \<XX>}"
proof -
  have "\<Union>\<XX> \<cdot>\<^sup>\<ddagger> Y = (\<Union>{X \<cdot> Y|X. X \<in> \<XX>})\<^sup>\<ddagger>"
    by (metis l_prod_inf_distr sm_l_prod_def)
  also have "... = \<Union>{X \<cdot>\<^sup>\<ddagger> Y|X. X \<in> \<XX>}"
    by (simp add: sm_l_prod_def sm_join_preserving_var, rule arg_cong, blast)
  finally show ?thesis .
qed

lemma sm_shuffle_one [simp]: shows "\<one> \<parallel>\<^sup>\<ddagger> X = X\<^sup>\<ddagger>" and "X \<parallel>\<^sup>\<ddagger> \<one> = X\<^sup>\<ddagger>"
proof -
  have "\<one> \<parallel>\<^sup>\<ddagger> X = ({[]}\<^sup>\<ddagger> \<parallel> X)\<^sup>\<ddagger>"
    by (simp add: sm_shuffle_def sm_one_def)
  also have "... = ({[]} \<parallel> X)\<^sup>\<ddagger>"
    by (metis (hide_lams, no_types) shuffle_closure sm_closure_idem sm_shuffle_def)
  also have "... = X\<^sup>\<ddagger>"
    by (metis shuffle_one(2))
  finally show "\<one> \<parallel>\<^sup>\<ddagger> X = X\<^sup>\<ddagger>" . 

  thus "X \<parallel>\<^sup>\<ddagger> \<one> = X\<^sup>\<ddagger>"
    by (metis sm_shuffle_comm)
qed

lemma sm_zero [simp]: "{}\<^sup>\<ddagger> = {}"
  by (auto simp add: sm_closure_def)

lemma sm_shuffle_zero [simp]: shows "{} \<parallel>\<^sup>\<ddagger> X = {}" and "X \<parallel>\<^sup>\<ddagger> {} = {}"
proof -
  show "{} \<parallel>\<^sup>\<ddagger> X = {}"
    by (simp add: sm_shuffle_def)

  thus "X \<parallel>\<^sup>\<ddagger> {} = {}"
    by (metis sm_shuffle_comm)
qed

lemma atomic_one [simp]: "\<langle>\<one>\<rangle> = \<one>"
proof -
  have "\<one> \<subseteq> \<langle>\<one>\<rangle>"
    apply (auto simp add: atomic_def sm_one_def sm_closure_def)
    apply (rule_tac x = "[0]" in exI)
    apply auto
    apply (rule_tac x = "[0]" in exI)
    apply (metis append_Nil listsum_append listsum_simps(1) listsum_simps(2) sm_set.self)
    by (metis sm_set_cons_unit)

  thus "\<langle>\<one>\<rangle> = \<one>"
    by (metis atomic_coextensive sm_one_def subset_antisym)
qed

lemma sm_set_self_replicate [intro]: "replicate (Suc n) 0 @ xs \<in> sm_set xs"
  by (induct n, auto) (metis sm_set.self sm_set_trans)

lemma sm_set_self_replicate_rev [intro]: "xs @ replicate (Suc n) 0 \<in> sm_set xs"
  by (induct n, auto) (metis append_Cons eq_Nil_appendI sm_set.stutter)

lemma replicate_range: "xs \<in> range (\<lambda>n. replicate (f n) x) \<Longrightarrow> xs = replicate (length xs) x"
  by (metis (mono_tags) length_replicate rangeE)

lemma replicate_head: "x # xs = replicate n y \<Longrightarrow> x = y"
  by (metis hd.simps hd_replicate list.distinct(1) replicate_0)

lemma replicate_rev: "x # xs = replicate n y \<Longrightarrow> x # xs = xs @ [x]"
  apply (induct xs)
  apply auto
  by (metis Cons_eq_appendI append_Nil2 hd.simps replicate_app_Cons_same tl.simps(2))

lemma replicate_append_rev: "xs @ ys = replicate n x \<Longrightarrow> xs @ ys = ys @ xs"
  apply (induct xs arbitrary: ys)
  apply auto
  by (metis append_Cons append_assoc eq_Nil_appendI replicate_rev)

lemma sm_set_empty_def: "sm_set [] = range (\<lambda>n. replicate (Suc n) 0)"
proof (auto simp del: replicate_Suc)
  fix xs :: "'a list"
  assume "xs \<in> sm_set []"
  thus "xs \<in> range (\<lambda>n. replicate (Suc n) 0)"
  proof (induct xs rule: sm_set.induct)
    show "[0] \<in> range (\<lambda>n. replicate (Suc n) 0)"
      by simp
  next
    fix as bs :: "'a list"
    assume "as @ bs \<in> range (\<lambda>n. replicate (Suc n) 0)"
    hence "as @ bs = replicate (length (as @ bs)) 0"
      by (induct as, auto) (metis length_append length_replicate)
    hence "as = replicate (length as) 0 \<and> bs = replicate (length bs) 0"
      by (simp add: replicate_add)
    thus "as @ [0] @ bs \<in> range (\<lambda>n. replicate (Suc n) 0)"
      apply simp
      apply clarify
      apply (erule ssubst)+
      apply (subst replicate_Suc[symmetric])
      apply (subst replicate_add[symmetric])
      by auto
  next
    fix bs cs :: 'a and as ds :: "'a list"
    assume "as @ [bs] @ [cs] @ ds \<in> range (\<lambda>n. replicate (Suc n) 0)"
    hence rep: "as @ [bs] @ [cs] @ ds = replicate (length (as @ [bs] @ [cs] @ ds)) 0"
      by (metis replicate_range)
    {
      from rep have "as @ [bs] @ [cs] @ ds = ([bs] @ [cs] @ ds) @ as"
        by (metis replicate_append_rev)
      also have "... = [bs] @ [cs] @ ds @ as"
        by (metis append_assoc)
      finally have "as @ [bs] @ [cs] @ ds = [bs] @ [cs] @ ds @ as" .
      moreover from rep and this have "... = [bs] @ [cs] @ as @ ds"
        apply (subgoal_tac "as @ ds = replicate (length (as @ ds)) 0")
        apply simp
        apply simp
        apply clarify
        by (metis replicate_append_rev)
      ultimately have "[bs] @ [cs] @ as @ ds = replicate (length (as @ [bs] @ [cs] @ ds)) 0" using rep
        by metis
    }
    hence "as = replicate (length as) 0 \<and> bs = 0 \<and> cs = 0 \<and> ds = replicate (length ds) 0"
      by (simp add: replicate_add)
    thus "as @ [bs + cs] @ ds \<in> range (\<lambda>n. replicate (Suc n) 0)"
      apply clarify
      apply (erule ssubst)+
      apply simp
      apply (subst replicate_Suc[symmetric])
      apply (subst replicate_add[symmetric])
      by auto
  qed
next
  fix n
  show "replicate (Suc n) 0 \<in> sm_set []"
    by (induct n, auto) (metis sm_set.self sm_set_trans)
qed

hide_fact replicate_range replicate_head replicate_rev replicate_append_rev

lemmas sm_one_replicate = trans[OF sm_set_one sm_set_empty_def]

lemma sm_l_prod_one [simp]: shows "\<one> \<cdot>\<^sup>\<ddagger> X = X\<^sup>\<ddagger>" and "X \<cdot>\<^sup>\<ddagger> \<one> = X\<^sup>\<ddagger>"
proof -
  have "\<one> \<cdot>\<^sup>\<ddagger> X = (range (\<lambda>n. replicate (Suc n) 0) \<cdot> X)\<^sup>\<ddagger>"
    by (simp add: sm_l_prod_def sm_one_replicate)
  also have "... = {u @ xs|u xs. u \<in> range (\<lambda>n. replicate (Suc n) 0) \<and> xs \<in> X}\<^sup>\<ddagger>"
    by (simp add: l_prod_def complex_product_def)
  also have "... = {replicate (Suc n) 0 @ xs|n xs. n \<in> UNIV \<and> xs \<in> X}\<^sup>\<ddagger>"
    by (metis (lifting) UNIV_I rangeE rev_image_eqI)
  finally have "\<one> \<cdot>\<^sup>\<ddagger> X = {replicate (Suc n) 0 @ xs|n xs. n \<in> UNIV \<and> xs \<in> X}\<^sup>\<ddagger>" .

  moreover have "{replicate (Suc n) 0 @ xs|n xs. n \<in> UNIV \<and> xs \<in> X}\<^sup>\<ddagger> \<subseteq> X\<^sup>\<ddagger>"
    by (auto simp add: sm_closure_def) (metis append_Cons replicate_Suc sm_set_self_replicate sm_set_trans)
  moreover have "X\<^sup>\<ddagger> \<subseteq> {replicate (Suc n) 0 @ xs|n xs. n \<in> UNIV \<and> xs \<in> X}\<^sup>\<ddagger>"
    by (auto simp add: sm_closure_def) (metis append_self_conv2 replicate_0 sm_set_cons_unit)
  ultimately show "\<one> \<cdot>\<^sup>\<ddagger> X = X\<^sup>\<ddagger>"
    by auto

  have "X \<cdot>\<^sup>\<ddagger> \<one> = (X \<cdot> range (\<lambda>n. replicate (Suc n) 0))\<^sup>\<ddagger>"
    by (simp add: sm_l_prod_def sm_one_replicate)
  also have "... = {xs @ u|xs u. xs \<in> X \<and> u \<in> range (\<lambda>n. replicate (Suc n) 0)}\<^sup>\<ddagger>"
    by (simp add: l_prod_def complex_product_def)
  also have "... = {xs @ replicate (Suc n) 0|xs n. xs \<in> X \<and> n \<in> UNIV}\<^sup>\<ddagger>"
    by (metis (lifting) UNIV_I rangeE rev_image_eqI)
  finally have "X \<cdot>\<^sup>\<ddagger> \<one> = {xs @ replicate (Suc n) 0|xs n. xs \<in> X \<and> n \<in> UNIV}\<^sup>\<ddagger>" .

  moreover have "{xs @ replicate (Suc n) 0|xs n. xs \<in> X \<and> n \<in> UNIV}\<^sup>\<ddagger> \<subseteq> X\<^sup>\<ddagger>"
    by (auto simp add: sm_closure_def) (metis replicate_Suc sm_set_self_replicate_rev sm_set_trans)
  moreover have "X\<^sup>\<ddagger> \<subseteq> {xs @ replicate (Suc n) 0|xs n. xs \<in> X \<and> n \<in> UNIV}\<^sup>\<ddagger>"
    by (auto simp add: sm_closure_def) (metis append_Nil2 replicate_0 sm_set_unit)
  ultimately show "X \<cdot>\<^sup>\<ddagger> \<one> = X\<^sup>\<ddagger>"
    by auto
qed

section {* Sequential Star *}

primrec l_power :: "'a lan \<Rightarrow> nat \<Rightarrow> 'a lan" ("_\<^bsup>_\<^esup>" [101,0] 100) where
  "X\<^bsup>0\<^esup> = {[]}"
| "X\<^bsup>Suc n\<^esup> = X \<cdot> X\<^bsup>n\<^esup>"

no_notation
  Transitive_Closure.rtrancl ("(_\<^sup>*)" [1000] 999)

definition l_star :: "'a lan \<Rightarrow> 'a lan" ("_\<^sup>*" [101] 100) where
  "X\<^sup>* \<equiv> \<Union>range (l_power X)"

lemma [intro]: "[] \<in> X\<^bsup>0\<^esup>"
  by (metis insertI1 l_power.simps(1))

lemma power_in_star: "X\<^bsup>n\<^esup> \<subseteq> X\<^sup>*"
  by (auto simp add: l_star_def)

lemma [intro]: "xs \<in> X \<Longrightarrow> ys \<in> X\<^bsup>n\<^esup> \<Longrightarrow> xs @ ys \<in> X\<^bsup>Suc n\<^esup>"
  by (auto simp add: in_l_prod)

lemma l_power_def_var: "X\<^bsup>Suc n\<^esup> = X\<^bsup>n\<^esup> \<cdot> X"
  by (induct n) (simp_all add: l_prod_assoc[symmetric])

lemma [intro]: "xs \<in> X \<Longrightarrow> ys \<in> X\<^bsup>n\<^esup> \<Longrightarrow> ys @ xs \<in> X\<^bsup>Suc n\<^esup>"
  by (auto simp add: in_l_prod l_power_def_var simp del: l_power.simps(2))

lemma l_star_unfoldl: "{[]} \<union> X\<cdot>X\<^sup>* \<subseteq> X\<^sup>*"
  by (auto simp add: l_star_def l_prod_def complex_product_def)

lemma l_star_unfoldr: "{[]} \<union> X\<^sup>*\<cdot>X \<subseteq> X\<^sup>*"
  by (auto simp add: l_star_def l_prod_def complex_product_def)

lemma l_power_inductl: "Z \<union> X\<cdot>Y \<subseteq> Y \<Longrightarrow> X\<^bsup>n\<^esup>\<cdot>Z \<subseteq> Y"
  by (induct n, simp_all, metis l_prod_assoc l_prod_isor subset_trans)

lemma l_star_inductl: "Z \<union> X\<cdot>Y \<subseteq> Y \<Longrightarrow> X\<^sup>*\<cdot>Z \<subseteq> Y"
proof -
  assume asm: "Z \<union> X\<cdot>Y \<subseteq> Y"
  have "\<Union>range (\<lambda>n. X\<^bsup>n\<^esup> \<cdot> Z) \<subseteq> Y"
    by (auto, metis asm in_mono l_power_inductl)
  moreover have "\<Union>range (\<lambda>n. X\<^bsup>n\<^esup> \<cdot> Z) = \<Union>range (l_power X) \<cdot> Z"
    by (auto simp add: l_prod_def complex_product_def)
  ultimately show "X\<^sup>*\<cdot>Z \<subseteq> Y"
    by (metis l_star_def)
qed

lemma l_power_inductr: "Z \<union> Y\<cdot>X \<subseteq> Y \<Longrightarrow> Z\<cdot>X\<^bsup>n\<^esup> \<subseteq> Y"
  apply (induct n)
  apply (simp_all del: l_power.simps(2) add: l_power_def_var)
  by (metis l_prod_assoc l_prod_isol order_trans)

lemma l_star_inductr: "Z \<union> Y\<cdot>X \<subseteq> Y \<Longrightarrow> Z\<cdot>X\<^sup>* \<subseteq> Y"
proof -
  assume asm: "Z \<union> Y\<cdot>X \<subseteq> Y"
  have "\<Union>range (\<lambda>n. Z \<cdot> X\<^bsup>n\<^esup>) \<subseteq> Y"
    by (auto, metis asm in_mono l_power_inductr)
  moreover have "\<Union>range (\<lambda>n. Z \<cdot> X\<^bsup>n\<^esup>) = Z \<cdot> \<Union>range (l_power X)"
    by (auto simp add: l_prod_def complex_product_def)
  ultimately show "Z\<cdot>X\<^sup>* \<subseteq> Y"
    by (metis l_star_def)
qed

subsection {* Star for stutter/mumble closed languages *}

primrec sm_l_power :: "'a::monoid_add lan \<Rightarrow> nat \<Rightarrow> 'a lan" where
  "sm_l_power X 0 = \<one>"
| "sm_l_power X (Suc n) = X \<cdot>\<^sup>\<ddagger> X\<^bsup>n\<^esup>"

lemma sm_l_power_to_l_power: "sm_l_power X n = (X\<^bsup>n\<^esup>)\<^sup>\<ddagger>"
  by (induct n) (simp_all add: sm_one_def sm_l_prod_def)

lemma sm_l_star_to_l_star: "\<Union>range (sm_l_power X) = (X\<^sup>*)\<^sup>\<ddagger>"
  by (simp add: l_star_def sm_l_power_to_l_power sm_closure_def)

lemma sm_l_star_unfoldl: "\<one> \<union> X\<cdot>\<^sup>\<ddagger>(X\<^sup>*)\<^sup>\<ddagger> \<subseteq> (X\<^sup>*)\<^sup>\<ddagger>"
  by (metis (hide_lams, no_types) l_star_unfoldl le_sup_iff sm_closure_idem sm_closure_iso sm_l_prod_closure sm_l_prod_def sm_one_def)

lemma sm_l_star_unfoldr: "\<one> \<union> (X\<^sup>*)\<^sup>\<ddagger>\<cdot>\<^sup>\<ddagger>X \<subseteq> (X\<^sup>*)\<^sup>\<ddagger>"
  by (metis (hide_lams, no_types) l_star_unfoldr le_sup_iff sm_closure_idem sm_closure_iso sm_l_prod_closure sm_l_prod_def sm_one_def)

lemma sm_l_power_inductl: "Z\<^sup>\<ddagger> \<union> X\<cdot>\<^sup>\<ddagger>Y \<subseteq> Y\<^sup>\<ddagger> \<Longrightarrow> X\<^bsup>n\<^esup>\<cdot>\<^sup>\<ddagger>Z \<subseteq> Y\<^sup>\<ddagger>"
proof (induct n arbitrary: Z, simp_all add: sm_l_prod_def l_power_def_var del: l_power.simps(2))
  fix n Z
  assume ih: "\<And>Z. Z\<^sup>\<ddagger> \<subseteq> Y\<^sup>\<ddagger> \<Longrightarrow> (X\<^bsup>n\<^esup> \<cdot> Z)\<^sup>\<ddagger> \<subseteq> Y\<^sup>\<ddagger>"
  and asm: "Z\<^sup>\<ddagger> \<subseteq> Y\<^sup>\<ddagger> \<and> (X \<cdot> Y)\<^sup>\<ddagger> \<subseteq> Y\<^sup>\<ddagger>"
  hence "(X \<cdot> Z)\<^sup>\<ddagger> = (X\<^sup>\<ddagger> \<cdot> Z\<^sup>\<ddagger>)\<^sup>\<ddagger>"
    by (metis sm_l_prod_closure sm_l_prod_def)
  also have "... \<subseteq> (X\<^sup>\<ddagger> \<cdot> Y\<^sup>\<ddagger>)\<^sup>\<ddagger>"
    by (metis asm l_prod_isor sm_closure_iso)
  also have "... = (X \<cdot> Y)\<^sup>\<ddagger>"
    by (metis sm_l_prod_closure sm_l_prod_def)
  also have "... \<subseteq> Y\<^sup>\<ddagger>"
    by (metis asm)
  finally show "(X\<^bsup>n\<^esup> \<cdot> X \<cdot> Z)\<^sup>\<ddagger> \<subseteq> Y\<^sup>\<ddagger>"
    by (metis ih l_prod_assoc)
qed

lemma sm_l_star_inductl: "Z\<^sup>\<ddagger> \<union> X\<cdot>\<^sup>\<ddagger>Y \<subseteq> Y\<^sup>\<ddagger> \<Longrightarrow> X\<^sup>*\<cdot>\<^sup>\<ddagger>Z \<subseteq> Y\<^sup>\<ddagger>"
proof -
  assume asm: "Z\<^sup>\<ddagger> \<union> X\<cdot>\<^sup>\<ddagger>Y \<subseteq> Y\<^sup>\<ddagger>"
  have "\<Union>range (\<lambda>n. X\<^bsup>n\<^esup> \<cdot>\<^sup>\<ddagger> Z) \<subseteq> Y\<^sup>\<ddagger>"
    by (auto, metis asm in_mono sm_l_power_inductl)
  moreover
  {
    have "\<Union>range (\<lambda>n. X\<^bsup>n\<^esup> \<cdot>\<^sup>\<ddagger> Z) = (\<Union>range (\<lambda>n. X\<^bsup>n\<^esup> \<cdot> Z))\<^sup>\<ddagger>"
      by (auto simp only: sm_join_preserving[symmetric] sm_l_prod_def)
    also have "... = (\<Union>range (l_power X) \<cdot> Z)\<^sup>\<ddagger>"
      by (rule arg_cong, auto simp add: l_prod_def complex_product_def)
    finally have "\<Union>range (\<lambda>n. X\<^bsup>n\<^esup> \<cdot>\<^sup>\<ddagger> Z) = X\<^sup>*\<cdot>\<^sup>\<ddagger>Z"
      by (metis l_star_def sm_l_prod_def)
  }
  ultimately show ?thesis by auto
qed

lemma sm_l_power_inductr: "Z\<^sup>\<ddagger> \<union> Y\<cdot>\<^sup>\<ddagger>X \<subseteq> Y\<^sup>\<ddagger> \<Longrightarrow> Z\<cdot>\<^sup>\<ddagger>X\<^bsup>n\<^esup> \<subseteq> Y\<^sup>\<ddagger>"
proof (induct n arbitrary: Z, simp_all add: sm_l_prod_def)
  fix n Z
  assume ih: "\<And>Z. Z\<^sup>\<ddagger> \<subseteq> Y\<^sup>\<ddagger> \<Longrightarrow> (Z \<cdot> X\<^bsup>n\<^esup>)\<^sup>\<ddagger> \<subseteq> Y\<^sup>\<ddagger>"
  and asm: "Z\<^sup>\<ddagger> \<subseteq> Y\<^sup>\<ddagger> \<and> (Y \<cdot> X)\<^sup>\<ddagger> \<subseteq> Y\<^sup>\<ddagger>"
  hence "(Z \<cdot> X)\<^sup>\<ddagger> = (Z\<^sup>\<ddagger> \<cdot> X\<^sup>\<ddagger>)\<^sup>\<ddagger>"
    by (metis sm_l_prod_closure sm_l_prod_def)
  also have "... \<subseteq> (Y\<^sup>\<ddagger> \<cdot> X\<^sup>\<ddagger>)\<^sup>\<ddagger>"
    by (metis asm l_prod_isol sm_closure_iso)
  also have "... = (Y \<cdot> X)\<^sup>\<ddagger>"
    by (metis sm_l_prod_closure sm_l_prod_def)
  also have "... \<subseteq> Y\<^sup>\<ddagger>"
    by (metis asm)
  finally show "(Z \<cdot> (X \<cdot> X\<^bsup>n\<^esup>))\<^sup>\<ddagger> \<subseteq> Y\<^sup>\<ddagger>"
    by (metis ih l_prod_assoc)
qed

lemma sm_l_star_inductr: "Z\<^sup>\<ddagger> \<union> Y\<cdot>\<^sup>\<ddagger>X \<subseteq> Y\<^sup>\<ddagger> \<Longrightarrow> Z\<cdot>\<^sup>\<ddagger>X\<^sup>* \<subseteq> Y\<^sup>\<ddagger>"
proof -
  assume asm: "Z\<^sup>\<ddagger> \<union> Y\<cdot>\<^sup>\<ddagger>X \<subseteq> Y\<^sup>\<ddagger>"
  have "\<Union>range (\<lambda>n. Z \<cdot>\<^sup>\<ddagger> X\<^bsup>n\<^esup>) \<subseteq> Y\<^sup>\<ddagger>"
    by (auto, metis asm in_mono sm_l_power_inductr)
  moreover
  {
    have "\<Union>range (\<lambda>n. Z \<cdot>\<^sup>\<ddagger> X\<^bsup>n\<^esup>) = (\<Union>range (\<lambda>n. Z \<cdot> X\<^bsup>n\<^esup>))\<^sup>\<ddagger>"
      by (auto simp only: sm_join_preserving[symmetric] sm_l_prod_def)
    also have "... = (Z \<cdot> \<Union>range (l_power X))\<^sup>\<ddagger>"
      by (rule arg_cong, auto simp add: l_prod_def complex_product_def)
    finally have "\<Union>range (\<lambda>n. Z \<cdot>\<^sup>\<ddagger> X\<^bsup>n\<^esup>) = Z\<cdot>\<^sup>\<ddagger>X\<^sup>*"
      by (metis l_star_def sm_l_prod_def)
  }
  ultimately show ?thesis by auto
qed

section {* Shuffle Star *}

primrec spawn :: "'a lan \<Rightarrow> nat \<Rightarrow> 'a lan" where
  "spawn X 0 = {[]}"
| "spawn X (Suc n) = X \<parallel> spawn X n"

definition shuffle_star :: "'a lan \<Rightarrow> 'a lan" ("_\<^sup>\<parallel>" [101] 100) where
  "X\<^sup>\<parallel> \<equiv> \<Union>range (spawn X)"

lemma [intro]: "[] \<in> spawn X 0"
  by simp

lemma spawn1 [intro]: "xs \<in> X \<Longrightarrow> ys \<in> spawn X n \<Longrightarrow> map \<langle>id,id\<rangle> ` (xs \<sha> ys) \<subseteq> spawn X (Suc n)"
  by (induct n, simp_all, metis word_shuffle_subset)

lemma spawn2 [intro]: "xs \<in> X \<Longrightarrow> ys \<in> spawn X n \<Longrightarrow> zs \<in> xs \<sha> ys \<Longrightarrow> map \<langle>id,id\<rangle> zs \<in> spawn X (Suc n)"
  by (metis image_eqI spawn1 set_mp)

lemma shuffle_star_unfold: "{[]} \<union> X\<parallel>X\<^sup>\<parallel> \<subseteq> X\<^sup>\<parallel>"
  by (auto simp add: shuffle_star_def shuffle_def)

lemma spawn_induct: "Z \<union> X \<parallel> Y \<subseteq> Y \<Longrightarrow> spawn X n \<parallel> Z \<subseteq> Y"
  apply (induct n arbitrary: Z)
  apply auto
  by (metis (hide_lams, no_types) in_mono shuffle_assoc shuffle_comm shuffle_iso)

lemma shuffle_star_induct: "Z \<union> X \<parallel> Y \<subseteq> Y \<Longrightarrow> X\<^sup>\<parallel> \<parallel> Z \<subseteq> Y"
proof -
  assume asm: "Z \<union> X \<parallel> Y \<subseteq> Y"
  have "\<Union>range (\<lambda>n. spawn X n \<parallel> Z) \<subseteq> Y"
    by (auto, metis asm in_mono spawn_induct)
  moreover have "\<Union>range (\<lambda>n. spawn X n \<parallel> Z) = \<Union>range (spawn X) \<parallel> Z"
    by (auto simp only: shuffle_inf_distr)
  ultimately show "X\<^sup>\<parallel>\<parallel>Z \<subseteq> Y"
    by (metis shuffle_star_def)
qed

subsection {* Shuffle star for stutter/mumble closed languages *}

primrec sm_spawn :: "'a::monoid_add lan \<Rightarrow> nat \<Rightarrow> 'a lan" where
  "sm_spawn X 0 = \<one>"
| "sm_spawn X (Suc n) = X \<parallel>\<^sup>\<ddagger> sm_spawn X n"

lemma sm_spawn_closure: "sm_spawn X n = (spawn X n)\<^sup>\<ddagger>"
  apply (induct n)
  apply (simp_all add: sm_one_def sm_shuffle_def)
  by (metis shuffle_closure sm_closure_idem sm_shuffle_def)

lemma sm_shuffle_star: "\<Union>range (sm_spawn X) = (X\<^sup>\<parallel>)\<^sup>\<ddagger>"
  apply (simp only: shuffle_star_def sm_join_preserving[symmetric])
  by (auto simp add: sm_spawn_closure)

lemma [intro]: "sm_spawn X n \<subseteq> (X\<^sup>\<parallel>)\<^sup>\<ddagger>"
  by (auto simp add: sm_shuffle_star[symmetric])

lemma [simp]: "(\<Union>{X \<parallel> Y|Y. Y \<in> range (sm_spawn X)})\<^sup>\<ddagger> = \<Union>range (\<lambda>n. sm_spawn X (Suc n))"
  by (simp only: sm_join_preserving[symmetric], auto simp add: sm_shuffle_def)

lemma sm_shuffle_star_unfoldl: "\<one> \<union> X\<parallel>\<^sup>\<ddagger>(X\<^sup>\<parallel>)\<^sup>\<ddagger> \<subseteq> (X\<^sup>\<parallel>)\<^sup>\<ddagger>"
  apply (simp add: sm_shuffle_def)
  apply (rule conjI)
  apply (rule order_trans[where y = "sm_spawn X 0"])
  apply simp
  apply rule back
  apply (simp only: sm_shuffle_star[symmetric] shuffle_inf_distl)
  apply auto
  apply (rule_tac x = "Suc xa" in exI)
  by auto

lemma sm_spawn_induct: "Z\<^sup>\<ddagger> \<union> X \<parallel>\<^sup>\<ddagger> Y \<subseteq> Y\<^sup>\<ddagger> \<Longrightarrow> spawn X n \<parallel>\<^sup>\<ddagger> Z \<subseteq> Y\<^sup>\<ddagger>"
proof (induct n arbitrary: Z, simp_all add: sm_shuffle_def)
  fix n Z
  assume ih: "\<And>Z. Z\<^sup>\<ddagger> \<subseteq> Y\<^sup>\<ddagger> \<Longrightarrow> (spawn X n \<parallel> Z)\<^sup>\<ddagger> \<subseteq> Y\<^sup>\<ddagger>"
  and asm: "Z\<^sup>\<ddagger> \<subseteq> Y\<^sup>\<ddagger> \<and> (X \<parallel> Y)\<^sup>\<ddagger> \<subseteq> Y\<^sup>\<ddagger>"
  hence "(X \<parallel> Z)\<^sup>\<ddagger> = (X\<^sup>\<ddagger> \<parallel> Z\<^sup>\<ddagger>)\<^sup>\<ddagger>"
    by (metis shuffle_closure sm_shuffle_def)
  also have "... \<subseteq> (X\<^sup>\<ddagger> \<parallel> Y\<^sup>\<ddagger>)\<^sup>\<ddagger>"
    by (metis asm shuffle_comm shuffle_iso sm_closure_iso)
  also have "... = (X \<parallel> Y)\<^sup>\<ddagger>"
    by (metis shuffle_closure sm_shuffle_def)
  also have "... \<subseteq> Y\<^sup>\<ddagger>"
    by (metis asm)
  finally show "(X \<parallel> spawn X n \<parallel> Z)\<^sup>\<ddagger> \<subseteq> Y\<^sup>\<ddagger>"
    by (metis (hide_lams, no_types) ih shuffle_assoc shuffle_comm)
qed

lemma sm_shuffle_star_inductl: "Z\<^sup>\<ddagger> \<union> X \<parallel>\<^sup>\<ddagger> Y \<subseteq> Y\<^sup>\<ddagger> \<Longrightarrow> X\<^sup>\<parallel> \<parallel>\<^sup>\<ddagger> Z \<subseteq> Y\<^sup>\<ddagger>"
proof -
  assume asm: "Z\<^sup>\<ddagger> \<union> X \<parallel>\<^sup>\<ddagger> Y \<subseteq> Y\<^sup>\<ddagger>"
  have "\<Union>range (\<lambda>n. spawn X n \<parallel>\<^sup>\<ddagger> Z) \<subseteq> Y\<^sup>\<ddagger>"
    by (auto, metis asm in_mono sm_spawn_induct)
  moreover
  {
    have "\<Union>range (\<lambda>n. spawn X n \<parallel>\<^sup>\<ddagger> Z) = (\<Union>range (\<lambda>n. spawn X n \<parallel> Z))\<^sup>\<ddagger>"
      by (auto simp only: sm_join_preserving[symmetric] sm_shuffle_def)
    also have "... = (\<Union>range (spawn X) \<parallel> Z)\<^sup>\<ddagger>"
      by (simp only: shuffle_inf_distr, rule arg_cong, blast)
    finally have "\<Union>range (\<lambda>n. spawn X n \<parallel>\<^sup>\<ddagger> Z) = X\<^sup>\<parallel> \<parallel>\<^sup>\<ddagger> Z"
      by (metis shuffle_star_def sm_shuffle_def)
  }
  ultimately show ?thesis by auto
qed

lemma [simp]: "listsum (map (\<lambda>x. [x]) xs) = xs"
  by (induct xs) (auto simp add: zero_list_def plus_list_def)

lemma sm_set_free_self [intro]: "[xs] \<in> sm_set (map (\<lambda>x. [x]) xs)"
proof (induct xs, simp_all)
  show "[[]] \<in> sm_set []"
    by (metis sm_set.self zero_list_def)
next
  fix x and xs :: "'a list"
  assume ih: "[xs] \<in> sm_set (map (\<lambda>x. [x]) xs)"
  have "[x] # [xs] \<in> sm_set ([x] # map (\<lambda>x. [x]) xs)"
    by (rule sm_set_cons[OF ih])
  hence "[[x]] @ [xs] \<in> sm_set ([x] # map (\<lambda>x. [x]) xs)"
    by simp
  hence "[[x] @ xs] \<in> sm_set ([x] # map (\<lambda>x. [x]) xs)"
    apply (simp only: plus_list_def[symmetric])
    apply (rule mumble[of "[]" _ _ "[]", simplified])
    by (simp add: plus_list_def)
  thus "[x # xs] \<in> sm_set ([x] # map (\<lambda>x. [x]) xs)"
    by simp
qed

section {* Stutter/mumble closure in the free monoid *}

text {*
If the monoid we are using is the free monoid (i.e. lists), then @{term sm_set} has an equivalent, non inductive definition.
*}

lemma sm_set_non_ind: "sm_set (map (\<lambda>x. [x]) xs) = {zs. xs = concat zs \<and> zs \<noteq> []}"
proof
  show "sm_set (map (\<lambda>x. [x]) xs) \<subseteq> {zs. xs = concat zs \<and> zs \<noteq> []}"
  proof auto
    fix ys
    assume "ys \<in> sm_set (map (\<lambda>x. [x]) xs)"
    thus "xs = concat ys"
      by (induct ys) (auto simp add: zero_list_def plus_list_def)
  next
    fix x assume "[] \<in> sm_set (map (\<lambda>x. [x]) xs)"
    from this and sm_set_empty show False by auto
  qed
  moreover
  {
    fix x :: "'a list" and xs :: "'a list list"
    have "x # xs \<in> sm_set (map (\<lambda>x. [x]) (concat (x # xs)))"
    proof (induct xs arbitrary: x)
      fix x :: "'a list" show "[x] \<in> sm_set (map (\<lambda>x. [x]) (concat [x]))"
        by auto
    next
      fix x and x' and xs :: "'a list list"
      assume ih: "\<And>x. x # xs \<in> sm_set (map (\<lambda>x. [x]) (concat (x # xs)))"
      have "[0,x] @ x' # xs \<in> sm_set (map (\<lambda>x. [x]) x @ map (\<lambda>x. [x]) (concat (x' # xs)))"
        by (rule sm_set_append, metis sm_set.self sm_set_free_self sm_set_trans, metis ih)
      hence "[] @ [0] @ [x] @ x' # xs \<in> sm_set (map (\<lambda>x. [x]) x @ map (\<lambda>x. [x]) (concat (x' # xs)))"
        by simp
      hence "[] @ [0 + x] @ x' # xs \<in> sm_set (map (\<lambda>x. [x]) x @ map (\<lambda>x. [x]) (concat (x' # xs)))"
        by (rule mumble)
      hence "[] @ [x] @ x' # xs \<in> sm_set (map (\<lambda>x. [x]) x @ map (\<lambda>x. [x]) (concat (x' # xs)))"
        by simp
      thus "x # x' # xs \<in> sm_set (map (\<lambda>x. [x]) (concat (x # x' # xs)))"
        by simp
    qed
  }
  thus "{zs. xs = concat zs \<and> zs \<noteq> []} \<subseteq> sm_set (map (\<lambda>x. [x]) xs)"
    by (safe, metis neq_Nil_conv)
qed

primrec unfree :: "('a \<Rightarrow> 'b::monoid_add) \<Rightarrow> 'a list list \<Rightarrow> 'b list" where
  "unfree f [] = []"
| "unfree f (x#xs) = listsum (map f x) # unfree f xs"

lemma unfree_append: "unfree id (xs @ ys) = unfree id xs @ unfree id ys"
  by (induct xs) auto

lemma [simp]: "unfree id (map (\<lambda>x. [x]) xs) = xs"
  by (induct xs) simp_all

lemma unfree_exists: "\<exists>ys. xs = unfree id ys"
  apply (rule_tac x = "map (\<lambda>x. [x]) xs" in exI)
  apply (induct xs)
  by auto

lemma unfree_split1:
  "as @ bs = unfree id cs \<Longrightarrow> \<exists>csa csb. as = unfree id csa \<and> bs = unfree id csb \<and> csa @ csb = cs"
proof (induct cs arbitrary: as bs, simp_all)
  fix c :: "'a list" and cs as bs
  assume ih: "\<And>as bs. as @ bs = unfree id cs \<Longrightarrow> \<exists>csa. as = unfree id csa \<and> (\<exists>csb. bs = unfree id csb \<and> csa @ csb = cs)"
  and "as @ bs = listsum c # unfree id cs"
  note assumptions = this
  show "\<exists>csa. as = unfree id csa \<and> (\<exists>csb. bs = unfree id csb \<and> csa @ csb = c # cs)"
  proof (rule list.exhaust[of as], insert assumptions, rule_tac x = "[]" in exI, simp_all)
    fix a as
    assume "a = listsum c \<and> as @ bs = unfree id cs"
    hence a: "a = listsum c" and b: "as @ bs = unfree id cs"
      by auto
    thus "\<exists>csa. listsum c # as = unfree id csa \<and> (\<exists>csb. bs = unfree id csb \<and> csa @ csb = c # cs)"
      apply (insert ih[OF b])
      by (metis List.map.id append_Cons id_apply unfree.simps(2))
  qed
qed

lemma unfree_length: "xs = unfree id ys \<Longrightarrow> length xs = length ys"
  by (induct ys arbitrary: xs) auto

lemma unfree_take: "as @ bs = unfree id cs \<Longrightarrow> as = unfree id (take (length as) cs)"
proof (induct cs arbitrary: as, simp_all)
  fix c :: "'a list" and cs as
  assume ih: "\<And>as. as @ bs = unfree id cs \<Longrightarrow> as = unfree id (take (length as) cs)"
  and asm: "as @ bs = listsum c # unfree id cs"
  show "as = unfree id (take (length as) (c # cs))"
    by (rule list.exhaust[of as], simp_all, metis Cons_eq_appendI asm ih list.inject)
qed

lemma unfree_drop: "as @ bs = unfree id cs \<Longrightarrow> bs = unfree id (drop (length as) cs)"
proof (induct cs arbitrary: as bs, simp_all)
  fix c :: "'a list" and cs as bs
  assume ih: "\<And>as bs. as @ bs = unfree id cs \<Longrightarrow> bs = unfree id (drop (length as) cs)"
  and asm: "as @ bs = listsum c # unfree id cs"
  show "bs = unfree id (drop (length as) (c # cs))"
    apply (rule list.exhaust[of as])
    apply simp
    apply (metis append_Nil asm)
    apply simp
    by (metis append_Cons asm ih list.inject)
qed

lemma unfree_cons: "x # xs = unfree id ys \<Longrightarrow> xs = unfree id (drop 1 ys)"
  by (induct ys) auto

lemma unfree_hd: "x # xs = unfree id ys \<Longrightarrow> x = listsum (hd ys)"
  by (induct ys) auto

lemma drop_hd: "length xs > n \<Longrightarrow> drop n xs = hd (drop n xs) # drop (Suc n) xs"
  apply (induct xs arbitrary: n)
  apply auto
  by (metis drop_Suc_Cons drop_Suc_conv_tl hd_drop_conv_nth length_Suc_conv)

lemma unfree_split2:
  "as @ [b] @ [c] @ ds = unfree id zs \<Longrightarrow>
  \<exists>zsa zb zc zsd. as = unfree id zsa \<and> b = listsum zb \<and> c = listsum zc \<and> ds = unfree id zsd \<and> zsa @ [zb] @ [zc] @ zsd = zs"
proof (intro exI conjI)
  assume asm: "as @ [b] @ [c] @ ds = unfree id zs"

  let ?zsa = "take (length as) zs"
  from asm show "as = unfree id ?zsa"
    by (metis unfree_take)

  let ?zb = "hd (drop (length as) zs)"
  show "b = listsum ?zb"
    by (rule unfree_hd[OF unfree_drop[OF asm, simplified]])

  let ?zc = "hd (drop (Suc (length as)) zs)"
  show "c = listsum ?zc"
    by (rule unfree_hd[OF unfree_cons[OF unfree_drop[OF asm, simplified]], simplified])

  let ?zsd = "drop (Suc (Suc (length as))) zs"
  show "ds = unfree id ?zsd"
    by (rule unfree_cons[OF unfree_cons[OF unfree_drop[OF asm, simplified]], simplified])

  from asm have zs_len: "length zs = Suc (Suc (length as + length ds))"
    by (insert unfree_length[OF asm], simp)

  show "?zsa @ [?zb] @ [?zc] @ ?zsd = zs"
    apply (simp)
    apply (subst append_take_drop_id[of "length as" "zs", symmetric])
    back back back back
    apply (rule arg_cong) back
    apply (subst drop_hd[symmetric])
    apply (metis add_Suc_right add_Suc_shift less_add_Suc1 zs_len)
    apply (subst drop_hd[symmetric])
    apply (metis (full_types) Suc_lessD length_append lessI nat_neq_iff not_add_less1 zs_len)
    by auto
qed

lemma unfree_replicate [simp]: "unfree id (replicate n []) = replicate n 0"
  by (induct n) auto

text {*
It is always possible to perform the stutter/mumble closure in the free monoid, and then map back down into an arbitrary monoid.
*}

lemma free_sm_set: "sm_set xs = unfree id ` sm_set (map (\<lambda>x. [x]) xs)"
proof -
  have "sm_set [] = unfree id ` sm_set (map (\<lambda>x. [x]) [])"
    apply (auto simp add: sm_set_empty_def image_def)
    apply (simp_all add: zero_list_def)
    apply (rule_tac x = "replicate (Suc xa) []" in exI)
    by (simp_all add: zero_list_def)

  moreover
  {
    fix x and xs :: "'a list"
    have "sm_set (x # xs) = unfree id ` sm_set (map (\<lambda>x. [x]) (x # xs))"
    proof (auto simp add: image_def sm_set_non_ind simp del: map.simps)
      fix ys
      show "ys \<in> sm_set (x # xs) \<Longrightarrow> \<exists>zs. x # xs = concat zs \<and> zs \<noteq> [] \<and> ys = unfree id zs"
      proof (induct ys rule: sm_set.induct, intro exI conjI)
        show "x # xs = concat ([[]] @ map (\<lambda>x. [x]) (x # xs))"
        and "[[]] @ map (\<lambda>x. [x]) (x # xs) \<noteq> []"
        and "0 # x # xs = unfree id ([[]] @ map (\<lambda>x. [x]) (x # xs))"
          by (induct xs) auto
      next
        fix as bs
        assume "as @ bs \<in> sm_set (x # xs)"
        and "\<exists>zs. (x # xs) = concat zs \<and> zs \<noteq> [] \<and> as @ bs = unfree id zs"
        then obtain zs where "(x # xs) = concat zs" and "zs \<noteq> []" and "as @ bs = unfree id zs" by auto
        then moreover obtain zsa and zsb where "as = unfree id zsa" and "bs = unfree id zsb" and "zsa @ zsb = zs"
          by (metis unfree_split1)
        ultimately show "\<exists>zs. (x # xs) = concat zs \<and> zs \<noteq> [] \<and> as @ [0] @ bs = unfree id zs"
          apply (rule_tac x = "zsa @ [0] @ zsb" in exI)
          by (auto simp add: zero_list_def unfree_append)
      next
        fix as bs cs ds
        assume "as @ [bs] @ [cs] @ ds \<in> sm_set (x # xs)"
        and "\<exists>zs. (x # xs) = concat zs \<and> zs \<noteq> [] \<and> as @ [bs] @ [cs] @ ds = unfree id zs"
        then obtain zs where "(x # xs) = concat zs \<and> as @ [bs] @ [cs] @ ds = unfree id zs" by auto
        then moreover obtain zsa and zb and zc and zsd
        where "as = unfree id zsa" and "bs = listsum zb" and "cs = listsum zc" and "ds = unfree id zsd" and "zsa @ [zb] @ [zc] @ zsd = zs"
          by (metis unfree_split2)
        ultimately show "\<exists>zs. (x # xs) = concat zs \<and> zs \<noteq> [] \<and> as @ [bs + cs] @ ds = unfree id zs"
          apply (rule_tac x = "zsa @ [zb @ zc] @ zsd" in exI)
          by (auto simp add: plus_list_def unfree_append)
      qed
    next
      fix ys :: "'a list list"
      assume "x # xs = concat ys" and "ys \<noteq> []"
      then obtain z and zs where ys_def: "ys = (z # zs)"
        by (metis neq_Nil_conv)
      have "[listsum z] @ unfree id zs \<in> sm_set (z @ concat zs)"
        apply (induct zs arbitrary: z)
        apply simp
        apply (metis append_Nil append_Nil2 listsum_simps(1) mumble_many neq_Nil_conv sm_set.self sm_set_self_var)
        apply (rule sm_set_append)
        apply (metis append_Nil append_Nil2 listsum_simps(1) mumble_many neq_Nil_conv sm_set.self sm_set_self_var)
        by simp
      hence "unfree id (z # zs) \<in> sm_set (concat (z # zs))"
        by (simp)
      thus "unfree id ys \<in> sm_set (concat ys)"
        by (metis ys_def)
    qed
  }
  ultimately show ?thesis
    by (metis list.exhaust)
qed

hide_fact unfree_split1 unfree_split2

section {* Power invariants *}

definition symbols :: "'a lan \<Rightarrow> 'a set" where
  "symbols X = \<Union>{set xs|xs. xs \<in> X}"

inductive_set pow_inv :: "'a set \<Rightarrow> 'a lan" for I :: "'a set" where
  pinv_empty [intro!]: "[] \<in> pow_inv I"
| pinv_cons: "x \<in> I \<Longrightarrow> xs \<in> pow_inv I \<Longrightarrow> (x # xs) \<in> pow_inv I"

definition sm_pow_inv :: "'a::monoid_add set \<Rightarrow> 'a lan" where
  "sm_pow_inv I \<equiv> (pow_inv I)\<^sup>\<ddagger>"

lemma inv_shuffle: "pow_inv I \<parallel> pow_inv I = pow_inv I"
proof -
  {
    fix xs
    assume "xs \<in> pow_inv I"
    hence "xs \<in> pow_inv I \<parallel> pow_inv I"
      apply (induct xs rule: pow_inv.induct)
      apply (metis (full_types) ewp_def ewp_shuffle pow_inv.pinv_empty)
      by (metis (hide_lams, no_types) bot_least in_mono insert_subset pow_inv.pinv_cons pow_inv.pinv_empty shuffle_iso shuffle_one(2))
  }
  moreover
  {
    fix xs
    assume "xs \<in> pow_inv I \<parallel> pow_inv I"
    hence "xs \<in> pow_inv I"
    proof (auto simp add: shuffle_def tshuffle_words_def)
      fix xs assume "\<ll> xs \<in> pow_inv I" and "\<rr> xs \<in> pow_inv I"
      thus "map \<langle>id,id\<rangle> xs \<in> pow_inv I"
        apply (induct xs rule: sum_list_induct)
        apply simp_all
        apply (metis cons_non_empty list.inject pow_inv.simps)
        by (metis cons_non_empty list.inject pow_inv.simps)
    qed
  }
  ultimately show ?thesis by auto
qed

lemma inv_l_prod: "pow_inv I \<cdot> pow_inv I = pow_inv I"
proof -
  have "pow_inv I \<subseteq> pow_inv I \<cdot> pow_inv I"
    by (metis empty_subsetI insert_subset l_prod_isol l_prod_one(1) pow_inv.pinv_empty)
  moreover
  {
    fix xs
    assume "xs \<in> pow_inv I \<cdot> pow_inv I"
    hence "xs \<in> pow_inv I"
    proof (auto simp add: l_prod_def complex_product_def)
      fix xs ys
      assume "xs \<in> pow_inv I" and "ys \<in> pow_inv I"
      thus "xs @ ys \<in> pow_inv I"
        by (induct xs) (auto intro: pinv_cons)
    qed
  }
  ultimately show ?thesis
    by (metis subsetI subset_antisym)
qed

lemma inv_alg1: shows "X \<subseteq> pow_inv I \<cdot> X" and "X \<subseteq> X \<cdot> pow_inv I"
  by (auto simp add: l_prod_def complex_product_def)

lemma inv_alg2: shows "X \<subseteq> pow_inv I \<parallel> X" and "X \<subseteq> X \<parallel> pow_inv I"
  by (rule order_trans[OF inv_alg1(1) l_prod_leq_shuffle]) (rule order_trans[OF inv_alg1(2) l_prod_leq_shuffle])

lemma inv_distl: "pow_inv I \<cdot> (X \<parallel> Y) \<subseteq> (pow_inv I \<cdot> X) \<parallel> (pow_inv I \<cdot> Y)"
  by (metis exchange inv_shuffle)

lemma inv_distr: "(X \<parallel> Y) \<cdot> pow_inv I \<subseteq> (X \<cdot> pow_inv I) \<parallel> (Y \<cdot> pow_inv I)"
  by (metis exchange inv_shuffle shuffle_comm)

lemma inv_l_prod_leq_shuffle: "pow_inv I \<cdot> X \<cdot> pow_inv I \<subseteq> pow_inv I \<parallel> X"
  by (metis (hide_lams, no_types) inv_shuffle l_prod_assoc l_prod_isor l_prod_leq_shuffle order_trans shuffle_assoc shuffle_comm)

lemma inv_power: "pow_inv I = (pow_inv I)\<^bsup>Suc n\<^esup>"
  by (induct n) (simp_all add: inv_l_prod)

lemma inv_spawn: "pow_inv I = spawn (pow_inv I) (Suc n)"
  by (induct n) (simp_all add: inv_shuffle)

lemma inv_star: "pow_inv I = (pow_inv I)\<^sup>*"
  apply (auto simp add: l_star_def)
  apply (rule_tac x = 1 in exI)
  apply simp
  by (metis inv_alg1(2) inv_power l_power_def_var set_mp)

lemma inv_shuffle_star: "pow_inv I = (pow_inv I)\<^sup>\<parallel>"
  apply (auto simp add: shuffle_star_def)
  apply (rule_tac x = 1 in exI)
  apply simp
  by (metis inv_alg2(1) inv_spawn set_mp spawn.simps(2))

lemma symbol_cons: "x # xs \<in> X \<Longrightarrow> x \<in> symbols X"
  by (auto simp add: symbols_def)

lemma pow_inv_iso: assumes "X \<subseteq> Y" shows "pow_inv X \<subseteq> pow_inv Y"
proof
  fix xs assume "xs \<in> pow_inv X" thus "xs \<in> pow_inv Y"
    apply (induct xs rule: pow_inv.induct)
    apply auto
    by (metis assms pow_inv.pinv_cons set_mp)
qed

lemma lan_tl: "x # xs \<in> X \<Longrightarrow> xs \<in> tl ` X"
  apply (auto simp add: image_def)
  apply (rule_tac x = "x # xs" in bexI)
  by auto

lemma symbols_tl: "symbols (tl ` X) \<subseteq> symbols X"
  apply (auto simp add: symbols_def)
  by (metis Cons_eq_appendI append_assoc in_set_conv_decomp_first rotate1_hd_tl set_rotate1 tl.simps(1))

lemma inv_sym_extensive: "X \<subseteq> pow_inv (symbols X)"
proof
  fix xs
  assume "xs \<in> X" thus "xs \<in> pow_inv (symbols X)"
  proof (induct xs arbitrary: X, simp add: pinv_empty)
    fix x :: 'a and xs X
    assume ih: "\<And>X. xs \<in> X \<Longrightarrow> xs \<in> pow_inv (symbols X)"
    and xxs: "x # xs \<in> X"
    hence "xs \<in> tl ` X"
      by (metis lan_tl)
    hence "xs \<in> pow_inv (symbols (tl ` X))"
      by (metis ih)
    hence "xs \<in> pow_inv (symbols X)"
      by (metis pow_inv_iso set_mp symbols_tl)
    thus "x # xs \<in> pow_inv (symbols X)"
      by (metis pow_inv.pinv_cons symbol_cons xxs)
  qed
qed

lemma pow_inv_tshuffle: "\<lbrakk>xs \<in> X; ys \<in> pow_inv (symbols X)\<rbrakk> \<Longrightarrow> map \<langle>id,id\<rangle> ` (xs \<sha> ys) \<subseteq> pow_inv (symbols X)"
proof (induct xs arbitrary: ys, simp)
  fix x xs ys
  assume ihx: "\<And>ys. xs \<in> X \<Longrightarrow> ys \<in> pow_inv (symbols X) \<Longrightarrow> map \<langle>id,id\<rangle> ` (xs \<sha> ys) \<subseteq> pow_inv (symbols X)"
  and xs_def: "x # xs \<in> X"
  and ys_def: "ys \<in> pow_inv (symbols X)"
  from ys_def show "map \<langle>id,id\<rangle> ` ((x # xs) \<sha> ys) \<subseteq> pow_inv (symbols X)"
  proof (induct ys)
    have "x # xs \<in> pow_inv (symbols X)"
      by (metis in_mono inv_sym_extensive xs_def)
    thus "map \<langle>id,id\<rangle> ` ((x # xs) \<sha> []) \<subseteq> pow_inv (symbols X)"
      by (metis inv_shuffle pow_inv.pinv_empty word_shuffle_subset)
  next
    fix y ys assume y_def: "y \<in> symbols X" and ys_def: "ys \<in> pow_inv (symbols X)"
    and ihy: "map \<langle>id,id\<rangle> ` ((x # xs) \<sha> ys) \<subseteq> pow_inv (symbols X)"
    show "map \<langle>id,id\<rangle> ` ((x # xs) \<sha> (y # ys)) \<subseteq> pow_inv (symbols X)"
      apply (simp add: tshuffle_ind)
      by (metis (hide_lams, no_types) y_def ys_def inv_shuffle inv_sym_extensive pow_inv.pinv_cons set_rev_mp tshuffle_ind word_shuffle_subset xs_def)
  qed
qed

lemma inv_shuffle_star_leq: "X\<^sup>\<parallel> \<subseteq> pow_inv (symbols X)"
proof
  fix xs
  assume "xs \<in> X\<^sup>\<parallel>"
  thus "xs \<in> pow_inv (symbols X)"
  proof (auto simp add: shuffle_star_def)
    fix n assume "xs \<in> spawn X n"
    thus "xs \<in> pow_inv (symbols X)"
      apply (induct n arbitrary: xs, auto simp add: pinv_empty shuffle_def)
      by (metis imageI pow_inv_tshuffle subsetD)
  qed
qed

(*
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

definition \<iota> :: "('a \<Rightarrow> 'a set) lan \<Rightarrow> 'a rel" where
  "\<iota> X = \<Union>{to_rel x|x. x \<in> symbols X}"

definition \<rho> :: "'a rel \<Rightarrow> ('a \<Rightarrow> 'a set) lan" where
  "\<rho> R = pow_inv {to_fun S|S. S \<subseteq> R}"

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

lemma [simp]: "\<Union>{to_rel xa|xa. \<exists>S. xa = to_fun S \<and> S \<subseteq> x} = \<Union>{S|S. S \<subseteq> x}"
  apply (rule arg_cong) back
  apply auto
  apply (rule_tac x = "to_fun xa" in exI)
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
  apply (rule_tac x = "to_rel xa" in exI)
  by auto

lemma galois_connection: "\<iota> x \<subseteq> y \<longleftrightarrow> x \<subseteq> \<rho> y"
  apply default
  apply (metis \<rho>_\<iota>_eq \<rho>_iso subset_trans)
  by (metis \<iota>_\<rho>_eq \<iota>_iso)

lemma "{[]} \<union> \<rho> x \<parallel> \<rho> x \<subseteq> \<rho> x"
  apply (simp add: \<rho>_def)
  apply (rule conjI)
  apply (metis pow_inv.pinv_empty)
  by (metis \<rho>_def inv_shuffle order_refl)

abbreviation (input)
  pred_all :: "('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" (binder "ALLS" 10) where
  "ALLS x. P x \<equiv> \<lambda>x. \<forall>y. P y x"

abbreviation (input)
  pred_ex :: "('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" (binder "EXS" 10) where
  "EXS x. P x \<equiv> \<lambda>x. \<exists>y. P y x" 

abbreviation (input)
  pred_imp :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" (infix "imp" 25) where
  " P imp Q \<equiv> \<lambda>x. P x \<longrightarrow> Q x"

abbreviation (input)
  pred_equals :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> bool" (infix "===" 55) where
  "f === g \<equiv> \<lambda>x. f x = g x"

abbreviation Pred :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set" where
  "Pred P \<equiv> {x. P x}"

abbreviation cf :: "'a set \<Rightarrow> 'a \<Rightarrow> bool" ("\<chi>") where
  "\<chi> X \<equiv> \<lambda>x. x \<in> X" 

lemma Pred_imp: "Pred (x imp y) = UNIV \<longleftrightarrow> Pred x \<subseteq> Pred y"
  by blast

lemma "Pred (\<chi> (\<iota> x) imp y) = UNIV \<longleftrightarrow> x \<subseteq> \<rho> (Pred y)"
  by (simp add: Pred_imp galois_connection)

*)

end

