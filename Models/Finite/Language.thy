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

definition ewp :: "'a lan \<Rightarrow> bool" where
  "ewp X \<equiv> [] \<in> X"

lemma ewp_union [simp]: "ewp (X \<union> Y) \<longleftrightarrow> ewp X \<or> ewp Y"
  by (auto simp add: ewp_def)

lemma ewp_l_prod [simp]: "ewp (X \<cdot> Y) \<longleftrightarrow> ewp X \<and> ewp Y"
  by (auto simp add: ewp_def l_prod_def complex_product_def)

lemma ewp_shuffle [simp]: "ewp (X \<parallel> Y) \<longleftrightarrow> ewp X \<and> ewp Y"
  apply default
  apply (simp add: ewp_def shuffle_def tshuffle_words_def image_def)
  apply auto
  apply (simp add: ewp_def)
  by (metis (hide_lams, full_types) empty_subsetI insert_subset set_mp shuffle_iso shuffle_one(2))

section {* Shuffle Star *}

primrec spawn :: "'a lan \<Rightarrow> nat \<Rightarrow> 'a lan" where
  "spawn X 0 = {[]}"
| "spawn X (Suc n) = X \<parallel> spawn X n"

definition shuffle_star :: "'a lan \<Rightarrow> 'a lan" ("_\<^sup>\<parallel>" [101] 100) where
  "X\<^sup>\<parallel> \<equiv> \<Union>range (spawn X)"

lemma [intro]: "[] \<in> spawn X 0"
  by simp

lemma word_shuffle_subset: "\<lbrakk>xs \<in> X; ys \<in> Y\<rbrakk> \<Longrightarrow> map \<langle>id,id\<rangle> ` (xs \<sha> ys) \<subseteq> (X \<parallel> Y)"
  by (auto simp add: shuffle_def)

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

section {* Power invariants *}

definition symbols :: "'a lan \<Rightarrow> 'a set" where
  "symbols X = \<Union>{set xs|xs. xs \<in> X}"

inductive_set pow_inv :: "'a set \<Rightarrow> 'a lan" for I :: "'a set" where
  pinv_empty [intro!]: "[] \<in> pow_inv I"
| pinv_cons: "x \<in> I \<Longrightarrow> xs \<in> pow_inv I \<Longrightarrow> (x # xs) \<in> pow_inv I"

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

end

