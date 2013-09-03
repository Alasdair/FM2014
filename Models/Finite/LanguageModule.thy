theory LanguageModule
  imports Language
begin

definition fold_rel :: "'a rel list \<Rightarrow> 'a rel" where
  "fold_rel xs = foldr op O xs Id" 

definition eval_word :: "'a rel list \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "eval_word xs H = fold_rel xs `` H"

lemma eval_empty_word [simp]: "eval_word [] h = h"
  by (auto simp add: eval_word_def fold_rel_def)

lemma eval_cons_word [simp]: "eval_word (x # xs) h = eval_word xs (x `` h)"
  by (auto simp add: eval_word_def fold_rel_def)

lemma eval_append_word: "eval_word (xs @ ys) h = eval_word ys (eval_word xs h)"
  by (induct xs arbitrary: h) simp_all

definition module :: "'a rel lan \<Rightarrow> 'a set \<Rightarrow> 'a set" (infix "\<Colon>" 60) where
  "x \<Colon> h \<equiv> \<Union>{eval_word w h|w. w \<in> x}"

lemma eval_word_continuous: "eval_word w (\<Union>X) = \<Union>eval_word w ` X"
  by (induct w arbitrary: X) (auto simp add: image_def eval_word_def)

lemma mod_mult: "x\<cdot>y \<Colon> h = y \<Colon> (x \<Colon> h)"
proof -
  have "x\<cdot>y \<Colon> h = \<Union>{eval_word w h|w. w \<in> x\<cdot>y}"
    by (simp add: module_def)
  also have "... = \<Union>{eval_word (xw @ yw) h|xw yw. xw \<in> x \<and> yw \<in> y}"
    by (auto simp add: l_prod_def complex_product_def)
  also have "... = \<Union>{eval_word yw (eval_word xw h)|xw yw. xw \<in> x \<and> yw \<in> y}"
    by (simp add: eval_append_word)
  also have "... = \<Union>{\<Union>{eval_word yw (eval_word xw h)|xw. xw \<in> x}|yw. yw \<in> y}"
    by blast
  also have "... = \<Union>{eval_word yw (\<Union>{eval_word xw h|xw. xw \<in> x})|yw. yw \<in> y}"
    by (subst eval_word_continuous) (auto simp add: image_def)
  also have "... = \<Union>{eval_word yw (x \<Colon> h)|yw. yw \<in> y}"
    by (simp add: module_def)
  also have "... = y \<Colon> (x \<Colon> h)"
    by (simp add: module_def)
  finally show ?thesis .
qed

lemma mod_one [simp]: "{[]} \<Colon> h = h"
  by (simp add: module_def)

lemma mod_zero [simp]: "{} \<Colon> h = {}"
  by (simp add: module_def)

lemma mod_empty [simp]: "x \<Colon> {} = {}"
  by (simp add: module_def eval_word_def)

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

definition mod_test :: "'a set \<Rightarrow> 'a rel lan" ("_?" [101] 100) where
  "p? \<equiv> {[Id_on p]}"

lemma mod_test: "p? \<Colon> q = p \<inter> q"
  by (auto simp add: module_def mod_test_def)

lemma test_true: "q \<subseteq> p \<Longrightarrow> p? \<Colon> q = q"
  by (metis Int_absorb1 mod_test)

lemma test_false: "q \<subseteq> -p \<Longrightarrow> p? \<Colon> q = {}"
  by (metis Int_commute disjoint_eq_subset_Compl mod_test)

end
