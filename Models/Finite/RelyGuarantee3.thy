theory RelyGuarantee3
  imports Language
begin

datatype 'a act = Act "'a set" "'a rel"

fun eval_word :: "'a act list \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "eval_word [] p = p"
| "eval_word (Act q x # xs) p = (if p \<subseteq> q then eval_word xs (x `` p) else {})"

lemma eval_word_empty [simp]: "eval_word xs {} = {}"
proof (induct xs)
  case Nil show ?case by simp
next
  case (Cons x xs) thus ?case by (cases x) simp
qed

lemma eval_append_word: "eval_word (xs @ ys) h = eval_word ys (eval_word xs h)"
proof (induct xs arbitrary: h)
  case Nil show ?case by simp
next
  case (Cons x xs) thus ?case
    by (cases x) simp
qed

lemma Image_continuous: "x `` (\<Union>X) = \<Union>Image x ` X"
  by auto

lemma eval_word_continuous: "eval_word w (\<Union>X) \<subseteq> \<Union>(eval_word w ` X)"
proof (induct w arbitrary: X)
  case Nil show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (induct x)
    fix p x
    {
      assume "\<Union>X \<subseteq> p"
      hence "eval_word (Act p x # xs) (\<Union>X) \<subseteq> \<Union> (eval_word (Act p x # xs) ` X)"
        apply (simp add: image_def)
        apply (subst Image_continuous)
        apply (rule order_trans[OF Cons.hyps])
        by auto
    }
    moreover
    {
      assume "\<not> (\<Union>X \<subseteq> p)"
      hence "eval_word (Act p x # xs) (\<Union>X) \<subseteq> Sup (eval_word (Act p x # xs) ` X)"
        by simp
    }
    ultimately show "eval_word (Act p x # xs) (\<Union>X) \<subseteq> Sup (eval_word (Act p x # xs) ` X)"
      by blast
  qed
qed

definition module :: "'a act lan \<Rightarrow> 'a set \<Rightarrow> 'a set" (infix "\<Colon>" 60) where
  "x \<Colon> h = Sup {eval_word w h|w. w \<in> x}"

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

lemma mod_mult: "y \<Colon> (x \<Colon> h) \<subseteq> x\<cdot>y \<Colon> h"
proof -
  have "y \<Colon> (x \<Colon> h) = \<Union>{eval_word yw (x \<Colon> h)|yw. yw \<in> y}"
    by (simp add: module_def)
  also have "... = \<Union>{eval_word yw (\<Union>{eval_word xw h|xw. xw \<in> x})|yw. yw \<in> y}"
    by (simp add: module_def)
  also have "... \<subseteq> \<Union>{\<Union>{eval_word yw (eval_word xw h)|xw. xw \<in> x}|yw. yw \<in> y}"
    apply (rule Sup_comp_mono)
    apply (rule order_trans[OF eval_word_continuous])
    by (auto simp add: image_def)
  also have "... = \<Union>{eval_word yw (eval_word xw h)|xw yw. xw \<in> x \<and> yw \<in> y}"
    by blast
  also have "... = \<Union>{eval_word (xw @ yw) h|xw yw. xw \<in> x \<and> yw \<in> y}"
    by (simp add: eval_append_word)
  also have "... = \<Union>{eval_word w h|w. w \<in> x\<cdot>y}"
    by (auto simp add: l_prod_def complex_product_def)
  also have "... = x\<cdot>y \<Colon> h"
    by (simp add: module_def)
  finally show ?thesis .
qed

end
