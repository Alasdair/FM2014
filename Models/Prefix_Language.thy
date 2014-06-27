theory Prefix_Language
  imports Language
begin

datatype 'a plist = Trace "'a llist" | Pre "'a llist"

fun pappend :: "'a plist \<Rightarrow> 'a plist \<Rightarrow> 'a plist" where
  "pappend (Pre xs) ys = Pre xs"
| "pappend (Trace xs) (Pre ys) = Pre (xs \<frown> ys)"
| "pappend (Trace xs) (Trace ys) = Trace (xs \<frown> ys)"

lemma pappend_assoc: "pappend (pappend xs ys) zs = pappend xs (pappend ys zs)"
  apply (cases xs)
  apply simp_all
  apply (cases ys)
  apply simp_all
  apply (cases zs)
  apply simp_all
  by (metis lappend_assoc)+

type_synonym 'a plan = "'a plist set"

primrec pclose :: "'a plist \<Rightarrow> 'a plan" where
  "pclose (Trace xs') = insert (Trace xs') {Pre xs |xs. lprefix xs xs'}"
| "pclose (Pre xs') = {Pre xs |xs. lprefix xs xs'}"

definition pclosure :: "'a plan \<Rightarrow> 'a plan" ("_\<^sup>\<dagger>" [1000] 1000) where
  "pclosure X = \<Union>(pclose ` X)"

lemma pclose_trans: "xs \<in> pclose ys \<Longrightarrow> ys \<in> pclose zs \<Longrightarrow> xs \<in> pclose zs"
  apply (cases ys)
  apply simp_all
  apply (cases zs)
  apply simp_all
  apply (cases zs)
  apply (simp_all)
  by (metis lprefix_trans)+

lemma pclose_refl: "xs \<in> pclose xs"
  by (cases xs) simp_all

lemma pc_idem: "X\<^sup>\<dagger>\<^sup>\<dagger> = X\<^sup>\<dagger>"
  apply (auto simp add: pclosure_def)
  apply (rename_tac xs zs ys)
  apply (rule_tac x = zs in bexI)
  apply (metis pclose_trans)
  apply simp
  apply (rename_tac xs ys)
  apply (rule_tac x = ys in bexI)
  apply simp_all
  apply (rule_tac x = xs in bexI)
  apply simp_all
  by (rule pclose_refl)

lemma "X \<le> X\<^sup>\<dagger>"
  by (auto simp add: pclosure_def) (metis pclose_refl)

lemma "X \<le> Y \<Longrightarrow> X\<^sup>\<dagger> \<le> Y\<^sup>\<dagger>"
  by (auto simp add: pclosure_def)

primrec pterm :: "'a plist \<Rightarrow> bool" where
  "pterm (Pre xs) = False"
| "pterm (Trace xs) = lfinite xs"

definition pprod :: "'a plan \<Rightarrow> 'a plan \<Rightarrow> 'a plan" (infixl "\<bowtie>" 80) where
  "pprod X Y = {pappend xs ys |xs ys. xs \<in> X \<and> pterm xs \<and> ys \<in> Y} \<union> {xs. xs \<in> X \<and> \<not> pterm xs}"

lemma pterm_pappend: "pterm (pappend xs ys) \<longleftrightarrow> (pterm xs \<and> pterm ys)"
  apply (cases xs)
  apply simp_all
  apply (cases ys)
  by simp_all

lemma pprod_assoc: "(X \<bowtie> Y) \<bowtie> Z = X \<bowtie> (Y \<bowtie> Z)"
  apply (simp add: pprod_def)
  apply safe
  by (metis pappend_assoc pterm_pappend)+

lemma pprod_inf_dist: "(\<Union> \<XX>) \<bowtie> Y = \<Union>{X \<bowtie> Y |X. X \<in> \<XX>}"
  by (auto simp add: pprod_def)

(*
lemma "(Trace ` X)\<^sup>\<dagger> \<bowtie> (Trace ` Y)\<^sup>\<dagger> = (Trace ` (X \<cdot> Y))\<^sup>\<dagger>"
proof -
  have "(Trace ` X)\<^sup>\<dagger> \<bowtie> (Trace ` Y)\<^sup>\<dagger> = \<Union>(pclose ` Trace ` X) \<bowtie> \<Union>(pclose ` Trace ` Y)"
    by (simp add: pclosure_def)
  also have "... = \<Union>{X' \<bowtie> \<Union>(pclose ` Trace ` Y) |X'. X' \<in> pclose ` Trace ` X}"
    by (subst pprod_inf_dist) simp
  also have "... = \<Union>(pclose ` Trace ` (X \<cdot> Y))"
    apply (rule arg_cong) back
    apply (simp add: l_prod_def pprod_def image_def)
    apply safe
    sledgehammer
    apply (rule_tac x
*)

find_consts "'a llist \<Rightarrow> 'a stream"

lemma "{Pre (list_of xs) |xs. lfinite xs \<and> lprefix xs xs'}"

fun pshuffle_words :: "'a plist \<Rightarrow> 'b plist \<Rightarrow> ('a + 'b) plan" (infix "\<sha>" 75) where
  "(Pre xs) \<sha> (Pre ys) = Pre ` list_of ` (llist_of xs \<sha> llist_of ys)"
| "(Term xs) \<sha> (Term ys) = Term ` list_of ` (llist_of xs \<sha> llist_of ys)"
| "(Inf xs) \<sha> (Inf ys) = Inf ` stream_of_llist ` (llist_of_stream xs \<sha> llist_of_stream ys)"
| "(Term xs) \<sha> (Inf ys) = Inf ` stream_of_llist ` (llist_of xs \<sha> llist_of_stream ys)"
| "(Inf xs) \<sha> (Term ys) = Inf ` stream_of_llist ` (llist_of_stream xs \<sha> llist_of ys)"
| "(Pre xs) \<sha> (Term ys) = Pre ` list_of ` (llist_of xs \<sha> llist_of ys)"
| "(Term xs) \<sha> (Pre ys) = Pre ` list_of ` (llist_of xs \<sha> llist_of ys)"
| "pshuffle_words xs ys = {}"



end
