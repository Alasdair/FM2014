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

lemma lprefixD: "lprefix xs' xs \<Longrightarrow> (\<exists>xs''. xs = xs' \<frown> xs'')"
  by (metis lprefix_def)

lemma set_bex_iso: "B \<subseteq> A \<Longrightarrow> \<exists>xs\<in>B. P xs \<Longrightarrow> \<exists>xs\<in>A. P xs"
  by (metis set_rev_mp)

lemma tshuffle_exchange: "lfinite xs \<Longrightarrow> lfinite ys \<Longrightarrow> (xs \<sha> ys) \<cdot> (xs' \<sha> ys') \<subseteq> (xs \<frown> xs') \<sha> (ys \<frown> ys')"
  apply (auto simp add: tshuffle_words_def l_prod_def)
  apply (metis lfinite_lr)
  apply (metis lfinite_lr)
  apply (metis lefts_append)
  by (metis rights_append)

definition strict_lprefix :: "'a llist \<Rightarrow> 'a llist \<Rightarrow> bool" (infixl "\<prec>" 57) where
  "xs \<prec> ys \<equiv> lprefix xs ys \<and> xs \<noteq> ys"

lemma "xs \<prec> ys \<Longrightarrow> lfinite xs"
  by (metis not_lfinite_lprefix_conv_eq strict_lprefix_def)

lemma strict_lprefix: "xs \<prec> ys \<longleftrightarrow> (\<exists>xs'. ys = xs \<frown> xs' \<and> xs' \<noteq> LNil \<and> lfinite xs)"
  by (metis lprefixD lstrict_prefix_def lstrict_prefix_lappend_conv strict_lprefix_def)

axiomatization
  alternates :: "'a llist \<Rightarrow> 'b llist \<Rightarrow> ('a + 'b) llist"
where
  alternate: "alternates xs ys \<in> xs \<sha> ys"

lemma shuffle_never_empty: "xs \<sha> ys \<noteq> {}"
  apply (auto simp add: tshuffle_words_def)
  apply (rule_tac x = "alternates xs ys" in exI)
  using alternate by (auto simp add: tshuffle_words_def)

lemma
  assumes "zs' \<in> xs' \<sha> ys'"
  and "xs' \<prec> xs" and "ys' \<prec> ys"
  shows "\<exists>zs\<in>xs \<sha> ys. zs' \<prec> zs"
proof -
  obtain xs'' and ys''
  where "xs = xs' \<frown> xs''" and "xs'' \<noteq> LNil" and "lfinite xs'"
  and "ys = ys' \<frown> ys''" and "ys'' \<noteq> LNil" and "lfinite ys'"
    by (metis assms(2) assms(3) lappend_LNil2 lprefixD not_lfinite_lprefix_conv_eq strict_lprefix_def)

  have "xs'' \<sha> ys'' \<noteq> {}"
    by (metis shuffle_never_empty)
  then obtain zs'' where "zs'' \<in> xs'' \<sha> ys''"
    by (metis alternate)

  have "\<exists>zs\<in>(xs' \<sha> ys') \<cdot> (xs'' \<sha> ys''). zs' \<prec> zs"
    apply (subst fin_l_prod)
    apply (metis FIN_def `lfinite xs'` `lfinite ys'` lfinite_shuffle mem_Collect_eq subsetI)
    apply (simp add: strict_lprefix)
    apply (rule_tac x = "zs' \<frown> zs''" in exI)
    apply (intro conjI)
    apply (rule_tac x = "zs'" in exI)
    apply (rule_tac x = "zs''" in exI)
    apply simp_all
    apply (metis `zs'' \<in> xs'' \<sha> ys''` assms(1))
    apply (rule_tac x = "zs''" in exI)
    apply simp
    by (metis (lifting, full_types) `xs'' \<noteq> LNil` `zs'' \<in> xs'' \<sha> ys''` `lfinite xs'` `lfinite ys'` assms(1) lefts_LNil lfinite_shuffle mem_Collect_eq tshuffle_words_def)
  hence "\<exists>zs\<in>(xs' \<frown> xs'') \<sha> (ys' \<frown> ys''). zs' \<prec> zs"
    by (metis `lfinite xs'` `lfinite ys'` in_mono tshuffle_exchange)
  thus "\<exists>zs\<in>xs \<sha> ys. zs' \<prec> zs"
    by (metis `xs = xs' \<frown> xs''` `ys = ys' \<frown> ys''`)
qed

lemma strict_lprefix_irrefl: "\<not> (xs \<prec> xs)"
  by (auto simp add: strict_lprefix) (metis lappend_LNil2 llist.distinct(1) lstrict_prefix_lappend_conv)

lemma strict_lprefix_trans: "xs \<prec> ys \<Longrightarrow> ys \<prec> zs \<Longrightarrow> xs \<prec> zs"
  apply (auto simp add: strict_lprefix_def)
  apply (metis lprefix_trans)
  by (metis lprefix_antisym)

lemma strict_lprefix_antisym: "xs \<prec> ys \<Longrightarrow> ys \<prec> xs \<Longrightarrow> False"
  by (metis lprefix_antisym strict_lprefix_def)

primrec pclose :: "'a plist \<Rightarrow> 'a plan" where
  "pclose (Trace xs') = insert (Trace xs') {Pre xs |xs. xs \<prec> xs'}"
| "pclose (Pre xs') = insert (Pre xs') {Pre xs |xs. xs \<prec> xs'}"

definition pclosure :: "'a plan \<Rightarrow> 'a plan" ("_\<^sup>\<dagger>" [1000] 1000) where
  "pclosure X = \<Union>(pclose ` X)"

lemma "Pre xs \<in> (Trace ` X)\<^sup>\<dagger> \<Longrightarrow> lfinite xs"
  by (auto simp add: pclosure_def) (metis strict_lprefix)

lemma pclose_trans: "xs \<in> pclose ys \<Longrightarrow> ys \<in> pclose zs \<Longrightarrow> xs \<in> pclose zs"
  apply (cases ys)
  apply simp_all
  apply (cases zs)
  apply simp_all
  apply (cases zs)
  apply (simp_all)
  by (metis strict_lprefix_trans)+

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

fun pshuffle_words :: "'a plist \<Rightarrow> 'b plist \<Rightarrow> ('a + 'b) plan" where
  "pshuffle_words (Pre xs) (Pre ys) = Pre ` (xs \<sha> ys)"
| "pshuffle_words (Pre xs) (Trace ys) = (if lfinite ys then Pre ` (xs \<sha> ys) else {})"
| "pshuffle_words (Trace xs) (Pre ys) = (if lfinite xs then Pre ` (xs \<sha> ys) else {})"
| "pshuffle_words (Trace xs) (Trace ys) = Trace ` (xs \<sha> ys)"

lemma lprefixD: "lprefix xs' xs \<Longrightarrow> (\<exists>xs''. xs = xs' \<frown> xs'')"
  by (metis lprefix_def)

lemma set_bex_iso: "B \<subseteq> A \<Longrightarrow> \<exists>xs\<in>B. P xs \<Longrightarrow> \<exists>xs\<in>A. P xs"
  by (metis set_rev_mp)

lemma tshuffle_exchange: "lfinite xs \<Longrightarrow> lfinite ys \<Longrightarrow> (xs \<sha> ys) \<cdot> (xs' \<sha> ys') \<subseteq> (xs \<frown> xs') \<sha> (ys \<frown> ys')"
  apply (auto simp add: tshuffle_words_def l_prod_def)
  apply (metis lfinite_lr)
  apply (metis lfinite_lr)
  apply (metis lefts_append)
  by (metis rights_append)

definition strict_lprefix :: "'a llist \<Rightarrow> 'a llist \<Rightarrow> bool" (infixl "\<prec>" 57) where
  "xs \<prec> ys \<equiv> lprefix xs ys \<and> xs \<noteq> ys"

lemma "xs \<prec> ys \<Longrightarrow> lfinite xs"
  by (metis not_lfinite_lprefix_conv_eq strict_lprefix_def)

lemma strict_lprefix: "xs \<prec> ys \<longleftrightarrow> (\<exists>xs'. ys = xs \<frown> xs' \<and> xs' \<noteq> LNil \<and> lfinite xs)"
  by (metis lprefixD lstrict_prefix_def lstrict_prefix_lappend_conv strict_lprefix_def)

axiomatization
  alternates :: "'a llist \<Rightarrow> 'b llist \<Rightarrow> ('a + 'b) llist"
where
  alternate: "alternates xs ys \<in> xs \<sha> ys"

lemma shuffle_never_empty: "xs \<sha> ys \<noteq> {}"
  apply (auto simp add: tshuffle_words_def)
  apply (rule_tac x = "alternates xs ys" in exI)
  using alternate by (auto simp add: tshuffle_words_def)

lemma
  assumes "zs' \<in> xs' \<sha> ys'"
  and "xs' \<prec> xs" and "ys' \<prec> ys"
  shows "\<exists>zs\<in>xs \<sha> ys. zs' \<prec> zs"
proof -
  obtain xs'' and ys''
  where "xs = xs' \<frown> xs''" and "xs'' \<noteq> LNil" and "lfinite xs'"
  and "ys = ys' \<frown> ys''" and "ys'' \<noteq> LNil" and "lfinite ys'"
    by (metis assms(2) assms(3) lappend_LNil2 lprefixD not_lfinite_lprefix_conv_eq strict_lprefix_def)

  have "xs'' \<sha> ys'' \<noteq> {}"
    by (metis shuffle_never_empty)
  then obtain zs'' where "zs'' \<in> xs'' \<sha> ys''"
    by (metis alternate)

  have "\<exists>zs\<in>(xs' \<sha> ys') \<cdot> (xs'' \<sha> ys''). zs' \<prec> zs"
    apply (subst fin_l_prod)
    apply (metis FIN_def `lfinite xs'` `lfinite ys'` lfinite_shuffle mem_Collect_eq subsetI)
    apply (simp add: strict_lprefix)
    apply (rule_tac x = "zs' \<frown> zs''" in exI)
    apply (intro conjI)
    apply (rule_tac x = "zs'" in exI)
    apply (rule_tac x = "zs''" in exI)
    apply simp_all
    apply (metis `zs'' \<in> xs'' \<sha> ys''` assms(1))
    apply (rule_tac x = "zs''" in exI)
    apply simp
    by (metis (lifting, full_types) `xs'' \<noteq> LNil` `zs'' \<in> xs'' \<sha> ys''` `lfinite xs'` `lfinite ys'` assms(1) lefts_LNil lfinite_shuffle mem_Collect_eq tshuffle_words_def)
  hence "\<exists>zs\<in>(xs' \<frown> xs'') \<sha> (ys' \<frown> ys''). zs' \<prec> zs"
    by (metis `lfinite xs'` `lfinite ys'` in_mono tshuffle_exchange)
  thus "\<exists>zs\<in>xs \<sha> ys. zs' \<prec> zs"
    by (metis `xs = xs' \<frown> xs''` `ys = ys' \<frown> ys''`)
qed

no_notation tshuffle_words (infix "\<sha>" 75)
notation pshuffle_words (infix "\<sha>" 75)

no_notation tshuffle (infixl "\<Sha>" 75)

definition pshuffle :: "'a plan \<Rightarrow> 'b plan \<Rightarrow> ('a + 'b) plan" (infixl "\<Sha>" 75) where
  "X \<Sha> Y \<equiv> \<Union>{x \<sha> y|x y. x \<in> X \<and> y \<in> Y}"

lemma "zs' \<in> xs' \<sha> ys' \<Longrightarrow> xs' \<in> pclose (Pre xs) \<Longrightarrow> ys' \<in> pclose (Pre ys) \<Longrightarrow> \<exists>zs\<in>(Pre xs) \<sha> (Pre ys). zs' \<in> pclose zs"
  apply simp_all
  apply (erule exE)+
  apply auto
  sledgehammer  


lemma "(pclose xs \<Sha> pclose ys) = (xs \<sha> ys)\<^sup>\<dagger>"
  apply (auto simp add: pshuffle_def pclosure_def)
  apply (rename_tac zs xs' ys')
  apply (cases xs)
  apply (simp_all)
  apply (cases ys)
  apply simp_all
  apply (erule disjE)
  apply (erule disjE)
  sledgehammer

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
