theory Antitrace
  imports Language
begin

function anti :: "('a \<times> 'a) llist \<Rightarrow> ('a \<times> 'a) llist" where
  "anti LNil = LNil"
| "anti (LCons (\<sigma>, \<sigma>') xs) = llist_unfold
     Option.is_none
     (\<lambda>t. case t of Some (\<sigma>, LNil) \<Rightarrow> (\<sigma>,\<sigma>) | Some (\<sigma>, LCons (\<sigma>', \<sigma>'') xs) \<Rightarrow> (\<sigma>, \<sigma>'))
     (\<lambda>t. case t of Some (\<sigma>, LNil) \<Rightarrow> None  | Some (\<sigma>, LCons (\<sigma>', \<sigma>'') xs) \<Rightarrow> Some (\<sigma>'', xs))
     (Some (\<sigma>, LCons (\<sigma>, \<sigma>') xs))"
 by auto (metis neq_LNil_conv surj_pair)
 termination by (metis "termination" wf_measure)

definition anti' :: "('a \<times> 'a) llist \<Rightarrow> ('a \<times> 'a) llist" where
  "anti' = llist_unfold (\<lambda>t. 2 \<le> llength t) (\<lambda>t. case t of LCons (\<sigma>, \<sigma>') (LCons (\<tau>, \<tau>') xs) \<Rightarrow> (\<sigma>', \<tau>)) (\<lambda>t. case t of LCons (\<sigma>, \<sigma>') (LCons (\<tau>, \<tau>') xs) \<Rightarrow> LCons (\<tau>, \<tau>') xs)"

declare Option.is_none_code(2)[simp]

lemma [simp]: "Option.is_none None"
  by (metis is_none_code(1))

lemma "anti (LCons (\<sigma>, \<sigma>') LNil) = LCons (\<sigma>, \<sigma>) (LCons (\<sigma>',\<sigma>') LNil)"
  by (simp add: llist_unfold_code)

lemma "anti (LCons (\<sigma>, \<sigma>') xs) = LCons (\<sigma>, \<sigma>) (ltl (anti (LCons (\<sigma>, \<sigma>') xs)))"
  by simp

axiomatization
  stutter :: "('a \<times> 'a) llist \<Rightarrow> ('a \<times> 'a) lan" and
  mumble :: "('a \<times> 'a) llist \<Rightarrow> ('a \<times> 'a) lan"
where
  anti_stutter: "anti (anti xs) \<in> stutter xs" and
  anti_mumble: "xs \<in> mumble (anti (anti xs))" and
  stutter_mumble: "(\<exists>ys. xs \<in> stutter ys \<and> ys \<in> mumble zs) \<longleftrightarrow> (\<exists>ys. xs \<in> mumble ys \<and> ys \<in> stutter zs)"

lemma anti_mumble_var: "mumble xs \<subseteq> mumble (anti (anti xs))"
  sorry

definition Stutter :: "('a \<times> 'a) lan \<Rightarrow> ('a \<times> 'a) lan" where
  "Stutter X = \<Union>{stutter xs |xs. xs \<in> X}"

lemma Stutter_iso: "X \<le> Y \<Longrightarrow> Stutter X \<le> Stutter Y"
  by (auto simp add: Stutter_def)

definition Mumble :: "('a \<times> 'a) lan \<Rightarrow> ('a \<times> 'a) lan" where
  "Mumble X = \<Union>{mumble xs |xs. xs \<in> X}"

lemma Mumble_iso: "X \<le> Y \<Longrightarrow> Mumble X \<le> Mumble Y"
  by (auto simp add: Mumble_def)

definition Anti :: "('a \<times> 'a) lan \<Rightarrow> ('a \<times> 'a) lan" where
  "Anti X = anti ` X"

lemma Stutter_Mumble: "Stutter (Mumble X) = Mumble (Stutter X)"
  by (auto simp add: Stutter_def Mumble_def) (metis stutter_mumble)+

definition SM_closure :: "('a \<times> 'a) lan \<Rightarrow> ('a \<times> 'a) lan" ("_\<^sup>\<dagger>" [1000] 1000) where
  "X\<^sup>\<dagger> = Stutter (Mumble X)"

lemma Stutter_iso_var: "X \<le> Stutter Y \<Longrightarrow> Stutter X \<le> Stutter Y"
  sorry

lemma Mumble_iso_var: "Mumble X \<le> Y \<Longrightarrow> Mumble X \<le> Mumble Y"
  sorry

lemma SM_iso: "X \<le> Y \<Longrightarrow> X\<^sup>\<dagger> \<le> Y\<^sup>\<dagger>"
  by (metis Mumble_iso SM_closure_def Stutter_iso)

lemma Anti_Anti_1: "(Anti (Anti X))\<^sup>\<dagger> \<subseteq> X\<^sup>\<dagger>"
  apply (simp add: Anti_def SM_closure_def)
  apply (simp only: Stutter_Mumble)
  apply (rule Mumble_iso)
  apply (rule Stutter_iso_var)
  apply (auto simp add: Mumble_def Stutter_def)
  by (metis anti_stutter)

lemma Anti_Anti_2: "X\<^sup>\<dagger> \<subseteq> (Anti (Anti X))\<^sup>\<dagger>"
  apply (auto intro!: Stutter_iso simp add: Anti_def SM_closure_def Mumble_def)
  by (metis anti_mumble_var rev_image_eqI subsetD)

lemma Anti_inv [simp]: "(Anti (Anti X))\<^sup>\<dagger> = X\<^sup>\<dagger>"
  by (metis Anti_Anti_1 Anti_Anti_2 subset_antisym)

lemma Anti_iso: "X \<le> Y \<Longrightarrow> Anti X \<le> Anti Y"
  by (auto simp add: Anti_def)

lemma SM_idem: "X\<^sup>\<dagger>\<^sup>\<dagger> = X\<^sup>\<dagger>"
  apply (auto simp add: SM_closure_def)
  sorry

lemma SM_ext: "X \<le> X\<^sup>\<dagger>"
  sorry

lemma Anti_SM: "(Anti X\<^sup>\<dagger>)\<^sup>\<dagger> \<le> (Anti X)\<^sup>\<dagger>"
  apply (auto simp add: Anti_def SM_closure_def image_def Stutter_def Mumble_def)
  apply (rule_tac x = "stutter xs" in exI)
  apply auto
  apply (rule_tac x = xs in exI)
  apply auto
  apply (rule_tac x = "mumble (anti xb)" in exI)
  apply auto
  apply (rule_tac x = "anti xsc" in exI)
  apply auto
  sledgehammer

lemma "Collect P = {xs. P xs}"

lemma "(Anti X)\<^sup>\<dagger> \<le> Y\<^sup>\<dagger> \<longleftrightarrow> X\<^sup>\<dagger> \<le> (Anti Y)\<^sup>\<dagger>"
  sledgehammer
  by (metis Anti_SM Anti_inv Anti_iso SM_iso)

lemma "(\<And>x. f (f x) = x) \<Longrightarrow> (\<And>x y. x \<le> y \<Longrightarrow> f x \<le> f y) \<Longrightarrow> f x \<le> y \<longleftrightarrow> x \<le> f y"
  by metis

end
