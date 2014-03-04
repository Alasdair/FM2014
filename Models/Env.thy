theory Env
  imports Language Mumble_Language
begin

coinductive env :: "'a rel \<Rightarrow> ('a \<times> 'a) llist \<Rightarrow> bool" for "\<Gamma>" where
  EqNil [intro!]: "env \<Gamma> LNil"
| EqSingle [intro!]: "env \<Gamma> (LCons \<sigma> LNil)"
| EqPair [intro!]: "(snd \<sigma>, fst \<sigma>') \<in> \<Gamma> \<Longrightarrow> env \<Gamma> (LCons \<sigma>' t) \<Longrightarrow> env \<Gamma> (LCons \<sigma> (LCons \<sigma>' t))"

lemma env_LConsD [dest]: "env \<Gamma> (LCons \<sigma> t) \<Longrightarrow> env \<Gamma> t"
  by (erule env.cases) auto

lemma env_LConsE [elim]: "env \<Gamma> (LCons \<sigma> (LCons \<sigma>' t)) \<Longrightarrow> (snd \<sigma>, fst \<sigma>') \<in> \<Gamma>"
  by (erule env.cases) auto

lemma lnth_repeat [simp]: "lnth (repeat x) n = x"
  by (induct n) simp_all

lemma inf_stutter_env:
  assumes "(\<sigma>, \<sigma>) \<in> \<Gamma>"
  shows "env \<Gamma> (repeat (\<sigma>, \<sigma>))"
proof -
  have "\<forall>n. (snd (lnth (repeat (\<sigma>, \<sigma>)) n), fst (lnth (repeat (\<sigma>, \<sigma>)) (Suc n))) \<in> \<Gamma>"
    by (simp add: assms del: lnth_iterates)
  thus ?thesis
  proof coinduct
    case (env t)
    show ?case
    proof (cases t)
      assume "t = LNil"
      thus ?case by simp
    next
      fix \<sigma> t'
      assume [simp]: "t = LCons \<sigma> t'"
      hence "?EqSingle \<or> ?EqPair"
      proof (cases t')
        assume "t' = LNil"
        thus "?EqSingle \<or> ?EqPair" by simp
      next
        fix \<sigma>' t''
        assume [simp]: "t' = LCons \<sigma>' t''"
        from env
        have "?EqPair"
          by (auto, erule_tac x = 0 in allE, auto, erule_tac x = "Suc n" in allE, auto)
        thus "?EqSingle \<or> ?EqPair" by simp
      qed
      thus ?case by simp
    qed
  qed
qed

definition Env :: "'a rel \<Rightarrow> ('a \<times> 'a) lan" where
  "Env \<Gamma> = Collect (env \<Gamma>)"

definition Rely :: "'a rel \<Rightarrow> ('a \<times> 'a) lan \<Rightarrow> ('a \<times> 'a) lan" ("rely _ \<bullet> _" [51,51] 52) where
  "rely R \<bullet> X \<equiv> X \<inter> Env (R\<^sup>*)"

lemma env_interE1 [elim]: "env (R \<inter> S) x \<Longrightarrow> env S x"
proof -
  assume "env (R \<inter> S) x"
  thus ?thesis
  proof coinduct
    case (env t)
    show ?case
    proof (cases t)
      assume "t = LNil"
      thus ?case
        by simp
    next
      fix \<sigma> t'
      assume [simp]: "t = LCons \<sigma> t'"
      hence "?EqSingle \<or> ?EqPair"
      proof (cases t')
        assume "t' = LNil"
        thus "?EqSingle \<or> ?EqPair" by simp
      next
        fix \<sigma>' t''
        assume [simp]: "t' = LCons \<sigma>' t''"
        from env
        have "?EqPair"
          by auto (metis (full_types) IntD2 env_LConsE)
        thus "?EqSingle \<or> ?EqPair" by simp
      qed
      thus ?case by simp
    qed
  qed
qed

lemma env_interE2 [elim]: "env (R \<inter> S) x \<Longrightarrow> env R x"
  by (metis env_interE1 inf_commute)

lemma env_interI [intro]: "env R t \<Longrightarrow> env S t \<Longrightarrow> env (R \<inter> S) t"
proof -
  assume "env R t" and "env S t"
  hence "env R t \<and> env S t"
    by auto
  thus "env (R \<inter> S) t"
  proof (coinduct)
    case (env t)
    thus ?case
    proof (cases t)
      assume "t = LNil"
      thus ?case
        by simp
    next
      fix \<sigma> t'
      assume [simp]: "t = LCons \<sigma> t'"
      hence "?EqSingle \<or> ?EqPair"
      proof (cases t')
        assume "t' = LNil"
        thus "?EqSingle \<or> ?EqPair" by simp
      next
        fix \<sigma>' t''
        assume [simp]: "t' = LCons \<sigma>' t''"
        from env
        show "?EqSingle \<or> ?EqPair"
          by auto
      qed
      thus ?case by simp
    qed
  qed
qed

lemma Rely_continuous: "rely R \<bullet> (\<Union>\<XX>) = \<Union>{(rely R \<bullet> X) |X. X \<in> \<XX>}"
  by (auto simp add: Rely_def)

lemma Rely_inter [simp]: "rely R \<bullet> X \<inter> Y = (rely R \<bullet> X) \<inter> (rely R \<bullet> Y)"
  by (metis Rely_def Int_assoc inf_commute inf_left_idem)

lemma Rely_union [simp]: "rely R \<bullet> X \<union> Y = (rely R \<bullet> X) \<union> (rely R \<bullet> Y)"
  by (auto simp add: Rely_def)

lemma Rely_coextensive [intro!]: "rely R \<bullet> X \<subseteq> X"
  by (auto simp add: Rely_def)

lemma Rely_iso [intro]: "X \<subseteq> Y \<Longrightarrow> rely R \<bullet> X \<subseteq> rely R \<bullet> Y"
  by (auto simp add: Rely_def)

lemma Rely_idem [simp]: "rely R \<inter> S \<bullet> X \<subseteq> rely R \<bullet> rely S \<bullet> X"
  apply (auto simp add: Rely_def Env_def)
  apply (metis env_interE1 inf_absorb1 inf_sup_ord(2) rtrancl_mono)
  by (metis env_interE2 inf_absorb2 inf_sup_ord(1) rtrancl_mono)

lemma Rely_comm: "rely R \<bullet> rely S \<bullet> X = rely S \<bullet> rely R \<bullet> X"
  by (auto simp add: Rely_def)

lemma Rely_rtrancl [simp]: "rely (S\<^sup>*) \<bullet> X = rely S \<bullet> X"
  by (metis Rely_def rtrancl_idemp)

lemma "rely (R\<^sup>* \<inter> S\<^sup>*) \<bullet> X = rely R \<bullet> rely S \<bullet> X"
  apply (intro antisym)
  apply (subst Rely_rtrancl[symmetric]) back back
  apply (subst Rely_rtrancl[symmetric]) back
  apply (rule Rely_idem)
  apply (auto simp add: Rely_def Env_def)
  by (metis env_interE1 env_interI inf.orderE r_into_rtrancl subsetI)

lemma Rely_zero [simp]: "rely R \<bullet> {} = {}"
  by (simp add: Rely_def)

lemma UNIV_env [intro!]: "env UNIV x"
proof -
  have True
    by auto
  thus ?thesis
    by (coinduct, auto, metis neq_LNil_conv surj_pair)
qed

lemma [simp]: "UNIV\<^sup>* = UNIV"
  by (metis (full_types) UNIV_I UNIV_eq_I r_into_rtrancl)

lemma Rely_top: "rely UNIV \<bullet> X = X"
  by (auto simp add: Rely_def Env_def)

definition guar :: "('a \<times> 'a) lan \<Rightarrow> 'a rel" where
  "guar X \<equiv> rtrancl (\<Union>(lset ` X))"

lemma [simp]: "ys \<notin> ltls ys \<longleftrightarrow> False"
  by (metis ltls.intros(1))

lemma env_if_no_pairs:
  assumes "\<not> (\<exists>ys \<sigma> \<sigma>' zs. lfinite ys \<and> xs = ys \<frown> LCons \<sigma> (LCons \<sigma>' zs) \<and> (snd \<sigma>, fst \<sigma>') \<notin> R)"
  shows "env R xs"
  using assms
proof coinduct
  case (env xs)
  thus ?case
  proof (cases xs)
    assume "xs = LNil"
    thus ?case
      by simp
  next
    fix \<sigma> xs'
    assume [simp]: "xs = LCons \<sigma> xs'"
    hence "?EqSingle \<or> ?EqPair"
    proof (cases xs')
      assume "xs' = LNil"
      thus "?EqSingle \<or> ?EqPair" by simp
    next
      fix \<sigma>' xs''
      assume [simp]: "xs' = LCons \<sigma>' xs''"
      from env
      have "?EqPair"
        apply auto
        apply (metis `xs = LCons \<sigma> xs'` `xs' = LCons \<sigma>' xs''` env lappend_code(1) lfinite_LNil)
        by (metis lappend_code(2) lfinite_LCons)
      thus "?EqSingle \<or> ?EqPair" by simp
    qed
    thus ?case by auto
  qed
qed

lemma not_envE: "\<not> env R xs \<Longrightarrow> \<exists>ys \<sigma> \<sigma>' zs. lfinite ys \<and> xs = ys \<frown> LCons \<sigma> (LCons \<sigma>' zs) \<and> (snd \<sigma>, fst \<sigma>') \<notin> R"
  by (metis env_if_no_pairs)

lemma in_shuffleE: "zs \<in> lmap \<langle>id,id\<rangle> ` (xs \<sha> ys) \<Longrightarrow> (\<exists>zs'. zs' \<in> (xs \<sha> ys) \<and> zs = lmap \<langle>id,id\<rangle> zs')"
  by (auto simp add: image_def)

lemma "zs \<in> (xs \<sha> ys) \<Longrightarrow> (\<exists>t. zs = xs \<triangleright> t \<triangleleft> ys \<and> llength (\<ll> t) = llength xs \<and> llength (\<rr> t) = llength ys)"
  apply (rule_tac x = "traj zs" in exI)
  apply auto
  apply (metis (mono_tags) mem_Collect_eq reinterleave tshuffle_words_def)
  apply (metis (mono_tags) mem_Collect_eq tshuffle_words_def)
  by (metis (mono_tags) mem_Collect_eq tshuffle_words_def)

lemma in_shuffleE2: "zs \<in> lmap \<langle>id,id\<rangle> ` (xs \<sha> ys) \<Longrightarrow> (\<exists>t. zs = lmap \<langle>id,id\<rangle> (xs \<triangleright> t \<triangleleft> ys))"
  apply (drule in_shuffleE)
  apply (erule exE)
  apply (rule_tac x = "traj zs'" in exI)
  by (metis (mono_tags) mem_Collect_eq reinterleave tshuffle_words_def)

lemma in_rely_shuffleE: "zs \<in> rely R \<bullet> lmap \<langle>id,id\<rangle> ` (xs \<sha> ys) \<Longrightarrow> (\<exists>t. zs = lmap \<langle>id,id\<rangle> (xs \<triangleright> t \<triangleleft> ys) \<and> env (R\<^sup>*) zs)"
  by (simp add: Rely_def Env_def) (metis in_shuffleE2)

notation ltake ("\<up>")
  and ldrop ("\<down>")

lemma [simp]: "llength (\<rr> (ltakeWhile is_right t)) = llength (ltakeWhile is_right t)"
  sorry

lemma [simp]: "LNil \<triangleright> ltakeWhile is_right t \<triangleleft> \<up> (llength (ltakeWhile is_right t)) zs = lmap Inr (\<up> (llength (ltakeWhile is_right t)) zs)"
  sorry

lemma 
  assumes "env R (lmap \<langle>id,id\<rangle> (LCons \<sigma> (LCons \<sigma>' ys) \<triangleright> t \<triangleleft> zs))"
  and "llength (\<ll> t) = llength (LCons \<sigma> (LCons \<sigma>' ys))"
  and "llength (\<rr> t) = llength zs"
  shows "(snd \<sigma>, fst \<sigma>') \<in> (R \<union> lset zs)\<^sup>*"
proof -
  let ?TR = "ltakeWhile is_right"
  let ?DR = "ldropWhile is_right"

  have "env R (lmap \<langle>id,id\<rangle> (LCons \<sigma> (LCons \<sigma>' ys) \<triangleright> ?TR t \<frown> ?DR t \<triangleleft> zs))"
    by (metis assms(1) lappend_ltakeWhile_ldropWhile)
  also have "... = lmap \<langle>id,id\<rangle> (lmap Inr (\<up> (llength (?TR t)) zs) \<frown> (LCons \<sigma> (LCons \<sigma>' ys) \<triangleright> ?DR t \<triangleleft> \<down> (llength (?TR t)) zs))"
    apply (subst interleave_append_llength)
    apply (metis assms(2) lappend_ltakeWhile_ldropWhile)
    apply (metis assms(3) lappend_ltakeWhile_ldropWhile)
    by simp
  also have "... = \<up> (llength (?TR t)) zs \<frown> lmap \<langle>id,id\<rangle> (LCons \<sigma> (LCons \<sigma>' ys) \<triangleright> ?DR t \<triangleleft> \<down> (llength (?TR t)) zs)"
    sorry
  finally have "env R (\<up> (llength (?TR t)) zs \<frown> lmap \<langle>id,id\<rangle> (LCons \<sigma> (LCons \<sigma>' ys) \<triangleright> ?DR t \<triangleleft> \<down> (llength (?TR t)) zs))"
    by simp

  hence "env R (lmap \<langle>id,id\<rangle> (LCons \<sigma> (LCons \<sigma>' ys) \<triangleright> ?DR t \<triangleleft> \<down> (llength (?TR t)) zs))"
    sorry
  also have "... = lmap \<langle>id,id\<rangle> (LCons \<sigma> (LCons \<sigma>' ys) \<triangleright> LCons (Inl ()) (ltl (?DR t)) \<triangleleft> \<down> (llength (?TR t)) zs)"
    sorry
  also have "... = LCons \<sigma> (lmap \<langle>id,id\<rangle> (LCons \<sigma>' ys \<triangleright> ltl (?DR t) \<triangleleft> \<down> (llength (?TR t)) zs))"
    sorry

lemma
  assumes "\<exists>zs. zs \<in> rely R \<bullet> lmap \<langle>id,id\<rangle> ` (xs \<sha> ys)"
  shows "env ((R \<union> lset ys)\<^sup>*) xs"
  using assms
  apply -
  apply (rule env_if_no_pairs)
  apply auto
  apply (drule in_rely_shuffleE)
  apply (erule exE)
  apply auto
  using assms
proof (coinduct xs)
  case (env xs)
  thus ?case
  proof (cases xs)
    assume "xs = LNil"
    thus ?case
      by simp
  next
    fix \<sigma> xs'
    assume [simp]: "xs = LCons \<sigma> xs'"
    hence "?EqSingle \<or> ?EqPair"
    proof (cases xs')
      assume "xs' = LNil"
      thus "?EqSingle \<or> ?EqPair" by simp
    next
      fix \<sigma>' xs''
      assume [simp]: "xs' = LCons \<sigma>' xs''"
      from env
      have "?EqPair"
        apply (rule_tac x = \<sigma> in exI)
        apply (rule_tac x = \<sigma>' in exI)
        apply (rule_tac x = xs'' in exI)
        apply (erule exE)
        apply (intro conjI)
        apply simp
        apply simp
        defer
        apply (drule in_rely_shuffleE)
        apply (intro disjI1)
        apply (metis case1)
        apply (intro disjI1)
        sorry
      thus "?EqSingle \<or> ?EqPair"
        by auto
    qed
    thus ?case by simp
  qed
qed


lemma
  assumes "zs \<in> xs \<sha> ys \<and> env (R\<^sup>*) (lmap \<langle>id,id\<rangle> zs)"
  shows "env ((R \<union> lset ys)\<^sup>*) xs"
  using assms
proof (coinduct)
  case (env xs)
  thus ?case
  proof (cases xs)
    assume "xs = LNil"
    thus ?case
      by simp
  next
    fix \<sigma> xs'
    assume [simp]: "xs = LCons \<sigma> xs'"
    hence "?EqSingle \<or> ?EqPair"
    proof (cases xs')
      assume "xs' = LNil"
      thus "?EqSingle \<or> ?EqPair" by simp
    next
      fix \<sigma>' xs''
      assume [simp]: "xs' = LCons \<sigma>' xs''"
      from env
      have "?EqPair"
        apply (rule_tac x = \<sigma> in exI)
        apply (rule_tac x = \<sigma>' in exI)
        apply (rule_tac x = xs'' in exI)
        apply (intro conjI)
        apply simp
        defer
        apply (intro disjI2)
        by auto
    qed
    thus ?case by simp
  qed
qed

notepad begin
  fix xs ys :: "('a \<times> 'a) llist" and zs and R
  assume "zs \<in> xs \<sha> ys \<and> env R (lmap \<langle>id,id\<rangle> zs)"
  hence "env R xs"
  proof coinduct
    case (env xs)
    thus ?case
    proof (cases xs)
      assume "xs = LNil"
      thus ?case
        by simp
    next
      fix \<sigma> xs'
      assume [simp]: "xs = LCons \<sigma> xs'"
      hence "?EqSingle \<or> ?EqPair"
      proof (cases xs')
        assume "xs' = LNil"
        thus "?EqSingle \<or> ?EqPair" by simp
      next
        fix \<sigma>' xs''
        assume [simp]: "xs' = LCons \<sigma>' xs''"
        from env
        have "?EqPair"
          apply auto
          sledgehammer
          by auto
      qed
      thus ?case by simp
    qed
  qed
qed

(*
lemma "rely R \<bullet> (X \<parallel> Y) \<subseteq> rely R \<bullet> (rely R \<union> guar Y \<bullet> X) \<parallel> (rely R \<union> guar X \<bullet> Y)"
  sorry

lemma "zs \<in> xs \<sha> ys \<Longrightarrow> env R zs \<Longrightarrow> env (R \<union> lset ys) xs"

lemma "rely R \<bullet> (X \<parallel> Y) \<subseteq> (rely R \<union> guar Y \<bullet> X) \<parallel> (rely R \<union> guar X \<bullet> Y)"

lemma rely_tshuffle_words:
  "rely R \<bullet> lmap \<langle>id,id\<rangle> ` (xs \<sha> ys) = lmap \<langle>id,id\<rangle> ` {zs. \<ll> zs = xs \<and> \<rr> zs = ys \<and> env R (lmap \<langle>id,id\<rangle> zs)}"
  by (auto simp add: image_def Rely_def Env_def tshuffle_words_def)
*)

lemma "rely R \<bullet> (X \<parallel> Y) \<le> (rely R \<bullet> X) \<parallel> Y"
proof -
  obtain zs where "zs \<in> rely R \<bullet> (X \<parallel> Y)"
    sledgehammer


lemma "\<Union>{rely R \<bullet> lmap \<langle>id,id\<rangle> ` (xs \<sha> ys) |xs ys. xs \<in> X \<and> ys \<in> Y} \<subseteq> \<Union>{lmap \<langle>id,id\<rangle> ` (xs \<sha> ys) |xs ys. xs \<in> rely R \<bullet> X \<and> ys \<in> Y}"
  apply (subst Sup_le_iff)
  apply (intro ballI)
  apply safe
  apply (simp only: rely_tshuffle_words)
  apply (simp add: image_def)
  apply safe

lemma "env R xs \<Longrightarrow> rtrancl (lset ys) \<subseteq> R \<Longrightarrow> zs \<in> lmap \<langle>id,id\<rangle> ` (xs \<sha> ys) \<Longrightarrow> env R zs"
proof -
  have "env R xs \<and> rtrancl (lset ys) \<subseteq> R \<and> zs \<in> lmap \<langle>id,id\<rangle> ` (xs \<sha> ys)"
    sorry  
  hence "env R zs"
  proof coinduct

    case (env t)
    show ?case
    proof (cases t)
      assume "t = LNil"
      thus ?case
        by simp
    next
      fix \<sigma> t'
      assume [simp]: "t = LCons \<sigma> t'"
      hence "?EqSingle \<or> ?EqPair"
      proof (cases t')
        assume "t' = LNil"
        thus "?EqSingle \<or> ?EqPair" by simp
      next
        fix \<sigma>' t''
        assume [simp]: "t' = LCons \<sigma>' t''"
        from env
        have "?EqPair"
          apply (auto simp add: tshuffle_words_def)
          apply (subgoal_tac "\<exists>v x'. x = LCons (Inl v) x' \<or> x = LCons (Inr v) x'")
          prefer 2
          apply (metis lmap_eq_LCons_conv swap.cases)
          apply (erule exE)+
          apply (erule disjE)
          apply simp
          apply (subgoal_tac "\<exists>v' x''. x' = LCons (Inl v') x'' \<or> x' = LCons (Inr v') x''")
          prefer 2
          apply (metis lmap_eq_LCons_conv swap.cases)
          apply (erule exE)+
          apply (erule disjE)
          apply simp
          apply (metis env_LConsE)
          apply simp
          sledgehammer
          apply (subgoal_tac "\<exists>v' x''. x' = LCons (Inl v') x'' \<or> x' = LCons (Inr v') x''")
          prefer 2
          apply (metis lmap_eq_LCons_conv swap.cases)
          apply (erule exE)+
          apply (erule disjE)
          apply simp
          apply (metis env_LConsE)

  shows "rely R \<bullet> (X \<parallel> Y) \<le> (rely R \<bullet> X) \<parallel> Y"
proof -
  have "rely R \<bullet> (X \<parallel> Y) \<subseteq> rely R \<bullet> \<Union>{lmap \<langle>id,id\<rangle> ` (xs \<sha> ys) |xs ys. xs \<in> X \<and> ys \<in> Y}"
    by (simp only: guar_def shuffle_def)
  also have "... = \<Union>{rely R \<bullet> lmap \<langle>id,id\<rangle> ` (xs \<sha> ys) |xs ys. xs \<in> X \<and> ys \<in> Y}"
    by (auto simp only: Rely_continuous)
  also have "... \<subseteq> \<Union>{lmap \<langle>id,id\<rangle> ` (xs \<sha> ys) |xs ys. xs \<in> (rely R \<bullet> X) \<and> ys \<in> Y}"
    apply (rule Sup_mono)
    apply auto
    apply (subgoal_tac "\<not> env R xs \<or> env R xs")
    apply (erule disjE)

lemma Con_l_prod: "Env R = (Env R \<cdot> Env R) \<inter> Env R"
  by (auto simp add: Env_def l_prod_def) (metis EqNil lappend_LNil2)

lemma [simp]: "rely R \<bullet> {xs \<in> X. \<not> lfinite xs} = rely R \<bullet> X \<cdot> {}"
  by (auto simp add: l_prod_def Rely_def)

lemma consistent_lappend1 [dest]:
  assumes "consistent (t \<frown> s)" shows "consistent t"
proof (cases "lfinite t")
  assume "lfinite t"
  from this and assms
  show "consistent t"
  proof (induct t rule: lfinite_induct)
    case Nil show ?case by blast
  next
    case (Cons \<sigma> t)
    thus ?case
      by (cases t) auto
  qed
next
  assume "\<not> lfinite t"
  from this and assms
  show "consistent t"
    by (metis lappend_inf)
qed

lemma consistent_lappend2 [dest]: "lfinite t \<Longrightarrow> consistent (t \<frown> s) \<Longrightarrow> consistent s"
proof (induct t rule: lfinite_induct)
  case Nil thus ?case by simp
next
  case (Cons \<sigma> t)
  thus ?case
    by (cases t) auto
qed

lemma [dest]: "xs \<frown> ys \<in> Con \<Longrightarrow> xs \<in> Con"
  by (auto simp add: Con_def)

lemma [dest]: "lfinite xs \<Longrightarrow> xs \<frown> ys \<in> Con \<Longrightarrow> ys \<in> Con"
  by (auto simp add: Con_def)

lemma [simp]: "X \<cdot> {} \<union> X \<inter> FIN = X"
  by (auto simp add: l_prod_def FIN_def)

lemma Aczel_l_prod [simp]: "\<pi> (\<pi> X \<cdot> \<pi> Y) = \<pi> (X \<cdot> Y)"
proof -
  have "\<pi> (X \<cdot> Y) = \<pi> {xs \<in> X. \<not> lfinite xs} \<union> \<pi> {xs \<frown> ys |xs ys. xs \<in> X \<and> lfinite xs \<and> ys \<in> Y}"
    by (simp add: l_prod_def)
  also have "... = \<pi> X \<cdot> {} \<union> \<pi> {xs \<frown> ys |xs ys. xs \<in> X \<and> lfinite xs \<and> ys \<in> Y}"
    by simp
  also have "... = \<pi> X \<cdot> {} \<union> \<pi> ((\<pi> X \<inter> FIN) \<cdot> \<pi> Y)"
    by (subst fin_l_prod, metis (mono_tags) inf.cobounded2, auto simp add: Aczel_def FIN_def)
  also have "... = \<pi> (\<pi> X \<cdot> {} \<union> (\<pi> X \<inter> FIN) \<cdot> \<pi> Y)"
    by (auto simp add: Aczel_def l_prod_def)
  also have "... = \<pi> (\<pi> X \<cdot> {} \<cdot> \<pi> Y \<union> (\<pi> X \<inter> FIN) \<cdot> \<pi> Y)"
    by (metis l_prod_zero seq.mult_assoc)
  also have "... = \<pi> ((\<pi> X \<cdot> {} \<union> (\<pi> X \<inter> FIN)) \<cdot> \<pi> Y)"
    by (metis l_prod_distr)
  also have "... = \<pi> (\<pi> X \<cdot> \<pi> Y)"
    by simp
  finally show ?thesis by blast
qed

lemma [simp]: "ltake \<infinity> xs = xs"
  apply (cases "lfinite xs")
  apply (induct xs rule: lfinite_induct)
  apply simp_all
  apply (subst eSuc_infinity[symmetric])
  apply (subst ltake_LCons)
  apply (simp del: eSuc_infinity)
  by (metis ltake_all not_lfinite_llength order_refl)

lemma llist_cases3:
  "P LNil \<Longrightarrow> (\<And>x. xs = LCons x LNil \<Longrightarrow> P xs) \<Longrightarrow> (\<And>x y ys. xs = LCons y (LCons x ys) \<Longrightarrow> P xs) \<Longrightarrow> P xs"
  by (metis (full_types) lhd_LCons_ltl) 

lemma consistent_ltake: "consistent t \<Longrightarrow> consistent (ltake n t)"
proof (induct n, simp_all)
  fix n
  assume "consistent t"
  thus "consistent (ltake (enat n) t)"
  proof (induct n arbitrary: t)
    case 0 show ?case by (auto simp: enat_0)
  next
    case (Suc n)
    show ?case
    proof (rule llist_cases3[where xs = t])
      show "consistent (ltake (enat (Suc n)) LNil)"
        by (simp add: eSuc_enat[symmetric]) blast
    next
      fix \<sigma>
      assume "t = LCons \<sigma> LNil"
      from this and Suc.prems show "consistent (ltake (enat (Suc n)) t)"
        by (cases n) (simp_all add: enat_0 eSuc_enat[symmetric])
    next
      fix \<sigma> \<sigma>' t'
      assume "t = LCons \<sigma> (LCons \<sigma>' t')"
      from this and Suc show "consistent (ltake (enat (Suc n)) t)"
        apply (cases n)
        apply (simp_all add: eSuc_enat[symmetric] enat_0)
        apply blast
        apply (rule EqPair)
        apply (erule consistent_LConsE)
        by (metis consistent_LConsD ltake_eSuc_LCons)
    qed
  qed
qed

lemma Aczel_par: "\<pi> (\<pi> X \<parallel> \<pi> Y) \<le> \<pi> (X \<parallel> Y)"
  by (metis Aczel_coextensive Aczel_iso par.mult_isol_var)

lemma Aczel_consistent [simp]: "\<pi> X \<inter> Con = \<pi> X"
  by (simp add: Aczel_def)

lemma Aczel_UNIV [simp]: "\<pi> UNIV = Con"
  by (auto simp add: Aczel_def)

lemma lappend_consistent:
  "lfinite xs \<Longrightarrow> consistent (LCons x xs \<frown> LCons y ys) \<Longrightarrow> snd (llast (LCons x xs)) = fst y"
  by (induct xs arbitrary: x rule: lfinite_induct) auto

lemma [dest!]: "consistent (LCons x xs \<frown> LCons y ys) \<Longrightarrow> lfinite xs \<longrightarrow> snd (llast (LCons x xs)) = fst y"
  by (metis lappend_consistent)

lemma [simp]: "llast (LCons (\<sigma>, \<sigma>) (llist_of (replicate n (\<sigma>, \<sigma>)))) = (\<sigma>, \<sigma>)"
  by (induct n) auto

definition Aczel_mult :: "('a \<times> 'a) lan \<Rightarrow> ('a \<times> 'a) lan \<Rightarrow> ('a \<times> 'a) lan" (infixl "\<otimes>" 75) where
  "X \<otimes> Y = \<pi> (X \<cdot> Y)"

lemma amult_distl [simp]: "X \<otimes> (Y \<union> Z) = X \<otimes> Y \<union> X \<otimes> Z"
  by (simp add: Aczel_mult_def)

lemma amult_distr [simp]: "(X \<union> Y) \<otimes> Z = X \<otimes> Z \<union> Y \<otimes> Z"
  by (simp add: Aczel_mult_def)

lemma amult_assoc: "X \<otimes> (Y \<otimes> Z) = (X \<otimes> Y) \<otimes> Z"
  by (simp add: Aczel_mult_def) (metis Aczel_def Aczel_l_prod inf_commute inf_left_idem seq.mult_assoc)

lemma consistent_replicate': "consistent (llist_of xs) \<Longrightarrow> \<forall>y\<in>set xs. \<exists>\<sigma>. y = (\<sigma>, \<sigma>) \<Longrightarrow> \<exists>n \<sigma>. xs = replicate n (\<sigma>, \<sigma>)"
proof (induct xs)
  case Nil show ?case by simp
next
  case (Cons x1 xs)
  thus ?case
  proof (induct xs)
    case Nil thus ?case
      by (rule_tac x = 1 in exI) auto
  next
    case (Cons x2 xs)
    thus ?case
      apply -
      apply simp
      apply (frule consistent_LConsD)
      apply simp
      apply (frule consistent_LConsD) back
      apply simp
      apply auto
      apply (subgoal_tac "\<exists>n \<sigma>. xs = replicate n (\<sigma>, \<sigma>)")
      apply simp
      apply (subgoal_tac "\<sigma>'' = \<sigma>'")
      apply simp
      apply (subgoal_tac "\<sigma>' = \<sigma>")
      apply simp
      apply (rule_tac x = "Suc n" in exI)
      apply simp
      apply (metis in_set_member in_set_replicate member_rec(1) prod.inject)
      apply (drule consistent_LConsE)
      apply simp
      apply (rule_tac x = "n - 1" in exI)
      by (metis tl.simps(2) tl_replicate)
  qed
qed

lemma replicate_finite_Con: "llist_of (replicate n (\<sigma>, \<sigma>)) \<in> Con"
proof (induct n)
  case 0 show ?case
    by (auto simp add: Con_def)
next
  case (Suc n) thus ?case
    by (cases n) (auto simp add: Con_def)
qed

lemma Aczel_inf [simp]: "\<pi> (x\<cdot>{}) = (\<pi> x)\<cdot>{}"
  by (auto simp add: l_prod_def Con_def)

lemma Aczel_one [simp]: "\<pi> {LNil} = {LNil}"
  by (auto simp add: Aczel_def Con_def)

primrec proj_power :: "('a \<times> 'a) lan \<Rightarrow> nat \<Rightarrow> ('a \<times> 'a) lan" where
  "proj_power x 0 = {LNil}"
| "proj_power x (Suc n) = \<pi> (x \<cdot> proj_power x n)"

definition proj_powers :: "('a \<times> 'a) lan \<Rightarrow> ('a \<times> 'a) lan set" where
  "proj_powers x  = {y. (\<exists>i. y = proj_power x i)}"

lemma power_to_proj: "\<pi> (power x i) = proj_power x i"
  apply (induct i)
  apply simp_all
  by (metis Aczel_idem Aczel_l_prod)

lemma proj_power_proj: "proj_power x i = proj_power (\<pi> x) i"
  apply (induct i)
  apply simp_all
  by (metis Aczel_l_prod Language.power.simps(2) power_to_proj proj_power.simps(2))

lemma powers_to_proj: "\<pi> ` powers x = proj_powers x"
  apply (auto simp add: proj_powers_def powers_def image_def)
  apply (metis power_to_proj)
  by (metis power_to_proj)

lemma proj_powers_proj: "proj_powers x = proj_powers (\<pi> x)"
  apply (auto simp add: proj_powers_def)
  apply (metis proj_power_proj)
  by (metis proj_power_proj)

lemma "\<Union>{\<pi> X |X. X \<in> powers (x \<inter> FIN)} = \<Union>{X. X \<in> \<pi> ` powers (x \<inter> FIN)}"
  by (auto simp add: image_def)

lemma Aczel_fin_star_lem: "\<Union>{\<pi> X |X. X \<in> powers (x \<inter> FIN)} = \<Union>{\<pi> X |X. X \<in> powers (\<pi> (x \<inter> FIN))}"
proof -
  have "\<Union>{\<pi> X |X. X \<in> powers (x \<inter> FIN)} = \<Union>{X. X \<in> \<pi> ` powers (x \<inter> FIN)}"
    by (auto simp add: image_def)
  also have "... = \<Union>{X. X \<in> proj_powers (x \<inter> FIN)}"
    by (metis powers_to_proj)
  also have "... = \<Union>{X. X \<in> proj_powers (\<pi> (x \<inter> FIN))}"
    by (metis proj_powers_proj)
  also have "... =  \<Union>{X. X \<in> \<pi> ` powers (\<pi> (x \<inter> FIN))}"
    by (metis powers_to_proj)
  also have "... = \<Union>{\<pi> X |X. X \<in> powers (\<pi> (x \<inter> FIN))}"
    by (auto simp add: image_def)
  finally show ?thesis .
qed

lemma Aczel_fin_star: "\<pi> ((x \<inter> FIN)\<^sup>\<star>) \<le> \<pi> ((\<pi> (x \<inter> FIN))\<^sup>\<star>)"
  apply (subst star_power_fin)
  apply simp
  apply (subst star_power_fin)
  apply (metis Aczel_coextensive inf.bounded_iff)
  apply (subst Aczel_continuous)+
  by (metis Aczel_fin_star_lem subset_refl)

lemma Aczel_star1: "\<pi> (x\<^sup>\<star>) \<le> \<pi> (\<pi> x\<^sup>\<star>)"
proof -
  have "\<pi> (x\<^sup>\<star>) = \<pi> ((x \<inter> FIN \<union> x\<cdot>{})\<^sup>\<star>)"
    by simp
  also have "... = \<pi> ((x \<inter> FIN)\<^sup>\<star>\<cdot>x\<cdot>{} \<union> (x \<inter> FIN)\<^sup>\<star>)"
    by (simp only: seq.inf_part_star)
  also have "... = \<pi> ((x \<inter> FIN)\<^sup>\<star> \<cdot> (x\<cdot>{} \<union> {LNil}))"
    by (metis seq.distrib_left seq.mult.right_neutral seq.mult_assoc)
  also have "... = \<pi> (\<pi> ((x \<inter> FIN)\<^sup>\<star>) \<cdot> \<pi> (x\<cdot>{} \<union> {LNil}))"
    by (metis Aczel_l_prod)
  also have "... \<le> \<pi> (\<pi> ((\<pi> (x \<inter> FIN))\<^sup>\<star>) \<cdot> \<pi> (x\<cdot>{} \<union> {LNil}))"
    by (metis (hide_lams, no_types) Aczel_fin_star Aczel_iso seq.mult_isor)
  also have "... = \<pi> (\<pi> (\<pi> (x \<inter> FIN)\<^sup>\<star>) \<cdot> (\<pi> x \<cdot> {} \<union> {LNil}))"
    by (simp only: Aczel_union Aczel_inf Aczel_one)
  also have "... = \<pi> (\<pi> (\<pi> (x \<inter> FIN)\<^sup>\<star>) \<cdot> \<pi> x \<cdot> {} \<union> \<pi> (\<pi> (x \<inter> FIN)\<^sup>\<star>))"
    by (metis seq.distrib_left seq.mult.right_neutral seq.mult_assoc)
  also have "... = \<pi> (\<pi> (x \<inter> FIN)\<^sup>\<star> \<cdot> \<pi> x \<cdot> {} \<union> \<pi> (x \<inter> FIN)\<^sup>\<star>)"
    by (metis Aczel_idem Aczel_l_prod Aczel_union)
  also have "... = \<pi> ((\<pi> (x \<inter> FIN) \<union> \<pi> x \<cdot> {})\<^sup>\<star>)"
    by (simp only: seq.inf_part_star)
  also have "... = \<pi> ((\<pi> (x \<inter> FIN \<union> x\<cdot>{}))\<^sup>\<star>)"
    by (simp only: Aczel_union Aczel_inf Aczel_idem)
  also have "... = \<pi> (\<pi> x\<^sup>\<star>)"
    by simp
  finally show ?thesis .
qed

lemma Aczel_star [simp]: "\<pi> (\<pi> x\<^sup>\<star>) = \<pi> (x\<^sup>\<star>)"
  by (metis Aczel_def Aczel_iso Aczel_star1 par.add_ub2 seq.star_iso subset_antisym sup_inf_absorb)

end
