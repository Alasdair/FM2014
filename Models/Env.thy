theory Env
  imports Language Mumble_Language
begin

coinductive env :: "'a rel \<Rightarrow> ('a \<times> 'a) llist \<Rightarrow> bool" for "R" where
  EqNil [intro!,simp]: "env R LNil"
| EqSingle [intro!,simp]: "env R (LCons \<sigma> LNil)"
| EqPair [intro!]: "(snd \<sigma>, fst \<sigma>') \<in> R \<Longrightarrow> env R (LCons \<sigma>' t) \<Longrightarrow> env R (LCons \<sigma> (LCons \<sigma>' t))"

lemma env_tl [dest]: "env R (LCons \<sigma> t) \<Longrightarrow> env R t"
  by (erule env.cases) auto

lemma env_LConsD [dest]: "env R (LCons \<sigma> (LCons \<sigma>' t)) \<Longrightarrow> (snd \<sigma>, fst \<sigma>') \<in> R"
  by (erule env.cases) auto

no_notation Cons (infixr "#" 65)
notation LCons (infixr "#" 65)

coinductive rg :: "'a rel \<Rightarrow> ('a \<times> 'a) llist \<Rightarrow> ('a \<times> 'a) llist \<Rightarrow> bool" for R where
  EqNil [intro!,simp]: "rg R LNil LNil"
| EqSingle [intro!]: "rg R (LCons \<sigma> LNil) (LCons \<sigma> LNil)"
| EqPairR: "(\<sigma>\<^sub>1', \<sigma>\<^sub>2) \<in> R \<Longrightarrow> rg R ((\<sigma>\<^sub>2,\<sigma>\<^sub>2') # t) ((\<sigma>\<^sub>2,\<sigma>\<^sub>2') # t') \<Longrightarrow> rg R ((\<sigma>\<^sub>1,\<sigma>\<^sub>1') # (\<sigma>\<^sub>2,\<sigma>\<^sub>2') # t) ((\<sigma>\<^sub>1,\<sigma>\<^sub>1') # (\<sigma>\<^sub>2,\<sigma>\<^sub>2') # t')"
| EqPairNR: "(\<sigma>\<^sub>1', \<sigma>\<^sub>2) \<notin> R \<Longrightarrow> rg R ((\<sigma>\<^sub>1,\<sigma>\<^sub>1') # (\<sigma>\<^sub>2,\<sigma>\<^sub>2') # t) ((\<sigma>\<^sub>1,\<sigma>\<^sub>1') # (\<sigma>\<^sub>2,\<sigma>\<^sub>2'') # t')"

definition RG :: "'a rel \<Rightarrow> ('a \<times> 'a) lan \<Rightarrow> ('a \<times> 'a) lan" (infix "\<leadsto>" 60) where
  "R \<leadsto> X = {ys. \<exists>xs\<in>X. rg (R\<^sup>*) xs ys}"

lemma lprefix_lset: "lprefix xs ys \<Longrightarrow> lset xs \<subseteq> lset ys"
  by (metis lprefix_def lset_lappend1)

lemma [simp]: "env R (LCons \<sigma> (LCons \<sigma>' LNil)) \<longleftrightarrow> (snd \<sigma>, fst \<sigma>') \<in> R"
  by auto

definition prog :: "'a rel \<Rightarrow> ('a \<times> 'a) lan" where
  "prog X = {xs. lset xs \<subseteq> X\<^sup>*}"

lemma rg_equality [intro]: "xs = ys \<Longrightarrow> rg R xs ys"
proof -
  assume "xs = ys"
  thus "rg R xs ys"
  proof coinduct
    case (rg xs ys)
    show ?case
    proof (cases xs)
      assume "xs = LNil"
      thus ?case
        by (metis rg)
    next
      fix \<sigma> xs'
      assume [simp]: "xs = LCons \<sigma> xs'"
      hence "?EqSingle \<or> ?EqPairR \<or> ?EqPairNR"
        by (metis llist.exhaust prod.exhaust rg)
      thus ?case
        by blast
    qed
  qed
qed

lemma rg_ext: "X \<le> R \<leadsto> X"
  by (auto simp add: RG_def)

lemma rg_trans: "rg R xs ys \<Longrightarrow> rg R ys zs \<Longrightarrow> rg R xs zs"
  sorry

lemma "X \<le> R \<leadsto> Y \<Longrightarrow> R \<leadsto> X \<le> R \<leadsto> Y"
  apply (auto simp add: RG_def)
  apply (subgoal_tac "xs \<in> {ys. \<exists>xs\<in>Y. rg (R\<^sup>*) xs ys}")
  apply auto
  by (metis rg_trans)

lemma RG_continuous: "R \<leadsto> \<Union>\<XX> = \<Union>{R \<leadsto> X |X. X \<in> \<XX>}"
  by (auto simp add: RG_def)

lemma RG_guar_meet: "R \<leadsto> prog G\<^sub>1 \<inter> prog G\<^sub>2 = (R \<leadsto> prog G\<^sub>1) \<inter> (R \<leadsto> prog G\<^sub>2)"
  apply (auto simp add: RG_def)
  apply (rename_tac xs ys zs)

lemma RG_UNIV: "R \<leadsto> UNIV = UNIV"
  by (auto simp add: RG_def)

definition Env :: "'a rel \<Rightarrow> ('a \<times> 'a) lan" where
  "Env \<Gamma> = Collect (env \<Gamma>)"

definition Rely :: "'a rel \<Rightarrow> ('a \<times> 'a) lan \<Rightarrow> ('a \<times> 'a) lan" (infixr "\<Colon>" 52) where
  "R \<Colon> X \<equiv> X \<inter> Env (R\<^sup>*)"

lemma rg_refl [intro!,simp]: "rg R xs xs"
  by (metis rg_equality)

lemma "rg R (LCons x xs) (LCons y ys) \<Longrightarrow> x = y"
  by (erule rg.cases) auto

lemma rg_lappend: "rg R (\<sigma> # ys) (\<sigma> # zs) \<Longrightarrow> rg R (xs \<frown> (\<sigma> # ys)) (xs \<frown> (\<sigma> # zs))"
  apply (cases "lfinite xs")
  prefer 2
  apply (metis lappend_inf rg_refl)
  apply (rotate_tac 1)
proof (induct xs rule: lfinite_induct)
  case Nil
  thus ?case
    by auto
next
  case (Cons x xs)
  from Cons(2)[OF Cons(3)]
  show ?case
    apply -
    apply simp
    apply (erule rg.cases)
    apply auto
    apply (metis EqPairNR EqPairR prod.exhaust)
    apply (cases x)
    apply simp
    by (metis EqPairNR EqPairR)
qed

lemma
  assumes "xs = xs\<^sub>p \<frown> ((\<sigma>\<^sub>1,\<sigma>\<^sub>1') # (\<sigma>\<^sub>2,\<sigma>\<^sub>2') # zs)"
  and "ys = xs\<^sub>p \<frown> ((\<sigma>\<^sub>1,\<sigma>\<^sub>1') # (\<sigma>\<^sub>2,\<sigma>\<^sub>2'') # zs')"
  and "env R (xs\<^sub>p \<frown> ((\<sigma>\<^sub>1,\<sigma>\<^sub>1') # LNil))"
  and "(\<sigma>\<^sub>1',\<sigma>\<^sub>2) \<notin> R"
  shows "rg R xs ys"
  apply (simp only: assms(1) assms(2))
  apply (rule rg_lappend)
  by (metis EqPairNR assms(4))

(*
lemma
  assumes "rg R xs ys"
  shows "(\<exists>xs\<^sub>p \<sigma>\<^sub>1 \<sigma>\<^sub>1' \<sigma>\<^sub>2 \<sigma>\<^sub>2' \<sigma>\<^sub>2'' zs zs'. xs = xs\<^sub>p \<frown> ((\<sigma>\<^sub>1,\<sigma>\<^sub>1') # (\<sigma>\<^sub>2,\<sigma>\<^sub>2') # zs) \<and> ys = xs\<^sub>p \<frown> ((\<sigma>\<^sub>1,\<sigma>\<^sub>1') # (\<sigma>\<^sub>2,\<sigma>\<^sub>2'') # zs') \<and> lfinite xs\<^sub>p \<and> env R (xs\<^sub>p \<frown> ((\<sigma>\<^sub>1,\<sigma>\<^sub>1') # LNil)) \<and> (\<sigma>\<^sub>1',\<sigma>\<^sub>2) \<notin> R) \<or> xs = ys"
  sorry
*)

primrec ldropLeft_nat :: "nat \<Rightarrow> ('a + 'b) llist \<Rightarrow> ('a + 'b) llist" where
  "ldropLeft_nat 0 xs = ldropWhile is_right xs"
| "ldropLeft_nat (Suc n) xs = (case ldropWhile is_right xs of (y # ys) \<Rightarrow> ldropLeft_nat n ys | LNil \<Rightarrow> LNil)"

primrec ldropLeft :: "enat \<Rightarrow> ('a + 'b) llist \<Rightarrow> ('a + 'b) llist" where
  "ldropLeft \<infinity> xs = LNil"
| "ldropLeft (enat n) xs = ldropLeft_nat n xs"

lemma ldropLeft_nat_eq: "n = enat m \<Longrightarrow> ldropLeft n = ldropLeft_nat m"
  apply simp
  apply (rule ext)
  by simp

lemma ldropLeft_eSuc: "n \<noteq> \<infinity> \<Longrightarrow> ldropLeft (eSuc n) xs = (case ldropWhile is_right xs of (y # ys) \<Rightarrow> ldropLeft n ys | LNil \<Rightarrow> LNil)"
  apply (subgoal_tac "\<exists>m. eSuc n = enat (Suc m)")
  apply (erule exE)
  apply simp
  apply (metis eSuc_def enat.simps(4) ldropLeft_nat.simps(2) ldropLeft_nat_eq)
  by (metis eSuc_enat not_enat_eq)

primrec ltakeLeft_nat :: "nat \<Rightarrow> ('a + 'b) llist \<Rightarrow> ('a + 'b) llist" where
  "ltakeLeft_nat 0 xs = ltakeWhile is_right xs"
| "ltakeLeft_nat (Suc n) xs = ltakeWhile is_right xs \<frown> (case ldropWhile is_right xs of (y # ys) \<Rightarrow> y # ltakeLeft_nat n ys | LNil \<Rightarrow> LNil)"

primrec ltakeLeft :: "enat \<Rightarrow> ('a + 'b) llist \<Rightarrow> ('a + 'b) llist" where
  "ltakeLeft \<infinity> xs = xs"
| "ltakeLeft (enat n) xs = ltakeLeft_nat n xs"

lemma lappend_ltakeLeft_ldropLeft [simp]: "ltakeLeft n xs \<frown> ldropLeft n xs = xs"
proof (induct n, simp_all)
  fix n
  show "ltakeLeft_nat n xs \<frown> ldropLeft_nat n xs = xs"
  proof (induct n arbitrary: xs)
    case 0
    thus ?case
      by simp
  next
    case (Suc n)
    thus ?case
      apply simp
      apply (cases "ldropWhile is_right xs")
      apply simp_all
      by (metis lappend_assoc lappend_code(2) lappend_ltakeWhile_ldropWhile)
  qed
qed

lemma lset_all_rightD [dest]: "\<forall>x\<in>lset xs. is_right x \<Longrightarrow> \<ll> xs = LNil"
  by (metis (full_types) lefts_ltake_right ltakeWhile_all)

lemma lefts_ltakeLeft: "\<ll> (ltakeLeft n xs) = ltake n (\<ll> xs)"
proof (induct n, simp_all)
  fix n
  show "\<ll> (ltakeLeft_nat n xs) = ltake (enat n) (\<ll> xs)"
  proof (induct n arbitrary: xs)
    case 0
    thus ?case
      by (simp add: enat_0)
  next
    case (Suc n)
    thus ?case
      apply simp
      apply (cases "ldropWhile is_right xs")
      apply (simp_all add: eSuc_enat[symmetric])
      apply (drule lset_all_rightD)
      apply simp
      apply (subst lefts_append)
      apply (metis in_lset_ldropWhileD ldropWhile_LConsD lfinite_ltakeWhile lset_intros(1))
      apply simp
      apply (rename_tac x xs')
      apply (subgoal_tac "\<exists>x'. x = Inl x'")
      apply (erule exE)
      apply simp
      apply (subgoal_tac "\<ll> xs = x' # \<ll> xs'")
      apply simp
      apply (metis Not_is_right is_left.simps(1) ldropWhile_lfilter_LConsD lefts_LConsl lefts_def_var lfilter_LCons_found)
      by (metis ldropWhile_right_LCons llist.inject)
  qed
qed

lemma ltakeLeft_simp1:
  assumes "llength (\<ll> t) = llength xs + llength ys"
  shows "\<up> (llength (\<ll> (ltakeLeft (llength xs) t))) (xs \<frown> ys) = xs"
  apply (simp add: lefts_ltakeLeft)
  by (metis assms llength_lappend ltake_all ltake_lappend1 ltake_ltake order_refl)

lemma lfinite_ldrop_llength: "lfinite xs \<Longrightarrow> \<down> (llength xs) (xs \<frown> ys) = ys"
  by (induct xs rule: lfinite_induct) auto

lemma ltakeLeft_simp2:
  assumes "llength (\<ll> t) = llength xs + llength ys"
  and "lfinite xs"
  shows "\<down> (llength (\<ll> (ltakeLeft (llength xs) t))) (xs \<frown> ys) = ys"
  apply (simp add: lefts_ltakeLeft)
  apply (subgoal_tac "min (llength xs) (llength (\<ll> t)) = llength xs")
  apply simp
  apply (metis assms(2) lfinite_ldrop_llength)
  by (metis assms(1) enat_le_plus_same(1) min.order_iff)

lemma left_interleave_split:
  assumes "llength (\<ll> t) = llength xs + llength ys"
  and "llength (\<rr> t) = llength zs"
  and "lfinite xs"
  shows "xs \<frown> ys \<triangleright> t \<triangleleft> zs = (xs \<triangleright> ltakeLeft (llength xs) t \<triangleleft> \<up> (llength (\<rr> (ltakeLeft (llength xs) t))) zs) \<frown>
                             (ys \<triangleright> ldropLeft (llength xs) t \<triangleleft> \<down> (llength (\<rr> (ltakeLeft (llength xs) t))) zs)"
proof -
  have "xs \<frown> ys \<triangleright> t \<triangleleft> zs = xs \<frown> ys \<triangleright> ltakeLeft (llength xs) t \<frown> ldropLeft (llength xs) t \<triangleleft> zs"
    by (metis lappend_ltakeLeft_ldropLeft)
  also have "... = (xs \<triangleright> ltakeLeft (llength xs) t \<triangleleft> \<up> (llength (\<rr> (ltakeLeft (llength xs) t))) zs) \<frown>
                   (ys \<triangleright> ldropLeft (llength xs) t \<triangleleft> \<down> (llength (\<rr> (ltakeLeft (llength xs) t))) zs)"
    apply (subst interleave_append_llength)
    prefer 3
    apply (subst ltakeLeft_simp1)
    prefer 2
    apply (subst ltakeLeft_simp2)
    apply simp_all
    apply (metis assms(1))
    apply (metis assms(3))
    apply (metis assms(1))
    by (metis assms(2))
  finally show ?thesis .
qed

lemmas left_interleave_split_LNil = left_interleave_split[where xs = LNil,simplified]

lemma
  assumes "(\<sigma>\<^sub>1',\<sigma>\<^sub>2) \<notin> (R \<union> G)\<^sup>*"
  and "lset ys \<subseteq> G\<^sup>*"
  and "lfinite ys"
  shows "\<not> env (R\<^sup>*) (((\<sigma>\<^sub>1,\<sigma>\<^sub>1') # LNil) \<frown> ys \<frown> ((\<sigma>\<^sub>2,\<sigma>\<^sub>2') # LNil))"
  using assms
  apply (rotate_tac 2)
  apply (induct ys rule: lfinite.induct)
  apply simp
  apply (metis in_rtrancl_UnI)
  apply auto
  sorry

lemma "(\<tau>\<^sub>1,\<tau>\<^sub>2') \<in> G\<^sup>* \<Longrightarrow> (\<sigma>\<^sub>1',\<sigma>\<^sub>2) \<notin> (R \<union> G)\<^sup>* \<Longrightarrow> (\<sigma>\<^sub>1',\<tau>\<^sub>1) \<notin> R\<^sup>* \<or> (\<tau>\<^sub>2',\<sigma>\<^sub>2) \<notin> R\<^sup>*"
  apply auto
  by (metis Un_commute in_rtrancl_UnI rtrancl_trans)

lemma RG:
  "rg R xs xs' \<Longrightarrow> (\<exists>xs\<^sub>p \<sigma>\<^sub>1 \<sigma>\<^sub>1' \<sigma>\<^sub>2 \<sigma>\<^sub>2' \<sigma>\<^sub>2'' xs\<^sub>t xs\<^sub>t'.
                      xs = xs\<^sub>p \<frown> ((\<sigma>\<^sub>1,\<sigma>\<^sub>1') # (\<sigma>\<^sub>2,\<sigma>\<^sub>2') # xs\<^sub>t) \<and>
                      xs' = xs\<^sub>p \<frown> ((\<sigma>\<^sub>1,\<sigma>\<^sub>1') # (\<sigma>\<^sub>2,\<sigma>\<^sub>2'') # xs\<^sub>t') \<and>
                      env R (xs\<^sub>p \<frown> ((\<sigma>\<^sub>1,\<sigma>\<^sub>1') # LNil)) \<and>
                      (\<sigma>\<^sub>1',\<sigma>\<^sub>2) \<notin> R
                      \<and> lfinite xs\<^sub>p)
                    \<or> xs = xs'"
  sorry

lemma llist_lhd_ltl: "xs \<noteq> LNil \<Longrightarrow> xs = lhd xs # ltl xs"
  by (metis llist.collapse)

lemma
  assumes "zs' \<in> xs' \<sha> ys'"
  and "rg ((R \<union> G\<^sub>2)\<^sup>*) xs xs'" and "lset xs \<subseteq> G\<^sub>1\<^sup>*"
  and "rg ((R \<union> G\<^sub>1)\<^sup>*) ys ys'" and "lset ys \<subseteq> G\<^sub>2\<^sup>*"
  shows "\<exists>zs \<in> xs \<sha> ys. rg (R\<^sup>*) (lmap \<langle>id,id\<rangle> zs) (lmap \<langle>id,id\<rangle> zs')"
proof -
  from assms(1) have llength_l_zs: "llength (\<ll> zs') = llength xs'"
    by (auto simp add: tshuffle_words_def)
  from assms(1) have llength_r_zs: "llength (\<rr> zs') = llength ys'"
    by (auto simp add: tshuffle_words_def)

  from RG[OF assms(2)] and RG[OF assms(4)]
  show ?thesis
    apply -
    apply (erule disjE)+
    prefer 3
    apply (erule disjE)
    prefer 3 defer
    prefer 2
  proof -
    assume "xs = xs'" and "ys = ys'"
    thus ?thesis
      by (metis assms(1) rg_refl)
  next
    assume "\<exists>xs\<^sub>p \<sigma>\<^sub>1 \<sigma>\<^sub>1' \<sigma>\<^sub>2 \<sigma>\<^sub>2' \<sigma>\<^sub>2'' xs\<^sub>t xs\<^sub>t'.
       xs = xs\<^sub>p \<frown> ((\<sigma>\<^sub>1, \<sigma>\<^sub>1') # (\<sigma>\<^sub>2, \<sigma>\<^sub>2') # xs\<^sub>t) \<and>
       xs' = xs\<^sub>p \<frown> ((\<sigma>\<^sub>1, \<sigma>\<^sub>1') # (\<sigma>\<^sub>2, \<sigma>\<^sub>2'') # xs\<^sub>t') \<and>
       env ((R \<union> G\<^sub>2)\<^sup>*) (xs\<^sub>p \<frown> ((\<sigma>\<^sub>1, \<sigma>\<^sub>1') # LNil)) \<and>
       (\<sigma>\<^sub>1', \<sigma>\<^sub>2) \<notin> (R \<union> G\<^sub>2)\<^sup>* \<and>
       lfinite xs\<^sub>p"
    and ys_same: "ys = ys'"

    then obtain xs\<^sub>p \<sigma>\<^sub>1 \<sigma>\<^sub>1' \<sigma>\<^sub>2 \<sigma>\<^sub>2' \<sigma>\<^sub>2'' xs\<^sub>t xs\<^sub>t'
    where xs_split: "xs = xs\<^sub>p \<frown> ((\<sigma>\<^sub>1,\<sigma>\<^sub>1') # (\<sigma>\<^sub>2,\<sigma>\<^sub>2') # xs\<^sub>t)"
    and xs'_split: "xs' = xs\<^sub>p \<frown> ((\<sigma>\<^sub>1,\<sigma>\<^sub>1') # (\<sigma>\<^sub>2,\<sigma>\<^sub>2'') # xs\<^sub>t')"
    and xs\<^sub>p_env: "env ((R \<union> G\<^sub>2)\<^sup>*) (xs\<^sub>p \<frown> ((\<sigma>\<^sub>1,\<sigma>\<^sub>1') # LNil))"
    and xs\<^sub>p_fin: "lfinite xs\<^sub>p"
    and bad_env: "(\<sigma>\<^sub>1',\<sigma>\<^sub>2) \<notin> (R \<union> G\<^sub>2)\<^sup>*"
      by auto

    from assms(1) and xs\<^sub>p_fin have "llength (\<ll> zs') > llength xs\<^sub>p"
      by (simp add: tshuffle_words_def xs'_split) (metis lfinite_llength_enat)
    from xs\<^sub>p_fin and this have [simp]: "lhd (ldropLeft (llength xs\<^sub>p) (traj zs')) = Inl ()"
      apply (induct xs\<^sub>p arbitrary: zs' rule: lfinite_induct)
      apply (simp add: enat_0[symmetric])
      apply (subgoal_tac "\<ll> zs' \<noteq> LNil")
      apply (metis ldropWhile_eq_LNil_iff ldropWhile_right_traj ldropWhile_rights_not_LNil lhd_LCons lset_all_rightD traj_not_LNil)
      apply (metis llength_LNil not_iless0)
      apply simp
      apply (subst ldropLeft_eSuc)
      apply (metis eSuc_infinity enat_ord_simps(6))
      apply (subgoal_tac "ldropWhile is_right (traj zs') = Inl () # ltl (ldropWhile is_right (traj zs'))")
      apply simp
      apply (subgoal_tac "llength xs < llength (\<ll> (ltl (ldropWhile is_right zs')))")
      apply blast
      apply (subgoal_tac "eSuc (llength xs) < llength (\<ll> (ldropWhile is_right zs'))")
      defer
      apply (subgoal_tac "eSuc (llength xs) < llength (\<ll> (ltakeWhile is_right zs' \<frown> ldropWhile is_right zs'))")
      apply simp
      apply (metis lappend_ltakeWhile_ldropWhile)
      apply simp
      apply (metis i0_less ldropWhile_eq_LNil_iff ldropWhile_right_traj ldropWhile_rights_not_LNil less_asym llength_LNil lset_all_rightD ltl_traj traj_not_LNil)
      apply (subgoal_tac "\<exists>z. ldropWhile is_right zs' = Inl z # ltl (ldropWhile is_right zs')")
      apply (erule exE)
      apply (metis eSuc_mono lefts_LConsl llength_LCons)
      by (metis ldropWhile_right_LCons llist.collapse llist.distinct(1) traj_not_LNil)

    obtain ys\<^sub>1 and ys\<^sub>2
    where ys\<^sub>1_def: "ys\<^sub>1 = \<up> (llength (\<rr> (ltakeLeft (llength xs\<^sub>p) (traj zs')))) ys"
    and ys\<^sub>2_def: "ys\<^sub>2 = \<down> (llength (\<rr> (ltakeLeft (llength xs\<^sub>p) (traj zs')))) ys"
    and ys_split: "ys = ys\<^sub>1 \<frown> ys\<^sub>2"
      by (metis lappend_ltake_ldrop)

    from ys_same xs'_split and assms(1)
    have "zs' = xs\<^sub>p \<frown> ((\<sigma>\<^sub>1,\<sigma>\<^sub>1') # (\<sigma>\<^sub>2,\<sigma>\<^sub>2'') # xs\<^sub>t') \<triangleright> traj zs' \<triangleleft> ys"
      by (auto simp add: tshuffle_words_def) (metis reinterleave)
    also have "... = (xs\<^sub>p \<triangleright> ltakeLeft (llength xs\<^sub>p) (traj zs') \<triangleleft> ys\<^sub>1) \<frown>
                     ((\<sigma>\<^sub>1,\<sigma>\<^sub>1') # (\<sigma>\<^sub>2,\<sigma>\<^sub>2'') # xs\<^sub>t' \<triangleright> ldropLeft (llength xs\<^sub>p) (traj zs') \<triangleleft> ys\<^sub>2)"
      by (subst left_interleave_split) (simp_all add: ys\<^sub>1_def ys\<^sub>2_def xs\<^sub>p_fin llength_l_zs xs'_split llength_r_zs ys_same)
    also have "... = (xs\<^sub>p \<triangleright> ltakeLeft (llength xs\<^sub>p) (traj zs') \<triangleleft> ys\<^sub>1) \<frown>
                     LCons (Inl (\<sigma>\<^sub>1,\<sigma>\<^sub>1')) LNil \<frown>
                     ((\<sigma>\<^sub>2,\<sigma>\<^sub>2'') # xs\<^sub>t' \<triangleright> ltl (ldropLeft (llength xs\<^sub>p) (traj zs')) \<triangleleft> ys\<^sub>2)"
      apply (subst llist_lhd_ltl[where xs = "ldropLeft (llength xs\<^sub>p) (traj zs')"])
      defer
      apply (simp add: interleave_left)
      apply (metis LCons_lappend_LNil lappend_assoc)
      sorry
    also have "... = (xs\<^sub>p \<triangleright> ltakeLeft (llength xs\<^sub>p) (traj zs') \<triangleleft> ys\<^sub>1) \<frown>
                     (Inl (\<sigma>\<^sub>1, \<sigma>\<^sub>1') # LNil) \<frown>
                     (LNil \<triangleright> ltakeWhile is_right (ltl (ldropLeft (llength xs\<^sub>p) (traj zs'))) \<triangleleft> \<up> (llength (\<rr> (ltakeWhile is_right (ltl (ldropLeft (llength xs\<^sub>p) (traj zs')))))) ys\<^sub>2) \<frown>
                     ((\<sigma>\<^sub>2, \<sigma>\<^sub>2'') # xs\<^sub>t' \<triangleright> ldropWhile is_right (ltl (ldropLeft (llength xs\<^sub>p) (traj zs'))) \<triangleleft> \<down> (llength (\<rr> (ltakeWhile is_right (ltl (ldropLeft (llength xs\<^sub>p) (traj zs')))))) ys\<^sub>2)"
      apply (subst left_interleave_split_LNil) back
      prefer 3
      apply (simp add: enat_0[symmetric] lappend_assoc)
      sorry

    thus ?thesis sorry
qed
  

lemma "(R \<union> G\<^sub>2 \<leadsto> prog G\<^sub>1 \<inter> X) \<parallel> (R \<union> G\<^sub>1 \<leadsto> prog G\<^sub>2 \<inter> Y) \<subseteq> R \<leadsto> (prog G\<^sub>1 \<inter> X) \<parallel> (prog G\<^sub>2 \<inter> Y)"
  apply (auto simp add: RG_def shuffle_def)
   sorry
  also have "... = (xs\<^sub>p \<triangleright> ltakeLeft (llength xs\<^sub>p) (traj zs') \<triangleleft> ys\<^sub>1) \<frown>
                   LCons (Inl (\<sigma>\<^sub>1,\<sigma>\<^sub>1')) LNil \<frown>
                   ((LNil \<triangleright> ltakeLeft 0 (ltl (ldropLeft (llength xs\<^sub>p) (traj zs'))) \<triangleleft> \<up> (llength (\<rr> (ltakeLeft 0 (ltl (ldropLeft (llength xs\<^sub>p) (traj zs')))))) ys\<^sub>2) \<frown>
                   ((\<sigma>\<^sub>2, \<sigma>\<^sub>2'') # xs\<^sub>t' \<triangleright> ldropLeft 0 (ltl (ldropLeft (llength xs\<^sub>p) (traj zs'))) \<triangleleft> \<down> (llength (\<rr> (ltakeLeft 0 (ltl (ldropLeft (llength xs\<^sub>p) (traj zs')))))) ys\<^sub>2))"
    apply (subst left_interleave_split_LNil) back
        apply (rename_tac xs' ys' zs xs ys)
  apply (rule_tac x = "lmap \<langle>id,id\<rangle> ` (xs \<sha> ys)" in exI)
  apply (intro conjI)
  apply (rule_tac x = xs in exI)
  apply (rule_tac x = ys in exI)
  apply simp
  nitpick

lemma rg_lprefix: "(\<forall>xs'. lfinite xs' \<and> lprefix xs' xs \<and> env (R\<^sup>*) xs' \<longrightarrow> lset xs' \<subseteq> G\<^sup>*) \<Longrightarrow> rg (R\<^sup>*) (G\<^sup>*) xs" 
proof -
  assume "(\<forall>xs'. lfinite xs' \<and> lprefix xs' xs \<and> env (R\<^sup>*) xs' \<longrightarrow> lset xs' \<subseteq> G\<^sup>*)"
  thus "rg (R\<^sup>*) (G\<^sup>*) xs"
  proof coinduct
    case (rg t)
    show ?case
    proof (cases t)
      assume "t = LNil"
      thus ?case by simp
    next
      fix \<sigma> t'
      assume [simp]: "t = LCons \<sigma> t'"
      hence "?EqSingle \<or> ?EqPairG \<or> ?EqPairNG"
      proof (cases t')
        assume "t' = LNil"
        from this and rg have "?EqSingle"
          by auto (metis env.EqSingle lfinite_LCons lfinite_LNil lprefix_refl lset_intros(1) set_rev_mp)
        thus "?EqSingle \<or> ?EqPairG \<or> ?EqPairNG"
          by simp
      next
        fix \<sigma>' t''
        assume [simp]: "t' = LCons \<sigma>' t''"
        from this and rg have "?EqPairG \<or> ?EqPairNG"
        proof (cases "(snd \<sigma>, fst \<sigma>') \<in> R\<^sup>*")
          assume "(snd \<sigma>, fst \<sigma>') \<in> R\<^sup>*"
          from this and rg have "?EqPairG"
            apply simp
            apply (intro conjI)
            apply (erule_tac x = "LCons \<sigma> (LCons \<sigma>' LNil)" in allE)
            apply simp
            apply (intro disjI1 allI impI)
            apply (erule conjE)
            apply (erule_tac x = "LCons \<sigma> xs'" in allE)
            apply (subgoal_tac "(\<exists>\<sigma>'' xs''. xs' = LCons \<sigma>'' xs'') \<or> xs' = LNil")
            apply (erule disjE)
            apply (erule exE)+
            apply simp
            apply (erule impE)
            apply (metis env.EqPair)
            by auto
          thus "?EqPairG \<or> ?EqPairNG"
            by blast
        next
          assume "(snd \<sigma>, fst \<sigma>') \<notin> R\<^sup>*"
          from this and rg have "?EqPairNG"
            apply simp
            apply (erule_tac x = "LCons \<sigma> LNil" in allE)
            by simp
          thus "?EqPairG \<or> ?EqPairNG"
            by blast
        qed
        thus "?EqSingle \<or> ?EqPairG \<or> ?EqPairNG"
          by simp
      qed
      thus ?case by simp
    qed
  qed
qed

lemma rg_lprefix2: "lfinite xs' \<Longrightarrow> rg (R\<^sup>*) (G\<^sup>*) xs \<Longrightarrow> lprefix xs' xs \<Longrightarrow> env (R\<^sup>*) xs' \<Longrightarrow> lset xs' \<subseteq> G\<^sup>*"
proof (induct xs' arbitrary: xs rule: lfinite_induct)
  case Nil
  thus ?case
    by auto
next
  case (Cons x xs')
  thus ?case
    apply (cases xs)
    apply simp
    apply simp
    apply auto
    apply (metis rg_hd)
    apply (rename_tac a b xs a' b')
    apply (subgoal_tac "(\<exists>y ys. xs = LCons y ys) \<or> xs = LNil")
    apply (erule disjE)
    apply (erule exE)+
    apply simp
    apply (drule rg_LCons2D)
    apply simp
    apply (cases xs')
    apply simp
    apply simp
    apply (metis LCons_lprefix_conv env_LConsD env_LConsE in_mono snd_conv)
    by auto
qed

lemma rg_lprefix_eq: "(\<forall>xs'. lfinite xs' \<and> lprefix xs' xs \<and> env (R\<^sup>*) xs' \<longrightarrow> lset xs' \<subseteq> G\<^sup>*) \<longleftrightarrow> rg (R\<^sup>*) (G\<^sup>*) xs"
  by (metis rg_lprefix rg_lprefix2)

lemma RG_lprefix: "xs \<in> R \<leadsto> G \<longleftrightarrow> (\<forall>xs'. lfinite xs' \<and> lprefix xs' xs \<and> env (R\<^sup>*) xs' \<longrightarrow> lset xs' \<subseteq> G\<^sup>*)"
  by (metis RG_def mem_Collect_eq rg_lprefix_eq)

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

definition Rely :: "'a rel \<Rightarrow> ('a \<times> 'a) lan \<Rightarrow> ('a \<times> 'a) lan" (infixr "\<Colon>" 52) where
  "R \<Colon> X \<equiv> X \<inter> Env (R\<^sup>*)"

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

lemma env_InterE: "env (\<Inter>\<RR>) x \<Longrightarrow> R \<in> \<RR> \<Longrightarrow> env R x"
proof -
  assume "env (\<Inter>\<RR>) x" and "R \<in> \<RR>"
  hence "env (\<Inter>\<RR>) x \<and> R \<in> \<RR>" by simp
  thus "env R x"
  proof coinduct
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
        have "?EqPair"
          apply auto
          apply (drule env_LConsE)
          by auto
        thus "?EqSingle \<or> ?EqPair"
          by auto
      qed
      thus ?case by simp
    qed
  qed
qed

lemma env_InterE_star: "env ((\<Inter>{R\<^sup>* |R. R \<in> \<RR>})\<^sup>*) x \<Longrightarrow> R \<in> \<RR> \<Longrightarrow> env (R\<^sup>*) x"
proof -
  assume "env ((\<Inter>{R\<^sup>* |R. R \<in> \<RR>})\<^sup>*) x" and "R \<in> \<RR>"
  hence "env ((\<Inter>{R\<^sup>* |R. R \<in> \<RR>})\<^sup>*) x \<and> R \<in> \<RR>" by simp
  thus "env (R\<^sup>*) x"
  proof coinduct
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
        have "?EqPair"
          apply auto
          apply (drule env_LConsE)
          apply (erule set_rev_mp)
          apply (subst rtrancl_idemp[symmetric]) back back
          apply (rule rtrancl_mono)
          by auto
        thus "?EqSingle \<or> ?EqPair"
          by auto
      qed
      thus ?case by simp
    qed
  qed
qed

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

lemma env_InterI [intro]: "(\<And>R. R \<in> \<RR> \<Longrightarrow> env R t) \<Longrightarrow> env (\<Inter>\<RR>) t"
proof -
  assume "(\<And>R. R \<in> \<RR> \<Longrightarrow> env R t)"
  hence "(\<forall>R. R \<in> \<RR> \<longrightarrow> env R t)"
    by auto
  thus "env (\<Inter>\<RR>) t"
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

lemma Rely_continuous: "R \<Colon> (\<Union>\<XX>) = \<Union>{R \<Colon> X |X. X \<in> \<XX>}"
  by (auto simp add: Rely_def)

lemma Rely_inter [simp]: "R \<Colon> X \<inter> Y = (R \<Colon> X) \<inter> (R \<Colon> Y)"
  by (metis Rely_def Int_assoc inf_commute inf_left_idem)

lemma Rely_union [simp]: "R \<Colon> X \<union> Y = (R \<Colon> X) \<union> (R \<Colon> Y)"
  by (auto simp add: Rely_def)

lemma Rely_coextensive [intro!]: "R \<Colon> X \<subseteq> X"
  by (auto simp add: Rely_def)

lemma Rely_iso [intro]: "X \<subseteq> Y \<Longrightarrow> R \<Colon> X \<subseteq> R \<Colon> Y"
  by (auto simp add: Rely_def)

lemma Rely_idem [simp]: "R \<inter> S \<Colon> X \<subseteq> R \<Colon> S \<Colon> X"
  apply (auto simp add: Rely_def Env_def)
  apply (metis env_interE1 inf_absorb1 inf_sup_ord(2) rtrancl_mono)
  by (metis env_interE2 inf_absorb2 inf_sup_ord(1) rtrancl_mono)

lemma Rely_inter2: "R\<^sup>* \<inter> S\<^sup>* \<Colon> X = (R \<Colon> X) \<inter> (S \<Colon> X)"
  apply (auto simp add: Rely_def Env_def)
  apply (metis env_interE2 inf.cobounded1 inf_absorb2 rtrancl_subset_rtrancl)
  apply (erule rev_mp)+
  apply (subst Int_commute)
  apply (intro impI)
  apply (metis env_interE2 inf.cobounded1 inf_absorb2 rtrancl_subset_rtrancl)
  by (metis env_interE1 env_interI le_iff_inf r_into_rtrancl subsetI)

lemma "\<Sqinter>{R\<^sup>* |R. R \<in> \<RR>} \<Colon> X \<subseteq> \<Sqinter>{R \<Colon> X |R. R \<in> \<RR>}"
  apply (auto simp add: Rely_def Env_def)
  apply (rule env_InterE_star)
  by simp_all

lemma Rely_comm: "R \<Colon> S \<Colon> X = S \<Colon> R \<Colon> X"
  by (auto simp add: Rely_def)

lemma Rely_rtrancl [simp]: "S\<^sup>* \<Colon> X = S \<Colon> X"
  by (metis Rely_def rtrancl_idemp)

lemma "R\<^sup>* \<inter> S\<^sup>* \<Colon> X = R \<Colon> S \<Colon> X"
  apply (intro antisym)
  apply (subst Rely_rtrancl[symmetric]) back back
  apply (subst Rely_rtrancl[symmetric]) back
  apply (rule Rely_idem)
  apply (auto simp add: Rely_def Env_def)
  by (metis env_interE1 env_interI inf.orderE r_into_rtrancl subsetI)

lemma Rely_zero [simp]: "R \<Colon> {} = {}"
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

lemma Rely_top: "UNIV \<Colon> X = X"
  by (auto simp add: Rely_def Env_def)

definition guar :: "('a \<times> 'a) lan \<Rightarrow> 'a rel" where
  "guar X \<equiv> (\<Union>(lset ` X))\<^sup>*"

lemma guar_iso: "x \<le> y \<Longrightarrow> guar x \<le> guar y"
  apply (simp add: guar_def)
  apply (rule rtrancl_mono)
  by auto

definition prog :: "'a rel \<Rightarrow> ('a \<times> 'a) lan" where
  "prog X = {xs. lset xs \<subseteq> X\<^sup>*}"

lemma guar_galois: "guar X \<subseteq> (Y\<^sup>*) \<longleftrightarrow> X \<subseteq> prog Y"
  apply (auto simp add: guar_def prog_def)
  apply (erule rtrancl.induct)
  apply auto
  by (metis in_mono mem_Collect_eq rtrancl_trans)

lemma guar_prog: "guar (prog g) \<le> g\<^sup>*"
  apply (auto simp add: guar_def prog_def)
  by (metis (lifting) UN_subset_iff mem_Collect_eq rtrancl_subset_rtrancl set_rev_mp)

lemma Rely_jp: "join_preserving (\<lambda>x. r \<Colon> x)"
  by (auto simp add: join_preserving_def Rely_continuous)

lemma lemma1: "x \<le> r \<Colon> g \<Longrightarrow> r \<Colon> x \<le> g"
  by (auto simp add: Rely_def Env_def)

lemma Rely_iso2: "r1\<^sup>* \<le> r2\<^sup>* \<Longrightarrow> r1 \<Colon> x \<le> r2 \<Colon> x"
  sorry

lemma prog_lset: "xs \<in> prog g \<longleftrightarrow> lset xs \<subseteq> g\<^sup>*"
  by (auto simp add: prog_def)

lemma test1: "r \<Colon> x \<le> prog g \<longleftrightarrow> (\<forall>xs \<in> x. env (r\<^sup>*) xs \<longrightarrow> lset xs \<subseteq> g\<^sup>*)"
  by (auto simp add: subset_eq Rely_def Env_def prog_lset)

(*
lemma rg_galois1: "guar (r \<Colon> x) \<subseteq> g\<^sup>* \<Longrightarrow> x \<subseteq> r \<leadsto> g"
  apply (erule rev_mp)
  apply (subst guar_galois)
  apply (subst test2)
  apply (auto simp add: RG_def)
  by (metis Rely_coextensive Rely_iso2 dual_order.trans not_lfinite_lprefix_conv_eq order_refl rg_lprefix test1)
*)

lemma subsetD2: "X \<subseteq> Y \<Longrightarrow> (\<forall>z. z \<in> X \<longrightarrow> z \<in> Y)"
  by auto

lemma contrp: "(\<not> P \<longrightarrow> Q) \<longleftrightarrow> (\<not> Q \<longrightarrow> P)"
  by blast

lemma env_lappend1: "env R (xs \<frown> ys) \<Longrightarrow> env R xs"
  sorry

lemma environment_var': "\<not> env R xs \<longrightarrow> (\<exists>ys \<sigma> \<sigma>' zs. lfinite ys \<and> env R (ys \<frown> LCons \<sigma> LNil) \<and> xs = ys \<frown> LCons \<sigma> (LCons \<sigma>' zs) \<and> (snd \<sigma>, fst \<sigma>') \<notin> R)"
proof (subst contrp, auto)
  assume "\<forall>ys. lfinite ys \<longrightarrow>
               (\<forall>a b. env R (ys \<frown> LCons (a, b) LNil) \<longrightarrow>
                      (\<forall>a'. (\<forall>b' zs. xs \<noteq> ys \<frown> LCons (a, b) (LCons (a', b') zs)) \<or> (b, a') \<in> R))"
  thus "env R xs"
  proof coinduct
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
        have "?EqPair"
          apply (rule_tac x = \<sigma> in exI)
          apply (rule_tac x = \<sigma>' in exI)
          apply (rule_tac x = t'' in exI)
          apply (intro conjI)
          apply simp
          apply simp
          apply (erule_tac x = LNil in allE)
          apply simp
          apply (metis surjective_pairing)
          apply (subgoal_tac "(snd \<sigma>, fst \<sigma>') \<in> R")
          defer
          apply simp
          apply (erule_tac x = LNil in allE)
          apply simp
          apply (metis surjective_pairing)
          apply auto
          apply (erule_tac x = "LCons \<sigma> ys" in allE)
          apply (erule impE)
          apply simp
          apply (erule_tac x = a in allE)
          apply (erule_tac x = b in allE)
          apply (erule impE)
          apply simp
          apply (subgoal_tac "(\<exists>\<sigma>'' ys'. ys = LCons \<sigma>'' ys') \<or> ys = LNil")
          apply (erule disjE)
          apply (erule exE)+
          apply simp
          apply (metis env.EqPair)
          apply simp
          apply (metis neq_LNil_conv)
          apply (erule_tac x = a' in allE)
          apply (erule disjE)
          apply (metis lappend_code(2))
          by blast
        thus "?EqSingle \<or> ?EqPair"
          by auto
      qed
      thus ?case by simp
    qed
  qed
qed

lemma environment_var: "\<not> env R xs \<Longrightarrow> (\<exists>ys \<sigma> \<sigma>' zs. lfinite ys \<and> env R (ys \<frown> LCons \<sigma> LNil) \<and> xs = ys \<frown> LCons \<sigma> (LCons \<sigma>' zs) \<and> (snd \<sigma>, fst \<sigma>') \<notin> R)"
  by (metis environment_var')

lemma environment': "\<not> env R xs \<longrightarrow> (\<exists>ys \<sigma> \<sigma>' zs. lfinite ys \<and> xs = ys \<frown> LCons \<sigma> (LCons \<sigma>' zs) \<and> (snd \<sigma>, fst \<sigma>') \<notin> R)"
proof (subst contrp, auto)
  assume "\<forall>ys. lfinite ys \<longrightarrow> (\<forall>a b a'. (\<forall>b' zs. xs \<noteq> ys \<frown> LCons (a, b) (LCons (a', b') zs)) \<or> (b, a') \<in> R)"
  thus "env R xs"
  proof coinduct
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
        have "?EqPair"
          apply auto
          apply (metis lappend_code(1) lfinite_code(1) surjective_pairing)
          by (metis lappend_code(2) lfinite_LCons)
        thus "?EqSingle \<or> ?EqPair"
          by auto
      qed
      thus ?case by simp
    qed
  qed
qed

lemma environment: "\<not> env R xs \<Longrightarrow> (\<exists>ys \<sigma> \<sigma>' zs. lfinite ys \<and> xs = ys \<frown> LCons \<sigma> (LCons \<sigma>' zs) \<and> (snd \<sigma>, fst \<sigma>') \<notin> R)"
  by (metis environment')

lemma shuffle_interleaving: "zs \<in> xs \<sha> ys \<Longrightarrow> zs = xs \<triangleright> traj zs \<triangleleft> ys"
  by (auto simp add: tshuffle_words_def reinterleave)

lemma llength_lr': "llength (\<rr> xs) = llength (\<rr> ys) \<Longrightarrow> llength (\<ll> xs) = llength (\<ll> ys) \<Longrightarrow> llength xs = llength ys"
  by (auto simp add: lefts_def rights_def) (metis llength_lr)

lemma lset_ltakeD[dest]:  "x \<in> lset (\<up> n xs) \<Longrightarrow> x \<in> lset xs"
  by (metis in_mono lset_ltake)

lemma lset_repeatD[dest!]: "x \<in> lset (repeat y) \<Longrightarrow> x = y"
  by (metis (mono_tags) Aczel.lnth_repeat Coinductive_List.lset_into_lsetp lmember_code(1) lmember_code(2) lset_ex_lnth lset_lmember lsetp_into_lset)

lemma [simp]: "\<rr> (\<up> n (repeat (Inl ()))) = LNil"
  by (auto simp add: rights_def)

lemma enat_0_le: "enat 0 < n \<Longrightarrow> (\<exists>m. n = eSuc m)"
  by (metis co.enat.exhaust i0_less zero_enat_def)

lemma [simp]: "\<up> (eSuc n) (repeat x) = LCons x (\<up> n (repeat x))"
  by (metis iterates_eq_LNil lhd_iterates llist.collapse ltake_eSuc_LCons ltl_iterates)

lemma lnth_ltake_repeat: "enat m < n \<Longrightarrow> lnth (\<up> n (repeat x)) m = x"
  apply (induct m)
  apply (drule enat_0_le)
  apply (erule exE)
  apply simp
  by (metis Aczel.lnth_repeat lnth_ltake)

lemma enat_le_llength: "enat n < llength t \<Longrightarrow> (\<exists>t' t''. t = LCons t' t'')"  
  by (cases t) auto

lemma lnth_no_rights: "\<rr> t = LNil \<Longrightarrow> enat n < llength t \<Longrightarrow> lnth t n = Inl ()"
  apply (induct n arbitrary: t)
  apply (simp add: rights_def)
  apply (drule enat_le_llength)
  apply (erule exE)+
  apply simp
  apply (metis (full_types) is_left.simps(2) obj_sumE unit.exhaust)
  apply (frule enat_le_llength)
  apply (erule exE)+
  apply simp
  apply (subgoal_tac "enat n < llength t''")
  apply (subgoal_tac "\<rr> t'' = LNil")
  apply auto
  apply (simp add: rights_def)
  apply (metis lfilter_empty_conv llist.distinct(1) not_is_right)
  by (metis Suc_ile_eq)

lemma lfilter_repeat: "P x \<Longrightarrow> lfilter P (repeat x) = repeat x"
  by (metis (full_types) lfilter_all lset_ltakeWhileD ltakeWhile_repeat)

lemma [simp]: "lfilter is_left (repeat (Inl ())) = repeat (Inl ())"
  by (metis is_left.simps(1) lfilter_repeat)

lemma [simp]: "llength (lfilter is_left (\<up> (enat n) (repeat (Inl ())))) = enat n"
  apply (induct n)
  apply (simp add: enat_0)
  by (simp add: eSuc_enat[symmetric])

lemma traj_all_lefts: "llength (\<ll> t) = n \<Longrightarrow> llength (\<rr> t) = 0 \<Longrightarrow> t = \<up> n (repeat (Inl ()))"
  apply (subst llist_all2_eq[symmetric])
  apply (rule llist_all2_all_lnthI)
  apply (rule llength_lr')
  apply simp
  defer
  apply (subst lnth_ltake_repeat)
  apply (subgoal_tac "llength t = n")
  apply (rotate_tac 3)
  apply (erule rev_mp)
  apply (subst llength_lr)
  apply (simp add: lefts_def rights_def)
  apply (simp add: lefts_def rights_def)
  apply (rule lnth_no_rights)
  apply simp_all
  apply (simp add: lefts_def rights_def)
  apply (cases n)
  by simp_all

lemma interleave_only_left [simp]: "xs \<triangleright> \<up> (llength xs) (repeat (Inl ())) \<triangleleft> LNil = lmap Inl xs"
  sorry

lemma [simp]: "min (n::enat) (n + m) = n"
proof (cases n, auto)
  fix n
  show "min (enat n) (enat n + m) = enat n"
    by (induct n, auto simp add: enat_0 eSuc_enat[symmetric], metis eSuc_plus min_eSuc_eSuc)
qed

lemma interleave_left_lappend:
  assumes "lfinite as" and "xs = as \<frown> bs \<triangleright> t \<triangleleft> cs"
  and "llength (\<ll> t) = llength as + llength bs" and "llength (\<rr> t) = llength cs"
  shows "\<exists>cs' cs''. lfinite cs' \<and> cs = cs' \<frown> cs'' \<and> xs = (as \<triangleright> \<up> (llength as + llength cs') t \<triangleleft> cs') \<frown> (bs \<triangleright> LCons (Inl ()) (\<down> (eSuc (llength as + llength cs')) t) \<triangleleft> cs'')"
  sorry
(*
proof (cases "cs = LNil")
  assume cs_LNil [simp]: "cs = LNil"

  from assms(4) have t_def: "t = \<up> (llength as + llength bs) (repeat (Inl ()))"
    by (intro traj_all_lefts assms(3)) simp

  have "xs = as \<frown> bs \<triangleright> t \<triangleleft> LNil"
    by (metis assms(2) cs_LNil)
  also have "... = as \<frown> bs \<triangleright> \<up> (llength as + llength bs) (repeat (Inl ())) \<triangleleft> LNil"
    by (metis t_def)
  also have "... = as \<frown> bs \<triangleright> \<up> (llength (as \<frown> bs)) (repeat (Inl ())) \<triangleleft> LNil"
    by (metis llength_lappend)
  also have "... = lmap Inl (as \<frown> bs)"
    by (simp only: interleave_only_left)
  also have "... = lmap Inl as \<frown> lmap Inl bs"
    by (metis lmap_lappend_distrib)
  also have "... = (as \<triangleright> \<up> (llength as) (repeat (Inl ())) \<triangleleft> LNil) \<frown> (bs \<triangleright> \<up> (llength bs) (repeat (Inl ())) \<triangleleft> LNil)"
    by (simp only: interleave_only_left)
  finally show ?thesis
    apply (rule_tac x = LNil in exI)
    apply (rule_tac x = LNil in exI)
    apply (intro conjI)
    apply simp
    apply simp
    apply (erule ssubst)
    apply (rule arg_cong2) back back
    apply (simp add: t_def)
    apply (rule arg_cong2) back back
    apply auto
    apply (simp add: t_def)
    sorry

  apply (induct as rule: lfinite_induct)
  apply (rule_tac x = "\<up> (llength (ltakeWhile is_right t)) cs" in exI)
  apply (rule_tac x = "\<down> (llength (ltakeWhile is_right t)) cs" in exI)
  apply (intro conjI)
  apply simp
  apply (rule disjI2)
  defer
  apply (metis lappend_ltake_ldrop)
  sorry
*)

lemma shuffle_llength: "zs \<in> xs \<sha> ys \<Longrightarrow> llength zs = llength xs + llength ys"
  by (auto simp add: tshuffle_words_def lefts_def rights_def) (metis llength_lr)

lemma "lfinite xs \<Longrightarrow> env R (xs \<frown> ys) \<Longrightarrow> env R ys"
  by (induct rule: lfinite.induct) auto

lemma gap_environment: "lfinite xs \<Longrightarrow> env R (LCons \<sigma> LNil \<frown> xs \<frown> LCons \<sigma>' LNil) \<Longrightarrow> (snd \<sigma>, fst \<sigma>') \<in> (R \<union> lset xs)\<^sup>*"
proof (induct arbitrary: \<sigma> rule: lfinite.induct)
  case lfinite_LNil thus ?case by simp
next
  case (lfinite_LConsI xs x)
  hence "env R (LCons \<sigma> (LCons x (xs \<frown> LCons \<sigma>' LNil)))"
    by (metis LCons_lappend_LNil lappend_code(2))
  hence "env R (LCons x (xs \<frown> LCons \<sigma>' LNil))" and "(snd \<sigma>, fst x) \<in> R"
    by - (metis env_LConsD, metis env_LConsE)
  hence "env R (LCons x LNil \<frown> xs \<frown> LCons \<sigma>' LNil)"
    by (metis LCons_lappend_LNil lappend_code(2))
  hence "(snd x, fst \<sigma>') \<in> (R \<union> lset xs)\<^sup>*"
    by (metis lfinite_LConsI.hyps(2))
  hence "(snd x, fst \<sigma>') \<in> (R \<union> lset (LCons x xs))\<^sup>*"
    by (rule set_rev_mp) (auto intro!: rtrancl_mono)
  moreover have "(fst x, snd x) \<in> lset (LCons x xs)"
    by (metis lset_intros(1) surjective_pairing)
  ultimately show ?case using `(snd \<sigma>, fst x) \<in> R`
    apply -
    apply (rule converse_rtrancl_into_rtrancl[where b = "fst x"])
    apply simp
    apply (rule converse_rtrancl_into_rtrancl[where b = "snd x"])
    by simp_all
qed

lemma lfinite_ltake_llength: "lfinite xs \<Longrightarrow> lfinite (\<up> (llength xs) ys)"
  by (metis infinity_ileE lfinite_llength_enat llength_ltake min_max.inf_le1 not_lfinite_llength)

lemma shuffle_env:
  assumes "zs \<in> xs \<sha> ys"
  and "env R (lmap \<langle>id,id\<rangle> zs)"
  shows "env ((R \<union> lset ys)\<^sup>*) xs"
proof (rule classical)
  assume "\<not> env ((R \<union> lset ys)\<^sup>*) xs"
  hence "\<exists>as \<sigma> \<sigma>' bs. lfinite as \<and> xs = as \<frown> LCons \<sigma> (LCons \<sigma>' bs) \<and> (snd \<sigma>, fst \<sigma>') \<notin> (R \<union> lset ys)\<^sup>*"
    by (metis environment)
  then obtain as and \<sigma> and \<sigma>' and bs
  where lfinite_as: "lfinite as" and xs_split: "xs = as \<frown> LCons \<sigma> (LCons \<sigma>' bs)" and "(snd \<sigma>, fst \<sigma>') \<notin> (R \<union> lset ys)\<^sup>*"
    by auto

  from assms(1)
  have zs_llen: "llength (\<ll> zs) = llength xs"
    by (auto simp add: tshuffle_words_def)

  have zs_interleave: "zs = as \<frown> LCons \<sigma> (LCons \<sigma>' bs) \<triangleright> traj zs \<triangleleft> ys"
    by (metis assms(1) shuffle_interleaving xs_split)
  have traj_zs_llen: "llength (\<ll> (traj zs)) = llength as + llength (LCons \<sigma> (LCons \<sigma>' bs))"
    by (simp add: zs_llen xs_split)
  have traj_zs_rlen: "llength (\<rr> (traj zs)) = llength ys"
    using assms(1) by (simp add: tshuffle_words_def) 

  from interleave_left_lappend[OF lfinite_as zs_interleave traj_zs_llen traj_zs_rlen]
  obtain ys' and ys''
  where "lfinite ys'" and ys_split: "ys = ys' \<frown> ys''"
  and zs_prefix: "zs = (as \<triangleright> \<up> (llength as + llength ys') (traj zs) \<triangleleft> ys') \<frown> (LCons \<sigma> (LCons \<sigma>' bs) \<triangleright> LCons (Inl ()) (\<down> (eSuc (llength as + llength ys')) (traj zs)) \<triangleleft> ys'')"
    by auto

  let ?prefix = "as \<triangleright> \<up> (llength as + llength ys') (traj zs) \<triangleleft> ys'"
  let ?t = "\<down> (eSuc (llength as + llength ys')) (traj zs)"

  have "zs = ?prefix \<frown> (LCons \<sigma> (LCons \<sigma>' bs) \<triangleright> LCons (Inl ()) ?t \<triangleleft> ys'')"
    by (metis zs_prefix)
  also have "... = ?prefix \<frown> LCons (Inl \<sigma>) (LCons \<sigma>' bs \<triangleright> ?t \<triangleleft> ys'')"
    by (metis zs_prefix interleave_left lhd_LCons ltl_simps(2))
  also have "... = ?prefix \<frown> LCons (Inl \<sigma>) (LCons \<sigma>' bs \<triangleright> ltakeWhile is_right ?t \<frown> LCons (Inl ()) (ltl (ldropWhile is_right ?t)) \<triangleleft> ys'')"
    sorry
  also have "... = ?prefix \<frown> LCons (Inl \<sigma>) LNil \<frown> lmap Inr (\<up> (llength (ltakeWhile is_right ?t)) ys'') \<frown> LCons (Inl \<sigma>') (bs \<triangleright> ltl (ldropWhile is_right ?t) \<triangleleft> \<down> (llength (ltakeWhile is_right ?t)) ys'')"
    sorry
  finally have "zs = ?prefix \<frown> LCons (Inl \<sigma>) LNil \<frown> lmap Inr (\<up> (llength (ltakeWhile is_right ?t)) ys'') \<frown> LCons (Inl \<sigma>') (bs \<triangleright> ltl (ldropWhile is_right ?t) \<triangleleft> \<down> (llength (ltakeWhile is_right ?t)) ys'')"
    by simp

  hence "env R (LCons \<sigma> LNil \<frown> \<up> (llength (ltakeWhile is_right ?t)) ys'' \<frown> LCons \<sigma>' LNil)"
    sorry  
  hence "(snd \<sigma>, fst \<sigma>') \<in> (R \<union> lset (\<up> (llength (ltakeWhile is_right ?t)) ys''))\<^sup>*"
    apply -
    apply (erule gap_environment[rotated 1])
    defer
    apply (rule lfinite_ltake_llength)
    sorry
  hence "(snd \<sigma>, fst \<sigma>') \<in> (R \<union> lset ys)\<^sup>*"
    apply (rule set_rev_mp)
    apply (intro rtrancl_mono Un_mono order_refl)
    by (metis Un_upper2 `lfinite ys'` lset_lappend_lfinite lset_ltake order.trans ys_split)
  from this and `(snd \<sigma>, fst \<sigma>') \<notin> (R \<union> lset ys)\<^sup>*` have False
    by blast
  thus ?thesis by blast
qed

lemma shuffle_env':
  assumes "zs \<in> xs \<sha> ys"
  and "env R (lmap \<langle>id,id\<rangle> zs)"
  shows "env ((R \<union> lset xs)\<^sup>*) ys"
  sorry

lemma lset_guar: "xs \<in> X \<Longrightarrow> lset xs \<subseteq> guar X"
  by (auto simp add: guar_def)

lemma env_iso: "R \<subseteq> S \<Longrightarrow> env R xs \<Longrightarrow> env S xs"
  sorry

lemma ex2_mono: "(\<And>x y. f x y \<longrightarrow> g x y) \<Longrightarrow> (\<exists>x y. f x y) \<longrightarrow> (\<exists>x y. g x y)"
  by auto

lemma
  assumes "r \<union> g1 \<le> r2"
  and "r \<union> g2 \<le> r1"
  and "\<And>zs. lprefix zs xs \<Longrightarrow> env (r1\<^sup>*) zs \<Longrightarrow> lset zs \<subseteq> g1\<^sup>*"
  and "\<And>zs. lprefix zs ys \<Longrightarrow> env (r2\<^sup>*) zs \<Longrightarrow> lset zs \<subseteq> g2\<^sup>*"
  and "env ((r \<union> lset ys)\<^sup>*) xs" and "env ((r \<union> lset xs)\<^sup>*) ys"
  shows "env (r1\<^sup>*) xs"
proof (rule classical, auto)
  assume "\<not> (env (r1\<^sup>*) xs)"
  from environment_var[OF this]
  obtain as \<sigma> \<sigma>' bs
  where as_finite: "lfinite as"
  and as_env: "env (r1\<^sup>*) (as \<frown> LCons \<sigma> LNil)"
  and xs_split: "xs = as \<frown> LCons \<sigma> (LCons \<sigma>' bs)"
  and bad_trans: "(snd \<sigma>, fst \<sigma>') \<notin> r1\<^sup>*"
    by blast
  have "\<exists>y y'. (y, y') \<in> lset ys \<and> (y, y') \<notin> r1\<^sup>*"
    sorry



    have "(snd \<sigma>, fst \<sigma>') \<in> r \<and> (snd \<sigma>, fst \<sigma>') \<in> (lset ys)\<^sup>*"

  have "lset (as \<frown> LCons \<sigma> LNil) \<subseteq> g1\<^sup>*"
    by (rule assms(3)) (simp_all add: xs_split as_env)

  have "lset xs \<subseteq> g1\<^sup>*"
    apply (rule assms(3))
    apply (rule env_iso)
    apply (rule rtrancl_mono)
    apply (rule assms(2))
    find_theorems "env"

  have "(snd \<sigma>, fst \<sigma>') \<in> (r \<union> lset ys)\<^sup>*"

lemma Rely_parallel:
  assumes "r1 \<Colon> x \<le> prog g1" and "r2 \<Colon> y \<le> prog g2"
  and "r \<union> g1 \<le> r2"
  and "r \<union> g2 \<le> r1"
  shows "r \<Colon> x \<parallel> y = r \<Colon> (r1 \<Colon> x) \<parallel> (r2 \<Colon> y)"
proof -
  from assms(1)
  have "\<And>xs. xs \<in> x \<Longrightarrow> env (r1\<^sup>*) xs \<Longrightarrow> lset xs \<subseteq> g1\<^sup>*"
    by (simp add: test1)
  from assms(2)
  have "\<And>ys. ys \<in> y \<Longrightarrow> env (r2\<^sup>*) ys \<Longrightarrow> lset ys \<subseteq> g2\<^sup>*"
    by (simp add: test1)

  have "r \<Colon> (x \<parallel> y) = r \<Colon> \<Union>{lmap \<langle>id,id\<rangle> ` (xs \<sha> ys) |xs ys. xs \<in> x \<and> ys \<in> y}"
    by (metis shuffle_def)
  also have "... = \<Union>{r \<Colon> lmap \<langle>id,id\<rangle> ` (xs \<sha> ys) |xs ys. xs \<in> x \<and> ys \<in> y}"
    by (subst Rely_continuous) auto
  also have "... = {zs. \<exists>xs ys. zs \<in> r \<Colon> lmap \<langle>id,id\<rangle> ` (xs \<sha> ys) \<and> xs \<in> x \<and> ys \<in> y}" 
    by (simp add: Rely_def Env_def image_def) auto
  also have "... = {zs. \<exists>xs ys. zs \<in> lmap \<langle>id,id\<rangle> ` (xs \<sha> ys) \<and> env (r\<^sup>*) zs \<and> xs \<in> x \<and> ys \<in> y}"
    by (rule Collect_cong) (auto simp add: Rely_def Env_def)
  also have "... = {lmap \<langle>id,id\<rangle> zs |zs. \<exists>xs ys. zs \<in> xs \<sha> ys \<and> env (r\<^sup>*) (lmap \<langle>id,id\<rangle> zs) \<and> xs \<in> x \<and> ys \<in> y}"
    by auto
  also have "... = lmap \<langle>id,id\<rangle> ` {zs. \<exists>xs ys. zs \<in> xs \<sha> ys \<and> env (r\<^sup>*) (lmap \<langle>id,id\<rangle> zs) \<and> xs \<in> x \<and> ys \<in> y}"
    by auto
  also have "... = lmap \<langle>id,id\<rangle> ` {zs. \<exists>xs ys. zs \<in> xs \<sha> ys \<and> env (r\<^sup>*) (lmap \<langle>id,id\<rangle> zs) \<and> env ((r \<union> lset ys)\<^sup>*) xs \<and> xs \<in> x \<and> env ((r \<union> lset xs)\<^sup>*) ys \<and> ys \<in> y}"
    by (rule arg_cong, rule Collect_cong) (metis rtrancl_Un_rtrancl rtrancl_idemp shuffle_env shuffle_env')

lemma Rely_parallel: "r \<Colon> x \<parallel> y = r \<Colon> (r \<union> guar y \<Colon> x) \<parallel> (r \<union> guar x \<Colon> y)"
proof -
  have "r \<Colon> (x \<parallel> y) = r \<Colon> \<Union>{lmap \<langle>id,id\<rangle> ` (xs \<sha> ys) |xs ys. xs \<in> x \<and> ys \<in> y}"
    by (metis shuffle_def)
  also have "... = \<Union>{r \<Colon> lmap \<langle>id,id\<rangle> ` (xs \<sha> ys) |xs ys. xs \<in> x \<and> ys \<in> y}"
    by (subst Rely_continuous) auto
  also have "... = {zs. \<exists>xs ys. zs \<in> r \<Colon> lmap \<langle>id,id\<rangle> ` (xs \<sha> ys) \<and> xs \<in> x \<and> ys \<in> y}" 
    by (simp add: Rely_def Env_def image_def) auto
  also have "... = {zs. \<exists>xs ys. zs \<in> lmap \<langle>id,id\<rangle> ` (xs \<sha> ys) \<and> env (r\<^sup>*) zs \<and> xs \<in> x \<and> ys \<in> y}"
    by (rule Collect_cong) (auto simp add: Rely_def Env_def)
  also have "... = {lmap \<langle>id,id\<rangle> zs |zs. \<exists>xs ys. zs \<in> xs \<sha> ys \<and> env (r\<^sup>*) (lmap \<langle>id,id\<rangle> zs) \<and> xs \<in> x \<and> ys \<in> y}"
    by auto
  also have "... = lmap \<langle>id,id\<rangle> ` {zs. \<exists>xs ys. zs \<in> xs \<sha> ys \<and> env (r\<^sup>*) (lmap \<langle>id,id\<rangle> zs) \<and> xs \<in> x \<and> ys \<in> y}"
    by auto
  also have "... = lmap \<langle>id,id\<rangle> ` {zs. \<exists>xs ys. zs \<in> xs \<sha> ys \<and> env (r\<^sup>*) (lmap \<langle>id,id\<rangle> zs) \<and> env ((r \<union> lset ys)\<^sup>*) xs \<and> xs \<in> x \<and> env ((r \<union> lset xs)\<^sup>*) ys \<and> ys \<in> y}"
    by (rule arg_cong, rule Collect_cong) (metis rtrancl_Un_rtrancl rtrancl_idemp shuffle_env shuffle_env')
  also have "... \<subseteq> lmap \<langle>id,id\<rangle> ` {zs. \<exists>xs ys. zs \<in> xs \<sha> ys \<and> env (r\<^sup>*) (lmap \<langle>id,id\<rangle> zs) \<and> env ((r \<union> guar y)\<^sup>*) xs \<and> xs \<in> x \<and> env ((r \<union> guar x)\<^sup>*) ys \<and> ys \<in> y}"
    apply (intro image_mono Collect_mono ex2_mono)
    apply auto
    apply (erule env_iso[rotated 1])
    apply (metis lset_guar rtrancl_mono subset_refl sup_mono)
    apply (erule env_iso[rotated 1])
    by (metis lset_guar rtrancl_mono subset_refl sup_mono)
  also have "... = lmap \<langle>id,id\<rangle> ` {zs. \<exists>xs ys. zs \<in> xs \<sha> ys \<and> env (r\<^sup>*) (lmap \<langle>id,id\<rangle> zs) \<and> xs \<in> r \<union> guar y \<Colon> x \<and> ys \<in> r \<union> guar x \<Colon> y}"
    by (rule arg_cong, rule Collect_cong) (auto simp add: Rely_def Env_def)
  also have "... = {zs. \<exists>xs ys. zs \<in> lmap \<langle>id,id\<rangle> ` (xs \<sha> ys) \<and> env (r\<^sup>*) zs \<and> xs \<in> r \<union> guar y \<Colon> x \<and> ys \<in> r \<union> guar x \<Colon> y}"
    by auto
  also have "... = {zs. \<exists>xs ys. zs \<in> r \<Colon> lmap \<langle>id,id\<rangle> ` (xs \<sha> ys) \<and> xs \<in> r \<union> guar y \<Colon> x \<and> ys \<in> r \<union> guar x \<Colon> y}" 
    by (simp add: Rely_def Env_def image_def)
  also have "... = \<Union>{r \<Colon> lmap \<langle>id,id\<rangle> ` (xs \<sha> ys) |xs ys. xs \<in> r \<union> guar y \<Colon> x \<and> ys \<in> r \<union> guar x \<Colon> y}"
    by auto
  also have "... = r \<Colon> \<Union>{lmap \<langle>id,id\<rangle> ` (xs \<sha> ys) |xs ys. xs \<in> r \<union> guar y \<Colon> x \<and> ys \<in> r \<union> guar x \<Colon> y}"
    by (subst Rely_continuous) auto
  also have "... = r \<Colon> (r \<union> guar y \<Colon> x) \<parallel> (r \<union> guar x \<Colon> y)"
    by (metis shuffle_def)
  finally have "r \<Colon> x \<parallel> y \<subseteq> r \<Colon> (r \<union> guar y \<Colon> x) \<parallel> (r \<union> guar x \<Colon> y)" .
  moreover have "r \<Colon> (r \<union> guar y \<Colon> x) \<parallel> (r \<union> guar x \<Colon> y) \<subseteq> r \<Colon> x \<parallel> y"
    by (metis Rely_coextensive Rely_iso par.mult_isol_var)
  ultimately show ?thesis by blast
qed

definition quintuple :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> ('a \<times> 'a) lan \<Rightarrow> ('a \<times> 'a) lan \<Rightarrow> ('a \<times> 'a) lan \<Rightarrow> bool" ("_, _ \<turnstile> \<lbrace>_\<rbrace> _ \<lbrace>_\<rbrace>" [20,20,20,20,20] 1000) where
  "r, g \<turnstile> \<lbrace>p\<rbrace> c \<lbrace>q\<rbrace> \<equiv> r \<Colon> (p \<cdot> c) \<le> q \<inter> prog g"

lemma Rely_iso2: "r1\<^sup>* \<le> r2\<^sup>* \<Longrightarrow> r1 \<Colon> x \<le> r2 \<Colon> y"
  sorry

primrec circle :: "'a rel \<Rightarrow> ('a \<times> 'a) lan \<Rightarrow> ('a \<times> 'a) lan \<Rightarrow> nat \<Rightarrow> ('a \<times> 'a) lan" where
  "circle r x y 0 = y"
| "circle r x y (Suc n) = r \<union> guar (circle r y x n) \<Colon> y"

lemma circle_simp1: "r \<squnion> guar (circle r x y n) \<Colon> circle r y x n = r \<squnion> guar (circle r x y n) \<Colon> x"
  apply (induct n arbitrary: x y)
  apply auto
  apply (metis Rely_coextensive Rely_comm set_rev_mp)
  sorry
(*
  sledgehammer
  by (metis guar_iso inf_absorb2 inf_sup_aci(1) mod_coext mod_meet order_refl sup_mono)
*)

lemma prog_lset: "xs \<in> prog g \<longleftrightarrow> lset xs \<subseteq> g\<^sup>*"
  by (auto simp add: prog_def)

lemma test1: "r \<Colon> x \<le> prog g \<longleftrightarrow> (\<forall>xs \<in> x. env (r\<^sup>*) xs \<longrightarrow> lset xs \<subseteq> g\<^sup>*)"
  by (auto simp add: subset_eq Rely_def Env_def prog_lset)

lemma test2: "r \<Colon> x \<le> prog g \<longleftrightarrow> (\<forall>xs \<in> x. \<forall>xs'. lprefix xs' xs \<and> lfinite xs' \<and> env (r\<^sup>*) xs' \<longrightarrow> lset xs' \<subseteq> g\<^sup>*)"
  apply (simp add: test1)
  apply auto
  apply (metis Rely_coextensive Rely_iso2 prog_lset r_into_rtrancl subsetD subsetI subset_trans test1)
  by (metis Rely_coextensive Rely_iso2 in_mono order_trans subset_refl test1)

lemma "r \<Colon> x \<subseteq> prog r \<Longrightarrow> \<exists>n. prog r = iter (\<lambda>g. guar g \<Colon> x) n UNIV"
  apply (simp add: test2)

lemma "\<not> (r \<Colon> x \<le> prog g) \<longleftrightarrow> (\<exists>xs\<in>X. env (r\<^sup>*) xs \<and> \<not> lset xs \<subseteq> g\<^sup>*)"
  by (metis (mono_tags) Rely_iso2 order_refl subset_antisym test1)

theorem parallel:
  assumes "r1, g1 \<turnstile> \<lbrace>p1\<rbrace> c1 \<lbrace>q1\<rbrace>" and "g2 \<le> r1"
  and "r2, g2 \<turnstile> \<lbrace>p2\<rbrace> c2 \<lbrace>q2\<rbrace>" and "g1 \<le> r2"
  and "(p1 \<inter> p2) \<cdot> (c1 \<parallel> c2) \<le> (p1 \<cdot> c1 \<parallel> p2 \<cdot> c2)"
  and "prog g1 \<parallel> q2 \<le> q2"
  and "q1 \<parallel> prog g2 \<le> q1"
  shows "(r1 \<inter> r2), (g1 \<union> g2) \<turnstile> \<lbrace>p1 \<inter> p2\<rbrace> c1 \<parallel> c2 \<lbrace>q1 \<inter> q2\<rbrace>"
proof -
  have "(r1 \<inter> r2) \<Colon> (p1 \<inter> p2) \<cdot> (c1 \<parallel> c2) \<le> r1 \<inter> r2 \<Colon> (p1 \<cdot> c1 \<parallel> p2 \<cdot> c2)"
    apply (simp add: shuffle_def)
    

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

lemma in_shuffleE2: "zs \<in> lmap \<langle>id,id\<rangle> ` (xs \<sha> ys) \<Longrightarrow> (\<exists>t. zs = lmap \<langle>id,id\<rangle> (xs \<triangleright> t \<triangleleft> ys) \<and> llength (\<ll> t) = llength xs \<and> llength (\<rr> t) = llength ys)"
  apply (drule in_shuffleE)
  apply (erule exE)
  apply (rule_tac x = "traj zs'" in exI)
  apply (simp add: tshuffle_words_def)
  by (metis reinterleave)

lemma in_rely_shuffleE: "zs \<in> rely R \<bullet> lmap \<langle>id,id\<rangle> ` (xs \<sha> ys) \<Longrightarrow> (\<exists>t. zs = lmap \<langle>id,id\<rangle> (xs \<triangleright> t \<triangleleft> ys) \<and> env (R\<^sup>*) zs \<and> llength (\<ll> t) = llength xs \<and> llength (\<rr> t) = llength ys)"
  apply (simp add: Rely_def Env_def)
  by (metis in_shuffleE2)

notation ltake ("\<up>")
  and ldrop ("\<down>")

lemma [simp]: "llength (\<rr> (ltakeWhile is_right t)) = llength (ltakeWhile is_right t)"
  sorry

lemma [simp]: "LNil \<triangleright> ltakeWhile is_right t \<triangleleft> \<up> (llength (ltakeWhile is_right t)) zs = lmap Inr (\<up> (llength (ltakeWhile is_right t)) zs)"
  sorry

lemma lem1:
  assumes "env (R\<^sup>*) (lmap \<langle>id,id\<rangle> (LCons \<sigma> (LCons \<sigma>' ys) \<triangleright> t \<triangleleft> zs))"
  and "llength (\<ll> t) = llength (LCons \<sigma> (LCons \<sigma>' ys))"
  and "llength (\<rr> t) = llength zs"
  shows "(snd \<sigma>, fst \<sigma>') \<in> (R \<union> lset zs)\<^sup>*"
  sorry
(*
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
*)

lemma lem2:
  assumes "env (R\<^sup>*) (lmap \<langle>id,id\<rangle> (xs \<frown> LCons \<sigma> (LCons \<sigma>' ys) \<triangleright> t \<triangleleft> zs))"
  and "llength (\<ll> t) = llength (xs \<frown> LCons \<sigma> (LCons \<sigma>' ys))"
  and "llength (\<rr> t) = llength zs"
  and "lfinite xs"
  shows "(snd \<sigma>, fst \<sigma>') \<in> (R \<union> lset zs)\<^sup>*"
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
  apply (subgoal_tac "(snd (a, b), fst (aa, ba)) \<in> (R \<union> lset ys)\<^sup>*")
  apply simp
  apply (rule_tac xs = ysa and ys = zsa and t = t in lem2)
  by auto

lemma "

(*
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
*)

lemma "rely R \<bullet> lmap \<langle>id,id\<rangle> ` (xs \<sha> ys) \<noteq> {} \<longleftrightarrow> (env ((R \<union> lset ys)\<^sup>*) xs \<and> env ((R \<union> lset xs)\<^sup>*) ys)"

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
