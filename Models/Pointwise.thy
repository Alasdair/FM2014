theory Pointwise
  imports Language
begin

context fixes binop :: "'a \<Rightarrow> 'b \<Rightarrow> bool" (infixl "\<triangleleft>" 55)
begin 

(* Pointwise comparison operator for lazy lists *)

coinductive pointwise :: "'a llist \<Rightarrow> 'b llist \<Rightarrow> bool" where
  pointwise_LNil [intro!]: "pointwise LNil LNil"
| pointwise_LConsI [intro!]: "x \<triangleleft> y \<Longrightarrow> pointwise xs ys \<Longrightarrow> pointwise (LCons x xs) (LCons y ys)"

(* Basic rules for pointwise *)

lemma pointwise_LConsE [dest]: "pointwise (LCons x xs) (LCons y ys) \<Longrightarrow> pointwise xs ys"
  by (metis LNil_not_LCons pointwise.simps ltl_LCons)

lemma [elim]: "pointwise (LCons x xs) (LCons y ys) \<Longrightarrow> x \<triangleleft> y"
  by (metis LCons_inject LNil_not_LCons pointwise.simps)

lemma [iff]: "pointwise xs LNil \<longleftrightarrow> xs = LNil"
  by (metis LNil_not_LCons pointwise.simps)

lemma [iff]: "pointwise LNil xs \<longleftrightarrow> xs = LNil"
  by (metis LNil_not_LCons pointwise.simps)

(* Two pointwise equivalent lists must have the same length *)

lemma pointwise_llength: "pointwise xs ys \<Longrightarrow> llength xs = llength ys"
proof -
  assume "pointwise xs ys"
  hence "(llength xs, llength ys) \<in> {(llength xs, llength ys)|(xs::'a llist) (ys::'b llist). pointwise xs ys}"
    by auto
  thus ?thesis
  proof (coinduct rule: enat_equalityI)
    case (Eqenat n m) note q = this[simplified]
    then obtain xs :: "'a llist" and ys :: "'b llist"
    where n_def: "n = llength xs" and m_def: "m = llength ys" and pointwise: "pointwise xs ys"
      by blast
    {
      assume "xs = LNil"
      moreover hence "ys = LNil"
        by (metis LNil_not_LCons pointwise pointwise.cases)
      ultimately have ?zero
        by (metis llength_LNil m_def n_def)
    }
    moreover
    {
      assume "ys = LNil"
      moreover hence "xs = LNil"
        by (metis LNil_not_LCons pointwise pointwise.cases)
      ultimately have ?zero
        by (metis llength_LNil m_def n_def)
    }
    moreover
    {
      assume "\<exists>x' xs'. xs = LCons x' xs'" and "\<exists>y' ys'. ys = LCons y' ys'"
      from this and n_def and m_def and pointwise
      have ?eSuc
        by (auto, rule_tac x = xs' in exI, auto)
    }
    ultimately show ?case
      by (cases xs, simp) (cases ys, simp_all)
  qed
qed

(* Properties of pointwise equivalence and lappend *)

lemma pointwise_lappend:
  assumes "pointwise t xs" and "pointwise s ys"
  shows "pointwise (t \<frown> s) (xs \<frown> ys)"
proof (cases "lfinite xs")
  assume "lfinite xs"
  from this and assms
  show "pointwise (t \<frown> s) (xs \<frown> ys)"
  proof (induct xs arbitrary: t rule: lfinite_induct)
    case Nil thus ?case by (cases t) auto
  next
    case (Cons x xs) thus ?case by (cases t) auto
  qed
next
  assume "\<not> lfinite xs"
  moreover hence "\<not> lfinite t" using assms
    by (auto dest!: pointwise_llength simp: lfinite_conv_llength_enat)
  ultimately show "pointwise (t \<frown> s) (xs \<frown> ys)"
    by (metis assms(1) lappend_inf)
qed

lemma pointwise_lappend_ltake1: "pointwise t (xs \<frown> ys) \<Longrightarrow> pointwise (ltake (llength xs) t) xs"
proof (cases "lfinite xs")
  assume "lfinite xs" and "pointwise t (xs \<frown> ys)"
  thus "pointwise (ltake (llength xs) t) xs"
  proof (induct xs arbitrary: t rule: lfinite_induct)
    case Nil show ?case by auto
  next
    case (Cons x xs)
    thus ?case
      by (cases t) auto
  qed
next
  assume "\<not> lfinite xs" and "pointwise t (xs \<frown> ys)"
  thus "pointwise (ltake (llength xs) t) xs"
    by (metis lappend_inf ltake_all order_refl pointwise_llength)
qed

lemma pointwise_lappend_ltake2:
  "lfinite xs \<Longrightarrow> pointwise t (xs \<frown> ys) \<Longrightarrow> pointwise (ldrop (llength xs) t) ys"
proof (induct xs arbitrary: t rule: lfinite_induct)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  thus ?case
    by (cases t) auto
qed

abbreviation pt :: "'b llist \<Rightarrow> 'a lan" where
  "pt xs \<equiv> {t. pointwise t xs}" 

lemma pt_LCons: "pt (LCons x xs) = {LCons y ys |y ys. pointwise (LCons y ys) (LCons x xs)}"
proof auto
  fix ys
  assume "pointwise ys (LCons x xs)"
  thus "\<exists>y' ys'. ys = LCons y' ys' \<and> pointwise (LCons y' ys') (LCons x xs)"
    by (cases ys) auto
qed

lemma pt_ind: "pt (LCons x xs) = {LCons y ys |y ys. y \<triangleleft> x \<and> ys \<in> pt xs}"
  by (simp add: pt_LCons) auto

definition Pt :: "'b lan \<Rightarrow> 'a lan" where
  "Pt X \<equiv> {t. \<exists>xs. pointwise t xs \<and> xs \<in> X}" 


end

lemma pt_FIN: "lfinite xs \<Longrightarrow> pt f xs \<subseteq> FIN"
  by (auto dest!: pointwise_llength simp add: FIN_def lfinite_conv_llength_enat)

lemma pt_infinite: "\<not> lfinite xs \<Longrightarrow> pt f xs \<cdot> {} = pt f xs"
  apply (auto simp add: l_prod_def)
  apply (drule pointwise_llength)
  by (metis lfinite_conv_llength_enat)

lemma pt_lappend: "pt f (xs \<frown> ys) = pt f xs \<cdot> pt f ys"
  apply (cases "lfinite xs")
  apply (frule pt_FIN[where f = f])
  apply (simp add: fin_l_prod)
  defer
  apply (metis l_prod_assoc lappend_inf seq.annil pt_infinite)
  apply auto
  apply (rename_tac t)
  apply (rule_tac x = "ltake (llength xs) t" in exI)
  apply (rule_tac x = "ldrop (llength xs) t" in exI)
  apply (intro conjI)
  apply (simp add: lappend_ltake_ldrop)
  apply (metis pointwise_lappend_ltake1)
  apply (metis pointwise_lappend_ltake2)
  by (metis pointwise_lappend)

lemma Pt_union [simp]: "Pt f (X \<union> Y) = Pt f X \<union> Pt f Y"
  by (auto simp add: Pt_def)

lemma l_prod_inf_distl: "X \<subseteq> FIN \<Longrightarrow> X \<cdot> \<Union>\<YY> = \<Union>{X \<cdot> Y |Y. Y \<in> \<YY>}"
  by (auto simp add: l_prod_def FIN_def)

lemma set_comp_fun_eq1: "(\<And>x. P x \<Longrightarrow> f x = g x) \<Longrightarrow> {f x |x. P x} = {g x |x. P x}"
  by auto metis

lemma [simp]: "Pt f {xs \<in> X. \<not> lfinite xs} = Pt f X \<cdot> {}"
  apply (simp add: l_prod_def)
  apply (auto simp add: Pt_def)
  apply (drule pointwise_llength)
  apply (auto simp: lfinite_conv_llength_enat)
  by (metis pointwise_llength)

lemma [simp]: "\<Union>{pt f xs |xs. xs \<in> X \<and> lfinite xs} = Pt f X \<inter> FIN"
  apply (auto simp add: FIN_def Pt_def)
  apply (metis lfinite_conv_llength_enat pointwise_llength)
  apply (rule_tac x = "pt f xs" in exI)
  apply simp
  apply (rule_tac x = xs in exI)
  apply auto
  by (metis lfinite_conv_llength_enat pointwise_llength)

lemma [simp]: "X \<cdot> {} \<union> X \<inter> FIN = X"
  by (auto simp add: l_prod_def FIN_def)

lemma Pt_l_prod: "Pt f (X \<cdot> Y) = Pt f X \<cdot> Pt f Y"
proof -
  have "Pt f (X \<cdot> Y) = Pt f {xs \<in> X. \<not> lfinite xs} \<union> Pt f {xs \<frown> ys |xs ys. xs \<in> X \<and> lfinite xs \<and> ys \<in> Y}"
    by (simp add: l_prod_def)
  also have "... = Pt f X \<cdot> {} \<union> Pt f {xs \<frown> ys |xs ys. xs \<in> X \<and> lfinite xs \<and> ys \<in> Y}"
    by simp
  also have "... = Pt f X \<cdot> {} \<union> \<Union>{pt f (xs \<frown> ys) |xs ys. xs \<in> X \<and> lfinite xs \<and> ys \<in> Y}"
    by (auto simp add: Pt_def)
  also have "... = Pt f X \<cdot> {} \<union> \<Union>{pt f xs \<cdot> pt f ys |xs ys. xs \<in> X \<and> lfinite xs \<and> ys \<in> Y}"
    by (simp add: pt_lappend)
  also have "... = Pt f X \<cdot> {} \<union> \<Union>{\<Union>{pt f xs \<cdot> pt f ys |ys. ys \<in> Y} |xs. xs \<in> X \<and> lfinite xs}"
    by blast
  also have "... = Pt f X \<cdot> {} \<union> \<Union>{pt f xs \<cdot> \<Union>{pt f ys |ys. ys \<in> Y} |xs. xs \<in> X \<and> lfinite xs}"
    by (rule arg_cong, rule set_comp_fun_eq1) (auto simp: pt_FIN[THEN l_prod_inf_distl])
  also have "... = Pt f X \<cdot> {} \<union> \<Union>{pt f xs |xs. xs \<in> X \<and> lfinite xs} \<cdot> \<Union>{pt f ys |ys. ys \<in> Y}"
    by (rule arg_cong, subst l_prod_inf_distr, blast)
  also have "... = Pt f X \<cdot> {} \<union> \<Union>{pt f xs |xs. xs \<in> X \<and> lfinite xs} \<cdot> Pt f Y"
    by (rule arg_cong, auto simp add: Pt_def)
  also have "... = Pt f X \<cdot> {} \<union> (Pt f X \<inter> FIN) \<cdot> Pt f Y"
    by simp
  also have "... = Pt f X \<cdot> {} \<cdot> Pt f Y \<union> (Pt f X \<inter> FIN) \<cdot> Pt f Y"
    by (metis l_prod_zero seq.mult_assoc)
  also have "... = (Pt f X \<cdot> {} \<union> (Pt f X \<inter> FIN)) \<cdot> Pt f Y"
    by (metis l_prod_distr)
  also have "... = Pt f X \<cdot> Pt f Y"
    by simp
  finally show ?thesis .
qed

fun sum_compare :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a + 'b) \<Rightarrow> ('a + 'b) \<Rightarrow> bool" (infixl "\<oplus>" 95) where
  "op \<oplus> P Q (Inl x) (Inl y) = P x y"
| "op \<oplus> P Q (Inr x) (Inr y) = Q x y"
| "op \<oplus> P Q (Inl _) (Inr _) = False"
| "op \<oplus> P Q (Inr _) (Inl _) = False"

context order
begin

lemma pointwise_refl [intro!]: "pointwise op \<le> x x"
  apply (coinduct rule: pointwise.coinduct[where X = "op ="])
  apply auto
  by (metis llist_cases order_refl)

lemma [simp]: "traj LNil = LNil"
  by (metis traj_LNil traj_interleave)

lemma [iff]: "xs \<triangleright> t \<triangleleft> ys = LNil \<longleftrightarrow> t = LNil"
  by (metis traj_LNil traj_interleave)

lemma [iff]: "traj xs = LNil \<longleftrightarrow> xs = LNil"
  by (metis reinterleave traj_LNil traj_interleave)

lemma [simp]: "traj (LCons (Inl x) xs) = LCons (Inl ()) (traj xs)"
  by (simp add: traj_def)

lemma [simp]: "traj (LCons (Inr x) xs) = LCons (Inr ()) (traj xs)"
  by (simp add: traj_def)

lemma pointwise_interleave:
  assumes "pointwise op \<le> (\<ll> zs) xs"
  and "pointwise op \<le> (\<rr> zs) ys"
  shows "pointwise (op \<le> \<oplus> op \<le>) zs (xs \<triangleright> traj zs \<triangleleft> ys)"
proof -
  from assms
  have "(zs, xs \<triangleright> traj zs \<triangleleft> ys) \<in> {(zs, xs \<triangleright> traj zs \<triangleleft> ys) |zs xs ys. pointwise op \<le> (\<ll> zs) xs \<and> pointwise op \<le> (\<rr> zs) ys}"
    by auto
  thus ?thesis
  proof coinduct
    case (pointwise zs ws) note q = this[simplified]
    then obtain xs and ys where ws_def: "ws = xs \<triangleright> traj zs \<triangleleft> ys" and pt_xs: "pointwise op \<le> (\<ll> zs) xs" and pt_ys: "pointwise op \<le> (\<rr> zs) ys"
      by auto

    show ?case
    proof (cases zs)
      assume "zs = LNil"
      from this and ws_def have ?pointwise_LNil by simp
      thus ?case
        by blast
    next
      fix z zs'
      assume zs_LCons: "zs = LCons z zs'"
      show ?case
      proof (cases ws)
        assume "ws = LNil"
        from this and ws_def have ?pointwise_LNil by simp
        thus ?case
          by blast
      next
        fix w ws'
        assume ws_LCons: "ws = LCons w ws'"
        show ?case
        proof (cases z)
          fix zr assume zr: "z = Inr zr"
          hence "\<exists>wr. w = Inr wr" using ws_LCons zs_LCons
            by (simp add: ws_def interleave_right) metis
          then obtain wr where wr: "w = Inr wr" by blast
          have "lhd ys = wr" and "ys \<noteq> LNil" using ws_def and pt_ys
            by (auto simp add: ws_LCons zs_LCons zr wr interleave_right)
          hence zr_wr: "zr \<le> wr" using pt_ys
            by (simp add: zs_LCons zr) (metis lhd_LCons pointwise.cases)
          show ?case
            apply (rule disjI2)
            apply (rule_tac x = "Inr zr" in exI)
            apply (rule_tac x = "Inr wr" in exI)
            apply (rule_tac x = "zs'" in exI)
            apply (rule_tac x = "ws'" in exI)
            apply (intro conjI)
            apply simp_all
            prefer 4
            apply (intro disjI1)
            apply (rule_tac x = xs in exI)
            apply (rule_tac x = "ltl ys" in exI)
            apply (intro conjI)
            using ws_def
            apply (simp add: ws_LCons zs_LCons zr interleave_right)
            using pt_xs
            apply (simp add: zs_LCons zr)
            using pt_ys
            apply (simp add: zs_LCons zr)
            apply (frule pointwise_llength)
            apply (subgoal_tac "ys = LCons (lhd ys) (ltl ys)")
            apply (metis pointwise_LConsE)
            apply (subst lhd_LCons_ltl)
            apply (metis LNil_not_LCons pointwise.simps)
            apply simp
            apply (simp add: zs_LCons zr)
            apply (simp add: ws_LCons wr)
            by (rule zr_wr)
        next
          fix zl assume zl: "z = Inl zl"
          hence "\<exists>wl. w = Inl wl" using ws_LCons zs_LCons
            by (simp add: ws_def interleave_left) metis
          then obtain wl where wl: "w = Inl wl" by blast
          have "lhd xs = wl" and "xs \<noteq> LNil" using ws_def and pt_xs
            by (auto simp add: ws_LCons zs_LCons zl wl interleave_left)
          hence zl_wl: "zl \<le> wl" using pt_xs
            by (simp add: zs_LCons zl) (metis lhd_LCons pointwise.cases)
          show ?case
            apply (rule disjI2)
            apply (rule_tac x = "Inl zl" in exI)
            apply (rule_tac x = "Inl wl" in exI)
            apply (rule_tac x = "zs'" in exI)
            apply (rule_tac x = "ws'" in exI)
            apply (intro conjI)
            apply simp_all
            prefer 4
            apply (intro disjI1)
            apply (rule_tac x = "ltl xs" in exI)
            apply (rule_tac x = "ys" in exI)
            apply (intro conjI)
            using ws_def
            apply (simp add: ws_LCons zs_LCons zl interleave_left)
            using pt_xs
            apply (simp add: zs_LCons zl)
            apply (frule pointwise_llength)
            apply (subgoal_tac "xs = LCons (lhd xs) (ltl xs)")
            apply (metis pointwise_LConsE)
            apply (subst lhd_LCons_ltl)
            apply (metis LNil_not_LCons pointwise.simps)
            apply simp
            using pt_ys
            apply (simp add: zs_LCons zl)
            apply (simp add: zs_LCons zl)
            apply (simp add: ws_LCons wl)
            by (rule zl_wl)
        qed
      qed
    qed
  qed
qed

lemma pt_shuffle: "pt op \<le> xs \<Sha> pt op \<le> ys = Pt (op \<le> \<oplus> op \<le>) (xs \<sha> ys)"
proof
  show "pt op \<le> xs \<Sha> pt op \<le> ys \<subseteq> Pt (op \<le> \<oplus> op \<le>) (xs \<sha> ys)"
    apply (auto simp add: tshuffle_words_def Pt_def tshuffle_def)
    apply (rename_tac zs)
    apply (rule_tac x = "xs \<triangleright> traj zs \<triangleleft> ys" in exI)
    apply (intro conjI)
    apply (metis pointwise_interleave)
    by (auto dest: pointwise_llength intro: lefts_interleave_llength rights_interleave_llength)
  show "Pt (op \<le> \<oplus> op \<le>) (xs \<sha> ys) \<subseteq> pt op \<le> xs \<Sha> pt op \<le> ys"
    apply (auto simp add: Pt_def tshuffle_def)
    apply (rename_tac ws zs)
    apply (rule_tac x = "\<ll> ws \<sha> \<rr> ws" in exI)
    apply auto
    apply (rule_tac x = "\<ll> ws" in exI)
    apply (rule_tac x = "\<rr> ws" in exI)
    apply (auto simp add: tshuffle_words_def)
    sorry
qed

abbreviation sublist_closure :: "'a lan \<Rightarrow> 'a lan" ("_\<^sup>\<dagger>" [101] 100) where
  "X\<^sup>\<dagger> \<equiv> Pt op \<le> X"

lemma [intro]: "pointwise (op \<le> \<oplus> op \<le>) xs ys \<Longrightarrow> pointwise op \<le> (lmap \<langle>id,id\<rangle> xs) (lmap \<langle>id,id\<rangle> ys)"
  sorry

lemma [simp]: "lmap \<langle>id,id\<rangle> ` Pt (op \<le> \<oplus> op \<le>) X = (lmap \<langle>id,id\<rangle> ` X)\<^sup>\<dagger>"
  apply (auto simp: Pt_def image_def)
  apply (rename_tac xs xs')
  sorry
  
lemma sl_closure_idem: "(X\<^sup>\<dagger>)\<^sup>\<dagger> = X\<^sup>\<dagger>"
  apply (auto simp add: Pt_def)
  sorry

lemma sl_closure_mono: "X \<le> Y \<Longrightarrow> X\<^sup>\<dagger> \<le> Y\<^sup>\<dagger>"
  by (auto simp add: Pt_def)

lemma sl_closure: "X \<le> X\<^sup>\<dagger>"
  by (auto simp add: Pt_def)

lemma sl_closure_par: "(X\<^sup>\<dagger> \<parallel> Y\<^sup>\<dagger>) = (X \<parallel> Y)\<^sup>\<dagger>"
proof -
  have "X\<^sup>\<dagger> \<parallel> Y\<^sup>\<dagger> = \<Union>{lmap \<langle>id,id\<rangle> ` (x \<sha> y) |x y. x \<in> X\<^sup>\<dagger> \<and> y \<in> Y\<^sup>\<dagger>}"
    by (simp add: shuffle_def)
  also have "... = \<Union>{lmap \<langle>id,id\<rangle> ` (pt op \<le> x \<Sha> pt op \<le> y) |x y. x \<in> X \<and> y \<in> Y}"
    apply (simp add: Pt_def tshuffle_def)
    apply auto
    apply (rename_tac xs ys zs xs' ys')
    apply (rule_tac x = "lmap \<langle>id,id\<rangle> ` (pt op \<le> xs' \<Sha> pt op \<le> ys')" in exI)
    apply auto
    apply (rule_tac x = xs' in exI)
    apply (rule_tac x = ys' in exI)
    apply (intro conjI)
    apply (rule arg_cong) back
    apply (simp add: tshuffle_def)
    apply simp_all
    apply (rule imageI)
    apply (simp add: tshuffle_def)
    by metis
  also have "... = \<Union>{lmap \<langle>id,id\<rangle> ` Pt (op \<le> \<oplus> op \<le>) (x \<sha> y) |x y. x \<in> X \<and> y \<in> Y}"
    by (simp add: pt_shuffle)
  also have "... = \<Union>{(lmap \<langle>id,id\<rangle> ` (x \<sha> y))\<^sup>\<dagger> |x y. x \<in> X \<and> y \<in> Y}"
    by simp
  also have "... = (X \<parallel> Y)\<^sup>\<dagger>"
    by (auto simp add: shuffle_def Pt_def)
  finally show ?thesis .
qed

lemma sl_closure_par2: "(X\<^sup>\<dagger> \<parallel> Y)\<^sup>\<dagger> = (X \<parallel> Y)\<^sup>\<dagger>"
  by (metis sl_closure_par sl_closure_idem)

end

lemma pointwise_self: "pointwise op \<in> t (lmap (\<lambda>x. {x}) t)"
proof -
  have "(\<forall>n. enat n < llength t \<longrightarrow> lnth t n \<in> lnth (lmap (\<lambda>x. {x}) t) n) \<and> llength t = llength (lmap (\<lambda>x. {x}) t)"
    by auto
  thus ?thesis
  proof (coinduct)
    case (pointwise t xs)
    thus ?case
      apply (cases t)
      apply simp
      apply (subgoal_tac "\<exists>y ys. xs = LCons y ys")
      apply auto
      apply (erule_tac x = 0 in allE)
      apply (simp add: enat_0)
      apply (erule_tac x = "Suc n" in allE)
      apply simp
      apply (metis Suc_ile_eq)
      by (metis llength_eq_0 neq_LNil_conv zero_ne_eSuc)
  qed
qed

end

