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

fun sum_compare :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a + 'b) \<Rightarrow> ('a + 'b) \<Rightarrow> bool" (infixl "\<oplus>" 95) where
  "op \<oplus> P Q (Inl x) (Inl y) = P x y"
| "op \<oplus> P Q (Inr x) (Inr y) = Q x y"
| "op \<oplus> P Q (Inl _) (Inr _) = False"
| "op \<oplus> P Q (Inr _) (Inl _) = False"

context order
begin

lemma "{xs} \<Sha> pt op \<le> ys = Pt (op = \<oplus> op \<le>) (xs \<sha> ys)"
  sorry

thm pointwise.coinduct

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

lemma
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
          then obtain wr where "w = Inr wr" by blast
          have "zr \<le> wr"
            using pt_ys
            apply (simp add: zs_LCons zr)
            

lemma "pt op \<le> xs \<Sha> pt op \<le> ys = Pt (op \<le> \<oplus> op \<le>) (xs \<sha> ys)"
  apply (auto simp add: tshuffle_words_def Pt_def tshuffle_def)
  apply (rename_tac zs)
  apply (rule_tac x = "xs \<triangleright> traj zs \<triangleleft> ys" in exI)
  apply (intro conjI)
  sledgehammer


end

end

