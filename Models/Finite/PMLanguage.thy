theory PMLanguage
  imports Language
begin

find_consts "('a \<times> 'b) set \<Rightarrow> 'a set"

value "\<lambda>X. fst ` X"

inductive_set dep_traces :: "'a rel \<Rightarrow> 'a lan" for D where
  dt_Nil [simp]: "[] \<in> dep_traces D"
| dt_no_dep: "b \<notin> Field D \<Longrightarrow> as @ cs \<in> dep_traces D \<Longrightarrow> as @ [b] @ cs \<in> dep_traces D"
| dt_dep: "b \<in> fst ` D \<Longrightarrow> c \<in> snd ` D \<Longrightarrow> as @ ds \<in> dep_traces D \<Longrightarrow> as @ [b] @ [c] @ ds \<in> dep_traces D"

definition shuffle_dep :: "'a lan \<Rightarrow> 'a rel \<Rightarrow> 'a lan \<Rightarrow> 'a lan" where
  "shuffle_dep X D Y = (X \<parallel> Y) \<inter> dep_traces D"

notation (input) shuffle_dep ("_ \<parallel>\<^sub>_ _" [74,0,75] 75)


lemma dep_traces_empty: "xs \<in> dep_traces {}"
  by (induct xs) (auto intro: dt_no_dep[where as = "[]", simplified])

lemma [simp]: "dep_traces {} = UNIV"
  by (metis UNIV_eq_I dep_traces_empty)

lemma "D = {} \<Longrightarrow> (X \<parallel>\<^sub>D Y) \<parallel>\<^sub>D Z = X \<parallel>\<^sub>D (Y \<parallel>\<^sub>D Z)"
  by (simp add: shuffle_dep_def shuffle_assoc)

definition shf :: "('c list \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> ('a + 'b) lan" where 
  "shf P f g xs ys = {zs. \<ll> zs = xs \<and> \<rr> zs = ys \<and> P (map \<langle>f,g\<rangle> zs)}"

lemma [simp]: "\<langle>f,g\<rangle> \<circ> Inr = g"
  by (simp add: o_def)

lemma [simp]: "shf P f g [] ys = (if P (map g ys) then {map Inr ys} else {})"
  apply (auto simp add: shf_def)
  apply (metis no_lefts)
  sorry

lemma [simp]: "shf P f g xs [] = (if P (map g xs) then {map Inl ys} else {})"
  sorry

lemma tshuffle_words_map:
  fixes f :: "'a \<Rightarrow> 'b"
  and g :: "'c \<Rightarrow> 'd"
  and h :: "'b \<Rightarrow> 'e"
  and k :: "'d \<Rightarrow> 'e"
  shows "shf P h k (map f xs) (map g ys) = map \<langle>Inl \<circ> f, Inr \<circ> g\<rangle> ` shf P (h \<circ> f) (k \<circ> g) xs ys"
proof
  show "shf P h k (map f xs) (map g ys) \<subseteq> map \<langle>Inl \<circ> f,Inr \<circ> g\<rangle> ` shf P (h \<circ> f) (k \<circ> g) xs ys"
  proof (induct xs arbitrary: ys)
    fix ys
    case Nil show ?case by (simp add: o_def)
  next
    fix ys :: "'c list"
    case (Cons x xs)

    have "shf P h k (map f (x # xs)) (map g ys) = shf P h k (f x # map f xs) (map g ys)"
      by simp
    also have "... \<subseteq> map \<langle>Inl \<circ> f,Inr \<circ> g\<rangle> ` shf P (h \<circ> f) (k \<circ> g) (x # xs) ys"
    proof (induct ys, simp)

lemma tshuffle_words_map:
  shows "map f xs \<sha>\<^sub>D map g ys = map \<langle>Inl \<circ> f, Inr \<circ> g\<rangle> ` (xs \<sha>\<^sub>D ys)"
proof
  show "map f xs \<sha>\<^sub>D map g ys \<subseteq> map \<langle>Inl \<circ> f, Inr \<circ> g\<rangle> ` (xs \<sha>\<^sub>D ys)"
  proof (induct xs arbitrary: ys, simp_all)
    fix x xs and ys :: "'c list"

    assume ih_xs: "\<And>ys::'c list. (map f xs) \<sha>\<^sub>D (map g ys) \<subseteq> map \<langle>Inl \<circ> f, Inr \<circ> g\<rangle> ` (xs \<sha>\<^sub>D ys)"

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

lemma shuffle_dep: "(X \<parallel>\<^sub>D Y) = \<Union>{map \<langle>id,id\<rangle> ` (x \<sha> y) \<inter> dep_traces D|x y. x \<in> X \<and> y \<in> Y}"
  apply simp
  by (auto simp: shuffle_dep_def shuffle_def Int_Union2)



lemma "(X \<parallel>\<^sub>D Y) = \<Union>{map \<langle>id,id\<rangle> ` (x \<sha> y) \<inter> dep_traces D|x y. x \<in> X \<and> y \<in> Y}"

lemma "(X \<parallel>\<^sub>D Y) \<parallel>\<^sub>D Z = X \<parallel>\<^sub>D (Y \<parallel>\<^sub>D Z)"
  by (simp add: shuffle_dep_def shuffle_assoc)

class comm_monoid_zero = comm_monoid_mult + zero +
  assumes mult_zero: "0 * x = 0"



lemma shuffle_sm: "X\<^sup>\<ddagger> \<parallel> Y \<subseteq> (X \<parallel> Y)\<^sup>\<ddagger>"
proof -
  have "X\<^sup>\<ddagger> \<parallel> Y = \<Union>sm_set ` X \<parallel> Y"
    by (simp add: sm_closure_def)
  also have "... = \<Union>{sm_set xs \<parallel> Y|xs. xs \<in> X}"
    by (subst shuffle_inf_distr) (auto simp add: image_def)
  also have "... = \<Union>{\<Union>{map \<langle>id,id\<rangle> ` (xs' \<sha> ys) |xs' ys. xs' \<in> sm_set xs \<and> ys \<in> Y}|xs. xs \<in> X}"
    by (simp add: shuffle_def)
  also have "... = \<Union>{\<Union>{map \<langle>id,id\<rangle> ` (xs' \<sha> ys) |xs'. xs' \<in> sm_set xs}|xs ys. xs \<in> X \<and> ys \<in> Y}"
    by blast
  also have "... \<subseteq> \<Union>{(map \<langle>id,id\<rangle> ` (xs \<sha> ys))\<^sup>\<ddagger>|xs ys. xs \<in> X \<and> ys \<in> Y}"
    by (insert tshuffle_sm) blast
  also have "... = \<Union>{\<Union>zs\<in>xs \<sha> ys. sm_set (map \<langle>id,id\<rangle> zs)|xs ys. xs \<in> X \<and> ys \<in> Y}"
    by (simp add: sm_closure_def)
  also have "... = (X \<parallel> Y)\<^sup>\<ddagger>"
    by (auto simp add: shuffle_def sm_closure_def)
  finally show ?thesis .
qed