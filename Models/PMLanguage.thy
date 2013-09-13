theory PMLanguage
  imports Language
begin

class comm_monoid_zero = comm_monoid_mult + zero +
  assumes mult_zero: "0 * x = 0"

inductive_set sm_set :: "('a + 'b::comm_monoid_zero) llist \<Rightarrow> ('a + 'b) lan" for T  where
  self [intro!]: "LCons (Inr 1) T \<in> sm_set T"
| stutter: "as \<frown> bs \<in> sm_set T \<Longrightarrow> as \<frown> LCons (Inr 1) bs \<in> sm_set T"
| mumble: "as \<frown> LCons (Inr b) (LCons (Inr c) ds) \<in> sm_set T \<Longrightarrow> as \<frown> LCons (Inr (b * c)) ds \<in> sm_set T"
| split: "as \<frown> LCons (Inr z) ds \<in> sm_set T \<Longrightarrow> z = b * c \<Longrightarrow>  as \<frown> LCons (Inr b) (LCons (Inr c) ds) \<in> sm_set T"
| deadlock: "as \<frown> LCons (Inr 0) bs \<in> sm_set T \<Longrightarrow> as \<frown> LCons (Inr 0) cs \<in> sm_set T"

definition deadlock :: "('a + 'b::comm_monoid_zero) lan" where
  "deadlock = {[Inr 0]}"

definition sm_closure :: "('a + 'b::comm_monoid_zero) lan \<Rightarrow> ('a + 'b::comm_monoid_zero) lan" ("_\<^sup>\<ddagger>" [101] 100) where
  "X\<^sup>\<ddagger> \<equiv> \<Union>(sm_set ` X)"

lemma tshuffle_sm: "\<Union>{map \<langle>id,id\<rangle> ` (xs' \<sha> ys)|xs'. xs' \<in> sm_set xs} \<subseteq> (map \<langle>id,id\<rangle> ` (xs \<sha> ys))\<^sup>\<ddagger>"
  sorry

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