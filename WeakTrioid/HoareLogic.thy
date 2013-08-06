theory HoareLogic
  imports WeakTrioid
begin

section {* Hoare Calculus - Sequential *}

context weak_trioid
begin

definition hoare_triple :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("\<lbrace> _ \<rbrace> _ \<lbrace> _ \<rbrace>" [54,54,54] 53)
  where "\<lbrace>x\<rbrace>y\<lbrace>z\<rbrace> \<equiv> x\<cdot>y \<le> z"

declare hoare_triple_def [simp]

lemma hoare_trivial: "\<lbrace>x\<rbrace>y\<lbrace>x\<cdot>y\<rbrace>"
  by simp

theorem weakening_rule: "\<lbrakk>x \<le> v; \<lbrace>v\<rbrace>y\<lbrace>w\<rbrace>; w \<le> z\<rbrakk> \<Longrightarrow> \<lbrace>x\<rbrace>y\<lbrace>z\<rbrace>"
  by (insert mult_isol[of x v y], auto)

theorem composition_rule: "\<lbrace>x\<rbrace>y\<cdot>y'\<lbrace>z\<rbrace> = (\<exists>x'. \<lbrace>x\<rbrace>y\<lbrace>x'\<rbrace> \<and> \<lbrace>x'\<rbrace>y'\<lbrace>z\<rbrace>)"
  by (auto, metis eq_refl mult_assoc, metis mult_assoc mult_isol order_trans)  

theorem skip_rule [simp]: "\<lbrace>x\<rbrace>1\<lbrace>z\<rbrace> \<longleftrightarrow> (x \<le> z)"
  by (simp, metis mult_oner)

corollary skip_true: "\<lbrace>x\<rbrace>1\<lbrace>x\<rbrace>"
  by (simp, metis eq_refl mult_oner)

lemma antitony: "(\<forall>x z. \<lbrace>x\<rbrace>y\<lbrace>z\<rbrace> \<longrightarrow> \<lbrace>x\<rbrace>y'\<lbrace>z\<rbrace>) \<longleftrightarrow> y' \<le> y"
  by (auto, metis eq_refl mult_onel, metis mult_isor order_trans)
  
lemma extensionality: "(\<forall>x z. \<lbrace>x\<rbrace>y\<lbrace>z\<rbrace> = \<lbrace>x\<rbrace>y'\<lbrace>z\<rbrace>) \<longleftrightarrow> y' = y"
  by (metis antisym antitony)

lemma comp_antitony: "(\<forall>x z w. \<lbrace>x\<rbrace>y\<lbrace>w\<rbrace> \<and> \<lbrace>w\<rbrace>y'\<lbrace>z\<rbrace> \<longrightarrow> \<lbrace>x\<rbrace>y''\<lbrace>z\<rbrace>) = (y'' \<le> y\<cdot>y')"
  by (smt antitony composition_rule)

lemma choice: "\<lbrace>x\<rbrace>y+y'\<lbrace>z\<rbrace> = (\<lbrace>x\<rbrace>y\<lbrace>z\<rbrace> \<and> \<lbrace>x\<rbrace>y'\<lbrace>z\<rbrace>)"
  by (simp, smt add_assoc add_comm add_idem leq_def mult_distl)

(* Failure needs the mult_annil axiom *)
lemma failure: "\<lbrace>x\<rbrace>0\<lbrace>z\<rbrace>"
  nitpick oops

lemma iteration: "\<lbrace>x\<rbrace>y\<lbrace>x\<rbrace> = \<lbrace>x\<rbrace>y\<^sup>*\<lbrace>x\<rbrace>"
  by (metis antitony hoare_triple_def star_ext star_inductr_var)

lemma iteration2: "\<lbrace>x\<rbrace>y\<lbrace>x\<rbrace> = \<lbrace>x\<rbrace>y\<^sup>+\<lbrace>x\<rbrace>"
  by (metis antitony composition_rule iteration star_trancl trancl_ext)

(* The following lemmas needs the exchange axiom *)
theorem concurrency: "\<lbrakk>\<lbrace>x\<rbrace>y\<lbrace>z\<rbrace>; \<lbrace>x'\<rbrace>y'\<lbrace>z'\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>x\<parallel>x'\<rbrace>y\<parallel>y'\<lbrace>z\<parallel>z'\<rbrace>"
  nitpick oops

theorem frame_rule: "\<lbrace>x\<rbrace>y\<lbrace>z\<rbrace> \<Longrightarrow> \<lbrace>w\<parallel>x\<rbrace>y\<lbrace>w\<parallel>z\<rbrace>"
  nitpick oops

end

(****************************************************************************)

section {* Hoare Calculus - Concurrency *}
context weak_cka
begin

theorem concurrency: "\<lbrakk>\<lbrace>x\<rbrace>y\<lbrace>z\<rbrace>; \<lbrace>x'\<rbrace>y'\<lbrace>z'\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>x\<parallel>x'\<rbrace>y\<parallel>y'\<lbrace>z\<parallel>z'\<rbrace>"
  by (simp, metis exchange order_trans par_double_iso)

theorem frame_rule: "\<lbrace>x\<rbrace>y\<lbrace>z\<rbrace> \<Longrightarrow> \<lbrace>w\<parallel>x\<rbrace>y\<lbrace>w\<parallel>z\<rbrace>"
  by (metis concurrency par_unitl skip_true)

end

end
