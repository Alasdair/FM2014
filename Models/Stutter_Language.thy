theory Stutter_Language
  imports Language
begin

inductive_set stutter :: "('a \<times> 'a) llist \<Rightarrow> ('a \<times> 'a) lan" for xs where
  self [simp, intro!]: "LCons (\<sigma>, \<sigma>) xs \<in> stutter xs"
| stutter [intro]: "ys \<frown> zs \<in> stutter xs \<Longrightarrow> ys \<frown> LCons (\<sigma>, \<sigma>) zs \<in> stutter xs"
| mumble [dest]: "ys \<frown> LCons (\<sigma>, \<sigma>') (LCons (\<sigma>', \<sigma>'') zs) \<in> stutter xs \<Longrightarrow> ys \<frown> LCons (\<sigma>, \<sigma>'') zs \<in> stutter xs"

definition Stutter :: "('a \<times> 'a) lan \<Rightarrow> ('a \<times> 'a) lan" ("_\<^sup>\<dagger>" [1000] 1000) where
  "X\<^sup>\<dagger> = \<Union>{stutter xs |xs. xs \<in> X}"

lemma [dest]: "xs \<in> stutter (LCons (\<sigma>, \<sigma>) ys) \<Longrightarrow> xs \<in> stutter ys"
  apply (induct xs rule: stutter.induct)
  apply (metis lappend_code(1) stutter.self stutter.stutter)
  apply (metis stutter.stutter)
  by (metis stutter.mumble)

lemma [simp]: "Id_on UNIV = {(\<sigma>, \<sigma>'). \<sigma> = \<sigma>'}"
  by (metis Collect_mem_eq in_rel_Collect_split_eq in_rel_Id_on_UNIV split_curry)

lemma [intro]: "xs \<in> stutter LNil \<Longrightarrow> xs \<in> \<Union>{stutter xs |xs. \<exists>a. xs = LCons (a, a) LNil}"
  apply (induct xs rule: stutter.induct)
  apply auto
  apply (rule_tac x = "stutter (LCons (\<sigma>, \<sigma>) LNil)" in exI)
  apply auto
  by (metis lappend_code(1) stutter.mumble stutter.self)

definition test :: "'a set \<Rightarrow> ('a \<times> 'a) lan" ("\<langle>_\<rangle>" [0] 1000) where
  "\<langle>S\<rangle> \<equiv> ((\<lambda>x. LCons x LNil) ` Id_on S)\<^sup>\<dagger>"

(* 1\<^sup>\<dagger> is the top test element *)
lemma [simp]: "{LNil}\<^sup>\<dagger> = \<langle>top\<rangle>"
  by (auto simp add: Stutter_def test_def image_def)

(* 0\<^sup>\<dagger> is the least test element *)
lemma [simp]: "{}\<^sup>\<dagger> = \<langle>bot\<rangle>"
  by (auto simp add: Stutter_def test_def)

lemma LNil_Stutter_fin [intro!]: "{LNil}\<^sup>\<dagger> \<subseteq> FIN"
proof (auto simp add: FIN_def Stutter_def)
  fix xs :: "('a \<times> 'a) llist"
  assume "xs \<in> stutter LNil"
  thus "lfinite xs"
    by (induct xs rule: stutter.induct, auto)
qed

lemma stutter_trans: "xs \<in> stutter ys \<Longrightarrow> ys \<in> stutter zs \<Longrightarrow> xs \<in> stutter zs"
  sorry

lemma stutter_lappend: "xs \<in> stutter xs' \<Longrightarrow> ys \<in> stutter ys' \<Longrightarrow> (xs \<frown> ys) \<in> stutter (xs' \<frown> ys')"
  sorry

lemma Stutter_iso: "X \<subseteq> Y \<Longrightarrow> X\<^sup>\<dagger> \<subseteq> Y\<^sup>\<dagger>"
  by (auto simp add: Stutter_def)

lemma stutter_never_LNil: "xs \<in> stutter ys \<Longrightarrow> xs = LNil \<Longrightarrow> False"
  by (induct rule: stutter.induct) auto

lemma [dest!]: "LNil \<in> stutter xs \<Longrightarrow> False"
  by (metis stutter_never_LNil)

lemma stutter_refl: "LCons x xs \<in> stutter (LCons x xs)"
proof (cases x, erule ssubst)
  fix \<sigma> \<sigma>'
  have "LCons (\<sigma>, \<sigma>) (LCons (\<sigma>, \<sigma>') xs) \<in> stutter (LCons (\<sigma>, \<sigma>') xs)"
    by (metis stutter.self)
  from stutter.mumble[where ys = "LNil", simplified, OF this]
  show "LCons (\<sigma>, \<sigma>') xs \<in> stutter (LCons (\<sigma>, \<sigma>') xs)" .
qed

lemma [dest!]: "x \<notin> stutter x \<Longrightarrow> x = LNil"
  by (metis neq_LNil_conv stutter_refl)

lemma Stutter_ext: "X - {LNil} \<subseteq> X\<^sup>\<dagger>"
  by (auto simp add: Stutter_def, erule_tac x = "stutter x" in allE, auto)

lemma Stutter_idem [simp]: "X\<^sup>\<dagger>\<^sup>\<dagger> = X\<^sup>\<dagger>"
proof -
  have "X\<^sup>\<dagger> = X\<^sup>\<dagger> - {LNil}"
    by (auto simp add: Stutter_def)
  also have "... \<subseteq> X\<^sup>\<dagger>\<^sup>\<dagger>"
    by (metis calculation Stutter_ext)
  finally show "X\<^sup>\<dagger>\<^sup>\<dagger> = X\<^sup>\<dagger>"
    by (auto dest: stutter_trans simp add: Stutter_def)
qed

lemma [simp]: "\<langle>top\<rangle> \<cdot> X\<^sup>\<dagger> = X\<^sup>\<dagger>"
  sorry

lemma [simp]: "X\<^sup>\<dagger> \<cdot> \<langle>top\<rangle> = X\<^sup>\<dagger>"
  sorry

lemma Stutter_union [simp]: "(X \<union> Y)\<^sup>\<dagger> = X\<^sup>\<dagger> \<union> Y\<^sup>\<dagger>"
  by (auto simp add: Stutter_def)

lemma Stutter_continuous: "(\<Union>\<XX>)\<^sup>\<dagger> = \<Union>{X\<^sup>\<dagger> |X. X \<in> \<XX>}"
  by (auto simp add: Stutter_def) 

lemma Stutter_meet [simp]: "(X\<^sup>\<dagger> \<inter> Y\<^sup>\<dagger>)\<^sup>\<dagger> = X\<^sup>\<dagger> \<inter> Y\<^sup>\<dagger>"
  apply (auto dest: stutter_trans simp add: Stutter_def)
  by (metis neq_LNil_conv stutter_never_LNil stutter_refl)

lemma stutter_infinite [dest]: "ys \<in> stutter xs \<Longrightarrow> \<not> lfinite xs \<Longrightarrow> \<not> lfinite ys"
  by (induct ys rule: stutter.induct) auto

lemma Stutter_l_prod [simp]: "(X \<cdot> Y)\<^sup>\<dagger> = (X\<^sup>\<dagger> \<cdot> Y\<^sup>\<dagger>)\<^sup>\<dagger>"
  sorry

definition ldeleteLeft :: "('a + 'b) llist \<Rightarrow> ('a + 'b) llist" where
  "ldeleteLeft xs = ltakeWhile is_right xs \<frown> ltl (ldropWhile is_right xs)"

lemma "xs' \<in> stutter xs \<Longrightarrow> zs \<in> xs' \<sha> ys \<Longrightarrow>
  (\<exists>zs'. stutter (lmap \<langle>id,id\<rangle> zs) = stutter zs' \<and> zs' \<in> lmap \<langle>id,id\<rangle> ` (xs \<sha> ys))"
proof (induct xs' arbitrary: zs rule: stutter.induct)
  case (self \<sigma>)
  
  hence "stutter (lmap \<langle>id,id\<rangle> zs) = stutter (lmap \<langle>id,id\<rangle> (LCons (\<sigma>, \<sigma>) xs \<triangleright> traj zs \<triangleleft> ys))"
    by (metis (lifting, full_types) mem_Collect_eq reinterleave tshuffle_words_def)
  also have "... = stutter (lmap \<langle>id,id\<rangle> (xs \<triangleright> ldeleteLeft (traj zs) \<triangleleft> ys))"
    sorry
  finally have "stutter (lmap \<langle>id,id\<rangle> zs) = stutter (lmap \<langle>id,id\<rangle> (xs \<triangleright> ldeleteLeft (traj zs) \<triangleleft> ys))" .

  moreover have "xs \<triangleright> ldeleteLeft (traj zs) \<triangleleft> ys \<in> xs \<sha> ys"
    sorry

  ultimately show ?case
    by auto
next
  case (stutter xs1 xs2 \<sigma>)
  


lemma "xs' \<in> stutter xs \<Longrightarrow> zs \<in> xs' \<sha> ys \<Longrightarrow> \<exists>Z. (\<exists>zs. Z = stutter zs \<and> zs \<in> lmap \<langle>id,id\<rangle> ` (xs \<sha> ys)) \<and> lmap \<langle>id,id\<rangle> zs \<in> Z"
proof (induct xs' rule: stutter.induct)
  fix \<sigma>
  assume "zs \<in> LCons (\<sigma>, \<sigma>) xs \<sha> ys" 

lemma "stutter xs \<parallel> {ys} \<subseteq> (lmap \<langle>id,id\<rangle> ` (xs \<sha> ys))\<^sup>\<dagger>"
  apply (auto simp add: shuffle_def Stutter_def)
  apply (rename_tac xs' zs)
  apply (rule_tac x = "stutter (lmap \<langle>id,id\<rangle> (xs' \<triangleright> traj zs \<triangleleft> ys))" in exI)
  apply (intro conjI)
  apply (rule_tac x = "(lmap \<langle>id,id\<rangle> ` (xs \<sha> ys))\<^sup>\<dagger>" in exI)
  apply simp

lemma "X\<^sup>\<dagger> \<parallel> Y \<subseteq> (X \<parallel> Y)\<^sup>\<dagger>"
  apply (simp add: shuffle_def Stutter_def)

lemma Stutter_shuffle [simp]: "(X \<parallel> Y)\<^sup>\<dagger> = X\<^sup>\<dagger> \<parallel> Y\<^sup>\<dagger>"
  apply (simp add: shuffle_def Stutter_def)
  apply safe
  sorry

lemma [simp]: "X\<^sup>\<dagger> \<parallel> {LNil}\<^sup>\<dagger> = X\<^sup>\<dagger>"
  by (metis Stutter_shuffle par.mult.right_neutral)

lemma [simp]: "{LNil}\<^sup>\<dagger> \<parallel> X\<^sup>\<dagger> = X\<^sup>\<dagger>"
  by (metis Stutter_shuffle par.mult.right_neutral shuffle_comm)

end

