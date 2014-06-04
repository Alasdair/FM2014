theory Stutter_Language
  imports Language
begin

inductive_set stutter :: "('a \<times> 'a) llist \<Rightarrow> ('a \<times> 'a) lan" for xs where
  self [simp, intro!]: "xs \<in> stutter xs"
| stutter_left [dest]: "ys \<frown> LCons (\<sigma>, \<sigma>') zs \<in> stutter xs \<Longrightarrow> ys \<frown> LCons (\<sigma>, \<sigma>) (LCons (\<sigma>, \<sigma>') zs) \<in> stutter xs"
| stutter_right [dest]: "ys \<frown> LCons (\<sigma>, \<sigma>') zs \<in> stutter xs \<Longrightarrow> ys \<frown> LCons (\<sigma>, \<sigma>') (LCons (\<sigma>', \<sigma>') zs) \<in> stutter xs"

definition Stutter :: "('a \<times> 'a) lan \<Rightarrow> ('a \<times> 'a) lan" ("_\<^sup>\<dagger>" [1000] 1000) where
  "X\<^sup>\<dagger> = \<Union>{stutter xs |xs. xs \<in> X}"

lemma stutter_trans: "xs \<in> stutter ys \<Longrightarrow> ys \<in> stutter zs \<Longrightarrow> xs \<in> stutter zs"
proof (induct xs rule: stutter.induct)
  case self
  thus ?case .
next
  case (stutter_left ys \<sigma> \<sigma>' zs)
  from stutter_left(2)[OF stutter_left(3)]
  show ?case
    by (rule stutter.stutter_left)
next
  case (stutter_right ys \<sigma> \<sigma>' zs)
  from stutter_right(2)[OF stutter_right(3)]
  show ?case
    by (rule stutter.stutter_right)
qed

lemma stutter_lappend: "xs \<in> stutter xs' \<Longrightarrow> ys \<in> stutter ys' \<Longrightarrow> (xs \<frown> ys) \<in> stutter (xs' \<frown> ys')"
proof (induct xs rule: stutter.induct)
  case self
  thus ?case
  proof (induct ys rule: stutter.induct)
    case self
    show ?case
      by (metis stutter.self)
  next
    case (stutter_left ws \<sigma> \<sigma>' vs)
    thus ?case
      by (metis lappend_assoc stutter.stutter_left)
  next
    case (stutter_right ws \<sigma> \<sigma>' vs)
    thus ?case
      by (metis lappend_assoc stutter.stutter_right)      
  qed
next
  case (stutter_left ws \<sigma> \<sigma>' vs)
  thus ?case
    by (metis lappend_assoc lappend_code(2) stutter.stutter_left)
next
  case (stutter_right ws \<sigma> \<sigma>' vs)
  thus ?case
    by (metis lappend_assoc lappend_code(2) stutter.stutter_right)
qed

lemma Stutter_iso: "X \<subseteq> Y \<Longrightarrow> X\<^sup>\<dagger> \<subseteq> Y\<^sup>\<dagger>"
  by (auto simp add: Stutter_def)

lemma Stutter_ext: "X \<subseteq> X\<^sup>\<dagger>"
  by (auto simp add: Stutter_def)

lemma Stutter_idem [simp]: "X\<^sup>\<dagger>\<^sup>\<dagger> = X\<^sup>\<dagger>"
proof -
  have "X\<^sup>\<dagger>  \<subseteq> X\<^sup>\<dagger>\<^sup>\<dagger>"
    by (metis Stutter_ext)
  thus "X\<^sup>\<dagger>\<^sup>\<dagger> = X\<^sup>\<dagger>"
    by (auto dest: stutter_trans simp add: Stutter_def)
qed

lemma Stutter_union [simp]: "(X \<union> Y)\<^sup>\<dagger> = X\<^sup>\<dagger> \<union> Y\<^sup>\<dagger>"
  by (auto simp add: Stutter_def)

lemma Stutter_continuous: "(\<Union>\<XX>)\<^sup>\<dagger> = \<Union>{X\<^sup>\<dagger> |X. X \<in> \<XX>}"
  by (auto simp add: Stutter_def)

lemma Stutter_meet [simp]: "(X\<^sup>\<dagger> \<inter> Y\<^sup>\<dagger>)\<^sup>\<dagger> = X\<^sup>\<dagger> \<inter> Y\<^sup>\<dagger>"
  by (auto dest: stutter_trans simp add: Stutter_def)

lemma stutter_infinite [dest]: "ys \<in> stutter xs \<Longrightarrow> \<not> lfinite xs \<Longrightarrow> \<not> lfinite ys"
  by (induct ys rule: stutter.induct) auto

lemma stutter_l_prod: "stutter xs \<cdot> stutter ys \<subseteq> stutter (xs \<frown> ys)"
  apply (auto simp add: l_prod_def)
  apply (metis lappend_inf stutter.self stutter_lappend)
  by (metis stutter_lappend)

lemma stutter_LNil: "xs \<in> stutter LNil \<Longrightarrow> xs = LNil"
  by (induct rule: stutter.induct) auto

end
