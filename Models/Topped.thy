theory Topped
  imports Main
begin

datatype 'a top = Top | NotTop 'a

abbreviation bind :: "('a \<Rightarrow> 'b top) \<Rightarrow> 'a top \<Rightarrow> 'b top" (infixr "\<hookleftarrow>" 56)  where
  "bind f x \<equiv> case x of Top \<Rightarrow> Top | NotTop x \<Rightarrow> f x"

lemma top_left_id: "f \<hookleftarrow> NotTop x = f x"
  by simp

lemma top_right_id: "NotTop \<hookleftarrow> x = x"
  by (cases x) auto

lemma top_assoc: "g \<hookleftarrow> f \<hookleftarrow> x = (\<lambda>x. g \<hookleftarrow> (f x)) \<hookleftarrow> x"
  by (cases x) auto

instantiation top :: (ord) ord
begin
  definition less_eq_top :: "'a top \<Rightarrow> 'a top \<Rightarrow> bool" where
    "x \<le> y \<equiv> case y of Top \<Rightarrow> True | NotTop y \<Rightarrow> case x of Top \<Rightarrow> False | NotTop x \<Rightarrow> x \<le> y"

  definition less_top :: "'a top \<Rightarrow> 'a top \<Rightarrow> bool" where
    "less_top x y \<equiv> x \<le> y \<and> \<not> (y \<le> x)"

  instance by default
end

instance top :: (order) order
proof
  fix x y z :: "'a top"
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (simp add: less_top_def)
  show "x \<le> x"
    by (cases x) (auto simp add: less_eq_top_def)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    apply (cases x)
    apply (cases y, cases z, (force simp add: less_eq_top_def)+)
    apply (cases y, cases z, (force simp add: less_eq_top_def)+)
    by (cases z, (force simp add: less_eq_top_def)+)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (cases x) (cases y, (force simp add: less_eq_top_def)+)+
qed

lemma [simp, intro!]: "x \<le> Top"
  by (simp add: less_eq_top_def)

lemma [simp]: "Top \<le> x \<longleftrightarrow> x = Top"
  by (cases x) (simp_all add: less_eq_top_def)

lemma NotTop_mono: "x \<le> y \<Longrightarrow> NotTop x \<le> NotTop y"
  by (auto simp add: less_eq_top_def)

lemma [simp]: "NotTop x \<le> NotTop y \<longleftrightarrow> x \<le> y"
  by (auto simp add: less_eq_top_def)  

instantiation top :: (lattice) lattice
begin
  definition sup_top :: "'a top \<Rightarrow> 'a top \<Rightarrow> 'a top" where
    "sup_top x y \<equiv> case x of Top \<Rightarrow> Top | NotTop x \<Rightarrow> (case y of Top \<Rightarrow> Top | NotTop y \<Rightarrow> NotTop (sup x y))"

  definition inf_top :: "'a top \<Rightarrow> 'a top \<Rightarrow> 'a top" where
    "inf_top x y \<equiv> case x of Top \<Rightarrow> y | NotTop x \<Rightarrow> (case y of Top \<Rightarrow> NotTop x | NotTop y \<Rightarrow> NotTop (inf x y))"  

  lemma [simp]: "inf Top y = y"
    by (simp add: inf_top_def)

  lemma [simp]: "inf x Top = x"
    by (cases x) (simp_all add: inf_top_def)

  lemma [simp]: "inf (NotTop x) (NotTop y) = NotTop (inf x y)"
    by (simp add: inf_top_def)

  lemma [simp]: "sup Top y = Top"
    by (simp add: sup_top_def)

  lemma [simp]: "sup x Top = Top"
    by (cases x) (simp_all add: sup_top_def)

  lemma [simp]: "sup (NotTop x) (NotTop y) = NotTop (sup x y)"
    by (simp add: sup_top_def)

  instance
  proof
    fix x y z :: "'a top"
    show "inf x y \<le> x"
      by (simp add: inf_top_def, cases x, simp, cases y, auto)
    show "inf x y \<le> y"
      by (simp add: inf_top_def, cases x, simp, cases y, auto)
    show "x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> inf y z"
      by (cases x, simp, cases y, simp, cases z, auto)
    show "x \<le> sup x y"
      by (cases x, simp, cases y, auto)
    show "y \<le> sup x y"
      by (cases x, simp, cases y, auto)
    show "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> sup y z \<le> x"
      by (cases x, simp, cases y, simp, cases z, auto)
  qed
end

find_theorems "Inf" "{}"

instantiation top :: (complete_lattice) complete_lattice
begin
  definition Inf_top :: "'a top set \<Rightarrow> 'a top" where "Inf_top X \<equiv> if X \<subseteq> {Top} then Top else NotTop (Inf {x. NotTop x \<in> X})"

  definition Sup_top :: "'a top set \<Rightarrow> 'a top" where "Sup_top X \<equiv> if Top \<in> X then Top else NotTop (Sup {x. NotTop x \<in> X})"

  definition top_top :: "'a top" where "top_top = Top"

  definition bot_top :: "'a top" where "bot_top = NotTop bot"

  instance
  proof
    fix a :: "'a top"
    show "a \<le> top"
      by (cases a) (auto simp add: top_top_def less_eq_top_def)
    show "bot \<le> a"
      by (cases a) (auto simp add: bot_top_def less_eq_top_def)
  next
    fix x :: "'a top" and A :: "'a top set"
    assume xA: "x \<in> A"
    show "Inf A \<le> x" using xA
      by (cases x) (auto intro: Inf_lower simp: Inf_top_def)
    show "x \<le> Sup A" using xA
      by (cases x) (auto intro: Sup_upper simp add: Sup_top_def less_eq_top_def) 
  next
    fix z :: "'a top" and A :: "'a top set"
    assume "\<And>x. x \<in> A \<Longrightarrow> z \<le> x"
    thus "z \<le> Inf A"
      apply (cases z)
      apply (auto simp add: Inf_top_def)
      by (metis (lifting, no_types) le_Inf_iff less_eq_top_def mem_Collect_eq top.simps(5))
  next
    fix z :: "'a top" and A :: "'a top set"
    assume "\<And>x. x \<in> A \<Longrightarrow> x \<le> z"
    thus "Sup A \<le> z"
      apply (cases z)
      apply (auto intro!: Sup_least simp add: Sup_top_def less_eq_top_def)
      apply (metis top.simps(4))
      by (metis (full_types) top.simps(5))
  qed
end

lemma top_bind [simp]: "f \<hookleftarrow> top = top" by (simp add: top_top_def)

end
