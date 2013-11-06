theory Examples
  imports Trace
begin


type_synonym state = "nat \<Rightarrow> nat"

datatype expr = Var nat
              | BinOp "nat \<Rightarrow> nat \<Rightarrow> nat" expr expr
              | UnOp "nat \<Rightarrow> nat" expr
              | Val nat

primrec vars :: "expr \<Rightarrow> nat set" where
  "vars (Var n) = {n}"
| "vars (BinOp f e1 e2) = vars e1 \<union> vars e2"
| "vars (UnOp f e) = vars e"
| "vars (Val n) = {}"

primrec eval :: "state \<Rightarrow> expr \<Rightarrow> nat" where
  "eval \<sigma> (Var v) = \<sigma> v"
| "eval \<sigma> (BinOp f e1 e2) = f (eval \<sigma> e1) (eval \<sigma> e2)"
| "eval \<sigma> (UnOp f e) = f (eval \<sigma> e)"
| "eval \<sigma> (Val n) = n"

lift_definition atomic_fn :: "(state \<Rightarrow> state) \<Rightarrow> state trace"
  is "\<lambda>f. {LCons (x, f x) LNil |x. True}" by simp

definition assign_value :: "nat \<Rightarrow> nat \<Rightarrow> state trace" (infix "\<leftharpoondown>" 110) where
  "x \<leftharpoondown> v = atomic_fn (\<lambda>\<sigma> y. if x = y then v else \<sigma> y)"

lemma assign_value_atomic: "x \<leftharpoondown> v = \<langle>{(\<sigma>, (\<lambda>y. if x = y then v else \<sigma> y)) |\<sigma>. True}\<rangle>"
  apply (auto simp add: assign_value_def)
  apply transfer
  apply (rule arg_cong) back
  by (auto simp add: atomic_def)

definition assign :: "nat \<Rightarrow> expr \<Rightarrow> state trace" (infix ":=" 110) where
  "x := e = (\<Squnion>v. test {\<sigma>. eval \<sigma> e = v} \<cdot> x \<leftharpoondown> v)"

definition preserves :: "'a set \<Rightarrow> 'a trace" where
  "preserves P = \<langle>{(\<sigma>, \<sigma>'). \<sigma> \<in> P \<longrightarrow> \<sigma>' \<in> P}\<rangle>\<^sup>\<star>"

lemma preserves_RG [intro]: "preserves X \<in> RG"
  by (simp add: preserves_def, transfer, auto)

definition unchanged :: "nat set \<Rightarrow> state trace" where
  "unchanged Vars \<equiv> \<langle>{(\<sigma>, \<sigma>'). \<forall>v\<in>Vars. \<sigma> v = \<sigma>' v}\<rangle>\<^sup>\<star>"

lemma unchanged_RG [intro]: "unchanged X \<in> RG"
  by (simp add: unchanged_def, transfer, auto)

lemma assign_unchanged [intro]: "x := e \<le> unchanged (- {x})"
  sorry

lift_definition ends :: "'a set \<Rightarrow> 'a trace"
  is "\<lambda>P. {t. lfinite t \<and> t \<noteq> LNil \<and> snd (llast t) \<in> P}" by simp

declare rg_meet_closed [intro!]

lemma atomic_shuffle [simp]: "\<langle>R\<rangle>\<^sup>\<star> \<parallel> \<langle>S\<rangle> = \<langle>R\<rangle>\<^sup>\<star> \<cdot> \<langle>S\<rangle> \<cdot> \<langle>R\<rangle>\<^sup>\<star>"
  sorry

lemma [simp]: "\<langle>R\<rangle>\<^sup>\<star> \<sqinter> \<langle>S\<rangle>\<^sup>\<star> = \<langle>R\<^sup>+ \<inter> S\<^sup>+\<rangle>\<^sup>\<star>"
  by transfer (metis Mumble_atomic Mumble_atomic_star rely_inter)

lemma [simp]: "{(\<sigma>, \<sigma>'). \<sigma> x = \<sigma>' x}\<^sup>+ = {(\<sigma>, \<sigma>'). \<sigma> x = \<sigma>' x}"
  by (rule trancl_id) (simp add: trans_def)

lemma [simp]: "{(\<sigma>, \<sigma>'). \<sigma> \<in> P \<longrightarrow> \<sigma>' \<in> P}\<^sup>+ = {(\<sigma>, \<sigma>'). \<sigma> \<in> P \<longrightarrow> \<sigma>' \<in> P}"
  by (rule trancl_id) (simp add: trans_def)

(*
lemma ends_preserves: "ends P \<cdot> preserves P \<le> ends P"
  apply (simp add: preserves_def)
  apply transfer
  apply simp
  apply (rule Mumble_iso)
*)

lemma atomic_iso: "X \<le> Y \<Longrightarrow> \<langle>X\<rangle> \<le> \<langle>Y\<rangle>"
  by transfer auto

(*
lemma ends_test_same: "ends P \<cdot> test P = ends P"
*)

lemma ends_test: "ends P \<cdot> test Q \<le>\<^sub>\<pi> ends (P \<inter> Q)"
  sorry

lemma test_ends: "test P \<le> ends P"
  apply (simp add: test_def)
  apply transfer
  apply (simp add: atomic_def)
  apply (rule Mumble_iso)
  by (auto simp add: image_def)

(*
lemma ends_right: "x\<cdot>0 = 0 \<Longrightarrow> x \<cdot> ends P \<le> ends P"
  apply transfer
  apply simp
*)

lemma Mumble_empty: "{}\<^sup>\<dagger> = {}"
  by (auto simp add: Mumble_def)

lemma [simp]: "lfinite xs \<Longrightarrow> llast (LCons x (xs \<frown> LCons y ys)) = llast (LCons y ys)"
  by (metis lappend_code(2) lfinite_LCons llast_lappend_LCons)

lemma proj_order_refl [intro!]: "x \<le>\<^sub>\<pi> x"
  by (metis order_refl proj_leq_iso)

abbreviation assigns_notation :: "state set \<Rightarrow> nat \<Rightarrow> expr \<Rightarrow> state set"
  ("_\<lbrakk>_ := _\<rbrakk>" [100,100,100] 101) where
  "P\<lbrakk>x := e\<rbrakk> \<equiv> (\<lambda>\<sigma> y. if x = y then eval \<sigma> e else \<sigma> y) ` P"

find_theorems UNION

lemma [simp]: "(\<Union>x\<in>X. (f x)\<^sup>\<dagger>)\<^sup>\<dagger> = (\<Union>x\<in>X. f x)\<^sup>\<dagger>"
  apply (auto simp add: Mumble_def)
  apply (metis mumble_trans)
  by (metis mumble.self)

lemma par_inf_dist: "(x::'a trace) \<parallel> \<Squnion>Y = \<Squnion>(op \<parallel> x ` Y)"
  apply transfer
  apply simp
  apply (simp add: shuffle_inf_dist)
  apply (rule arg_cong) back
  by auto

lemma inf_distl: "x\<cdot>0 = 0 \<Longrightarrow> (x::'a trace) \<cdot> \<Squnion>Y = \<Squnion>(op \<cdot> x ` Y)"
  apply transfer
  apply (simp only: Mumble_l_prod)
  apply (subst l_prod_inf_distl)
  defer
  apply (subst Mumble_continuous)
  apply (subst Mumble_continuous)
  apply (rule arg_cong) back
  apply (auto simp add: image_def)
  apply (metis Mumble_l_prod)
  by (auto simp add: FIN_def Mumble_def l_prod_def)

lemma [simp]: "{(\<sigma>, \<sigma>'). (\<forall>v\<in>vars e. \<sigma> v = \<sigma>' v)}\<^sup>+ = {(\<sigma>, \<sigma>'). (\<forall>v\<in>vars e. \<sigma> v = \<sigma>' v)}"
  by (rule trancl_id) (auto simp add: trans_def)

lemma [simp]: "({(\<sigma>, \<sigma>'). (\<forall>v\<in>vars e. \<sigma> v = \<sigma>' v)} \<inter> {(\<sigma>, \<sigma>'). \<sigma> \<in> P \<longrightarrow> \<sigma>' \<in> P})\<^sup>+ = ({(\<sigma>, \<sigma>'). (\<forall>v\<in>vars e. \<sigma> v = \<sigma>' v)} \<inter> {(\<sigma>, \<sigma>'). \<sigma> \<in> P \<longrightarrow> \<sigma>' \<in> P})"
  by (rule trancl_id) (auto simp add: trans_def)

lemma assign_value: "ends (P \<inter> {\<sigma>. eval \<sigma> e = v}) \<cdot> x \<leftharpoondown> v \<le>\<^sub>\<pi> ends (P\<lbrakk>x := e\<rbrakk>)"
  apply (simp add: assign_value_def proj_leq_def proj_def)
  apply transfer
  apply simp
  apply (subst fin_l_prod)
  apply (simp add: FIN_def)
  apply blast
  apply simp
  apply (rule Mumble_iso)
  by (auto simp add: image_def Con_def)

lemma proj_SUPR_continuous [simp]:
  fixes f :: "'b \<Rightarrow> 'a trace"
  shows "\<pi> (\<Squnion>v. f v) = (\<Squnion>v. \<pi> (f v))"
  by (simp add: proj_def SUP_def, transfer, simp)

lemma (in complete_lattice) SUPR_mono: "(\<And>x. f x \<le> g x) \<Longrightarrow> (\<Squnion>x. f x) \<le> (\<Squnion>x. g x)"
  by (auto intro: Sup_mono simp: SUP_def)

lemma proj_SUPR_iso:
  fixes f :: "'b \<Rightarrow> 'a trace"
  shows "(\<And>v. \<pi> (f v) \<le> \<pi> (g v)) \<Longrightarrow> (\<Squnion>v. f v) \<le>\<^sub>\<pi> (\<Squnion>v. g v)"
  apply (subst proj_leq_def)
  apply simp
  apply (rule SUPR_mono)
  by auto

lemma rg_iso: "X \<le> Y \<Longrightarrow> \<langle>X\<rangle>\<^sup>\<star> \<le> \<langle>Y\<rangle>\<^sup>\<star>"
  by (metis atomic_iso star_iso)

lemma [dest!]: "LCons (\<sigma>, \<sigma>') xs \<in> Language.star (atomic R) \<Longrightarrow> (\<sigma>, \<sigma>') \<in> R \<and> xs \<in> Language.star (atomic R)"
  apply (erule rev_mp)
  apply (subst star_power)
  apply (metis atom_finite)
  apply (subst star_power)
  apply (metis atom_finite)
  apply (auto simp add: powers_def)
  apply (metis lset_intros(1) rely_power2)
  by (metis lfinite_LCons lset_LCons_subsetD rely_power1 rely_power2 rely_power3 subrelI)

lemma ends_preserving_helper:
      "ys \<in> star (atomic R) \<Longrightarrow>
       snd (llast (LCons (a, b) xs)) \<in> P \<Longrightarrow>
       lfinite ys \<Longrightarrow>
       consistent (LCons (a, b) (xs \<frown> ys)) \<Longrightarrow>
       R `` P \<subseteq> P \<Longrightarrow>
       snd (llast (LCons (a, b) (xs \<frown> ys))) \<in> P"
  apply (subgoal_tac "lfinite ys")
  apply (rotate_tac 5)
  apply (induct ys arbitrary: xs rule: lfinite_induct)
  apply auto
  apply (rename_tac \<sigma> \<sigma>' ys xs)
  apply (subgoal_tac "snd (llast (LCons (a, b) (xs \<frown> LCons (\<sigma>, \<sigma>') LNil))) \<in> P")
  apply (subgoal_tac "consistent (LCons (a, b) ((xs \<frown> LCons (\<sigma>, \<sigma>') LNil) \<frown> ys))")
  apply (metis LCons_lappend_LNil lappend_assoc lappend_code(2))
  apply (metis LCons_lappend_LNil lappend_assoc)
  by (metis fst_conv lappend_code(2) lappend_consistent lappend_inf llast_lappend_LCons llast_singleton rev_ImageI set_rev_mp snd_conv)

lemma ends_preserving: "R `` P \<subseteq> P \<Longrightarrow> ends P \<cdot> \<langle>R\<rangle>\<^sup>\<star> \<le>\<^sub>\<pi> ends P"
  apply (simp add: proj_leq_def proj_def)
  apply transfer
  apply simp
  apply (subst fin_l_prod)
  apply (simp add: FIN_def)
  apply blast
  apply simp
  apply (rule Mumble_iso)
  apply (auto simp add: Con_def)
  apply (metis atomic_star_lfinite)
  by (metis atomic_star_lfinite ends_preserving_helper)

lemma eval_vars_equiv: "\<forall>v\<in>vars e. \<sigma> v = \<sigma>' v \<Longrightarrow> eval \<sigma> e = eval \<sigma>' e"
  apply (induct e)
  by auto

lemma [simp]: "ends P \<cdot> 0 = 0"
  by transfer (auto simp add: l_prod_def FIN_def Mumble_def)

lemma assignment:
  shows "(unchanged (vars e) \<sqinter> preserves P \<sqinter> preserves (P\<lbrakk>x := e\<rbrakk>)), (unchanged (- {x})) \<turnstile> \<lbrace>ends P\<rbrace> x := e \<lbrace>ends (P\<lbrakk>x := e\<rbrakk>)\<rbrace>"
proof (auto simp only: quintuple_def)
  let ?U = "{(\<sigma>, \<sigma>'). (\<forall>v\<in>vars e. \<sigma> v = \<sigma>' v)}"
  let ?P = "{(\<sigma>, \<sigma>'). \<sigma> \<in> P \<longrightarrow> \<sigma>' \<in> P}"
  let ?P' = "{(\<sigma>, \<sigma>'). \<sigma> \<in> P\<lbrakk>x := e\<rbrakk> \<longrightarrow> \<sigma>' \<in> P\<lbrakk>x := e\<rbrakk>}"

  let ?lhs = "ends P \<cdot> (unchanged (vars e) \<sqinter> preserves P \<sqinter> preserves (P\<lbrakk>x := e\<rbrakk>) \<parallel> x := e)"

  have "?lhs = ends P \<cdot> (\<langle>?U \<inter> ?P \<inter> ?P'\<rangle>\<^sup>\<star> \<parallel> (\<Squnion>v. test {\<sigma>. eval \<sigma> e = v} \<cdot> x \<leftharpoondown> v))"
    by (simp add: unchanged_def preserves_def assign_def)
  also have "... = (\<Squnion>v. ends P \<cdot> (\<langle>?U \<inter> ?P \<inter> ?P'\<rangle>\<^sup>\<star> \<parallel> test {\<sigma>. eval \<sigma> e = v} \<cdot> x \<leftharpoondown> v))"
    apply (simp add: SUP_def)
    apply (subst par_inf_dist)
    apply (subst inf_distl)
    defer
    apply (rule arg_cong) back
    by (auto simp add: image_def)
  also have "... \<le> (\<Squnion>v. ends P \<cdot> (\<langle>?U \<inter> ?P \<inter> ?P'\<rangle>\<^sup>\<star> \<parallel> test {\<sigma>. eval \<sigma> e = v}) \<cdot> (\<langle>?U \<inter> ?P \<inter> ?P'\<rangle>\<^sup>\<star> \<parallel> x \<leftharpoondown> v))"
    apply (rule SUPR_mono)
    apply (subst mult_assoc)
    apply (rule mult_isol[rule_format])
    apply (subst rg3)
    apply simp_all
    apply transfer
    by (auto simp add: image_def)
  also have "... = (\<Squnion>v. ends P \<cdot> \<langle>?U \<inter> ?P \<inter> ?P'\<rangle>\<^sup>\<star> \<cdot> test {\<sigma>. eval \<sigma> e = v} \<cdot> \<langle>?U \<inter> ?P \<inter> ?P'\<rangle>\<^sup>\<star> \<cdot> (\<langle>?U \<inter> ?P \<inter> ?P'\<rangle>\<^sup>\<star> \<parallel> x \<leftharpoondown> v))"
    by (simp add: test_def mult_assoc)
  also have "... \<le> (\<Squnion>v. ends P \<cdot> \<langle>?P\<rangle>\<^sup>\<star> \<cdot> test {\<sigma>. eval \<sigma> e = v} \<cdot> \<langle>?U \<inter> ?P \<inter> ?P'\<rangle>\<^sup>\<star> \<cdot> (\<langle>?U \<inter> ?P \<inter> ?P'\<rangle>\<^sup>\<star> \<parallel> x \<leftharpoondown> v))"
    apply (rule SUPR_mono)
    apply (intro mult_isor[rule_format] mult_isol[rule_format] rg_iso)
    by auto
  also have "... \<le>\<^sub>\<pi> (\<Squnion>v. ends P \<cdot> test {\<sigma>. eval \<sigma> e = v} \<cdot> \<langle>?U \<inter> ?P \<inter> ?P'\<rangle>\<^sup>\<star> \<cdot> (\<langle>?U \<inter> ?P \<inter> ?P'\<rangle>\<^sup>\<star> \<parallel> x \<leftharpoondown> v))"
    apply (rule proj_SUPR_iso)
    apply (subst proj_leq_def[symmetric])
    apply (intro proj_mult_iso proj_order_refl)
    apply (rule ends_preserving)
    by auto
  also have "... \<le>\<^sub>\<pi> (\<Squnion>v. ends (P \<inter> {\<sigma>. eval \<sigma> e = v}) \<cdot> \<langle>?U \<inter> ?P \<inter> ?P'\<rangle>\<^sup>\<star> \<cdot> (\<langle>?U \<inter> ?P \<inter> ?P'\<rangle>\<^sup>\<star> \<parallel> x \<leftharpoondown> v))"
    apply (rule proj_SUPR_iso)
    apply (subst proj_leq_def[symmetric])
    apply (intro proj_mult_iso proj_order_refl)
    by (rule ends_test)
  also have "... = (\<Squnion>v. ends (P \<inter> {\<sigma>. eval \<sigma> e = v}) \<cdot> \<langle>?U \<inter> ?P \<inter> ?P'\<rangle>\<^sup>\<star> \<cdot> \<langle>?U \<inter> ?P \<inter> ?P'\<rangle>\<^sup>\<star> \<cdot> x \<leftharpoondown> v \<cdot> \<langle>?U \<inter> ?P \<inter> ?P'\<rangle>\<^sup>\<star>)"
    by (simp add: assign_value_atomic mult_assoc[symmetric])
  also have "... \<le> (\<Squnion>v. ends (P \<inter> {\<sigma>. eval \<sigma> e = v}) \<cdot> \<langle>?U \<inter> ?P \<inter> ?P'\<rangle>\<^sup>\<star> \<cdot> x \<leftharpoondown> v \<cdot> \<langle>?U \<inter> ?P \<inter> ?P'\<rangle>\<^sup>\<star>)"
    by (rule SUPR_mono) (simp add: mult_assoc)
  also have "... \<le> (\<Squnion>v. ends (P \<inter> {\<sigma>. eval \<sigma> e = v}) \<cdot> \<langle>?U \<inter> ?P\<rangle>\<^sup>\<star> \<cdot> x \<leftharpoondown> v \<cdot> \<langle>?U \<inter> ?P \<inter> ?P'\<rangle>\<^sup>\<star>)"
    by (auto intro!: SUPR_mono mult_isol[rule_format] mult_isor[rule_format] rg_iso)
  also have "... \<le>\<^sub>\<pi> (\<Squnion>v. ends (P \<inter> {\<sigma>. eval \<sigma> e = v}) \<cdot> x \<leftharpoondown> v \<cdot> \<langle>?U \<inter> ?P \<inter> ?P'\<rangle>\<^sup>\<star>)"
    apply (rule proj_SUPR_iso)
    apply (subst proj_leq_def[symmetric])
    apply (intro proj_mult_iso proj_order_refl)
    apply (rule ends_preserving)
    apply (auto simp add: image_def)
    by (metis eval_vars_equiv)
  also have "... \<le> (\<Squnion>v. ends (P \<inter> {\<sigma>. eval \<sigma> e = v}) \<cdot> x \<leftharpoondown> v \<cdot> \<langle>?P'\<rangle>\<^sup>\<star>)"
    by (auto intro!: SUPR_mono mult_isol[rule_format] rg_iso)
  also have "... \<le>\<^sub>\<pi> ends (P\<lbrakk>x := e\<rbrakk>) \<cdot> \<langle>?P'\<rangle>\<^sup>\<star>"
    by (simp add: proj_leq_def) (auto intro!: proj_mult_iso assign_value simp add: Sup_le_iff SUP_def proj_leq_def[symmetric])
  also have "... \<le>\<^sub>\<pi> ends (P\<lbrakk>x := e\<rbrakk>)"
    by (rule ends_preserving) (auto simp add: image_def)
  finally show "ends P \<cdot> (unchanged (vars e) \<sqinter> preserves P \<sqinter> preserves (P\<lbrakk>x := e\<rbrakk>) \<parallel> x := e) \<le>\<^sub>\<pi> ends (P\<lbrakk>x := e\<rbrakk>)" .
qed

lemma unchanged_antitone: "Y \<subseteq> X \<Longrightarrow> unchanged X \<le> unchanged Y"
  apply (simp add: unchanged_def)
  apply (rule star_iso[rule_format])
  apply transfer
  apply (rule Mumble_iso)
  apply (simp add: atomic_def)
  by (auto simp add: image_def)

notation
  times (infixl ";" 64)

definition while_inv :: "'a set \<Rightarrow> 'b \<Rightarrow> 'a trace \<Rightarrow> 'a trace" ("WHILE _ INVARIANT _ DO _ WEND" [64,64,64] 63) where
  "WHILE b INVARIANT i DO p WEND = (test b ; p)\<^sup>\<star> ; test b"

end
