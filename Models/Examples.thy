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

lemma ends_preserves: "ends P \<cdot> preserves P \<le> ends P"
  apply (simp add: preserves_def)
  apply transfer
  apply simp
  apply (rule Mumble_iso)
  sorry

lemma atomic_iso: "X \<le> Y \<Longrightarrow> \<langle>X\<rangle> \<le> \<langle>Y\<rangle>"
  by transfer auto

lemma ends_test: "ends P \<cdot> test P = ends P"
  sorry

lemma test_ends: "test P \<le> ends P"
  apply (simp add: test_def)
  apply transfer
  apply (simp add: atomic_def)
  apply (rule Mumble_iso)
  by (auto simp add: image_def)

lemma ends_right: "x\<cdot>0 = 0 \<Longrightarrow> x \<cdot> ends P \<le> ends P"
  apply transfer
  apply simp
  sorry

lemma Mumble_empty: "{}\<^sup>\<dagger> = {}"
  by (auto simp add: Mumble_def)

lemma [simp]: "lfinite xs \<Longrightarrow> llast (LCons x (xs \<frown> LCons y ys)) = llast (LCons y ys)"
  by (metis lappend_code(2) lfinite_LCons llast_lappend_LCons)

(*
lemma assign1: "\<forall>\<sigma>\<in>P. eval \<sigma> expr = v \<Longrightarrow> ends P \<cdot> x := expr \<le>\<^sub>\<pi> ends {\<sigma>. \<sigma> x = v}"
  apply (simp add: assign_def proj_leq_def proj_def)
  apply transfer
  apply simp
  apply (rule Mumble_iso)
  apply (subst fin_l_prod)
  apply (simp add: FIN_def)
  apply blast
  by (auto simp add: Con_def)
*)

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

lemma assignment:
  shows "(unchanged ({x} \<union> vars e) \<sqinter> preserves P \<sqinter> preserves (P\<lbrakk>x := e\<rbrakk>)), (unchanged (- {x})) \<turnstile> \<lbrace>ends P\<rbrace> x := e \<lbrace>ends (P\<lbrakk>x := e\<rbrakk>)\<rbrace>"
proof (auto simp only: quintuple_def)
  let ?P = "preserves P"
  let ?P' = "preserves (P\<lbrakk>x := e\<rbrakk>)" 

  have "ends P \<cdot> ((unchanged ({x} \<union> vars e) \<sqinter> ?P \<sqinter> ?P') \<parallel> x := e) = ends P \<cdot> ((unchanged ({x} \<union> vars e) \<sqinter> ?P \<sqinter> ?P') \<parallel> (\<Squnion>v. test {\<sigma>. eval \<sigma> e = v} \<cdot> x \<leftharpoondown> v))"
    by (simp only: assign_def)
  also have "... = (\<Squnion>v. ends P \<cdot> ((unchanged ({x} \<union> vars e) \<sqinter> ?P \<sqinter> ?P') \<parallel> test {\<sigma>. eval \<sigma> e = v} \<cdot> x \<leftharpoondown> v))"
    sorry
  also have "... = (\<Squnion>v. ends P \<cdot> ((unchanged ({x} \<union> vars e) \<sqinter> ?P \<sqinter> ?P') \<parallel> test {\<sigma>. eval \<sigma> e = v}) \<cdot> ((unchanged ({x} \<union> vars e) \<sqinter> ?P \<sqinter> ?P') \<parallel> x \<leftharpoondown> v))"
    sorry
  also have "... = (\<Squnion>v. ends P \<cdot> (?P \<cdot> test {\<sigma>. eval \<sigma> e = v} \<cdot> )

(*
proof (auto simp add: quintuple_def)
*)
sorry

lemma [simp]: "\<langle>R\<rangle>\<^sup>\<star> \<parallel> \<langle>S\<rangle>\<^sup>\<star> = (\<langle>R\<rangle>\<^sup>\<star> \<cdot> \<langle>S\<rangle>\<^sup>\<star>)\<^sup>\<star>"
  sorry

lemma "unchanged (- {x}) \<parallel> unchanged (- {y}) = unchanged (- {x, y})"
  sorry

lemma unchanged_antitone: "Y \<subseteq> X \<Longrightarrow> unchanged X \<le> unchanged Y"
  apply (simp add: unchanged_def)
  apply (rule star_iso[rule_format])
  apply transfer
  apply (rule Mumble_iso)
  apply (simp add: atomic_def)
  by (auto simp add: image_def)

lemma "ends P \<sqinter> ends Q = ends (P \<sqinter> Q)"
  apply transfer
  apply simp
  sorry

lemma
  assumes "({x} \<union> vars e1) \<inter> ({y} \<union> vars e2) = {}"
  and "P\<lbrakk>x := e1\<rbrakk> \<inter> P\<lbrakk>y := e2\<rbrakk> \<subseteq> Q"
  shows "(unchanged ({x,y} \<union> vars e1 \<union> vars e2)), (unchanged (- {x, y})) \<turnstile> \<lbrace>ends P\<rbrace> x := e1 \<parallel> y := e2 \<lbrace>ends Q\<rbrace>"

lemma
  assumes "x \<noteq> y" and "({x} \<union> vars e1) \<inter> ({y} \<union> vars e2) = {}"
  shows "((unchanged ({x} \<union> vars e1)) \<sqinter> (unchanged ({y} \<union> vars e2))), (unchanged (- {x}) \<parallel> unchanged (- {y})) \<turnstile> \<lbrace>ends P \<sqinter> ends P\<rbrace> x := e1 \<parallel> y := e2 \<lbrace>ends (P\<lbrakk>x := e1\<rbrakk>) \<sqinter> ends (P\<lbrakk>y := e2\<rbrakk>)\<rbrace>"
  using assms
  apply -
  apply (rule parallel)
  apply (rule assignment)
  apply (rule order_refl)
  apply (rule unchanged_antitone)
  apply blast
  apply (rule assignment)
  apply (rule order_refl)
  apply (rule unchanged_antitone)
  by blast

  notation
    times (infixl ";" 64)

  definition while_inv :: "'a set \<Rightarrow> 'b \<Rightarrow> 'a trace \<Rightarrow> 'a trace" ("WHILE _ INVARIANT _ DO _ WEND" [64,64,64] 63) where
    "WHILE b INVARIANT i DO p WEND = (test b ; p)\<^sup>\<star> ; test b"

  definition par_rg :: "'b \<Rightarrow> 'a trace \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'a trace \<Rightarrow> 'b \<Rightarrow> 'a trace"
    ("COBEGIN RELY _ DO _ GUAR _ RELY _ DO _ GUAR _ COEND" [64,64,64,64,64,64] 63) where
    "COBEGIN RELY r1 DO p1 GUAR g1 RELY r2 DO p2 GUAR g2 COEND \<equiv> p1 \<parallel> p2"


end
