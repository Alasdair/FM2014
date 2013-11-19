theory Example2
  imports Trace
begin

datatype state = State nat nat nat nat

datatype variable = IA | FA | IB | FB

datatype expr = Var variable
              | BinOp "nat \<Rightarrow> nat \<Rightarrow> nat" expr expr
              | UnOp "nat \<Rightarrow> nat" expr
              | Val nat

primrec vars :: "expr \<Rightarrow> variable set" where
  "vars (Var n) = {n}"
| "vars (BinOp f e1 e2) = vars e1 \<union> vars e2"
| "vars (UnOp f e) = vars e"
| "vars (Val n) = {}"

fun lookup :: "state \<Rightarrow> variable \<Rightarrow> nat" where
  "lookup (State ia fa ib fb) IA = ia"
| "lookup (State ia fa ib fb) FA = fa"
| "lookup (State ia fa ib fb) IB = ib"
| "lookup (State ia fa ib fb) FB = fb"

primrec eval :: "state \<Rightarrow> expr \<Rightarrow> nat" where
  "eval \<sigma> (Var v) = lookup \<sigma> v"
| "eval \<sigma> (BinOp f e1 e2) = f (eval \<sigma> e1) (eval \<sigma> e2)"
| "eval \<sigma> (UnOp f e) = f (eval \<sigma> e)"
| "eval \<sigma> (Val n) = n"

lift_definition ends :: "'a set \<Rightarrow> 'a trace"
  is "\<lambda>P. {t. lfinite t \<and> t \<noteq> LNil \<and> snd (llast t) \<in> P}" by simp

lemma atomic_iso: "X \<le> Y \<Longrightarrow> \<langle>X\<rangle> \<le> \<langle>Y\<rangle>"
  by transfer auto

lemma ends_test: "ends P \<cdot> test Q \<le>\<^sub>\<pi> ends (P \<inter> Q)"
  sorry

lemma test_ends: "test P \<le> ends P"
  apply (simp add: test_def)
  apply transfer
  apply (simp add: atomic_def)
  apply (rule Mumble_iso)
  by (auto simp add: image_def)

lemma Mumble_empty: "{}\<^sup>\<dagger> = {}"
  by (auto simp add: Mumble_def)

fun update :: "variable \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> state" where
  "update IA ia' (State ia fa ib fb) = (State ia' fa ib fb)"
| "update FA fa' (State ia fa ib fb) = (State ia fa' ib fb)"
| "update IB ib' (State ia fa ib fb) = (State ia fa ib' fb)"
| "update FB fb' (State ia fa ib fb) = (State ia fa ib fb')"

abbreviation assigns_notation :: "state set \<Rightarrow> variable \<Rightarrow> expr \<Rightarrow> state set"
  ("_\<lbrakk>_ := _\<rbrakk>" [100,100,100] 101) where
  "P\<lbrakk>x := e\<rbrakk> \<equiv> (\<lambda>\<sigma>. update x (eval \<sigma> e) \<sigma>) ` P"

definition preserves :: "'a set \<Rightarrow> 'a trace" where
  "preserves P = \<langle>{(\<sigma>, \<sigma>'). \<sigma> \<in> P \<longrightarrow> \<sigma>' \<in> P}\<rangle>\<^sup>\<star>"

lemma preserves_RG [simp,intro!]: "preserves X \<in> RG"
  by (simp add: preserves_def, transfer, auto)

definition unchanged :: "variable set \<Rightarrow> state trace" where
  "unchanged Vars \<equiv> \<langle>{(\<sigma>, \<sigma>'). \<forall>v\<in>Vars. lookup \<sigma> v = lookup \<sigma>' v}\<rangle>\<^sup>\<star>"

lemma unchanged_RG [intro!]: "unchanged X \<in> RG"
  by (simp add: unchanged_def, transfer, auto)

definition decreasing :: "variable set \<Rightarrow> state trace" where
  "decreasing Vars \<equiv> \<langle>{(\<sigma>, \<sigma>'). \<forall>v\<in>Vars. lookup \<sigma> v \<le> lookup \<sigma>' v}\<rangle>\<^sup>\<star>"

lemma atomic_shuffle [simp]: "\<langle>R\<rangle>\<^sup>\<star> \<parallel> \<langle>S\<rangle> = \<langle>R\<rangle>\<^sup>\<star> \<cdot> \<langle>S\<rangle> \<cdot> \<langle>R\<rangle>\<^sup>\<star>"
  sorry

lift_definition atomic_fn :: "(state \<Rightarrow> state) \<Rightarrow> state trace"
  is "\<lambda>f. {LCons (x, f x) LNil |x. True}" by simp

definition assign_value :: "variable \<Rightarrow> nat \<Rightarrow> state trace" (infix "\<leftharpoondown>" 110) where
  "x \<leftharpoondown> v = atomic_fn (update x v)"

definition assign :: "variable \<Rightarrow> expr \<Rightarrow> state trace" (infix ":=" 110) where
  "x := e = (\<Squnion>v. test {\<sigma>. eval \<sigma> e = v} \<cdot> x \<leftharpoondown> v)"

lemma assignment:
  assumes "(x := e) \<le> g"
  shows "(unchanged (vars e) \<sqinter> preserves P \<sqinter> preserves (P\<lbrakk>x := e\<rbrakk>)), g \<turnstile> \<lbrace>ends P\<rbrace> x := e \<lbrace>ends (P\<lbrakk>x := e\<rbrakk>)\<rbrace>"
  sorry

notation
  times (infixr ";//" 63)

no_notation par (infixl "\<parallel>" 69)

notation par (infixr "//\<parallel>" 62)

definition while_inv :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a trace \<Rightarrow> 'a trace" ("WHILE _ //INVARIANT _ //DO _ //WEND" [64,64,64] 63) where
  "WHILE b INVARIANT i DO p WEND = (test b ; p)\<^sup>\<star> ; test b"

definition if_then_else :: "'a set \<Rightarrow> 'a trace \<Rightarrow> 'a trace \<Rightarrow> 'a trace" ("IF _ //THEN _ //ELSE _" [64,64,64] 64) where
  "IF b THEN  p ELSE q = test b \<cdot> p + test b \<cdot> q"

definition LEN :: "nat" where "LEN = 10"

definition array :: "nat \<Rightarrow> nat" where
  "array n = n"

definition loop1_inv :: "(nat \<Rightarrow> bool) \<Rightarrow> state set" where
  "loop1_inv p = {\<sigma>. (\<forall>v. even v \<and> v < lookup \<sigma> IA \<longrightarrow> \<not> p (array v)) \<and> even (lookup \<sigma> IA) \<and> ((p (array (lookup \<sigma> FA)) \<and> lookup \<sigma> FA \<le> LEN) \<or> lookup \<sigma> FA = LEN)}"

definition loop2_inv :: "(nat \<Rightarrow> bool) \<Rightarrow> state set" where
  "loop2_inv p = {\<sigma>. (\<forall>v. odd v \<and> v < lookup \<sigma> IB \<longrightarrow> \<not> p (array v)) \<and> odd (lookup \<sigma> IB) \<and> ((p (array (lookup \<sigma> FB)) \<and> lookup \<sigma> FB \<le> LEN) \<or> lookup \<sigma> FB = LEN)}"


definition FIND :: "(nat \<Rightarrow> bool) \<Rightarrow> state trace" where
  "FIND p \<equiv>
  FA := Val LEN;
  FB := Val LEN;
  ( IA := Val 0;
    WHILE {\<sigma>. lookup \<sigma> IA < lookup \<sigma> FA \<and> lookup \<sigma> IA < lookup \<sigma> FB}
    INVARIANT loop1_inv p
    DO
      IF {\<sigma>. p (array (lookup \<sigma> IA))}
      THEN FA := Var IA
      ELSE IA := BinOp op + (Var IA) (Val 2)
    WEND
  \<parallel> IB := Val 1;
    WHILE {\<sigma>. lookup \<sigma> IB < lookup \<sigma> FA \<and> lookup \<sigma> IB < lookup \<sigma> FB}
    INVARIANT loop2_inv p
    DO
      IF {\<sigma>. p (array (lookup \<sigma> IB))}
      THEN FB := Var IB
      ELSE IB := BinOp op + (Var IB) (Val 2)
    WEND)"

lemma sequential: "r, g \<turnstile> \<lbrace>p\<rbrace> c1 \<lbrace>x\<rbrace> \<Longrightarrow> r, g \<turnstile> \<lbrace>x\<rbrace> c2 \<lbrace>q\<rbrace> \<Longrightarrow> r, g \<turnstile> \<lbrace>p\<rbrace> c1 \<cdot> c2 \<lbrace>q\<rbrace>"
  sorry

lemma while:
  assumes "ends p \<le> ends i"
  and "ends (-b \<inter> i) \<le> ends q"
  and "r, g \<turnstile> \<lbrace>ends (i \<inter> b)\<rbrace> c \<lbrace>ends i\<rbrace>"
  shows "r, g \<turnstile> \<lbrace>ends p\<rbrace> WHILE b INVARIANT i DO c WEND \<lbrace>ends q\<rbrace>"
  sorry

lemma if_then_else:
  assumes "r, g \<turnstile> \<lbrace>ends (p \<inter> b)\<rbrace> c1 \<lbrace>ends q\<rbrace>"
  and "r, g \<turnstile> \<lbrace>ends (p \<inter> - b)\<rbrace> c2 \<lbrace>ends q\<rbrace>"
  shows "r, g \<turnstile> \<lbrace>ends p\<rbrace> IF b THEN c1 ELSE c2 \<lbrace>ends q\<rbrace>"
  sorry

lemma preserves_inter_leq: "x \<le> preserves X \<Longrightarrow> x \<le> preserves Y \<Longrightarrow> x \<le> preserves (X \<inter> Y)"
  sorry

lemma lookup_update [simp]: "lookup (update v x n) v = x"
  by (induct v) (induct n, simp)+

lemma [intro]: "1 \<le> unchanged V"
  sorry

lemma [intro]: "1 \<le> preserves X"
  sorry

lemma [intro]: "1 \<le> decreasing X"
  sorry

lemma [intro]: "decreasing V \<in> RG"
  sorry

lemma [intro]: "\<langle>X\<rangle>\<^sup>\<star> \<in> RG"
  sorry

lemma [intro]: "1 \<in> RG"
  sorry

lemma [intro]: "x \<le> \<langle>UNIV\<rangle>\<^sup>\<star>"
  sorry

lemma assignment_var:
  assumes "P\<lbrakk>x := e\<rbrakk> \<le> Q"
  and "r \<le> unchanged (vars e) \<sqinter> preserves P \<sqinter> preserves (P\<lbrakk>x := e\<rbrakk>)" and "r \<in> RG"
  and "x := e \<le> g" and "g \<in> RG"
  shows "r, g \<turnstile> \<lbrace>ends P\<rbrace> x := e \<lbrace>ends Q\<rbrace>"
  sorry

lemma strengthen_guar: "x \<le> g \<Longrightarrow> g \<in> RG \<Longrightarrow> r, x \<turnstile> \<lbrace>p\<rbrace> c \<lbrace>q\<rbrace> \<Longrightarrow> r, g \<turnstile> \<lbrace>p\<rbrace> c \<lbrace>q\<rbrace>"
  by (auto simp add: quintuple_def proj_leq_def)

lemma weaken_rely: "r \<le> x \<Longrightarrow> r \<in> RG \<Longrightarrow> x, g \<turnstile> \<lbrace>p\<rbrace> c \<lbrace>q\<rbrace> \<Longrightarrow> r, g \<turnstile> \<lbrace>p\<rbrace> c \<lbrace>q\<rbrace>"
  apply (auto simp add: quintuple_def proj_leq_def)
  by (metis mult_isol par_comm par_isor proj_leq_def proj_leq_trans2)

lemma weaken_precondition: "p \<le> x \<Longrightarrow> r, g \<turnstile> \<lbrace>x\<rbrace> c \<lbrace>q\<rbrace> \<Longrightarrow> r, g \<turnstile> \<lbrace>p\<rbrace> c \<lbrace>q\<rbrace>"
  apply (auto simp add: quintuple_def proj_leq_def)
  by (metis mult_isor proj_leq_def proj_leq_trans2)

lemma strengthen_postcondition_proj: "x \<le>\<^sub>\<pi> q \<Longrightarrow> r, g \<turnstile> \<lbrace>p\<rbrace> c \<lbrace>x\<rbrace> \<Longrightarrow> r, g \<turnstile> \<lbrace>p\<rbrace> c \<lbrace>q\<rbrace>"
  by (auto simp add: quintuple_def proj_leq_def)

lemma strengthen_postcondition: "x \<le> q \<Longrightarrow> r, g \<turnstile> \<lbrace>p\<rbrace> c \<lbrace>x\<rbrace> \<Longrightarrow> r, g \<turnstile> \<lbrace>p\<rbrace> c \<lbrace>q\<rbrace>"
  apply (auto simp add: quintuple_def proj_leq_def)
  by (metis order.trans proj_iso)

lemma ends_inter [simp]: "ends P \<sqinter> ends Q = ends (P \<inter> Q)"
  sorry

lemma ends_mono: "P \<subseteq> Q \<Longrightarrow> ends P \<le> ends Q"
  sorry

lemma [intro]: "x \<in> RG \<Longrightarrow> y \<in> RG \<Longrightarrow> x \<sqinter> y \<in> RG"
  sorry

lemma [simp]: "unchanged {} = \<langle>UNIV\<rangle>\<^sup>\<star>"
  apply (simp add: unchanged_def)
  apply (rule arg_cong) back back
  by auto

lemma rg_mono: "X \<le> Y \<Longrightarrow> \<langle>X\<rangle>\<^sup>\<star> \<le> \<langle>Y\<rangle>\<^sup>\<star>"
  sorry

lemma [intro]: "x \<notin> V \<Longrightarrow> x := v \<le> unchanged V"
  sorry

lemma [intro]: "x \<notin> V \<Longrightarrow> x := v \<le> decreasing V"
  sorry

lemma preserves_empty [simp]: "preserves {} = \<langle>UNIV\<rangle>\<^sup>\<star>"
  by (auto intro: arg_cong simp add: preserves_def)

lemma rg_inter: "trans X \<Longrightarrow> trans Y \<Longrightarrow> \<langle>X\<rangle>\<^sup>\<star> \<sqinter> \<langle>Y\<rangle>\<^sup>\<star> = \<langle>X \<inter> Y\<rangle>\<^sup>\<star>"
  by transfer (metis Mumble_atomic Mumble_atomic_star rely_inter trancl_id)

lemma "1, \<langle>UNIV\<rangle>\<^sup>\<star> \<turnstile> \<lbrace>ends UNIV\<rbrace> FIND P \<lbrace>ends {\<sigma>. P (array (min (lookup \<sigma> FA) (lookup \<sigma> FB))) \<or> (lookup \<sigma> FA = LEN \<and> lookup \<sigma> FB = LEN)}\<rbrace>"
  apply (simp add: FIND_def)

  (* First two assignments *)
  apply (rule_tac x = "ends {\<sigma>. lookup \<sigma> FA = LEN}" in sequential)
  apply (rule assignment_var)
    apply (auto simp add: image_def)
  apply (rule_tac x = "ends {\<sigma>. lookup \<sigma> FA = LEN \<and> lookup \<sigma> FB = LEN}" in sequential)
  apply (rule assignment_var)
    apply (auto simp add: image_def)
    apply (metis lookup.simps(2) state.exhaust update.simps(4))

  (* Weakening and strengthening to apply parallel *)
  apply (rule_tac x = "decreasing {FA} \<sqinter> unchanged {IB, FB} \<parallel> decreasing {FB} \<sqinter> unchanged {IA, FA}" in strengthen_guar)
    apply auto
  apply (rule_tac x = "(decreasing {FB} \<sqinter> unchanged {IA, FA}) \<sqinter> (decreasing {FA} \<sqinter> unchanged {IB, FB})" in weaken_rely)
    apply auto
    apply (rule_tac x = "ends {\<sigma>. lookup \<sigma> FA = LEN} \<sqinter> ends {\<sigma>. lookup \<sigma> FB = LEN}" in weaken_precondition)
    apply (force intro: ends_mono)
  apply (rule_tac x = "ends (loop1_inv P \<inter> - {\<sigma>. lookup \<sigma> IA < lookup \<sigma> FA \<and> lookup \<sigma> IA < lookup \<sigma> FB})
                     \<sqinter> ends (loop2_inv P \<inter> - {\<sigma>. lookup \<sigma> IB < lookup \<sigma> FA \<and> lookup \<sigma> IB < lookup \<sigma> FB})" in strengthen_postcondition)
    apply (subst ends_inter)
    apply (rule ends_mono)
    apply (simp add: loop1_inv_def loop2_inv_def)
    apply clarify
    apply (metis min_def min_max.inf_absorb2)

  (* Ready to apply parallel *)
  apply (rule parallel)

    (* First loop *)
  apply (rule_tac x = "ends {\<sigma>. lookup \<sigma> FA = LEN \<and> lookup \<sigma> IA = 0}" in sequential)
  apply (rule assignment_var)
    apply (simp add: image_def)
    apply clarify
    apply (metis lookup.simps(2) lookup_update state.exhaust update.simps(1))
    apply (rule le_infI2)
    apply simp
    apply (intro conjI)
    apply force
    apply (simp add: unchanged_def preserves_def)
    apply (rule rg_mono)
    apply force
    apply (simp add: unchanged_def preserves_def)
    apply (rule rg_mono)
    apply (simp add: image_def)
    apply clarify
    apply (metis lookup.simps(1) lookup.simps(2) state.exhaust update.simps(1))
    apply force
    apply simp
    apply (intro conjI)
    apply force
    apply force
    apply force
  apply (rule while)
    apply (rule ends_mono)
    apply (simp add: loop1_inv_def)
    apply clarify
    apply (metis even_zero_nat less_nat_zero_code)
    apply (rule ends_mono)
    apply (simp add: loop1_inv_def)
    apply (rule if_then_else)
      apply (rule assignment_var)
      apply (simp add: loop1_inv_def image_def)
      apply clarify
      apply (rule_tac y = xa in state.exhaust)
      apply simp
      apply (metis dual_order.strict_trans not_less)
      apply (simp add: decreasing_def unchanged_def)
      apply (intro conjI)
      apply (subst rg_inter)
      apply (simp add: trans_def)
      apply (simp add: trans_def)
      apply (rule rg_mono)
      apply blast
      apply (simp add: preserves_def)
      apply (subst rg_inter)
      apply (simp add: trans_def)
      apply (simp add: trans_def)
      apply (rule rg_mono)
      apply clarify
      apply (simp add: loop1_inv_def)
      apply (simp add: preserves_def)
      apply (subst rg_inter)
      apply (simp add: trans_def)
      apply (simp add: trans_def)
      apply (rule rg_mono)
      apply safe
      apply (simp add: loop1_inv_def image_def)
      apply clarify
      apply (rule_tac y = b in state.exhaust)
      apply (rule_tac y = \<sigma> in state.exhaust)
      apply simp
      apply (rule_tac x = "State nat2 nat2a nat3 nat4" in bexI)
      apply simp
      apply simp
      apply blast
      defer
      apply blast
      apply (rule assignment_var)
      apply (simp add: loop1_inv_def image_def)
      apply clarify
      apply (rule_tac y = xa in state.exhaust)
      apply simp
      apply clarify
      apply (metis dual_order.order_iff_strict even_Suc le_less_linear not_less_eq)
      apply simp
      apply (intro conjI)
      apply (simp add: unchanged_def decreasing_def)
      apply (subst rg_inter)
      apply (simp add: trans_def)
      apply (simp add: trans_def)
      apply (rule rg_mono)
      apply blast
      apply (simp add: unchanged_def decreasing_def preserves_def)
      apply (subst rg_inter)
      apply (simp add: trans_def)
      apply (simp add: trans_def)
      apply (rule rg_mono)      
      apply (simp add: loop1_inv_def)
      apply clarify
      apply (metis dual_order.strict_trans1)
      apply (simp add: unchanged_def decreasing_def preserves_def)
      apply (subst rg_inter)
      apply (simp add: trans_def)
      apply (simp add: trans_def)
      apply (rule rg_mono)      
      apply (simp add: loop1_inv_def)
      apply clarify
      apply (rule_tac y = a in state.exhaust)
      apply (rule_tac y = b in state.exhaust)
      apply (rule_tac y = \<sigma> in state.exhaust)
      apply (simp add: image_def)
      apply (erule_tac x = "State nat1b nat2a nat3a nat4a" in ballE)
      apply clarsimp
      apply simp
      apply blast
      defer
      apply blast

  (* Second loop *)
  apply (rule_tac x = "ends {\<sigma>. lookup \<sigma> FB = LEN \<and> lookup \<sigma> IB = 1}" in sequential)
  apply (rule assignment_var)
    apply (simp add: image_def)
    apply clarify
    apply (metis lookup.simps(4) lookup_update state.exhaust update.simps(3))
    apply (rule le_infI2)
    apply simp
    apply (intro conjI)
    apply force
    apply (simp add: unchanged_def preserves_def)
    apply (rule rg_mono)
    apply force
    apply (simp add: unchanged_def preserves_def)
    apply (rule rg_mono)
    apply (simp add: image_def)
    apply clarify
    apply (metis lookup.simps(3) lookup.simps(4) state.exhaust update.simps(3))
    apply force
    apply simp
    apply (intro conjI)
    apply force
    apply force
    apply force
  apply (rule while)
    apply (rule ends_mono)
    apply (simp add: loop2_inv_def)
    apply clarify
    apply (metis even_Suc even_zero_nat less_Suc0)
    apply (rule ends_mono)
    apply (simp add: loop1_inv_def)
    apply (rule if_then_else)
      apply (rule assignment_var)
      apply (simp add: loop2_inv_def image_def)
      apply clarify
      apply (rule_tac y = xa in state.exhaust)
      apply simp
      apply (metis dual_order.strict_trans1 linear)
      apply (simp add: decreasing_def unchanged_def)
      apply (intro conjI)
      apply (subst rg_inter)
      apply (simp add: trans_def)
      apply (simp add: trans_def)
      apply (rule rg_mono)
      apply blast
      apply (simp add: preserves_def)
      apply (subst rg_inter)
      apply (simp add: trans_def)
      apply (simp add: trans_def)
      apply (rule rg_mono)
      apply clarify
      apply (simp add: loop2_inv_def)
      apply (simp add: preserves_def)
      apply (subst rg_inter)
      apply (simp add: trans_def)
      apply (simp add: trans_def)
      apply (rule rg_mono)
      apply safe
      apply (simp add: loop2_inv_def image_def)
      apply clarify
      apply (rule_tac y = b in state.exhaust)
      apply (rule_tac y = \<sigma> in state.exhaust)
      apply simp
      apply (rule_tac x = "State nat1 nat2 nat3 nat4a" in bexI)
      apply simp_all
      apply blast
      defer
      apply blast
      apply (rule assignment_var)
      apply (simp add: loop2_inv_def image_def)
      apply clarify
      apply (rule_tac y = xa in state.exhaust)
      apply simp
      apply clarify
      apply (metis dual_order.order_iff_strict even_Suc le_less_linear not_less_eq)
      apply simp
      apply (intro conjI)
      apply (simp add: unchanged_def decreasing_def)
      apply (subst rg_inter)
      apply (simp add: trans_def)
      apply (simp add: trans_def)
      apply (rule rg_mono)
      apply blast
      apply (simp add: unchanged_def decreasing_def preserves_def)
      apply (subst rg_inter)
      apply (simp add: trans_def)
      apply (simp add: trans_def)
      apply (rule rg_mono)      
      apply (simp add: loop2_inv_def)
      apply clarify
      apply (metis dual_order.strict_trans1)
      apply (simp add: unchanged_def decreasing_def preserves_def)
      apply (subst rg_inter)
      apply (simp add: trans_def)
      apply (simp add: trans_def)
      apply (rule rg_mono)    
      apply (simp add: loop2_inv_def)
      apply clarify
      apply (rule_tac y = a in state.exhaust)
      apply (rule_tac y = b in state.exhaust)
      apply (rule_tac y = \<sigma> in state.exhaust)
      apply (simp add: image_def)
      apply (erule_tac x = "State nat1a nat2a nat3b nat4a" in ballE)
      apply clarsimp
      apply simp
      apply blast
      defer
      apply blast

  (* Simple atomic goals *)
  apply safe
  defer
  sorry

