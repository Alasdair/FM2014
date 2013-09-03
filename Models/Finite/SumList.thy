theory SumList
  imports Main
begin

(* This is probably in the standard libraries... *)

primrec sum_elim :: "('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'a + 'b \<Rightarrow> 'c" ("\<langle>_,_\<rangle>" [0,0] 1000) where
  "sum_elim f g (Inl x) = f x"
| "sum_elim f g (Inr x) = g x"

fun lefts :: "('a + 'b) list \<Rightarrow> 'a list" ("\<ll>") where
  "lefts [] = []"
| "lefts (Inl x # zs) = x # lefts zs"
| "lefts (Inr y # zs) = lefts zs"

fun rights :: "('a + 'b) list \<Rightarrow> 'b list" ("\<rr>") where
  "rights [] = []"
| "rights (Inl x # zs) = rights zs"
| "rights (Inr y # zs) = y # rights zs"

lemma rights_mapR [simp]: "\<rr> (map Inr xs) = xs"
  by (induct xs) auto

lemma lefts_mapL [simp]: "\<ll> (map Inl xs) = xs"
  by (induct xs) auto

lemma rights_mapL [simp]: "\<rr> (map Inl xs) = []"
  by (induct xs) auto

lemma lefts_mapR [simp]: "\<ll> (map Inr xs) = []"
  by (induct xs) auto

fun swap :: "('a + 'b) \<Rightarrow> ('b, 'a) sum" where
  "swap (Inl x) = Inr x"
| "swap (Inr x) = Inl x"

lemma sum_list_induct: "\<lbrakk>P []; \<And>x xs. P xs \<Longrightarrow> P (Inl x # xs); \<And>x xs. P xs \<Longrightarrow> P (Inr x # xs)\<rbrakk> \<Longrightarrow> P xs"
  by (induct xs, auto, metis swap.cases)

lemma sum_list_cases: "\<lbrakk>P []; \<And>x xs. P (Inl x # xs); \<And>x xs. P (Inr x # xs)\<rbrakk> \<Longrightarrow> P xs"
  by (induct xs rule: sum_list_induct) auto

lemma [simp]: "\<rr> (map swap xs) = \<ll> xs"
  by (induct xs rule: sum_list_induct) auto

lemma [simp]: "\<ll> (map swap xs) = \<rr> xs"
  by (induct xs rule: sum_list_induct) auto

lemma [simp]: "\<langle>id,id\<rangle> (swap x) = \<langle>id,id\<rangle> x"
  by (cases x) auto

lemma no_lefts: "\<ll> xs = [] \<Longrightarrow> map Inr (\<rr> xs) = xs"
  by (induct xs rule: sum_list_induct) auto

lemma no_rights: "rights xs = [] \<Longrightarrow> map Inl (\<ll> xs) = xs"
  by (induct xs rule: sum_list_induct) auto

fun rbr1 :: "'a + ('b + 'c) \<Rightarrow> ('a + 'b) + 'c" where
  "rbr1 (Inl x) = Inl (Inl x)"
| "rbr1 (Inr (Inl x)) = Inl (Inr x)"
| "rbr1 (Inr (Inr x)) = Inr x"

lemma sum3_list_induct1: "\<lbrakk>P []; \<And>x xs. P xs \<Longrightarrow> P (Inl x # xs); \<And>x xs. P xs \<Longrightarrow> P (Inr (Inl x) # xs); \<And>x xs. P xs \<Longrightarrow> P (Inr (Inr x) # xs)\<rbrakk> \<Longrightarrow> P xs"
  by (induct xs, auto, metis swap.cases)

lemma sum3_list_induct2: "\<lbrakk>P []; \<And>x xs. P xs \<Longrightarrow> P (Inr x # xs); \<And>x xs. P xs \<Longrightarrow> P (Inl (Inr x) # xs); \<And>x xs. P xs \<Longrightarrow> P (Inl (Inl x) # xs)\<rbrakk> \<Longrightarrow> P xs"
  by (induct xs, auto, metis swap.cases)

fun rbr2 :: "('a + 'b) + 'c \<Rightarrow> 'a + ('b + 'c)" where
  "rbr2 (Inr x) = Inr (Inr x)"
| "rbr2 (Inl (Inr x)) = Inr (Inl x)"
| "rbr2 (Inl (Inl x)) = Inl x"

lemma [simp]: "lefts (lefts (map rbr1 xs)) = lefts xs"
  by (induct xs rule: sum3_list_induct1) auto

lemma [simp]: "rights (lefts (map rbr1 xs)) = lefts (rights xs)"
  by (induct xs rule: sum3_list_induct1) auto

lemma [simp]: "rights (map rbr1 xs) = rights (rights xs)"
  by (induct xs rule: sum3_list_induct1) auto

lemma [simp]: "sum_elim (sum_elim id id) id (rbr1 x) = sum_elim id (sum_elim id id) x"
  apply (cases x)
  apply auto
  by (metis rbr1.simps(2) rbr1.simps(3) sum_elim.simps(1) sum_elim.simps(2) swap.cases)

lemma [simp]: "rights (rights (map rbr2 xs)) = rights xs"
  by (induct xs rule: sum3_list_induct2) auto

lemma [simp]: "lefts (rights (map rbr2 xs)) = rights (lefts xs)"
  by (induct xs rule: sum3_list_induct2) auto

lemma [simp]: "lefts (map rbr2 xs) = lefts (lefts xs)"
  by (induct xs rule: sum3_list_induct2) auto

lemma [simp]: "sum_elim id (sum_elim id id) (rbr2 x) = sum_elim (sum_elim id id) id x"
  apply (cases x)
  apply auto
  by (metis id_def rbr2.simps(2) rbr2.simps(3) sum_elim.simps(1) sum_elim.simps(2) swap.cases)

lemma left_append [simp]: "\<ll> (xs @ ys) = \<ll> xs @ \<ll> ys"
  by (induct xs rule: sum_list_induct) auto

lemma right_append [simp]: "\<rr> (xs @ ys) = \<rr> xs @ \<rr> ys"
  by (induct xs rule: sum_list_induct) auto

lemma sum_ext:
  assumes "\<And>x. f (Inl x) = g (Inl x)"
  and "\<And>x. f (Inr x) = g (Inr x)"
  shows "f = g"
proof -
  {
    fix x
    have "f x = g x"
      by (cases x, auto intro: assms)
  }
  thus ?thesis by auto
qed

lemma sum_elim_split: "\<langle>Inl \<circ> f, Inr \<circ> g\<rangle> = \<langle>Inl \<circ> f, Inr\<rangle> \<circ> \<langle>Inl, Inr \<circ> g\<rangle>"
  by (rule sum_ext, auto)

lemma sum_elim_id: "sum_elim Inl Inr = id"
proof -
  {
    fix x :: "('a + 'b)"
    have "sum_elim Inl Inr x = id x"
      by (cases x) auto
  }
  thus ?thesis by auto
qed

fun rfl :: "('a + 'b) list \<Rightarrow> ('a + 'b) list" where
  "rfl [] = []"
| "rfl ((Inl x)#xs) = xs"
| "rfl ((Inr x)#xs) = rfl xs"

fun rfr :: "('a + 'b) list \<Rightarrow> ('a + 'b) list" where
  "rfr [] = []"
| "rfr ((Inr x)#xs) = xs"
| "rfr ((Inl x)#xs) = rfr xs"

lemma rfl1 [intro]: "lefts z = x # xs \<Longrightarrow> lefts (rfl z) = xs"
  by (induct z rule: sum_list_induct, auto)

lemma rfr1 [intro]: "rights z = x # xs \<Longrightarrow> rights (rfr z) = xs"
  by (induct z rule: sum_list_induct, auto)

lemma map_sum_elim_simp1: "map \<langle>id,id\<rangle> \<circ> map \<langle>Inl \<circ> \<langle>id,id\<rangle>, Inr\<rangle> = map \<langle>\<langle>id,id\<rangle>,id\<rangle>"
proof -
  {
    fix xs :: "(('a, 'a) sum, 'a) sum list"
    have "(map \<langle>id,id\<rangle> \<circ> map \<langle>Inl \<circ> \<langle>id,id\<rangle>, Inr\<rangle>) xs = map \<langle>\<langle>id,id\<rangle>,id\<rangle> xs"
      by (induct xs rule: sum3_list_induct2) auto
  }
  thus ?thesis by auto
qed

lemma map_sum_elim_simp2: "map \<langle>id,id\<rangle> \<circ> map \<langle>Inl, Inr \<circ> \<langle>id,id\<rangle>\<rangle> = map \<langle>id,\<langle>id,id\<rangle>\<rangle>"
proof -
  {
    fix xs :: "('a, ('a, 'a) sum) sum list"
    have "(map \<langle>id,id\<rangle> \<circ> map \<langle>Inl, Inr \<circ> \<langle>id,id\<rangle>\<rangle>) xs = map \<langle>id,\<langle>id,id\<rangle>\<rangle> xs"
      by (induct xs rule: sum3_list_induct1) auto
  }
  thus ?thesis by auto
qed

fun take_left :: "nat \<Rightarrow> ('a + 'b) list \<Rightarrow> ('a + 'b) list" where
  "take_left n [] = []"
| "take_left 0 ((Inl x) # xs) = []"
| "take_left n ((Inr x) # xs) = Inr x # take_left n xs"
| "take_left (Suc n) ((Inl x) # xs) = Inl x # take_left n xs"

value "take_left 2 [Inl a, Inr b, Inl c, Inr d, Inl e]"

fun drop_left :: "nat \<Rightarrow> ('a + 'b) list \<Rightarrow> ('a + 'b) list" where
  "drop_left n [] = []"
| "drop_left n ((Inr x) # xs) = drop_left n xs"
| "drop_left 0 ((Inl x) # xs) = Inl x # xs"
| "drop_left (Suc n) ((Inl x) # xs) = drop_left n xs"

definition delete_left :: "nat \<Rightarrow> ('a + 'b) list \<Rightarrow> ('a + 'b) list" where
  "delete_left n xs = take_left n xs @ tl (drop_left n xs)"

lemma sum_list_induct_with_n:
  "\<lbrakk> P 0 []; \<And>n. P (Suc n) []
   ; \<And>x xs. (\<And>n. P n xs) \<Longrightarrow> P 0 (Inl x # xs); \<And>x xs. (\<And>n. P n xs) \<Longrightarrow> P 0 (Inr x # xs)
   ; \<And>n x xs. (\<And>n. P n xs) \<Longrightarrow> P (Suc n) (Inl x # xs); \<And>n x xs. (\<And>n. P n xs) \<Longrightarrow> P (Suc n) (Inr x # xs)
   \<rbrakk> \<Longrightarrow> P n xs"
  by (induct xs arbitrary: n rule: sum_list_induct) (metis nat.exhaust)+

lemma left_take_flip: "\<ll> (take_left n xs) = take n (\<ll> xs)"
  by (induct xs rule: sum_list_induct_with_n, auto)

lemma left_drop_flip: "\<ll> (drop_left n xs) = drop n (\<ll> xs)"
  by (induct xs rule: sum_list_induct_with_n, auto)

lemma take_drop_left: "take_left n xs @ drop_left n xs = xs"
  by (induct xs rule: sum_list_induct_with_n, auto)

lemma take_left_idem: "take_left n (take_left n xs) = take_left n xs"
  by (induct xs rule: sum_list_induct_with_n, auto)

lemma take_all_left: "(take_left (length (\<ll> xs)) xs) = xs"
  by (induct xs rule: sum_list_induct, auto)

lemma take_take_append: "n \<le> length (\<ll> xs) \<Longrightarrow> take_left n (take_left n xs @ (Inl y) # ys) = take_left n xs" 
  by (induct xs rule: sum_list_induct_with_n, auto)

lemma lefts_non_empty: "\<ll> xs \<noteq> [] \<Longrightarrow> xs \<noteq> []"
  by (induct xs) auto

lemma rights_non_empty: "\<rr> xs \<noteq> [] \<Longrightarrow> xs \<noteq> []"
  by (induct xs) auto

lemma cons_non_empty: "xs = y#ys \<Longrightarrow> xs \<noteq> []"
  by (metis list.distinct(1))

lemma delete_left_rights [simp]: "\<rr> (delete_left n xs) = \<rr> xs"
  by (induct xs rule: sum_list_induct_with_n) (auto simp add: delete_left_def)

lemma drop_left_append_non_empty: "\<ll> ws = xs @ y # ys \<Longrightarrow> drop_left (length xs) ws \<noteq> []"
  apply (induct xs)
  apply simp
  apply (induct ws rule: sum_list_induct)
  apply simp
  apply simp
  apply simp
  by (metis append_eq_conv_conj left_drop_flip lefts.simps(1) list.distinct(1))

lemma [simp]: "map (\<langle>id,id\<rangle> \<circ> Inr) xs = xs"
  by (metis (lifting, mono_tags) id_apply map_eq_conv map_ident o_eq_dest_lhs sum_elim.simps(2))

lemma [simp]: "map (\<langle>id,id\<rangle> \<circ> Inl) xs = xs"
  by (induct xs, auto)

lemma empty_left: "\<ll> xs = [] \<Longrightarrow> \<rr> xs = map \<langle>id,id\<rangle> xs"
  by (induct xs rule: sum_list_induct) auto

lemma drop_head: "\<ll> ws = xs @ (y # ys) \<Longrightarrow> hd (drop_left (length xs) ws) = Inl y"
proof (induct ws arbitrary: xs rule: sum_list_induct, simp_all)
  fix w :: "'a" and ws :: "('a + 'b) list" and xs :: "'a list"
  assume ih: "\<And>xs. \<ll> ws = xs @ y # ys \<Longrightarrow> hd (drop_left (length xs) ws) = Inl y"
  and ws_lefts: "w # (\<ll> ws) = xs @ y # ys"
  thus "hd (drop_left (length xs) (Inl w # ws)) = Inl y"
  proof (cases "length xs = 0", simp)
    assume "length xs \<noteq> 0"
    then obtain x and xs' where xs_def: "xs = x # xs'"
      by (metis gen_length_code(1) length_code neq_Nil_conv)
    thus "hd (drop_left (length xs) (Inl w # ws)) = Inl y"
      by simp (metis Cons_eq_appendI ws_lefts ih list.inject)
  qed
qed

lemma left_singleton [simp]: "map \<langle>id,id\<rangle> [Inl x] = [x]"
  by simp

lemma delete_left_lefts: "\<ll> ws = xs @ y # ys \<Longrightarrow> \<ll> (delete_left (length xs) ws) = xs @ ys"
proof (induct ws arbitrary: xs rule: sum_list_induct, simp_all add: delete_left_def)
  fix w :: "'a" and ws :: "('a + 'b) list" and xs :: "'a list"
  assume ih: "\<And>xs. \<ll> ws = xs @ y # ys \<Longrightarrow> \<ll> (take_left (length xs) ws) @ \<ll> (tl (drop_left (length xs) ws)) = xs @ ys"
  and ws_lefts: "w # \<ll> ws = xs @ y # ys"
  thus "\<ll> (take_left (length xs) (Inl w # ws)) @ \<ll> (tl (drop_left (length xs) (Inl w # ws))) = xs @ ys"
  proof (cases "length xs = 0", simp)
    assume "length xs \<noteq> 0"
    then obtain x and xs' where xs_def: "xs = x # xs'"
      by (metis list.size(3) neq_Nil_conv)
    thus "\<ll> (take_left (length xs) (Inl w # ws)) @ \<ll> (tl (drop_left (length xs) (Inl w # ws))) = xs @ ys"
      by simp (metis append_Cons ih list.inject ws_lefts)
  qed
qed

lemma lefts_insert:
  assumes "\<ll> ws = xs @ [y] @ ys"
  and "\<rr> ws = zs"
  and "n = length xs"
  shows "ws = take_left n ws @ [Inl y] @ tl (drop_left n ws)"
proof -
  have "ws = take_left n ws @ drop_left n ws"
    by (metis take_drop_left)
  also have "... = take_left n ws @ hd (drop_left n ws) # tl (drop_left n ws)"
    apply (subst hd_Cons_tl)
    apply (insert assms)
    apply simp
    apply (rule drop_left_append_non_empty)
    apply auto
    done
  also have "... = take_left n ws @ Inl y # tl (drop_left n ws)"
    by (metis append_Cons assms(1) assms(3) drop_head)
  also have "... = take_left n ws @ [Inl y] @ tl (drop_left n ws)"
    by auto
  finally show ?thesis .
qed

lemma take_lefts_is_append: "\<ll> xs = ys @ zs \<Longrightarrow> \<ll> (take_left (length ys) xs) = ys"
  apply (induct xs rule: sum_list_induct)
  apply auto
  apply (cases "length ys = 0")
  apply simp
  by (metis append_eq_conv_conj left_take_flip lefts.simps(2))

lemma drop_lefts_is_append: "\<ll> zs' = as @ d # ds \<Longrightarrow> \<ll> (tl (drop_left (length as) zs')) = ds"
  apply (induct zs' arbitrary: as rule: sum_list_induct)
  apply auto
proof -
  fix x :: "'a" and xs :: "('a + 'b) list" and as :: "'a list"
  assume ih: "\<And>as. \<ll> xs = as @ d # ds \<Longrightarrow> \<ll> (tl (drop_left (length as) xs)) = ds"
  and xs_lefts: "x # \<ll> xs = as @ d # ds"
  thus "\<ll> (tl (drop_left (length as) (Inl x # xs))) = ds"
  proof (cases "length as = 0", simp)
    assume "length as \<noteq> 0"
    then obtain a and as' where as_def: "as = a # as'"
      by (metis length_0_conv neq_Nil_conv)
    thus "\<ll> (tl (drop_left (length as) (Inl x # xs))) = ds"
      apply simp
      by (metis `length as \<noteq> 0` ih length_0_conv tl.simps(2) tl_append2 xs_lefts)
  qed
qed

lemma single_left [simp]: "\<ll> xs = [l] \<Longrightarrow> map \<langle>id,id\<rangle> xs = \<rr> (take_left 0 xs) @ l # \<rr> (drop_left 0 xs)"
  apply (induct xs rule: sum_list_induct)
  apply simp
  apply simp
  apply (metis empty_left)
  by simp

lemma sum_list_empty [simp]: "xs = [] \<longleftrightarrow> \<ll> xs = [] \<and> \<rr> xs = []"
  by (induct xs rule: sum_list_induct) auto

lemma [intro]: "\<ll> xs = y # ys \<Longrightarrow> \<ll> (delete_left 0 xs) = ys"
  by (induct xs rule: sum_list_induct) (auto simp add: delete_left_def)

primrec is_left :: "('a, 'b) sum \<Rightarrow> bool" where
  "is_left (Inl x) = True"
| "is_left (Inr x) = False"

primrec is_right :: "('a, 'b) sum \<Rightarrow> bool" where
  "is_right (Inr x) = True"
| "is_right (Inl x) = False"

lemma not_is_left [simp]: "\<not> is_left x \<longleftrightarrow> is_right x"
  by (cases x) auto

lemma not_is_right [simp]: "\<not> is_right x \<longleftrightarrow> is_left x"
  by (cases x) auto

lemma is_left_swap [simp]: "is_left (swap x) \<longleftrightarrow> is_right x" 
  by (cases x) auto

lemma is_right_swap [simp]: "is_right (swap x) \<longleftrightarrow> is_left x" 
  by (cases x) auto

lemma lefts_singleton_emp [elim]: "is_right x \<Longrightarrow> \<ll> [x] = []"
  by (cases x) auto

lemma rights_singleton_emp [elim]: "is_left x \<Longrightarrow> \<rr> [x] = []"
  by (cases x) auto

primrec unl :: "('a, 'b) sum \<Rightarrow> 'a" where
  "unl (Inl x) = x"
| "unl (Inr x) = undefined"

primrec unr :: "('a, 'b) sum \<Rightarrow> 'b" where
  "unr (Inr x) = x"
| "unr (Inl x) = undefined"

end
