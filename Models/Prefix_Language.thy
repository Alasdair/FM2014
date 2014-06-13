theory Prefix_Language
  imports Language
begin

datatype 'a plist = Term "'a list" | Inf "'a stream" | Pre "'a list"

fun pappend :: "'a plist \<Rightarrow> 'a plist \<Rightarrow> 'a plist" where
  "pappend (Pre xs) ys = Pre xs"
| "pappend (Term xs) (Pre ys) = Pre (xs @ ys)"
| "pappend (Term xs) (Inf ys) = Inf (xs @- ys)"
| "pappend (Term xs) (Term ys) = Term (xs @ ys)"
| "pappend (Inf xs) ys = Inf xs"

lemma pappend_assoc: "pappend (pappend xs ys) zs = pappend xs (pappend ys zs)"
  apply (cases xs)
  apply simp_all
  apply (cases ys)
  apply simp_all
  apply (cases zs)
  by simp_all

type_synonym 'a plan = "'a plist set"

primrec pterm :: "'a plist \<Rightarrow> bool" where
  "pterm (Pre xs) = False"
| "pterm (Term xs) = True"
| "pterm (Inf xs) = False"

no_notation Language.l_prod (infixl "\<cdot>" 80)

definition pprod :: "'a plan \<Rightarrow> 'a plan \<Rightarrow> 'a plan" (infixl "\<cdot>" 80) where
  "pprod X Y = {pappend xs ys |xs ys. xs \<in> X \<and> pterm xs \<and> ys \<in> Y} \<union> {xs. xs \<in> X \<and> \<not> pterm xs}"

lemma pterm_pappend: "pterm (pappend xs ys) \<longleftrightarrow> (pterm xs \<and> pterm ys)"
  apply (cases xs)
  apply simp_all
  apply (cases ys)
  by simp_all

lemma pprod_assoc: "(X \<cdot> Y) \<cdot> Z = X \<cdot> (Y \<cdot> Z)"
  apply (simp add: pprod_def)
  apply safe
  by (metis pappend_assoc pterm_pappend)+

find_consts "'a llist \<Rightarrow> 'a stream"

fun pshuffle_words :: "'a plist \<Rightarrow> 'b plist \<Rightarrow> ('a + 'b) plan" (infix "\<sha>" 75) where
  "(Pre xs) \<sha> (Pre ys) = Pre ` list_of ` (llist_of xs \<sha> llist_of ys)"
| "(Term xs) \<sha> (Term ys) = Term ` list_of ` (llist_of xs \<sha> llist_of ys)"
| "(Inf xs) \<sha> (Inf ys) = Inf ` stream_of_llist ` (llist_of_stream xs \<sha> llist_of_stream ys)"

end
