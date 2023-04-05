(*
  Session: Generalised_Cauchy_Davenport
  Title: Generalised_Cauchy_Davenport.thy
  Authors: Mantas Bakšys
  Affiliation: University of Cambridge
  Date: April 2023.


*)


theory Generalised_Cauchy_Davenport
  imports 
 Complex_Main
 "Jacobson_Basic_Algebra.Group_Theory"

begin

(* well_order lemmas *)

lemma wf_prod_lex_fibers_inter: 
  fixes r :: "('a \<times> 'a) set" and s :: "('b \<times> 'b) set" and f :: "'c \<Rightarrow> 'a" and g :: "'c \<Rightarrow> 'b" and
  t :: "('c \<times> 'c) set"
  assumes h1: "wf ((inv_image r f) \<inter> t)" and
  h2: "\<And> a. a \<in> range f \<Longrightarrow> wf (({x. f x = a} \<times> {x. f x = a} \<inter> (inv_image s g)) \<inter> t)" and
  h3: "trans t"
  shows "wf ((inv_image (r <*lex*> s) (\<lambda> c. (f c, g c))) \<inter> t)"
proof-
  have h4: "(\<Union> a \<in> range f. ({x. f x = a} \<times> {x. f x = a} \<inter> (inv_image s g)) \<inter> t) = 
    (\<Union> a \<in> range f. ({x. f x = a} \<times> {x. f x = a} \<inter> (inv_image s g))) \<inter> t" by blast 
  have "(inv_image (r <*lex*> s) (\<lambda> c. (f c, g c))) \<inter> t = (inv_image r f \<inter> t) \<union>
    (\<Union> a \<in> range f. {x. f x = a} \<times> {x. f x = a} \<inter> (inv_image s g) \<inter> t)"
  proof
    show "inv_image (r <*lex*> s) (\<lambda>c. (f c, g c)) \<inter> t
    \<subseteq> inv_image r f \<inter> t \<union> (\<Union>a\<in>range f. {x. f x = a} \<times> {x. f x = a} \<inter> inv_image s g \<inter> t)"
    proof
      fix y assume hy: "y \<in> inv_image (r <*lex*> s) (\<lambda>c. (f c, g c)) \<inter> t"
      then obtain a b where hx: "y = (a, b)" and "(f a, f b) \<in> r \<or> (f a = f b \<and> (g a, g b) \<in> s)"
        using in_inv_image in_lex_prod Int_iff SigmaE UNIV_Times_UNIV inf_top_right by (smt (z3))
      then show "y \<in> inv_image r f \<inter> t \<union> (\<Union>a\<in>range f. {x. f x = a} \<times> {x. f x = a} \<inter> inv_image s g \<inter> t)" 
        using hy by auto
    qed
    show "inv_image r f \<inter> t \<union> (\<Union>a\<in>range f. {x. f x = a} \<times> {x. f x = a} \<inter> inv_image s g \<inter> t) \<subseteq> 
      inv_image (r <*lex*> s) (\<lambda>c. (f c, g c)) \<inter> t" using Int_iff SUP_le_iff SigmaD1 SigmaD2 
      in_inv_image in_lex_prod mem_Collect_eq subrelI by force
  qed
  moreover have "((inv_image r f) \<inter> t) O
    (\<Union> a \<in> range f. ({x. f x = a} \<times> {x. f x = a} \<inter> (inv_image s g)) \<inter> t) \<subseteq> (inv_image r f) \<inter> t"
   using h3 trans_O_subset by fastforce
  moreover have "wf (\<Union> a \<in> range f. {x. f x = a} \<times> {x. f x = a} \<inter> (inv_image s g) \<inter> t)"
    apply(rule wf_UN, auto simp add: h2)
    done
  ultimately show "wf (inv_image (r <*lex*> s) (\<lambda> c. (f c, g c)) \<inter> t)" 
    using wf_union_compatible[OF h1] by fastforce
qed

lemma wf_prod_lex_fibers: 
  fixes r :: "('a \<times> 'a) set" and s :: "('b \<times> 'b) set" and f :: "'c \<Rightarrow> 'a" and g :: "'c \<Rightarrow> 'b"
  assumes h1: "wf (inv_image r f)" and
  h2: "\<And> a. a \<in> range f \<Longrightarrow> wf ({x. f x = a} \<times> {x. f x = a} \<inter> (inv_image s g))"
  shows "wf (inv_image (r <*lex*> s) (\<lambda> c. (f c, g c)))"
  using assms trans_def wf_prod_lex_fibers_inter[of r f UNIV s g] inf_top_right
  by (metis (mono_tags, lifting) iso_tuple_UNIV_I)

context monoid

begin

inductive_set smul :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" for A B 
  where
    smulI[intro]: "\<lbrakk>a \<in> A; a \<in> M; b \<in> B; b \<in> M\<rbrakk> \<Longrightarrow> a \<cdot> b \<in> smul A B"

syntax "smul" ::  "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" ("(_ \<cdots> _)")

lemma smul_eq: "smul A B = {c. \<exists>a \<in> A \<inter> M. \<exists>b \<in> B \<inter> M. c = a \<cdot> b}"
  by (auto simp: smul.simps elim!: smul.cases)

lemma smul: "smul A B = (\<Union>a \<in> A \<inter> M. \<Union>b \<in> B \<inter> M. {a \<cdot> b})"
  by (auto simp: smul_eq)

lemma smul_subset_carrier: "smul A B \<subseteq> M"
  by (auto simp: smul_eq)

lemma smul_Int_carrier [simp]: "smul A B \<inter> M = smul A B"
  by (simp add: Int_absorb2 smul_subset_carrier)

lemma smul_mono: "\<lbrakk>A' \<subseteq> A; B' \<subseteq> B\<rbrakk> \<Longrightarrow> smul A' B' \<subseteq> smul A B"
  by (auto simp: smul_eq)

lemma smul_insert1: "NO_MATCH {} A \<Longrightarrow> smul (insert x A) B = smul {x} B \<union> smul A B"
  by (auto simp: smul_eq)

lemma smul_insert2: "NO_MATCH {} B \<Longrightarrow> smul A (insert x B) = smul A {x} \<union> smul A B"
  by (auto simp: smul_eq)

lemma smul_subset_Un1: "smul (A \<union> A') B = smul A B \<union> smul A' B"
  by (auto simp: smul_eq)

lemma smul_subset_Un2: "smul A (B \<union> B') = smul A B \<union> smul A B'"
  by (auto simp: smul_eq)

lemma smul_subset_Union1: "smul (\<Union> A) B = (\<Union> a \<in> A. smul a B)"
  by (auto simp: smul_eq)

lemma smul_subset_Union2: "smul A (\<Union> B) = (\<Union> b \<in> B. smul A b)"
  by (auto simp: smul_eq)

lemma smul_subset_insert: "smul A B \<subseteq> smul A (insert x B)" "smul A B \<subseteq> smul (insert x A) B"
  by (auto simp: smul_eq)

lemma smul_subset_Un: "smul A B \<subseteq> smul A (B\<union>C)" "smul A B \<subseteq> smul (A\<union>C) B"
  by (auto simp: smul_eq)

lemma smul_empty [simp]: "smul A {} = {}" "smul {} A = {}"
  by (auto simp: smul_eq)

lemma smul_empty':
  assumes "A \<inter> M = {}"
  shows "smul B A = {}" "smul A B = {}"
  using assms by (auto simp: smul_eq)

lemma smul_is_empty_iff [simp]: "smul A B = {} \<longleftrightarrow> A \<inter> M = {} \<or> B \<inter> M = {}"
  by (auto simp: smul_eq)

lemma smul_D [simp]: "smul A {\<one>} = A \<inter> M" "smul {\<one>} A = A \<inter> M"
  by (auto simp: smul_eq)

lemma smul_Int_carrier_eq [simp]: "smul A (B \<inter> M) = smul A B" "smul (A \<inter> M) B = smul A B"
  by (auto simp: smul_eq)

lemma smul_assoc:
  shows "smul (smul A B) C = smul A (smul B C)"
  by (fastforce simp add: smul_eq associative Bex_def)

lemma finite_smul:
  assumes "finite A" "finite B"  shows "finite (smul A B)"
  using assms by (auto simp: smul_eq)

lemma finite_smul':
  assumes "finite (A \<inter> M)" "finite (B \<inter> M)"
    shows "finite (smul A B)"
  using assms by (auto simp: smul_eq)

primrec power :: "'a \<Rightarrow> nat \<Rightarrow> 'a" (infix "^" 100)
  where
  power0: "power g 0 = \<one>"
| power_suc: "power g (Suc n) = power g n \<cdot> g"

lemma power_one:
  assumes "g \<in> M"
  shows "power g 1 = g" using power_def power0 assms by simp

lemma power_mem_carrier:
  fixes n
  assumes "g \<in> M"
  shows "g ^ n \<in> M"
  apply (induction n, auto simp add: assms power_def)
  done

lemma power_mult:
  assumes "g \<in> M"
  shows "g ^ n \<cdot> g ^ m = g ^ (n + m)"
proof(induction m)
  case 0
  then show ?case using assms power0 right_unit power_mem_carrier by simp
next
  case (Suc m)
  assume "g ^ n \<cdot> g ^ m = g ^ (n + m)"
  then show ?case using power_def by (smt (verit) add_Suc_right assms associative 
    power_mem_carrier power_suc)
qed

lemma mult_inverse_power:
  assumes "g \<in> M" and "invertible g"
  shows "g ^ n \<cdot> ((inverse g) ^ n) = \<one>"
proof(induction n)
  case 0
  then show ?case using power_0 by auto
next
  case (Suc n)
  assume hind: "g ^ n \<cdot> local.inverse g ^ n = \<one>"
  then have "g ^ Suc n \<cdot> inverse g ^ Suc n = (g \<cdot> g ^ n) \<cdot> (inverse g ^ n \<cdot> inverse g)" 
    using power_def power_mult assms by (smt (z3) add.commute invertible_inverse_closed 
    invertible_right_inverse left_unit monoid.associative monoid_axioms power_mem_carrier power_suc)
  then show ?case using associative power_mem_carrier assms hind by (smt (verit, del_insts) 
    composition_closed invertible_inverse_closed invertible_right_inverse right_unit)
qed

lemma inverse_mult_power:
  assumes "g \<in> M" and "invertible g"
  shows "((inverse g) ^ n) \<cdot> g ^ n = \<one>" using assms by (metis invertible_inverse_closed 
    invertible_inverse_inverse invertible_inverse_invertible mult_inverse_power)

lemma inverse_mult_power_eq:
  assumes "g \<in> M" and "invertible g"
  shows "inverse (g ^ n) = (inverse g) ^ n"
  using assms inverse_equality by (simp add: inverse_mult_power mult_inverse_power power_mem_carrier)

definition power_int :: "'a \<Rightarrow> int \<Rightarrow> 'a" (infixr "powi" 80) where
  "power_int g n = (if n \<ge> 0 then g ^ (nat n) else (inverse g) ^ (nat (-n)))"

definition nat_powers :: "'a \<Rightarrow> 'a set" where "nat_powers g = ((\<lambda> n. g ^ n) ` UNIV)"

lemma nat_powers_eq_Union: "nat_powers g = (\<Union> n. {g ^ n})" using nat_powers_def by auto

definition powers :: "'a \<Rightarrow> 'a set" where "powers g = ((\<lambda> n. g powi n) ` UNIV)"

lemma nat_powers_subset:
  "nat_powers g \<subseteq> powers g"
proof
  fix x assume "x \<in> nat_powers g"
  then obtain n where "x = g ^ n" and "nat n = n" using nat_powers_def by auto
  then show "x \<in> powers g" using powers_def power_int_def 
    by (metis UNIV_I image_iff of_nat_0_le_iff)
qed

lemma inverse_nat_powers_subset:
  "nat_powers (inverse g) \<subseteq> powers g"
proof
  fix x assume "x \<in> nat_powers (inverse g)"
  then obtain n where hx: "x = (inverse g) ^ n" using nat_powers_def by blast
  then show "x \<in> powers g"
  proof(cases "n = 0")
    case True
    then show ?thesis using hx power0 powers_def
      by (metis nat_powers_def nat_powers_subset rangeI subsetD)
  next
    case False
    then have hpos: "\<not> (- int n) \<ge> 0" by auto
    then have "x = g powi (- int n)" using hx hpos power_int_def by simp
    then show ?thesis using powers_def by auto
  qed
qed

lemma powers_eq_union_nat_powers:
  "powers g = nat_powers g \<union> nat_powers (inverse g)"
proof
  show "powers g \<subseteq> nat_powers g \<union> nat_powers (local.inverse g)"
    using powers_def nat_powers_def power_int_def by auto
next 
  show "nat_powers g \<union> nat_powers (inverse g) \<subseteq> powers g"
    by (simp add: inverse_nat_powers_subset nat_powers_subset)
qed

lemma one_mem_nat_powers: "\<one> \<in> nat_powers g"
  using rangeI power0 nat_powers_def by metis

lemma nat_powers_subset_carrier:
  assumes "g \<in> M"
  shows "nat_powers g \<subseteq> M"
  using nat_powers_def power_mem_carrier assms by auto

lemma nat_powers_mult_closed:
  assumes "g \<in> M"
  shows "\<And> x y. x \<in> nat_powers g \<Longrightarrow> y \<in> nat_powers g \<Longrightarrow> x \<cdot> y \<in> nat_powers g"
  using nat_powers_def power_mult assms by auto

lemma nat_powers_inv_mult:
  assumes "g \<in> M" and "invertible g"
  shows "\<And> x y. x \<in> nat_powers g \<Longrightarrow> y \<in> nat_powers (inverse g) \<Longrightarrow> x \<cdot> y \<in> powers g"
proof-
  fix x y assume "x \<in> nat_powers g" and "y \<in> nat_powers (inverse g)"
  then obtain n m where hx: "x = g ^ n" and hy: "y = (inverse g) ^ m" using nat_powers_def by blast
  show "x \<cdot> y \<in> powers g"
  proof(cases "n \<ge> m")
    case True
    then obtain k where "n = k + m" using add.commute le_Suc_ex by blast
    then have "g ^ n \<cdot> (inverse g) ^ m = g ^ k" using mult_inverse_power assms associative 
      by (smt (verit) invertible_inverse_closed local.power_mult power_mem_carrier right_unit)
    then show ?thesis using hx hy powers_eq_union_nat_powers nat_powers_def by auto
  next
    case False
    then obtain k where "m = n + k" by (metis leI less_imp_add_positive)
    then have "g ^ n \<cdot> (inverse g) ^ m = (inverse g) ^ k" using inverse_mult_power assms associative 
      by (smt (verit) left_unit local.power_mult monoid.invertible_inverse_closed monoid_axioms 
        mult_inverse_power power_mem_carrier)
    then show ?thesis using hx hy powers_eq_union_nat_powers nat_powers_def by auto
  qed
qed

lemma inv_nat_powers_mult:
  assumes "g \<in> M" and "invertible g"
  shows "\<And> x y. x \<in> nat_powers (inverse g) \<Longrightarrow> y \<in> nat_powers g \<Longrightarrow> x \<cdot> y \<in> powers g"
  by (metis assms invertible_inverse_closed invertible_inverse_inverse invertible_inverse_invertible
    nat_powers_inv_mult powers_eq_union_nat_powers sup_commute)

lemma powers_mult_closed:
  assumes "g \<in> M" and "invertible g"
  shows "\<And> x y. x \<in> powers g \<Longrightarrow> y \<in> powers g \<Longrightarrow> x \<cdot> y \<in> powers g"
  using powers_eq_union_nat_powers assms 
    nat_powers_mult_closed nat_powers_inv_mult inv_nat_powers_mult by fastforce

lemma nat_powers_submonoid:
  assumes "g \<in> M"
  shows "submonoid (nat_powers g) M (\<cdot>) \<one>"
  apply(unfold_locales)
  apply(auto simp add: assms nat_powers_mult_closed one_mem_nat_powers nat_powers_subset_carrier)
  done

lemma nat_powers_monoid:
  assumes "g \<in> M"
  shows "monoid (nat_powers g) (\<cdot>) \<one>"
  using nat_powers_submonoid assms by (smt (verit) monoid.intro associative left_unit 
      one_mem_nat_powers nat_powers_mult_closed right_unit submonoid.sub)

lemma powers_submonoid:
  assumes "g \<in> M" and "invertible g"
  shows "submonoid (powers g) M (\<cdot>) \<one>"
proof
  show "powers g \<subseteq> M" using powers_eq_union_nat_powers nat_powers_subset_carrier assms by auto
next
  show "\<And>a b. a \<in> powers g \<Longrightarrow> b \<in> powers g \<Longrightarrow> a \<cdot> b \<in> powers g" 
    using powers_mult_closed assms by auto
next
  show "\<one> \<in> powers g" using powers_eq_union_nat_powers one_mem_nat_powers by auto
qed

lemma powers_monoid:
  assumes "g \<in> M" and "invertible g"
  shows "monoid (powers g) (\<cdot>) \<one>"
  by (smt (verit) monoid.intro Un_iff assms associative in_mono invertible_inverse_closed 
      monoid.left_unit monoid.right_unit nat_powers_monoid powers_eq_union_nat_powers 
      powers_mult_closed powers_submonoid submonoid.sub_unit_closed submonoid.subset)

lemma mem_nat_powers_invertible:
  assumes "g \<in> M" and "invertible g" and "u \<in> nat_powers g"
  shows "monoid.invertible (powers g) (\<cdot>) \<one> u"
proof-
  obtain n where hu: "u = g ^ n" using assms nat_powers_def by blast
  then have "inverse u \<in> powers g" using assms inverse_mult_power_eq 
      powers_eq_union_nat_powers nat_powers_def by auto
  then show ?thesis using hu assms by (metis in_mono inverse_mult_power inverse_mult_power_eq 
    monoid.invertibleI monoid.nat_powers_subset monoid.powers_monoid monoid_axioms mult_inverse_power)
qed

lemma mem_nat_inv_powers_invertible:
  assumes "g \<in> M" and "invertible g" and "u \<in> nat_powers (inverse g)"
  shows "monoid.invertible (powers g) (\<cdot>) \<one> u"
  using assms by (metis inf_sup_aci(5) invertible_inverse_closed invertible_inverse_inverse 
    invertible_inverse_invertible mem_nat_powers_invertible powers_eq_union_nat_powers)

lemma powers_group:
  assumes "g \<in> M" and "invertible g"
  shows "group (powers g) (\<cdot>) \<one>"
proof(auto simp add: group_def Group_Theory.group_axioms_def assms powers_monoid)
  show "\<And>u. u \<in> powers g \<Longrightarrow> monoid.invertible (powers g) (\<cdot>) \<one> u" using assms 
    mem_nat_inv_powers_invertible mem_nat_powers_invertible powers_eq_union_nat_powers by auto
qed

lemma nat_powers_ne_one:
  assumes "g \<in> M" and "g \<noteq> \<one>"
  shows "nat_powers g \<noteq> {\<one>}"
proof-
  have "g \<in> nat_powers g" using power_one nat_powers_def assms rangeI by metis
  then show ?thesis using assms by blast
qed

lemma powers_ne_one: 
  assumes "g \<in> M" and "g \<noteq> \<one>"
  shows "powers g \<noteq> {\<one>}" using assms nat_powers_ne_one 
  by (metis all_not_in_conv nat_powers_subset one_mem_nat_powers subset_singleton_iff)

definition order 
  where "order g = (if (\<exists> n. n > 0 \<and> g ^ n = \<one>) then Min {n. g ^ n = \<one> \<and> n > 0} else 0)"

definition min_order where "min_order = Min ((order ` M) - {0})"

end 

context group

begin

lemma card_smul_singleton_right_eq:
  assumes "finite A" shows "card (smul A {a}) = (if a \<in> G then card (A \<inter> G) else 0)"
proof (cases "a \<in> G")
  case True
  then have "smul A {a} = (\<lambda>x. x \<cdot> a) ` (A \<inter> G)"
    by (auto simp: smul_eq)
  moreover have "inj_on (\<lambda>x. x \<cdot> a) (A \<inter> G)"
    by (auto simp: inj_on_def True)
  ultimately show ?thesis
    by (metis True card_image)
qed (auto simp: smul_eq)

lemma card_smul_singleton_left_eq:
  assumes "finite A" shows "card (smul {a} A) = (if a \<in> G then card (A \<inter> G) else 0)"
proof (cases "a \<in> G")
  case True
  then have "smul {a} A = (\<lambda>x. a \<cdot> x) ` (A \<inter> G)"
    by (auto simp: smul_eq)
  moreover have "inj_on (\<lambda>x. a \<cdot> x) (A \<inter> G)"
    by (auto simp: inj_on_def True)
  ultimately show ?thesis
    by (metis True card_image)
qed (auto simp: smul_eq)

lemma card_smul_sing_right_le:
  assumes "finite A" shows "card (smul A {a}) \<le> card A"
  by (simp add: assms card_mono card_smul_singleton_right_eq)

lemma card_smul_sing_left_le:
  assumes "finite A" shows "card (smul {a} A) \<le> card A"
  by (simp add: assms card_mono card_smul_singleton_left_eq)

lemma card_le_smul_right:
  assumes A: "finite A" "a \<in> A" "a \<in> G"
    and   B: "finite B" "B \<subseteq> G"
  shows "card B \<le> card (smul A B)"
proof -
  have "B \<subseteq> (\<lambda> x.  (inverse a) \<cdot> x) ` smul A B"
    using A B
    apply (clarsimp simp: smul image_iff)
    using Int_absorb2 Int_iff invertible invertible_left_inverse2 by metis
  with A B show ?thesis
    by (meson  finite_smul surj_card_le)
qed

lemma card_le_smul_left:
  assumes A: "finite A" "b \<in> B" "b \<in> G"
    and   B: "finite B" "A \<subseteq> G"
  shows "card A \<le> card (smul A B)"
proof -
  have "A \<subseteq> (\<lambda> x. x \<cdot> (inverse b)) ` smul A B"
    using A B
    apply (clarsimp simp: smul image_iff associative)     
    using Int_absorb2 Int_iff invertible invertible_right_inverse assms(5) by (metis right_unit)
  with A B show ?thesis
    by (meson  finite_smul surj_card_le)
qed


lemma infinite_smul_right:
  assumes "A \<inter> G \<noteq> {}" and "infinite (B \<inter> G)"
  shows "infinite (A \<cdots> B)" 
proof
  assume hfin: "finite (smul A B)"
  obtain a where ha: "a \<in> A \<inter> G" using assms by auto
  then have "finite (smul {a} B)" using hfin by (metis Int_Un_eq(1) finite_subset insert_is_Un 
    mk_disjoint_insert smul_subset_Un(2))
  moreover have "B \<inter> G \<subseteq> (\<lambda> x. inverse a \<cdot> x) ` smul {a} B" 
  proof
    fix b assume hb: "b \<in> B \<inter> G"
    then have "b = inverse a \<cdot> (a \<cdot> b)" using associative ha by (simp add: invertible_left_inverse2)
    then show "b \<in> (\<lambda> x. inverse a \<cdot> x) ` smul {a} B" using smul.simps hb ha by blast
  qed
  ultimately show False using assms using finite_surj by blast
qed

lemma infinite_smul_left:
  assumes "B \<inter> G \<noteq> {}" and "infinite (A \<inter> G)"
  shows "infinite (A \<cdots> B)"
proof
  assume hfin: "finite (smul A B)"
  obtain b where hb: "b \<in> B \<inter> G" using assms by auto
  then have "finite (smul A {b})" using hfin by (simp add: rev_finite_subset smul_mono)
  moreover have "A \<inter> G \<subseteq> (\<lambda> x. x \<cdot> inverse b) ` smul A {b}"
  proof
    fix a assume ha: "a \<in> A \<inter> G"
    then have "a = (a \<cdot> b) \<cdot> inverse b" using associative hb
      by (metis IntD2 invertible invertible_inverse_closed invertible_right_inverse right_unit)
    then show "a \<in> (\<lambda> x. x \<cdot> inverse b) ` smul A {b}" using smul.simps hb ha by blast
  qed
  ultimately show False using assms using finite_surj by blast
qed

lemma set_inverse_composition_commute:
  assumes "X \<subseteq> G" and "Y \<subseteq> G"
  shows "inverse ` (X \<cdots> Y) = (inverse ` Y) \<cdots> (inverse ` X)"
proof
  show "inverse ` (X \<cdots> Y) \<subseteq> (inverse ` Y) \<cdots> (inverse ` X)"
  proof
    fix z assume "z \<in> inverse ` (X \<cdots> Y)"
    then obtain x y where "z = inverse (x \<cdot> y)" and "x \<in> X" and "y \<in> Y" 
      by (smt (verit) image_iff smul.cases)
    then show "z \<in> (inverse ` Y) \<cdots> (inverse ` X)" 
      using inverse_composition_commute assms 
      by (smt (verit) image_eqI in_mono inverse_equality invertible invertibleE smul.simps)
  qed
  show "(inverse ` Y) \<cdots> (inverse ` X) \<subseteq> inverse ` (X \<cdots> Y)"
  proof
    fix z assume "z \<in> (inverse ` Y) \<cdots> (inverse ` X)"
    then obtain x y where "x \<in> X" and "y \<in> Y" and "z = inverse y \<cdot> inverse x" 
      using smul.cases image_iff by blast
    then show "z \<in> inverse ` (X \<cdots> Y)" using inverse_composition_commute assms smul.simps
      by (smt (verit) image_iff in_mono invertible)
  qed
qed

definition devos_rel where 
  "devos_rel = (\<lambda> (A, B). card(A \<cdots> B)) <*mlex*> (inv_image ({(n, m). n > m} <*lex*> 
  measure (\<lambda> (A, B). card A))) (\<lambda> (A, B). (card A + card B, (A, B)))"

lemma devos_rel_iff: 
  "((A, B), (C, D)) \<in> devos_rel \<longleftrightarrow> card(A \<cdots> B) < card(C \<cdots> D) \<or> 
  (card(A \<cdots> B) = card(C \<cdots> D) \<and> card A + card B > card C + card D) \<or>
  (card(A \<cdots> B) = card(C \<cdots> D) \<and> card A + card B = card C + card D \<and> card A < card C)"
  using devos_rel_def mlex_iff[of _ _ "\<lambda> (A, B). card(A \<cdots> B)"] by fastforce

lemma devos_rel_le_smul:
  "((A, B), (C, D)) \<in> devos_rel \<Longrightarrow> card(A \<cdots> B) \<le> card(C \<cdots> D)"
  using devos_rel_iff by fastforce

lemma devos_rel_wf : "wf (Restr devos_rel 
  {(A, B). finite A \<and> A \<noteq> {} \<and> A \<subseteq> G \<and> finite B \<and> B \<noteq> {} \<and> B \<subseteq> G})" (is "wf (Restr devos_rel ?fin)")
proof-
  define f where "f = (\<lambda> (A, B). card(A\<cdots>B))"
  define g where "g = (\<lambda> (A :: 'a set, B :: 'a set). (card A + card B, (A, B)))"
  define h where "h = (\<lambda> (A :: 'a set, B :: 'a set). card A + card B)"
  define s where "s = ({(n :: nat, m :: nat). n > m} <*lex*> measure (\<lambda> (A :: 'a set, B :: 'a set). card A))"
  have hle2f: "\<And> x. x \<in> ?fin \<Longrightarrow> h x \<le> 2 * f x"
  proof-
    fix x assume hx: "x \<in> ?fin"
    then obtain A B where hxAB: "x = (A, B)" by blast
    then have "card A \<le> card (A \<cdots> B)" and "card B \<le> card (A \<cdots> B)" 
      using card_le_smul_left card_le_smul_right hx by auto
    then show "h x \<le> 2 * f x" using hxAB h_def f_def by force
  qed
  have "wf (Restr (measure f) ?fin)" by (simp add: wf_Int1)
  moreover have "\<And> a. a \<in> range f \<Longrightarrow> wf (Restr (Restr (inv_image s g) {x. f x = a}) ?fin)"
  proof-
    fix y assume "y \<in>  range f"
    then show "wf (Restr (Restr (inv_image s g) {x. f x = y}) ?fin)"
    proof-
      have "Restr ({x. f x = y} \<times> {x. f x = y} \<inter> (inv_image s g)) ?fin \<subseteq> 
        Restr (((\<lambda> x. 2 * f x - h x) <*mlex*> measure (\<lambda> (A :: 'a set, B :: 'a set). card A)) \<inter> 
        {x. f x = y} \<times> {x. f x = y}) ?fin"
      proof
        fix z assume hz: "z \<in> Restr ({x. f x = y} \<times> {x. f x = y} \<inter> (inv_image s g)) ?fin"
        then obtain a b where hzab: "z = (a, b)" and "f a = y" and "f b = y" and 
          "h a > h b \<or> h a = h b \<and> (a, b) \<in> measure (\<lambda> (A, B). card A)" and 
          "a \<in> ?fin" and "b \<in> ?fin"
          using s_def g_def h_def by force
        then obtain "2 * f a - h a < 2 * f b - h b \<or> 
          2 * f a - h a = 2 * f b - h b \<and> (a, b) \<in> measure (\<lambda> (A, B). card A)" 
          using hle2f by (smt (verit) diff_less_mono2 le_antisym nat_less_le)
        then show "z \<in> Restr (((\<lambda> x. 2 * f x - h x) <*mlex*> measure (\<lambda> (A, B). card A)) \<inter> 
        {x. f x = y} \<times> {x. f x = y}) ?fin" using hzab hz by (simp add: mlex_iff)
      qed
      moreover have "wf ((\<lambda> x. 2 * f x - h x) <*mlex*> measure (\<lambda> (A, B). card A))"
        by (simp add: wf_mlex)
      ultimately show ?thesis by (simp add: Int_commute wf_Int1 wf_subset)
    qed
  qed
  moreover have "trans (?fin \<times> ?fin)" using trans_def by fast
  ultimately have "wf (Restr (inv_image (less_than <*lex*> s) (\<lambda> c. (f c, g c))) ?fin)" 
    using wf_prod_lex_fibers_inter[of "less_than" "f" "?fin \<times> ?fin" "s" "g"] measure_def
    by (metis (no_types, lifting) inf_sup_aci(1))
  moreover have "(inv_image (less_than <*lex*> s) (\<lambda> c. (f c, g c))) = devos_rel"
    using s_def f_def g_def devos_rel_def mlex_prod_def by fastforce
  ultimately show ?thesis by simp
qed

lemma smul_singleton_eq_contains_nat_powers:
  fixes n :: nat
  assumes "X \<subseteq> G" and "g \<in> G" and "X \<cdots> {g} = X"
  shows "X \<cdots> {g ^ n} = X"
proof(induction n)
  case 0
  then show ?case using power_def assms by auto
next
  case (Suc n)
  assume hXn: "X \<cdots> {g ^ n} = X"
  moreover have "X \<cdots> {g ^ Suc n} = (X \<cdots> {g ^ n}) \<cdots> {g}"
  proof
    show "X \<cdots> {g ^ Suc n} \<subseteq> (X \<cdots> {g ^ n}) \<cdots> {g}"
    proof
      fix z assume "z \<in> X \<cdots> {g ^ Suc n}"
      then obtain x where "z = x \<cdot> (g ^ Suc n)" and hx: "x \<in> X"  using smul.simps by auto
      then have "z = (x \<cdot> g ^ n) \<cdot> g" using assms associative by (simp add: in_mono power_mem_carrier) 
      then show "z \<in> (X \<cdots> {g ^ n}) \<cdots> {g}" using hx assms 
        by (simp add: power_mem_carrier smul.smulI subsetD)
    qed
  next
    show "(X \<cdots> {g ^ n}) \<cdots> {g} \<subseteq> X \<cdots> {g ^ Suc n}"
    proof
      fix z assume "z \<in> (X \<cdots> {g ^ n}) \<cdots> {g}"
      then obtain x where "z = (x \<cdot> g ^ n) \<cdot> g" and hx: "x \<in> X" using smul.simps by auto
      then have "z = x \<cdot> g ^ Suc n" 
        using power_def associative power_mem_carrier assms by (simp add: in_mono)
      then show "z \<in> X \<cdots> {g ^ Suc n}" using hx assms 
        by (simp add: power_mem_carrier smul.smulI subsetD)
    qed
  qed
  ultimately show ?case using assms by simp
qed

lemma smul_singleton_eq_contains_inverse_nat_powers:
  fixes n :: nat
  assumes "X \<subseteq> G" and "g \<in> G" and "X \<cdots> {g} = X"
  shows "X \<cdots> {(inverse g) ^ n} = X"
proof-
  have "(X \<cdots> {g}) \<cdots> {inverse g} = X"
  proof
    show "(X \<cdots> {g}) \<cdots> {inverse g} \<subseteq> X"
    proof
      fix z assume "z \<in> (X \<cdots> {g}) \<cdots> {inverse g}"
      then obtain y x where "y \<in> X \<cdots> {g}" and "z = y \<cdot> inverse g" and "x \<in> X"  and "y = x \<cdot> g" 
        using assms smul.simps by (metis empty_iff insert_iff)
      then show "z \<in> X" using assms by (simp add: associative subset_eq)
    qed
  next
    show "X \<subseteq> (X \<cdots> {g}) \<cdots> {inverse g}" 
    proof
      fix x assume hx: "x \<in> X"
      then have "x = x \<cdot> g \<cdot> inverse g" using assms by (simp add: associative subset_iff)
      then show "x \<in> (X \<cdots> {g}) \<cdots> {inverse g}" using assms smul.simps hx by auto
    qed
  qed
  then have "X \<cdots> {inverse g} = X" using assms by auto
  then show ?thesis using assms by (simp add: smul_singleton_eq_contains_nat_powers)
qed

lemma smul_singleton_eq_contains_powers:
  fixes n :: nat
  assumes "X \<subseteq> G" and "g \<in> G" and "X \<cdots> {g} = X"
  shows "X \<cdots> (powers g) = X" using powers_eq_union_nat_powers smul_subset_Union2 
    nat_powers_eq_Union smul_singleton_eq_contains_nat_powers 
    smul_singleton_eq_contains_inverse_nat_powers assms smul_subset_Un2 by auto

definition p where "p = Inf (card ` {H. subgroup H G (\<cdot>) \<one> \<and> finite H \<and> H \<noteq> {\<one>}})"

lemma powers_subgroup:
  assumes "g \<in> G"
  shows "subgroup (powers g) G (\<cdot>) \<one>" 
  by (simp add: assms powers_group powers_submonoid subgroup.intro)

lemma subgroup_finite_ge:
  assumes "subgroup H G (\<cdot>) \<one>" and "H \<noteq> {\<one>}" and "finite H"
  shows "card H \<ge> p"
  using p_def assms by (simp add: wellorder_Inf_le1)

lemma subgroup_infinite_or_ge:
  assumes "subgroup H G (\<cdot>) \<one>" and "H \<noteq> {\<one>}"
  shows "infinite H \<or> card H \<ge> p" using subgroup_finite_ge assms by auto

end


(* Generalised Cauchy-Davenport theorem for (non-abelian) groups due to Matt DeVos
  Reference: Matt DeVos, On a generalization of the Cauchy-Davenport theorem
  Link: http://math.colgate.edu/~integers/q7/q7.pdf  *)
theorem (in group) Generalised_Cauchy_Davenport:
  assumes hAne: "A \<noteq> {}" and hBne: "B \<noteq> {}" and hAG: "A \<subseteq> G" and hBG: "B \<subseteq> G" and
  hAfin: "finite A" and hBfin: "finite B" and
  hsub: "{H. subgroup_of_group H G (\<cdot>) \<one> \<and> finite H \<and> H \<noteq> {\<one>}} \<noteq> {}"
  shows "card (A \<cdots> B) \<ge> min p (card A + card B - 1)"
proof(rule ccontr)
  assume hcontr: "\<not> min p (card A + card B - 1) \<le> card (A \<cdots> B)"
  let ?fin = "{(A, B). finite A \<and> A \<noteq> {} \<and> A \<subseteq> G \<and> finite B \<and> B \<noteq> {} \<and> B \<subseteq> G}"
  define M where "M = {(A, B). card (A \<cdots> B) < min p (card A + card B - 1)} \<inter> ?fin"
  have hmemM: "(A, B) \<in> M" using assms hcontr M_def by auto
  then obtain X Y where hXYM: "(X, Y) \<in> M" and hmin: "\<And>Z. Z \<in> M \<Longrightarrow> (Z, (X, Y)) \<notin> Restr devos_rel ?fin" 
    using devos_rel_wf wfE_min by (smt (verit, del_insts) old.prod.exhaust)
  have hXG: "X \<subseteq> G" and hYG: "Y \<subseteq> G" and hXfin: "finite X" and hYfin: "finite Y" and 
    hXYlt: "card (X \<cdots> Y) < min p (card X + card Y - 1)" using hXYM M_def by auto
  have hXY: "card X \<le> card Y"
  proof(rule ccontr)
    assume hcontr: "\<not> card X \<le> card Y"
    have hinvinj: "inj_on inverse G" using inj_onI invertible invertible_inverse_inverse by metis
    let ?M = "inverse ` X"
    let ?N = "inverse ` Y"
    have "?N \<cdots> ?M = inverse ` (X \<cdots> Y)" using set_inverse_composition_commute hXYM M_def by auto
    then have hNM: "card (?N \<cdots> ?M) = card (X \<cdots> Y)" 
      using hinvinj card_image subset_inj_on smul_subset_carrier by metis
    moreover have hM: "card ?M = card X"
      using hinvinj hXG hYG card_image subset_inj_on by metis
    moreover have hN: "card ?N = card Y" 
      using hinvinj hYG card_image subset_inj_on by metis
    moreover have hNplusM: "card ?N + card ?M = card X + card Y" using hM hN by auto
    ultimately have "card (?N \<cdots> ?M) < min p (card ?N + card ?M - 1)" 
      using hXYM M_def by auto
    then have "(?N, ?M) \<in> M" using M_def hXYM by blast
    then have "((?N, ?M), (X, Y)) \<notin> devos_rel" using hmin hXYM M_def by blast
    then have "\<not> card Y < card X" using hN  hNM hNplusM devos_rel_iff by simp
    then show False using hcontr by linarith
  qed
  have hX2: "2 \<le> card X"
  proof(rule ccontr)
    assume " \<not> 2 \<le> card X"
    moreover have "card X > 0" using hXYM M_def card_gt_0_iff by blast
    ultimately have hX1: "card X = 1" by auto
    then obtain x where "X = {x}" and "x \<in> G" using hXG by (metis card_1_singletonE insert_subset)
    then have "card (X \<cdots> Y) = card X + card Y - 1" using card_smul_singleton_left_eq hYG hXYM M_def
      by (simp add: Int_absorb2)
    then show False using hXYlt by linarith
  qed
  then obtain a b where habX: "{a, b} \<subseteq> X" and habne: "a \<noteq> b" by (metis card_2_iff obtain_subset_with_card_n)
  moreover have "b \<in> X \<cdots> {inverse a \<cdot> b}" by (smt (verit) habX composition_closed hXG insert_subset 
    invertible invertible_inverse_closed invertible_right_inverse2 singletonI smul.smulI subsetD)
  then obtain g where hgG: "g \<in> G" and hg1: "g \<noteq> \<one>" and hXgne: "(X \<cdots> {g}) \<inter> X \<noteq> {}" 
    using habne habX hXG by (metis composition_closed insert_disjoint(2) insert_subset invertible 
      invertible_inverse_closed invertible_right_inverse2 mk_disjoint_insert right_unit)
  have hpsubX: "(X \<cdots> {g}) \<inter> X \<subset> X"
  proof(rule ccontr)
    assume "\<not> (X \<cdots> {g}) \<inter> X \<subset> X"
    then have hXsub: "X \<subseteq> X \<cdots> {g}" by auto
    then have "card X \<cdots> {g} = card X" using card_smul_sing_right_le hXYM M_def
      by (metis Int_absorb2 \<open>g \<in> G\<close> card.infinite card_smul_singleton_right_eq finite_Int hXG)
    moreover have hXfin: "finite X" using hXYM M_def by auto
    ultimately have "X \<cdots> {g} = X" using hXsub 
      by (metis card_subset_eq finite.emptyI finite.insertI finite_smul)
    then have hXpow: "X \<cdots> (powers g) = X" by (simp add: hXG hgG smul_singleton_eq_contains_powers)
    moreover have hfinpowers: "finite (powers g)"
    proof(rule ccontr)
      assume "infinite (powers g)"
      then have "infinite X" using hXG hX2 hXpow by (metis Int_absorb1 hXgne hXsub hgG 
        infinite_smul_right invertible le_iff_inf powers_submonoid submonoid.subset)
      then show False using hXYM M_def by auto
    qed
    ultimately have "card (powers g) \<le> card X" using card_le_smul_right 
      powers_submonoid submonoid.subset hXYM M_def habX hXG 
      by (metis (no_types, lifting) hXfin hgG insert_subset invertible subsetD)
    then have "p \<le> card X" 
      by (meson hfinpowers hg1 hgG le_trans powers_ne_one powers_subgroup subgroup_infinite_or_ge)
    then have "p \<le> card (X \<cdots> Y)" using card_le_smul_left hXYM M_def 
      by (metis (full_types) \<open>b \<in> smul X {inverse a \<cdot> b}\<close> bot_nat_0.extremum_uniqueI card.infinite 
          card_0_eq card_le_smul_right empty_iff hXY hXfin hYG le_trans smul.cases)
    then show False using hXYlt by auto
  qed
  let ?X1 = "(X \<cdots> {g}) \<inter> X"
  let ?X2 = "(X \<cdots> {g}) \<union> X"
  let ?Y1 = "({inverse g} \<cdots> Y) \<union> Y"
  let ?Y2 = "({inverse g} \<cdots> Y) \<inter> Y"
  have hY1G: "?Y1 \<subseteq> G" and hY1fin: "finite ?Y1" and hX2G: "?X2 \<subseteq> G" and hX2fin: "finite ?X2" 
    using hYfin hYG hXG finite_smul hXfin smul_subset_carrier by auto
  have hXY1: "?X1 \<cdots> ?Y1 \<subseteq> X \<cdots> Y"
  proof
    fix z assume "z \<in> ?X1 \<cdots> ?Y1"
    then obtain x y where hz: "z = x \<cdot> y" and hx: "x \<in> ?X1" and hy: "y \<in> ?Y1" by (meson smul.cases)
    show "z \<in> X \<cdots> Y"
    proof(cases "y \<in> Y")
      case True
      then show ?thesis using hz hx smulI hXG hYG by auto
    next
      case False
      then obtain w where "y = inverse g \<cdot>  w" and "w \<in> Y" using hy smul.cases by (metis UnE singletonD)
      moreover obtain v where "x = v \<cdot> g" and "v \<in> X" using hx smul.cases by blast
      ultimately show ?thesis using hz hXG hYG hgG associative invertible_right_inverse2
        by (simp add: smul.smulI subsetD)
    qed
  qed
  have hXY2: "?X2 \<cdots> ?Y2 \<subseteq> X \<cdots> Y"
  proof
    fix z assume "z \<in> ?X2 \<cdots> ?Y2"
    then obtain x y where hz: "z = x \<cdot> y" and hx: "x \<in> ?X2" and hy: "y \<in> ?Y2" by (meson smul.cases)
    show "z \<in> X \<cdots> Y"
    proof(cases "x \<in> X")
      case True
      then show ?thesis using hz hy smulI hXG hYG by auto
    next
      case False
      then obtain v where "x = v \<cdot> g" and "v \<in> X" using hx smul.cases by (metis UnE singletonD)
      moreover obtain w where "y = inverse g \<cdot> w" and "w \<in> Y" using hy smul.cases by blast
      ultimately show ?thesis using hz hXG hYG hgG associative invertible_right_inverse2
        by (simp add: smul.smulI subsetD)
    qed
  qed
  have hY2ne: "?Y2 \<noteq> {}"
  proof
    assume hY2: "?Y2 = {}"
    have "card X + card Y \<le> card Y + card Y" by (simp add: hXY)
    also have "... = card ?Y1" using card_Un_disjoint hYfin hYG hgG finite_smul inf.orderE invertible
      by (metis hY2 card_smul_singleton_left_eq finite.emptyI finite.insertI invertible_inverse_closed)
    also have "... \<le> card (?X1 \<cdots> ?Y1)" using card_le_smul_right[OF _ _ _ hY1fin hY1G] 
        hXgne hXG Int_assoc Int_commute ex_in_conv finite_Int hXfin smul.simps smul_D(2) 
        smul_Int_carrier unit_closed by auto
    also have "... \<le> card (X \<cdots> Y)" using hXY1 finite_smul card_mono by (metis hXfin hYfin)
    finally show False using hXYlt by linarith
  qed
  have hXadd: "card ?X1 + card ?X2 = 2 * card X" 
    using card_smul_singleton_right_eq hgG hXfin hXG card_Un_Int
    by (metis Un_Int_eq(3) add.commute finite.emptyI finite.insertI finite_smul mult_2 subset_Un_eq)
  have hYadd: "card ?Y1 + card ?Y2 = 2 * card Y"
    using card_smul_singleton_left_eq hgG hYfin hYG card_Un_Int finite_smul
    by (metis Int_lower1 Un_Int_eq(3) card_0_eq card_Un_le card_seteq finite.emptyI finite.insertI  
      hY2ne le_add_same_cancel1 mult_2 subset_Un_eq)
  show False
  proof (cases "card ?X2 + card ?Y2 > card X + card Y")
    case h: True
    have hXY2le: "card (?X2 \<cdots> ?Y2) \<le> card (X \<cdots> Y)" using hXY2 finite_smul card_mono by (metis hXfin hYfin)
    also have "... < min p (card X + card Y - 1)" using hXYlt by auto
    also have "... \<le> min p (card ?X2 + card ?Y2 - 1)" using h by simp
    finally have hXY1M: "(?X2, ?Y2) \<in> M" using M_def hY2ne hX2fin hX2G hXYM by auto
    moreover have "((?X2, ?Y2), (X, Y)) \<in>  Restr devos_rel ?fin" using hXYM M_def hXY1M h hXY2le 
        devos_rel_iff by auto
    ultimately show False using hmin by blast 
  next
    case False
    then have h: "card ?X1 + card ?Y1 \<ge> card X + card Y" using hXadd hYadd by linarith
    have hX1lt: "card ?X1 < card X" using hXfin by (simp add: hpsubX psubset_card_mono)
    have hXY1le: "card (?X1 \<cdots> ?Y1) \<le> card (X \<cdots> Y)" using hXY1 finite_smul card_mono hYfin hXfin by metis
    also have "... < min p (card X + card Y - 1)" using hXYlt by auto
    also have "... \<le> min p (card ?X1 + card ?Y1 - 1)" using h by simp
    finally have hXY1M: "(?X1, ?Y1) \<in> M" using M_def hXgne hY1fin hY1G hXYM by auto
    moreover have "((?X1, ?Y1), (X, Y)) \<in>  Restr devos_rel ?fin" using hXYM M_def hXY1M h hXY1le 
        devos_rel_iff hX1lt hXY1le h by force
    ultimately show ?thesis using hmin by blast
  qed
qed


end