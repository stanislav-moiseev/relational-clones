theory common
imports Main
begin

(**************************************************************************************************)
subsection "Preliminaries"

datatype dom3 = V0 | V1 | V2

lemma UNIV_dom3: "UNIV = {V0, V1, V2}"
  by (auto intro: dom3.exhaust)
  
instantiation dom3 :: enum begin
  definition "enum_dom3 \<equiv> [V0, V1, V2]"
  definition "enum_all_dom3 P \<equiv> P V0 \<and> P V1 \<and> P V2"
  definition "enum_ex_dom3 P \<equiv> P V0 \<or> P V1 \<or> P V2"
  instance proof
  qed (simp_all only: enum_dom3_def enum_all_dom3_def enum_ex_dom3_def UNIV_dom3, simp_all)
  end

(*
lemma dom3_all: "P V0 ∧ P V1 \<and> P V2 \<Longrightarrow> (\<forall>x. P x)"
  by (rule allI; induct_tac rule: dom3.induct; simp)
*)


(**************************************************************************************************)
subsection "Operations over predicates"

type_synonym pred2 = "dom3 \<Rightarrow> dom3 \<Rightarrow> bool"

definition p_false :: "pred2" where
  "p_false x1 x2 \<equiv>  False"

definition p_true :: "pred2" where
  "p_true x1 x2 \<equiv> True"

definition p_eq :: "pred2" where
  "p_eq x1 x2 \<equiv> (x1 = x2)"


(* permutation, \<leftrightarrow>p *)
definition op_perm :: "pred2 \<Rightarrow> pred2" where
  "(op_perm p) x1 x2 \<equiv> p x2 x1"

(* conjunction (a.k.a. intersection), p1 \<inter> p2 *)
definition op_conj :: "pred2 \<Rightarrow> pred2 \<Rightarrow> pred2" where
  "(op_conj p1 p2) x1 x2 \<equiv> (p1 x1 x2 \<and> p2 x1 x2)"

(* composition, (p1 \<circ> p2) x1 x2 \<equiv> (\<exists>y. p1 x1 y \<and> p2 y x2)" *)
definition op_comp :: "pred2 \<Rightarrow> pred2 \<Rightarrow> pred2" where
  "(op_comp p1 p2) x1 x2 \<equiv> (\<exists>y. p1 x1 y \<and> p2 y x2)"


(**************************************************************************************************)
section "Weak closure operator on predicates of arity $2$"

inductive_set closure :: "pred2 set \<Rightarrow> pred2 set" ("\<langle>_\<rangle>")
  for M :: "pred2 set"
where
   closure_p_false: "p_false \<in> \<langle>M\<rangle>"
 | closure_p_true:  "p_true \<in> \<langle>M\<rangle>"
 | closure_p_eq:    "p_eq \<in> \<langle>M\<rangle>"
 | closure_base:    "\<lbrakk>p \<in> M\<rbrakk> \<Longrightarrow> p \<in> \<langle>M\<rangle>"
 | closure_op_perm: "\<lbrakk>p \<in> \<langle>M\<rangle>\<rbrakk> \<Longrightarrow> op_perm p \<in> \<langle>M\<rangle>"
 | closure_op_conj: "\<lbrakk>p1 \<in> \<langle>M\<rangle>; p2 \<in> \<langle>M\<rangle>\<rbrakk> \<Longrightarrow> op_conj p1 p2 \<in> \<langle>M\<rangle>"
 | closure_op_comp: "\<lbrakk>p1 \<in> \<langle>M\<rangle>; p2 \<in> \<langle>M\<rangle>\<rbrakk> \<Longrightarrow> op_comp p1 p2 \<in> \<langle>M\<rangle>"


subsubsection "Basic properties of weak closure operator"

lemma closure_extensive: "M \<subseteq> \<langle>M\<rangle>"
  using closure.closure_base apply blast
done

lemma closure_monotone: "M1 \<subseteq> M2 \<Longrightarrow> \<langle>M1\<rangle> \<subseteq> \<langle>M2\<rangle>"
  apply auto
  apply (erule closure.induct)
    using closure.closure_p_false apply blast
    using closure.closure_p_true apply blast
    using closure.closure_p_eq apply blast
    using closure.closure_base apply blast
    using closure.closure_op_perm apply blast
    using closure.closure_op_conj apply blast
    using closure.closure_op_comp apply blast
done

lemma closure_idempotent: "\<langle>\<langle>M\<rangle>\<rangle> = \<langle>M\<rangle>"
  apply auto
  apply (erule closure.induct)
    using closure.closure_p_false apply blast
    using closure.closure_p_true apply blast
    using closure.closure_p_eq apply blast
    using closure.closure_base apply blast
    using closure.closure_op_perm apply blast
    using closure.closure_op_conj apply blast
    using closure.closure_op_comp apply blast
  using closure.closure_base apply blast
done

lemma closure_idempotent_cup: "\<langle>A \<union> \<langle>M\<rangle>\<rangle> = \<langle>A \<union> M\<rangle>"
proof
  show "\<langle>A \<union> \<langle>M\<rangle>\<rangle> \<subseteq> \<langle>A \<union> M\<rangle>"
  proof -
    have 1: "A \<subseteq> \<langle>A \<union> M\<rangle>" using closure_base by blast 
    have 2: "\<langle>M\<rangle> \<subseteq> \<langle>A \<union> M\<rangle>" using closure_monotone by auto 
    have 3: "A \<union> \<langle>M\<rangle> \<subseteq> \<langle>A \<union> M\<rangle>" using 1 2 by (rule Un_least)
    show ?thesis using 3 closure_monotone closure_idempotent by blast
  qed
  
  show "\<langle>A \<union> M\<rangle> \<subseteq> \<langle>A \<union> \<langle>M\<rangle>\<rangle>" using closure_extensive closure_monotone set_eq_subset Un_mono by metis
qed



(**************************************************************************************************)
section "The set of all weakly closed sets of predicates"

inductive_set relational_clones :: "(pred2 set) set"
where
  rel_clones_empty: "\<langle>{}\<rangle> \<in> relational_clones"
| rel_clones_step:  "\<lbrakk>C \<in> relational_clones\<rbrakk> \<Longrightarrow> \<langle>C \<union> {p}\<rangle> \<in> relational_clones"

text "Validation of the definition. The following two theorems state that the
(inductively defined) set $relational_clones$ is exactly the set of all
relational clones."

theorem rel_clones_correctness: "C \<in> relational_clones \<Longrightarrow> \<langle>C\<rangle> = C"
  apply (erule relational_clones.induct)
  apply (rule closure_idempotent)
  apply (rule closure_idempotent)
done

theorem rel_clones_validity:
  assumes "finite M"     (* TODO: remove this obvious assumption *)
  shows "\<langle>M\<rangle> \<in> relational_clones"
using assms proof (induct M rule: finite_induct)
  case empty (* M = {} *)
    show ?case using relational_clones.rel_clones_empty by simp
    
  case (insert p M) (* M = {p} \<union> M' *)
    have 1: "\<langle>{p} \<union> \<langle>M\<rangle>\<rangle> \<in> relational_clones" using insert.hyps relational_clones.rel_clones_step by auto
    have 2: "\<langle>{p} \<union> \<langle>M\<rangle>\<rangle> = \<langle>{p} \<union> M\<rangle>" using closure_idempotent_cup by blast
    show ?case using 1 2 by auto
qed



(*
text "The list of all weakly closed set containing p_false, p_true, p_eq."
inductive_set all_clones :: "(pred2 set) set" where
  "clone0 \<in> all_clones"
| "clone1 \<in> all_clones"

text "This is a temporal hack."
lemma small_dom: "P p_false \<Longrightarrow> P p_true \<Longrightarrow> P p_eq \<Longrightarrow> P p_neq \<Longrightarrow> P p"
sorry


theorem
  assumes "M \<in> relational_clones"
  shows "M \<in> all_clones"
using assms proof (induct rule: relational_clones.induct)
  case rel_clones_empty
  show "\<langle>{}\<rangle> \<in> all_clones" using all_clones.intros clone0_def cl_empty by auto
  
  case (rel_clones_step C p)
  show "C \<in> all_clones \<Longrightarrow> \<langle>C \<union> {p}\<rangle> \<in> all_clones"
    proof (erule all_clones.induct; induct p rule: small_dom)
      -- "clone0 \<union> {p} \<in> all_clones
      show "\<langle>clone0 \<union> {p_false}\<rangle> \<in> all_clones" using all_clones.intros cl_clone0_plus_false by auto
      show "\<langle>clone0 \<union> {p_true}\<rangle> \<in> all_clones" using all_clones.intros cl_clone0_plus_true by auto
      show "\<langle>clone0 \<union> {p_eq}\<rangle> \<in> all_clones" using all_clones.intros cl_clone0_plus_eq by auto
      show "\<langle>clone0 \<union> {p_neq}\<rangle> \<in> all_clones" using all_clones.intros cl_clone0_plus_neq by auto
      -- "clone1 \<union> {p} \<in> all_clones"
      show "\<langle>clone1 \<union> {p_false}\<rangle> \<in> all_clones" using all_clones.intros cl_clone1_plus_false by auto
      show "\<langle>clone1 \<union> {p_true}\<rangle> \<in> all_clones" using all_clones.intros cl_clone1_plus_true by auto
      show "\<langle>clone1 \<union> {p_eq}\<rangle> \<in> all_clones" using all_clones.intros cl_clone1_plus_eq by auto
      show "\<langle>clone1 \<union> {p_neq}\<rangle> \<in> all_clones" using all_clones.intros cl_clone1_plus_neq by auto
    qed
qed
*)


end



