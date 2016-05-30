theory common
imports Main
begin

datatype dom3 = V0 | V1 | V2

type_synonym pred2 = "dom3 \<Rightarrow> dom3 \<Rightarrow> bool"

(* permutation, \<leftrightarrow>p *)
definition op_perm :: "pred2 \<Rightarrow> pred2" where
  "(op_perm p) x1 x2 \<equiv> p x2 x1"

(* conjunction (a.k.a. intersection), p1 \<inter> p2 *)
definition op_conj :: "pred2 \<Rightarrow> pred2 \<Rightarrow> pred2" where
  "(op_conj p1 p2) x1 x2 \<equiv> (p1 x1 x2 \<and> p2 x1 x2)"

(* composition, (p1 \<circ> p2) x1 x2 \<equiv> (\<exists>y. p1 x1 y \<and> p2 y x2)" *)
definition op_comp :: "pred2 \<Rightarrow> pred2 \<Rightarrow> pred2" where
  "(op_comp p1 p2) x1 x2 \<equiv> (p1 x1 V0 \<and> p2 V0 x2)
                         \<or> (p1 x1 V1 \<and> p2 V1 x2)
                         \<or> (p1 x1 V2 \<and> p2 V2 x2)"

end
