theory hw1
imports Main
begin

datatype \<Phi> = P int | Neg \<Phi> | Or \<Phi> \<Phi> 
            (* | And \<Phi> \<Phi> | Imp \<Phi> \<Phi> *)
type_synonym \<Sigma> = "int \<Rightarrow> bool"

fun interp :: "\<Sigma> \<Rightarrow> \<Phi> \<Rightarrow> bool" where
  "interp \<sigma> (P n) = \<sigma> n"
| "interp \<sigma> (Neg \<phi>) = (\<not> (interp \<sigma> \<phi>))"
| "interp \<sigma> (Or \<phi>\<^sub>1 \<phi>\<^sub>2) = (interp \<sigma> \<phi>\<^sub>1 \<or> interp \<sigma> \<phi>\<^sub>2)"
(*
| "interp \<sigma> (And \<phi>\<^sub>1 \<phi>\<^sub>2) = (interp \<sigma> \<phi>\<^sub>1 \<and> interp \<sigma> \<phi>\<^sub>2)"
| "interp \<sigma> (Imp \<phi>\<^sub>1 \<phi>\<^sub>2) = (interp \<sigma> \<phi>\<^sub>1 \<longrightarrow> interp \<sigma> \<phi>\<^sub>2)"
*)

abbreviation "And \<phi>\<^sub>1 \<phi>\<^sub>2 \<equiv> Neg (Or (Neg \<phi>\<^sub>1) (Neg \<phi>\<^sub>2))"
abbreviation "Imp \<phi>\<^sub>1 \<phi>\<^sub>2 \<equiv> Or (Neg \<phi>\<^sub>1) \<phi>\<^sub>2"

abbreviation "tt \<equiv> Or (P 0) (Neg (P 0))"
abbreviation "ff \<equiv> And (P 0) (Neg (P 0))"

fun BAnd :: "\<Phi> list \<Rightarrow> \<Phi>" where
  "BAnd [] = tt"
| "BAnd (\<phi> # \<phi>s) = And \<phi> (BAnd \<phi>s)"

fun BOr :: "\<Phi> list \<Rightarrow> \<Phi>" where
  "BOr [] = ff"
| "BOr (\<phi> # \<phi>s) = Or \<phi> (BOr \<phi>s)"

type_synonym \<Gamma> = "\<Phi> list"
type_synonym \<Delta> = "\<Phi> list"

inductive proves :: "\<Gamma> \<Rightarrow> \<Delta> \<Rightarrow> bool" where
  I    : "proves [\<phi>] [\<phi>]"
| Cut  : "\<lbrakk>proves \<Gamma>\<^sub>1 (\<phi> # \<Delta>\<^sub>1); proves (\<phi> # \<Gamma>\<^sub>2) \<Delta>\<^sub>2\<rbrakk>
          \<Longrightarrow> proves (\<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2) (\<Delta>\<^sub>1 @ \<Delta>\<^sub>2)"
| orL  : "\<lbrakk>proves (\<phi>\<^sub>1 # \<Gamma>\<^sub>1) \<Delta>\<^sub>1; proves (\<phi>\<^sub>2 # \<Gamma>\<^sub>2) \<Delta>\<^sub>2\<rbrakk>
          \<Longrightarrow> proves (Or \<phi>\<^sub>1 \<phi>\<^sub>2 # \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2) (\<Delta>\<^sub>1 @ \<Delta>\<^sub>2)"
| orR1 : "proves \<Gamma> (\<phi>\<^sub>1 # \<Delta>) \<Longrightarrow> proves \<Gamma> (Or \<phi>\<^sub>1 \<phi>\<^sub>2 # \<Delta>)"
| orR2 : "proves \<Gamma> (\<phi>\<^sub>2 # \<Delta>) \<Longrightarrow> proves \<Gamma> (Or \<phi>\<^sub>1 \<phi>\<^sub>2 # \<Delta>)"
| notL : "proves \<Gamma> (\<phi> # \<Delta>) \<Longrightarrow> proves (Neg \<phi> # \<Gamma>) \<Delta>"
| notR : "proves (\<phi> # \<Gamma>) \<Delta> \<Longrightarrow> proves \<Gamma> (Neg \<phi> # \<Delta>)"
| WL   : "proves \<Gamma> \<Delta> \<Longrightarrow> proves (\<phi> # \<Gamma>) \<Delta>"
| WR   : "proves \<Gamma> \<Delta> \<Longrightarrow> proves \<Gamma> (\<phi> # \<Delta>)"
| CL   : "proves (\<phi> # \<phi> # \<Gamma>) \<Delta> \<Longrightarrow> proves (\<phi> # \<Gamma>) \<Delta>"
| CR   : "proves \<Gamma> (\<phi> # \<phi> # \<Delta>) \<Longrightarrow> proves \<Gamma> (\<phi> # \<Delta>)"
| PL   : "proves (\<Gamma>\<^sub>1 @ [\<phi>\<^sub>1, \<phi>\<^sub>2] @ \<Gamma>\<^sub>2) \<Delta> \<Longrightarrow> proves (\<Gamma>\<^sub>1 @ [\<phi>\<^sub>2, \<phi>\<^sub>1] @ \<Gamma>\<^sub>2) \<Delta>"
| PR   : "proves \<Gamma> (\<Delta>\<^sub>1 @ [\<phi>\<^sub>1, \<phi>\<^sub>2] @ \<Delta>\<^sub>2) \<Longrightarrow> proves \<Gamma> (\<Delta>\<^sub>1 @ [\<phi>\<^sub>2, \<phi>\<^sub>1] @ \<Delta>\<^sub>2)"
(* Derived rules
| andL1: "proves (\<Gamma> @ [\<phi>\<^sub>1]) \<Delta> \<Longrightarrow> proves (\<Gamma> @ [And \<phi>\<^sub>1 \<phi>\<^sub>2]) \<Delta>"
| andL2: "proves (\<Gamma> @ [\<phi>\<^sub>2]) \<Delta> \<Longrightarrow> proves (\<Gamma> @ [And \<phi>\<^sub>1 \<phi>\<^sub>2]) \<Delta>"
| andR : "\<lbrakk>proves \<Gamma>\<^sub>1 (\<phi>\<^sub>1 # \<Delta>\<^sub>1); proves \<Gamma>\<^sub>2 (\<phi>\<^sub>2 # \<Delta>\<^sub>2)\<rbrakk>
          \<Longrightarrow> proves (\<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2) (And \<phi>\<^sub>1 \<phi>\<^sub>2 # \<Delta>\<^sub>1 @ \<Delta>\<^sub>2)"
| impL : "\<lbrakk>proves \<Gamma>\<^sub>1 (\<phi>\<^sub>1 # \<Delta>\<^sub>1); proves (\<Gamma>\<^sub>2 @ [\<phi>\<^sub>2]) \<Delta>\<^sub>2\<rbrakk>
          \<Longrightarrow> proves (\<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2 @ [Imp \<phi>\<^sub>1 \<phi>\<^sub>2]) (\<Delta>\<^sub>1 @ \<Delta>\<^sub>2)"
| impR : "proves (\<Gamma> @ [\<phi>\<^sub>1]) (\<phi>\<^sub>2 # \<Delta>) \<Longrightarrow> proves \<Gamma> (Imp \<phi>\<^sub>1 \<phi>\<^sub>2 # \<Delta>)"
*)

abbreviation "valid \<phi> \<equiv> proves [] [\<phi>]"

lemma "valid (Or (P 0) (Neg (P 0)))"
by (rule CR, rule orR2, rule notR, rule orR1, rule I)

(** Q1 *)
inductive dual\<^sub>1 :: "(bool \<Rightarrow> bool) \<Rightarrow> (bool \<Rightarrow> bool) \<Rightarrow> bool" for R where
  du1: "R x = (\<not> (R' (\<not> x))) \<Longrightarrow> dual\<^sub>1 R R'"

inductive dual\<^sub>2 :: "(bool \<Rightarrow> bool \<Rightarrow> bool) \<Rightarrow> (bool \<Rightarrow> bool \<Rightarrow> bool) \<Rightarrow> bool" for R where
  du2: "R x y = (\<not> (R' (\<not> x) (\<not> y))) \<Longrightarrow> dual\<^sub>2 R R'"

(* a *)
lemma "dual\<^sub>1 Not Not" by (auto simp add: du1)

(* b *)
fun q2b :: "bool \<Rightarrow> bool \<Rightarrow> bool" (infixr "\<triangleright>" 40) where
  "q2b False True = True"
| "q2b _ _ = False"

lemma "dual\<^sub>2 (op \<longrightarrow>) (op \<triangleright>)"
apply (rule du2)
by auto

(* TODO c *)


(** Q2 *)

lemma a: "valid (Imp (And (P 0) (Neg (P 0))) (P 1))"
by (rule orR1, rule notR, rule notL, rule CR, rule orR2, rule notR, rule orR1, rule I)

lemma b: "valid (Imp (And (P 0) (Or (P 1) (P 2))) (Or (P 0) (P 2)))"
by (rule CR, rule orR1, rule notR, rule orR2, rule orR1, rule notL, rule orR1, rule notR, rule I)

end
