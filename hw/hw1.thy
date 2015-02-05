theory hw1
imports Main
begin

datatype \<Phi> = P int | Neg \<Phi> | Or \<Phi> \<Phi> (* using `int` for variable names *)
type_synonym \<Sigma> = "int \<Rightarrow> bool"
type_synonym \<Gamma> = "\<Phi> list"
type_synonym \<Delta> = "\<Phi> list"

fun interp :: "\<Sigma> \<Rightarrow> \<Phi> \<Rightarrow> bool" (infix "\<Turnstile>" 40) where
  "(op \<Turnstile>) \<sigma> (P n) = \<sigma> n"
| "(op \<Turnstile>) \<sigma> (Neg \<phi>) = (\<not> \<sigma> \<Turnstile> \<phi>)"
| "(op \<Turnstile>) \<sigma> (Or \<phi>\<^sub>1 \<phi>\<^sub>2) = (\<sigma> \<Turnstile> \<phi>\<^sub>1 \<or> \<sigma> \<Turnstile> \<phi>\<^sub>2)"

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

inductive proves :: "\<Gamma> \<Rightarrow> \<Delta> \<Rightarrow> bool" (infix "\<turnstile>" 40) where
  I    : "[\<phi>] \<turnstile> [\<phi>]"
(* | Cut  : "\<lbrakk>\<Gamma>\<^sub>1 \<turnstile> \<phi> # \<Delta>\<^sub>1; \<phi> # \<Gamma>\<^sub>2 \<turnstile> \<Delta>\<^sub>2\<rbrakk>
          \<Longrightarrow> \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2 \<turnstile> \<Delta>\<^sub>1 @ \<Delta>\<^sub>2" *)
| orL  : "\<lbrakk>\<phi>\<^sub>1 # \<Gamma>\<^sub>1 \<turnstile> \<Delta>\<^sub>1; \<phi>\<^sub>2 # \<Gamma>\<^sub>2 \<turnstile> \<Delta>\<^sub>2\<rbrakk>
          \<Longrightarrow> Or \<phi>\<^sub>1 \<phi>\<^sub>2 # \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2 \<turnstile> \<Delta>\<^sub>1 @ \<Delta>\<^sub>2"
| orR1 : "\<Gamma> \<turnstile> (\<phi>\<^sub>1 # \<Delta>) \<Longrightarrow> \<Gamma> \<turnstile> Or \<phi>\<^sub>1 \<phi>\<^sub>2 # \<Delta>"
| orR2 : "\<Gamma> \<turnstile> (\<phi>\<^sub>2 # \<Delta>) \<Longrightarrow> \<Gamma> \<turnstile> Or \<phi>\<^sub>1 \<phi>\<^sub>2 # \<Delta>"
| notL : "\<Gamma> \<turnstile> (\<phi> # \<Delta>) \<Longrightarrow> Neg \<phi> # \<Gamma> \<turnstile> \<Delta>"
| notR : "\<phi> # \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> Neg \<phi> # \<Delta>"
| WL   : "\<Gamma> \<turnstile> \<Delta> \<Longrightarrow> \<phi> # \<Gamma> \<turnstile> \<Delta>"
| WR   : "\<Gamma> \<turnstile> \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> \<phi> # \<Delta>"
| CL   : "\<phi> # \<phi> # \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> \<phi> # \<Gamma> \<turnstile> \<Delta>"
| CR   : "\<Gamma> \<turnstile> \<phi> # \<phi> # \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> \<phi> # \<Delta>"
| PL   : "\<Gamma>\<^sub>1 @ [\<phi>\<^sub>1, \<phi>\<^sub>2] @ \<Gamma>\<^sub>2 \<turnstile> \<Delta> \<Longrightarrow> \<Gamma>\<^sub>1 @ [\<phi>\<^sub>2, \<phi>\<^sub>1] @ \<Gamma>\<^sub>2 \<turnstile> \<Delta>"
| PR   : "\<Gamma> \<turnstile> \<Delta>\<^sub>1 @ [\<phi>\<^sub>1, \<phi>\<^sub>2] @ \<Delta>\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> \<Delta>\<^sub>1 @ [\<phi>\<^sub>2, \<phi>\<^sub>1] @ \<Delta>\<^sub>2"

theorem soundness: "\<Gamma> \<turnstile> \<Delta> \<Longrightarrow> \<sigma> \<Turnstile> Imp (BAnd \<Gamma>) (BOr \<Delta>)" sorry
theorem completeness: "\<sigma> \<Turnstile> Imp (BAnd \<Gamma>) (BOr \<Delta>) \<Longrightarrow> \<Gamma> \<turnstile> \<Delta>" sorry

(* Derived rules *)
lemma andL1: "\<phi>\<^sub>1 # \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> And \<phi>\<^sub>1 \<phi>\<^sub>2 # \<Gamma> \<turnstile> \<Delta>" by (auto simp: notL orR1 notR)
lemma andL2: "\<phi>\<^sub>2 # \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> And \<phi>\<^sub>1 \<phi>\<^sub>2 # \<Gamma> \<turnstile> \<Delta>" by (auto simp: notL orR2 notR)
lemma andR: "\<lbrakk>\<Gamma>\<^sub>1 \<turnstile> \<phi>\<^sub>1 # \<Delta>\<^sub>1; \<Gamma>\<^sub>2 \<turnstile> \<phi>\<^sub>2 # \<Delta>\<^sub>2\<rbrakk> \<Longrightarrow> \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2 \<turnstile> And \<phi>\<^sub>1 \<phi>\<^sub>2 # \<Delta>\<^sub>1 @ \<Delta>\<^sub>2"
by (auto simp: notR notL orL)
lemma impL: "\<lbrakk>\<Gamma>\<^sub>1 \<turnstile> \<phi>\<^sub>1 # \<Delta>\<^sub>1; \<phi>\<^sub>2 # \<Gamma>\<^sub>2 \<turnstile> \<Delta>\<^sub>2\<rbrakk> \<Longrightarrow> Imp \<phi>\<^sub>1 \<phi>\<^sub>2 # \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2 \<turnstile> \<Delta>\<^sub>1 @ \<Delta>\<^sub>2" sorry
lemma impR: "\<phi>\<^sub>1 # \<Gamma> \<turnstile> \<phi>\<^sub>2 # \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> Imp \<phi>\<^sub>1 \<phi>\<^sub>2 # \<Delta>"
apply (rule CR) by (auto simp: orR1 notR orR2)

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

abbreviation "valid \<phi> \<equiv> [] \<turnstile> [\<phi>]"

lemma a: "valid (Imp (And (P 0) (Neg (P 0))) (P 1))"
by (rule orR1, rule notR, rule notL, rule CR, rule orR2, rule notR, rule orR1, rule I)

lemma b: "valid (Imp (And (P 0) (Or (P 1) (P 2))) (Or (P 0) (P 2)))"
by (rule CR, rule orR1, rule notR, rule orR2, rule orR1, rule notL, rule orR1, rule notR, rule I)

(** Q3 *)

abbreviation "Eqv \<phi>\<^sub>1 \<phi>\<^sub>2 \<equiv> And (Imp \<phi>\<^sub>1 \<phi>\<^sub>2) (Imp \<phi>\<^sub>2 \<phi>\<^sub>1)"

lemma eqvR: "\<lbrakk>\<phi>\<^sub>1 # \<Gamma>\<^sub>1 \<turnstile> \<phi>\<^sub>2 # \<Delta>\<^sub>1; \<phi>\<^sub>2 # \<Gamma>\<^sub>2 \<turnstile> \<phi>\<^sub>1 # \<Delta>\<^sub>2\<rbrakk> \<Longrightarrow> \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2 \<turnstile> Eqv \<phi>\<^sub>1 \<phi>\<^sub>2 # \<Delta>\<^sub>1 @ \<Delta>\<^sub>2"
apply (rule andR)
apply (rule CR, rule orR1, rule notR, rule orR2, simp)
apply (rule CR, rule orR1, rule notR, rule orR2, simp)
done

lemma eqvL1: "\<phi>\<^sub>1 # \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> Eqv \<phi>\<^sub>1 \<phi>\<^sub>2 # \<Gamma> \<turnstile> \<Delta>" sorry
lemma eqvL2: "\<phi>\<^sub>2 # \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> Eqv \<phi>\<^sub>1 \<phi>\<^sub>2 # \<Gamma> \<turnstile> \<Delta>" sorry


end
