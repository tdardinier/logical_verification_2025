/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe09_OperationalSemantics_ExerciseSheet
import LoVe.LoVe10_HoareLogic_Demo


/- # LoVe Homework 10 (10 points + 1 bonus point): Hoare Logic

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1 (5 points): Factorial

The following WHILE program is intended to compute the factorial of `n₀`, leaving
the result in `r`. -/

def FACT : Stmt :=
  Stmt.assign "i" (fun _ ↦ 0);
  Stmt.assign "r" (fun _ ↦ 1);
  Stmt.whileDo (fun s ↦ s "i" ≠ s "n")
    (Stmt.assign "i" (fun s ↦ s "i" + 1);
     Stmt.assign "r" (fun s ↦ s "r" * s "i"))

/-
i := 0
r := 1
while i ≠ n do
  i := i  + 1
  r := r * i
end
-/

/- Recall the definition of the `fact` function: -/

#print fact

/- Let us register its recursive equations as simplification rules to
strengthen the simplifier and `aesop`, using some new Lean syntax: -/

attribute [simp] fact

/- Prove the correctness of `FACT` using `vcg`.

Hint: Remember to strengthen the loop invariant with `s "n" = n₀` to
capture the fact that the variable `n` does not change. -/

lemma natural_number_strictly_smaller {i n: Nat}
  (leq: i ≤ n) (diff: i ≠ n)
:
  i + 1 ≤ n :=
  sorry


lemma same_with_inv I:
  Stmt.whileDo = Stmt.invWhileDo I :=
    by
      apply funext
      intro b
      apply funext
      intro C
      simp [Stmt.invWhileDo]


theorem FACT_correct (n₀ : ℕ) :
    {* fun s ↦ s "n" = n₀ *} (FACT) {* fun s ↦ s "r" = fact n₀ *} := by
      rw [FACT]
      rw [same_with_inv (fun s => s "r" = fact (s "i") ∧ s "i" ≤ s "n" ∧ s "n" = n₀)]
      vcg
      simp
      intro s h1 h2 h3 h4
      apply And.intro _ (And.intro _ h3)
      rw [h1]
      ac_rfl
      exact natural_number_strictly_smaller h2 h4
      intro s h1 h2
      have hin: s "i" = s "n" := by
        aesop
      simp [h2, hin]
      simp


/- ## Question 2 (5 points + 1 bonus point):
## Hoare Logic for the Guarded Command Language

Recall the definition of GCL from exercise 9: -/

namespace GCL

#check Stmt
#check BigStep

/- The definition of Hoare triples for partial correctness is unsurprising: -/

def PartialHoare (P : State → Prop) (S : Stmt) (Q : State → Prop) : Prop :=
  ∀s t, P s → (S, s) ⟹ t → Q t

macro (priority := high) "{*" P:term " *} " "(" S:term ")" " {* " Q:term " *}" :
  term =>
  `(PartialHoare $P $S $Q)

namespace PartialHoare

/- 2.1 (5 points). Prove the following Hoare rules: -/

theorem consequence {P P' Q Q' S} (h : {* P *} (S) {* Q *})
      (hp : ∀s, P' s → P s) (hq : ∀s, Q s → Q' s) :
    {* P' *} (S) {* Q' *} := by
    rw [PartialHoare] at *
    intro s s' pre trans
    apply hq s'
    apply h s
    apply hp s pre
    exact trans

theorem assign_intro {P x a} :
    {* fun s ↦ P (s[x ↦ a s]) *} (Stmt.assign x a) {* P *} :=
    by simp [PartialHoare]

theorem assert_intro {P Q : State → Prop} :
    {* fun s ↦ Q s → P s *} (Stmt.assert Q) {* P *} :=
    by simp [PartialHoare]

theorem seq_intro {P Q R S T}
      (hS : {* P *} (S) {* Q *}) (hT : {* Q *} (T) {* R *}) :
    {* P *} (Stmt.seq S T) {* R *} := by
      simp [PartialHoare] at *
      intro s s' pre s'' trans1 trans2
      apply hT s''
      apply hS s
      exact pre
      exact trans1
      exact trans2


theorem choice_intro {P Q Ss}
      (h : ∀i (hi : i < List.length Ss), {* P *} (Ss[i]'hi) {* Q *}) :
    {* P *} (Stmt.choice Ss) {* Q *} := by
    simp [PartialHoare] at *
    intro s s' pre i h_wf trans
    exact h i _ s _ pre trans


/- 2.2 (1 bonus point). Prove the rule for `loop`. Notice the similarity with
the rule for `while` in the WHILE language. -/

theorem loop_intro {P S} (h : {* P *} (S) {* P *}) :
    {* P *} (Stmt.loop S) {* P *} := by
    rw [PartialHoare] at *
    intro s s' pre trans

    generalize ws_eq : (S.loop, s) = Ss
    rw [ws_eq] at trans
    induction trans generalizing s with
    | loop_more C s1 s2 s3 hone hloop ih hloop_ih =>
      apply hloop_ih s2
      apply h s _ pre
      aesop
      aesop
    | loop_stop => aesop
    | _ => cases ws_eq


end PartialHoare

end GCL

end LoVe
