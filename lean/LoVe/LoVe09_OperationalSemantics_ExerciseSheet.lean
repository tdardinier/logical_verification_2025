/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe09_OperationalSemantics_Demo


/- # LoVe Exercise 9: Operational Semantics

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Guarded Command Language

In 1976, E. W. Dijkstra introduced the guarded command language (GCL), a
minimalistic imperative language with built-in nondeterminism. A grammar for one
of its variants is given below:

    S  ::=  x := e       -- assignment
         |  assert B     -- assertion
         |  S ; S        -- sequential composition
         |  S | ⋯ | S    -- nondeterministic choice
         |  loop S       -- nondeterministic iteration

Assignment and sequential composition are as in the WHILE language. The other
statements have the following semantics:

* `assert B` aborts if `B` evaluates to false; otherwise, the command is a
  no-op.

* `S | ⋯ | S` chooses any of the branches and executes it, ignoring the other
  branches.

* `loop S` executes `S` any number of times.

In Lean, GCL is captured by the following inductive type: -/

namespace GCL

inductive Stmt : Type
  | assign : String → (State → ℕ) → Stmt
  | assert : (State → Prop) → Stmt
  | seq    : Stmt → Stmt → Stmt
  | choice : List Stmt → Stmt
  | loop   : Stmt → Stmt

infixr:90 "; " => Stmt.seq

/- 1.1. Complete the following big-step semantics, based on the informal
specification of GCL above. -/

inductive BigStep : (Stmt × State) → State → Prop
  | assign x e s : BigStep (Stmt.assign x e, s) (s[x ↦ e s])
  | assert (B s) (hB : B s) :
    BigStep (Stmt.assert B, s) s
  | seq (C1 C2 s s'' s')
    (h1: BigStep (C1, s) s'') (h2: BigStep (C2, s'') s'):
    BigStep (Stmt.seq C1 C2, s) s'
  -- below, `Ss[i]'hless` returns element `i` of `Ss`, which exists thanks to
  -- condition `hless`
  | choice (Ss s t i) (hless : i < List.length Ss)
      (hbody : BigStep (Ss[i]'hless, s) t) :
    BigStep (Stmt.choice Ss, s) t
  | loop_more C s s'' s'
    (hone: BigStep (C, s) s'') (hloop: BigStep (Stmt.loop C, s'') s'):
    BigStep (Stmt.loop C, s) s'
  | loop_stop s : BigStep (Stmt.loop _, s) s

infixl:110 " ⟹ " => BigStep

/- 1.2. Prove the following inversion rules, as we did in the lecture for the
WHILE language. -/

@[simp] theorem BigStep_assign_iff {x a s t} :
    (Stmt.assign x a, s) ⟹ t ↔ t = s[x ↦ a s] :=
    by
      apply Iff.intro
      {
        intro h
        cases h
        simp
      }
      {
        intro h
        rw [h]
        apply BigStep.assign
      }

@[simp] theorem BigStep_assert {B s t} :
    (Stmt.assert B, s) ⟹ t ↔ t = s ∧ B s :=
    by
      apply Iff.intro
      {
        intro h
        cases h
        simp [hB]
      }
      {
        intro h
        rw [h.left]
        apply BigStep.assert
        apply h.right
      }

@[simp] theorem BigStep_seq_iff {S₁ S₂ s t} :
    (Stmt.seq S₁ S₂, s) ⟹ t ↔ (∃u, (S₁, s) ⟹ u ∧ (S₂, u) ⟹ t) :=
    by
      apply Iff.intro
      {
        intro h
        cases h
        apply Exists.intro
        apply And.intro <;> assumption
      }
      {
        intro h
        cases h
        apply BigStep.seq _ _ _ w <;> simp [h_1]
      }

theorem BigStep_loop {S s u} :
    (Stmt.loop S, s) ⟹ u ↔
    (s = u ∨ (∃t, (S, s) ⟹ t ∧ (Stmt.loop S, t) ⟹ u)) :=
  by
    apply Iff.intro
    {
    intro h
    cases h with
    | loop_stop => simp
    | loop_more =>
      apply Or.inr
      apply Exists.intro s''
      simp [hone, hloop]
    }
    {
      intro h
      cases h
      {
        rw [h_1]
        apply BigStep.loop_stop
      }
      {
        cases h_1
        apply BigStep.loop_more _ _ w
        simp [h]
        simp [h]
      }
    }

/- This one is more difficult: -/

@[simp] theorem BigStep_choice {Ss s t} :
    (Stmt.choice Ss, s) ⟹ t ↔
    (∃(i : ℕ) (hless : i < List.length Ss), (Ss[i]'hless, s) ⟹ t) :=
  by
    apply Iff.intro
    {
      intro h
      cases h
      apply Exists.intro i
      apply Exists.intro hless
      assumption
    }
    {
      intro h
      cases h
      cases h_1
      apply BigStep.choice _ _ _ w
      assumption
    }

end GCL

/- 1.3. Complete the translation below of a deterministic program to a GCL
program, by filling in the `sorry` placeholders below. -/

def gcl_of : Stmt → GCL.Stmt
  | Stmt.skip =>
    GCL.Stmt.assert (fun _ ↦ True)
  | Stmt.assign x a =>
    GCL.Stmt.assign x a
  | S; T =>
    (gcl_of S); (gcl_of T)
  | Stmt.ifThenElse B S T  =>
    GCL.Stmt.choice [(GCL.Stmt.assert B; gcl_of S), (GCL.Stmt.assert (fun s => ¬(B s)); gcl_of T)]
  | Stmt.whileDo B S =>
    (GCL.Stmt.loop (GCL.Stmt.assert B; gcl_of S)); (GCL.Stmt.assert (fun s => ¬(B s)))

/- 1.4. In the definition of `gcl_of` above, `skip` is translated to
`assert (fun _ ↦ True)`. Looking at the big-step semantics of both constructs,
we can convince ourselves that it makes sense. Can you think of other correct
ways to define the `skip` case? -/

-- enter your answer here
-- assign x (fun s => s "x")


/- ## Question 2: Program Equivalence

For this question, we introduce the notion of program equivalence: `S₁ ~ S₂`. -/

def BigStepEquiv (S₁ S₂ : Stmt) : Prop :=
  ∀s t, (S₁, s) ⟹ t ↔ (S₂, s) ⟹ t

infix:50 (priority := high) " ~ " => BigStepEquiv

/- Program equivalence is an equivalence relation, i.e., it is reflexive,
symmetric, and transitive. -/

theorem BigStepEquiv.refl {S} :
    S ~ S :=
  fix s t : State
  show (S, s) ⟹ t ↔ (S, s) ⟹ t from
    by rfl

theorem BigStepEquiv.symm {S₁ S₂} :
    S₁ ~ S₂ → S₂ ~ S₁ :=
  assume h : S₁ ~ S₂
  fix s t : State
  show (S₂, s) ⟹ t ↔ (S₁, s) ⟹ t from
    Iff.symm (h s t)

theorem BigStepEquiv.trans {S₁ S₂ S₃} (h₁₂ : S₁ ~ S₂) (h₂₃ : S₂ ~ S₃) :
    S₁ ~ S₃ :=
  fix s t : State
  show (S₁, s) ⟹ t ↔ (S₃, s) ⟹ t from
    Iff.trans (h₁₂ s t) (h₂₃ s t)

/- 2.1. Prove the following program equivalences. -/

theorem BigStepEquiv.skip_assign_id {x} :
    Stmt.assign x (fun s ↦ s x) ~ Stmt.skip :=
    by simp [BigStepEquiv]


theorem BigStepEquiv.seq_skip_left {S} :
    Stmt.skip; S ~ S :=
    by simp [BigStepEquiv]

theorem BigStepEquiv.seq_skip_right {S} :
    S; Stmt.skip ~ S :=
    by simp [BigStepEquiv]

theorem BigStepEquiv.if_seq_while_skip {B S} :
    Stmt.ifThenElse B (S; Stmt.whileDo B S) Stmt.skip ~ Stmt.whileDo B S :=
    by
      simp [BigStepEquiv]
      intro s t
      apply Iff.intro
      {
        intro h
        cases h
        simp_all
        rw [h_1.right]
        apply BigStep.while_false
        exact h_1.left
      }
      {
        intro h
        cases h
        simp_all
        apply Exists.intro t_1
        simp [hbody, hrest]
        apply Or.inr
        simp [hcond]
      }

/- 2.2 (**optional**). Program equivalence can be used to replace subprograms
by other subprograms with the same semantics. Prove the following so-called
congruence rules that facilitate such replacement: -/

lemma BigStepEquivE {C1 C2 s s'}
  (hequiv: C1 ~ C2) (hleft: (C1, s) ⟹  s'):
  (C2, s) ⟹  s' :=
  by
    rw [BigStepEquiv] at hequiv
    apply (hequiv s s').mp
    exact hleft

theorem BigStepEquiv.seq_congr {S₁ S₂ T₁ T₂} (hS : S₁ ~ S₂)
      (hT : T₁ ~ T₂) :
    S₁; T₁ ~ S₂; T₂ :=
    by
      simp [BigStepEquiv]
      intro s s'
      apply Iff.intro
      {
        intro h
        cases h
        cases h_1
        apply Exists.intro w
        apply And.intro
        apply BigStepEquivE hS left
        apply BigStepEquivE hT right
      }
      {
        intro h
        cases h
        cases h_1
        apply Exists.intro
        apply And.intro
        apply BigStepEquivE (BigStepEquiv.symm hS) left
        apply BigStepEquivE (BigStepEquiv.symm hT) right
      }


theorem BigStepEquiv.if_congr {B S₁ S₂ T₁ T₂} (hS : S₁ ~ S₂) (hT : T₁ ~ T₂) :
    Stmt.ifThenElse B S₁ T₁ ~ Stmt.ifThenElse B S₂ T₂ :=
    by
      simp [BigStepEquiv]
      intro s s'
      apply Iff.intro
      {
        intro h
        cases h
        cases h_1
        apply Or.inl
        apply And.intro left
        apply BigStepEquivE hS right
        cases h_1
        apply Or.inr
        apply And.intro left
        apply BigStepEquivE hT right
      }
      {
        intro h
        cases h
        cases h_1
        apply Or.inl
        apply And.intro left
        apply BigStepEquivE (BigStepEquiv.symm hS) right
        cases h_1
        apply Or.inr
        apply And.intro left
        apply BigStepEquivE (BigStepEquiv.symm hT) right
      }


end LoVe
