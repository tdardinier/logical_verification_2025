/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe Exercise 4: Forward Proofs -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Connectives and Quantifiers

1.1. Supply structured proofs of the following theorems. -/

theorem I (a : Prop) :
    a → a :=
    fix aa: a
    show a from aa

theorem K (a b : Prop) :
    a → b → b :=
    fix aa: a
    fix bb: b
    show b from bb

theorem C (a b c : Prop) :
    (a → b → c) → b → a → c :=
    fix abc: a → b → c
    fix bb: b
    fix aa: a
    show c from abc aa bb

theorem proj_fst (a : Prop) :
    a → a → a :=
    fix a1: a
    fix a2: a
    show a from a1

/- Please give a different answer than for `proj_fst`. -/

theorem proj_snd (a : Prop) :
    a → a → a :=
    fix a1: a
    fix a2: a
    show a from a2

theorem some_nonsense (a b c : Prop) :
    (a → b → c) → a → (a → c) → b → c :=
    fix abc: a → b → c
    fix aa: a
    fix ac: a → c
    fix bb: b
    show c from ac aa

/- 1.2. Supply a structured proof of the contraposition rule. -/

theorem contrapositive (a b : Prop) :
    (a → b) → ¬ b → ¬ a :=
    fix ab: a → b
    fix nb: ¬ b
    fix aa: a
    show False from nb (ab aa)

/- 1.3. Supply a structured proof of the distributivity of `∀` over `∧`. -/

theorem forall_and {α : Type} (p q : α → Prop) :
    (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) :=
    Iff.intro
    (
      assume pq: ∀x, p x ∧ q x
      show (∀x, p x) ∧ (∀x, q x) from
      And.intro
      (
        fix x: α
        have pqx: p x ∧ q x := pq x
        show p x from And.left pqx
      )
      (
        fix x: α
        have pqx: p x ∧ q x := pq x
        show q x from And.right pqx
      )
    )
    (
      assume pq: (∀x, p x) ∧ (∀x, q x)
      fix x: α
      show p x ∧ q x from
        And.intro
        (And.left pq x)
        (And.right pq x)
    )

/- 1.4 (**optional**). Supply a structured proof of the following property,
which can be used to pull a `∀` quantifier past an `∃` quantifier. -/

theorem forall_exists_of_exists_forall {α : Type} (p : α → α → Prop) :
    (∃x, ∀y, p x y) → (∀y, ∃x, p x y) :=
    assume hex: ∃x, ∀y, p x y
    fix y: α
    show ∃x, p x y from
    Exists.elim hex
    (

      fix x: α
      assume hxy: (∀ (y : α), p x y)
      show ∃ x, p x y from
      Exists.intro x (hxy y)
    )

/- ## Question 2: Chain of Equalities

2.1. Write the following proof using `calc`.

      (a + b) * (a + b)
    = a * (a + b) + b * (a + b)
    = a * a + a * b + b * a + b * b
    = a * a + a * b + a * b + b * b
    = a * a + 2 * a * b + b * b

Hint: This is a difficult question. You might need the tactics `simp` and
`ac_rfl` and some of the theorems `mul_add`, `add_mul`, `add_comm`, `add_assoc`,
`mul_comm`, `mul_assoc`, , and `Nat.two_mul`. -/
#check mul_add

theorem binomial_square (a b : ℕ) :
    (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
    calc
      (a + b) * (a + b) = a * (a + b) + b * (a + b) :=
        by rw [add_mul]
      _ = a * a + a * b + b * a + b * b :=
        by
          rw [mul_add, mul_add]
          ac_rfl
      _ = a * a + a * b + a * b + b * b :=
          by ac_rfl
      _ = a * a + 2 * a * b + b * b := by
        rw [Nat.two_mul, add_mul]
        ac_rfl


/- 2.2 (**optional**). Prove the same argument again, this time as a structured
proof, with `have` steps corresponding to the `calc` equations. Try to reuse as
much of the above proof idea as possible, proceeding mechanically. -/

theorem binomial_square₂ (a b : ℕ) :
    (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
      have h1: (a + b) * (a + b) = a * (a + b) + b * (a + b) :=
        by rw [add_mul]
      have h2: a * (a + b) + b * (a + b)  = a * a + a * b + b * a + b * b :=
        by
          rw [mul_add, mul_add]
          ac_rfl
      have h3: _ = a * a + a * b + a * b + b * b :=
          by ac_rfl
      have h4: _ = a * a + 2 * a * b + b * b := by
        rw [Nat.two_mul, add_mul]
        ac_rfl
      show _
      from
        Eq.trans (Eq.trans h1 h2) (Eq.trans h3 h4)


/- ## Question 3 (**optional**): One-Point Rules

3.1 (**optional**). Prove that the following wrong formulation of the one-point
rule for `∀` is inconsistent, using a structured proof. -/

axiom All.one_point_wrong {α : Type} (t : α) (P : α → Prop) :
    (∀x : α, x = t ∧ P x) ↔ P t

theorem All.proof_of_False :
    False :=
    have spec: (∀x : Nat, x = 0 ∧ True) ↔ True :=
      All.one_point_wrong 0 _
    have h: 1 = 0 ∧ True :=
      Iff.mpr spec True.intro 1
    show False by cases h.left

/- 3.2 (**optional**). Prove that the following wrong formulation of the
one-point rule for `∃` is inconsistent, using a structured proof. -/

axiom Exists.one_point_wrong {α : Type} (t : α) (P : α → Prop) :
    (∃x : α, x = t → P x) ↔ P t

theorem Exists.proof_of_False :
    False :=
    have h: (∃x : Nat, x = 1 → (fun x => False) x) :=
      Exists.intro 0
        (
          by
          intro hfalse
          cases hfalse
        )
    show False from
      Iff.mp (Exists.one_point_wrong 1 _) h

end LoVe
