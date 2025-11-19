/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe12_LogicalFoundationsOfMathematics_Demo


/- # LoVe Exercise 12: Logical Foundations of Mathematics

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Vectors as Subtypes

Recall the definition of vectors from the demo: -/

#check Vector

/- The following function adds two lists of integers elementwise. If one
function is longer than the other, the tail of the longer list is ignored. -/

def List.add : List ℤ → List ℤ → List ℤ
  | [],      []      => []
  | x :: xs, y :: ys => (x + y) :: List.add xs ys
  | [],      y :: ys => []
  | x :: xs, []      => []

/- 1.1. Show that if the lists have the same length, the resulting list also
has that length. -/

theorem List.length_add :
    ∀xs ys, List.length xs = List.length ys →
      List.length (List.add xs ys) = List.length xs
  | [], [] => by simp [List.add]
  | x :: xs, y :: ys => by
    intro h
    simp [List.add]
    apply List.length_add xs ys
    aesop
  | [], y :: ys =>
    by simp
  | x :: xs, [] =>
    by simp

/- 1.2. Define componentwise addition on vectors using `List.add` and
`List.length_add`. -/

def Vector.add {n : ℕ} (x y: Vector ℤ n): Vector ℤ n :=
  Subtype.mk (List.add x.val y.val) (by
    have h := Eq.symm (x.property)
    conv =>
      rhs
      rw [h]
    apply List.length_add
    have hh := y.property
    simp [h, hh]
  )

/- 1.3. Show that `List.add` and `Vector.add` are commutative. -/

theorem List.add.comm :
    ∀xs ys, List.add xs ys = List.add ys xs := by
    intro xs ys
    cases xs
    cases ys
    simp [List.add]
    simp [List.add]
    cases ys
    simp [List.add]
    simp [List.add]
    exact And.intro (by ac_rfl) (List.add.comm tail tail_1)

theorem Vector.add.comm {n : ℕ} (u v : Vector ℤ n) :
    Vector.add u v = Vector.add v u := by
    apply Subtype.eq
    apply List.add.comm

/- ## Question 2: Integers as Quotients

Recall the construction of integers from the lecture, not to be confused with
Lean's predefined type `Int` (= `ℤ`): -/

#check Int.Setoid
#check Int.Setoid_Iff
#check Int

/- 2.1. Define negation on these integers. Observe that if `(p, n)` represents
an integer, then `(n, p)` represents its negation. -/

def Int.neg: Int → Int :=
  Quotient.lift
  (fun p: Nat × Nat => ⟦(Prod.snd p, Prod.fst p)⟧)
  (by
    intro a b h
    simp
    apply Quotient.sound
    rw [Int.Setoid_Iff] at *
    simp
    linarith
  )

/- 2.2. Prove the following theorems about negation. -/

theorem Int.neg_eq (p n : ℕ) :
    Int.neg ⟦(p, n)⟧ = ⟦(n, p)⟧ :=
    by rfl

theorem int.neg_neg (a : Int) :
    Int.neg (Int.neg a) = a := by
  simp [Int.neg]
  induction a using Quotient.inductionOn
  cases a_1
  simp

end LoVe
