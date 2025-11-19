/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe06_InductivePredicates_Demo


/- # LoVe Homework 12 (10 points + 2 bonus points):
# Logical Foundations of Mathematics

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1 (8 points): Even Numbers as a Subtype

Usually, the most convenient way to represent even natural numbers is to use the
larger type `ℕ`, which also includes the odd natural numbers. If we want to
quantify only over even numbers `n`, we can add an assumption `Even n` to our
theorem statement.

An alternative is to encode evenness in the type, using a subtype. We will
explore this approach.

1.1 (1 point). Define the type `Eveℕ` of even natural numbers, using the `Even`
predicate introduced in the lecture 5 demo. -/

#print Even

def Eveℕ : Type :=
  {n : Nat // Even n}

/- 1.2 (1 point). Prove the following theorem about the `Even` predicate. You will
need it to answer question 1.3.

Hint: The theorems `add_assoc` and `add_comm` might be useful. -/

theorem Even.add {m n : ℕ} (hm : Even m) (hn : Even n) :
    Even (m + n) := by
    induction hm
    simp [hn]
    have h := Even.add_two (k + n) a_ih
    have hh: k + n + 2 = k + 2 + n := by ac_rfl
    aesop

/- 1.3 (2 points). Define zero and addition of even numbers by filling in the
`sorry` placeholders. -/

def Eveℕ.zero : Eveℕ :=
  Subtype.mk 0 (Even.zero)

def Eveℕ.add (m n : Eveℕ) : Eveℕ :=
  Subtype.mk (Subtype.val m + Subtype.val n) (Even.add (m.property) (n.property))

/- 1.4 (4 points). Prove that addition of even numbers is commutative and
associative, and has 0 as an identity element. -/

theorem Eveℕ.add_comm (m n : Eveℕ) :
    Eveℕ.add m n = Eveℕ.add n m := by
    rcases m with ⟨m, hm⟩
    rcases n with ⟨n, hn⟩
    have h := Nat.add_comm m n
    simp [add, h]


theorem Eveℕ.add_assoc (l m n : Eveℕ) :
    Eveℕ.add (Eveℕ.add l m) n = Eveℕ.add l (Eveℕ.add m n) := by
    rcases l with ⟨l, hl⟩
    rcases m with ⟨m, hm⟩
    rcases n with ⟨n, hn⟩
    have h := Nat.add_assoc l m n
    simp [add, h]

theorem Eveℕ.add_iden_left (n : Eveℕ) :
    Eveℕ.add Eveℕ.zero n = n :=
    by simp [add, zero]

theorem Eveℕ.add_iden_right (n : Eveℕ) :
    Eveℕ.add n Eveℕ.zero = n :=
    by simp [add, zero]


/- ## Question 2 (2 points + 2 bonus points): Hilbert Choice

2.1 (2 bonus points). Prove the following theorem.

Hints:

* A good way to start is to make a case distinction on whether `∃n, f n < x`
  is true or false.

* The theorem `le_of_not_gt` might be useful. -/

#check le_of_not_gt

theorem exists_minimal_arg_helper (f : ℕ → ℕ) :
    ∀x m, f m = x → ∃n, ∀i, f n ≤ f i
  | x, m, eq =>
    by
      cases (Classical.em (∃n, f n < x))
      {
        cases h
        have h := exists_minimal_arg_helper f (f w) w (by rfl)
        exact h
      }
      {
        apply Exists.intro m
        intro i
        simp at h
        specialize h i
        aesop
      }


/- Now this interesting theorem falls off: -/

theorem exists_minimal_arg (f : ℕ → ℕ) :
    ∃n : ℕ, ∀i : ℕ, f n ≤ f i :=
  exists_minimal_arg_helper f _ 0 (by rfl)

/- 2.2 (1 point). Use what you learned about Hilbert choice in the lecture to
define the following function, which returns the (or an) index of the minimal
element in `f`'s image. -/

noncomputable def minimal_arg (f : ℕ → ℕ) : ℕ :=
  Classical.choose (exists_minimal_arg f)

/- 2.3 (1 point). Prove the following characteristic theorem about your
definition. -/

theorem minimal_arg_spec (f : ℕ → ℕ) :
    ∀i : ℕ, f (minimal_arg f) ≤ f i := by
    simp [minimal_arg]
    apply Classical.choose_spec (exists_minimal_arg f)

end LoVe
