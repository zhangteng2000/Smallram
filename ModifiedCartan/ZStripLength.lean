import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.Finset.Basic

open scoped Classical

namespace ModifiedCartan
noncomputable section

theorem zStripReturn_exists {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z : Finset A)
    (a : Z) : ∃ n : ℕ, 0 < n ∧ (θ ^ n) a.val ∈ Z := by
  refine ⟨orderOf θ, orderOf_pos θ, ?_⟩
  rw [pow_orderOf_eq_one]
  exact a.property

/-- First positive return to Z. The actual strip consists of the powers
0 through zStripLength-1, so fixed points in Z give strips of length one. -/
def zStripLength {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z : Finset A) (a : Z) : ℕ :=
  Nat.find (zStripReturn_exists θ Z a)

theorem zStripLength_pos {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z : Finset A) (a : Z) :
    0 < zStripLength θ Z a := (Nat.find_spec (zStripReturn_exists θ Z a)).1

theorem zStripLength_return {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z : Finset A) (a : Z) :
    (θ ^ zStripLength θ Z a) a.val ∈ Z := (Nat.find_spec (zStripReturn_exists θ Z a)).2

theorem zStripLength_minimal {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z : Finset A)
    (a : Z) (n : ℕ) (hn : 0 < n) (hlt : n < zStripLength θ Z a) :
    (θ ^ n) a.val ∉ Z := by
  intro hm
  have hle := Nat.find_min' (zStripReturn_exists θ Z a) ⟨hn, hm⟩
  exact (Nat.not_lt_of_ge hle) hlt

theorem zStripLength_le_orderOf {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z : Finset A) (a : Z) :
    zStripLength θ Z a ≤ orderOf θ := by
  apply Nat.find_min'
  refine ⟨orderOf_pos θ, ?_⟩
  rw [pow_orderOf_eq_one]
  exact a.property

end
end ModifiedCartan

