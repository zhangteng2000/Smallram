import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

/-- A finite matrix triangular by a natural weight, orthogonal without
    conjugation, and with nonnegative integral diagonal is the identity.
    Auxiliary to the Schur identification for paper `lem:KP-correspondence`. -/
theorem weighted_triangular_orthogonal_identity {I : Type*} [Fintype I] [DecidableEq I]
    (w : I → ℕ) (A : I → I → ℂ)
    (ht : ∀ i j, w i ≤ w j → i ≠ j → A i j = 0)
    (ho : ∀ i j, (∑ k : I, A i k * A j k) = if i = j then 1 else 0)
    (hd : ∀ i, ∃ k : ℕ, A i i = (k : ℂ)) :
    ∀ i j, A i j = if i = j then 1 else 0 := by
  have hall : ∀ n : ℕ, ∀ i : I, w i = n → ∀ j, A i j = if i = j then 1 else 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i hi
      have hoff : ∀ j, j ≠ i → A i j = 0 := by
        intro j hji
        by_cases hw : w j < n
        · have hj := ih (w j) hw j rfl
          have h := ho i j
          simpa [hj, Ne.symm hji] using h
        · exact ht i j (by omega) (Ne.symm hji)
      have hsum : (∑ k : I, A i k * A i k) = A i i * A i i := by
        apply Finset.sum_eq_single i
        · intro k _ hki
          rw [hoff k hki, zero_mul]
        · simp
      have hs := ho i i
      rw [hsum, ite_eq_left rfl] at hs
      obtain ⟨k, hk⟩ := hd i
      rw [hk] at hs
      have hnat : k * k = 1 := by exact_mod_cast hs
      have hk1 : k = 1 := by nlinarith
      have hii : A i i = 1 := by simpa only [hk1, Nat.cast_one] using hk
      intro j
      by_cases hji : j = i
      · subst j
        simp [hii]
      · simp [hoff j hji, Ne.symm hji]
  intro i j
  exact hall (w i) i rfl j

end
end ModifiedCartan

#print axioms ModifiedCartan.weighted_triangular_orthogonal_identity
