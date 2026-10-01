import ModifiedCartan.NormalizedCompositionBoundary
import ModifiedCartan.CompositionBoundaryResidue

open scoped BigOperators Classical LaurentPolynomial

namespace ModifiedCartan
noncomputable section

theorem normalizedCompositionSum_residue {A B R : Type*} [Fintype A] [Fintype B]
    [CommRing R] [IsDomain R] [CharZero R] (s : Finset A) (ℓ : A → ℕ) (x : B → R) :
    ((∏ b : B, compositionUnusedWeight (x b)) *
      (normalizedCompositionSum s ℓ x + ∑ a ∈ s,
        compositionJacobianWeight (R := R) (ℓ a) * normalizedCompositionSum (s.erase a) ℓ x)).coeff (-1) = 0 := by
  have h := compositionBoundaryResidue s ℓ x
  simp_rw [← normalizedCompositionSum_boundary] at h
  rw [mul_add, Finset.mul_sum]
  have he (a : A) : (∏ b : B, compositionUnusedWeight (x b)) *
      (compositionJacobianWeight (R := R) (ℓ a) * normalizedCompositionSum (s.erase a) ℓ x) =
      compositionJacobianWeight (R := R) (ℓ a) *
        ((∏ b : B, compositionUnusedWeight (x b)) * normalizedCompositionSum (s.erase a) ℓ x) :=
    mul_left_comm _ _ _
  simp_rw [he]
  exact h

end
end ModifiedCartan

