import ModifiedCartan.CompositionLaurentWeights
import ModifiedCartan.MarkerSquarefreeJacobian

open scoped BigOperators Classical LaurentPolynomial

namespace ModifiedCartan
noncomputable section

def compositionMarkerPolynomial {A B R : Type*} [Fintype A] [Fintype B] [CommRing R]
    (ℓ : A → ℕ) (x : B → R) : MvPolynomial A (LaurentPolynomial R) :=
  (1 + ∑ a : A, MvPolynomial.X a * MvPolynomial.C (compositionJacobianWeight (ℓ a))) *
    markerAffineProduct (fun b => compositionUnusedWeight (x b))
      (fun a b => compositionBoundaryWeight (ℓ a) (x b))

theorem compositionMarkerPolynomial_residue {A B R : Type*} [Fintype A] [Fintype B]
    [CommRing R] [IsDomain R] [CharZero R] (ℓ : A → ℕ) (x : B → R) (d : A →₀ ℕ) :
    (MvPolynomial.coeff d (compositionMarkerPolynomial ℓ x)).coeff (-1) = 0 := by
  have hz : (laurentMarkerEquiv A R (compositionMarkerPolynomial ℓ x)).coeff (-1) = 0 := by
    rw [compositionMarkerPolynomial, map_mul, map_add, map_one, map_sum]
    simp_rw [laurentMarkerEquiv_jacobian]
    rw [markerAffineProduct, map_prod]
    simp_rw [map_add, map_sum, laurentMarkerEquiv_unused]
    have hw (a : A) (b : B) :
        laurentMarkerEquiv A R (MvPolynomial.X a *
          MvPolynomial.C (compositionBoundaryWeight (ℓ a) (x b))) =
        LaurentPolynomial.C (MvPolynomial.X a) *
          (LaurentPolynomial.T (-(ℓ a : ℤ)) * LaurentPolynomial.C (MvPolynomial.C (x b)) -
            LaurentPolynomial.C ((MvPolynomial.C (x b)) ^ (ℓ a + 1))) := by
      rw [map_mul, laurentMarkerEquiv_X, laurentMarkerEquiv_boundary]
    simp_rw [hw]
    exact compositionMarkerResidue ℓ (fun a => MvPolynomial.X a) (fun b => MvPolynomial.C (x b))
  rw [← laurentMarkerEquiv_coeff, hz, MvPolynomial.coeff_zero]

/-- The squarefree coefficient of the formal change-of-variable identity.
This is the boundary-weight form of KP source Lemma 2.25. -/
theorem compositionBoundaryResidue {A B R : Type*} [Fintype A] [Fintype B]
    [CommRing R] [IsDomain R] [CharZero R] (s : Finset A) (ℓ : A → ℕ) (x : B → R) :
    ((∑ f : s ↪ B, markerEmbeddingWeight s (fun b => compositionUnusedWeight (x b))
        (fun a b => compositionBoundaryWeight (ℓ a) (x b)) f) +
      ∑ a ∈ s, compositionJacobianWeight (R := R) (ℓ a) *
        ∑ f : s.erase a ↪ B, markerEmbeddingWeight (s.erase a)
          (fun b => compositionUnusedWeight (x b))
          (fun i b => compositionBoundaryWeight (ℓ i) (x b)) f).coeff (-1) = 0 := by
  have h := compositionMarkerPolynomial_residue ℓ x (markerSquarefreeDegree s)
  rw [compositionMarkerPolynomial, markerAffineProduct_jacobian_coeff] at h
  exact h

end
end ModifiedCartan

