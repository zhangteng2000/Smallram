import ModifiedCartan.NormalizedGeometricLaurent
import ModifiedCartan.MarkerEmbeddingCoefficients

open scoped BigOperators Classical LaurentPolynomial

namespace ModifiedCartan
noncomputable section

def normalizedCompositionSum {A B R : Type*} [Fintype B] [CommRing R]
    (s : Finset A) (ℓ : A → ℕ) (x : B → R) : LaurentPolynomial R :=
  ∑ f : s ↪ B, ∏ a : s, normalizedGeometricColor (ℓ a.val) (x (f a))

theorem normalizedCompositionSum_boundary {A B R : Type*} [Fintype B] [CommRing R]
    (s : Finset A) (ℓ : A → ℕ) (x : B → R) :
    (∏ b : B, compositionUnusedWeight (x b)) * normalizedCompositionSum s ℓ x =
      ∑ f : s ↪ B, markerEmbeddingWeight s (fun b => compositionUnusedWeight (x b))
        (fun a b => compositionBoundaryWeight (ℓ a) (x b)) f := by
  rw [normalizedCompositionSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f hf
  rw [product_split_embedding f (fun b => compositionUnusedWeight (x b)), mul_right_comm,
    ← Finset.prod_mul_distrib]
  simp only [normalizedGeometricColor_boundary, markerEmbeddingWeight]

end
end ModifiedCartan

