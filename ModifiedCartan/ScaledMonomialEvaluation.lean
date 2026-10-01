import ModifiedCartan.ScaledMonomialPowerSums
import ModifiedCartan.InjectiveColorSums

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem scaledMonomialPolynomial_embeddings {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] (κ : A → ℕ) :
    scaledMonomialPolynomial B κ = ∑ f : A ↪ B, ∏ a : A, MvPolynomial.X (f a) ^ κ a := by
  rw [scaledMonomialPolynomial]
  exact sum_injective_eq_sum_embeddings (fun f : A → B =>
    ∏ a : A, (MvPolynomial.X (f a) : MvPolynomial B ℂ) ^ κ a)

theorem scaledMonomialPolynomial_map {A B R : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [CommSemiring R] (κ : A → ℕ) (φ : MvPolynomial B ℂ →+* R) :
    φ (scaledMonomialPolynomial B κ) = ∑ f : A ↪ B, ∏ a : A, φ (MvPolynomial.X (f a)) ^ κ a := by
  rw [scaledMonomialPolynomial_embeddings, map_sum]
  simp only [map_prod, map_pow]

end
end ModifiedCartan

