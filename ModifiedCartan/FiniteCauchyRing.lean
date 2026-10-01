import ModifiedCartan.FiniteCauchyDeterminant
import Mathlib.RingTheory.Localization.FractionRing

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

/-- Transfer the finite Cauchy determinant to actual inverses in a domain.
    Auxiliary to the formal-series proof for paper `lem:KP-correspondence`. -/
theorem finiteCauchy_inverse_det_mul_denominator {R : Type*} [CommRing R] [IsDomain R]
    {n : ℕ} (x y : Fin n → R) (K : Matrix (Fin n) (Fin n) R)
    (hK : ∀ i j, K i j * (1 - x i * y j) = 1) :
    K.det * finiteCauchyDenominator x y =
      finiteVandermondeProduct x * finiteVandermondeProduct y := by
  let φ : R →+* FractionRing R := algebraMap R (FractionRing R)
  have hn : ∀ i j, φ (1 - x i * y j) ≠ 0 := by
    intro i j hz
    have h := congrArg φ (hK i j)
    rw [map_mul, hz, mul_zero, map_one] at h
    exact zero_ne_one h
  have he : ∀ i j, φ (K i j) = (1 - φ (x i) * φ (y j))⁻¹ := by
    intro i j
    apply eq_inv_of_mul_eq_one_left
    simpa only [map_mul, map_sub, map_one] using congrArg φ (hK i j)
  apply IsFractionRing.injective R (FractionRing R)
  change φ (K.det * finiteCauchyDenominator x y) =
    φ (finiteVandermondeProduct x * finiteVandermondeProduct y)
  have hd := finiteCauchyMatrix_det_mul_denominator (φ ∘ x) (φ ∘ y)
    (fun i j => by simpa only [map_sub, map_one, map_mul, Function.comp_apply] using hn i j)
  have hm : φ.mapMatrix K = finiteCauchyMatrix (φ ∘ x) (φ ∘ y) := by
    ext i j
    exact he i j
  simpa only [map_mul, RingHom.map_det, hm, finiteCauchyDenominator,
    finiteVandermondeProduct, map_prod, map_sub, map_one, Function.comp_apply] using hd

theorem finiteCauchy_inverse_product {R : Type*} [CommRing R]
    {n : ℕ} (x y : Fin n → R) (K : Matrix (Fin n) (Fin n) R)
    (hK : ∀ i j, K i j * (1 - x i * y j) = 1) :
    finiteCauchyDenominator x y * (∏ i : Fin n, ∏ j : Fin n, K i j) = 1 := by
  unfold finiteCauchyDenominator
  rw [← Finset.prod_mul_distrib]
  calc
    _ = ∏ i : Fin n, ∏ j : Fin n, ((1 - x i * y j) * K i j) := by
      apply Finset.prod_congr rfl
      intro i _
      exact (Finset.prod_mul_distrib).symm
    _ = ∏ i : Fin n, ∏ j : Fin n, (1 : R) := by
      apply Finset.prod_congr rfl
      intro i _
      apply Finset.prod_congr rfl
      intro j _
      rw [mul_comm]
      exact hK i j
    _ = 1 := by simp

theorem finiteCauchy_inverse_det {R : Type*} [CommRing R] [IsDomain R]
    {n : ℕ} (x y : Fin n → R) (K : Matrix (Fin n) (Fin n) R)
    (hK : ∀ i j, K i j * (1 - x i * y j) = 1) :
    K.det = (finiteVandermondeProduct x * finiteVandermondeProduct y) *
      (∏ i : Fin n, ∏ j : Fin n, K i j) := by
  calc
    K.det = (K.det * finiteCauchyDenominator x y) *
        (∏ i : Fin n, ∏ j : Fin n, K i j) := by
      rw [mul_assoc, finiteCauchy_inverse_product x y K hK, mul_one]
    _ = _ := by rw [finiteCauchy_inverse_det_mul_denominator x y K hK]

end
end ModifiedCartan

#print axioms ModifiedCartan.finiteCauchy_inverse_det
