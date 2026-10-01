import ModifiedCartan.PolynomialLinearCoefficients
import ModifiedCartan.PolynomialODEKernelBound
import Mathlib.RingTheory.Polynomial.Basic

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

def polynomialCoefficientContraction {B : Type*} (p : Polynomial (MvPolynomial B ℂ)) :
    Module.Dual ℂ (MvPolynomial B ℂ) →ₗ[ℂ] Polynomial ℂ where
  toFun L := polynomialLinearCoefficientMap L p
  map_add' L M := by
    ext k
    simp only [polynomialLinearCoefficientMap_coeff, Polynomial.coeff_add, LinearMap.add_apply]
  map_smul' c L := by
    ext k
    simp only [polynomialLinearCoefficientMap_coeff, Polynomial.coeff_smul,
      LinearMap.smul_apply, RingHom.id_apply]

/-- All scalar coefficient contractions of a polynomial with polynomial
    coefficients. Auxiliary to the space reconstructed in `lem:KP-correspondence`. -/
def polynomialCoefficientSpace {B : Type*} (p : Polynomial (MvPolynomial B ℂ)) :
    Submodule ℂ (Polynomial ℂ) := LinearMap.range (polynomialCoefficientContraction p)

theorem polynomialCoefficientSpace_le_degreeLT {B : Type*}
    (p : Polynomial (MvPolynomial B ℂ)) :
    polynomialCoefficientSpace p ≤ Polynomial.degreeLT ℂ (p.natDegree + 1) := by
  rintro q ⟨L, rfl⟩
  apply Polynomial.mem_degreeLT.mpr
  apply (Polynomial.degree_lt_iff_coeff_zero _ _).mpr
  intro k hk
  change (polynomialLinearCoefficientMap L p).coeff k = 0
  rw [polynomialLinearCoefficientMap_coeff,
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero]

instance polynomialCoefficientSpace_finiteDimensional {B : Type*}
    (p : Polynomial (MvPolynomial B ℂ)) : FiniteDimensional ℂ (polynomialCoefficientSpace p) :=
  Module.Finite.of_injective
    ((Polynomial.degreeLTEquiv ℂ (p.natDegree + 1)).toLinearMap.comp
      (Submodule.inclusion (polynomialCoefficientSpace_le_degreeLT p)))
    ((Polynomial.degreeLTEquiv ℂ (p.natDegree + 1)).injective.comp
      (Submodule.inclusion_injective _))

theorem polynomialDifferentialApply_reversed (N : ℕ) (c : ℕ → Polynomial ℂ) (p : Polynomial ℂ) :
    polynomialDifferentialApply (fun i : Fin (N + 1) => c i.rev.val) p =
      ∑ k ∈ Finset.range (N + 1), c k * Polynomial.derivative^[N - k] p := by
  unfold polynomialDifferentialApply
  have h := Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (N + 1)))
    (fun i : Fin (N + 1) => c i.val * Polynomial.derivative^[N - i.val] p)
  have he (i : Fin (N + 1)) : N - i.rev.val = i.val := by
    simp only [Fin.val_rev]
    have := i.isLt
    omega
  change (∑ i : Fin (N + 1), c i.rev.val * Polynomial.derivative^[N - i.rev.val] p) =
    ∑ i : Fin (N + 1), c i.val * Polynomial.derivative^[N - i.val] p at h
  simp only [he] at h
  erw [Fin.sum_univ_eq_sum_range (fun k => c k * Polynomial.derivative^[N - k] p) (N + 1)] at h
  exact h

/-- The scalar coefficient space lies in the ordinary polynomial kernel,
    so its dimension is bounded by the actual order of the operator.
    Auxiliary to `lem:KP-correspondence`. -/
theorem polynomialCoefficientSpace_finrank_le {m : ℕ} (N : ℕ) (c : ℕ → Polynomial ℂ)
    (hc : c 0 ≠ 0) (p : Polynomial (MvPolynomial (Fin m) ℂ))
    (hp : polynomialFirstDifferential N c p = 0) :
    Module.finrank ℂ (polynomialCoefficientSpace p) ≤ N := by
  apply polynomialDifferential_subspace_finrank_le
    (fun i : Fin (N + 1) => c i.rev.val)
  · simpa only [Fin.rev_last, Fin.val_zero] using hc
  · rintro q ⟨L, rfl⟩
    rw [polynomialDifferentialApply_reversed]
    change (∑ k ∈ Finset.range (N + 1), c k * Polynomial.derivative^[N - k]
      (polynomialLinearCoefficientMap L p)) = 0
    rw [← polynomialFirstDifferential_linearCoefficientMap, hp, map_zero]

end
end ModifiedCartan

#print axioms ModifiedCartan.polynomialCoefficientSpace_finrank_le
