import ModifiedCartan.TranslatedDifferentialKernel
import Mathlib.Algebra.Polynomial.Module.Basic

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

def polynomialLinearCoefficientMap {R S : Type*} [CommRing R] [CommRing S]
    [Algebra ℂ R] [Algebra ℂ S] (L : R →ₗ[ℂ] S) : Polynomial R →ₗ[ℂ] Polynomial S :=
  (PolynomialModule.equivPolynomial (R := ℂ) (S := S)).toLinearMap.comp
    ((PolynomialModule.map ℂ L).comp
      (PolynomialModule.equivPolynomial (R := ℂ) (S := R)).symm.toLinearMap)

theorem polynomialLinearCoefficientMap_coeff {R S : Type*} [CommRing R] [CommRing S]
    [Algebra ℂ R] [Algebra ℂ S] (L : R →ₗ[ℂ] S) (p : Polynomial R) (k : ℕ) :
    (polynomialLinearCoefficientMap L p).coeff k = L (p.coeff k) := by
  rfl

theorem polynomialLinearCoefficientMap_derivative {R S : Type*} [CommRing R] [CommRing S]
    [Algebra ℂ R] [Algebra ℂ S] (L : R →ₗ[ℂ] S) (p : Polynomial R) :
    polynomialLinearCoefficientMap L p.derivative = (polynomialLinearCoefficientMap L p).derivative := by
  ext k
  simp only [polynomialLinearCoefficientMap_coeff, Polynomial.coeff_derivative]
  simpa only [nsmul_eq_mul, mul_comm, Nat.cast_add, Nat.cast_one] using
    map_nsmul L (k + 1) (p.coeff (k + 1))

theorem polynomialLinearCoefficientMap_iterate_derivative {R S : Type*} [CommRing R] [CommRing S]
    [Algebra ℂ R] [Algebra ℂ S] (L : R →ₗ[ℂ] S) (p : Polynomial R) (k : ℕ) :
    polynomialLinearCoefficientMap L (Polynomial.derivative^[k] p) =
      Polynomial.derivative^[k] (polynomialLinearCoefficientMap L p) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [Function.iterate_succ_apply', polynomialLinearCoefficientMap_derivative, ih]

theorem polynomialLinearCoefficientMap_scalar_mul {B : Type*}
    (L : MvPolynomial B ℂ →ₗ[ℂ] ℂ) (a : Polynomial ℂ) (p : Polynomial (MvPolynomial B ℂ)) :
    polynomialLinearCoefficientMap L (a.map MvPolynomial.C * p) =
      a * polynomialLinearCoefficientMap L p := by
  ext k
  simp only [polynomialLinearCoefficientMap_coeff, Polynomial.coeff_mul,
    Polynomial.coeff_map, map_sum]
  apply Finset.sum_congr rfl
  intro ij _
  rw [← MvPolynomial.smul_eq_C_mul]
  exact L.map_smul _ _

theorem polynomialFirstDifferential_linearCoefficientMap {m : ℕ} (N : ℕ)
    (c : ℕ → Polynomial ℂ) (L : MvPolynomial (Fin m) ℂ →ₗ[ℂ] ℂ)
    (p : Polynomial (MvPolynomial (Fin m) ℂ)) :
    polynomialLinearCoefficientMap L (polynomialFirstDifferential N c p) =
      ∑ k ∈ Finset.range (N + 1), c k *
        Polynomial.derivative^[N - k] (polynomialLinearCoefficientMap L p) := by
  simp only [polynomialFirstDifferential, map_sum, polynomialLinearCoefficientMap_scalar_mul,
    polynomialLinearCoefficientMap_iterate_derivative]

end
end ModifiedCartan

#print axioms ModifiedCartan.polynomialFirstDifferential_linearCoefficientMap
