import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Data.Complex.Basic

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

def mvPolynomialCoefficientScale (B : Type*) (a : (B →₀ ℕ) → ℂ) :
    MvPolynomial B ℂ →ₗ[ℂ] MvPolynomial B ℂ :=
  (MvPolynomial.basisMonomials B ℂ).constr ℂ (fun d => MvPolynomial.monomial d (a d))

theorem mvPolynomialCoefficientScale_monomial_one {B : Type*} (a : (B →₀ ℕ) → ℂ)
    (d : B →₀ ℕ) :
    mvPolynomialCoefficientScale B a (MvPolynomial.monomial d 1) = MvPolynomial.monomial d (a d) := by
  exact (MvPolynomial.basisMonomials B ℂ).constr_basis ℂ (fun d => MvPolynomial.monomial d (a d)) d

theorem mvPolynomialCoefficientScale_coeff {B : Type*} (a : (B →₀ ℕ) → ℂ)
    (P : MvPolynomial B ℂ) (d : B →₀ ℕ) :
    MvPolynomial.coeff d (mvPolynomialCoefficientScale B a P) = a d * MvPolynomial.coeff d P := by
  have h : (MvPolynomial.lcoeff ℂ d).comp (mvPolynomialCoefficientScale B a) =
      a d • MvPolynomial.lcoeff ℂ d := by
    apply (MvPolynomial.basisMonomials B ℂ).ext
    intro e
    change MvPolynomial.coeff d (mvPolynomialCoefficientScale B a (MvPolynomial.monomial e 1)) =
      a d * MvPolynomial.coeff d (MvPolynomial.monomial e 1)
    rw [mvPolynomialCoefficientScale_monomial_one]
    by_cases he : e = d <;> simp [he]
  exact congrArg (fun f : MvPolynomial B ℂ →ₗ[ℂ] ℂ => f P) h

theorem mvPolynomialCoefficientScale_monomial {B : Type*} (a : (B →₀ ℕ) → ℂ)
    (d : B →₀ ℕ) (c : ℂ) :
    mvPolynomialCoefficientScale B a (MvPolynomial.monomial d c) = MvPolynomial.monomial d (a d * c) := by
  ext e
  rw [mvPolynomialCoefficientScale_coeff]
  by_cases he : d = e <;> simp [he]

theorem mvPolynomialCoefficientScale_C_mul {B : Type*} (a : (B →₀ ℕ) → ℂ)
    (c : ℂ) (P : MvPolynomial B ℂ) :
    mvPolynomialCoefficientScale B a (MvPolynomial.C c * P) =
      MvPolynomial.C c * mvPolynomialCoefficientScale B a P := by
  ext d
  simp only [mvPolynomialCoefficientScale_coeff, MvPolynomial.coeff_C_mul]
  ring

/-- A nonvanishing diagonal coefficient change loses no polynomial information.
    Auxiliary to the divided-power normalization for `lem:KP-correspondence`. -/
theorem mvPolynomialCoefficientScale_ne_zero {B : Type*} (a : (B →₀ ℕ) → ℂ)
    (ha : ∀ d, a d ≠ 0) (P : MvPolynomial B ℂ) (hP : P ≠ 0) :
    mvPolynomialCoefficientScale B a P ≠ 0 := by
  intro hzero
  apply hP
  ext d
  have hc := congrArg (MvPolynomial.coeff d) hzero
  rw [mvPolynomialCoefficientScale_coeff, MvPolynomial.coeff_zero] at hc
  exact (mul_eq_zero.mp hc).resolve_left (ha d)

end
end ModifiedCartan
