import ModifiedCartan.MvPolynomialCoefficientScale
import Mathlib.Algebra.MvPolynomial.Equiv

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

def multiDegreeInverseFactorial {B : Type*} [Fintype B] (d : B →₀ ℕ) : ℂ :=
  ∏ b : B, ((d b).factorial : ℂ)⁻¹

theorem multiDegreeInverseFactorial_ne_zero {B : Type*} [Fintype B] (d : B →₀ ℕ) :
    multiDegreeInverseFactorial d ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro b hb
  exact inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero (d b))

def mvDividedPowerNormalize (B : Type*) [Fintype B] :
    MvPolynomial B ℂ →ₗ[ℂ] MvPolynomial B ℂ :=
  mvPolynomialCoefficientScale B multiDegreeInverseFactorial

theorem mvDividedPowerNormalize_coeff {B : Type*} [Fintype B]
    (P : MvPolynomial B ℂ) (d : B →₀ ℕ) :
    MvPolynomial.coeff d (mvDividedPowerNormalize B P) =
      multiDegreeInverseFactorial d * MvPolynomial.coeff d P :=
  mvPolynomialCoefficientScale_coeff _ P d

theorem mvDividedPowerNormalize_C_mul {B : Type*} [Fintype B]
    (c : ℂ) (P : MvPolynomial B ℂ) :
    mvDividedPowerNormalize B (MvPolynomial.C c * P) =
      MvPolynomial.C c * mvDividedPowerNormalize B P :=
  mvPolynomialCoefficientScale_C_mul _ c P

theorem mvDividedPowerNormalize_ne_zero {B : Type*} [Fintype B]
    (P : MvPolynomial B ℂ) (hP : P ≠ 0) : mvDividedPowerNormalize B P ≠ 0 :=
  mvPolynomialCoefficientScale_ne_zero _ multiDegreeInverseFactorial_ne_zero P hP

/-- Passing to divided powers commutes with extraction of one variable's
    coefficient, with precisely its factorial factor. Auxiliary to the
    differential contraction for manuscript `lem:KP-correspondence`. -/
theorem mvDividedPowerNormalize_first_coeff {m : ℕ}
    (P : MvPolynomial (Fin (m + 1)) ℂ) (j : ℕ) :
    mvDividedPowerNormalize (Fin m) ((MvPolynomial.finSuccEquiv ℂ m P).coeff j) =
      MvPolynomial.C (j.factorial : ℂ) *
        (MvPolynomial.finSuccEquiv ℂ m (mvDividedPowerNormalize (Fin (m + 1)) P)).coeff j := by
  ext d
  simp only [mvDividedPowerNormalize_coeff, MvPolynomial.coeff_C_mul,
    MvPolynomial.finSuccEquiv_coeff_coeff, multiDegreeInverseFactorial,
    Fin.prod_univ_succ, Finsupp.cons_zero, Finsupp.cons_succ]
  have hj : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  simp [← mul_assoc, hj]

end
end ModifiedCartan

#print axioms ModifiedCartan.mvDividedPowerNormalize_first_coeff
