import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

/-- A homogeneous polynomial factor only sees one total degree of a series.
    Auxiliary coefficient extraction for paper `lem:KP-correspondence`. -/
theorem homogeneous_polynomial_mul_series_coeff {B R : Type*} [CommSemiring R]
    (P Q : MvPolynomial B R) (F : MvPowerSeries B R) (n k : ℕ)
    (hP : P.IsHomogeneous k)
    (hF : ∀ e : B →₀ ℕ, e.degree = n → MvPowerSeries.coeff e F = MvPolynomial.coeff e Q)
    (d : B →₀ ℕ) (hd : d.degree = k + n) :
    MvPowerSeries.coeff d ((P : MvPowerSeries B R) * F) = MvPolynomial.coeff d (P * Q) := by
  rw [MvPowerSeries.coeff_mul, MvPolynomial.coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [MvPolynomial.coeff_coe]
  by_cases hzero : MvPolynomial.coeff p.1 P = 0
  · simp [hzero]
  · have hk : p.1.degree = k := by
      by_contra hne
      exact hzero (hP.coeff_eq_zero hne)
    have he : p.2.degree = n := by
      have hsum := congrArg Finsupp.degree (Finset.mem_antidiagonal.mp hp)
      rw [map_add, hk, hd] at hsum
      exact Nat.add_left_cancel hsum
    rw [hF p.2 he]

end
end ModifiedCartan

#print axioms ModifiedCartan.homogeneous_polynomial_mul_series_coeff
