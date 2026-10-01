import ModifiedCartan.SeriesHomogenization
import ModifiedCartan.FiniteGeometricSeries

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

attribute [local instance 2000] MvPowerSeries.instAlgebra

theorem seriesHomogenization_monomial {B R : Type*} [Fintype B] [CommSemiring R]
    (d : B →₀ ℕ) (a : R) :
    seriesHomogenization B R (MvPowerSeries.monomial d a) =
      PowerSeries.monomial d.degree (MvPolynomial.monomial d a) := by
  apply PowerSeries.ext
  intro n
  apply MvPolynomial.ext
  intro e
  rw [seriesHomogenization_coeff_coeff]
  by_cases he : e = d <;> by_cases hn : n = d.degree <;>
    simp [he, hn, MvPowerSeries.coeff_monomial, PowerSeries.coeff_monomial,
      MvPolynomial.coeff_monomial, eq_comm] <;> aesop

theorem seriesHomogenization_C {B R : Type*} [Fintype B] [CommSemiring R] (a : R) :
    seriesHomogenization B R (MvPowerSeries.C a) = PowerSeries.C (MvPolynomial.C a) := by
  have h := seriesHomogenization_monomial (B := B) (0 : B →₀ ℕ) a
  simpa [PowerSeries.monomial, PowerSeries.C] using h

theorem seriesHomogenization_X {B R : Type*} [Fintype B] [CommSemiring R] (j : B) :
    seriesHomogenization B R (MvPowerSeries.X j) =
      PowerSeries.C (MvPolynomial.X j) * PowerSeries.X := by
  have h := seriesHomogenization_monomial (Finsupp.single j 1) (1 : R)
  change seriesHomogenization B R (MvPowerSeries.X j) =
    PowerSeries.monomial (Finsupp.single j 1).degree (MvPolynomial.X j) at h
  rw [Finsupp.degree_single] at h
  rw [h]
  apply PowerSeries.ext
  intro n
  by_cases hn : n = 1 <;>
    simp [hn, PowerSeries.coeff_monomial, PowerSeries.coeff_C_mul, PowerSeries.coeff_X]

/-- Homogenization sends the actual geometric series to the geometric series
    with its polynomial variable attached. Auxiliary to `lem:KP-correspondence`. -/
theorem seriesHomogenization_geometricMvSeries {B R : Type*} [Fintype B] [CommRing R]
    (j : B) (a : R) :
    seriesHomogenization B R (geometricMvSeries j a) =
      geometricPowerSeries (MvPolynomial.C a * MvPolynomial.X j) := by
  have h := congrArg (seriesHomogenization B R) (geometricMvSeries_inverse j a)
  rw [map_mul, map_sub, map_one, map_mul, seriesHomogenization_C,
    seriesHomogenization_X, ← mul_assoc, ← map_mul] at h
  have hg := geometricPowerSeries_inverse (MvPolynomial.C a * MvPolynomial.X j)
  calc
    _ = seriesHomogenization B R (geometricMvSeries j a) *
        ((1 - PowerSeries.C (MvPolynomial.C a * MvPolynomial.X j) * PowerSeries.X) *
          geometricPowerSeries (MvPolynomial.C a * MvPolynomial.X j)) := by
      rw [mul_comm (1 - _), hg, mul_one]
    _ = _ := by rw [← mul_assoc, h, one_mul]

end
end ModifiedCartan

#print axioms ModifiedCartan.seriesHomogenization_geometricMvSeries
