import ModifiedCartan.ArbitraryRadiusData
import ModifiedCartan.MeasureLimitTransfer

open scoped Topology BigOperators
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- Coefficients of the actual limiting monic equation, with the vanished
first canonical coefficient in the final index. -/
noncomputable def ArbitraryRadiusLimitData.fullCoefficient {n : ℕ} {f : Curve n}
    {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ) : Index n → ℂ → ℂ :=
  Fin.lastCases (fun _ => 0) d.coefficient

theorem ArbitraryRadiusLimitData.fullCoefficient_last {n : ℕ} {f : Curve n}
    {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ) :
    d.fullCoefficient (Fin.last n) = fun _ => 0 := Fin.lastCases_last

theorem ArbitraryRadiusLimitData.fullCoefficient_castSucc {n : ℕ} {f : Curve n}
    {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ) (i : Fin n) :
    d.fullCoefficient i.castSucc = d.coefficient i := Fin.lastCases_castSucc i

theorem ArbitraryRadiusLimitData.fullCoefficient_analytic {n : ℕ} {f : Curve n}
    {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ) (i : Index n) :
    AnalyticOnNhd ℂ (d.fullCoefficient i) univ := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [d.fullCoefficient_last]
    exact analyticOnNhd_const
  · rw [d.fullCoefficient_castSucc]
    exact d.coefficient_analytic j

/-- Actual polynomial coefficients converge to the coefficients used in
`eq:gradient-equation`; both terms of the replacement comparison are used. -/
theorem ArbitraryRadiusLimitData.polynomial_coefficient_limit {n : ℕ} {f : Curve n}
    {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ) (i : Index n) :
    LocalMeasureConvergence (ball (0 : ℂ) 4)
      (fun ν z => FewInflection.fundamentalCoefficients n
        (fun j w => (d.polynomial ν j).eval w) z i /
          (characteristic f (r (d.subseq ν)) : ℂ) ^ (n + 1 - i.val)) (d.fullCoefficient i) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [d.fullCoefficient_last, Fin.val_last, Nat.add_sub_cancel_left, pow_one] using
      d.replacement.first_coefficient
  · rw [d.fullCoefficient_castSucc]
    simpa only [sub_add_cancel, zero_add, Fin.val_castSucc] using
      (d.replacement.scaled_coefficients j).add ((d.coefficient_limit j).mono (subset_univ _))

end ModifiedCartan
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.polynomial_coefficient_limit
