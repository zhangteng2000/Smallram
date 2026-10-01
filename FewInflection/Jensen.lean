import FewInflection.Definitions
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Meromorphic.Divisor

open Filter MeromorphicAt MeromorphicOn MeasureTheory Metric Real Set Topology
open scoped BigOperators ComplexConjugate

namespace FewInflection

noncomputable section

/-- Jensen's formula gives the nonnegative scalar characteristic increment for
an entire function that is nonzero at the centre.  This is the scalar
ingredient used when estimating the vector characteristic. -/
theorem scalar_circleAverage_log_norm_sub_nonneg
    {g : ℂ → ℂ} (hg : Differentiable ℂ g) {r : ℝ} (hr : 0 < r)
    (hg0 : g 0 ≠ 0) :
    0 ≤ Real.circleAverage (fun z : ℂ => Real.log ‖g z‖) 0 r -
      Real.log ‖g 0‖ := by
  have hA : AnalyticOnNhd ℂ g (closedBall (0 : ℂ) |r|) := by
    exact (Complex.analyticOnNhd_univ_iff_differentiable.mpr hg).mono
      (subset_univ _)
  have hj := hA.circleAverage_log_norm hr.ne' hg0
  rw [hj]
  have hsum :
      0 ≤ ∑ᶠ u : ℂ,
        (MeromorphicOn.divisor g (closedBall (0 : ℂ) |r|) u : ℝ) *
          Real.log (r * ‖(0 : ℂ) - u‖⁻¹) := by
    apply finsum_nonneg
    intro u
    by_cases hu : u ∈ closedBall (0 : ℂ) |r|
    · by_cases hu0 : u = 0
      · subst u
        have hdiv0 : MeromorphicOn.divisor g (closedBall (0 : ℂ) |r|) 0 = 0 := by
          rw [hA.divisor_apply (by simp)]
          simp [(hA 0 (by simp)).analyticOrderAt_eq_zero.mpr hg0]
        rw [hdiv0]
        simp
      · have hdiv :
            0 ≤ (MeromorphicOn.divisor g (closedBall (0 : ℂ) |r|) u : ℝ) := by
          exact_mod_cast hA.divisor_nonneg u
        have hnorm : ‖u‖ ≤ r := by
          have hd := Metric.mem_closedBall.mp hu
          simpa [dist_zero_right, abs_of_pos hr] using hd
        have hnormpos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
        have harg : 1 ≤ r * ‖(0 : ℂ) - u‖⁻¹ := by
          have harg' : 1 ≤ r / ‖u‖ :=
            (le_div_iff₀ hnormpos).2 (by simpa using hnorm)
          simpa [norm_sub_rev, norm_neg, div_eq_mul_inv] using harg'
        exact mul_nonneg hdiv (Real.log_nonneg harg)
    · simp [hu]
  linarith

/- The same Jensen increment with an arbitrary centre, obtained by translating
   the entire function. -/
theorem scalar_circleAverage_log_norm_sub_nonneg_at
    {g : ℂ → ℂ} (hg : Differentiable ℂ g) {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hgc : g c ≠ 0) :
    0 ≤ Real.circleAverage (fun z : ℂ => Real.log ‖g z‖) c r -
      Real.log ‖g c‖ := by
  have hcomp : Differentiable ℂ (fun z : ℂ => g (z + c)) := by
    fun_prop
  have hzero := scalar_circleAverage_log_norm_sub_nonneg hcomp hr (by
    simpa using hgc)
  rw [← Real.circleAverage_map_add_const]
  simpa using hzero

/- For an entire function nonzero at the centre, the zero-counting part of
the value-distribution characteristic is exactly the Jensen increment. -/
theorem logCounting_zero_eq_circleAverage_sub_const_of_entire
    {g : ℂ → ℂ} (hg : Differentiable ℂ g) {r : ℝ} (hr : 0 < r)
    (hg0 : g 0 ≠ 0) :
    ValueDistribution.logCounting g (0 : WithTop ℂ) r =
      Real.circleAverage (fun z : ℂ => Real.log ‖g z‖) 0 r -
        Real.log ‖g 0‖ := by
  have hA : AnalyticOnNhd ℂ g Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr hg
  have hdiv : 0 ≤ MeromorphicOn.divisor g Set.univ := hA.divisor_nonneg
  have hneg : (MeromorphicOn.divisor g Set.univ)⁻ = 0 :=
    negPart_eq_zero.mpr hdiv
  have htop : ValueDistribution.logCounting g (⊤ : WithTop ℂ) r = 0 := by
    rw [ValueDistribution.logCounting_top, hneg]
    simp
  have hJ :=
    ValueDistribution.logCounting_zero_sub_logCounting_top_eq_circleAverage_sub_const
      (meromorphicOn_univ.mp hA.meromorphicOn) hr.ne'
  change (ValueDistribution.logCounting g (0 : WithTop ℂ) r -
      ValueDistribution.logCounting g (⊤ : WithTop ℂ) r) = _ at hJ
  have hcoeff : meromorphicTrailingCoeffAt g 0 = g 0 :=
    (hA 0 (by simp)).meromorphicTrailingCoeffAt_of_ne_zero hg0
  rw [htop, sub_zero, hcoeff] at hJ
  exact hJ

theorem ramification_eq_circleAverage_sub_const_of_wronskian_nezero_at_zero
    {n : ℕ} (f : Curve n)
    (hWdiff : Differentiable ℂ (fun z : ℂ => wronskian n f.coord z))
    (hW0 : wronskian n f.coord 0 ≠ 0) {r : ℝ} (hr : 0 < r) :
    ramification f r =
      Real.circleAverage
          (fun z : ℂ => Real.log ‖wronskian n f.coord z‖) 0 r -
        Real.log ‖wronskian n f.coord 0‖ := by
  unfold ramification
  exact logCounting_zero_eq_circleAverage_sub_const_of_entire
    hWdiff hr hW0

end

end FewInflection
