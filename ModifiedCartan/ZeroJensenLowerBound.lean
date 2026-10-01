import ModifiedCartan.Counting
import ModifiedCartan.DivisorPolynomial

open scoped Topology BigOperators
open Filter Set Metric MeromorphicOn Function Function.locallyFinsuppWithin
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

theorem divisor_at_zero_ge_one {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    (hHnonzero : ∃ z, H z ≠ 0) (hzero : H 0 = 0) :
    1 ≤ divisor H univ 0 := by
  have hA := Complex.analyticOnNhd_univ_iff_differentiable.mpr hH
  have hnonneg : 0 ≤ divisor H univ 0 := hA.divisor_nonneg 0
  have hne : divisor H univ 0 ≠ 0 := by
    rw [hA.meromorphicOn.divisor_apply (mem_univ 0)]
    intro h
    have hord : meromorphicOrderAt H 0 = 0 :=
      (WithTop.untop₀_eq_zero.mp h).resolve_right (entire_meromorphicOrder_ne_top hH hHnonzero 0)
    exact ((hA 0 (mem_univ 0)).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp hord) hzero
  omega

theorem log_le_logCounting_of_zero {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    (hHnonzero : ∃ z, H z ≠ 0) (hzero : H 0 = 0) {r : ℝ} (hr : 1 ≤ r) :
    Real.log r ≤ ValueDistribution.logCounting H (0 : WithTop ℂ) r := by
  classical
  have hA := Complex.analyticOnNhd_univ_iff_differentiable.mpr hH
  have hD : single (0 : ℂ) (1 : ℤ) ≤ divisor H univ := by
    intro z
    by_cases hz : z = 0
    · subst z
      simpa [single_apply] using divisor_at_zero_ge_one hH hHnonzero hzero
    · simpa [single_apply, hz] using hA.divisor_nonneg z
  have hl := Function.locallyFinsuppWithin.logCounting_le hD hr
  rw [logCounting_single_eq_log_sub_const (by simpa using zero_le_one.trans hr),
    norm_zero, Real.log_zero, sub_zero, Int.cast_one, one_mul] at hl
  simpa only [ValueDistribution.logCounting_zero, posPart_eq_self.mpr hA.divisor_nonneg] using hl

theorem scalar_logarithmic_circle_lower_bound {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    (hHnonzero : ∃ z, H z ≠ 0) (hzero : H 0 = 0) {r : ℝ} (hr : 1 ≤ r) :
    Real.log r + Real.log ‖meromorphicTrailingCoeffAt H 0‖ ≤
      Real.circleAverage (fun z => Real.log ‖H z‖) 0 r := by
  rw [Paper.eq_zerojensen hH (ne_of_gt (zero_lt_one.trans_le hr))]
  have hl := log_le_logCounting_of_zero hH hHnonzero hzero hr
  linarith

end
end ModifiedCartan
#print axioms ModifiedCartan.scalar_logarithmic_circle_lower_bound
