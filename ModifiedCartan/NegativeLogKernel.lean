import ModifiedCartan.LogKernel
import ModifiedCartan.CauchyTruncation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open scoped Topology ENNReal
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan
noncomputable section

/-- Integrable representative of the negative logarithm of the norm.
Its value at zero is zero; exceptional polynomial zeros are handled separately.
LaTeX context: `eq:polynomial-negative-area`. -/
def negativeLogNorm (z : ℂ) : ℝ := max 0 (-Real.log ‖z‖)

theorem negativeLogNorm_nonneg (z : ℂ) : 0 ≤ negativeLogNorm z :=
  le_max_left _ _

theorem measurable_negativeLogNorm : Measurable negativeLogNorm :=
  measurable_const.max ((Real.measurable_log.comp measurable_norm).neg)

theorem negativeLogNorm_mul_le (z w : ℂ) :
    negativeLogNorm (z * w) ≤ negativeLogNorm z + negativeLogNorm w := by
  by_cases hz : z = 0
  · simp [hz, negativeLogNorm]
  by_cases hw : w = 0
  · simp [hw, negativeLogNorm]
  rw [negativeLogNorm, norm_mul,
    Real.log_mul (norm_ne_zero_iff.mpr hz) (norm_ne_zero_iff.mpr hw)]
  apply max_le
  · exact add_nonneg (negativeLogNorm_nonneg z) (negativeLogNorm_nonneg w)
  · have hz' : -Real.log ‖z‖ ≤ negativeLogNorm z := le_max_right _ _
    have hw' : -Real.log ‖w‖ ≤ negativeLogNorm w := le_max_right _ _
    linarith

theorem negativeLogNorm_prod_le {ι : Type*} (S : Finset ι) (v : ι → ℂ) :
    negativeLogNorm (∏ i ∈ S, v i) ≤ ∑ i ∈ S, negativeLogNorm (v i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [negativeLogNorm]
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact (negativeLogNorm_mul_le _ _).trans (add_le_add le_rfl ih)

theorem negativeLogNorm_eq_indicator :
    negativeLogNorm = (ball (0 : ℂ) 1).indicator (fun z => -Real.log ‖z‖) := by
  funext z
  by_cases hz : z ∈ ball (0 : ℂ) 1
  · rw [indicator_of_mem hz, negativeLogNorm, max_eq_right]
    exact neg_nonneg.mpr (Real.log_nonpos (norm_nonneg z)
      ((show ‖z‖ < 1 by simpa only [mem_ball, dist_zero_right] using hz).le))
  · rw [indicator_of_notMem hz, negativeLogNorm, max_eq_left]
    exact neg_nonpos.mpr (Real.log_nonneg (by
      simpa only [mem_ball, dist_zero_right, not_lt] using hz))

theorem integrable_negativeLogNorm : Integrable negativeLogNorm := by
  rw [negativeLogNorm_eq_indicator]
  apply IntegrableOn.integrable_indicator _ measurableSet_ball
  have h := (integrableOn_logKernel (0 : ℂ) (isCompact_closedBall 0 1)).neg
  convert! h.mono_set ball_subset_closedBall using 1
  funext z
  change -Real.log ‖z‖ = -Real.log ‖z - 0‖
  rw [sub_zero]

theorem integral_mul_log_unit_interval :
    (∫ r : ℝ in (0 : ℝ)..1, r * Real.log r) = -(1 / 4 : ℝ) := by
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := 0) (b := 1) (f := fun x : ℝ => x ^ 2) (f' := fun x => 2 * x)
    (g := Real.log) (by fun_prop)
    (fun x _ => by
      convert! (hasDerivAt_id x).pow 2 using 1
      simp)
    (fun x hx => by
      simp only [min_eq_left (by norm_num : (0 : ℝ) ≤ 1),
        max_eq_right (by norm_num : (0 : ℝ) ≤ 1), mem_Ioo] at hx
      exact mul_nonneg (by norm_num) hx.1.le)
  have heq : (fun x : ℝ => (Real.log ∘ (fun y => y ^ 2)) x * (2 * x)) =
      fun x => 4 * (x * Real.log x) := by
    funext x
    simp only [Function.comp_def, Real.log_pow, Nat.cast_ofNat]
    ring
  rw [heq, intervalIntegral.integral_const_mul] at hsub
  norm_num at hsub
  linarith

theorem integral_negativeLogNorm :
    (∫ z : ℂ, negativeLogNorm z) = Real.pi / 2 := by
  rw [negativeLogNorm_eq_indicator, integral_indicator measurableSet_ball,
    radial_integral_ball (fun r : ℝ => -Real.log r) 1]
  have heq : (fun r : ℝ => r * -Real.log r) = fun r => -(r * Real.log r) := by
    funext r
    ring
  rw [heq, integral_neg, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_mul_log_unit_interval]
  ring

theorem integrable_negativeLogNorm_sub (a : ℂ) :
    Integrable (fun z : ℂ => negativeLogNorm (z - a)) := by
  exact ((measurePreserving_sub_right (volume : Measure ℂ) a).integrable_comp
    measurable_negativeLogNorm.aestronglyMeasurable).mpr integrable_negativeLogNorm

theorem integral_negativeLogNorm_sub (a : ℂ) :
    (∫ z : ℂ, negativeLogNorm (z - a)) = Real.pi / 2 := by
  rw [integral_sub_right_eq_self, integral_negativeLogNorm]

end
end ModifiedCartan
