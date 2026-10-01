import ModifiedCartan.WeakDirectionalLogTest
import ModifiedCartan.LogPhaseTest

open scoped Topology ContDiff
open Filter Set Metric MeasureTheory ContinuousLinearMap
set_option autoImplicit false
namespace ModifiedCartan

/-- An extremal phase has a nonnegative distributional derivative in each
direction of its supporting cone. All hypotheses concern the actual gradient. -/
theorem IsSubharmonicOn.weak_gradient_phase_test
    {U : Set ℂ} (hU : IsOpen U) {u : ℂ → ℝ} {g : ℂ → ℂ}
    (hu : IsSubharmonicOn U (fun z => (u z : EReal)))
    (hc : Continuous u) (hw : HasWeakComplexGradient U u g)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᵐ z ∂volume.restrict U, ‖g z‖ ≤ C)
    (a w : ℂ) (hgre : ∀ᵐ z ∂volume.restrict U, ((g z - a) * w).re ≤ 0)
    {c : ℂ} {r R : ℝ} (hrR : r < R) (hball : closedBall c R ⊆ U)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hφr : tsupport φ ⊆ ball c r) (hφpos : ∀ z, 0 ≤ φ z) :
    (∫ z, (if g z = a then (1 : ℝ) else 0) * fderiv ℝ φ z w) ≤ 0 := by
  classical
  by_cases hw0 : w = 0
  · simp only [hw0, map_zero, mul_zero, integral_zero, le_refl]
  have hK : tsupport φ ⊆ U := hφr.trans
    ((ball_subset_closedBall.trans (closedBall_subset_closedBall hrR.le)).trans hball)
  have hgm₀ : AEStronglyMeasurable g (volume.restrict (tsupport φ)) :=
    (hw.gradient_integrable _ hφc hK).aestronglyMeasurable
  have hgm : AEStronglyMeasurable (fun z => (g z - a) * w) (volume.restrict (tsupport φ)) :=
    (hgm₀.sub aestronglyMeasurable_const).mul aestronglyMeasurable_const
  have hB : 0 ≤ (C + ‖a‖) * ‖w‖ := mul_nonneg (add_nonneg hC (norm_nonneg _)) (norm_nonneg _)
  have hbounds : ∀ᵐ z ∂volume.restrict (tsupport φ),
      ((g z - a) * w).re ≤ 0 ∧ ‖(g z - a) * w‖ ≤ (C + ‖a‖) * ‖w‖ := by
    filter_upwards [hbound.filter_mono (ae_mono (Measure.restrict_mono_set _ hK)),
      hgre.filter_mono (ae_mono (Measure.restrict_mono_set _ hK))] with z hz hz'
    refine ⟨hz', ?_⟩
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right ((norm_sub_le _ _).trans (add_le_add hz le_rfl)) (norm_nonneg w)
  have hh := phase_test_of_regularized_log_tests hφ hφc hgm hB hbounds w
    (fun ε hε => hu.weak_gradient_directional_regularized_log_test hU hc hw hC hbound a w hgre
      hrR hball hε hφ hφc hφr hφpos)
  simpa only [mul_eq_zero, hw0, or_false, sub_eq_zero] using hh

end ModifiedCartan
#print axioms ModifiedCartan.IsSubharmonicOn.weak_gradient_phase_test
