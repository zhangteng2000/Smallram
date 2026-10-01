import ModifiedCartan.DirectionalPhaseTest
import ModifiedCartan.DirectionalTestSmoothing
import ModifiedCartan.PhaseIndicator

open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory ContinuousLinearMap
set_option autoImplicit false
namespace ModifiedCartan

theorem IsSubharmonicOn.phaseCutoff_test
    {U : Set ℂ} (hU : IsOpen U) {u : ℂ → ℝ} {g : ℂ → ℂ}
    (hu : IsSubharmonicOn U (fun z => (u z : EReal)))
    (hc : Continuous u) (hw : HasWeakComplexGradient U u g)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᵐ z ∂volume.restrict U, ‖g z‖ ≤ C)
    (a w : ℂ) (hgre : ∀ᵐ z ∂volume.restrict U, ((g z - a) * w).re ≤ 0)
    {c : ℂ} {r R : ℝ} (hrR : r < R) (hball : closedBall c R ⊆ U)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hφr : tsupport φ ⊆ ball c r) (hφpos : ∀ z, 0 ≤ φ z) :
    (∫ z, phaseCutoff (closedBall c R) g a z * fderiv ℝ φ z w) ≤ 0 := by
  have heq : phaseCutoff (closedBall c R) g a =ᵐ[volume.restrict (ball c r)]
      (fun z => if g z = a then (1 : ℝ) else 0) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    rw [phaseCutoff_eq ((ball_subset_closedBall.trans (closedBall_subset_closedBall hrR.le)) hz),
      phaseIndicator_eq_ite]
  rw [integral_mul_test_congr_ae measurableSet_ball heq
    ((tsupport_fderiv_apply_subset ℝ w).trans hφr)]
  exact hu.weak_gradient_phase_test hU hc hw hC hbound a w hgre hrR hball hφ hφc hφr hφpos

/-- The same sufficiently fine phase smoothing is ordered between every
pair of interior points whose displacement belongs to the supporting cone. -/
theorem IsSubharmonicOn.eventually_phaseCutoff_convolution_mono
    {U : Set ℂ} (hU : IsOpen U) {u : ℂ → ℝ} {g : ℂ → ℂ}
    (hu : IsSubharmonicOn U (fun z => (u z : EReal)))
    (hc : Continuous u) (hw : HasWeakComplexGradient U u g)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᵐ z ∂volume.restrict U, ‖g z‖ ≤ C)
    (a : ℂ) {c : ℂ} {s r R : ℝ} (hsr : s < r) (hrR : r < R) (hball : closedBall c R ⊆ U) :
    ∀ᶠ ν in atTop, ∀ x ∈ ball c s, ∀ y ∈ ball c s,
      (∀ᵐ z ∂volume.restrict U, ((g z - a) * (y - x)).re ≤ 0) →
      (phaseCutoff (closedBall c R) g a ⋆[lsmul ℝ ℝ, volume] (shrinkingWeakBump ν).normed volume) x ≤
      (phaseCutoff (closedBall c R) g a ⋆[lsmul ℝ ℝ, volume] (shrinkingWeakBump ν).normed volume) y := by
  have hqi := integrable_phaseCutoff (isCompact_closedBall c R)
    (hw.gradient_integrable _ (isCompact_closedBall c R) hball) a
  have hm : s < (s + r) / 2 := by linarith
  have hmr : closedBall c ((s + r) / 2) ⊆ ball c r := closedBall_subset_ball (by linarith)
  filter_upwards [shrinkingWeakBump_eventually_translations_subset hm hmr] with ν hν x hx y hy hcone
  have hh := convolution_le_along_line_of_tests hqi.locallyIntegrable (y - x)
    (fun φ hφ hφc hφr hφpos => hu.phaseCutoff_test hU hc hw hC hbound a (y - x) hcone
      hrR hball hφ hφc hφr hφpos)
    ((shrinkingWeakBump ν).contDiff_normed (μ := volume))
    ((shrinkingWeakBump ν).hasCompactSupport_normed (μ := volume))
    ((shrinkingWeakBump ν).nonneg_normed (μ := volume)) x (T := 1) zero_le_one ?_
  · simpa only [one_smul, add_sub_cancel] using hh
  · intro t ht z hz
    have hline : x + t • (y - x) ∈ ball c s :=
      (convex_ball c s).add_smul_mem hx (by simpa only [add_sub_cancel] using hy) ht
    simpa only [sub_sub_cancel] using hν (x + t • (y - x)) hline (x + t • (y - x) - z) hz

end ModifiedCartan
#print axioms ModifiedCartan.IsSubharmonicOn.eventually_phaseCutoff_convolution_mono
