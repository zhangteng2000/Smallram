import ModifiedCartan.SubharmonicConvolution
import ModifiedCartan.WeakGradientHalfPlane
import ModifiedCartan.WeakGradientSmoothBound
import ModifiedCartan.WeakGradientSmoothConvergence
import ModifiedCartan.RegularizedLogBounds

open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory ContinuousLinearMap
set_option autoImplicit false
namespace ModifiedCartan

/-- The same actual mollifications simultaneously have a nonnegative
Laplacian, a half-plane gradient bound, and a uniform gradient norm bound. -/
theorem IsSubharmonicOn.eventually_smoothing_gradient_bounds
    {U : Set ℂ} (hU : IsOpen U) {u : ℂ → ℝ} {g : ℂ → ℂ}
    (hu : IsSubharmonicOn U (fun z => (u z : EReal)))
    (hc : Continuous u) (hw : HasWeakComplexGradient U u g)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᵐ z ∂volume.restrict U, ‖g z‖ ≤ C)
    (hgre : ∀ᵐ z ∂volume.restrict U, (g z).re ≤ 0)
    {c : ℂ} {r R : ℝ} (hrR : r < R) (hball : closedBall c R ⊆ U) :
    ∀ᶠ ν in atTop,
      (∀ x ∈ ball c r, (classicalComplexGradient
        (u ⋆[lsmul ℝ ℝ, volume] (shrinkingWeakBump ν).normed volume) x).re ≤ 0) ∧
      (∀ x ∈ ball c r, ‖classicalComplexGradient
        (u ⋆[lsmul ℝ ℝ, volume] (shrinkingWeakBump ν).normed volume) x‖ ≤ 2 * C) ∧
      (∀ x ∈ ball c r, 0 ≤ Laplacian.laplacian
        (u ⋆[lsmul ℝ ℝ, volume] (shrinkingWeakBump ν).normed volume) x) := by
  filter_upwards [shrinkingWeakBump_tendsto.eventually (gt_mem_nhds (sub_pos.mpr hrR))]
    with ν hν
  have htrans : ∀ x ∈ ball c r, ∀ w ∈ tsupport ((shrinkingWeakBump ν).normed volume), x - w ∈ U := by
    intro x hx w hw
    have hw' : ‖w‖ ≤ (shrinkingWeakBump ν).rOut := by
      simpa only [(shrinkingWeakBump ν).tsupport_normed_eq, mem_closedBall, dist_zero_right] using hw
    have hdist : dist (x - w) c ≤ dist x c + ‖w‖ := by
      have he : x - w - c = (x - c) - w := by abel
      simpa only [dist_eq_norm, he] using norm_sub_le (x - c) w
    apply hball
    apply mem_closedBall.mpr
    linarith [mem_ball.mp hx]
  have hsupp (x : ℂ) (hx : x ∈ ball c r) :
      (fun z : ℂ => x - z) ⁻¹' tsupport ((shrinkingWeakBump ν).normed volume) ⊆ U := by
    intro z hz
    simpa only [sub_sub_cancel] using htrans x hx (x - z) hz
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [classicalComplexGradient_re]
    apply hw.fderiv_convolution_apply_le hU hc.locallyIntegrable (fun _ _ => rfl)
      (shrinkingWeakBump ν).contDiff_normed (shrinkingWeakBump ν).hasCompactSupport_normed
      (shrinkingWeakBump ν).nonneg_normed (shrinkingWeakBump ν).integral_normed _ x (hsupp x hx)
    simpa only [mul_one] using hgre
  · intro x hx
    apply (norm_classicalComplexGradient_le _ _).trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
    exact hw.norm_fderiv_convolution_le hU hc.locallyIntegrable (fun _ _ => rfl)
      (shrinkingWeakBump ν).contDiff_normed (shrinkingWeakBump ν).hasCompactSupport_normed
      (shrinkingWeakBump ν).nonneg_normed (shrinkingWeakBump ν).integral_normed hC hbound x (hsupp x hx)
  · intro x hx
    exact hu.laplacian_convolution_nonneg isOpen_ball hc (shrinkingWeakBump ν).contDiff_normed
      (shrinkingWeakBump ν).hasCompactSupport_normed (shrinkingWeakBump ν).nonneg_normed htrans hx

end ModifiedCartan
#print axioms ModifiedCartan.IsSubharmonicOn.eventually_smoothing_gradient_bounds
