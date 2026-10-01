import ModifiedCartan.SubharmonicGradientSmoothing

open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory ContinuousLinearMap
set_option autoImplicit false
namespace ModifiedCartan

theorem classicalComplexGradient_mul_re (f : ℂ → ℝ) (z w : ℂ) :
    (classicalComplexGradient f z * w).re = fderiv ℝ f z w := by
  rw [realCLM_apply_complex (fderiv ℝ f z) w]
  simp [classicalComplexGradient, Complex.mul_re]
  ring

theorem shrinkingWeakBump_eventually_translations_subset {U : Set ℂ}
    {c : ℂ} {r R : ℝ} (hrR : r < R) (hball : closedBall c R ⊆ U) :
    ∀ᶠ ν in atTop, ∀ x ∈ ball c r,
      ∀ w ∈ tsupport ((shrinkingWeakBump ν).normed volume), x - w ∈ U := by
  filter_upwards [shrinkingWeakBump_tendsto.eventually (gt_mem_nhds (sub_pos.mpr hrR))]
    with ν hν x hx w hw
  have hw' : ‖w‖ ≤ (shrinkingWeakBump ν).rOut := by
    simpa only [(shrinkingWeakBump ν).tsupport_normed_eq, mem_closedBall, dist_zero_right] using hw
  have hdist : dist (x - w) c ≤ dist x c + ‖w‖ := by
    have he : x - w - c = (x - c) - w := by abel
    simpa only [dist_eq_norm, he] using norm_sub_le (x - c) w
  apply hball
  apply mem_closedBall.mpr
  linarith [mem_ball.mp hx]

theorem IsSubharmonicOn.eventually_directional_smoothing_gradient_bounds
    {U : Set ℂ} (hU : IsOpen U) {u : ℂ → ℝ} {g : ℂ → ℂ}
    (hu : IsSubharmonicOn U (fun z => (u z : EReal)))
    (hc : Continuous u) (hw : HasWeakComplexGradient U u g)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᵐ z ∂volume.restrict U, ‖g z‖ ≤ C)
    (a w : ℂ) (hgre : ∀ᵐ z ∂volume.restrict U, ((g z - a) * w).re ≤ 0)
    {c : ℂ} {r R : ℝ} (hrR : r < R) (hball : closedBall c R ⊆ U) :
    ∀ᶠ ν in atTop,
      (∀ x ∈ ball c r, ((classicalComplexGradient
        (u ⋆[lsmul ℝ ℝ, volume] (shrinkingWeakBump ν).normed volume) x - a) * w).re ≤ 0) ∧
      (∀ x ∈ ball c r, ‖(classicalComplexGradient
        (u ⋆[lsmul ℝ ℝ, volume] (shrinkingWeakBump ν).normed volume) x - a) * w‖ ≤
          (2 * C + ‖a‖) * ‖w‖) ∧
      (∀ x ∈ ball c r, 0 ≤ Laplacian.laplacian
        (u ⋆[lsmul ℝ ℝ, volume] (shrinkingWeakBump ν).normed volume) x) := by
  filter_upwards [shrinkingWeakBump_eventually_translations_subset hrR hball] with ν htrans
  have hsupp (x : ℂ) (hx : x ∈ ball c r) :
      (fun z : ℂ => x - z) ⁻¹' tsupport ((shrinkingWeakBump ν).normed volume) ⊆ U := by
    intro z hz
    simpa only [sub_sub_cancel] using htrans x hx (x - z) hz
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [sub_mul, Complex.sub_re, classicalComplexGradient_mul_re]
    apply sub_nonpos.mpr
    apply hw.fderiv_convolution_apply_le hU hc.locallyIntegrable (fun _ _ => rfl)
      (shrinkingWeakBump ν).contDiff_normed (shrinkingWeakBump ν).hasCompactSupport_normed
      (shrinkingWeakBump ν).nonneg_normed (shrinkingWeakBump ν).integral_normed _ x (hsupp x hx)
    simpa only [sub_mul, Complex.sub_re, sub_nonpos] using hgre
  · intro x hx
    have hn := hw.norm_fderiv_convolution_le hU hc.locallyIntegrable (fun _ _ => rfl)
      (shrinkingWeakBump ν).contDiff_normed (shrinkingWeakBump ν).hasCompactSupport_normed
      (shrinkingWeakBump ν).nonneg_normed (shrinkingWeakBump ν).integral_normed hC hbound x (hsupp x hx)
    have hg := (norm_classicalComplexGradient_le
      (u ⋆[lsmul ℝ ℝ, volume] (shrinkingWeakBump ν).normed volume) x).trans
      (mul_le_mul_of_nonneg_left hn (by norm_num : (0 : ℝ) ≤ 2))
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg w)
    exact (norm_sub_le _ _).trans (add_le_add hg le_rfl)
  · intro x hx
    exact hu.laplacian_convolution_nonneg isOpen_ball hc (shrinkingWeakBump ν).contDiff_normed
      (shrinkingWeakBump ν).hasCompactSupport_normed (shrinkingWeakBump ν).nonneg_normed htrans hx

end ModifiedCartan
#print axioms ModifiedCartan.IsSubharmonicOn.eventually_directional_smoothing_gradient_bounds
