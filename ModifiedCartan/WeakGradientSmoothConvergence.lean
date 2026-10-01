import ModifiedCartan.WeakGradientConvolution
import ModifiedCartan.WeakGradientConstancy

open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory ContinuousLinearMap
set_option autoImplicit false
namespace ModifiedCartan

/-- The actual derivatives of the mollified function converge almost
everywhere to each direction of its original weak gradient. -/
theorem HasWeakComplexGradient.ae_fderiv_smoothing_tendsto
    {U : Set ℂ} {u : ℂ → ℝ} {g : ℂ → ℂ} (hu : HasWeakComplexGradient U u g)
    (hui : LocallyIntegrable u) {c : ℂ} {r R : ℝ}
    (hrR : r < R) (hball : closedBall c R ⊆ U) (w : ℂ) :
    ∀ᵐ x ∂volume.restrict (ball c r),
      Tendsto (fun ν => fderiv ℝ (u ⋆[lsmul ℝ ℝ, volume]
        (shrinkingWeakBump ν).normed volume) x w) atTop (𝓝 ((g x * w).re)) := by
  classical
  let q : ℂ → ℝ := (closedBall c R).indicator (fun z => (g z * w).re)
  have hqr : IntegrableOn (fun z => (g z * w).re) (closedBall c R) :=
    Complex.reCLM.integrable_comp ((hu.gradient_integrable _
      (isCompact_closedBall c R) hball).mul_const w)
  have hqi : Integrable q := hqr.integrable_indicator measurableSet_closedBall
  have huR := hu.restrict (ball_subset_closedBall.trans hball)
  have heq : ∀ᶠ ν in atTop, ∀ x ∈ ball c r,
      fderiv ℝ (u ⋆[lsmul ℝ ℝ, volume] (shrinkingWeakBump ν).normed volume) x w =
      (q ⋆[lsmul ℝ ℝ, volume] (shrinkingWeakBump ν).normed volume) x := by
    filter_upwards [shrinkingWeakBump_tendsto.eventually (gt_mem_nhds (sub_pos.mpr hrR))]
      with ν hν x hx
    have hsupp : (fun z : ℂ => x - z) ⁻¹' tsupport ((shrinkingWeakBump ν).normed volume) ⊆ ball c R := by
      intro z hz
      have hsmall : dist (x - z) 0 ≤ (shrinkingWeakBump ν).rOut := by
        rw [(shrinkingWeakBump ν).tsupport_normed_eq] at hz
        exact hz
      have hdist : dist z c ≤ dist x c + dist (x - z) 0 := by
        simpa only [dist_zero_right, dist_eq_norm, norm_sub_rev, sub_zero, add_comm] using dist_triangle z x c
      exact mem_ball.mpr (by linarith [mem_ball.mp hx])
    rw [huR.fderiv_convolution_apply isOpen_ball hui (fun _ _ => rfl)
      (shrinkingWeakBump ν).contDiff_normed (shrinkingWeakBump ν).hasCompactSupport_normed x hsupp w,
      convolution_def]
    change (∫ z, (g z * w).re * (shrinkingWeakBump ν).normed volume (x - z)) =
      ∫ z, q z * (shrinkingWeakBump ν).normed volume (x - z)
    apply integral_congr_ae
    apply Eventually.of_forall
    intro z
    dsimp only
    by_cases hz : z ∈ closedBall c R
    · rw [show q z = (g z * w).re from indicator_of_mem hz _]
    · have hz' : x - z ∉ tsupport ((shrinkingWeakBump ν).normed volume) :=
        fun hh => hz (ball_subset_closedBall (hsupp hh))
      rw [image_eq_zero_of_notMem_tsupport hz', mul_zero, mul_zero]
  have hratio : ∀ ν, (shrinkingWeakBump ν).rOut ≤ 2 * (shrinkingWeakBump ν).rIn := by
    intro ν
    dsimp only [shrinkingWeakBump]
    linarith
  have hae := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    shrinkingWeakBump_tendsto (Eventually.of_forall hratio) hqi.locallyIntegrable
  filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem measurableSet_ball] with x hx hxball
  have hqx : q x = (g x * w).re := indicator_of_mem
    ((ball_subset_closedBall.trans (closedBall_subset_closedBall hrR.le)) hxball) _
  rw [hqx] at hx
  have ht : Tendsto (fun ν => (q ⋆[lsmul ℝ ℝ, volume] (shrinkingWeakBump ν).normed volume) x)
      atTop (𝓝 ((g x * w).re)) := by
    simpa only [real_convolution_comm q] using hx
  exact (tendsto_congr' (heq.mono (fun ν hν => hν x hxball))).mpr ht

theorem HasWeakComplexGradient.ae_classicalGradient_smoothing_tendsto
    {U : Set ℂ} {u : ℂ → ℝ} {g : ℂ → ℂ} (hu : HasWeakComplexGradient U u g)
    (hui : LocallyIntegrable u) {c : ℂ} {r R : ℝ}
    (hrR : r < R) (hball : closedBall c R ⊆ U) :
    ∀ᵐ x ∂volume.restrict (ball c r),
      Tendsto (fun ν => classicalComplexGradient (u ⋆[lsmul ℝ ℝ, volume]
        (shrinkingWeakBump ν).normed volume) x) atTop (𝓝 (g x)) := by
  filter_upwards [hu.ae_fderiv_smoothing_tendsto hui hrR hball 1,
    hu.ae_fderiv_smoothing_tendsto hui hrR hball Complex.I] with x hx hIx
  have h₁ := Complex.continuous_ofReal.continuousAt.tendsto.comp hx
  have h₂ := Complex.continuous_ofReal.continuousAt.tendsto.comp hIx
  have he : ((g x * 1).re : ℂ) - Complex.I * ((g x * Complex.I).re : ℂ) = g x := by
    apply Complex.ext <;> simp
  simpa only [classicalComplexGradient, Function.comp_def, he] using h₁.sub (h₂.const_mul Complex.I)

end ModifiedCartan
#print axioms ModifiedCartan.HasWeakComplexGradient.ae_classicalGradient_smoothing_tendsto
