import ModifiedCartan.SubharmonicGradientSmoothing
import ModifiedCartan.RegularizedLogTest

open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory ContinuousLinearMap
set_option autoImplicit false
namespace ModifiedCartan

/-- The logarithmic test inequality for the original weak gradient,
obtained from the actual mollifications and dominated convergence. -/
theorem IsSubharmonicOn.weak_gradient_regularized_log_test
    {U : Set ℂ} (hU : IsOpen U) {u : ℂ → ℝ} {g : ℂ → ℂ}
    (hu : IsSubharmonicOn U (fun z => (u z : EReal)))
    (hc : Continuous u) (hw : HasWeakComplexGradient U u g)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᵐ z ∂volume.restrict U, ‖g z‖ ≤ C)
    (hgre : ∀ᵐ z ∂volume.restrict U, (g z).re ≤ 0)
    {c : ℂ} {r R : ℝ} (hrR : r < R) (hball : closedBall c R ⊆ U)
    {ε : ℝ} (hε : 0 < ε) {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (hφr : tsupport φ ⊆ ball c r) (hφpos : ∀ z, 0 ≤ φ z) :
    (∫ z, (Complex.log ((ε : ℂ) - g z)).im * fderiv ℝ φ z Complex.I) ≤
      ∫ z, (Complex.log ((ε : ℂ) - g z)).re * fderiv ℝ φ z 1 := by
  let F : ℕ → ℂ → ℝ := fun ν => u ⋆[lsmul ℝ ℝ, volume] (shrinkingWeakBump ν).normed volume
  let G : ℕ → ℂ → ℂ := fun ν => classicalComplexGradient (F ν)
  have hF (ν : ℕ) : ContDiff ℝ ∞ (F ν) :=
    (shrinkingWeakBump ν).hasCompactSupport_normed.contDiff_convolution_right
      (lsmul ℝ ℝ) hc.locallyIntegrable (shrinkingWeakBump ν).contDiff_normed
  have hG (ν : ℕ) : Continuous (G ν) :=
    continuous_classicalComplexGradient ((hF ν).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1))
  have hK : tsupport φ ⊆ U := hφr.trans
    ((ball_subset_closedBall.trans (closedBall_subset_closedBall hrR.le)).trans hball)
  have hs := hu.eventually_smoothing_gradient_bounds hU hc hw hC hbound hgre hrR hball
  have hlim : ∀ᵐ z ∂volume.restrict (tsupport φ),
      Tendsto (fun ν => G ν z) atTop (𝓝 (g z)) :=
    (hw.ae_classicalGradient_smoothing_tendsto hc.locallyIntegrable hrR hball).filter_mono
      (ae_mono (Measure.restrict_mono_set _ hφr))
  have hgreK : ∀ᵐ z ∂volume.restrict (tsupport φ), (g z).re ≤ 0 :=
    hgre.filter_mono (ae_mono (Measure.restrict_mono_set _ hK))
  have hbounds : ∀ᶠ ν in atTop, ∀ᵐ z ∂volume.restrict (tsupport φ),
      (G ν z).re ≤ 0 ∧ ‖G ν z‖ ≤ 2 * C := by
    filter_upwards [hs] with ν hν
    filter_upwards [ae_restrict_mem hφc.measurableSet] with z hz
    exact ⟨hν.1 z (hφr hz), hν.2.1 z (hφr hz)⟩
  have ht (L : ℂ →L[ℝ] ℝ) (w : ℂ) :
      Tendsto (fun ν => ∫ z, L (Complex.log ((ε : ℂ) - G ν z)) * fderiv ℝ φ z w) atTop
        (𝓝 (∫ z, L (Complex.log ((ε : ℂ) - g z)) * fderiv ℝ φ z w)) := by
    have hψ : Continuous (fun z => fderiv ℝ φ z w) :=
      (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hp : IntegrableOn (fun z => fderiv ℝ φ z w) (tsupport φ) :=
      hψ.continuousOn.integrableOn_compact hφc
    have heq (a : ℂ → ℂ) :
        (∫ z in tsupport φ, L (Complex.log ((ε : ℂ) - a z)) * fderiv ℝ φ z w) =
          ∫ z, L (Complex.log ((ε : ℂ) - a z)) * fderiv ℝ φ z w := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      have hz' : z ∉ tsupport (fun y => fderiv ℝ φ y w) :=
        fun hh => hz (tsupport_fderiv_apply_subset ℝ w hh)
      rw [image_eq_zero_of_notMem_tsupport hz', mul_zero]
    have ht' := integral_regularized_clog_tendsto hε
      (Eventually.of_forall (fun ν => (hG ν).aestronglyMeasurable)) hbounds hgreK hlim hp L
    simpa only [heq] using ht'
  apply le_of_tendsto_of_tendsto (ht Complex.imCLM Complex.I) (ht Complex.reCLM 1)
  filter_upwards [hs] with ν hν
  exact regularized_clog_gradient_test_inequality isOpen_ball
    ((hF ν).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hε
    hν.1 hν.2.2 hφ hφc hφr hφpos

end ModifiedCartan
#print axioms ModifiedCartan.IsSubharmonicOn.weak_gradient_regularized_log_test
