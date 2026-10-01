import ModifiedCartan.PhaseLogDominated
import ModifiedCartan.WeakGradientLogTest

open scoped Topology ContDiff
open Filter Set Metric MeasureTheory ContinuousLinearMap
set_option autoImplicit false
namespace ModifiedCartan

/-- The zero-phase indicator of a bounded half-plane-valued weak gradient
has a nonnegative real-direction distributional derivative. -/
theorem IsSubharmonicOn.weak_gradient_zero_phase_test
    {U : Set ℂ} (hU : IsOpen U) {u : ℂ → ℝ} {g : ℂ → ℂ}
    (hu : IsSubharmonicOn U (fun z => (u z : EReal)))
    (hc : Continuous u) (hw : HasWeakComplexGradient U u g)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᵐ z ∂volume.restrict U, ‖g z‖ ≤ C)
    (hgre : ∀ᵐ z ∂volume.restrict U, (g z).re ≤ 0)
    {c : ℂ} {r R : ℝ} (hrR : r < R) (hball : closedBall c R ⊆ U)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hφr : tsupport φ ⊆ ball c r) (hφpos : ∀ z, 0 ≤ φ z) :
    (∫ z, (if g z = 0 then (1 : ℝ) else 0) * fderiv ℝ φ z 1) ≤ 0 := by
  classical
  have hK : tsupport φ ⊆ U := hφr.trans
    ((ball_subset_closedBall.trans (closedBall_subset_closedBall hrR.le)).trans hball)
  have hgm := (hw.gradient_integrable _ hφc hK).aestronglyMeasurable
  have hbounds : ∀ᵐ z ∂volume.restrict (tsupport φ), (g z).re ≤ 0 ∧ ‖g z‖ ≤ C := by
    filter_upwards [hbound.filter_mono (ae_mono (Measure.restrict_mono_set _ hK)),
      hgre.filter_mono (ae_mono (Measure.restrict_mono_set _ hK))] with z hz hz'
    exact ⟨hz', hz⟩
  have ht (L : ℂ →L[ℝ] ℝ) (w : ℂ) :
      Tendsto (fun ν => ∫ z, L (phaseLogApprox ν (g z)) * fderiv ℝ φ z w) atTop
        (𝓝 (∫ z, (if g z = 0 then L 1 else 0) * fderiv ℝ φ z w)) := by
    have hψ : Continuous (fun z => fderiv ℝ φ z w) :=
      (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hp : IntegrableOn (fun z => fderiv ℝ φ z w) (tsupport φ) :=
      hψ.continuousOn.integrableOn_compact hφc
    have heq (a : ℂ → ℝ) : (∫ z in tsupport φ, a z * fderiv ℝ φ z w) =
        ∫ z, a z * fderiv ℝ φ z w := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      have hz' : z ∉ tsupport (fun y => fderiv ℝ φ y w) :=
        fun hh => hz (tsupport_fderiv_apply_subset ℝ w hh)
      rw [image_eq_zero_of_notMem_tsupport hz', mul_zero]
    simpa only [heq] using integral_phaseLogApprox_tendsto hgm hC hbounds hp L
  have hreal : Tendsto (fun ν => ∫ z, (phaseLogApprox ν (g z)).re * fderiv ℝ φ z 1) atTop
      (𝓝 (∫ z, (if g z = 0 then (1 : ℝ) else 0) * fderiv ℝ φ z 1)) := by
    simpa using ht Complex.reCLM 1
  have himag : Tendsto (fun ν => ∫ z, (phaseLogApprox ν (g z)).im * fderiv ℝ φ z Complex.I)
      atTop (𝓝 0) := by
    simpa using ht Complex.imCLM Complex.I
  apply le_of_tendsto_of_tendsto hreal himag
  apply Eventually.of_forall
  intro ν
  have hh := hu.weak_gradient_regularized_log_test hU hc hw hC hbound hgre hrR hball
    (Real.exp_pos (-phaseLogScale ν)) hφ hφc hφr hφpos
  simp only [phaseLogApprox, Complex.smul_re, Complex.smul_im, smul_eq_mul,
    mul_assoc, integral_const_mul]
  exact mul_le_mul_of_nonpos_left hh (neg_nonpos.mpr (inv_nonneg.mpr (phaseLogScale_pos ν).le))

end ModifiedCartan
#print axioms ModifiedCartan.IsSubharmonicOn.weak_gradient_zero_phase_test
