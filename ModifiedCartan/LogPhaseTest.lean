import ModifiedCartan.PhaseLogDominated
import ModifiedCartan.RegularizedLogTest

open scoped Topology ContDiff
open Filter Set MeasureTheory ContinuousLinearMap
set_option autoImplicit false
namespace ModifiedCartan

/-- A family of proved logarithmic test inequalities gives the test
inequality for the zero set of the same function, in any direction. -/
theorem phase_test_of_regularized_log_tests {g : ℂ → ℂ} {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hg : AEStronglyMeasurable g (volume.restrict (tsupport φ)))
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᵐ z ∂volume.restrict (tsupport φ), (g z).re ≤ 0 ∧ ‖g z‖ ≤ C)
    (w : ℂ)
    (hlog : ∀ ε : ℝ, 0 < ε →
      (∫ z, (Complex.log ((ε : ℂ) - g z)).im * fderiv ℝ φ z (Complex.I * w)) ≤
        ∫ z, (Complex.log ((ε : ℂ) - g z)).re * fderiv ℝ φ z w) :
    (∫ z, (if g z = 0 then (1 : ℝ) else 0) * fderiv ℝ φ z w) ≤ 0 := by
  classical
  have ht (L : ℂ →L[ℝ] ℝ) (v : ℂ) :
      Tendsto (fun ν => ∫ z, L (phaseLogApprox ν (g z)) * fderiv ℝ φ z v) atTop
        (𝓝 (∫ z, (if g z = 0 then L 1 else 0) * fderiv ℝ φ z v)) := by
    have hψ : Continuous (fun z => fderiv ℝ φ z v) :=
      (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hp : IntegrableOn (fun z => fderiv ℝ φ z v) (tsupport φ) :=
      hψ.continuousOn.integrableOn_compact hφc
    have heq (a : ℂ → ℝ) : (∫ z in tsupport φ, a z * fderiv ℝ φ z v) =
        ∫ z, a z * fderiv ℝ φ z v := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      have hz' : z ∉ tsupport (fun y => fderiv ℝ φ y v) :=
        fun hh => hz (tsupport_fderiv_apply_subset ℝ v hh)
      rw [image_eq_zero_of_notMem_tsupport hz', mul_zero]
    simpa only [heq] using integral_phaseLogApprox_tendsto hg hC hbound hp L
  have hreal : Tendsto (fun ν => ∫ z, (phaseLogApprox ν (g z)).re * fderiv ℝ φ z w) atTop
      (𝓝 (∫ z, (if g z = 0 then (1 : ℝ) else 0) * fderiv ℝ φ z w)) := by
    simpa using ht Complex.reCLM w
  have himag : Tendsto (fun ν => ∫ z, (phaseLogApprox ν (g z)).im * fderiv ℝ φ z (Complex.I * w))
      atTop (𝓝 0) := by
    simpa using ht Complex.imCLM (Complex.I * w)
  apply le_of_tendsto_of_tendsto hreal himag
  apply Eventually.of_forall
  intro ν
  have hh := hlog (Real.exp (-phaseLogScale ν)) (Real.exp_pos _)
  simp only [phaseLogApprox, Complex.smul_re, Complex.smul_im, smul_eq_mul,
    mul_assoc, integral_const_mul]
  exact mul_le_mul_of_nonpos_left hh (neg_nonpos.mpr (inv_nonneg.mpr (phaseLogScale_pos ν).le))

end ModifiedCartan
#print axioms ModifiedCartan.phase_test_of_regularized_log_tests
