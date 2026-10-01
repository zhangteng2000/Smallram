import ModifiedCartan.WeakGradientConvolution

open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory ContinuousLinearMap
set_option autoImplicit false
namespace ModifiedCartan

/-- Positive unit-mass smoothing preserves each half-plane bound on the
actual weak complex gradient, in every real direction. -/
theorem HasWeakComplexGradient.fderiv_convolution_apply_le {U : Set ℂ} (hU : IsOpen U)
    {u v : ℂ → ℝ} {g : ℂ → ℂ} (hu : HasWeakComplexGradient U u g)
    (hv : LocallyIntegrable v) (hvu : EqOn v u U)
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχpos : ∀ z, 0 ≤ χ z) (hχone : (∫ z, χ z) = 1)
    {a : ℝ} {w : ℂ} (hg : ∀ᵐ z ∂volume.restrict U, (g z * w).re ≤ a)
    (x : ℂ) (hx : (fun z : ℂ => x - z) ⁻¹' tsupport χ ⊆ U) :
    fderiv ℝ (v ⋆[lsmul ℝ ℝ, volume] χ) x w ≤ a := by
  rw [hu.fderiv_convolution_apply hU hv hvu hχ hχc x hx w]
  let φ : ℂ → ℝ := fun z => χ (x - z)
  have hφ : Continuous φ := hχ.continuous.comp (continuous_const.sub continuous_id)
  have hφc : HasCompactSupport φ :=
    hχc.comp_homeomorph (IsometryEquiv.subLeft x).toHomeomorph
  have hφU : tsupport φ ⊆ U :=
    (tsupport_comp_subset_preimage χ (continuous_const.sub continuous_id)).trans hx
  have hi : Integrable (fun z => (g z * w).re * φ z) :=
    integrable_mul_test_of_local_integrability
      (fun K hK hKU => Complex.reCLM.integrable_comp
        ((hu.gradient_integrable K hK hKU).mul_const w)) hφ hφc hφU
  have hφi : Integrable φ := hφ.integrable_of_hasCompactSupport hφc
  have hb : ∀ᵐ z ∂volume, (g z * w).re * φ z ≤ a * φ z := by
    filter_upwards [(ae_restrict_iff' hU.measurableSet).mp hg] with z hz
    by_cases hzU : z ∈ U
    · exact mul_le_mul_of_nonneg_right (hz hzU) (hχpos (x - z))
    · have hzφ : z ∉ tsupport φ := fun hh => hzU (hφU hh)
      rw [image_eq_zero_of_notMem_tsupport hzφ, mul_zero, mul_zero]
  calc
    (∫ z, (g z * w).re * χ (x - z)) ≤ ∫ z, a * φ z := integral_mono_ae hi (hφi.const_mul a) hb
    _ = a := by
      rw [integral_const_mul]
      change a * (∫ z, χ (x - z)) = a
      rw [integral_sub_left_eq_self χ volume x, hχone, mul_one]

end ModifiedCartan
#print axioms ModifiedCartan.HasWeakComplexGradient.fderiv_convolution_apply_le
