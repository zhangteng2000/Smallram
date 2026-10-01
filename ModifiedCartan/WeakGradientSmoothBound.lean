import ModifiedCartan.WeakGradientConvolution
import Mathlib.Analysis.Calculus.MeanValue

open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory ContinuousLinearMap
set_option autoImplicit false
namespace ModifiedCartan

/-- A positive unit-mass smoothing preserves the bound on the actual weak
gradient. The function may be cut off outside the region used by the kernel. -/
theorem HasWeakComplexGradient.norm_fderiv_convolution_le {U : Set ℂ} (hU : IsOpen U)
    {u v : ℂ → ℝ} {g : ℂ → ℂ} (hu : HasWeakComplexGradient U u g)
    (hv : LocallyIntegrable v) (hvu : EqOn v u U)
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχpos : ∀ z, 0 ≤ χ z) (hχone : (∫ z, χ z) = 1)
    {C : ℝ} (hC : 0 ≤ C) (hg : ∀ᵐ z ∂volume.restrict U, ‖g z‖ ≤ C)
    (x : ℂ) (hx : (fun z : ℂ => x - z) ⁻¹' tsupport χ ⊆ U) :
    ‖fderiv ℝ (v ⋆[lsmul ℝ ℝ, volume] χ) x‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro w
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
  have hb : ∀ᵐ z ∂volume, ‖(g z * w).re * φ z‖ ≤ (C * ‖w‖) * φ z := by
    filter_upwards [(ae_restrict_iff' hU.measurableSet).mp hg] with z hz
    by_cases hzU : z ∈ U
    · have hh : ‖(g z * w).re‖ ≤ C * ‖w‖ := by
        calc
          ‖(g z * w).re‖ = |(g z * w).re| := Real.norm_eq_abs _
          _ ≤ ‖g z * w‖ := Complex.abs_re_le_norm _
          _ = ‖g z‖ * ‖w‖ := norm_mul _ _
          _ ≤ C * ‖w‖ := mul_le_mul_of_nonneg_right (hz hzU) (norm_nonneg _)
      rw [norm_mul, Real.norm_eq_abs (φ z), abs_of_nonneg (show 0 ≤ φ z from hχpos (x - z))]
      exact mul_le_mul_of_nonneg_right hh (hχpos (x - z))
    · have hzφ : z ∉ tsupport φ := fun hh => hzU (hφU hh)
      rw [image_eq_zero_of_notMem_tsupport hzφ, mul_zero, norm_zero, mul_zero]
  calc
    ‖∫ z, (g z * w).re * χ (x - z)‖ ≤ ∫ z, ‖(g z * w).re * φ z‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ z, (C * ‖w‖) * φ z := integral_mono_ae hi.norm (hφi.const_mul _) hb
    _ = C * ‖w‖ := by
      rw [integral_const_mul]
      change (C * ‖w‖) * (∫ z, χ (x - z)) = _
      rw [integral_sub_left_eq_self χ volume x, hχone, mul_one]

end ModifiedCartan
#print axioms ModifiedCartan.HasWeakComplexGradient.norm_fderiv_convolution_le
