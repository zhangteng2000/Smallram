import ModifiedCartan.WeakGradientZeroTests

open scoped Topology ContDiff
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- Integration by parts for the actual weak gradient in every real direction. -/
theorem HasWeakComplexGradient.integral_mul_fderiv {U : Set ℂ}
    {u : ℂ → ℝ} {g : ℂ → ℂ} (h : HasWeakComplexGradient U u g)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (w : ℂ) :
    (∫ z, u z * fderiv ℝ φ z w) = -(∫ z, (g z * w).re * φ z) := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hi (a : ℂ) : Integrable (fun z => u z * fderiv ℝ φ z a) :=
    integrable_mul_test_of_local_integrability h.function_integrable
      ((hφ1.continuous_fderiv_apply one_ne_zero).comp (continuous_id.prodMk continuous_const))
      (hφc.fderiv_apply ℝ a) ((tsupport_fderiv_apply_subset ℝ a).trans hφU)
  have hir : Integrable (fun z => (g z).re * φ z) :=
    integrable_mul_test_of_local_integrability
      (fun K hK hKU => Complex.reCLM.integrable_comp (h.gradient_integrable K hK hKU))
      hφ.continuous hφc hφU
  have hii : Integrable (fun z => -(g z).im * φ z) :=
    integrable_mul_test_of_local_integrability
      (fun K hK hKU => (-Complex.imCLM).integrable_comp (h.gradient_integrable K hK hKU))
      hφ.continuous hφc hφU
  have hleft : (∫ z, u z * fderiv ℝ φ z w) =
      w.re * (∫ z, u z * fderiv ℝ φ z 1) +
      w.im * (∫ z, u z * fderiv ℝ φ z Complex.I) := by
    have he (z : ℂ) : u z * fderiv ℝ φ z w =
        w.re * (u z * fderiv ℝ φ z 1) +
        w.im * (u z * fderiv ℝ φ z Complex.I) := by
      rw [realCLM_apply_complex]
      ring
    simp_rw [he]
    rw [integral_add ((hi 1).const_mul w.re) ((hi Complex.I).const_mul w.im),
      integral_const_mul, integral_const_mul]
  have hright : (∫ z, (g z * w).re * φ z) =
      w.re * (∫ z, (g z).re * φ z) + w.im * (∫ z, -(g z).im * φ z) := by
    have he (z : ℂ) : (g z * w).re * φ z =
        w.re * ((g z).re * φ z) + w.im * (-(g z).im * φ z) := by
      rw [Complex.mul_re]
      ring
    simp_rw [he]
    rw [integral_add (hir.const_mul w.re) (hii.const_mul w.im),
      integral_const_mul, integral_const_mul]
  rw [hleft, hright, h.test_one φ hφ hφc hφU, h.test_I φ hφ hφc hφU]
  ring

end ModifiedCartan
#print axioms ModifiedCartan.HasWeakComplexGradient.integral_mul_fderiv
