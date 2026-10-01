import ModifiedCartan.WeakGradientCalculus

open scoped Topology ContDiff
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

theorem HasWeakComplexGradient.of_gradient_ae_zero {U : Set ℂ} (hU : IsOpen U)
    {u : ℂ → ℝ} {g : ℂ → ℂ} (h : HasWeakComplexGradient U u g)
    (hg : g =ᵐ[volume.restrict U] (fun _ => 0)) :
    HasWeakComplexGradient U u (fun _ => 0) where
  function_integrable := h.function_integrable
  gradient_integrable _ _ _ := integrableOn_zero
  test_one φ hφ hφc hφU := by
    have hre : (fun z => (g z).re) =ᵐ[volume.restrict U] (fun _ => 0) := by
      filter_upwards [hg] with z hz
      simp only [hz, Complex.zero_re]
    have he := h.test_one φ hφ hφc hφU
    rw [integral_mul_test_congr_ae hU.measurableSet hre hφU] at he
    simpa only [Complex.zero_re] using he
  test_I φ hφ hφc hφU := by
    have him : (fun z => -(g z).im) =ᵐ[volume.restrict U] (fun _ => 0) := by
      filter_upwards [hg] with z hz
      simp only [hz, Complex.zero_im, neg_zero]
    have he := h.test_I φ hφ hφc hφU
    rw [integral_mul_test_congr_ae hU.measurableSet him hφU] at he
    simpa only [Complex.zero_im, neg_zero] using he

theorem realCLM_apply_complex (L : ℂ →L[ℝ] ℝ) (v : ℂ) :
    L v = v.re * L 1 + v.im * L Complex.I := by
  have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
    simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im v).symm
  calc
    L v = L (v.re • (1 : ℂ) + v.im • Complex.I) := congrArg L hv
    _ = _ := by rw [map_add, map_smul, map_smul]; rfl

/-- A vanishing complex weak gradient annihilates test derivatives in
every real direction, not just the two defining coordinate directions. -/
theorem HasWeakComplexGradient.integral_mul_fderiv_zero {U : Set ℂ} {u : ℂ → ℝ}
    (h : HasWeakComplexGradient U u (fun _ => 0)) (φ : ℂ → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U)
    (v : ℂ) : (∫ z, u z * fderiv ℝ φ z v) = 0 := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hi (w : ℂ) : Integrable (fun z => u z * fderiv ℝ φ z w) :=
    integrable_mul_test_of_local_integrability h.function_integrable
      ((hφ1.continuous_fderiv_apply one_ne_zero).comp (continuous_id.prodMk continuous_const))
      (hφc.fderiv_apply ℝ w) ((tsupport_fderiv_apply_subset ℝ w).trans hφU)
  have h1 : (∫ z, u z * fderiv ℝ φ z 1) = 0 := by
    simpa only [Complex.zero_re, zero_mul, integral_zero, neg_zero] using h.test_one φ hφ hφc hφU
  have hI : (∫ z, u z * fderiv ℝ φ z Complex.I) = 0 := by
    simpa only [Complex.zero_im, neg_zero, zero_mul, integral_zero] using h.test_I φ hφ hφc hφU
  have he : (fun z => u z * fderiv ℝ φ z v) =
      (fun z => v.re * (u z * fderiv ℝ φ z 1) + v.im * (u z * fderiv ℝ φ z Complex.I)) := by
    funext z
    rw [realCLM_apply_complex]
    ring
  rw [he, integral_add ((hi 1).const_mul v.re) ((hi Complex.I).const_mul v.im),
    integral_const_mul, integral_const_mul, h1, hI, mul_zero, mul_zero, add_zero]

end ModifiedCartan
#print axioms ModifiedCartan.HasWeakComplexGradient.integral_mul_fderiv_zero
