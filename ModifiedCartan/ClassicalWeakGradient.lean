import ModifiedCartan.SobolevLocality
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

open scoped Topology ENNReal ContDiff
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan

/-! Classical and weak derivatives for `lem:logderivlimit`. C1 regularity is
only required on the open domain. The logarithmic modulus derivative is proved
using complex logarithms on a slit plane, switching f to -f when necessary. -/

theorem continuousOn_classicalComplexGradient {U : Set ℂ} (hU : IsOpen U)
    {u : ℂ → ℝ} (hu : ContDiffOn ℝ 1 u U) : ContinuousOn (classicalComplexGradient u) U := by
  unfold classicalComplexGradient
  have hc (v : ℂ) : ContinuousOn (fun z => fderiv ℝ u z v) U :=
    (hu.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  exact (Complex.continuous_ofReal.comp_continuousOn (hc 1)).sub
    (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn (hc Complex.I)))

theorem contDiffOn_hasWeakComplexGradient {U : Set ℂ} (hU : IsOpen U)
    {u : ℂ → ℝ} (hu : ContDiffOn ℝ 1 u U) :
    HasWeakComplexGradient U u (classicalComplexGradient u) where
  function_integrable K hK hKU := (hu.continuousOn.mono hKU).integrableOn_compact hK
  gradient_integrable K hK hKU :=
    ((continuousOn_classicalComplexGradient hU hu).mono hKU).integrableOn_compact hK
  test_one φ hφ hφc hφU := by
    simp_rw [classicalComplexGradient_re]
    exact integral_mul_test_fderiv_of_contDiffOn hU hu
      (hφ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)) hφc hφU 1
  test_I φ hφ hφc hφU := by
    simp_rw [classicalComplexGradient_neg_im]
    exact integral_mul_test_fderiv_of_contDiffOn hU hu
      (hφ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)) hφc hφU Complex.I

theorem classicalComplexGradient_re_of_hasDerivAt {f : ℂ → ℂ} {f' z : ℂ}
    (hf : HasDerivAt f f' z) : classicalComplexGradient (fun w => (f w).re) z = f' := by
  have hfd := Complex.reCLM.hasFDerivAt.comp z hf.complexToReal_fderiv
  have heq : fderiv ℝ (fun w => (f w).re) z = Complex.reCLM.comp (f' • (1 : ℂ →L[ℝ] ℂ)) := by
    exact hfd.fderiv
  simp [classicalComplexGradient, heq, Complex.ext_iff]

theorem classicalComplexGradient_log_norm {f : ℂ → ℂ} {f' z : ℂ}
    (hf : HasDerivAt f f' z) (hf0 : f z ≠ 0) :
    classicalComplexGradient (fun w => Real.log ‖f w‖) z = f' / f z := by
  rcases Complex.mem_slitPlane_or_neg_mem_slitPlane hf0 with hpos | hneg
  · have heq : (fun w => Real.log ‖f w‖) = (fun w => (Complex.log (f w)).re) := by
      funext w
      exact (Complex.log_re _).symm
    rw [heq]
    exact classicalComplexGradient_re_of_hasDerivAt (hf.clog hpos)
  · have heq : (fun w => Real.log ‖f w‖) = (fun w => (Complex.log (-f w)).re) := by
      funext w
      simp only [Complex.log_re, norm_neg]
    rw [heq]
    simpa only [Pi.neg_apply, neg_div_neg_eq] using classicalComplexGradient_re_of_hasDerivAt (hf.neg.clog hneg)

theorem HasWeakComplexGradient.const_mul {U : Set ℂ} {u : ℂ → ℝ} {g : ℂ → ℂ}
    (hu : HasWeakComplexGradient U u g) (r : ℝ) :
    HasWeakComplexGradient U (fun z => r * u z) (fun z => r • g z) where
  function_integrable K hK hKU := (hu.function_integrable K hK hKU).const_mul r
  gradient_integrable K hK hKU := Integrable.smul r (hu.gradient_integrable K hK hKU)
  test_one φ hφ hφc hφU := by
    simp only [Complex.smul_re, smul_eq_mul]
    simp_rw [mul_assoc, integral_const_mul, hu.test_one φ hφ hφc hφU]
    ring
  test_I φ hφ hφc hφU := by
    simp only [Complex.smul_im, smul_eq_mul]
    simp_rw [neg_mul_eq_mul_neg, mul_assoc, integral_const_mul, hu.test_I φ hφ hφc hφU]
    ring





end ModifiedCartan


