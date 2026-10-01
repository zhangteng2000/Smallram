import ModifiedCartan.WeakGradientCalculus
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

open scoped Topology ENNReal ContDiff
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan

/-! Uniqueness of the distributional complex gradient on an open domain, for
`lem:logderivlimit`. The two real coordinates are separated by smooth compact
tests using mathlib's proved fundamental lemma of distributions. -/

theorem HasWeakComplexGradient.unique {U : Set ℂ} (hU : IsOpen U)
    {u : ℂ → ℝ} {g h : ℂ → ℂ}
    (hg : HasWeakComplexGradient U u g) (hh : HasWeakComplexGradient U u h) :
    g =ᵐ[volume.restrict U] h := by
  have hre : ∀ᵐ z ∂volume, z ∈ U → (g z).re - (h z).re = 0 := by
    apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    · apply (locallyIntegrableOn_iff hU.isLocallyClosed).mpr
      intro K hKU hK
      exact (Complex.reCLM.integrable_comp (hg.gradient_integrable K hK hKU)).sub
        (Complex.reCLM.integrable_comp (hh.gradient_integrable K hK hKU))
    · intro φ hφ hφc hφU
      have hig := integrable_mul_test_of_local_integrability
        (fun K hK hKU => Complex.reCLM.integrable_comp (hg.gradient_integrable K hK hKU))
        hφ.continuous hφc hφU
      have hih := integrable_mul_test_of_local_integrability
        (fun K hK hKU => Complex.reCLM.integrable_comp (hh.gradient_integrable K hK hKU))
        hφ.continuous hφc hφU
      change Integrable (fun z => (g z).re * φ z) at hig
      change Integrable (fun z => (h z).re * φ z) at hih
      have heq : (∫ z, (g z).re * φ z) = ∫ z, (h z).re * φ z := by
        linarith [hg.test_one φ hφ hφc hφU, hh.test_one φ hφ hφc hφU]
      simpa only [smul_eq_mul, mul_sub, mul_comm] using
        (integral_sub hig hih).trans (sub_eq_zero.mpr heq)
  have him : ∀ᵐ z ∂volume, z ∈ U → (-(g z).im) - (-(h z).im) = 0 := by
    apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    · apply (locallyIntegrableOn_iff hU.isLocallyClosed).mpr
      intro K hKU hK
      exact ((-Complex.imCLM).integrable_comp (hg.gradient_integrable K hK hKU)).sub
        ((-Complex.imCLM).integrable_comp (hh.gradient_integrable K hK hKU))
    · intro φ hφ hφc hφU
      have hig := integrable_mul_test_of_local_integrability
        (fun K hK hKU => (-Complex.imCLM).integrable_comp (hg.gradient_integrable K hK hKU))
        hφ.continuous hφc hφU
      have hih := integrable_mul_test_of_local_integrability
        (fun K hK hKU => (-Complex.imCLM).integrable_comp (hh.gradient_integrable K hK hKU))
        hφ.continuous hφc hφU
      change Integrable (fun z => -(g z).im * φ z) at hig
      change Integrable (fun z => -(h z).im * φ z) at hih
      have heq : (∫ z, -(g z).im * φ z) = ∫ z, -(h z).im * φ z := by
        linarith [hg.test_I φ hφ hφc hφU, hh.test_I φ hφ hφc hφU]
      simpa only [smul_eq_mul, mul_sub, mul_comm] using
        (integral_sub hig hih).trans (sub_eq_zero.mpr heq)
  apply (ae_restrict_iff' hU.measurableSet).mpr
  filter_upwards [hre, him] with z hzre hzim hzU
  apply Complex.ext
  · exact sub_eq_zero.mp (hzre hzU)
  · linarith [hzim hzU]



end ModifiedCartan


