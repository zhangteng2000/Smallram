import ModifiedCartan.LogKernelDerivative

open scoped Topology ENNReal
open Filter MeasureTheory Set Metric

namespace ModifiedCartan

/-! Distributional first derivatives of logarithmic potentials, used in
`lem:logderivlimit`. Joint integrability of the kernels multiplied by compact
continuous tests justifies every application of Fubini. The conclusion applies
to all finite measures supported on a compact set, including atomic measures. -/

theorem integrable_prod_cappedLogKernel_mul_test (ν : Measure ℂ) [IsFiniteMeasure ν]
    {L : ℝ} (hL : 1 ≤ L) {ψ : ℂ → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) :
    Integrable (fun x : ℂ × ℂ => cappedLogKernel L (x.2 - x.1) * ψ x.2)
      (ν.prod volume) := by
  obtain ⟨C, hC⟩ := hψc.exists_bound_of_continuous hψ
  have hm : AEStronglyMeasurable (fun x : ℂ × ℂ => ψ x.2) (ν.prod volume) :=
    (hψ.comp continuous_snd).aestronglyMeasurable
  have herr := (integrable_prod_cappedLog_error ν zero_lt_one le_rfl hL).mul_bdd hm
    (Eventually.of_forall fun x => hC x.2)
  have hψi := (hψ.integrable_of_hasCompactSupport (μ := volume) hψc).comp_snd ν
  have hreg := hψi.bdd_mul
    (((continuous_logRegularization zero_lt_one L).comp
      (continuous_snd.sub continuous_fst)).aestronglyMeasurable)
    (Eventually.of_forall fun x => norm_logRegularization_le zero_lt_one hL (x.2 - x.1))
  convert! herr.fun_add hreg using 1
  ext x
  dsimp only [Function.comp_def, Pi.sub_apply]
  ring

theorem integrable_prod_logKernel_mul_test (ν : Measure ℂ) [IsFiniteMeasure ν]
    {S : Set ℂ} (hS : IsCompact S) (hsupp : ∀ᵐ a ∂ν, a ∈ S)
    {ψ : ℂ → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    Integrable (fun x : ℂ × ℂ => Real.log ‖x.2 - x.1‖ * ψ x.2)
      (ν.prod volume) := by
  obtain ⟨L, hL, hbound⟩ := exists_log_cap_of_compact hψc hS
  apply (integrable_prod_cappedLogKernel_mul_test ν hL hψ hψc).congr
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := ν) (ν := volume)).tendsto_ae hsupp] with x hx
  by_cases hψ0 : ψ x.2 = 0
  · simp only [hψ0, mul_zero]
  · have hmem : x.2 ∈ tsupport ψ := subset_closure hψ0
    simp only [cappedLogKernel, min_eq_right (hbound x.2 hmem x.1 hx)]

theorem integrable_prod_test_smul_cauchyKernel (ν : Measure ℂ) [IsFiniteMeasure ν]
    {ψ : ℂ → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    Integrable (fun x : ℂ × ℂ => ψ x.2 • (x.2 - x.1)⁻¹) (ν.prod volume) := by
  obtain ⟨C, hC⟩ := hψc.exists_bound_of_continuous hψ
  have hm : AEStronglyMeasurable (fun x : ℂ × ℂ => ψ x.2) (ν.prod volume) :=
    (hψ.comp continuous_snd).aestronglyMeasurable
  have he : Integrable (fun x : ℂ × ℂ =>
      (x.2 - x.1)⁻¹ - cauchyRegularization 1 (x.2 - x.1)) (ν.prod volume) := by
    apply ((integrable_prod_nearCauchyKernel ν (R := 1) zero_le_one).smul (2 : ℝ)).mono
      (measurable_cauchyRegularization_error zero_lt_one).aestronglyMeasurable
    exact Eventually.of_forall fun x => norm_cauchyRegularization_error_le zero_lt_one x.1 x.2
  have herr := he.bdd_smul C hm (Eventually.of_forall fun x => hC x.2)
  have hψi := (hψ.integrable_of_hasCompactSupport (μ := volume) hψc).comp_snd ν
  have hreg := hψi.smul_bdd 1
    (((continuous_cauchyRegularization zero_lt_one).comp
      (continuous_snd.sub continuous_fst)).aestronglyMeasurable)
    (Eventually.of_forall fun x => by
      simpa only [Function.comp_def, Pi.sub_apply, inv_one] using norm_cauchyRegularization_le zero_lt_one (x.2 - x.1))
  convert! herr.fun_add hreg using 1
  ext x
  change ψ x.2 • (x.2 - x.1)⁻¹ =
    ψ x.2 • ((x.2 - x.1)⁻¹ - cauchyRegularization 1 (x.2 - x.1)) +
      ψ x.2 • cauchyRegularization 1 (x.2 - x.1)
  rw [smul_sub, sub_add_cancel]

theorem integral_logPotential_mul_test_eq (ν : Measure ℂ) [IsFiniteMeasure ν]
    {S : Set ℂ} (hS : IsCompact S) (hsupp : ∀ᵐ a ∂ν, a ∈ S)
    {ψ : ℂ → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    (∫ z : ℂ, logPotential ν z * ψ z) =
      ∫ a, (∫ z : ℂ, Real.log ‖z - a‖ * ψ z) ∂ν := by
  calc
    _ = ∫ z : ℂ, ∫ a, Real.log ‖z - a‖ * ψ z ∂ν := by
      simp only [integral_mul_const, logPotential]
    _ = _ := (integral_integral_swap
      (integrable_prod_logKernel_mul_test ν hS hsupp hψ hψc)).symm

theorem integral_cauchyTransform_clm_mul_test_eq (ν : Measure ℂ) [IsFiniteMeasure ν]
    (L : ℂ →L[ℝ] ℝ) {ψ : ℂ → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    (∫ z : ℂ, L (cauchyTransform ν z) * ψ z) =
      ∫ a, (∫ z : ℂ, L ((z - a)⁻¹) * ψ z) ∂ν := by
  have hi : Integrable (fun x : ℂ × ℂ => L ((x.2 - x.1)⁻¹) * ψ x.2)
      (ν.prod volume) := by
    simpa only [map_smul, smul_eq_mul, mul_comm] using
      L.integrable_comp (integrable_prod_test_smul_cauchyKernel ν hψ hψc)
  calc
    _ = ∫ z : ℂ, ∫ a, L ((z - a)⁻¹) * ψ z ∂ν := by
      apply integral_congr_ae
      filter_upwards [ae_integrable_cauchyKernel ν] with z hz
      rw [integral_mul_const, L.integral_comp_comm hz]
      rfl
    _ = _ := (integral_integral_swap hi).symm

theorem integral_logPotential_mul_fderiv_one (ν : Measure ℂ) [IsFiniteMeasure ν]
    {S : Set ℂ} (hS : IsCompact S) (hsupp : ∀ᵐ a ∂ν, a ∈ S)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) :
    (∫ z : ℂ, logPotential ν z * fderiv ℝ φ z 1) =
      -(∫ z : ℂ, (cauchyTransform ν z).re * φ z) := by
  rw [integral_logPotential_mul_test_eq ν hS hsupp (ψ := fun z => fderiv ℝ φ z 1)
    ((hφ.continuous_fderiv_apply one_ne_zero).comp (continuous_id.prodMk continuous_const))
    (hφc.fderiv_apply ℝ 1)]
  simp_rw [integral_logKernel_mul_fderiv_one _ hφ hφc]
  rw [integral_neg]
  congr 1
  exact (integral_cauchyTransform_clm_mul_test_eq ν Complex.reCLM hφ.continuous hφc).symm

theorem integral_logPotential_mul_fderiv_I (ν : Measure ℂ) [IsFiniteMeasure ν]
    {S : Set ℂ} (hS : IsCompact S) (hsupp : ∀ᵐ a ∂ν, a ∈ S)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) :
    (∫ z : ℂ, logPotential ν z * fderiv ℝ φ z Complex.I) =
      -(∫ z : ℂ, (-(cauchyTransform ν z).im) * φ z) := by
  rw [integral_logPotential_mul_test_eq ν hS hsupp (ψ := fun z => fderiv ℝ φ z Complex.I)
    ((hφ.continuous_fderiv_apply one_ne_zero).comp (continuous_id.prodMk continuous_const))
    (hφc.fderiv_apply ℝ Complex.I)]
  simp_rw [integral_logKernel_mul_fderiv_I _ hφ hφc]
  rw [integral_neg]
  congr 1
  exact (integral_cauchyTransform_clm_mul_test_eq ν (-Complex.imCLM) hφ.continuous hφc).symm


end ModifiedCartan





