import ModifiedCartan.LogPotentialDerivative
import ModifiedCartan.LogPotentialLp

open scoped Topology ENNReal ContDiff
open Filter MeasureTheory Set Metric

namespace ModifiedCartan

/-! Literal distributional gradients and local Sobolev membership for
`lem:logderivlimit`. Smooth compactly supported tests define the weak derivatives;
the potential Sobolev theorem is proved, and weak gradients are closed under
local L1 convergence of both functions and gradients. -/

/-- The complex encoding `g = ∂ₓu - I ∂ᵧu` of the distributional gradient.
Tests are smooth and compactly supported in the stated domain. -/
structure HasWeakComplexGradient (U : Set ℂ) (u : ℂ → ℝ) (g : ℂ → ℂ) : Prop where
  function_integrable : ∀ K, IsCompact K → K ⊆ U → IntegrableOn u K
  gradient_integrable : ∀ K, IsCompact K → K ⊆ U → IntegrableOn g K
  test_one : ∀ (φ : ℂ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
    (∫ z, u z * fderiv ℝ φ z 1) = -(∫ z, (g z).re * φ z)
  test_I : ∀ (φ : ℂ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
    (∫ z, u z * fderiv ℝ φ z Complex.I) = -(∫ z, (-(g z).im) * φ z)

/-- Local W¹ᵖ membership using the literal weak first derivatives. -/
def MemW1pLoc (p : ℝ≥0∞) (U : Set ℂ) (u : ℂ → ℝ) : Prop :=
  ∃ g : ℂ → ℂ, HasWeakComplexGradient U u g ∧
    (∀ K, IsCompact K → K ⊆ U → MemLp u p (volume.restrict K)) ∧
    (∀ K, IsCompact K → K ⊆ U → MemLp g p (volume.restrict K))

theorem HasWeakComplexGradient.restrict {U V : Set ℂ} {u : ℂ → ℝ} {g : ℂ → ℂ}
    (h : HasWeakComplexGradient U u g) (hVU : V ⊆ U) : HasWeakComplexGradient V u g where
  function_integrable K hK hKV := h.function_integrable K hK (hKV.trans hVU)
  gradient_integrable K hK hKV := h.gradient_integrable K hK (hKV.trans hVU)
  test_one φ hφ hφc hφV := h.test_one φ hφ hφc (hφV.trans hVU)
  test_I φ hφ hφc hφV := h.test_I φ hφ hφc (hφV.trans hVU)

theorem logPotential_hasWeakComplexGradient (ν : Measure ℂ) [IsFiniteMeasure ν]
    {S : Set ℂ} (hS : IsCompact S) (hsupp : ∀ᵐ a ∂ν, a ∈ S) (U : Set ℂ) :
    HasWeakComplexGradient U (logPotential ν) (cauchyTransform ν) where
  function_integrable K hK _ := memLp_one_iff_integrable.mp
    (memLp_logPotential_on_compact ν hS hsupp hK)
  gradient_integrable K hK _ := by
    have h := memLp_cauchyTransform_on_compact ν (p := 1) le_rfl (by norm_num) hK
    simpa only [IntegrableOn, ENNReal.ofReal_one, memLp_one_iff_integrable] using h
  test_one φ hφ hφc _ :=
    integral_logPotential_mul_fderiv_one ν hS hsupp (hφ.of_le (by norm_num)) hφc
  test_I φ hφ hφc _ :=
    integral_logPotential_mul_fderiv_I ν hS hsupp (hφ.of_le (by norm_num)) hφc

theorem logPotential_memW1pLoc (ν : Measure ℂ) [IsFiniteMeasure ν]
    {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p < 2) {S : Set ℂ}
    (hS : IsCompact S) (hsupp : ∀ᵐ a ∂ν, a ∈ S) (U : Set ℂ) :
    MemW1pLoc (ENNReal.ofReal p) U (logPotential ν) := by
  refine ⟨cauchyTransform ν, logPotential_hasWeakComplexGradient ν hS hsupp U, ?_, ?_⟩
  · intro K hK _
    exact memLp_logPotential_of_one_le ν hp1 hS hsupp hK
  · intro K hK _
    exact memLp_cauchyTransform_on_compact ν hp1 hp2 hK

theorem LocalLpConvergence.clm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞} {U : Set ℂ}
    {f : ℕ → ℂ → E} {u : ℂ → E} (h : LocalLpConvergence p U f u) (L : E →L[ℝ] F) :
    LocalLpConvergence p U (fun n z => L (f n z)) (fun z => L (u z)) where
  source_mem K hK hKU n := L.comp_memLp' (h.source_mem K hK hKU n)
  limit_mem K hK hKU := L.comp_memLp' (h.limit_mem K hK hKU)
  tendsto K hK hKU := by
    have hlim : Tendsto (fun n => ENNReal.ofReal ‖L‖ * eLpNorm (f n - u) p (volume.restrict K))
        atTop (𝓝 0) := by
      simpa only [mul_zero] using ENNReal.Tendsto.const_mul (h.tendsto K hK hKU)
        (Or.inr ENNReal.ofReal_ne_top : (0 : ℝ≥0∞) ≠ 0 ∨ ENNReal.ofReal ‖L‖ ≠ ⊤)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le)
    intro n
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    exact Eventually.of_forall fun z => by
      simpa only [Pi.sub_apply, ← map_sub] using L.le_opNorm (f n z - u z)

theorem HasWeakComplexGradient.of_localL1_limit {U : Set ℂ}
    {u : ℕ → ℂ → ℝ} {u₀ : ℂ → ℝ} {g : ℕ → ℂ → ℂ} {g₀ : ℂ → ℂ}
    (hu : LocalLpConvergence 1 U u u₀) (hg : LocalLpConvergence 1 U g g₀)
    (hw : ∀ n, HasWeakComplexGradient U (u n) (g n)) :
    HasWeakComplexGradient U u₀ g₀ where
  function_integrable K hK hKU := memLp_one_iff_integrable.mp (hu.limit_mem K hK hKU)
  gradient_integrable K hK hKU := memLp_one_iff_integrable.mp (hg.limit_mem K hK hKU)
  test_one φ hφ hφc hφU := by
    have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
    have huφ : Tendsto (fun n => ∫ z, u n z * fderiv ℝ φ z 1) atTop
        (𝓝 (∫ z, u₀ z * fderiv ℝ φ z 1)) := by
      simpa only [mul_comm] using hu.compactlySupported_test_integral
        (φ := fun z => fderiv ℝ φ z 1)
        ((hφ1.continuous_fderiv_apply one_ne_zero).comp (continuous_id.prodMk continuous_const))
        (hφc.fderiv_apply ℝ 1) ((tsupport_fderiv_apply_subset ℝ 1).trans hφU)
    have hgφ : Tendsto (fun n => -(∫ z, (g n z).re * φ z)) atTop
        (𝓝 (-(∫ z, (g₀ z).re * φ z))) := by
      simpa [mul_comm] using
        ((hg.clm Complex.reCLM).compactlySupported_test_integral hφ.continuous hφc hφU).neg
    have heq : (fun n => ∫ z, u n z * fderiv ℝ φ z 1) =
        (fun n => -(∫ z, (g n z).re * φ z)) :=
      funext fun n => (hw n).test_one φ hφ hφc hφU
    rw [heq] at huφ
    exact tendsto_nhds_unique huφ hgφ
  test_I φ hφ hφc hφU := by
    have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
    have huφ : Tendsto (fun n => ∫ z, u n z * fderiv ℝ φ z Complex.I) atTop
        (𝓝 (∫ z, u₀ z * fderiv ℝ φ z Complex.I)) := by
      simpa only [mul_comm] using hu.compactlySupported_test_integral
        (φ := fun z => fderiv ℝ φ z Complex.I)
        ((hφ1.continuous_fderiv_apply one_ne_zero).comp (continuous_id.prodMk continuous_const))
        (hφc.fderiv_apply ℝ Complex.I) ((tsupport_fderiv_apply_subset ℝ Complex.I).trans hφU)
    have hgφ : Tendsto (fun n => -(∫ z, (-(g n z).im) * φ z)) atTop
        (𝓝 (-(∫ z, (-(g₀ z).im) * φ z))) := by
      simpa [mul_comm] using
        ((hg.clm (-Complex.imCLM)).compactlySupported_test_integral hφ.continuous hφc hφU).neg
    have heq : (fun n => ∫ z, u n z * fderiv ℝ φ z Complex.I) =
        (fun n => -(∫ z, (-(g n z).im) * φ z)) :=
      funext fun n => (hw n).test_I φ hφ hφc hφU
    rw [heq] at huφ
    exact tendsto_nhds_unique huφ hgφ


end ModifiedCartan



