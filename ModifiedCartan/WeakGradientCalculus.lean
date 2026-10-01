import ModifiedCartan.HarmonicWeak
import ModifiedCartan.WeakGradient

open scoped Topology ENNReal ContDiff
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan

/-! Weak-gradient calculus for `lem:logderivlimit`: C1 functions, sums, and
almost-everywhere representatives. Test product integrability is proved before
using linearity of the integral. -/

theorem memLp_on_compact_of_continuous {E : Type*} [NormedAddCommGroup E]
    {f : ℂ → E} (hf : Continuous f) {K : Set ℂ} (hK : IsCompact K) (p : ℝ≥0∞) :
    MemLp f p (volume.restrict K) := by
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  obtain ⟨M, hM⟩ := (hK.image hf).isBounded.exists_norm_le
  apply MemLp.of_bound hf.aestronglyMeasurable M
  filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
  exact hM _ (mem_image_of_mem f hz)

theorem integrable_mul_test_of_local_integrability {U : Set ℂ} {u φ : ℂ → ℝ}
    (hu : ∀ K, IsCompact K → K ⊆ U → IntegrableOn u K)
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    Integrable (fun z => u z * φ z) := by
  have hi : Integrable ((tsupport φ).indicator u) :=
    IntegrableOn.integrable_indicator (hu _ hφc hφU) hφc.measurableSet
  obtain ⟨M, hM⟩ := hφc.exists_bound_of_continuous hφ
  have heq : (fun z => (tsupport φ).indicator u z * φ z) = (fun z => u z * φ z) := by
    funext z
    by_cases hz : z ∈ tsupport φ
    · rw [indicator_of_mem hz]
    · rw [image_eq_zero_of_notMem_tsupport hz, mul_zero, mul_zero]
  rw [← heq]
  exact hi.mul_bdd hφ.aestronglyMeasurable (Eventually.of_forall hM)

theorem integral_mul_test_congr_ae {U : Set ℂ} (hU : MeasurableSet U) {u v φ : ℂ → ℝ}
    (huv : u =ᵐ[volume.restrict U] v) (hφU : tsupport φ ⊆ U) :
    (∫ z, u z * φ z) = ∫ z, v z * φ z := by
  apply integral_congr_ae
  filter_upwards [(ae_restrict_iff' hU).mp huv] with z hz
  by_cases hzU : z ∈ U
  · rw [hz hzU]
  · have hzφ : z ∉ tsupport φ := fun hh => hzU (hφU hh)
    rw [image_eq_zero_of_notMem_tsupport hzφ, mul_zero, mul_zero]

theorem HasWeakComplexGradient.congr_function_ae {U : Set ℂ} (hU : IsOpen U)
    {u v : ℂ → ℝ} {g : ℂ → ℂ} (h : HasWeakComplexGradient U u g)
    (huv : u =ᵐ[volume.restrict U] v) : HasWeakComplexGradient U v g where
  function_integrable K hK hKU := (h.function_integrable K hK hKU).congr
    (huv.filter_mono (ae_mono (Measure.restrict_mono_set _ hKU)))
  gradient_integrable := h.gradient_integrable
  test_one φ hφ hφc hφU := by
    rw [integral_mul_test_congr_ae hU.measurableSet huv.symm
      ((tsupport_fderiv_apply_subset ℝ 1).trans hφU)]
    exact h.test_one φ hφ hφc hφU
  test_I φ hφ hφc hφU := by
    rw [integral_mul_test_congr_ae hU.measurableSet huv.symm
      ((tsupport_fderiv_apply_subset ℝ Complex.I).trans hφU)]
    exact h.test_I φ hφ hφc hφU

noncomputable def classicalComplexGradient (u : ℂ → ℝ) (z : ℂ) : ℂ :=
  (fderiv ℝ u z 1 : ℂ) - Complex.I * (fderiv ℝ u z Complex.I : ℂ)

theorem classicalComplexGradient_re (u : ℂ → ℝ) (z : ℂ) :
    (classicalComplexGradient u z).re = fderiv ℝ u z 1 := by
  simp [classicalComplexGradient]

theorem classicalComplexGradient_neg_im (u : ℂ → ℝ) (z : ℂ) :
    -(classicalComplexGradient u z).im = fderiv ℝ u z Complex.I := by
  simp [classicalComplexGradient]

theorem continuous_classicalComplexGradient {u : ℂ → ℝ} (hu : ContDiff ℝ 1 u) :
    Continuous (classicalComplexGradient u) := by
  unfold classicalComplexGradient
  have hc (v : ℂ) : Continuous (fun z => fderiv ℝ u z v) :=
    (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const
  exact (Complex.continuous_ofReal.comp (hc 1)).sub
    (continuous_const.mul (Complex.continuous_ofReal.comp (hc Complex.I)))

theorem contDiff_hasWeakComplexGradient {u : ℂ → ℝ} (hu : ContDiff ℝ 1 u) (U : Set ℂ) :
    HasWeakComplexGradient U u (classicalComplexGradient u) where
  function_integrable K hK _ := hu.continuous.continuousOn.integrableOn_compact hK
  gradient_integrable K hK _ :=
    (continuous_classicalComplexGradient hu).continuousOn.integrableOn_compact hK
  test_one φ hφ hφc _ := by
    simp_rw [classicalComplexGradient_re]
    exact integral_mul_test_fderiv_of_contDiffOn isOpen_univ hu.contDiffOn
      (hφ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)) hφc (subset_univ _) 1
  test_I φ hφ hφc _ := by
    simp_rw [classicalComplexGradient_neg_im]
    exact integral_mul_test_fderiv_of_contDiffOn isOpen_univ hu.contDiffOn
      (hφ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)) hφc (subset_univ _) Complex.I

theorem contDiff_memW1pLoc {u : ℂ → ℝ} (hu : ContDiff ℝ 1 u) (p : ℝ≥0∞) (U : Set ℂ) :
    MemW1pLoc p U u :=
  ⟨classicalComplexGradient u, contDiff_hasWeakComplexGradient hu U,
    fun _ hK _ => memLp_on_compact_of_continuous hu.continuous hK p,
    fun _ hK _ => memLp_on_compact_of_continuous (continuous_classicalComplexGradient hu) hK p⟩

theorem MemW1pLoc.congr_ae {p : ℝ≥0∞} {U : Set ℂ} (hU : IsOpen U) {u v : ℂ → ℝ}
    (hu : MemW1pLoc p U u) (huv : u =ᵐ[volume.restrict U] v) : MemW1pLoc p U v := by
  obtain ⟨g, hg, humem, hgmem⟩ := hu
  refine ⟨g, hg.congr_function_ae hU huv, ?_, hgmem⟩
  intro K hK hKU
  exact (memLp_congr_ae (huv.filter_mono (ae_mono (Measure.restrict_mono_set _ hKU)))).mp
    (humem K hK hKU)

theorem HasWeakComplexGradient.add {U : Set ℂ} {u v : ℂ → ℝ} {g h : ℂ → ℂ}
    (hu : HasWeakComplexGradient U u g) (hv : HasWeakComplexGradient U v h) :
    HasWeakComplexGradient U (u + v) (g + h) where
  function_integrable K hK hKU := (hu.function_integrable K hK hKU).add
    (hv.function_integrable K hK hKU)
  gradient_integrable K hK hKU := (hu.gradient_integrable K hK hKU).add
    (hv.gradient_integrable K hK hKU)
  test_one φ hφ hφc hφU := by
    have hφ1 := hφ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)
    have hiu := integrable_mul_test_of_local_integrability hu.function_integrable
      ((hφ1.continuous_fderiv one_ne_zero).clm_apply continuous_const)
      (hφc.fderiv_apply ℝ 1) ((tsupport_fderiv_apply_subset ℝ 1).trans hφU)
    have hiv := integrable_mul_test_of_local_integrability hv.function_integrable
      ((hφ1.continuous_fderiv one_ne_zero).clm_apply continuous_const)
      (hφc.fderiv_apply ℝ 1) ((tsupport_fderiv_apply_subset ℝ 1).trans hφU)
    have hig := integrable_mul_test_of_local_integrability
      (fun K hK hKU => Complex.reCLM.integrable_comp (hu.gradient_integrable K hK hKU))
      hφ.continuous hφc hφU
    have hih := integrable_mul_test_of_local_integrability
      (fun K hK hKU => Complex.reCLM.integrable_comp (hv.gradient_integrable K hK hKU))
      hφ.continuous hφc hφU
    change Integrable (fun z => (g z).re * φ z) at hig
    change Integrable (fun z => (h z).re * φ z) at hih
    simp only [Pi.add_apply, Complex.add_re, add_mul]
    rw [integral_add hiu hiv, integral_add hig hih,
      hu.test_one φ hφ hφc hφU, hv.test_one φ hφ hφc hφU]
    ring
  test_I φ hφ hφc hφU := by
    have hφ1 := hφ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)
    have hiu := integrable_mul_test_of_local_integrability hu.function_integrable
      ((hφ1.continuous_fderiv one_ne_zero).clm_apply continuous_const)
      (hφc.fderiv_apply ℝ Complex.I) ((tsupport_fderiv_apply_subset ℝ Complex.I).trans hφU)
    have hiv := integrable_mul_test_of_local_integrability hv.function_integrable
      ((hφ1.continuous_fderiv one_ne_zero).clm_apply continuous_const)
      (hφc.fderiv_apply ℝ Complex.I) ((tsupport_fderiv_apply_subset ℝ Complex.I).trans hφU)
    have hig := integrable_mul_test_of_local_integrability
      (fun K hK hKU => (-Complex.imCLM).integrable_comp (hu.gradient_integrable K hK hKU))
      hφ.continuous hφc hφU
    have hih := integrable_mul_test_of_local_integrability
      (fun K hK hKU => (-Complex.imCLM).integrable_comp (hv.gradient_integrable K hK hKU))
      hφ.continuous hφc hφU
    change Integrable (fun z => -(g z).im * φ z) at hig
    change Integrable (fun z => -(h z).im * φ z) at hih
    simp only [Pi.add_apply, Complex.add_im, neg_add_rev, add_mul]
    rw [integral_add hiu hiv, integral_add hih hig,
      hu.test_I φ hφ hφc hφU, hv.test_I φ hφ hφc hφU]
    ring

theorem MemW1pLoc.add {p : ℝ≥0∞} {U : Set ℂ} {u v : ℂ → ℝ}
    (hu : MemW1pLoc p U u) (hv : MemW1pLoc p U v) : MemW1pLoc p U (u + v) := by
  obtain ⟨g, hg, humem, hgmem⟩ := hu
  obtain ⟨h, hh, hvmem, hhmem⟩ := hv
  exact ⟨g + h, hg.add hh, fun K hK hKU => (humem K hK hKU).add (hvmem K hK hKU),
    fun K hK hKU => (hgmem K hK hKU).add (hhmem K hK hKU)⟩





end ModifiedCartan


