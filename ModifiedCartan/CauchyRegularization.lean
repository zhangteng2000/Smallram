import ModifiedCartan.MeasureCauchy

open scoped Topology ENNReal ComplexConjugate
open Filter MeasureTheory Set Metric

namespace ModifiedCartan

/-! A continuous regularization of the Cauchy kernel for
`eq:kernel-truncation-bound` in `lem:logderivlimit`. The explicit conjugate formula
agrees with the inverse outside the truncation ball and has a controlled error
inside it. The transform statements use genuine almost-everywhere integrability. -/

noncomputable def cauchyRegularization (R : ℝ) (w : ℂ) : ℂ :=
  conj w / ((max R ‖w‖ : ℝ) : ℂ) ^ 2

theorem continuous_cauchyRegularization {R : ℝ} (hR : 0 < R) :
    Continuous (cauchyRegularization R) := by
  apply Complex.continuous_conj.div
    ((Complex.continuous_ofReal.comp (continuous_const.max continuous_norm)).pow 2)
  intro w
  exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le hR (le_max_left _ _))))

theorem cauchyRegularization_eq_inv {R : ℝ} {w : ℂ} (hw : R ≤ ‖w‖) :
    cauchyRegularization R w = w⁻¹ := by
  rw [Complex.inv_def w, Complex.normSq_eq_norm_sq]
  simp only [cauchyRegularization, max_eq_right hw, Complex.ofReal_inv,
    Complex.ofReal_pow, div_eq_mul_inv]

theorem norm_cauchyRegularization {R : ℝ} (hR : 0 < R) (w : ℂ) :
    ‖cauchyRegularization R w‖ = ‖w‖ / (max R ‖w‖) ^ 2 := by
  simp only [cauchyRegularization, norm_div, Complex.norm_conj, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le hR (le_max_left _ _))]

theorem norm_cauchyRegularization_le {R : ℝ} (hR : 0 < R) (w : ℂ) :
    ‖cauchyRegularization R w‖ ≤ R⁻¹ := by
  rw [norm_cauchyRegularization hR]
  have hm : 0 < max R ‖w‖ := lt_of_lt_of_le hR (le_max_left _ _)
  apply (div_le_iff₀ (sq_pos_of_pos hm)).mpr
  have h1 := le_max_right R ‖w‖
  have h2 := le_max_left R ‖w‖
  apply (mul_le_mul_iff_right₀ hR).mp
  field_simp
  nlinarith [norm_nonneg w]

theorem norm_cauchyRegularization_le_inv {R : ℝ} (hR : 0 < R) (w : ℂ) :
    ‖cauchyRegularization R w‖ ≤ ‖w⁻¹‖ := by
  by_cases hw : w = 0
  · simp [hw, cauchyRegularization]
  rw [norm_cauchyRegularization hR, norm_inv]
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hm : 0 < max R ‖w‖ := lt_of_lt_of_le hR (le_max_left _ _)
  apply (div_le_iff₀ (sq_pos_of_pos hm)).mpr
  apply (mul_le_mul_iff_right₀ hn).mp
  field_simp
  nlinarith [le_max_right R ‖w‖]

theorem norm_inv_sub_cauchyRegularization_le {R : ℝ} (hR : 0 < R) (w : ℂ) :
    ‖w⁻¹ - cauchyRegularization R w‖ ≤ 2 * ‖nearCauchyKernel R 0 w‖ := by
  by_cases hw : R ≤ ‖w‖
  · rw [cauchyRegularization_eq_inv hw, sub_self, norm_zero]
    positivity
  · have hmem : w ∈ ball (0 : ℂ) R := by simpa using lt_of_not_ge hw
    simp only [nearCauchyKernel, indicator_of_mem hmem, sub_zero]
    calc
      _ ≤ ‖w⁻¹‖ + ‖cauchyRegularization R w‖ := norm_sub_le _ _
      _ ≤ 2 * ‖w⁻¹‖ := by linarith [norm_cauchyRegularization_le_inv hR w]

theorem norm_cauchyRegularization_error_le {R : ℝ} (hR : 0 < R) (a z : ℂ) :
    ‖(z - a)⁻¹ - cauchyRegularization R (z - a)‖ ≤
      ‖(2 : ℝ) • nearCauchyKernel R a z‖ := by
  have heq : nearCauchyKernel R 0 (z - a) = nearCauchyKernel R a z := by
    simp only [nearCauchyKernel, indicator, mem_ball, dist_eq_norm, sub_zero]
  simpa only [heq, norm_smul, Real.norm_ofNat] using
    norm_inv_sub_cauchyRegularization_le hR (z - a)

theorem measurable_cauchyRegularization_error {R : ℝ} (hR : 0 < R) :
    Measurable (fun x : ℂ × ℂ => (x.2 - x.1)⁻¹ -
      cauchyRegularization R (x.2 - x.1)) := by
  exact ((measurable_snd.sub measurable_fst).inv).sub
    ((continuous_cauchyRegularization hR).measurable.comp (measurable_snd.sub measurable_fst))

theorem eLpNorm_cauchyRegularization_error_le {p R : ℝ}
    (hp1 : 1 ≤ p) (hp2 : p < 2) (hR : 0 < R) (a : ℂ) (K : Set ℂ) :
    eLpNorm (fun z => (z - a)⁻¹ - cauchyRegularization R (z - a))
      (ENNReal.ofReal p) (volume.restrict K) ≤
      2 * ENNReal.ofReal (((2 * Real.pi / (2 - p)) * R ^ (2 - p)) ^ p⁻¹) := by
  calc
    _ ≤ eLpNorm ((2 : ℝ) • nearCauchyKernel R a) (ENNReal.ofReal p)
        (volume.restrict K) := eLpNorm_mono (norm_cauchyRegularization_error_le hR a)
    _ = 2 * eLpNorm (nearCauchyKernel R a) (ENNReal.ofReal p)
        (volume.restrict K) := by
      rw [eLpNorm_const_smul, Real.enorm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    _ ≤ _ := by
      have hle := (eLpNorm_mono_measure (nearCauchyKernel R a)
        (p := ENNReal.ofReal p) (ν := volume.restrict K) Measure.restrict_le_self).trans_eq
        (eLpNorm_nearCauchyKernel (lt_of_lt_of_le zero_lt_one hp1) hp2 hR.le a)
      gcongr

theorem integrable_cauchyRegularization (ν : Measure ℂ) [IsFiniteMeasure ν]
    {R : ℝ} (hR : 0 < R) (z : ℂ) :
    Integrable (fun a => cauchyRegularization R (z - a)) ν := by
  apply (integrable_const R⁻¹).mono'
    (((continuous_cauchyRegularization hR).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable)
  exact Eventually.of_forall fun a => norm_cauchyRegularization_le hR (z - a)

theorem ae_integrable_cauchyKernel (ν : Measure ℂ) [IsFiniteMeasure ν] :
    ∀ᵐ z ∂volume, Integrable (fun a => (z - a)⁻¹) ν := by
  filter_upwards [ae_integrable_nearCauchyKernel ν (R := 1) zero_le_one] with z hz
  have herror : Integrable (fun a => (z - a)⁻¹ - cauchyRegularization 1 (z - a)) ν := by
    apply (hz.smul (2 : ℝ)).mono
      ((measurable_cauchyRegularization_error zero_lt_one).comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    exact Eventually.of_forall fun a => norm_cauchyRegularization_error_le zero_lt_one a z
  simpa only [sub_add_cancel] using
    herror.fun_add (integrable_cauchyRegularization ν zero_lt_one z)

noncomputable def cauchyTransform (ν : Measure ℂ) (z : ℂ) : ℂ := ∫ a, (z - a)⁻¹ ∂ν

noncomputable def regularizedCauchyTransform (R : ℝ) (ν : Measure ℂ) (z : ℂ) : ℂ :=
  ∫ a, cauchyRegularization R (z - a) ∂ν

theorem eLpNorm_cauchyTransform_sub_regularized_le (ν : Measure ℂ) [IsFiniteMeasure ν]
    {p R : ℝ} (hp1 : 1 ≤ p) (hp2 : p < 2) (hR : 0 < R) (K : Set ℂ) :
    eLpNorm (cauchyTransform ν - regularizedCauchyTransform R ν)
      (ENNReal.ofReal p) (volume.restrict K) ≤
      ν univ * (2 * ENNReal.ofReal (((2 * Real.pi / (2 - p)) * R ^ (2 - p)) ^ p⁻¹)) := by
  have heq : cauchyTransform ν - regularizedCauchyTransform R ν =ᵐ[volume.restrict K]
      (fun z => ∫ a, (z - a)⁻¹ - cauchyRegularization R (z - a) ∂ν) := by
    filter_upwards [ae_restrict_of_ae (ae_integrable_cauchyKernel ν)] with z hz
    exact (integral_sub hz (integrable_cauchyRegularization ν hR z)).symm
  rw [eLpNorm_congr_ae heq]
  exact eLpNorm_integral_finite_le ν (volume.restrict K)
    (measurable_cauchyRegularization_error hR) hp1
    (fun a => eLpNorm_cauchyRegularization_error_le hp1 hp2 hR a K)

theorem measurable_cauchyTransform (ν : Measure ℂ) [IsFiniteMeasure ν] :
    Measurable (cauchyTransform ν) := by
  have hf : Measurable (fun x : ℂ × ℂ => (x.2 - x.1)⁻¹) := by fun_prop
  exact hf.stronglyMeasurable.integral_prod_left'.measurable

theorem measurable_regularizedCauchyTransform (ν : Measure ℂ) [IsFiniteMeasure ν]
    {R : ℝ} (hR : 0 < R) : Measurable (regularizedCauchyTransform R ν) := by
  have hf : Measurable (fun x : ℂ × ℂ => cauchyRegularization R (x.2 - x.1)) :=
    (continuous_cauchyRegularization hR).measurable.comp (measurable_snd.sub measurable_fst)
  exact hf.stronglyMeasurable.integral_prod_left'.measurable

theorem norm_regularizedCauchyTransform_le (ν : Measure ℂ) [IsFiniteMeasure ν]
    {R : ℝ} (hR : 0 < R) (z : ℂ) :
    ‖regularizedCauchyTransform R ν z‖ ≤ R⁻¹ * ν.real univ :=
  norm_integral_le_of_norm_le_const (Eventually.of_forall fun a =>
    norm_cauchyRegularization_le hR (z - a))

theorem memLp_regularizedCauchyTransform (ν : Measure ℂ) [IsFiniteMeasure ν]
    {R : ℝ} (hR : 0 < R) {K : Set ℂ} (hK : IsCompact K) (p : ℝ≥0∞) :
    MemLp (regularizedCauchyTransform R ν) p (volume.restrict K) := by
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  exact MemLp.of_bound (measurable_regularizedCauchyTransform ν hR).aestronglyMeasurable
    (R⁻¹ * ν.real univ) (Eventually.of_forall (norm_regularizedCauchyTransform_le ν hR))

theorem memLp_cauchyTransform_on_compact (ν : Measure ℂ) [IsFiniteMeasure ν]
    {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p < 2) {K : Set ℂ} (hK : IsCompact K) :
    MemLp (cauchyTransform ν) (ENNReal.ofReal p) (volume.restrict K) := by
  have herr : MemLp (cauchyTransform ν - regularizedCauchyTransform 1 ν)
      (ENNReal.ofReal p) (volume.restrict K) := by
    refine ⟨((measurable_cauchyTransform ν).sub
      (measurable_regularizedCauchyTransform ν zero_lt_one)).aestronglyMeasurable, ?_⟩
    apply (eLpNorm_cauchyTransform_sub_regularized_le ν hp1 hp2 zero_lt_one K).trans_lt
    finiteness
  simpa only [sub_add_cancel] using
    herr.add (memLp_regularizedCauchyTransform ν zero_lt_one hK (ENNReal.ofReal p))


end ModifiedCartan
