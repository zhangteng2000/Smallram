import ModifiedCartan.CauchyTruncation
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

open scoped Topology ENNReal
open Filter MeasureTheory Set Metric


namespace ModifiedCartan

/-! The general finite-measure form of the Cauchy-kernel estimate used in
`eq:kernel-truncation-bound`, within the proof of `lem:logderivlimit`.
Hölder for probability measures followed by Tonelli gives the integral estimate;
normalizing a nonzero finite measure restores its total-mass factor. -/

theorem eLpNorm_integral_probability_le {α β E : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    (ν : Measure α) [IsProbabilityMeasure ν] (μ : Measure β) [SFinite μ]
    {f : α × β → E} (hf : Measurable f) {p : ℝ} (hp : 1 ≤ p)
    {C : ℝ≥0∞} (hC : ∀ a, eLpNorm (fun z => f (a, z)) (ENNReal.ofReal p) μ ≤ C) :
    eLpNorm (fun z => ∫ a, f (a, z) ∂ν) (ENNReal.ofReal p) μ ≤ C := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hpne : ENNReal.ofReal p ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hp0)
  have hpoint (z : β) : ‖∫ a, f (a, z) ∂ν‖ₑ ≤
      eLpNorm (fun a => f (a, z)) (ENNReal.ofReal p) ν := by
    apply (enorm_integral_le_lintegral_enorm _).trans
    rw [← eLpNorm_one_eq_lintegral_enorm]
    exact eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.one_le_ofReal.mpr hp)
      (hf.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal hpne ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp0.le, one_div] at hpoint hC ⊢
  apply (ENNReal.rpow_inv_le_iff hp0).mpr
  calc
    _ ≤ ∫⁻ z, ∫⁻ a, ‖f (a, z)‖ₑ ^ p ∂ν ∂μ := by
      apply lintegral_mono
      intro z
      exact (ENNReal.rpow_le_rpow (hpoint z) hp0.le).trans_eq
        (ENNReal.rpow_inv_rpow hp0.ne' _)
    _ = ∫⁻ a, ∫⁻ z, ‖f (a, z)‖ₑ ^ p ∂μ ∂ν := by
      exact lintegral_lintegral_swap (hf.comp measurable_swap |>.enorm.pow_const p
        |>.aemeasurable)
    _ ≤ ∫⁻ _a, C ^ p ∂ν := by
      apply lintegral_mono
      intro a
      exact (ENNReal.rpow_inv_le_iff hp0).mp (hC a)
    _ = C ^ p := by simp

theorem eLpNorm_integral_finite_le {α β E : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    (ν : Measure α) [IsFiniteMeasure ν] (μ : Measure β) [SFinite μ]
    {f : α × β → E} (hf : Measurable f) {p : ℝ} (hp : 1 ≤ p)
    {C : ℝ≥0∞} (hC : ∀ a, eLpNorm (fun z => f (a, z)) (ENNReal.ofReal p) μ ≤ C) :
    eLpNorm (fun z => ∫ a, f (a, z) ∂ν) (ENNReal.ofReal p) μ ≤ ν univ * C := by
  by_cases hν : ν = 0
  · simp [hν]
  let : NeZero ν := ⟨hν⟩
  let ν' := (ν univ)⁻¹ • ν
  have hrepr : ν univ • ν' = ν := by
    dsimp [ν']
    rw [smul_smul, ENNReal.mul_inv_cancel (NeZero.ne _) (measure_ne_top _ _), one_smul]
  have heq : (fun z => ∫ a, f (a, z) ∂ν) =
      (ν univ).toReal • (fun z => ∫ a, f (a, z) ∂ν') := by
    funext z
    change (∫ a, f (a, z) ∂ν) = (ν univ).toReal • ∫ a, f (a, z) ∂ν'
    rw [← integral_smul_measure, hrepr]
  rw [heq, eLpNorm_const_smul, Real.enorm_of_nonneg ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hle := eLpNorm_integral_probability_le ν' μ hf hp hC
  gcongr

theorem measurable_nearCauchyKernel (R : ℝ) :
    Measurable (fun x : ℂ × ℂ => nearCauchyKernel R x.1 x.2) := by
  have hf : Measurable (fun x : ℂ × ℂ => (x.2 - x.1)⁻¹) := by fun_prop
  have hs : MeasurableSet {x : ℂ × ℂ | ‖x.2 - x.1‖ < R} :=
    measurableSet_lt (by fun_prop) measurable_const
  convert hf.indicator hs using 1
  funext x
  simp only [nearCauchyKernel, indicator, mem_ofPred_eq, mem_ball, dist_eq_norm]

theorem eLpNorm_integral_nearCauchyKernel_le (ν : Measure ℂ) [IsFiniteMeasure ν]
    {p R : ℝ} (hp1 : 1 ≤ p) (hp2 : p < 2) (hR : 0 ≤ R) (K : Set ℂ) :
    eLpNorm (fun z => ∫ a, nearCauchyKernel R a z ∂ν)
      (ENNReal.ofReal p) (volume.restrict K) ≤
      ν univ * ENNReal.ofReal (((2 * Real.pi / (2 - p)) * R ^ (2 - p)) ^ p⁻¹) := by
  apply eLpNorm_integral_finite_le ν (volume.restrict K) (measurable_nearCauchyKernel R) hp1
  intro a
  exact (eLpNorm_mono_measure (nearCauchyKernel R a) Measure.restrict_le_self).trans_eq
    (eLpNorm_nearCauchyKernel (lt_of_lt_of_le zero_lt_one hp1) hp2 hR a)

theorem memLp_integral_nearCauchyKernel (ν : Measure ℂ) [IsFiniteMeasure ν]
    {p R : ℝ} (hp1 : 1 ≤ p) (hp2 : p < 2) (hR : 0 ≤ R) (K : Set ℂ) :
    MemLp (fun z => ∫ a, nearCauchyKernel R a z ∂ν)
      (ENNReal.ofReal p) (volume.restrict K) := by
  refine ⟨(measurable_nearCauchyKernel R).stronglyMeasurable.integral_prod_left'
    |>.aestronglyMeasurable, ?_⟩
  exact (eLpNorm_integral_nearCauchyKernel_le ν hp1 hp2 hR K).trans_lt
    (ENNReal.mul_lt_top (measure_lt_top _ _) ENNReal.ofReal_lt_top)

theorem integrable_prod_of_eLpNorm_one_le {α β E : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ν : Measure α) [IsFiniteMeasure ν] (μ : Measure β) [SFinite μ]
    {f : α × β → E} (hf : Measurable f) {C : ℝ≥0∞} (hCtop : C < ⊤)
    (hC : ∀ a, eLpNorm (fun z => f (a, z)) 1 μ ≤ C) :
    Integrable f (ν.prod μ) := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hf.enorm.aemeasurable]
  calc
    _ ≤ ∫⁻ _a, C ∂ν := by
      apply lintegral_mono
      intro a
      simpa only [eLpNorm_one_eq_lintegral_enorm] using hC a
    _ < ⊤ := by
      rw [lintegral_const]
      exact ENNReal.mul_lt_top hCtop (measure_lt_top _ _)

theorem integrable_prod_nearCauchyKernel (ν : Measure ℂ) [IsFiniteMeasure ν]
    {R : ℝ} (hR : 0 ≤ R) :
    Integrable (fun x : ℂ × ℂ => nearCauchyKernel R x.1 x.2) (ν.prod volume) := by
  apply integrable_prod_of_eLpNorm_one_le ν volume (measurable_nearCauchyKernel R)
    ENNReal.ofReal_lt_top
  intro a
  have heq := eLpNorm_nearCauchyKernel (p := 1) (by norm_num) (by norm_num) hR a
  simpa using heq.le

theorem ae_integrable_nearCauchyKernel (ν : Measure ℂ) [IsFiniteMeasure ν]
    {R : ℝ} (hR : 0 ≤ R) :
    ∀ᵐ z ∂volume, Integrable (fun a => nearCauchyKernel R a z) ν :=
  (integrable_prod_nearCauchyKernel ν hR).prod_left_ae

theorem uniform_cauchy_truncation_measures (ν : ℕ → Measure ℂ)
    [∀ n, IsFiniteMeasure (ν n)] {p M : ℝ} (hp1 : 1 ≤ p) (hp2 : p < 2)
    (hM : ∀ n, ν n univ ≤ ENNReal.ofReal M) (K : Set ℂ) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ R : ℝ, 0 ≤ R → R < δ → ∀ n,
      eLpNorm (fun z => ∫ a, nearCauchyKernel R a z ∂ν n)
        (ENNReal.ofReal p) (volume.restrict K) < ε := by
  intro ε hε
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp1
  have hlim : Tendsto (fun R : ℝ => ENNReal.ofReal M *
      ENNReal.ofReal (((2 * Real.pi / (2 - p)) * R ^ (2 - p)) ^ p⁻¹))
      (𝓝 0) (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul
      (cauchy_truncation_bound_tendsto_zero hp0 hp2)
      (Or.inr ENNReal.ofReal_ne_top : (0 : ℝ≥0∞) ≠ 0 ∨ ENNReal.ofReal M ≠ ⊤)
  obtain ⟨δ, hδ, hsmall⟩ := Metric.eventually_nhds_iff_ball.mp (hlim.eventually_lt_const hε)
  refine ⟨δ, hδ, ?_⟩
  intro R hR hRδ n
  have hnear : R ∈ ball (0 : ℝ) δ := by
    simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hR] using hRδ
  apply lt_of_le_of_lt (eLpNorm_integral_nearCauchyKernel_le (ν n) hp1 hp2 hR K)
  apply lt_of_le_of_lt _ (hsmall R hnear)
  gcongr
  exact hM n


end ModifiedCartan
