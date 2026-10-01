import ModifiedCartan.CauchyRegularization
import ModifiedCartan.LocalConvergence
import Mathlib.MeasureTheory.Measure.FiniteMeasure

open scoped Topology ENNReal BoundedContinuousFunction
open Filter MeasureTheory Set Metric

namespace ModifiedCartan

/-! Weak convergence of finite measures implies local Lp convergence of their
Cauchy transforms for 1 ≤ p < 2. This supplies the transform-convergence step in
`lem:logderivlimit`; the Riesz measures and the harmonic remainder are separate
obligations. The proof combines continuous regularization, dominated convergence,
and the previously proved uniform truncation error. -/

theorem tendsto_eLpNorm_zero_of_bounded_ae_tendsto {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E]
    (μ : Measure α) [IsFiniteMeasure μ] {f : ℕ → α → E}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) {C p : ℝ} (hp : 0 < p)
    (hC : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ C)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n) (ENNReal.ofReal p) μ) atTop (𝓝 0) := by
  have hpow : Tendsto (fun n => ∫⁻ x, ‖f n x‖ₑ ^ p ∂μ) atTop (𝓝 0) := by
    have h := tendsto_lintegral_of_dominated_convergence'
      (fun _x : α => ENNReal.ofReal C ^ p)
      (fun n => (hf n).enorm.pow_const p) (f := fun _x => 0)
    simp only [lintegral_zero] at h
    apply h
    · intro n
      filter_upwards [hC n] with x hx
      apply ENNReal.rpow_le_rpow _ hp.le
      simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal hx
    · rw [lintegral_const]
      exact (ENNReal.mul_lt_top
        (ENNReal.rpow_lt_top_of_nonneg hp.le ENNReal.ofReal_ne_top)
        (measure_lt_top _ _)).ne
    · filter_upwards [hlim] with x hx
      have hn : Tendsto (fun n => ‖f n x‖) atTop (𝓝 0) := by simpa using hx.norm
      have he : Tendsto (fun n => ‖f n x‖ₑ) atTop (𝓝 0) := by
        simpa only [ofReal_norm, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hn
      simpa only [ENNReal.zero_rpow_of_pos hp] using he.ennrpow_const p
  simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ne_of_gt (ENNReal.ofReal_pos.mpr hp)) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp.le, one_div]
  simpa only [ENNReal.zero_rpow_of_pos (inv_pos.mpr hp)] using hpow.ennrpow_const p⁻¹

theorem exists_mass_bound_of_weak_tendsto {ν : ℕ → FiniteMeasure ℂ} {ν₀ : FiniteMeasure ℂ}
    (hν : Tendsto ν atTop (𝓝 ν₀)) :
    ∃ M : ℝ, 0 < M ∧ (ν₀ : Measure ℂ).real univ ≤ M ∧
      ∀ n, (ν n : Measure ℂ).real univ ≤ M := by
  have hm : Tendsto (fun n => (ν n : Measure ℂ).real univ) atTop
      (𝓝 ((ν₀ : Measure ℂ).real univ)) := by
    simpa only [Measure.real, ← FiniteMeasure.ennreal_mass, ENNReal.coe_toReal,
      Function.comp_def] using
      (NNReal.continuous_coe.tendsto ν₀.mass).comp hν.mass
  obtain ⟨M, hM0, hM⟩ := (Metric.isBounded_range_of_tendsto _ hm).exists_pos_norm_le
  refine ⟨M + (ν₀ : Measure ℂ).real univ, add_pos_of_pos_of_nonneg hM0
    ENNReal.toReal_nonneg, ?_, ?_⟩
  · linarith
  · intro n
    have hn := hM _ (mem_range_self n)
    have hn' : (ν n : Measure ℂ).real univ ≤ M :=
      (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hn)
    linarith [show 0 ≤ (ν₀ : Measure ℂ).real univ from ENNReal.toReal_nonneg]

noncomputable def cauchyRegularizationTest {R : ℝ} (hR : 0 < R) (z : ℂ) : ℂ →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun a => cauchyRegularization R (z - a))
    ((continuous_cauchyRegularization hR).comp (continuous_const.sub continuous_id)) R⁻¹
    (fun a => norm_cauchyRegularization_le hR (z - a))

theorem regularizedCauchyTransform_tendsto {ν : ℕ → FiniteMeasure ℂ} {ν₀ : FiniteMeasure ℂ}
    (hν : Tendsto ν atTop (𝓝 ν₀)) {R : ℝ} (hR : 0 < R) (z : ℂ) :
    Tendsto (fun n => regularizedCauchyTransform R (ν n) z) atTop
      (𝓝 (regularizedCauchyTransform R ν₀ z)) :=
  (FiniteMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp hν
    (cauchyRegularizationTest hR z)

theorem regularizedCauchyTransform_tendsto_eLpNorm {ν : ℕ → FiniteMeasure ℂ}
    {ν₀ : FiniteMeasure ℂ} (hν : Tendsto ν atTop (𝓝 ν₀))
    {R p : ℝ} (hR : 0 < R) (hp : 0 < p) {K : Set ℂ} (hK : IsCompact K) :
    Tendsto (fun n => eLpNorm (regularizedCauchyTransform R (ν n) -
      regularizedCauchyTransform R ν₀) (ENNReal.ofReal p) (volume.restrict K)) atTop (𝓝 0) := by
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  obtain ⟨M, hM0, hMlim, hM⟩ := exists_mass_bound_of_weak_tendsto hν
  apply tendsto_eLpNorm_zero_of_bounded_ae_tendsto (volume.restrict K)
    (fun n => ((measurable_regularizedCauchyTransform (ν n) hR).sub
      (measurable_regularizedCauchyTransform ν₀ hR)).aestronglyMeasurable)
    (C := 2 * (R⁻¹ * M)) hp
  · intro n
    apply Eventually.of_forall
    intro z
    calc
      _ ≤ ‖regularizedCauchyTransform R (ν n) z‖ +
          ‖regularizedCauchyTransform R ν₀ z‖ := norm_sub_le _ _
      _ ≤ R⁻¹ * (ν n : Measure ℂ).real univ + R⁻¹ * (ν₀ : Measure ℂ).real univ :=
        add_le_add (norm_regularizedCauchyTransform_le (ν n) hR z)
          (norm_regularizedCauchyTransform_le ν₀ hR z)
      _ ≤ _ := by nlinarith [inv_pos.mpr hR, hM n]
  · apply Eventually.of_forall
    intro z
    simpa only [Pi.sub_apply, sub_self] using
      (regularizedCauchyTransform_tendsto hν hR z).sub_const (regularizedCauchyTransform R ν₀ z)

theorem eLpNorm_sub_le_three {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {f g F G : α → E} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hF : AEStronglyMeasurable F μ) (hG : AEStronglyMeasurable G μ) :
    eLpNorm (f - g) p μ ≤
      eLpNorm (f - F) p μ + eLpNorm (F - G) p μ + eLpNorm (g - G) p μ := by
  have heq : f - g = ((f - F) + (F - G)) - (g - G) := by abel
  calc
    _ = eLpNorm (((f - F) + (F - G)) - (g - G)) p μ := by rw [← heq]
    _ ≤ eLpNorm ((f - F) + (F - G)) p μ + eLpNorm (g - G) p μ :=
      eLpNorm_sub_le ((hf.sub hF).add (hF.sub hG)) (hg.sub hG) hp
    _ ≤ _ := by
      gcongr
      exact eLpNorm_add_le (hf.sub hF) (hF.sub hG) hp

theorem cauchyTransform_tendsto_eLpNorm {ν : ℕ → FiniteMeasure ℂ}
    {ν₀ : FiniteMeasure ℂ} (hν : Tendsto ν atTop (𝓝 ν₀))
    {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p < 2) {K : Set ℂ} (hK : IsCompact K) :
    Tendsto (fun n => eLpNorm (cauchyTransform (ν n) - cauchyTransform ν₀)
      (ENNReal.ofReal p) (volume.restrict K)) atTop (𝓝 0) := by
  obtain ⟨M, hM0, hMlim, hM⟩ := exists_mass_bound_of_weak_tendsto hν
  have hmass (n : ℕ) : (ν n : Measure ℂ) univ ≤ ENNReal.ofReal M := by
    simpa only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)] using
      ENNReal.ofReal_le_ofReal (hM n)
  have hmass₀ : (ν₀ : Measure ℂ) univ ≤ ENNReal.ofReal M := by
    simpa only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)] using
      ENNReal.ofReal_le_ofReal hMlim
  let B (R : ℝ) := ENNReal.ofReal M *
    (2 * ENNReal.ofReal (((2 * Real.pi / (2 - p)) * R ^ (2 - p)) ^ p⁻¹))
  have hBlim : Tendsto B (𝓝 0) (𝓝 0) := by
    have hc : ENNReal.ofReal M * 2 ≠ ⊤ := by finiteness
    simpa only [B, mul_assoc, mul_zero] using ENNReal.Tendsto.const_mul
      (cauchy_truncation_bound_tendsto_zero (lt_of_lt_of_le zero_lt_one hp1) hp2)
      (Or.inr hc : (0 : ℝ≥0∞) ≠ 0 ∨ ENNReal.ofReal M * 2 ≠ ⊤)
  have herr (R : ℝ) (hR : 0 < R) (n : ℕ) :
      eLpNorm (cauchyTransform (ν n) - regularizedCauchyTransform R (ν n))
        (ENNReal.ofReal p) (volume.restrict K) ≤ B R := by
    apply (eLpNorm_cauchyTransform_sub_regularized_le (ν n) hp1 hp2 hR K).trans
    dsimp [B]
    gcongr
    exact hmass n
  have herr₀ (R : ℝ) (hR : 0 < R) :
      eLpNorm (cauchyTransform ν₀ - regularizedCauchyTransform R ν₀)
        (ENNReal.ofReal p) (volume.restrict K) ≤ B R := by
    apply (eLpNorm_cauchyTransform_sub_regularized_le ν₀ hp1 hp2 hR K).trans
    dsimp [B]
    gcongr
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  have hε3 : (0 : ℝ≥0∞) < ε / 3 := ENNReal.div_pos hε.ne' (by norm_num)
  obtain ⟨δ, hδ, hsmall⟩ :=
    Metric.eventually_nhds_iff_ball.mp (hBlim.eventually_lt_const hε3)
  have hR : 0 < δ / 2 := by positivity
  have hB : B (δ / 2) < ε / 3 := by
    apply hsmall
    simp only [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hR]
    linarith
  have hreg := regularizedCauchyTransform_tendsto_eLpNorm hν hR
    (lt_of_lt_of_le zero_lt_one hp1) hK
  filter_upwards [hreg.eventually_lt_const hε3] with n hn
  calc
    _ ≤ eLpNorm (cauchyTransform (ν n) - regularizedCauchyTransform (δ / 2) (ν n))
        (ENNReal.ofReal p) (volume.restrict K) +
        eLpNorm (regularizedCauchyTransform (δ / 2) (ν n) - regularizedCauchyTransform (δ / 2) ν₀)
          (ENNReal.ofReal p) (volume.restrict K) +
        eLpNorm (cauchyTransform ν₀ - regularizedCauchyTransform (δ / 2) ν₀)
          (ENNReal.ofReal p) (volume.restrict K) :=
      eLpNorm_sub_le_three (ENNReal.one_le_ofReal.mpr hp1)
        (measurable_cauchyTransform (ν n)).aestronglyMeasurable
        (measurable_cauchyTransform ν₀).aestronglyMeasurable
        (measurable_regularizedCauchyTransform (ν n) hR).aestronglyMeasurable
        (measurable_regularizedCauchyTransform ν₀ hR).aestronglyMeasurable
    _ ≤ ε / 3 + ε / 3 + ε / 3 :=
      add_le_add (add_le_add ((herr _ hR n).trans hB.le) hn.le)
        ((herr₀ _ hR).trans hB.le)
    _ = ε := ENNReal.add_thirds ε

theorem cauchyTransform_localLpConvergence {ν : ℕ → FiniteMeasure ℂ}
    {ν₀ : FiniteMeasure ℂ} (hν : Tendsto ν atTop (𝓝 ν₀))
    {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p < 2) (U : Set ℂ) :
    LocalLpConvergence (ENNReal.ofReal p) U
      (fun n => cauchyTransform (ν n)) (cauchyTransform ν₀) where
  source_mem _K hK _ n := memLp_cauchyTransform_on_compact (ν n) hp1 hp2 hK
  limit_mem _K hK _ := memLp_cauchyTransform_on_compact ν₀ hp1 hp2 hK
  tendsto _K hK _ := cauchyTransform_tendsto_eLpNorm hν hp1 hp2 hK


end ModifiedCartan

