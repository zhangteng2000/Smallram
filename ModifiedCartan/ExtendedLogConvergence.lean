import ModifiedCartan.LogDerivativeLimit
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp

open scoped Topology ENNReal
open Filter MeasureTheory Set

set_option autoImplicit false

namespace ModifiedCartan

/-- The actual extended logarithm, including value negative infinity at zero. -/
noncomputable def extendedLogNorm (z : ℂ) : EReal := ENNReal.log (ENNReal.ofReal ‖z‖)

noncomputable def normalizedExtendedLog (s : ℝ) (f : ℂ → ℂ) (z : ℂ) : EReal :=
  ((s⁻¹ : ℝ) : EReal) * extendedLogNorm (f z)

@[simp] theorem extendedLogNorm_zero : extendedLogNorm 0 = ⊥ := by
  simp [extendedLogNorm]

theorem extendedLogNorm_of_ne_zero {z : ℂ} (hz : z ≠ 0) :
    extendedLogNorm z = (Real.log ‖z‖ : EReal) :=
  ENNReal.log_ofReal_of_pos (norm_pos_iff.mpr hz)

@[simp] theorem extendedLogNorm_toReal (z : ℂ) : (extendedLogNorm z).toReal = Real.log ‖z‖ := by
  by_cases hz : z = 0
  · simp [hz]
  · rw [extendedLogNorm_of_ne_zero hz, EReal.toReal_coe]

@[simp] theorem normalizedExtendedLog_toReal (s : ℝ) (f : ℂ → ℂ) (z : ℂ) :
    (normalizedExtendedLog s f z).toReal = s⁻¹ * Real.log ‖f z‖ := by
  simp [normalizedExtendedLog, EReal.toReal_mul]

theorem normalizedExtendedLog_eq_bot {s : ℝ} (hs : 0 < s) {f : ℂ → ℂ} {z : ℂ}
    (hf : f z = 0) : normalizedExtendedLog s f z = ⊥ := by
  rw [normalizedExtendedLog, hf, extendedLogNorm_zero]
  exact EReal.coe_mul_bot_of_pos (inv_pos.mpr hs)

theorem normalizedExtendedLog_of_ne_zero (s : ℝ) {f : ℂ → ℂ} {z : ℂ} (hf : f z ≠ 0) :
    normalizedExtendedLog s f z = ((s⁻¹ * Real.log ‖f z‖ : ℝ) : EReal) := by
  rw [normalizedExtendedLog, extendedLogNorm_of_ne_zero hf, EReal.coe_mul]

theorem normalizedExtendedLog_finite_iff {s : ℝ} (hs : 0 < s) (f : ℂ → ℂ) (z : ℂ) :
    (normalizedExtendedLog s f z ≠ ⊥ ∧ normalizedExtendedLog s f z ≠ ⊤) ↔ f z ≠ 0 := by
  by_cases hf : f z = 0
  · simp [normalizedExtendedLog_eq_bot hs hf, hf]
  · rw [normalizedExtendedLog_of_ne_zero s hf]
    exact iff_of_true ⟨EReal.coe_ne_bot _, EReal.coe_ne_top _⟩ hf

/-- Local Lp convergence of extended-valued functions to a finite representative.
Finiteness almost everywhere is explicit, as in the usual Lp convention. -/
structure LocalERealLpConvergence (p : ℝ≥0∞) (U : Set ℂ)
    (f : ℕ → ℂ → EReal) (v : ℂ → ℝ) : Prop where
  source_finite : ∀ n, ∀ᵐ z ∂volume.restrict U, f n z ≠ ⊥ ∧ f n z ≠ ⊤
  real_convergence : LocalLpConvergence p U (fun n z => (f n z).toReal) v

/-- Convergence in measure to a finite representative, using its order
neighborhoods and retaining both infinite values in the deviation sets. -/
def LocalERealMeasureConvergence (U : Set ℂ) (f : ℕ → ℂ → EReal) (v : ℂ → ℝ) : Prop :=
  ∀ K, IsCompact K → K ⊆ U → ∀ ε : ℝ, 0 < ε →
    Tendsto (fun n => (volume.restrict K)
      {z | f n z ≤ ((v z - ε : ℝ) : EReal) ∨ ((v z + ε : ℝ) : EReal) ≤ f n z}) atTop (𝓝 0)

theorem LocalERealLpConvergence.normalizedLog_real {p : ℝ≥0∞} {U : Set ℂ}
    {f : ℕ → ℂ → ℂ} {s : ℕ → ℝ} {v : ℂ → ℝ}
    (h : LocalERealLpConvergence p U (fun n => normalizedExtendedLog (s n) (f n)) v) :
    LocalLpConvergence p U (fun n z => (s n)⁻¹ * Real.log ‖f n z‖) v := by
  simpa only [normalizedExtendedLog_toReal] using h.real_convergence

theorem LocalERealLpConvergence.normalizedLog_ae_ne_zero {p : ℝ≥0∞} {U : Set ℂ}
    {f : ℕ → ℂ → ℂ} {s : ℕ → ℝ} {v : ℂ → ℝ}
    (h : LocalERealLpConvergence p U (fun n => normalizedExtendedLog (s n) (f n)) v)
    {n : ℕ} (hs : 0 < s n) : ∀ᵐ z ∂volume.restrict U, f n z ≠ 0 := by
  filter_upwards [h.source_finite n] with z hz
  exact (normalizedExtendedLog_finite_iff hs (f n) z).mp hz

theorem LocalERealLpConvergence.normalizedLog_nontrivial {p : ℝ≥0∞} {U : Set ℂ}
    (hU : IsOpen U) (hne : U.Nonempty) {f : ℕ → ℂ → ℂ} {s : ℕ → ℝ} {v : ℂ → ℝ}
    (h : LocalERealLpConvergence p U (fun n => normalizedExtendedLog (s n) (f n)) v)
    {n : ℕ} (hs : 0 < s n) : ∃ z ∈ U, f n z ≠ 0 :=
  Measure.exists_mem_of_measure_ne_zero_of_ae (hU.measure_ne_zero volume hne) (h.normalizedLog_ae_ne_zero hs)

theorem LocalERealLpConvergence.comp_tendsto {p : ℝ≥0∞} {U : Set ℂ}
    {f : ℕ → ℂ → EReal} {v : ℂ → ℝ} (h : LocalERealLpConvergence p U f v)
    {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop) :
    LocalERealLpConvergence p U (fun n => f (ns n)) v :=
  ⟨fun n => h.source_finite (ns n), h.real_convergence.comp_tendsto hns⟩

theorem LocalERealMeasureConvergence.comp_tendsto {U : Set ℂ}
    {f : ℕ → ℂ → EReal} {v : ℂ → ℝ} (h : LocalERealMeasureConvergence U f v)
    {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop) :
    LocalERealMeasureConvergence U (fun n => f (ns n)) v :=
  fun K hK hKU ε hε => (h K hK hKU ε hε).comp hns

theorem LocalERealMeasureConvergence.real_of_ae {U : Set ℂ}
    {F : ℕ → ℂ → EReal} {f : ℕ → ℂ → ℝ} {v : ℂ → ℝ}
    (h : LocalERealMeasureConvergence U F v)
    (hrep : ∀ n, F n =ᵐ[volume.restrict U] (fun z => (f n z : EReal))) :
    LocalMeasureConvergence U f v := by
  intro K hK hKU
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  apply (h K hK hKU ε hε).congr'
  apply Eventually.of_forall
  intro n
  apply measure_congr
  filter_upwards [(hrep n).filter_mono (ae_mono (Measure.restrict_mono_set _ hKU))] with z hz
  apply propext
  change (F n z ≤ ((v z - ε : ℝ) : EReal) ∨ ((v z + ε : ℝ) : EReal) ≤ F n z) ↔
    ε ≤ ‖f n z - v z‖
  simp only [hz, EReal.coe_le_coe_iff, Real.norm_eq_abs]
  by_cases h0 : 0 ≤ f n z - v z
  · rw [abs_of_nonneg h0]
    constructor
    · rintro (ha | ha) <;> linarith
    · intro ha
      right
      linarith
  · rw [abs_of_neg (lt_of_not_ge h0)]
    constructor
    · rintro (ha | ha) <;> linarith
    · intro ha
      left
      linarith

theorem LocalERealMeasureConvergence.normalizedLog_real {U : Set ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U) {f : ℕ → ℂ → ℂ} {s : ℕ → ℝ} {v : ℂ → ℝ}
    (h : LocalERealMeasureConvergence U (fun n => normalizedExtendedLog (s n) (f n)) v)
    (hf : ∀ n, AnalyticOnNhd ℂ (f n) U) (hnz : ∀ n, ∃ z ∈ U, f n z ≠ 0) :
    LocalMeasureConvergence U (fun n z => (s n)⁻¹ * Real.log ‖f n z‖) v := by
  apply h.real_of_ae
  intro n
  filter_upwards [analytic_ae_ne_zero hU hUc (hf n) (hnz n)] with z hz
  exact normalizedExtendedLog_of_ne_zero (s n) hz

theorem LocalERealMeasureConvergence.normalizedLog_eventually_nontrivial {U : Set ℂ}
    (hU : IsOpen U) (hne : U.Nonempty) {f : ℕ → ℂ → ℂ} {s : ℕ → ℝ}
    (h : LocalERealMeasureConvergence U (fun n => normalizedExtendedLog (s n) (f n)) (fun _ => 0))
    (hs : Tendsto s atTop atTop) : ∀ᶠ n in atTop, ∃ z ∈ U, f n z ≠ 0 := by
  obtain ⟨c, hc⟩ := hne
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU c hc
  let K := Metric.closedBall c (ε / 2)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKU : K ⊆ U := (Metric.closedBall_subset_ball (half_lt_self hε)).trans hεU
  have hKpos : 0 < volume K :=
    (Metric.isOpen_ball.measure_pos volume ⟨c, Metric.mem_ball_self (half_pos hε)⟩).trans_le
      (measure_mono Metric.ball_subset_closedBall)
  have hsmall := (h K hK hKU 1 zero_lt_one).eventually (gt_mem_nhds hKpos)
  filter_upwards [hsmall, hs.eventually (eventually_gt_atTop 0)] with n hn hsn
  by_contra! hall
  have hle : volume K ≤ (volume.restrict K)
      {z | normalizedExtendedLog (s n) (f n) z ≤ ((0 - 1 : ℝ) : EReal) ∨
        ((0 + 1 : ℝ) : EReal) ≤ normalizedExtendedLog (s n) (f n) z} := by
    calc
      _ = (volume.restrict K) K := by simp [Measure.restrict_apply hK.measurableSet]
      _ ≤ _ := measure_mono (fun z hz => Or.inl (by
        rw [normalizedExtendedLog_eq_bot hsn (hall z (hKU hz))]
        exact bot_le))
  exact (not_lt_of_ge hle) hn


end ModifiedCartan

