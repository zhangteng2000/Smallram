import ModifiedCartan.LogRegularization
import Mathlib.MeasureTheory.Measure.Portmanteau

open scoped Topology ENNReal BoundedContinuousFunction
open Filter MeasureTheory Set Metric

namespace ModifiedCartan

/-! Logarithmic-potential convergence in `lem:logderivlimit`. For weakly
convergent finite measures supported on a common compact set, the full
logarithmic potentials converge in local L1. Support of the limit is derived
from Portmanteau; it is not an extra hypothesis. -/

noncomputable def logRegularizationTest {R L : ℝ} (hR : 0 < R) (hRL : R ≤ L)
    (z : ℂ) : ℂ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun a => logRegularization R L (z - a))
    ((continuous_logRegularization hR L).comp (continuous_const.sub continuous_id))
    (|Real.log R| + |Real.log L|) (fun a => norm_logRegularization_le hR hRL (z - a))

theorem regularizedLogPotential_tendsto {ν : ℕ → FiniteMeasure ℂ} {ν₀ : FiniteMeasure ℂ}
    (hν : Tendsto ν atTop (𝓝 ν₀)) {R L : ℝ} (hR : 0 < R) (hRL : R ≤ L) (z : ℂ) :
    Tendsto (fun n => regularizedLogPotential R L (ν n) z) atTop
      (𝓝 (regularizedLogPotential R L ν₀ z)) :=
  FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hν (logRegularizationTest hR hRL z)

theorem regularizedLogPotential_tendsto_eLpNorm {ν : ℕ → FiniteMeasure ℂ}
    {ν₀ : FiniteMeasure ℂ} (hν : Tendsto ν atTop (𝓝 ν₀))
    {R L p : ℝ} (hR : 0 < R) (hRL : R ≤ L) (hp : 0 < p) {K : Set ℂ} (hK : IsCompact K) :
    Tendsto (fun n => eLpNorm (regularizedLogPotential R L (ν n) -
      regularizedLogPotential R L ν₀) (ENNReal.ofReal p) (volume.restrict K)) atTop (𝓝 0) := by
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  obtain ⟨M, hM0, hMlim, hM⟩ := exists_mass_bound_of_weak_tendsto hν
  apply tendsto_eLpNorm_zero_of_bounded_ae_tendsto (volume.restrict K)
    (fun n => ((measurable_regularizedLogPotential hR L (ν n)).sub
      (measurable_regularizedLogPotential hR L ν₀)).aestronglyMeasurable)
    (C := 2 * ((|Real.log R| + |Real.log L|) * M)) hp
  · intro n
    apply Eventually.of_forall
    intro z
    calc
      _ ≤ ‖regularizedLogPotential R L (ν n) z‖ +
          ‖regularizedLogPotential R L ν₀ z‖ := norm_sub_le _ _
      _ ≤ (|Real.log R| + |Real.log L|) * (ν n : Measure ℂ).real univ +
          (|Real.log R| + |Real.log L|) * (ν₀ : Measure ℂ).real univ :=
        add_le_add (norm_regularizedLogPotential_le (ν n) hR hRL z)
          (norm_regularizedLogPotential_le ν₀ hR hRL z)
      _ ≤ _ := by nlinarith [abs_nonneg (Real.log R), abs_nonneg (Real.log L), hM n]
  · apply Eventually.of_forall
    intro z
    simpa only [Pi.sub_apply, sub_self] using
      (regularizedLogPotential_tendsto hν hR hRL z).sub_const (regularizedLogPotential R L ν₀ z)

theorem cappedLogPotential_tendsto_eLpNorm {ν : ℕ → FiniteMeasure ℂ}
    {ν₀ : FiniteMeasure ℂ} (hν : Tendsto ν atTop (𝓝 ν₀))
    {L : ℝ} (hL : 1 ≤ L) {K : Set ℂ} (hK : IsCompact K) :
    Tendsto (fun n => eLpNorm (cappedLogPotential L (ν n) - cappedLogPotential L ν₀)
      1 (volume.restrict K)) atTop (𝓝 0) := by
  obtain ⟨M, hM0, hMlim, hM⟩ := exists_mass_bound_of_weak_tendsto hν
  have hmass (n : ℕ) : (ν n : Measure ℂ) univ ≤ ENNReal.ofReal M := by
    simpa only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)] using
      ENNReal.ofReal_le_ofReal (hM n)
  have hmass₀ : (ν₀ : Measure ℂ) univ ≤ ENNReal.ofReal M := by
    simpa only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)] using
      ENNReal.ofReal_le_ofReal hMlim
  let B (R : ℝ) := ENNReal.ofReal M * ENNReal.ofReal (2 * Real.pi * R)
  have hBlim : Tendsto B (𝓝 0) (𝓝 0) := by
    have hr : Tendsto (fun R : ℝ => 2 * Real.pi * R) (𝓝 0) (𝓝 0) := by
      simpa only [mul_zero, id_eq] using
        (tendsto_id : Tendsto (fun R : ℝ => R) (𝓝 0) (𝓝 0)).const_mul (2 * Real.pi)
    have he : Tendsto (fun R : ℝ => ENNReal.ofReal (2 * Real.pi * R)) (𝓝 0) (𝓝 0) := by
      simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hr
    simpa only [B, mul_zero] using ENNReal.Tendsto.const_mul he
      (Or.inr ENNReal.ofReal_ne_top : (0 : ℝ≥0∞) ≠ 0 ∨ ENNReal.ofReal M ≠ ⊤)
  have herr (R : ℝ) (hR : 0 < R) (hR1 : R ≤ 1) (n : ℕ) :
      eLpNorm (cappedLogPotential L (ν n) - regularizedLogPotential R L (ν n))
        1 (volume.restrict K) ≤ B R := by
    apply (eLpNorm_cappedLogPotential_sub_regularized_le (ν n) hR hR1 hL K).trans
    dsimp [B]
    gcongr
    exact hmass n
  have herr₀ (R : ℝ) (hR : 0 < R) (hR1 : R ≤ 1) :
      eLpNorm (cappedLogPotential L ν₀ - regularizedLogPotential R L ν₀)
        1 (volume.restrict K) ≤ B R := by
    apply (eLpNorm_cappedLogPotential_sub_regularized_le ν₀ hR hR1 hL K).trans
    dsimp [B]
    gcongr
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  have hε3 : (0 : ℝ≥0∞) < ε / 3 := ENNReal.div_pos hε.ne' (by norm_num)
  obtain ⟨δ, hδ, hsmall⟩ := Metric.eventually_nhds_iff_ball.mp (hBlim.eventually_lt_const hε3)
  let R := min δ 1 / 2
  have hR : 0 < R := half_pos (lt_min hδ zero_lt_one)
  have hR1 : R ≤ 1 := by dsimp [R]; linarith [min_le_right δ (1 : ℝ)]
  have hRδ : R < δ := by dsimp [R]; linarith [min_le_left δ (1 : ℝ)]
  have hB : B R < ε / 3 := by
    apply hsmall
    simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hR] using hRδ
  have hreg : Tendsto (fun n => eLpNorm (regularizedLogPotential R L (ν n) -
      regularizedLogPotential R L ν₀) 1 (volume.restrict K)) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_one] using
      regularizedLogPotential_tendsto_eLpNorm hν hR (hR1.trans hL) zero_lt_one hK
  filter_upwards [hreg.eventually_lt_const hε3] with n hn
  calc
    _ ≤ eLpNorm (cappedLogPotential L (ν n) - regularizedLogPotential R L (ν n))
        1 (volume.restrict K) +
        eLpNorm (regularizedLogPotential R L (ν n) - regularizedLogPotential R L ν₀)
          1 (volume.restrict K) +
        eLpNorm (cappedLogPotential L ν₀ - regularizedLogPotential R L ν₀)
          1 (volume.restrict K) :=
      eLpNorm_sub_le_three le_rfl
        (measurable_cappedLogPotential L (ν n)).aestronglyMeasurable
        (measurable_cappedLogPotential L ν₀).aestronglyMeasurable
        (measurable_regularizedLogPotential hR L (ν n)).aestronglyMeasurable
        (measurable_regularizedLogPotential hR L ν₀).aestronglyMeasurable
    _ ≤ ε / 3 + ε / 3 + ε / 3 :=
      add_le_add (add_le_add ((herr _ hR hR1 n).trans hB.le) hn.le)
        ((herr₀ _ hR hR1).trans hB.le)
    _ = ε := ENNReal.add_thirds ε

theorem ae_mem_closed_of_weak_tendsto {ν : ℕ → FiniteMeasure ℂ} {ν₀ : FiniteMeasure ℂ}
    (hν : Tendsto ν atTop (𝓝 ν₀)) {S : Set ℂ} (hS : IsClosed S)
    (hsupp : ∀ n, ∀ᵐ a ∂(ν n : Measure ℂ), a ∈ S) :
    ∀ᵐ a ∂(ν₀ : Measure ℂ), a ∈ S := by
  have hmass : Tendsto (fun n => (ν n : Measure ℂ) univ) atTop
      (𝓝 ((ν₀ : Measure ℂ) univ)) := by
    simpa only [Function.comp_def, FiniteMeasure.ennreal_mass] using
      (ENNReal.continuous_coe.tendsto ν₀.mass).comp hν.mass
  have heq : (fun n => (ν n : Measure ℂ) S) = fun n => (ν n : Measure ℂ) univ := by
    funext n
    exact (ae_mem_iff_measure_eq hS.measurableSet.nullMeasurableSet).mp (hsupp n)
  have hset : Tendsto (fun n => (ν n : Measure ℂ) S) atTop
      (𝓝 ((ν₀ : Measure ℂ) univ)) := by rw [heq]; exact hmass
  have hle := FiniteMeasure.limsup_measure_closed_le_of_tendsto hν hS
  rw [hset.limsup_eq] at hle
  exact (ae_mem_iff_measure_eq hS.measurableSet.nullMeasurableSet).mpr
    (le_antisymm (measure_mono (subset_univ S)) hle)

noncomputable def logPotential (ν : Measure ℂ) (z : ℂ) : ℝ :=
  ∫ a, Real.log ‖z - a‖ ∂ν

theorem exists_log_cap_of_compact {K S : Set ℂ} (hK : IsCompact K) (hS : IsCompact S) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ z ∈ K, ∀ a ∈ S, ‖z - a‖ ≤ L := by
  obtain ⟨A, hA0, hA⟩ := hK.isBounded.exists_pos_norm_le
  obtain ⟨B, hB0, hB⟩ := hS.isBounded.exists_pos_norm_le
  refine ⟨A + B + 1, by linarith, ?_⟩
  intro z hz a ha
  have hn := norm_sub_le z a
  linarith [hA z hz, hB a ha]

theorem logPotential_eq_capped_of_ae_bound (ν : Measure ℂ) {L : ℝ} (z : ℂ)
    (hbound : ∀ᵐ a ∂ν, ‖z - a‖ ≤ L) :
    logPotential ν z = cappedLogPotential L ν z := by
  apply integral_congr_ae
  filter_upwards [hbound] with a ha
  simp only [cappedLogKernel, min_eq_right ha]

theorem memLp_logPotential_on_compact (ν : Measure ℂ) [IsFiniteMeasure ν]
    {S K : Set ℂ} (hS : IsCompact S) (hsupp : ∀ᵐ a ∂ν, a ∈ S) (hK : IsCompact K) :
    MemLp (logPotential ν) 1 (volume.restrict K) := by
  obtain ⟨L, hL, hbound⟩ := exists_log_cap_of_compact hK hS
  have heq : logPotential ν =ᵐ[volume.restrict K] cappedLogPotential L ν := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    exact logPotential_eq_capped_of_ae_bound ν z (hsupp.mono fun a ha => hbound z hz a ha)
  exact (memLp_congr_ae heq).mpr (memLp_cappedLogPotential_on_compact ν hL hK)

theorem logPotential_tendsto_eLpNorm {ν : ℕ → FiniteMeasure ℂ} {ν₀ : FiniteMeasure ℂ}
    (hν : Tendsto ν atTop (𝓝 ν₀)) {S K : Set ℂ} (hS : IsCompact S)
    (hsupp : ∀ n, ∀ᵐ a ∂(ν n : Measure ℂ), a ∈ S) (hK : IsCompact K) :
    Tendsto (fun n => eLpNorm (logPotential (ν n) - logPotential ν₀)
      1 (volume.restrict K)) atTop (𝓝 0) := by
  have hsupp₀ := ae_mem_closed_of_weak_tendsto hν hS.isClosed hsupp
  obtain ⟨L, hL, hbound⟩ := exists_log_cap_of_compact hK hS
  have heq : (fun n => eLpNorm (logPotential (ν n) - logPotential ν₀) 1 (volume.restrict K)) =
      (fun n => eLpNorm (cappedLogPotential L (ν n) - cappedLogPotential L ν₀)
        1 (volume.restrict K)) := by
    funext n
    apply eLpNorm_congr_ae
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    have hn := logPotential_eq_capped_of_ae_bound (ν n : Measure ℂ) z
      ((hsupp n).mono fun a ha => hbound z hz a ha)
    have h0 := logPotential_eq_capped_of_ae_bound (ν₀ : Measure ℂ) z
      (hsupp₀.mono fun a ha => hbound z hz a ha)
    exact congrArg₂ (· - ·) hn h0
  rw [heq]
  exact cappedLogPotential_tendsto_eLpNorm hν hL hK

theorem logPotential_localL1Convergence {ν : ℕ → FiniteMeasure ℂ} {ν₀ : FiniteMeasure ℂ}
    (hν : Tendsto ν atTop (𝓝 ν₀)) {S : Set ℂ} (hS : IsCompact S)
    (hsupp : ∀ n, ∀ᵐ a ∂(ν n : Measure ℂ), a ∈ S) (U : Set ℂ) :
    LocalLpConvergence 1 U (fun n => logPotential (ν n)) (logPotential ν₀) where
  source_mem _K hK _ n := memLp_logPotential_on_compact (ν n) hS (hsupp n) hK
  limit_mem _K hK _ := memLp_logPotential_on_compact ν₀ hS
    (ae_mem_closed_of_weak_tendsto hν hS.isClosed hsupp) hK
  tendsto _K hK _ := logPotential_tendsto_eLpNorm hν hS hsupp hK


end ModifiedCartan
