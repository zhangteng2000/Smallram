import ModifiedCartan.SobolevLocality
import ModifiedCartan.LocalConvergenceAlgebra

open scoped Topology ENNReal NNReal ContDiff
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan

/-! Convergence infrastructure for `lem:logderivlimit`: uniform convergence on
compact sets implies local Lp convergence, and a common limit on a further
subsequence of every subsequence implies whole-sequence local Lp convergence. -/




theorem tendsto_eLpNorm_of_tendstoUniformlyOn {E : Type*} [NormedAddCommGroup E]
    {f : ℕ → ℂ → E} {g : ℂ → E} {K : Set ℂ} (hK : IsCompact K) (p : ℝ≥0∞)
    (h : TendstoUniformlyOn f g atTop K) :
    Tendsto (fun n => eLpNorm (f n - g) p (volume.restrict K)) atTop (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  have hC : (volume.restrict K univ) ^ p.toReal⁻¹ ≠ ⊤ := by
    apply ENNReal.rpow_ne_top_of_nonneg (by positivity)
    simpa only [Measure.restrict_apply_univ] using hK.measure_ne_top
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.exists_nnreal_pos_mul_lt hC hε.ne'
  have hu := (Metric.tendstoUniformlyOn_iff.mp h) (δ : ℝ) (by exact_mod_cast hδ)
  filter_upwards [hu] with n hn
  have hbound : ∀ᵐ z ∂volume.restrict K, ‖(f n - g) z‖ ≤ (δ : ℝ) := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    simpa only [Pi.sub_apply, ← dist_eq_norm, dist_comm] using (hn z hz).le
  exact (eLpNorm_le_of_ae_bound hbound).trans (by
    simpa only [ENNReal.ofReal_coe_nnreal, mul_comm] using hδε.le)

theorem localLpConvergence_of_tendstoUniformlyOn {E : Type*} [NormedAddCommGroup E]
    {f : ℕ → ℂ → E} {g : ℂ → E} {U : Set ℂ} (p : ℝ≥0∞)
    (hf : ∀ n, ContinuousOn (f n) U) (hg : ContinuousOn g U)
    (h : TendstoUniformlyOn f g atTop U) : LocalLpConvergence p U f g where
  source_mem K hK hKU n := by
    let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
    have hc := (hf n).mono hKU
    obtain ⟨M, hM⟩ := (hK.image_of_continuousOn hc).isBounded.exists_norm_le
    apply MemLp.of_bound (hc.aestronglyMeasurable hK.measurableSet) M
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    exact hM _ (mem_image_of_mem (f n) hz)
  limit_mem K hK hKU := by
    let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
    have hc := hg.mono hKU
    obtain ⟨M, hM⟩ := (hK.image_of_continuousOn hc).isBounded.exists_norm_le
    apply MemLp.of_bound (hc.aestronglyMeasurable hK.measurableSet) M
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    exact hM _ (mem_image_of_mem g hz)
  tendsto K hK hKU := tendsto_eLpNorm_of_tendstoUniformlyOn hK p (h.mono hKU)

theorem LocalLpConvergence.comp_tendsto {E : Type*} [NormedAddCommGroup E]
    {p : ℝ≥0∞} {U : Set ℂ} {f : ℕ → ℂ → E} {g : ℂ → E}
    (h : LocalLpConvergence p U f g) {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop) :
    LocalLpConvergence p U (fun n => f (ns n)) g where
  source_mem K hK hKU n := h.source_mem K hK hKU (ns n)
  limit_mem := h.limit_mem
  tendsto K hK hKU := (h.tendsto K hK hKU).comp hns

theorem localLpConvergence_of_subseq {E : Type*} [NormedAddCommGroup E]
    {p : ℝ≥0∞} {U : Set ℂ} {f : ℕ → ℂ → E} {g : ℂ → E}
    (hf : ∀ K, IsCompact K → K ⊆ U → ∀ n, MemLp (f n) p (volume.restrict K))
    (hsub : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop → ∃ ms : ℕ → ℕ,
      LocalLpConvergence p U (fun n => f (ns (ms n))) g) :
    LocalLpConvergence p U f g := by
  obtain ⟨ms, hms⟩ := hsub id tendsto_id
  refine ⟨hf, hms.limit_mem, ?_⟩
  intro K hK hKU
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms, hms⟩ := hsub ns hns
  exact ⟨ms, hms.tendsto K hK hKU⟩



end ModifiedCartan


