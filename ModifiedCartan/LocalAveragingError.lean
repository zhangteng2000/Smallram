import ModifiedCartan.WeightedAveragingError

open scoped Topology ENNReal NNReal
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan

/-- Positivity on the cutoff support converts the signed error into a local L1 error. -/
theorem integral_norm_diskAverage_twice_sub_le {r : ℝ} (hr : 0 < r)
    {f χ : ℂ → ℝ} (hf : Integrable f) (hχ : Integrable χ)
    {L : ℝ≥0} (hL : LipschitzWith L χ)
    (hχnonneg : ∀ z, 0 ≤ χ z) (hχbound : ∀ z, ‖χ z‖ ≤ 1)
    {K : Set ℂ} (hK : MeasurableSet K) (hχone : ∀ z ∈ K, χ z = 1)
    (hpos : ∀ᵐ z, χ z ≠ 0 → f z ≤ diskAverage r (diskAverage r f) z) :
    (∫ z in K, ‖diskAverage r (diskAverage r f) z - f z‖) ≤
      2 * (L : ℝ) * r * ∫ z, ‖f z‖ := by
  have hdiff := (diskAverage_integrable hr.le (diskAverage_integrable hr.le hf)).sub hf
  have hweighted := hdiff.bdd_mul hχ.aestronglyMeasurable (Eventually.of_forall hχbound)
  have hineq : (∫ z in K, ‖diskAverage r (diskAverage r f) z - f z‖) ≤
      ∫ z, χ z * (diskAverage r (diskAverage r f) z - f z) := by
    rw [← integral_indicator hK]
    apply integral_mono_ae (hdiff.norm.indicator hK) hweighted
    filter_upwards [hpos] with z hz
    change K.indicator (fun w => ‖diskAverage r (diskAverage r f) w - f w‖) z ≤
      χ z * (diskAverage r (diskAverage r f) z - f z)
    by_cases hzK : z ∈ K
    · have hne : χ z ≠ 0 := by rw [hχone z hzK]; norm_num
      simp only [indicator_of_mem hzK, hχone z hzK, one_mul,
        Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (hz hne)), le_refl]
    · rw [indicator_of_notMem hzK]
      by_cases hzero : χ z = 0
      · rw [hzero, zero_mul]
      · exact mul_nonneg (hχnonneg z) (sub_nonneg.mpr (hz hzero))
  exact hineq.trans ((le_abs_self _).trans
    (norm_integral_mul_diskAverage_twice_sub_le hr hf hχ hχbound hL))


end ModifiedCartan
