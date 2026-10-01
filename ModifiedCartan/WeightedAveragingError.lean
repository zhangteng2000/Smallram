import ModifiedCartan.DiskAverageApproximation

open scoped Topology ENNReal NNReal
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan

theorem integral_mul_diskAverage_twice_sub {r : ℝ} (hr : 0 < r) {f χ : ℂ → ℝ}
    (hf : Integrable f) (hχ : Integrable χ) {C : ℝ} (hχbound : ∀ z, ‖χ z‖ ≤ C) :
    (∫ z, χ z * (diskAverage r (diskAverage r f) z - f z)) =
      ∫ z, f z * (diskAverage r (diskAverage r χ) z - χ z) := by
  have hAf := diskAverage_integrable hr.le (diskAverage_integrable hr.le hf)
  have hAχ := diskAverage_integrable hr.le (diskAverage_integrable hr.le hχ)
  have hAχbound : ∀ z, ‖diskAverage r (diskAverage r χ) z‖ ≤ C :=
    fun z => norm_diskAverage_le_of_bound hr
      (fun w => norm_diskAverage_le_of_bound hr hχbound w) z
  simp_rw [mul_sub]
  rw [integral_sub (hAf.bdd_mul hχ.aestronglyMeasurable (Eventually.of_forall hχbound))
      (hf.bdd_mul hχ.aestronglyMeasurable (Eventually.of_forall hχbound)),
    integral_sub (hf.mul_bdd hAχ.aestronglyMeasurable (Eventually.of_forall hAχbound))
      (hf.mul_bdd hχ.aestronglyMeasurable (Eventually.of_forall hχbound)),
    integral_mul_diskAverage_twice hr hf hχ hχbound]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => mul_comm _ _)

/-- The error is transferred to a Lipschitz test function, retaining a uniform L1 bound. -/
theorem norm_integral_mul_diskAverage_twice_sub_le {r : ℝ} (hr : 0 < r)
    {f χ : ℂ → ℝ} (hf : Integrable f) (hχ : Integrable χ)
    {C : ℝ} (hχbound : ∀ z, ‖χ z‖ ≤ C) {L : ℝ≥0} (hL : LipschitzWith L χ) :
    ‖∫ z, χ z * (diskAverage r (diskAverage r f) z - f z)‖ ≤
      2 * (L : ℝ) * r * ∫ z, ‖f z‖ := by
  rw [integral_mul_diskAverage_twice_sub hr hf hχ hχbound]
  have hdiff : AEStronglyMeasurable
      (fun z => diskAverage r (diskAverage r χ) z - χ z) volume :=
    (diskAverage_integrable hr.le (diskAverage_integrable hr.le hχ)).aestronglyMeasurable.sub
      hχ.aestronglyMeasurable
  have hbound : ∀ z, ‖diskAverage r (diskAverage r χ) z - χ z‖ ≤ 2 * (L : ℝ) * r :=
    lipschitz_norm_diskAverage_twice_sub_le hL hχ hr
  have hint := hf.mul_bdd hdiff (Eventually.of_forall hbound)
  calc
    _ ≤ ∫ z, ‖f z * (diskAverage r (diskAverage r χ) z - χ z)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ z, ‖f z‖ * (2 * (L : ℝ) * r) :=
      integral_mono_ae hint.norm (hf.norm.mul_const _) (Eventually.of_forall (fun z => by
        simp only [norm_mul]
        exact mul_le_mul_of_nonneg_left (hbound z) (norm_nonneg _)))
    _ = _ := by rw [integral_mul_const]; ring


end ModifiedCartan
