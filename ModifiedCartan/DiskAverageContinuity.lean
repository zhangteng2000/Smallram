import ModifiedCartan.MovingDiskIntegrals
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.UniformSpace.UniformApproximation

open scoped Topology ENNReal NNReal BoundedContinuousFunction
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan

/-- L1 approximation by bounded continuous functions gives continuity of disk averaging. -/
theorem continuous_diskAverage {f : ℂ → ℝ} (hf : Integrable f) {r : ℝ} (hr : 0 < r) :
    Continuous (diskAverage r f) := by
  apply continuous_of_uniform_approx_of_continuous
  intro W hW
  obtain ⟨ε, hε, hεW⟩ := Metric.mem_uniformity_dist.mp hW
  obtain ⟨δ, hδ, hδε⟩ := exists_pos_mul_lt hε ((Real.pi * r ^ 2)⁻¹)
  obtain ⟨g, hfg, hg⟩ := hf.exists_boundedContinuous_integral_sub_le hδ
  refine ⟨diskAverage r g,
    (diskAverage_lipschitzWith_of_bounded g.continuous.aestronglyMeasurable g.norm_coe_le_norm hr).continuous,
    ?_⟩
  intro z
  apply hεW
  rw [dist_eq_norm]
  have h := norm_diskAverage_sub_le hr (c := z) (T := univ) (subset_univ _) hf.integrableOn hg.integrableOn
  simp only [Measure.restrict_univ] at h
  exact h.trans_lt ((mul_le_mul_of_nonneg_left hfg
    (inv_nonneg.mpr (mul_nonneg Real.pi_pos.le (sq_nonneg r)))).trans_lt hδε)


end ModifiedCartan
