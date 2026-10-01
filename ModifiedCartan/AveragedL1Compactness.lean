import ModifiedCartan.UniformLipschitzCompactness
import ModifiedCartan.ApproximationCompactness
import ModifiedCartan.L1CompactnessMetric

open scoped Topology ENNReal NNReal
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan

theorem totallyBounded_l1_range_of_uniform_lipschitz {K : Set ℂ} (hK : IsCompact K)
    {f : ℕ → ℂ → ℝ} (hf : ∀ n, IntegrableOn (f n) K volume)
    {L : ℝ≥0} (hL : ∀ n, LipschitzWith L (f n)) {B : ℝ}
    (hB : ∀ n z, z ∈ K → ‖f n z‖ ≤ B) :
    TotallyBounded (range (fun n => (hf n).toL1 (μ := volume.restrict K) (f n))) := by
  apply totallyBounded_of_cauchy_subsequences
  intro v hv
  choose k hk using hv
  obtain ⟨ns, hns, g, hconv⟩ := exists_uniformly_convergent_subsequence_of_lipschitz hK
    (fun n => hL (k n)) (fun n => hB (k n))
  refine ⟨ns, hns, ?_⟩
  have hc := uniformCauchySeqOn_toL1 hK (fun n => hf (k (ns n))) hconv.uniformCauchySeqOn
  convert hc using 1
  funext n
  exact (hk (ns n)).symm

theorem totallyBounded_l1_range_diskAverage_twice {K : Set ℂ} (hK : IsCompact K)
    {f : ℕ → ℂ → ℝ} (hf : ∀ n, Integrable (f n))
    {B : ℝ} (hB : ∀ n, (∫ z, ‖f n z‖) ≤ B) {r : ℝ} (hr : 0 < r) :
    TotallyBounded (range (fun n =>
      ((diskAverage_integrable hr.le (diskAverage_integrable hr.le (hf n))).integrableOn).toL1
        (μ := volume.restrict K) (diskAverage r (diskAverage r (f n))))) := by
  apply totallyBounded_l1_range_of_uniform_lipschitz hK
  · exact fun n => diskAverage_twice_lipschitzWith (hf n) hr (hB n)
  · intro n z _
    apply norm_diskAverage_le_of_bound hr (C := (Real.pi * r ^ 2)⁻¹ * B) _ z
    intro w
    exact (norm_diskAverage_le_integral_norm (hf n) hr w).trans
      (mul_le_mul_of_nonneg_left (hB n)
        (inv_nonneg.mpr (mul_nonneg Real.pi_pos.le (sq_nonneg r))))


end ModifiedCartan
