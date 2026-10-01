import ModifiedCartan.ExceptionalRadii
import ModifiedCartan.CountingPowerEnvelope
import ModifiedCartan.TaylorWronskianGrowth

open scoped Topology
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- Dominated convergence for the literal counting integrals in
`lem:entire-majorant`, with the integrable power bound proved from the
component orders and with only a countable exceptional set of radii. -/
theorem taylorWronskian_counting_integral_tendsto {n : ℕ}
    {y : Fin (n + 1) → ℂ → ℂ} (hy : ∀ j, Differentiable ℂ (y j))
    (horder : ∀ j, entireOrder (y j) < 1)
    (hjets : ∀ i j : Fin (n + 1), iteratedDeriv i.val (y j) 0 = if i = j then 1 else 0)
    {r : ℝ} (hr : 0 < r) :
    Tendsto (fun N => ∫ t in Ioi 0, ValueDistribution.logCounting
      (FewInflection.wronskian n (fun j z => (FewInflection.taylorPolynomial (y j) 0 N).eval z))
        (0 : WithTop ℂ) t / (r + t) ^ 2) atTop
      (𝓝 (∫ t in Ioi 0, ValueDistribution.logCounting (FewInflection.wronskian n y)
        (0 : WithTop ℂ) t / (r + t) ^ 2)) := by
  obtain ⟨σ, hσ0, hσ1, hσ⟩ := finite_entireOrder_exists_exponent_lt_one horder
  obtain ⟨D, hD, hbound⟩ := entire_taylorWronskian_posLog_bound hy hσ0.le hσ
  let W : ℕ → ℂ → ℂ := fun N => FewInflection.wronskian n
    (fun j z => (FewInflection.taylorPolynomial (y j) 0 N).eval z)
  have hW (N : ℕ) : Differentiable ℂ (W N) := entire_wronskian_differentiable
    (fun j => (FewInflection.taylorPolynomial (y j) 0 N).differentiable)
  have hW0 (N : ℕ) (hN : n < N) : W N 0 = 1 := entire_taylorPolynomial_wronskian_zero hN hjets
  have hlarge : ∀ᶠ N in atTop, n < N := eventually_gt_atTop n
  apply tendsto_integral_filter_of_dominated_convergence
    (fun t : ℝ => D * (max 1 (t ^ σ) / (r + t) ^ 2))
  · filter_upwards [hlarge] with N hN
    have h0 : W N 0 ≠ 0 := by rw [hW0 N hN]; exact one_ne_zero
    have hm : AEStronglyMeasurable (fun t : ℝ => ((r + t) ^ 2)⁻¹)
        (volume.restrict (Ioi (0 : ℝ))) := by fun_prop
    simpa only [div_eq_mul_inv, W, Pi.mul_apply] using!
      (entire_logCounting_aestronglyMeasurableOn (hW N) h0).mul hm
  · filter_upwards [hlarge] with N hN
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have h0 : W N 0 ≠ 0 := by rw [hW0 N hN]; exact one_ne_zero
    rw [Real.norm_of_nonneg (div_nonneg (entire_logCounting_nonneg (hW N) h0 ht) (sq_nonneg _))]
    have hb := logCounting_le_power_envelope (hW N) (hW0 N hN) hD.le (hbound N) ht
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hb (sq_nonneg (r + t))
  · exact (power_counting_kernel_integrable hσ0.le hσ1 hr).const_mul D
  · filter_upwards [taylorWronskian_logCounting_ae_tendsto hy hjets] with t ht
    exact ht.div_const ((r + t) ^ 2)

end ModifiedCartan
#print axioms ModifiedCartan.taylorWronskian_counting_integral_tendsto
