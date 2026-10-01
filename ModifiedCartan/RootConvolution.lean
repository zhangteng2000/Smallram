import ModifiedCartan.ZeroCopyLogCounting
import ModifiedCartan.RootMajorantProduct
import ModifiedCartan.IntegrableSum
import ModifiedCartan.RootKernel
import ModifiedCartan.WronskianReciprocalRoots

open scoped Topology BigOperators
open Filter Set MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- The exact Tonelli identity used in LaTeX `cor:convolution`, including
integrability of the actual logarithmic counting function against its kernel. -/
theorem entire_root_product_convolution {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hs : Summable (fun a : entireZeroCopies f => ‖a.1‖⁻¹))
    {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t => ValueDistribution.logCounting f (0 : WithTop ℂ) t / (r + t) ^ 2)
      (Ioi 0) ∧
      Real.log (rootMajorantProduct f r) =
        r * ∫ t in Ioi 0, ValueDistribution.logCounting f (0 : WithTop ℂ) t / (r + t) ^ 2 := by
  letI : Countable (entireZeroCopies f) := entireZeroCopies_countable hf
  let F : entireZeroCopies f → ℝ → ℝ := fun a t => Real.posLog (t / ‖a.1‖) / (r + t) ^ 2
  have hF (a : entireZeroCopies f) : IntegrableOn (F a) (Ioi 0) :=
    (root_kernel_identity hr (entireZeroCopies_ne_zero hf h0 a)).1
  have hvalue (a : entireZeroCopies f) : (∫ t in Ioi 0, F a t) =
      Real.log (1 + r / ‖a.1‖) / r := by
    apply (eq_div_iff hr.ne').mpr
    simpa only [mul_comm] using (root_kernel_identity hr (entireZeroCopies_ne_zero hf h0 a)).2
  have hnorm (a : entireZeroCopies f) (t : ℝ) : ‖F a t‖ = F a t :=
    Real.norm_of_nonneg (div_nonneg Real.posLog_nonneg (sq_nonneg _))
  have hsum : Summable (fun a => ∫ t in Ioi 0, ‖F a t‖) := by
    simp_rw [hnorm, hvalue]
    exact (rootMajorant_log_summable hs r).div_const r
  have hi : IntegrableOn (fun t => ∑' a, F a t) (Ioi 0) :=
    integrable_real_tsum_of_summable_integral_norm hF hsum
  have heq (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      (∑' a, F a t) = ValueDistribution.logCounting f (0 : WithTop ℂ) t / (r + t) ^ 2 := by
    dsimp only [F]
    rw [tsum_div_const, entire_logCounting_eq_tsum_zeroCopies hf h0 ht]
  refine ⟨hi.congr_fun heq measurableSet_Ioi, ?_⟩
  rw [log_rootMajorantProduct hs hr.le,
    ← setIntegral_congr_fun measurableSet_Ioi heq,
    ← integral_tsum_of_summable_integral_norm hF hsum]
  simp_rw [hvalue]
  rw [tsum_div_const, mul_div_cancel₀ _ hr.ne']

/-- The root-product/convolution equality of `cor:convolution` under
the original normalized entire-system hypotheses. The component majorant
is proved separately before concluding that corollary. -/
theorem normalized_wronskian_product_convolution {n : ℕ}
    {y : Fin (n + 1) → ℂ → ℂ} (hy : ∀ j, Differentiable ℂ (y j))
    (horder : ∀ j, entireOrder (y j) < 1)
    (hjets : ∀ i j : Fin (n + 1), iteratedDeriv i.val (y j) 0 = if i = j then 1 else 0)
    {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t => ValueDistribution.logCounting (FewInflection.wronskian n y)
      (0 : WithTop ℂ) t / (r + t) ^ 2) (Ioi 0) ∧
      Real.log (rootMajorantProduct (FewInflection.wronskian n y) r) =
        r * ∫ t in Ioi 0, ValueDistribution.logCounting (FewInflection.wronskian n y)
          (0 : WithTop ℂ) t / (r + t) ^ 2 := by
  apply entire_root_product_convolution (entire_wronskian_differentiable hy)
    (by rw [wronskian_zero_of_initial_jets hjets]; exact one_ne_zero)
    (normalized_entire_system_reciprocal_roots hy horder hjets).1 hr

end ModifiedCartan
#print axioms ModifiedCartan.entire_root_product_convolution
#print axioms ModifiedCartan.normalized_wronskian_product_convolution
