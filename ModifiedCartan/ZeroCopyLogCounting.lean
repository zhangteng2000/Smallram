import ModifiedCartan.ZeroCopiesCount
import Mathlib.Topology.Algebra.InfiniteSum.Real

open scoped Topology BigOperators
open Filter Set Metric Function MeromorphicOn Function.locallyFinsuppWithin
set_option autoImplicit false
namespace ModifiedCartan

theorem posLog_div_norm_eq_zero_of_lt {R : ℝ} (hR : 0 ≤ R) {z : ℂ}
    (hz : R < ‖z‖) : Real.posLog (R / ‖z‖) = 0 := by
  apply (Real.posLog_eq_zero_iff _).mpr
  rw [abs_of_nonneg (div_nonneg hR (norm_nonneg z))]
  exact (div_le_one (hR.trans_lt hz)).mpr hz.le

theorem zeroCopy_posLog_hasFiniteSupport {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {R : ℝ} (hR : 0 ≤ R) :
    Function.HasFiniteSupport (fun a : entireZeroCopies f => Real.posLog (R / ‖a.1‖)) := by
  have hfinite : {a : entireZeroCopies f | ‖a.1‖ ≤ R}.Finite :=
    @Set.toFinite (entireZeroCopies f) {a | ‖a.1‖ ≤ R}
      (zeroCopiesInClosedBall_finite hf hR)
  apply hfinite.subset
  intro a ha
  by_contra h
  exact ha (posLog_div_norm_eq_zero_of_lt hR (lt_of_not_ge h))

/-- The zero-sum identity in LaTeX `cor:convolution`: the actual logarithmic counting function is
the finite-at-each-radius sum over the analytic zero multiplicities. -/
theorem entire_logCounting_eq_tsum_zeroCopies {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) {R : ℝ} (hR : 0 < R) :
    ValueDistribution.logCounting f (0 : WithTop ℂ) R =
      ∑' a : entireZeroCopies f, Real.posLog (R / ‖a.1‖) := by
  classical
  have hsum : Summable (fun a : entireZeroCopies f => Real.posLog (R / ‖a.1‖)) :=
    summable_of_hasFiniteSupport (zeroCopy_posLog_hasFiniteSupport hf hR.le)
  have hD0 : divisor f univ 0 = 0 := by
    rw [entire_divisor_eq_analyticMultiplicity hf,
      (hf.analyticAt 0).analyticOrderAt_eq_zero.mpr h0]
    simp
  have hfinite : (∑' z : ℂ, ((analyticOrderAt f z).toNat : ℝ) * Real.posLog (R / ‖z‖)) =
      ∑ z ∈ diskSupport (divisor f univ) R,
        ((analyticOrderAt f z).toNat : ℝ) * Real.posLog (R / ‖z‖) := by
    apply tsum_eq_sum
    intro z hz
    by_cases hdz : divisor f univ z = 0
    · have hm : (analyticOrderAt f z).toNat = 0 := by
        simpa only [entire_divisor_eq_analyticMultiplicity hf, Nat.cast_eq_zero] using hdz
      simp [hm]
    · have hnorm : R < ‖z‖ := by
        by_contra hn
        apply hz
        apply mem_diskSupport_of_ne
        rw [toClosedBall_eval_within _ (by
          simpa only [mem_closedBall, dist_zero_right, abs_of_pos hR] using le_of_not_gt hn)]
        exact hdz
      rw [posLog_div_norm_eq_zero_of_lt hR.le hnorm, mul_zero]
  rw [hsum.tsum_sigma]
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hfinite, ValueDistribution.logCounting_zero,
    posPart_eq_self.mpr (Complex.analyticOnNhd_univ_iff_differentiable.mpr hf).divisor_nonneg,
    divisor_logCounting_eq_sum hR, hD0]
  simp only [Int.cast_zero, zero_mul, add_zero]
  rw [← Finset.sum_erase_add _ _ (zero_mem_diskSupport (divisor f univ) R)]
  simp only [norm_zero, div_zero, Real.posLog_zero, mul_zero, add_zero]
  apply Finset.sum_congr rfl
  intro z hz
  have hz0 : z ≠ 0 := (Finset.mem_erase.mp hz).1
  have hnorm := norm_le_of_mem_diskSupport hR.le (Finset.mem_of_mem_erase hz)
  rw [Real.posLog_eq_log (by
    rw [abs_of_pos (div_pos hR (norm_pos_iff.mpr hz0))]
    exact (one_le_div (norm_pos_iff.mpr hz0)).mpr hnorm),
    entire_divisor_eq_analyticMultiplicity hf]
  norm_cast

end ModifiedCartan
#print axioms ModifiedCartan.entire_logCounting_eq_tsum_zeroCopies
