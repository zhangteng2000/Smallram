import ModifiedCartan.ZeroCopyLogCounting

open scoped Topology BigOperators
open Filter Set Metric Function MeromorphicOn Function.locallyFinsuppWithin
set_option autoImplicit false
namespace ModifiedCartan

/-- Counting weight with the origin contribution kept explicitly.
Required for LaTeX `eq:translated-count`. -/
noncomputable def rootCountingWeight (R : ℝ) (z : ℂ) : ℝ :=
  if z = 0 then Real.log R else Real.posLog (R / ‖z‖)

theorem rootCountingWeight_eq_zero_of_lt {R : ℝ} (hR : 0 ≤ R) {z : ℂ}
    (hz : R < ‖z‖) : rootCountingWeight R z = 0 := by
  have hn : z ≠ 0 := norm_pos_iff.mp (hR.trans_lt hz)
  rw [rootCountingWeight, if_neg hn, posLog_div_norm_eq_zero_of_lt hR hz]

theorem zeroCopy_weight_hasFiniteSupport {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {R : ℝ} (hR : 0 ≤ R) :
    Function.HasFiniteSupport (fun a : entireZeroCopies f => rootCountingWeight R a.1) := by
  have hfinite : {a : entireZeroCopies f | ‖a.1‖ ≤ R}.Finite :=
    @Set.toFinite (entireZeroCopies f) {a | ‖a.1‖ ≤ R}
      (zeroCopiesInClosedBall_finite hf hR)
  apply hfinite.subset
  intro a ha
  by_contra h
  exact ha (rootCountingWeight_eq_zero_of_lt hR (lt_of_not_ge h))

/-- The actual repeated-zero counting sum, including arbitrary
multiplicity at the origin. No normalization of f(0) is assumed. -/
theorem entire_logCounting_eq_tsum_weights {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {R : ℝ} (hR : 0 < R) :
    ValueDistribution.logCounting f (0 : WithTop ℂ) R =
      ∑' a : entireZeroCopies f, rootCountingWeight R a.1 := by
  classical
  have hsum : Summable (fun a : entireZeroCopies f => rootCountingWeight R a.1) :=
    summable_of_hasFiniteSupport (zeroCopy_weight_hasFiniteSupport hf hR.le)
  have hfinite : (∑' z : ℂ, ((analyticOrderAt f z).toNat : ℝ) * rootCountingWeight R z) =
      ∑ z ∈ diskSupport (divisor f univ) R,
        ((analyticOrderAt f z).toNat : ℝ) * rootCountingWeight R z := by
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
      rw [rootCountingWeight_eq_zero_of_lt hR.le hnorm, mul_zero]
  have hsplit : (∑ z ∈ diskSupport (divisor f univ) R,
        ((analyticOrderAt f z).toNat : ℝ) * rootCountingWeight R z) =
      (∑ z ∈ (diskSupport (divisor f univ) R).erase 0,
        ((analyticOrderAt f z).toNat : ℝ) * rootCountingWeight R z) +
      ((analyticOrderAt f 0).toNat : ℝ) * Real.log R := by
    rw [← Finset.sum_erase_add _ _ (zero_mem_diskSupport (divisor f univ) R)]
    simp [rootCountingWeight]
  rw [hsum.tsum_sigma]
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hfinite, hsplit, ValueDistribution.logCounting_zero,
    posPart_eq_self.mpr (Complex.analyticOnNhd_univ_iff_differentiable.mpr hf).divisor_nonneg,
    divisor_logCounting_eq_sum hR]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro z hz
    have hz0 : z ≠ 0 := (Finset.mem_erase.mp hz).1
    have hnorm := norm_le_of_mem_diskSupport hR.le (Finset.mem_of_mem_erase hz)
    rw [rootCountingWeight, if_neg hz0, Real.posLog_eq_log (by
      rw [abs_of_pos (div_pos hR (norm_pos_iff.mpr hz0))]
      exact (one_le_div (norm_pos_iff.mpr hz0)).mpr hnorm),
      entire_divisor_eq_analyticMultiplicity hf]
    norm_cast
  · rw [entire_divisor_eq_analyticMultiplicity hf]
    norm_cast

theorem rootCountingWeight_nonneg {R : ℝ} (hR : 1 ≤ R) (z : ℂ) :
    0 ≤ rootCountingWeight R z := by
  unfold rootCountingWeight
  split_ifs
  · exact Real.log_nonneg hR
  · exact Real.posLog_nonneg

end ModifiedCartan
#print axioms ModifiedCartan.entire_logCounting_eq_tsum_weights
