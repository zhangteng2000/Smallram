import FewInflection.Jensen
import Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem

/-!
# The zero and pole count in the fixed-radius logarithmic derivative estimate

The first step of Lemma `logderivbound` compares the unweighted count in a
smaller disk with the logarithmically weighted count in a larger disk.  We
prove that comparison first for an arbitrary nonnegative locally finite
divisor.  The centre is excluded by an explicit zero coefficient hypothesis.
-/

open scoped BigOperators Topology
open Filter Function Function.locallyFinsuppWithin MeromorphicOn Metric Real Set

namespace FewInflection

noncomputable section

/-- The number of points of a nonnegative divisor in a smaller disk, with
multiplicity, is bounded by its outer logarithmic count. -/
theorem divisor_count_mul_log_le_logCounting
    {D : locallyFinsupp ℂ ℤ} (hD : 0 ≤ D) (hD0 : D 0 = 0)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    (∑ᶠ z : ℂ, ((toClosedBall r D) z : ℝ)) * Real.log (R / r) ≤
      D.logCounting R := by
  have hR : 0 < R := hr.trans hrR
  rw [finsum_mul]
  change _ ≤ (∑ᶠ z : ℂ, ((toClosedBall R D) z : ℝ) *
    Real.log (R * ‖z‖⁻¹)) + (D 0 : ℝ) * Real.log R
  rw [hD0, Int.cast_zero, zero_mul, add_zero]
  refine finsum_le_finsum' ?_ ?_ (fun z => ?_)
  · exact (toClosedBall r D).finiteSupport (isCompact_closedBall ..) |>.subset
      (fun _ _ => by simp_all)
  · exact (toClosedBall R D).finiteSupport (isCompact_closedBall ..) |>.subset
      (fun _ _ => by simp_all)
  · by_cases hzR : z ∈ closedBall (0 : ℂ) |R|
    · rw [toClosedBall_eval_within D hzR]
      by_cases hzr : z ∈ closedBall (0 : ℂ) |r|
      · rw [toClosedBall_eval_within D hzr]
        by_cases hz0 : z = 0
        · simp [hz0, hD0]
        · have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
          have hzr' : ‖z‖ ≤ r := by
            simpa [mem_closedBall, dist_zero_right, abs_of_pos hr] using hzr
          apply mul_le_mul_of_nonneg_left _ (Int.cast_nonneg (hD z))
          apply Real.log_le_log (div_pos hR hr)
          rw [← div_eq_mul_inv]
          exact div_le_div_of_nonneg_left hR.le hzn hzr'
      · rw [apply_eq_zero_of_notMem (toClosedBall r D) hzr]
        simp only [Int.cast_zero, zero_mul]
        by_cases hz0 : z = 0
        · simp [hz0]
        · apply mul_nonneg (Int.cast_nonneg (hD z))
          apply Real.log_nonneg
          rw [← div_eq_mul_inv, le_div_iff₀ (norm_pos_iff.mpr hz0), one_mul]
          simpa [mem_closedBall, dist_zero_right, abs_of_pos hR] using hzR
    · have hzr : z ∉ closedBall (0 : ℂ) |r| := by
        intro hz
        apply hzR
        exact closedBall_subset_closedBall (by simpa [abs_of_pos hr, abs_of_pos hR]
          using hrR.le) hz
      simp [apply_eq_zero_of_notMem (toClosedBall r D) hzr,
        apply_eq_zero_of_notMem (toClosedBall R D) hzR]

/-- The quotient form of the preceding estimate. -/
theorem divisor_count_le_logCounting_div_log
    {D : locallyFinsupp ℂ ℤ} (hD : 0 ≤ D) (hD0 : D 0 = 0)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    (∑ᶠ z : ℂ, ((toClosedBall r D) z : ℝ)) ≤
      D.logCounting R / Real.log (R / r) := by
  apply (le_div_iff₀ (Real.log_pos ((one_lt_div hr).mpr hrR))).mpr
  exact divisor_count_mul_log_le_logCounting hD hD0 hr hrR

/-- The two disk counts which occur in the fixed-radius argument can be
combined before any estimate of the characteristic is made. -/
theorem add_divisor_count_mul_log_four_thirds_le_add_logCounting
    {D₁ D₂ : locallyFinsupp ℂ ℤ}
    (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (hD₁0 : D₁ 0 = 0) (hD₂0 : D₂ 0 = 0) :
    ((∑ᶠ z : ℂ, ((toClosedBall 3 D₁) z : ℝ)) +
      (∑ᶠ z : ℂ, ((toClosedBall 3 D₂) z : ℝ))) *
        Real.log (4 / 3) ≤ D₁.logCounting 4 + D₂.logCounting 4 := by
  have h₁ := divisor_count_mul_log_le_logCounting hD₁ hD₁0
    (r := (3 : ℝ)) (R := (4 : ℝ)) (by norm_num) (by norm_num)
  have h₂ := divisor_count_mul_log_le_logCounting hD₂ hD₂0
    (r := (3 : ℝ)) (R := (4 : ℝ)) (by norm_num) (by norm_num)
  nlinarith

/-! The corresponding analytic estimate is already proved by Mathlib's
Jensen API.  Keeping this wrapper in the project gives the exact form used in
the paper's first counting step, with the centre and absolute radii explicit. -/
theorem analytic_divisor_count_le
    {c : ℂ} {r R M : ℝ} {h : ℂ → ℂ}
    (hr : 0 < |r|) (hrR : |r| < |R|) (hM : 1 ≤ M)
    (hhol : AnalyticOnNhd ℂ h (closedBall c |R|)) (h0 : h c ≠ 0)
    (hbound : ∀ z ∈ sphere c |R|, ‖h z‖ ≤ M) :
    (∑ᶠ z : ℂ, ((divisor h (closedBall c |r|)) z : ℝ)) ≤
      Real.log (M / ‖h c‖) / Real.log (R / r) := by
  have hcast := map_finsum (Int.castRingHom ℝ)
    ((divisor h (closedBall c |r|)).finiteSupport (isCompact_closedBall ..))
  have hcast' :
      ((∑ᶠ z : ℂ, (divisor h (closedBall c |r|) z) : ℤ) : ℝ) =
        ∑ᶠ z : ℂ, ((divisor h (closedBall c |r|) z : ℤ) : ℝ) := by
    simpa using hcast
  rw [← hcast']
  exact AnalyticOnNhd.sum_divisor_le hr hrR hM hhol h0 hbound

end

end FewInflection
