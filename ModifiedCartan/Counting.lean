import ModifiedCartan.NormComparison
import FewInflection.Nevanlinna
import FewInflection.Nevanlinna.CountingBounds

open scoped BigOperators Topology
open Filter Function Function.locallyFinsuppWithin MeromorphicOn Metric Real Set

namespace ModifiedCartan

noncomputable section

/-- Unweighted zero count, including the multiplicity at the origin.
LaTeX context: `eq:zero-count-definition`. -/
def zeroCount (H : ℂ → ℂ) (r : ℝ) : ℝ :=
  ∑ᶠ z : ℂ, ((toClosedBall r (divisor H Set.univ)) z : ℝ)

theorem entire_pole_count_eq_zero {H : ℂ → ℂ} (hH : Differentiable ℂ H) (r : ℝ) :
    ValueDistribution.logCounting H (⊤ : WithTop ℂ) r = 0 := by
  have ha := Complex.analyticOnNhd_univ_iff_differentiable.mpr hH
  rw [ValueDistribution.logCounting_top, negPart_eq_zero.mpr ha.divisor_nonneg]
  simp

namespace Paper

/-- LaTeX label `eq:zerojensen`. Zeros at the centre are allowed. -/
theorem eq_zerojensen {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    {r : ℝ} (hr : r ≠ 0) :
    Real.circleAverage (fun z => Real.log ‖H z‖) 0 r =
      ValueDistribution.logCounting H (0 : WithTop ℂ) r +
        Real.log ‖meromorphicTrailingCoeffAt H 0‖ := by
  have ha := Complex.analyticOnNhd_univ_iff_differentiable.mpr hH
  have h := ValueDistribution.logCounting_zero_sub_logCounting_top_eq_circleAverage_sub_const
    (meromorphicOn_univ.mp ha.meromorphicOn) hr
  change ValueDistribution.logCounting H (0 : WithTop ℂ) r -
    ValueDistribution.logCounting H (⊤ : WithTop ℂ) r = _ at h
  rw [entire_pole_count_eq_zero hH r] at h
  linarith

end Paper

theorem divisor_pointwise_count_bound
    {D : locallyFinsupp ℂ ℤ} (hD : 0 ≤ D) {r R : ℝ}
    (hr : 1 ≤ r) (hrR : r < R) (z : ℂ) :
    ((toClosedBall r D) z : ℝ) * Real.log (R / r) ≤
      ((toClosedBall R D) z : ℝ) * Real.log (R * ‖z‖⁻¹) +
        if z = 0 then (D 0 : ℝ) * Real.log R else 0 := by
  have hrpos : 0 < r := zero_lt_one.trans_le hr
  have hR : 0 < R := hrpos.trans hrR
  by_cases hz0 : z = 0
  · subst z
    rw [toClosedBall_eval_within D (by simp)]
    simp only [norm_zero, inv_zero, mul_zero, Real.log_zero, mul_zero,
      zero_add]
    apply mul_le_mul_of_nonneg_left _ (Int.cast_nonneg (hD 0))
    apply Real.log_le_log (div_pos hR hrpos)
    apply (div_le_iff₀ hrpos).mpr
    nlinarith
  · simp only [hz0, ite_false, add_zero]
    by_cases hzR : z ∈ closedBall (0 : ℂ) |R|
    · rw [toClosedBall_eval_within D hzR]
      by_cases hzr : z ∈ closedBall (0 : ℂ) |r|
      · rw [toClosedBall_eval_within D hzr]
        apply mul_le_mul_of_nonneg_left _ (Int.cast_nonneg (hD z))
        apply Real.log_le_log (div_pos hR hrpos)
        rw [← div_eq_mul_inv]
        apply div_le_div_of_nonneg_left hR.le (norm_pos_iff.mpr hz0)
        simpa [mem_closedBall, dist_zero_right, abs_of_pos hrpos] using hzr
      · rw [apply_eq_zero_of_notMem (toClosedBall r D) hzr]
        simp only [Int.cast_zero, zero_mul]
        apply mul_nonneg (Int.cast_nonneg (hD z))
        apply Real.log_nonneg
        rw [← div_eq_mul_inv, le_div_iff₀ (norm_pos_iff.mpr hz0), one_mul]
        simpa [mem_closedBall, dist_zero_right, abs_of_pos hR] using hzR
    · have hzr : z ∉ closedBall (0 : ℂ) |r| := by
        intro hz
        apply hzR
        apply closedBall_subset_closedBall _ hz
        simpa [abs_of_pos hrpos, abs_of_pos hR] using hrR.le
      simp [apply_eq_zero_of_notMem (toClosedBall r D) hzr,
        apply_eq_zero_of_notMem (toClosedBall R D) hzR]

theorem divisor_count_bound_with_origin
    {D : locallyFinsupp ℂ ℤ} (hD : 0 ≤ D) {r R : ℝ}
    (hr : 1 ≤ r) (hrR : r < R) :
    (∑ᶠ z : ℂ, ((toClosedBall r D) z : ℝ)) * Real.log (R / r) ≤
      D.logCounting R := by
  classical
  have hfiniteR : Function.HasFiniteSupport (fun z : ℂ =>
      ((toClosedBall R D) z : ℝ) * Real.log (R * ‖z‖⁻¹)) :=
    (toClosedBall R D).finiteSupport (isCompact_closedBall ..) |>.subset
      (fun _ _ => by simp_all)
  have hcenter : Function.HasFiniteSupport (fun z : ℂ =>
      if z = 0 then (D 0 : ℝ) * Real.log R else 0) := by
    apply (Set.finite_singleton (0 : ℂ)).subset
    intro z hz
    by_contra hn
    simp only [Set.mem_singleton_iff] at hn
    simp [hn] at hz
  have hsum := finsum_le_finsum'
    ((toClosedBall r D).finiteSupport (isCompact_closedBall ..) |>.subset
      (fun _ _ => by simp_all))
    ((hfiniteR.union hcenter).subset (Function.support_add _ _))
    (divisor_pointwise_count_bound hD hr hrR)
  rw [← finsum_mul, finsum_add_distrib hfiniteR hcenter] at hsum
  have hsingle : (∑ᶠ z : ℂ, if z = 0 then (D 0 : ℝ) * Real.log R else 0) =
      (D 0 : ℝ) * Real.log R := by
    rw [finsum_eq_single _ 0 (by intro z hz; simp [hz])]
    simp
  rw [hsingle] at hsum
  exact hsum

namespace Paper

/-- LaTeX label `eq:countbound`. The centre may be a zero of any multiplicity. -/
theorem eq_countbound {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    {r : ℝ} (hr : 1 ≤ r) :
    zeroCount H r * Real.log 2 ≤
      ValueDistribution.logCounting H (0 : WithTop ℂ) (2 * r) := by
  have ha := Complex.analyticOnNhd_univ_iff_differentiable.mpr hH
  have hd := ha.divisor_nonneg
  have h := divisor_count_bound_with_origin hd hr (R := 2 * r) (by linarith)
  have hratio : 2 * r / r = 2 := by field_simp
  rw [hratio] at h
  simpa only [zeroCount, ValueDistribution.logCounting_zero,
    posPart_eq_self.mpr hd] using h

/-- LaTeX label `eq:quotientbound`, with the manuscript's Euclidean norm. -/
theorem eq_quotientbound {n : ℕ} (f : Curve n) (j l : Index n)
    (hj0 : f.coord j 0 ≠ 0) {r : ℝ} (hr : 1 ≤ r) :
    ValueDistribution.characteristic (fun z => f.coord l z / f.coord j z) ⊤ r ≤
      characteristic f r + Real.log (euclideanNorm (f.vector 0)) -
        Real.log ‖f.coord j 0‖ := by
  have h := FewInflection.quotient_characteristic_le_curve f j l hj0 hr
  have hm := circleAverage_log_norm_le f r
  unfold characteristic FewInflection.characteristic at *
  linarith

end Paper
end
end ModifiedCartan

