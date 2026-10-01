import ModifiedCartan.DivisorPolynomial
import ModifiedCartan.Counting

open scoped Topology BigOperators Classical
open Filter MeasureTheory Set Metric MeromorphicOn Function Function.locallyFinsuppWithin
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

theorem open_disk_divisor_le_closed_count {F : ℂ → ℂ}
    (hF : Differentiable ℂ F) {R : ℝ} (hR : 0 < R) :
    (∑ᶠ a : ℂ, (divisor F (ball 0 R) a : ℝ)) ≤ zeroCount F R := by
  have hA := Complex.analyticOnNhd_univ_iff_differentiable.mpr hF
  have hclosed := hA.mono (subset_univ (closedBall (0 : ℂ) R))
  have hfinite := hclosed.meromorphicOn.divisor_ball_support_finite
  let G := toClosedBall R (divisor F univ)
  have hG : G.support.Finite := G.finiteSupport (isCompact_closedBall ..)
  have hGn : 0 ≤ G := by
    change 0 ≤ toClosedBall R (divisor F univ)
    rw [← toClosedBall_divisor (fun z => hA.meromorphicOn z (mem_univ z)), abs_of_pos hR]
    exact hclosed.divisor_nonneg
  apply finsum_le_finsum'
    (hfinite.subset (fun a ha => by simpa only [mem_support, ne_eq, Int.cast_eq_zero] using ha))
    (hG.subset (fun a ha => by simpa only [mem_support, ne_eq, Int.cast_eq_zero] using ha))
  intro a
  change (divisor F (ball 0 R) a : ℝ) ≤ (G a : ℝ)
  by_cases ha : a ∈ ball (0 : ℂ) R
  · have hac : a ∈ closedBall (0 : ℂ) |R| := by
      simpa only [abs_of_pos hR] using ball_subset_closedBall ha
    change (divisor F (ball 0 R) a : ℝ) ≤ (G a : ℝ)
    dsimp [G]
    rw [toClosedBall_eval_within _ hac,
      (hA.mono (subset_univ (ball (0 : ℂ) R))).meromorphicOn.divisor_apply ha,
      hA.meromorphicOn.divisor_apply (mem_univ a)]
  · rw [apply_eq_zero_of_notMem (divisor F (ball 0 R)) ha, Int.cast_zero]
    exact Int.cast_nonneg (hGn a)

theorem finiteDivisorPolynomial_degree_count_bound {F : ℂ → ℂ}
    (hF : Differentiable ℂ F) {R : ℝ} (hR : 1 ≤ R)
    (hfinite : (divisor F (ball 0 R)).support.Finite) :
    ((finiteDivisorPolynomial (divisor F (ball 0 R)) hfinite).natDegree : ℝ) *
      Real.log 2 ≤ ValueDistribution.logCounting F (0 : WithTop ℂ) (2 * R) := by
  have hA := Complex.analyticOnNhd_univ_iff_differentiable.mpr hF
  rw [finiteDivisorPolynomial_natDegree_cast _ _ (hA.mono (subset_univ _)).divisor_nonneg]
  exact (mul_le_mul_of_nonneg_right
    (open_disk_divisor_le_closed_count hF (zero_lt_one.trans_le hR))
    (Real.log_nonneg (by norm_num))).trans (Paper.eq_countbound hF hR)

theorem open_disk_logCounting_term {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {R : ℝ} (hR : 0 < R) (a : ℂ) :
    (divisor F (ball 0 R) a : ℝ) * (Real.log R - Real.log ‖a‖) =
      (toClosedBall R (divisor F univ) a : ℝ) * Real.log (R * ‖a‖⁻¹) +
        if a = 0 then (divisor F univ 0 : ℝ) * Real.log R else 0 := by
  have hA := Complex.analyticOnNhd_univ_iff_differentiable.mpr hF
  have hAB := hA.mono (subset_univ (ball (0 : ℂ) R))
  by_cases ha0 : a = 0
  · subst a
    rw [hAB.meromorphicOn.divisor_apply (mem_ball_self hR),
      hA.meromorphicOn.divisor_apply (mem_univ 0)]
    simp
  · simp only [ha0, ite_false, add_zero]
    by_cases ha : a ∈ ball (0 : ℂ) R
    · have hac : a ∈ closedBall (0 : ℂ) |R| := by
        simpa only [abs_of_pos hR] using ball_subset_closedBall ha
      rw [toClosedBall_eval_within _ hac,
        hAB.meromorphicOn.divisor_apply ha,
        hA.meromorphicOn.divisor_apply (mem_univ a),
        Real.log_mul hR.ne' (inv_ne_zero (norm_ne_zero_iff.mpr ha0)), Real.log_inv]
      ring
    · rw [apply_eq_zero_of_notMem (divisor F (ball 0 R)) ha, Int.cast_zero, zero_mul]
      by_cases hac : a ∈ closedBall (0 : ℂ) |R|
      · have hnorm : ‖a‖ = R := by
          have hle : ‖a‖ ≤ R := by
            simpa only [mem_closedBall, dist_zero_right, abs_of_pos hR] using hac
          have hge : R ≤ ‖a‖ := by simpa only [mem_ball, dist_zero_right, not_lt] using ha
          exact le_antisymm hle hge
        rw [hnorm, mul_inv_cancel₀ hR.ne', Real.log_one, mul_zero]
      · rw [apply_eq_zero_of_notMem (toClosedBall R (divisor F univ)) hac,
          Int.cast_zero, zero_mul]

/-- Open-disk zero sum form of Jensen counting. Zeros on the boundary have
zero logarithmic weight; the origin correction is retained exactly. -/
theorem logCounting_eq_open_disk_sum {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {R : ℝ} (hR : 0 < R) :
    ValueDistribution.logCounting F (0 : WithTop ℂ) R =
      (∑ᶠ a : ℂ, (divisor F (ball 0 R) a : ℝ)) * Real.log R -
        ∑ᶠ a : ℂ, (divisor F (ball 0 R) a : ℝ) * Real.log ‖a‖ := by
  have hA := Complex.analyticOnNhd_univ_iff_differentiable.mpr hF
  let d := divisor F (ball 0 R)
  let G := toClosedBall R (divisor F univ)
  have hd := (hA.meromorphicOn.mono_set (subset_univ (closedBall (0 : ℂ) R))).divisor_ball_support_finite
  have hG := G.finiteSupport (isCompact_closedBall ..)
  have hd1 : HasFiniteSupport (fun a : ℂ => (d a : ℝ) * Real.log R) :=
    hd.subset (fun a ha => by
      change d a ≠ 0
      intro he
      exact ha (by simp [he]))
  have hd2 : HasFiniteSupport (fun a : ℂ => (d a : ℝ) * Real.log ‖a‖) :=
    hd.subset (fun a ha => by
      change d a ≠ 0
      intro he
      exact ha (by simp [he]))
  have hG1 : HasFiniteSupport (fun a : ℂ => (G a : ℝ) * Real.log (R * ‖a‖⁻¹)) :=
    hG.subset (fun a ha => by
      change G a ≠ 0
      intro he
      exact ha (by simp [he]))
  have hc : HasFiniteSupport (fun a : ℂ =>
      if a = 0 then (divisor F univ 0 : ℝ) * Real.log R else 0) := by
    apply (finite_singleton (0 : ℂ)).subset
    intro a ha
    by_contra hne
    simp only [mem_singleton_iff] at hne
    exact ha (by simp [hne])
  rw [ValueDistribution.logCounting_zero, posPart_eq_self.mpr hA.divisor_nonneg]
  change (∑ᶠ a : ℂ, (G a : ℝ) * Real.log (R * ‖a‖⁻¹)) +
    (divisor F univ 0 : ℝ) * Real.log R = _
  have hcenter : (∑ᶠ a : ℂ, if a = 0 then (divisor F univ 0 : ℝ) * Real.log R else 0) =
      (divisor F univ 0 : ℝ) * Real.log R := by
    rw [finsum_eq_single _ 0 (by intro a ha; simp [ha])]
    simp
  rw [← hcenter, ← finsum_add_distrib hG1 hc]
  have hpoint := funext (open_disk_logCounting_term hF hR)
  change (fun a : ℂ => (d a : ℝ) * (Real.log R - Real.log ‖a‖)) = _ at hpoint
  rw [← hpoint]
  simp_rw [mul_sub]
  rw [finsum_sub_distrib hd1 hd2, finsum_mul]

/-- The exact center value of an exponential factor. This includes arbitrary
vanishing order of F at zero and is the unscaled form of `eq:centeridentity`. -/
theorem exponential_factor_center_identity {F : ℂ → ℂ}
    (hF : Differentiable ℂ F) {R : ℝ} (hR : 0 < R)
    (hfinite : (divisor F (ball 0 R)).support.Finite)
    {L : ℂ → ℂ} (hL : AnalyticOnNhd ℂ L (ball 0 R))
    (heq : ∀ z ∈ ball (0 : ℂ) R,
      F z = (finiteDivisorPolynomial (divisor F (ball 0 R)) hfinite).eval z *
        Complex.exp (L z)) :
    (L 0).re = ValueDistribution.logCounting F (0 : WithTop ℂ) R -
      ((finiteDivisorPolynomial (divisor F (ball 0 R)) hfinite).natDegree : ℝ) *
        Real.log R + Real.log ‖meromorphicTrailingCoeffAt F 0‖ := by
  have hA := Complex.analyticOnNhd_univ_iff_differentiable.mpr hF
  have hAB := hA.mono (subset_univ (ball (0 : ℂ) R))
  have hcod : F =ᶠ[codiscreteWithin (ball (0 : ℂ) R)]
      (∏ᶠ a, (fun z : ℂ => z - a) ^ divisor F (ball 0 R) a) •
        (fun z => Complex.exp (L z)) := by
    rw [← finiteDivisorPolynomial_eval_eq_factorized _ hfinite hAB.divisor_nonneg]
    filter_upwards [self_mem_codiscreteWithin (ball (0 : ℂ) R)] with z hz
    exact heq z hz
  have hlog := MeromorphicOn.log_norm_meromorphicTrailingCoeffAt_extract_zeros_poles
    hfinite (mem_ball_self hR)
    (isOpen_ball.preperfect 0 (mem_ball_self hR))
    (hA 0 (mem_univ _)).meromorphicAt
    (show AnalyticAt ℂ (fun z => Complex.exp (L z)) 0 by
      exact (hL 0 (mem_ball_self hR)).cexp)
    (Complex.exp_ne_zero (L 0)) hcod
  simp only [zero_sub, norm_neg, Complex.norm_exp, Real.log_exp] at hlog
  rw [logCounting_eq_open_disk_sum hF hR,
    finiteDivisorPolynomial_natDegree_cast _ _ hAB.divisor_nonneg]
  linarith

end
end ModifiedCartan
#print axioms ModifiedCartan.finiteDivisorPolynomial_degree_count_bound
#print axioms ModifiedCartan.logCounting_eq_open_disk_sum
#print axioms ModifiedCartan.exponential_factor_center_identity
