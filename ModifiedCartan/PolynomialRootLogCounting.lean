import ModifiedCartan.PolynomialRootCount
import ModifiedCartan.ZeroCopyLogCounting
import ModifiedCartan.RootKernel

open scoped Topology BigOperators
open Filter Set Metric MeasureTheory MeromorphicOn Function.locallyFinsuppWithin
set_option autoImplicit false
namespace ModifiedCartan

theorem single_root_logCounting {a : ℂ} (ha : a ≠ 0) {r : ℝ} (hr : 0 < r) :
    (single a (1 : ℤ)).logCounting r = Real.posLog (r / ‖a‖) := by
  classical
  by_cases har : ‖a‖ ≤ r
  · rw [logCounting_single_eq_log_sub_const har, Int.cast_one, one_mul,
      Real.posLog_eq_log (by
        rw [abs_of_pos (div_pos hr (norm_pos_iff.mpr ha))]
        exact (one_le_div (norm_pos_iff.mpr ha)).mpr har),
      Real.log_div hr.ne' (norm_ne_zero_iff.mpr ha)]
  · have hd : toClosedBall r (single a (1 : ℤ)) = 0 := by
      ext z
      by_cases hz : z ∈ closedBall (0 : ℂ) |r|
      · rw [toClosedBall_eval_within _ hz]
        have hza : z ≠ a := by
          intro hza
          subst z
          exact har (by simpa only [mem_closedBall, dist_zero_right, abs_of_pos hr] using hz)
        simp [single_apply, hza]
      · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz]
    change (∑ᶠ z : ℂ, ((toClosedBall r (single a (1 : ℤ))) z : ℝ) *
      Real.log (r * ‖z‖⁻¹)) + (single a (1 : ℤ) 0 : ℝ) * Real.log r = _
    rw [hd, posLog_div_norm_eq_zero_of_lt hr.le (lt_of_not_ge har)]
    simp [single_apply, ha.symm]

/-- A finite polynomial root factorization gives exactly the same
logarithmic counting function as the analytic divisor, including multiplicities. -/
theorem polynomial_root_list_logCounting {M : ℕ} (P : Polynomial ℂ) (a : Fin M → ℂ)
    (hP : normalize P = ∏ i, (Polynomial.X - Polynomial.C (a i)))
    (ha : ∀ i, a i ≠ 0) {r : ℝ} (hr : 0 < r) :
    ValueDistribution.logCounting (fun z => P.eval z) (0 : WithTop ℂ) r =
      ∑ i, Real.posLog (r / ‖a i‖) := by
  classical
  have hD : divisor (fun z => P.eval z) univ = ∑ i : Fin M, single (a i) (1 : ℤ) := by
    rw [← polynomial_divisor_normalize]
    have he : (fun z => (normalize P).eval z) = fun z => ∏ i, (z - a i) := by
      funext z
      simp only [hP, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    rw [he]
    ext z
    rw [divisor_root_product_apply, Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply]
    simp [single_apply]
  rw [ValueDistribution.logCounting_zero,
    posPart_eq_self.mpr (AnalyticOnNhd.eval_polynomial P).divisor_nonneg, hD,
    map_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl (fun i _ => single_root_logCounting (ha i) hr)

theorem polynomial_root_list_kernel_integral {M : ℕ} (P : Polynomial ℂ) (a : Fin M → ℂ)
    (hP : normalize P = ∏ i, (Polynomial.X - Polynomial.C (a i)))
    (ha : ∀ i, a i ≠ 0) {r : ℝ} (hr : 0 < r) :
    r * (∫ t in Ioi 0, ValueDistribution.logCounting (fun z => P.eval z)
      (0 : WithTop ℂ) t / (r + t) ^ 2) = ∑ i, Real.log (1 + r / ‖a i‖) := by
  have hi (i : Fin M) := (root_kernel_identity hr (ha i)).1
  calc
    _ = r * ∫ t in Ioi 0, ∑ i, Real.posLog (t / ‖a i‖) / (r + t) ^ 2 := by
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [polynomial_root_list_logCounting P a hP ha ht, Finset.sum_div]
    _ = ∑ i, r * ∫ t in Ioi 0, Real.posLog (t / ‖a i‖) / (r + t) ^ 2 := by
      rw [integral_finsetSum _ (fun i _ => hi i), Finset.mul_sum]
    _ = _ := Finset.sum_congr rfl (fun i _ => (root_kernel_identity hr (ha i)).2)

end ModifiedCartan
#print axioms ModifiedCartan.polynomial_root_list_logCounting
#print axioms ModifiedCartan.polynomial_root_list_kernel_integral
