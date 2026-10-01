import ModifiedCartan.EntireOrder
import ModifiedCartan.CountingIntegral

open scoped Topology
open Filter Set Metric Function Function.locallyFinsuppWithin MeromorphicOn
set_option autoImplicit false
namespace ModifiedCartan

/-- Jensen's unweighted zero-count consequence, Step 2 of LaTeX
`lem:entire-majorant`. The count is the actual analytic divisor. -/
theorem zeroCount_le_of_posLog_bound {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h0 : f 0 = 1) {D σ r : ℝ} (hD : 0 ≤ D) (hr : 1 ≤ r)
    (hb : ∀ z ∈ closedBall (0 : ℂ) (2 * r),
      Real.posLog ‖f z‖ ≤ D * (2 * r) ^ σ) :
    zeroCount f r ≤ (D * (2 : ℝ) ^ σ / Real.log 2) * r ^ σ := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hR : 0 < 2 * r := mul_pos (by norm_num) hr0
  have hA := Complex.analyticOnNhd_univ_iff_differentiable.mpr hf
  have hJ := FewInflection.analytic_divisor_count_le (c := 0) (r := r) (R := 2 * r)
    (M := Real.exp (D * (2 * r) ^ σ))
    (by simpa only [abs_of_pos hr0] using hr0)
    (by rw [abs_of_pos hr0, abs_of_pos hR]; linarith)
    (Real.one_le_exp_iff.mpr (mul_nonneg hD (Real.rpow_nonneg hR.le _)))
    (hA.mono (subset_univ _)) (by simpa only [h0] using one_ne_zero)
    (fun z hz => Real.le_exp_of_log_le ((le_max_right 0 _).trans (hb z (by
      rw [abs_of_pos hR] at hz
      exact sphere_subset_closedBall hz))))
  rw [h0, norm_one, div_one, Real.log_exp,
    show 2 * r / r = (2 : ℝ) by field_simp] at hJ
  rw [toClosedBall_divisor (meromorphicOn_univ.mp hA.meromorphicOn)] at hJ
  change zeroCount f r ≤ D * (2 * r) ^ σ / Real.log 2 at hJ
  exact hJ.trans_eq (by rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hr0.le]; ring)

theorem entire_zeroCount_power_bound {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h0 : f 0 = 1) {σ D : ℝ} (hD : 0 < D)
    (hb : ∀ r, 1 ≤ r → ∀ z ∈ closedBall (0 : ℂ) r, Real.posLog ‖f z‖ ≤ D * r ^ σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r, 1 ≤ r → zeroCount f r ≤ C * r ^ σ := by
  refine ⟨D * (2 : ℝ) ^ σ / Real.log 2,
    div_pos (mul_pos hD (Real.rpow_pos_of_pos (by norm_num) _)) (Real.log_pos (by norm_num)), ?_⟩
  intro r hr
  exact zeroCount_le_of_posLog_bound hf h0 hD.le hr (hb (2 * r) (by linarith))

end ModifiedCartan
#print axioms ModifiedCartan.entire_zeroCount_power_bound
