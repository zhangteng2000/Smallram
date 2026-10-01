import ModifiedCartan.MaximumModulus
import ModifiedCartan.QuantitativeTaylor

open scoped Topology BigOperators
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Uniform Taylor-truncation bound, Step 1 of LaTeX
`lem:entire-majorant`. The constant is independent of the truncation. -/
theorem entire_taylorPolynomial_norm_le {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {r : ℝ} (hr : 0 < r)
    (N : ℕ) {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) r) :
    ‖(FewInflection.taylorPolynomial f 0 N).eval z‖ ≤ 2 * maximumModulus f (2 * r) := by
  have hM0 := maximumModulus_nonneg hf.continuous (by linarith : 0 ≤ 2 * r)
  have hterm (k : ℕ) := norm_taylor_term_le (by linarith : 0 < 2 * r) hr.le hM0
    hf.differentiableOn (fun w hw => norm_le_maximumModulus hf.continuous (sphere_subset_closedBall hw)) hz k
  have hratio : r / (2 * r) = (1 / 2 : ℝ) := by field_simp
  have hsum : (∑ k ∈ Finset.range N, (1 / 2 : ℝ) ^ k) ≤ 2 := by
    rw [geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1)]
    norm_num
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) N]
  rw [FewInflection.taylorPolynomial_eval_eq_sum]
  calc
    _ ≤ ∑ k ∈ Finset.range N, ‖(k.factorial : ℂ)⁻¹ * iteratedDeriv k f 0 * (z - 0) ^ k‖ :=
      norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range N, maximumModulus f (2 * r) * (1 / 2 : ℝ) ^ k := by
      apply Finset.sum_le_sum
      intro k _
      simpa only [hratio] using hterm k
    _ = maximumModulus f (2 * r) * ∑ k ∈ Finset.range N, (1 / 2 : ℝ) ^ k :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ maximumModulus f (2 * r) * 2 := mul_le_mul_of_nonneg_left hsum hM0
    _ = _ := mul_comm _ _

theorem entire_taylorPolynomial_maximumModulus_le {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {r : ℝ} (hr : 0 < r) (N : ℕ) :
    maximumModulus (fun z => (FewInflection.taylorPolynomial f 0 N).eval z) r ≤
      2 * maximumModulus f (2 * r) :=
  maximumModulus_le hr.le (fun _ hz => entire_taylorPolynomial_norm_le hf hr N hz)

/-- Uniform Cauchy bound for every derivative of every Taylor truncation,
as used for the Wronskian growth estimate `eq:WN-growth`. -/
theorem entire_taylorPolynomial_iteratedDeriv_le {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {r : ℝ} (hr : 0 < r)
    (N k : ℕ) {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) r) :
    ‖iteratedDeriv k (fun w => (FewInflection.taylorPolynomial f 0 N).eval w) z‖ ≤
      (k.factorial : ℝ) * (2 * maximumModulus f (4 * r)) / r ^ k := by
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hr
    (FewInflection.taylorPolynomial f 0 N).differentiable.diffContOnCl
  intro w hw
  have hw' : w ∈ closedBall (0 : ℂ) (2 * r) := by
    have hdist : dist w z ≤ r := (mem_sphere.mp hw).le
    have hz' : dist z 0 ≤ r := mem_closedBall.mp hz
    exact mem_closedBall.mpr ((dist_triangle w z 0).trans (by linarith))
  simpa only [show 2 * (2 * r) = 4 * r by ring] using
    entire_taylorPolynomial_norm_le hf (by linarith : 0 < 2 * r) N hw'

end ModifiedCartan
#print axioms ModifiedCartan.entire_taylorPolynomial_iteratedDeriv_le
