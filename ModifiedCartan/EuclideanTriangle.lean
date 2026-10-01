import ModifiedCartan.NormComparison
import Mathlib.Analysis.Normed.Lp.PiLp

open scoped Topology
set_option autoImplicit false
namespace ModifiedCartan

theorem euclideanNorm_add_le {n : ℕ} (v w : Index n → ℂ) :
    euclideanNorm (v + w) ≤ euclideanNorm v + euclideanNorm w := by
  let e := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Index n => ℂ)).symm
  have he (x : Index n → ℂ) : ‖e x‖ = euclideanNorm x := by
    rw [PiLp.norm_eq_of_L2]
    rfl
  have hh := norm_add_le (e v) (e w)
  simpa only [← map_add, he] using hh

theorem abs_euclideanNorm_sub_le {n : ℕ} (v w : Index n → ℂ) :
    |euclideanNorm v - euclideanNorm w| ≤ euclideanNorm (v - w) := by
  let e := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Index n => ℂ)).symm
  have he (x : Index n → ℂ) : ‖e x‖ = euclideanNorm x := by
    rw [PiLp.norm_eq_of_L2]
    rfl
  have hh := abs_norm_sub_norm_le (e v) (e w)
  simpa only [← map_sub, he] using hh

theorem euclideanNorm_difference_le_of_component_error {n : ℕ} (v w : Index n → ℂ)
    {E : ℝ} (hE : 0 ≤ E) (herror : ∀ j, ‖v j - w j‖ ≤ E) :
    |euclideanNorm v - euclideanNorm w| ≤ Real.sqrt (n + 1) * E := by
  apply (abs_euclideanNorm_sub_le v w).trans
  apply (euclideanNorm_le (v - w)).trans
  exact mul_le_mul_of_nonneg_left ((pi_norm_le_iff_of_nonneg hE).mpr herror) (Real.sqrt_nonneg _)

end ModifiedCartan
#print axioms ModifiedCartan.euclideanNorm_difference_le_of_component_error
