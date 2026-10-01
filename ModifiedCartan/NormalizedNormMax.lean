import ModifiedCartan.NormComparison
import Mathlib.Analysis.Normed.Group.Constructions

open scoped Topology BigOperators
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

theorem normalized_log_pi_norm_eq_max {n : ℕ} (v : Index n → ℂ) {s : ℝ}
    (hs : 0 < s) (hv : ∀ j, v j ≠ 0) :
    s⁻¹ * Real.log ‖v‖ = Finset.univ.sup' Finset.univ_nonempty
      (fun j => s⁻¹ * Real.log ‖v j‖) := by
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ)
    Finset.univ_nonempty (fun j : Index n => ‖v j‖)
  have hmax (k : Index n) : ‖v k‖ ≤ ‖v j‖ := by
    rw [← hj]
    exact Finset.le_sup' (fun i => ‖v i‖) (Finset.mem_univ k)
  have hnorm : ‖v‖ = ‖v j‖ := le_antisymm
    ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr hmax) (norm_le_pi_norm v j)
  rw [hnorm]
  apply le_antisymm
  · exact Finset.le_sup' (fun k => s⁻¹ * Real.log ‖v k‖) (Finset.mem_univ j)
  · apply Finset.sup'_le
    intro k _
    exact mul_le_mul_of_nonneg_left
      (Real.log_le_log (norm_pos_iff.mpr (hv k)) (hmax k)) (inv_pos.mpr hs).le

/-- Quantified Euclidean norm/coordinate maximum comparison in
LaTeX `eq:norm-max`, after normalization. -/
theorem normalized_log_euclideanNorm_sub_max_bound {n : ℕ} (v : Index n → ℂ) {s : ℝ}
    (hs : 0 < s) (hv : ∀ j, v j ≠ 0) :
    ‖s⁻¹ * Real.log (euclideanNorm v) -
      Finset.univ.sup' Finset.univ_nonempty (fun j => s⁻¹ * Real.log ‖v j‖)‖ ≤
        s⁻¹ * Real.log (Real.sqrt (n + 1)) := by
  have hne : v ≠ 0 := by
    intro he
    exact hv 0 (congrFun he 0)
  rw [← normalized_log_pi_norm_eq_max v hs hv, Real.norm_eq_abs]
  have hlo := mul_le_mul_of_nonneg_left (log_norm_le_log_euclideanNorm hne) (inv_pos.mpr hs).le
  have hhi := mul_le_mul_of_nonneg_left (log_euclideanNorm_le hne) (inv_pos.mpr hs).le
  rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
  nlinarith

end ModifiedCartan
#print axioms ModifiedCartan.normalized_log_pi_norm_eq_max
#print axioms ModifiedCartan.normalized_log_euclideanNorm_sub_max_bound
