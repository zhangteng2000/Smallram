import ModifiedCartan.ExponentialJetApproximation
import ModifiedCartan.RescaledGauge

open scoped Topology BigOperators
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

def unitBoundWronskianConstant (n : ℕ) : ℝ :=
  ((n + 1).factorial : ℝ) * ((n + 1).factorial : ℝ) ^ (n + 1)

theorem unitBoundWronskianConstant_ge_one (n : ℕ) : 1 ≤ unitBoundWronskianConstant n := by
  have hf : (1 : ℝ) ≤ (n + 1).factorial := by exact_mod_cast Nat.factorial_pos (n + 1)
  simpa only [unitBoundWronskianConstant, one_mul] using! mul_le_mul hf (one_le_pow₀ hf (n := n + 1))
    (by norm_num : (0 : ℝ) ≤ 1) (by positivity : (0 : ℝ) ≤ (n + 1).factorial)

theorem norm_wronskian_le_of_unit_bound {n : ℕ} {g : Index n → ℂ → ℂ}
    (hg : ∀ j, AnalyticOnNhd ℂ (g j) (ball 0 256))
    (hbound : ∀ z ∈ ball (0 : ℂ) 256, euclideanNorm (fun j => g j z) ≤ 1)
    {z : ℂ} (hz : z ∈ ball 0 64) :
    ‖FewInflection.wronskian n g z‖ ≤ unitBoundWronskianConstant n := by
  have hsub : closedBall z 1 ⊆ ball (0 : ℂ) 256 := by
    intro w hw
    have hw' : ‖w-z‖ ≤ 1 := by simpa only [mem_closedBall, dist_eq_norm] using hw
    have hz' : ‖z‖ < 64 := by simpa only [mem_ball, dist_zero_right] using hz
    have ht : ‖w‖ ≤ ‖w-z‖ + ‖z‖ := by simpa only [sub_add_cancel] using norm_add_le (w-z) z
    simpa only [mem_ball, dist_zero_right] using (show ‖w‖ < (256 : ℝ) by linarith)
  apply norm_wronskian_le_of_jet_bound g z (by positivity)
  intro j k hk
  have he := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k
    (by norm_num : (0 : ℝ) < 1) ((hg j).differentiableOn.diffContOnCl_ball hsub)
    (fun w hw => ((norm_le_pi_norm (fun l => g l w) j).trans (norm_le_euclideanNorm _)).trans
      (hbound w (hsub (sphere_subset_closedBall hw))))
  simp only [one_pow, div_one, mul_one] at he
  exact he.trans (by exact_mod_cast Nat.factorial_le hk)

theorem rescaledRepresentation_wronskian_gauge_change {n : ℕ} (f : Curve n) (t : ℝ)
    {H L : ℂ → ℂ} {z : ℂ} (hH : AnalyticAt ℂ H z) (hL : AnalyticAt ℂ L z) :
    FewInflection.wronskian n (rescaledRepresentation f t L) z =
      FewInflection.wronskian n (rescaledRepresentation f t H) z *
        Complex.exp ((n + 1 : ℂ) * (H z - L z)) := by
  rw [rescaledRepresentation_wronskian f t hL, rescaledRepresentation_wronskian f t hH]
  simp only [← Complex.exp_nat_mul, Nat.cast_add, Nat.cast_one]
  have he : Complex.exp ((n + 1 : ℂ) * (-L z)) =
      Complex.exp ((n + 1 : ℂ) * (-H z)) * Complex.exp ((n + 1 : ℂ) * (H z - L z)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [he]
  ring

end
end ModifiedCartan
#print axioms ModifiedCartan.norm_wronskian_le_of_unit_bound
