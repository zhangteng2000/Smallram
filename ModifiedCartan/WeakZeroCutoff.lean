import ModifiedCartan.WeakGradientSmoothing
import Mathlib.Analysis.Calculus.MeanValue

open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory ContinuousLinearMap
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

def weakZeroCutoff (u : ℂ → ℝ) : ℂ → ℝ :=
  (closedBall (0 : ℂ) (7 / 2)).indicator u

theorem weakZeroCutoff_eq {u : ℂ → ℝ} {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) (7 / 2)) :
    weakZeroCutoff u z = u z := indicator_of_mem hz _

theorem weakZeroCutoff_integrable {u : ℂ → ℝ}
    (hu : HasWeakComplexGradient (ball (0 : ℂ) 4) u (fun _ => 0)) :
    Integrable (weakZeroCutoff u) :=
  (hu.function_integrable _ (isCompact_closedBall _ _)
    (closedBall_subset_ball (by norm_num : (7 / 2 : ℝ) < 4))).integrable_indicator measurableSet_closedBall

theorem weak_zero_smooth_constant {u : ℂ → ℝ}
    (hu : HasWeakComplexGradient (ball (0 : ℂ) 4) u (fun _ => 0))
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχsupp : tsupport χ ⊆ closedBall (0 : ℂ) (1 / 4)) :
    ∃ c : ℝ, ∀ z ∈ ball (0 : ℂ) 3,
      (weakZeroCutoff u ⋆[lsmul ℝ ℝ, volume] χ) z = c := by
  have hv := (weakZeroCutoff_integrable hu).locallyIntegrable
  have hu' := hu.restrict (ball_subset_ball (by norm_num : (7 / 2 : ℝ) ≤ 4))
  apply isOpen_ball.exists_is_const_of_fderiv_eq_zero (𝕜 := ℝ) (convex_ball (0 : ℂ) 3).isPreconnected
  · intro z _
    exact (hχc.hasFDerivAt_convolution_right (lsmul ℝ ℝ) hv (hχ.of_le (by norm_num)) z).differentiableAt.differentiableWithinAt
  · intro z hz
    apply hu'.fderiv_convolution_eq_zero isOpen_ball hv
      (fun _ hx => weakZeroCutoff_eq (ball_subset_closedBall hx)) hχ hχc z
    intro w hw
    have hsmall : ‖z - w‖ ≤ 1 / 4 := by
      simpa only [mem_closedBall, dist_zero_right] using hχsupp hw
    have hz' : ‖z‖ < 3 := by simpa only [mem_ball, dist_zero_right] using hz
    have hnorm : ‖w‖ ≤ ‖z‖ + ‖z - w‖ := by
      simpa only [sub_sub_cancel] using norm_sub_le z (z - w)
    simpa only [mem_ball, dist_zero_right] using (show ‖w‖ < (7 / 2 : ℝ) by linarith)

theorem real_convolution_comm (f g : ℂ → ℝ) :
    (f ⋆[lsmul ℝ ℝ, volume] g) = (g ⋆[lsmul ℝ ℝ, volume] f) := by
  funext x
  rw [convolution_def, convolution_lsmul_swap]
  simp only [lsmul_apply, smul_eq_mul, mul_comm]

end
end ModifiedCartan
#print axioms ModifiedCartan.weak_zero_smooth_constant
