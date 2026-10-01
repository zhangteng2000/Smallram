import ModifiedCartan.PoissonMajorant
import ModifiedCartan.MaximumModulus
import Mathlib.Analysis.Complex.ValueDistribution.CharacteristicFunction

open scoped Topology
open Filter Set Metric Complex MeromorphicOn
set_option autoImplicit false
namespace ModifiedCartan

theorem entire_characteristic_eq_circleAverage_posLog {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (r : ℝ) :
    ValueDistribution.characteristic f ⊤ r =
      Real.circleAverage (fun z => Real.posLog ‖f z‖) 0 r := by
  have hA := Complex.analyticOnNhd_univ_iff_differentiable.mpr hf
  have hp : ValueDistribution.logCounting f ⊤ = 0 := by
    rw [ValueDistribution.logCounting_top, negPart_eq_zero.mpr hA.divisor_nonneg]
    simp
  simp only [ValueDistribution.characteristic, hp, add_zero, ValueDistribution.proximity_top]

theorem poissonKernel_le_three {r : ℝ} (hr : 0 < r) {z w : ℂ}
    (hz : z ∈ closedBall 0 r) (hw : w ∈ sphere 0 (2 * r)) :
    poissonKernel 0 z w ≤ 3 := by
  have hn : ‖z‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hz
  have hz2 : z ∈ ball 0 (2 * r) := by
    simpa only [mem_ball, dist_zero_right] using (show ‖z‖ < 2 * r by linarith)
  have hk : poissonKernel 0 z w ≤ (2 * r + ‖z‖) / (2 * r - ‖z‖) := by
    simpa only [poissonKernel_eq_re_herglotzRieszKernel, Function.comp_apply,
      herglotzRieszKernel_def, sub_zero] using re_herglotzRieszKernel_le hw hz2
  apply hk.trans
  apply (div_le_iff₀ (by linarith : 0 < 2 * r - ‖z‖)).mpr
  linarith

/-- The precise scalar Poisson estimate used in Step 1 of LaTeX
`lem:small-order-coordinates`, including points at which f vanishes. -/
theorem entire_posLog_le_three_characteristic {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : z ∈ closedBall 0 r) :
    Real.posLog ‖f z‖ ≤ 3 * ValueDistribution.characteristic f ⊤ (2 * r) := by
  rw [entire_characteristic_eq_circleAverage_posLog hf]
  have hnmean : 0 ≤ Real.circleAverage (fun w => Real.posLog ‖f w‖) 0 (2 * r) :=
    Real.circleAverage_nonneg_of_nonneg (fun _ _ => Real.posLog_nonneg)
  by_cases hz0 : f z = 0
  · simp only [hz0, norm_zero, Real.posLog_zero]
    positivity
  let U := fun w => max 1 ‖f w‖
  have hUc : Continuous U := continuous_const.max hf.continuous.norm
  have hUp : ∀ w, 0 < U w := fun w => zero_lt_one.trans_le (le_max_left _ _)
  have hbound : ∀ w, ‖f w‖ ≤ U w := fun w => le_max_right _ _
  have hnz : ‖z‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hz
  have hz2 : z ∈ ball 0 (2 * r) := by
    simpa only [mem_ball, dist_zero_right] using (show ‖z‖ < 2 * r by linarith)
  have hmaj := log_norm_le_poisson_log_majorant hf hz0 hUc hUp hbound hz2
  have hlogU (w : ℂ) : Real.log (U w) = Real.posLog ‖f w‖ :=
    (Real.posLog_eq_log_max_one (norm_nonneg (f w))).symm
  simp only [hlogU] at hmaj
  have hi : CircleIntegrable (fun w => Real.posLog ‖f w‖) 0 (2 * r) :=
    (Real.continuous_posLog.comp hf.continuous.norm).continuousOn.circleIntegrable'
  have he := Real.circleAverage_mono
    (hi.continuousOn_smul (continuousOn_poissonKernel_sphere hz2))
    (show CircleIntegrable (fun w => (3 : ℝ) • Real.posLog ‖f w‖) 0 (2 * r) from hi.const_smul)
    (by
      intro w hw
      have hw' : w ∈ sphere (0 : ℂ) (2 * r) := by simpa [abs_of_pos (by positivity : 0 < 2 * r)] using hw
      exact mul_le_mul_of_nonneg_right (poissonKernel_le_three hr hz hw') Real.posLog_nonneg)
  rw [Real.circleAverage_fun_smul] at he
  change Real.circleAverage (fun w => poissonKernel 0 z w * Real.posLog ‖f w‖) 0 (2 * r) ≤
    3 * Real.circleAverage (fun w => Real.posLog ‖f w‖) 0 (2 * r) at he
  exact max_le (by positivity) (hmaj.trans he)

theorem entire_posLog_maximumModulus_le_three_characteristic {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {r : ℝ} (hr : 0 < r) :
    Real.posLog (maximumModulus f r) ≤ 3 * ValueDistribution.characteristic f ⊤ (2 * r) := by
  obtain ⟨z, hz, he⟩ := maximumModulus_attained hf.continuous hr.le
  rw [he]
  exact entire_posLog_le_three_characteristic hf hr hz

end ModifiedCartan
#print axioms ModifiedCartan.entire_posLog_maximumModulus_le_three_characteristic
