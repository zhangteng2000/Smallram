import ModifiedCartan.DiskCharacteristic

open scoped Topology
open Filter Set Metric MeromorphicOn
set_option autoImplicit false
namespace ModifiedCartan

theorem abs_log_eq_twice_posLog_sub_log (x : ℝ) :
    |Real.log x| = Real.posLog x + Real.posLog x - Real.log x := by
  by_cases hx : 0 ≤ Real.log x
  · rw [abs_of_nonneg hx, Real.posLog_apply, max_eq_right hx]
    ring
  · rw [abs_of_neg (lt_of_not_ge hx), Real.posLog_apply, max_eq_left (le_of_not_ge hx)]
    ring

theorem disk_boundary_abs_log_identity {f : ℂ → ℂ} {r : ℝ}
    (hf : MeromorphicOn f (sphere 0 |r|)) :
    Real.circleAverage (fun z => |Real.log ‖f z‖|) 0 r =
      2 * ValueDistribution.proximity f ⊤ r -
        Real.circleAverage (fun z => Real.log ‖f z‖) 0 r := by
  have hp := hf.circleIntegrable_posLog_norm
  have hl := hf.circleIntegrable_log_norm
  have hpp : CircleIntegrable (fun z => Real.posLog ‖f z‖ + Real.posLog ‖f z‖) 0 r := hp.add hp
  calc
    _ = Real.circleAverage (fun z => Real.posLog ‖f z‖ + Real.posLog ‖f z‖ - Real.log ‖f z‖) 0 r := by
      apply Real.circleAverage_congr_sphere
      intro z _
      exact abs_log_eq_twice_posLog_sub_log _
    _ = _ := by
      rw [Real.circleAverage_fun_sub hpp hl, Real.circleAverage_fun_add hp hp,
        ValueDistribution.proximity_top]
      ring

/-- Exact local boundary-mass estimate for LaTeX `lem:NH`, valid for every
positive radius and using only the negative central logarithm. -/
theorem disk_boundary_abs_log_bound {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : MeromorphicOn f (closedBall 0 |r|)) (hfa : AnalyticAt ℂ f 0) (h0 : f 0 ≠ 0) :
    Real.circleAverage (fun z => |Real.log ‖f z‖|) 0 r ≤
      2 * diskCharacteristic f r + Real.posLog (1 / ‖f 0‖) := by
  have hid := disk_boundary_abs_log_identity (hf.mono_set sphere_subset_closedBall)
  have hj := diskCounting_jensen hr.ne' hf
  rw [hfa.meromorphicTrailingCoeffAt_of_ne_zero h0] at hj
  obtain ⟨hZ, hP⟩ := diskCounting_nonneg_of_regular_center hr hf hfa h0
  have hc : -Real.log ‖f 0‖ ≤ Real.posLog (1 / ‖f 0‖) := by
    rw [one_div, Real.posLog_apply, Real.log_inv]
    exact le_max_right _ _
  unfold diskCharacteristic
  linarith

theorem diskCharacteristic_nonneg_of_regular_center {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : MeromorphicOn f (closedBall 0 |r|)) (hfa : AnalyticAt ℂ f 0) (h0 : f 0 ≠ 0) :
    0 ≤ diskCharacteristic f r :=
  add_nonneg (ValueDistribution.proximity_nonneg r)
    (diskCounting_nonneg_of_regular_center hr hf hfa h0).2

end ModifiedCartan
#print axioms ModifiedCartan.disk_boundary_abs_log_bound
