import ModifiedCartan.AnalyticLogSubharmonic
import ModifiedCartan.SubharmonicUpperBounds

open scoped Topology
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- A nonpositive constant logarithm limit gives exponential bounds on the
closed unit disk. Used in the local alternative proof of `prop:indices`. -/
theorem normalized_log_eventually_small_on_unit_disk {f : ℕ → ℂ → ℂ}
    {s : ℕ → ℝ} {a : ℝ}
    (hf : ∀ ν, AnalyticOnNhd ℂ (f ν) (ball (0 : ℂ) 3))
    (hne : ∀ ν, ∃ z ∈ ball (0 : ℂ) 3, f ν z ≠ 0) (hs : ∀ ν, 0 < s ν)
    (hu : LocalLpConvergence 1 (ball (0 : ℂ) 3)
      (fun ν z => (s ν)⁻¹ * Real.log ‖f ν z‖) (fun _ => a)) (ha : a ≤ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ ν in atTop, ∀ z ∈ closedBall (0 : ℂ) 1, ‖f ν z‖ ≤ Real.exp (ε * s ν) := by
  have hsub (ν : ℕ) := normalizedExtendedLog_isSubharmonicOn isOpen_ball
    (convex_ball (0 : ℂ) 3).isPreconnected (hf ν) (hne ν) (hs ν)
  have hconv : LocalLpConvergence 1 (ball (0 : ℂ) 3)
      (fun ν z => (normalizedExtendedLog (s ν) (f ν) z).toReal) (fun _ => a) := by
    simpa only [normalizedExtendedLog_toReal] using hu
  have hb := subharmonic_eventually_upper_bound hsub hconv
    (isCompact_closedBall (0 : ℂ) 1) (V := ball 0 2) isOpen_ball
    (by rw [closure_ball (0 : ℂ) (by norm_num : (2 : ℝ) ≠ 0)]; exact isCompact_closedBall _ _)
    (closedBall_subset_ball (by norm_num : (1 : ℝ) < 2))
    (by rw [closure_ball (0 : ℂ) (by norm_num : (2 : ℝ) ≠ 0)]; exact closedBall_subset_ball (by norm_num))
    (M := 0) (Eventually.of_forall (fun _ => ha)) hε
  filter_upwards [hb] with ν hν z hz
  by_cases hfz : f ν z = 0
  · rw [hfz, norm_zero]
    exact (Real.exp_pos _).le
  · have hl := hν z hz
    rw [normalizedExtendedLog_of_ne_zero (s ν) hfz, EReal.coe_le_coe_iff, zero_add,
      mul_comm, ← div_eq_mul_inv] at hl
    exact (Real.log_le_iff_le_exp (norm_pos_iff.mpr hfz)).mp ((div_le_iff₀ (hs ν)).mp hl)

end ModifiedCartan
#print axioms ModifiedCartan.normalized_log_eventually_small_on_unit_disk
