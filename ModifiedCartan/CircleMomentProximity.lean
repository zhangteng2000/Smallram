import ModifiedCartan.Counting

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

theorem posLog_le_fractional_moment_tangent {x p C : ℝ} (hx : 0 ≤ x) (hp : 0 < p)
    (hC : 0 ≤ C) :
    p * Real.posLog x ≤ Real.log (1 + C) + (1 + C)⁻¹ * x ^ p := by
  have hCp : 0 < 1 + C := by linarith
  have hlogC : 0 ≤ Real.log (1 + C) := Real.log_nonneg (by linarith)
  by_cases hl : Real.log x ≤ 0
  · rw [Real.posLog_apply, max_eq_left hl, mul_zero]
    exact add_nonneg hlogC (mul_nonneg (inv_nonneg.mpr hCp.le) (Real.rpow_nonneg hx p))
  have hxp : 0 < x := lt_of_le_of_ne hx (by
    intro he
    exact hl (by rw [← he, Real.log_zero]))
  have hratio := Real.log_le_sub_one_of_pos (div_pos (Real.rpow_pos_of_pos hxp p) hCp)
  rw [Real.log_div (Real.rpow_pos_of_pos hxp p).ne' hCp.ne', Real.log_rpow hxp] at hratio
  rw [Real.posLog_apply, max_eq_right (le_of_lt (lt_of_not_ge hl))]
  rw [div_eq_mul_inv] at hratio
  nlinarith

/-- An integrable fractional norm moment controls the actual proximity.
This is the logarithmic averaging step for LaTeX `lem:NH`. -/
theorem circle_proximity_le_of_fractional_moment {f : ℂ → ℂ} {r p C : ℝ}
    (hp : 0 < p) (hC : 0 ≤ C)
    (hlog : CircleIntegrable (fun z => Real.posLog ‖f z‖) 0 r)
    (hmoment : CircleIntegrable (fun z => ‖f z‖ ^ p) 0 r)
    (hbound : Real.circleAverage (fun z => ‖f z‖ ^ p) 0 r ≤ C) :
    ValueDistribution.proximity f ⊤ r ≤ p⁻¹ * (Real.log (1 + C) + 1) := by
  have hCp : 0 < 1 + C := by linarith
  have hlp : CircleIntegrable (fun z => p * Real.posLog ‖f z‖) 0 r := by
    change IntervalIntegrable _ _ _ _
    exact (hlog : IntervalIntegrable _ _ _ _).const_mul p
  have hmp : CircleIntegrable (fun z => (1 + C)⁻¹ * ‖f z‖ ^ p) 0 r := by
    change IntervalIntegrable _ _ _ _
    exact (hmoment : IntervalIntegrable _ _ _ _).const_mul (1 + C)⁻¹
  have havg (a : ℝ) (g : ℂ → ℝ) :
      Real.circleAverage (fun z => a * g z) 0 r = a * Real.circleAverage g 0 r := by
    simpa only [smul_eq_mul] using
      (Real.circleAverage_fun_smul (a := a) (f := g) (c := 0) (R := r))
  have he := Real.circleAverage_mono hlp ((circleIntegrable_const (Real.log (1 + C)) 0 r).add hmp)
    (fun z _ => posLog_le_fractional_moment_tangent (norm_nonneg (f z)) hp hC)
  rw [havg, Real.circleAverage_add (circleIntegrable_const _ 0 r) hmp,
    Real.circleAverage_const, havg] at he
  have hb := mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hCp.le)
  have hc : (1 + C)⁻¹ * C ≤ 1 := by
    rw [mul_comm, ← div_eq_mul_inv]
    exact (div_le_one hCp).mpr (by linarith)
  rw [ValueDistribution.proximity_top]
  have hfinal : Real.circleAverage (fun z => Real.posLog ‖f z‖) 0 r * p ≤
      Real.log (1 + C) + 1 := by nlinarith
  simpa only [div_eq_mul_inv, mul_comm] using (le_div_iff₀ hp).mpr hfinal

end ModifiedCartan
#print axioms ModifiedCartan.circle_proximity_le_of_fractional_moment
