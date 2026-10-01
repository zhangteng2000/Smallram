import ModifiedCartan.CurveCoordinateCounting
import ModifiedCartan.CharacteristicMonotone

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

/-- Nonnegativity of the literal order, including constant curves.
Used when letting beta decrease to rho in `lem:small-order-coordinates`. -/
theorem order_nonneg {n : ℕ} (f : Curve n) : 0 ≤ order f := by
  by_cases hz : ∀ r : ℝ, 0 < r → characteristic f r = 0
  · have ht : Tendsto (logGrowthRatio f) atTop (𝓝 (0 : EReal)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
      simp [logGrowthRatio, hz r hr]
    exact ht.limsup_eq.ge
  · push_neg at hz
    obtain ⟨s, hs, hsz⟩ := hz
    have hsp : 0 < characteristic f s := lt_of_le_of_ne (characteristic_nonneg f hs) (Ne.symm hsz)
    have ht : Tendsto (fun r : ℝ => Real.log (characteristic f s) / Real.log r) atTop (𝓝 0) :=
      Real.tendsto_log_atTop.const_div_atTop _
    have hb : ∀ᶠ r : ℝ in atTop,
        ((Real.log (characteristic f s) / Real.log r : ℝ) : EReal) ≤ logGrowthRatio f r := by
      filter_upwards [eventually_ge_atTop s, eventually_ge_atTop (2 : ℝ)] with r hsr hr2
      have hr : 0 < r := by linarith
      have hlog := Real.log_le_log hsp (characteristic_monotoneOn f hs hr hsr)
      have hdiv := div_le_div_of_nonneg_right hlog (Real.log_pos (by linarith : 1 < r)).le
      dsimp only [logGrowthRatio]
      exact_mod_cast hdiv
    have hi := limsup_le_limsup hb
    rw [(EReal.tendsto_coe.mpr ht).limsup_eq] at hi
    exact hi

/-- A power bound controls the exact scalar entire order. -/
theorem entireOrder_le_of_posLog_power_bound {f : ℂ → ℂ} {C β : ℝ}
    (hβ : 0 ≤ β) (hC : 0 < C)
    (hb : ∀ r : ℝ, 1 ≤ r → Real.posLog (maximumModulus f r) ≤ C * r ^ β) :
    entireOrder f ≤ (β : EReal) := by
  have ht : Tendsto (fun r : ℝ => β + Real.posLog C / Real.log r) atTop (𝓝 β) := by
    simpa only [add_zero] using tendsto_const_nhds.add
      (Real.tendsto_log_atTop.const_div_atTop (Real.posLog C))
  have he : ∀ᶠ r : ℝ in atTop,
      ((Real.posLog (Real.posLog (maximumModulus f r)) / Real.log r : ℝ) : EReal) ≤
        ((β + Real.posLog C / Real.log r : ℝ) : EReal) := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with r hr2
    have hr : 1 ≤ r := by linarith
    have hr0 : 0 < r := by linarith
    have hlr : 0 < Real.log r := Real.log_pos (by linarith)
    have hp := Real.posLog_le_posLog Real.posLog_nonneg (hb r hr)
    have hm : Real.posLog (C * r ^ β) ≤ Real.posLog C + β * Real.log r := by
      rw [Real.posLog_apply, Real.log_mul hC.ne' (Real.rpow_pos_of_pos hr0 β).ne',
        Real.log_rpow hr0]
      apply max_le (add_nonneg Real.posLog_nonneg (mul_nonneg hβ hlr.le))
      have hh : Real.log C ≤ Real.posLog C := le_max_right _ _
      linarith
    have hdiv := div_le_div_of_nonneg_right (hp.trans hm) hlr.le
    have heq : (Real.posLog C + β * Real.log r) / Real.log r =
        β + Real.posLog C / Real.log r := by field_simp; ring
    rw [heq] at hdiv
    exact_mod_cast hdiv
  have hi := limsup_le_limsup he
  rw [(EReal.tendsto_coe.mpr ht).limsup_eq] at hi
  exact hi

end ModifiedCartan
#print axioms ModifiedCartan.order_nonneg
#print axioms ModifiedCartan.entireOrder_le_of_posLog_power_bound
