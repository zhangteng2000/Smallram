import ModifiedCartan.WeightedZeroCounting

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

theorem posLog_norm_add_ratio_le {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    Real.posLog (‖a + b‖ / ‖a‖) ≤ ‖b‖ / ‖a‖ := by
  have ha0 := norm_pos_iff.mpr ha
  have hn : ‖a + b‖ / ‖a‖ ≤ 1 + ‖b‖ / ‖a‖ := by
    simpa only [add_div, div_self ha0.ne'] using
      div_le_div_of_nonneg_right (norm_add_le a b) ha0.le
  have hp := Real.posLog_le_posLog (div_nonneg (norm_nonneg _) ha0.le) hn
  have hq : 1 ≤ 1 + ‖b‖ / ‖a‖ := by linarith [div_nonneg (norm_nonneg b) ha0.le]
  have hqp : 0 < 1 + ‖b‖ / ‖a‖ := zero_lt_one.trans_le hq
  rw [Real.posLog_eq_log (x := 1 + ‖b‖ / ‖a‖) (by rw [abs_of_pos hqp]; exact hq)] at hp
  exact hp.trans (by simpa only [add_sub_cancel_left] using Real.log_le_sub_one_of_pos hqp)

/-- Pointwise translation estimate. The extra one in the summable error
absorbs roots translated to zero, so no finite exceptional-root assumption
is used. This specializes to LaTeX `eq:translated-count`. -/
theorem rootCountingWeight_translate_bound {a : ℂ} (ha : a ≠ 0) (b : ℂ)
    {t : ℝ} (ht : 1 ≤ t) :
    Real.posLog (t / ‖a‖) ≤ rootCountingWeight (t + ‖b‖) (a + b) +
      (‖b‖ + 1) * ‖a‖⁻¹ := by
  have ha0 := norm_pos_iff.mpr ha
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  by_cases hab : a + b = 0
  · rw [rootCountingWeight, if_pos hab]
    have hpart := Real.posLog_mul (x := t) (y := ‖a‖⁻¹)
    rw [← div_eq_mul_inv, Real.posLog_eq_log (x := t) (by rw [abs_of_pos ht0]; exact ht)] at hpart
    have hi : Real.posLog ‖a‖⁻¹ ≤ (‖b‖ + 1) * ‖a‖⁻¹ := by
      apply max_le (by positivity)
      have hl := Real.log_le_self (inv_nonneg.mpr ha0.le)
      have hn : ‖a‖⁻¹ ≤ (‖b‖ + 1) * ‖a‖⁻¹ := by
        nlinarith [inv_nonneg.mpr ha0.le, norm_nonneg b]
      exact hl.trans hn
    have hr := Real.log_le_log ht0 (show t ≤ t + ‖b‖ by linarith [norm_nonneg b])
    linarith
  · rw [rootCountingWeight, if_neg hab]
    have hab0 := norm_pos_iff.mpr hab
    have he : t / ‖a‖ = (t / ‖a + b‖) * (‖a + b‖ / ‖a‖) := by field_simp
    have hpart := Real.posLog_mul (x := t / ‖a + b‖) (y := ‖a + b‖ / ‖a‖)
    rw [← he] at hpart
    have hfirst := Real.posLog_le_posLog (div_nonneg ht0.le hab0.le)
      (div_le_div_of_nonneg_right (show t ≤ t + ‖b‖ by linarith [norm_nonneg b]) hab0.le)
    have hsecond := posLog_norm_add_ratio_le ha b
    have heB : ‖b‖ / ‖a‖ = ‖b‖ * ‖a‖⁻¹ := div_eq_mul_inv _ _
    rw [heB] at hsecond
    have hn : 0 ≤ ‖a‖⁻¹ := inv_nonneg.mpr ha0.le
    linarith

end ModifiedCartan
#print axioms ModifiedCartan.rootCountingWeight_translate_bound
