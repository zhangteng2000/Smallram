import FewInflection.GrowthBasics
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Instances.EReal.Lemmas

open scoped Topology
open Filter

namespace FewInflection

/-- The multiplicative constant in a positive power bound disappears after
dividing its logarithm by `log r`. -/
theorem tendsto_log_const_mul_rpow_div_log
    {c : ℝ} (hc : 0 < c) (ρ : ℝ) :
    Tendsto (fun r : ℝ => Real.log (c * r ^ ρ) / Real.log r)
      atTop (𝓝 ρ) := by
  have hlim : Tendsto (fun r : ℝ => Real.log c / Real.log r + ρ)
      atTop (𝓝 ρ) := by
    simpa using (Real.tendsto_log_atTop.const_div_atTop (Real.log c)).add_const ρ
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with r hr
  have hr0 : 0 < r := zero_lt_one.trans hr
  rw [Real.log_mul hc.ne' (Real.rpow_pos_of_pos hr0 ρ).ne',
    Real.log_rpow hr0, add_div, mul_div_cancel_right₀ _ (Real.log_pos hr).ne']

/-- A positive lower power bound forces the characteristic to tend to infinity. -/
theorem characteristic_tendsto_atTop_of_rpow_lower_bound
    {n : ℕ} (f : Curve n) {c ρ : ℝ} (hc : 0 < c) (hρ : 0 < ρ)
    (hlower : ∀ᶠ r in atTop, c * r ^ ρ ≤ characteristic f r) :
    Tendsto (characteristic f) atTop atTop := by
  exact tendsto_atTop_mono' atTop hlower ((tendsto_rpow_atTop hρ).const_mul_atTop hc)

/-- Two-sided bounds by positive multiples of the same positive power imply
convergence of the exact logarithmic growth ratio used in the frozen targets. -/
theorem logGrowthRatio_tendsto_of_two_sided_power_bounds
    {n : ℕ} (f : Curve n) {c C ρ : ℝ}
    (hc : 0 < c) (hC : 0 < C) (hρ : 0 < ρ)
    (hbounds : ∀ᶠ r in atTop,
      c * r ^ ρ ≤ characteristic f r ∧ characteristic f r ≤ C * r ^ ρ) :
    Tendsto (logGrowthRatio f) atTop (𝓝 (ρ : EReal)) := by
  have hT := characteristic_tendsto_atTop_of_rpow_lower_bound f hc hρ
    (hbounds.mono fun _ h => h.1)
  have hlarge : ∀ᶠ r in atTop, 1 ≤ characteristic f r := hT.eventually_ge_atTop 1
  have hcomp : ∀ᶠ r in atTop,
      Real.log (c * r ^ ρ) / Real.log r ≤
        Real.log (max (characteristic f r) 1) / Real.log (max r 2) ∧
      Real.log (max (characteristic f r) 1) / Real.log (max r 2) ≤
        Real.log (C * r ^ ρ) / Real.log r := by
    filter_upwards [hbounds, hlarge, eventually_gt_atTop (2 : ℝ)] with r hb hTr hr
    have hr0 : 0 < r := lt_trans (by norm_num) hr
    have hTr0 : 0 < characteristic f r := zero_lt_one.trans_le hTr
    have hp : 0 < r ^ ρ := Real.rpow_pos_of_pos hr0 ρ
    have hlogr : 0 ≤ Real.log r := Real.log_nonneg (by linarith)
    rw [max_eq_left hTr, max_eq_left hr.le]
    constructor
    · exact div_le_div_of_nonneg_right
        (Real.log_le_log (mul_pos hc hp) hb.1) hlogr
    · exact div_le_div_of_nonneg_right
        (Real.log_le_log hTr0 hb.2) hlogr
  have hreal : Tendsto (fun r : ℝ =>
      Real.log (max (characteristic f r) 1) / Real.log (max r 2))
      atTop (𝓝 ρ) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_log_const_mul_rpow_div_log hc ρ)
      (tendsto_log_const_mul_rpow_div_log hC ρ)
      (hcomp.mono fun _ h => h.1) (hcomp.mono fun _ h => h.2)
  exact EReal.tendsto_coe.mpr hreal

/-- The sharpness construction's two-sided characteristic estimate gives both
orders, with no finiteness assumption on either order. -/
theorem order_lowerOrder_eq_of_two_sided_power_bounds
    {n : ℕ} (f : Curve n) {c C ρ : ℝ}
    (hc : 0 < c) (hC : 0 < C) (hρ : 0 < ρ)
    (hbounds : ∀ᶠ r in atTop,
      c * r ^ ρ ≤ characteristic f r ∧ characteristic f r ≤ C * r ^ ρ) :
    order f = (ρ : EReal) ∧ lowerOrder f = (ρ : EReal) :=
  order_and_lowerOrder_eq_of_logGrowthRatio_tendsto f
    (logGrowthRatio_tendsto_of_two_sided_power_bounds f hc hC hρ hbounds)

end FewInflection
