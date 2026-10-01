import ModifiedCartan.SmallOrderCoordinates
import ModifiedCartan.EuclideanJensen

open scoped Topology
open Filter Set Asymptotics
set_option autoImplicit false
namespace ModifiedCartan

/-- The two exact comparison inequalities transfer an eventual bound
on the curve's ramification to all positive radii of the normalized system. -/
theorem system_divisor_majorant_of_eventual_bound {n : ℕ} (f : Curve n)
    {y : Index n → ℂ → ℂ} (hy : ∀ j, Differentiable ℂ (y j)) (h0 : y 0 0 = 1)
    {B CT CN c : ℝ} (hB : 0 ≤ B) (hc : 0 ≤ c)
    (hT : ∀ s : ℝ, 1 ≤ s → characteristic f s ≤ systemLogMaximum y (s + B) + CT)
    (hN : ∀ t : ℝ, 1 ≤ t → systemCounting y t ≤ ramification f (t + B) + CN)
    (hram : ∀ᶠ s : ℝ in atTop, ramification f s ≤ c * characteristic f s) :
    ∃ C : ℝ, ∀ t : ℝ, 0 < t → systemCounting y t ≤ c * systemLogMaximum y (3 * t) + C := by
  have hshift : Tendsto (fun t : ℝ => t + B) atTop atTop :=
    tendsto_atTop_add_const_right atTop B tendsto_id
  have hlarge : ∀ᶠ t : ℝ in atTop,
      systemCounting y t ≤ c * systemLogMaximum y (3 * t) + (c * CT + CN) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop B,
      hshift.eventually hram] with t ht hBt hrt
    have htB : 1 ≤ t + B := by linarith
    have hcomp := hT (t + B) htB
    have hm := systemLogMaximum_monotoneOn (fun j => (hy j).continuous) h0
      (show 0 ≤ t + B + B by linarith)
      (show 0 ≤ 3 * t by linarith) (show t + B + B ≤ 3 * t by linarith)
    have hmult := mul_le_mul_of_nonneg_left (hcomp.trans (add_le_add hm le_rfl)) hc
    have hn := hN t ht
    linarith
  obtain ⟨R, hR⟩ := eventually_atTop.mp hlarge
  let S : ℝ := max 1 R
  refine ⟨max (c * CT + CN) (systemCounting y S), ?_⟩
  intro t ht
  by_cases hRt : R ≤ t
  · exact (hR t hRt).trans (add_le_add le_rfl (le_max_left _ _))
  · have hS : 0 < S := zero_lt_one.trans_le (le_max_left 1 R)
    have htS : t ≤ S := (le_of_not_ge hRt).trans (le_max_right 1 R)
    have hm : systemCounting y t ≤ systemCounting y S :=
      ValueDistribution.logCounting_monotoneOn ht hS htS
    have hnonneg : 0 ≤ c * systemLogMaximum y (3 * t) := mul_nonneg hc
      (systemLogMaximum_nonneg (fun j => (hy j).continuous) h0 (by positivity))
    have hmax := le_max_right (c * CT + CN) (systemCounting y S)
    linarith

theorem smallRamification_eventually_le {n : ℕ} {f : Curve n}
    (hsmall : SmallRamification f) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℝ in atTop, ramification f r ≤ ε * characteristic f r := by
  filter_upwards [hsmall.def hε, eventually_gt_atTop (0 : ℝ)] with r hr hr0
  rw [Real.norm_of_nonneg (characteristic_nonneg f hr0)] at hr
  exact (le_abs_self (ramification f r)).trans hr

/-- LaTeX `eq:small-order-divisor-majorant`, derived from the manuscript's
actual small-ramification hypothesis and both coordinate comparisons. -/
theorem small_order_divisor_majorant {n : ℕ} {f : Curve n}
    (hsmall : SmallRamification f) {y : Index n → ℂ → ℂ}
    (hy : ∀ j, Differentiable ℂ (y j)) (h0 : y 0 0 = 1)
    {B CT CN : ℝ} (hB : 0 ≤ B)
    (hT : ∀ s : ℝ, 1 ≤ s → characteristic f s ≤ systemLogMaximum y (s + B) + CT)
    (hN : ∀ t : ℝ, 1 ≤ t → systemCounting y t ≤ ramification f (t + B) + CN)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ t : ℝ, 0 < t → systemCounting y t ≤ ε * systemLogMaximum y (3 * t) + C :=
  system_divisor_majorant_of_eventual_bound f hy h0 hB hε.le hT hN
    (smallRamification_eventually_le hsmall hε)

end ModifiedCartan
#print axioms ModifiedCartan.system_divisor_majorant_of_eventual_bound
#print axioms ModifiedCartan.small_order_divisor_majorant
