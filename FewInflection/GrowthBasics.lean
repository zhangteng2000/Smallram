import FewInflection.VectorJensen

open scoped BigOperators Topology
open Filter Asymptotics

namespace FewInflection

noncomputable section

/-! Elementary order facts that are independent of the main regularity
theorem.  The first is the general liminf/limsup inequality, while the second
uses the eventual nonnegativity of the logarithmic growth ratio. -/

theorem lowerOrder_le_order {n : ℕ} (f : Curve n) :
    lowerOrder f ≤ order f := by
  unfold lowerOrder order
  exact liminf_le_limsup

/-! A filter limit of the normalized logarithmic ratio determines both order
    notions.  This isolates the order-theoretic step used repeatedly after a
    growth estimate has been established. -/
theorem order_and_lowerOrder_eq_of_logGrowthRatio_tendsto
    {n : ℕ} (f : Curve n) {ρ : EReal}
    (hρ : Tendsto (logGrowthRatio f) atTop (𝓝 ρ)) :
    order f = ρ ∧ lowerOrder f = ρ := by
  constructor
  · unfold order
    exact hρ.limsup_eq
  · unfold lowerOrder
    exact hρ.liminf_eq

theorem finiteLowerOrder_of_logGrowthRatio_tendsto
    {n : ℕ} (f : Curve n) {ρ : ℝ}
    (hρ : Tendsto (logGrowthRatio f) atTop (𝓝 (ρ : EReal))) :
    FiniteLowerOrder f := by
  unfold FiniteLowerOrder
  rw [order_and_lowerOrder_eq_of_logGrowthRatio_tendsto f hρ |>.2]
  exact EReal.coe_lt_top ρ

theorem tendsto_real_coe_ereal_zero {α : Type*} {l : Filter α}
    {u : α → ℝ} (hu : Tendsto u l (𝓝 0)) :
    Tendsto (fun x => (u x : EReal)) l (𝓝 (0 : EReal)) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    cases a with
    | bot => filter_upwards [] with x; simp
    | coe a =>
      have ha' : a < (0 : ℝ) := by simpa using ha
      have h := (tendsto_order.1 hu).1 a ha'
      filter_upwards [h] with x hx
      exact EReal.coe_lt_coe_iff.2 hx
    | top => simp at ha
  · intro a ha
    cases a with
    | bot => simp at ha
    | coe a =>
      have ha' : (0 : ℝ) < a := by simpa using ha
      have h := (tendsto_order.1 hu).2 a ha'
      filter_upwards [h] with x hx
      exact EReal.coe_lt_coe_iff.2 hx
    | top => filter_upwards [] with x; simp

theorem order_nonneg {n : ℕ} (f : Curve n) :
    (0 : EReal) ≤ order f := by
  unfold order
  exact le_limsup_of_frequently_le
    (logGrowthRatio_eventually_nonneg f).frequently

theorem characteristic_nonneg_eventually {n : ℕ} (f : Curve n) :
    0 ≤ᶠ[atTop] characteristic f := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  exact characteristic_nonneg_of_reduced_curve f hr

/- The ramification is a zero-counting function of the entire Wronskian.
   Mathlib's logarithmic-counting API therefore gives its eventual
   nonnegativity and monotonicity directly, without any Jensen hypothesis at
   the centre. -/
theorem ramification_nonneg_eventually {n : ℕ} (f : Curve n) :
    0 ≤ᶠ[atTop] ramification f := by
  unfold ramification
  exact ValueDistribution.logCounting_eventually_nonneg

theorem ramification_monotoneOn {n : ℕ} (f : Curve n) :
    MonotoneOn (ramification f) (Set.Ioi (0 : ℝ)) := by
  unfold ramification
  exact ValueDistribution.logCounting_monotoneOn

end

end FewInflection
