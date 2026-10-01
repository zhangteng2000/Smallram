import FewInflection.Results
import FewInflection.Growth.PowerBounds

open scoped Topology
open Filter

namespace FewInflection

noncomputable section

/-- The explicit two-sided growth clause in a realization witness already
determines its order and lower order. -/
theorem RealizationWitness.order_lowerOrder_eq
    {n : ℕ} {ρ : ℝ} (w : RealizationWitness n ρ) (hρ : 0 < ρ) :
    order w.curve = (ρ : EReal) ∧ lowerOrder w.curve = (ρ : EReal) := by
  rcases w.two_sided_growth with ⟨c, C, r₀, hc, hC, hr₀, hbounds⟩
  apply order_lowerOrder_eq_of_two_sided_power_bounds w.curve hc hC hρ
  filter_upwards [eventually_ge_atTop r₀] with r hr
  exact hbounds r hr

/-! A realization witness becomes a `MainConclusion` as soon as the
regular-variation and factor assertions have been established.  The order
equalities are derived from the witness' actual two-sided growth field. -/
def RealizationWitness.mainConclusion
    {n : ℕ} {ρ : ℝ} (w : RealizationWitness n ρ) (hρ : 0 < ρ)
    (hAdm : AdmissibleOrder n ρ)
    (hreg : RegularlyVarying (characteristic w.curve) ρ)
    (hslow : ∃ ℓ : ℝ → ℝ, SlowlyVarying ℓ ∧
      ∀ᶠ r in atTop, characteristic w.curve r = Real.rpow r ρ * ℓ r) :
    MainConclusion w.curve := by
  have horders := w.order_lowerOrder_eq hρ
  exact ⟨ρ, horders.1.trans horders.2.symm, horders.1, horders.2,
    hAdm, hreg, hslow⟩

end

end FewInflection
