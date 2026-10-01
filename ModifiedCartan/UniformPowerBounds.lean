import ModifiedCartan.StrongGrowthIndices
import ModifiedCartan.GrowthMultiplierBounds
import ModifiedCartan.GrowthPowerSymmetry

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

/-- LaTeX `lem:power-bounds` and `eq:power-bounds`, derived from the actual
joint-limit Drasin--Shea indices. No power bound is assumed. -/
theorem Paper.lem_power_bounds (T : ℝ → ℝ)
    (hT : ∀ r, 0 < r → 0 < T r) (hmono : MonotoneOn T (Ioi 0))
    (_hunbounded : ∀ M : ℝ, ∃ r : ℝ, 0 < r ∧ M < T r)
    {ρ ε : ℝ} (_hρ : 0 < ρ)
    (hlower : strongLowerIndex T = (ρ : EReal))
    (hupper : strongUpperIndex T = (ρ : EReal))
    (hε : 0 < ε) (hερ : ε < ρ) :
    ∃ C r0 : ℝ, 1 ≤ C ∧ 0 < r0 ∧ ∀ t r : ℝ, r0 ≤ r → r0 ≤ t * r →
      C⁻¹ * min (t ^ (ρ - ε)) (t ^ (ρ + ε)) ≤ T (t * r) / T r ∧
        T (t * r) / T r ≤ C * max (t ^ (ρ - ε)) (t ^ (ρ + ε)) := by
  have hlow : ((ρ - ε : ℝ) : EReal) < strongLowerIndex T := by
    rw [hlower]
    exact_mod_cast (sub_lt_self ρ hε)
  have hupp : strongUpperIndex T < ((ρ + ε : ℝ) : EReal) := by
    rw [hupper]
    exact_mod_cast (lt_add_of_pos_right ρ hε)
  obtain ⟨c, Xl, rl, hc, hXl, hrl, hbl⟩ := strongLowerIndex_uniform_lower T hT hlow
  obtain ⟨D, Xu, ru, hD, hXu, hru, hbu⟩ := strongUpperIndex_uniform_upper T hT hupp
  obtain ⟨a, ha, hla⟩ := extend_growth_lower_to_one T hT hmono (by linarith : 0 ≤ ρ - ε)
    hc hXl (zero_lt_one.trans_le hrl) hbl
  obtain ⟨b, hb, hub⟩ := extend_growth_upper_to_one T hT hmono (by linarith : 0 ≤ ρ + ε)
    hD hXu (zero_lt_one.trans_le hru) hbu
  let r0 := max rl ru
  have hr0 : 0 < r0 := (zero_lt_one.trans_le hrl).trans_le (le_max_left _ _)
  obtain ⟨C, hC, hbound⟩ := common_growth_power_constant T ha hb
    (r0 := r0)
    (fun x r hx hr => hla x r hx ((le_max_left _ _).trans hr))
    (fun x r hx hr => hub x r hx ((le_max_right _ _).trans hr))
  refine ⟨C, r0, hC, hr0, ?_⟩
  intro t r hr htr
  have hrpos := hr0.trans_le hr
  have htrpos := hr0.trans_le htr
  have ht : 0 < t := by
    by_contra h
    have hm := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) hrpos.le
    linarith
  exact symmetric_growth_power_bounds_of_ge_one T hT hC hr0 hbound t r ht hr htr

end
end ModifiedCartan
#print axioms ModifiedCartan.Paper.lem_power_bounds
