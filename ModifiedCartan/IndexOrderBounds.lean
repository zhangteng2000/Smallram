import ModifiedCartan.OrdinaryGrowthOrders
import ModifiedCartan.UniformPowerLogBounds

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

theorem upperGrowthOrder_le_strongUpperIndex (T : ℝ → ℝ)
    (hT : ∀ r, 0 < r → 0 < T r) :
    upperGrowthOrder T ≤ strongUpperIndex T := by
  by_contra h
  obtain ⟨p, hp0, hp1⟩ := EReal.exists_between_coe_real (lt_of_not_ge h)
  obtain ⟨C, X, r0, hC, hX, hr0, hb⟩ := strongUpperIndex_uniform_upper T hT hp0
  obtain ⟨K, hK⟩ := log_upper_of_uniform_power_upper T hT hC hX hr0 hb
  exact (not_le_of_gt hp1) (upperGrowthOrder_le_of_log_upper T hK)

theorem strongLowerIndex_le_lowerGrowthOrder (T : ℝ → ℝ)
    (hT : ∀ r, 0 < r → 0 < T r) :
    strongLowerIndex T ≤ lowerGrowthOrder T := by
  by_contra h
  obtain ⟨p, hp0, hp1⟩ := EReal.exists_between_coe_real (lt_of_not_ge h)
  obtain ⟨c, X, r0, hc, hX, hr0, hb⟩ := strongLowerIndex_uniform_lower T hT hp1
  obtain ⟨K, hK⟩ := log_lower_of_uniform_power_lower T hT hc hX hr0 hb
  exact (not_le_of_gt hp0) (le_lowerGrowthOrder_of_log_lower T hK)

/-- The general positive-monotone-function part of LaTeX `eq:index-order-bounds`.
Specializing to the curve characteristic still requires its proved positivity
and monotonicity, and does not add them to the manuscript hypotheses. -/
theorem strong_index_order_bounds (T : ℝ → ℝ)
    (hT : ∀ r, 0 < r → 0 < T r) (hm : MonotoneOn T (Ioi 0)) :
    0 ≤ strongLowerIndex T ∧ strongLowerIndex T ≤ lowerGrowthOrder T ∧
      lowerGrowthOrder T ≤ upperGrowthOrder T ∧ upperGrowthOrder T ≤ strongUpperIndex T :=
  ⟨strongLowerIndex_nonneg T hT hm, strongLowerIndex_le_lowerGrowthOrder T hT,
    lowerGrowthOrder_le_upperGrowthOrder T, upperGrowthOrder_le_strongUpperIndex T hT⟩

end
end ModifiedCartan
#print axioms ModifiedCartan.strong_index_order_bounds
