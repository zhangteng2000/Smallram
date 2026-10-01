import ModifiedCartan.CharacteristicZero
import ModifiedCartan.CharacteristicMonotone
import ModifiedCartan.IndexOrderBounds

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

theorem characteristic_pos_of_nonconstant {n : ℕ} (f : Curve n)
    (hnonconstant : ∃ z j k, f.coord j 0 * f.coord k z ≠ f.coord k 0 * f.coord j z)
    {r : ℝ} (hr : 0 < r) : 0 < characteristic f r := by
  rcases eq_or_lt_of_le (characteristic_nonneg f hr) with hz | hp
  · obtain ⟨z, j, k, hneq⟩ := hnonconstant
    exact False.elim (hneq (coordinates_proportional_of_characteristic_zero f hr hz.symm z j k))
  · exact hp

namespace Paper

/-- LaTeX `eq:index-order-bounds` for a nonconstant holomorphic curve.
The coordinate condition says precisely that its projective values are not
all equal to its value at zero; reducedness guarantees that this is intrinsic. -/
theorem eq_index_order_bounds {n : ℕ} (f : Curve n)
    (hnonconstant : ∃ z j k, f.coord j 0 * f.coord k z ≠ f.coord k 0 * f.coord j z) :
    0 ≤ strongLowerIndex (characteristic f) ∧
      strongLowerIndex (characteristic f) ≤ lowerOrder f ∧
      lowerOrder f ≤ order f ∧ order f ≤ strongUpperIndex (characteristic f) := by
  exact strong_index_order_bounds (characteristic f)
    (fun _ hr => characteristic_pos_of_nonconstant f hnonconstant hr)
    (characteristic_monotoneOn f)

theorem eq_index_order_bounds_of_transcendental {n : ℕ} (f : Curve n)
    (htrans : f.Transcendental) :
    0 ≤ strongLowerIndex (characteristic f) ∧
      strongLowerIndex (characteristic f) ≤ lowerOrder f ∧
      lowerOrder f ≤ order f ∧ order f ≤ strongUpperIndex (characteristic f) := by
  exact strong_index_order_bounds (characteristic f)
    (fun _ hr => characteristic_pos_of_transcendental f htrans hr)
    (characteristic_monotoneOn f)

end Paper
end
end ModifiedCartan
#print axioms ModifiedCartan.Paper.eq_index_order_bounds
#print axioms ModifiedCartan.Paper.eq_index_order_bounds_of_transcendental
