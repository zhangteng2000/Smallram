import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open scoped BigOperators Classical

namespace ModifiedCartan

/-- Double counting with a weight on the other endpoint of a two-edge path. -/
theorem finite_weighted_common_neighbors {U V : Type*} [Fintype U] [Fintype V]
    (R : U → V → Prop) (f : U → ℕ) (a : U) :
    (∑ v : V, if R a v then ∑ b : U, if R b v then f b else 0 else 0) =
      ∑ b : U, Fintype.card {v : V // R a v ∧ R b v} * f b := by
  classical
  calc
    _ = ∑ v : V, ∑ b : U, if R a v ∧ R b v then f b else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases hv : R a v <;> simp [hv]
    _ = ∑ b : U, ∑ v : V, if R a v ∧ R b v then f b else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      rw [← Finset.sum_filter]
      simp [Fintype.card_subtype]

end ModifiedCartan


