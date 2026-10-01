import ModifiedCartan.YoungColumns
import ModifiedCartan.FiniteRowMinimum

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem youngColumn_function_injective (μ : YoungDiagram) (f : YoungBoxes μ → ℕ)
    (hf : ∀ a b, a.val.2 = b.val.2 → f a = f b → a = b) (j : Fin (μ.rowLen 0)) :
    Function.Injective (fun b : YoungColumnBoxes μ j => f b.val) := by
  intro a b hab
  apply Subtype.ext
  apply hf a.val b.val
  · exact congrArg Fin.val (a.property.trans b.property.symm)
  · exact hab

theorem youngColumn_sum_min (μ : YoungDiagram) (f : YoungBoxes μ → ℕ)
    (hf : ∀ a b, a.val.2 = b.val.2 → f a = f b → a = b) (j : Fin (μ.rowLen 0)) :
    (∑ b : YoungColumnBoxes μ j, b.val.val.1) ≤ ∑ b : YoungColumnBoxes μ j, f b.val := by
  rw [youngColumnBoxes_row_sum]
  have h := fintype_nat_sum_min_of_injective (fun b : YoungColumnBoxes μ j => f b.val)
    (youngColumn_function_injective μ f hf j)
  rw [youngColumnBoxes_card] at h
  exact h

/-- A column-injective row assignment with the original total row sum stays in the diagram. -/
theorem youngColumn_assignment_mem (μ : YoungDiagram) (f : YoungBoxes μ → ℕ)
    (hf : ∀ a b, a.val.2 = b.val.2 → f a = f b → a = b)
    (hs : (∑ b : YoungBoxes μ, f b) = ∑ b : YoungBoxes μ, b.val.1) (b : YoungBoxes μ) :
    (f b, b.val.2) ∈ μ.cells := by
  have heq : (∑ j : Fin (μ.rowLen 0), ∑ c : YoungColumnBoxes μ j, c.val.val.1) =
      ∑ j : Fin (μ.rowLen 0), ∑ c : YoungColumnBoxes μ j, f c.val := by
    rw [young_sum_columns μ (fun c => c.val.1), young_sum_columns μ f]
    exact hs.symm
  have hp := (Finset.sum_eq_sum_iff_of_le (fun (j : Fin (μ.rowLen 0))
    (_ : j ∈ Finset.univ) => youngColumn_sum_min μ f hf j)).mp heq
  let j := youngColumnIndex μ b
  have hj := hp j (Finset.mem_univ j)
  rw [youngColumnBoxes_row_sum] at hj
  have hj' : (∑ i : Fin (Fintype.card (YoungColumnBoxes μ j)), i.val) =
      ∑ c : YoungColumnBoxes μ j, f c.val := by
    rw [youngColumnBoxes_card]
    exact hj
  have hb := fintype_nat_lt_card_of_min_sum (fun c : YoungColumnBoxes μ j => f c.val)
    (youngColumn_function_injective μ f hf j) hj' ⟨b, rfl⟩
  rw [youngColumnBoxes_card] at hb
  exact YoungDiagram.mem_iff_lt_colLen.mpr hb

end
end ModifiedCartan


