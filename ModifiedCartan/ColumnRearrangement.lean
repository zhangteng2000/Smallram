import ModifiedCartan.ColumnPermutations
import ModifiedCartan.StrictPermutationWeight
import ModifiedCartan.YoungFillings

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

def youngColumnFilling (μ : YoungDiagram) (T : YoungFilling μ) (j : Fin (μ.rowLen 0)) :
    Fin (μ.colLen j.val) → ℕ := fun r => (T ((youngColumnEquiv μ j r).val)).val

theorem youngColumnFilling_strict (μ : YoungDiagram) (T : YoungFilling μ)
    (hT : YoungColumnStandard T) (j : Fin (μ.rowLen 0)) :
    StrictMono (youngColumnFilling μ T j) := by
  intro a b hab
  exact hT _ _ hab rfl

theorem youngColumn_weighted_sum_le (μ : YoungDiagram) (T : YoungFilling μ)
    (hT : YoungColumnStandard T) (c : youngColumnSubgroup μ) (j : Fin (μ.rowLen 0)) :
    (∑ b : YoungColumnBoxes μ j, (c.val b.val).val.1 * (T b.val).val) ≤
      ∑ b : YoungColumnBoxes μ j, b.val.val.1 * (T b.val).val := by
  rw [← Equiv.sum_comp (youngColumnEquiv μ j)
      (fun b => (c.val b.val).val.1 * (T b.val).val),
    ← Equiv.sum_comp (youngColumnEquiv μ j) (fun b => b.val.val.1 * (T b.val).val)]
  exact fin_strictMono_weighted_sum_perm_le (youngColumnFilling μ T j)
    (youngColumnFilling_strict μ T hT j) (youngColumnPermutation μ c j)

theorem youngColumn_weighted_sum_lt (μ : YoungDiagram) (T : YoungFilling μ)
    (hT : YoungColumnStandard T) (c : youngColumnSubgroup μ) (j : Fin (μ.rowLen 0))
    (hc : youngColumnPermutation μ c j ≠ 1) :
    (∑ b : YoungColumnBoxes μ j, (c.val b.val).val.1 * (T b.val).val) <
      ∑ b : YoungColumnBoxes μ j, b.val.val.1 * (T b.val).val := by
  rw [← Equiv.sum_comp (youngColumnEquiv μ j)
      (fun b => (c.val b.val).val.1 * (T b.val).val),
    ← Equiv.sum_comp (youngColumnEquiv μ j) (fun b => b.val.val.1 * (T b.val).val)]
  exact fin_strictMono_weighted_sum_perm_lt (youngColumnFilling μ T j)
    (youngColumnFilling_strict μ T hT j) (youngColumnPermutation μ c j) hc

/-- A nonidentity column permutation strictly lowers the row-label weight of
a column-standard filling. -/
theorem youngColumn_total_weighted_sum_lt (μ : YoungDiagram) (T : YoungFilling μ)
    (hT : YoungColumnStandard T) (c : youngColumnSubgroup μ) (hc : c ≠ 1) :
    (∑ b : YoungBoxes μ, (c.val b).val.1 * (T b).val) <
      ∑ b : YoungBoxes μ, b.val.1 * (T b).val := by
  rw [← young_sum_columns μ (fun b => (c.val b).val.1 * (T b).val),
    ← young_sum_columns μ (fun b => b.val.1 * (T b).val)]
  apply Finset.sum_lt_sum
  · intro j _
    exact youngColumn_weighted_sum_le μ T hT c j
  · obtain ⟨j, hj⟩ := youngColumn_exists_nontrivial_restriction μ c hc
    exact ⟨j, Finset.mem_univ _, youngColumn_weighted_sum_lt μ T hT c j hj⟩

end
end ModifiedCartan


