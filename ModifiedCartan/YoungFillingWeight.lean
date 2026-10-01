import ModifiedCartan.GarnirMixing
import ModifiedCartan.TwoBlockWeightedSum
import ModifiedCartan.ColumnSorting

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

/-- A natural-number measure for Garnir straightening. Sorting a column leaves
this measure unchanged; a mixed Garnir term at a row inversion decreases it. -/
def youngFillingWeight (μ : YoungDiagram) (T : YoungFilling μ) : ℕ :=
  ∑ b : YoungBoxes μ, (μ.rowLen 0 - b.val.2) * (T b).val

theorem youngFillingWeight_column (μ : YoungDiagram) (T : YoungFilling μ)
    (c : youngColumnSubgroup μ) :
    youngFillingWeight μ (c.val.trans T) = youngFillingWeight μ T := by
  unfold youngFillingWeight
  calc
    _ = ∑ b : YoungBoxes μ, (μ.rowLen 0 - (c.val b).val.2) * (T (c.val b)).val := by
      apply Finset.sum_congr rfl
      intro b _
      have hc : (c.val b).val.2 = b.val.2 := c.property b
      rw [hc]
      rfl
    _ = _ := Equiv.sum_comp c.val (fun b => (μ.rowLen 0 - b.val.2) * (T b).val)

/-- A strict decrease holds before sorting and hence also after sorting. -/
theorem youngFillingWeight_garnir_lt (μ : YoungDiagram) (T : YoungFilling μ)
    (hT : YoungColumnStandard T) (r j : ℕ) (hl : (r, j) ∈ μ) (hr : (r, j + 1) ∈ μ)
    (hinv : T ⟨(r, j + 1), hr⟩ < T ⟨(r, j), hl⟩)
    (g : supportedPermutationSubgroup (garnirBelt μ r j))
    (hg : g ∈ garnirMixingPermutations μ r j) :
    youngFillingWeight μ (g.val.trans T) < youngFillingWeight μ T := by
  have hj : j + 1 < μ.rowLen 0 := YoungDiagram.mem_iff_lt_rowLen.mp
    (μ.up_left_mem (Nat.zero_le r) le_rfl hr)
  apply two_block_weighted_sum_lt (garnirLeft μ r j) (garnirRight μ r j)
    (garnirLeft_disjoint_right μ r j) g
    (fun b => μ.rowLen 0 - b.val.2) (fun b => (T b).val) (μ.rowLen 0 - (j + 1))
  · intro a ha
    rw [((mem_garnirLeft μ r j a).mp ha).1]
    omega
  · intro a ha
    rw [((mem_garnirRight μ r j a).mp ha).1]
  · exact garnir_mixing_left_sum_lt μ T hT r j hl hr hinv g hg

end
end ModifiedCartan


