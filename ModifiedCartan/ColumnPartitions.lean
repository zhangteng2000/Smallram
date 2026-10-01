import ModifiedCartan.RowColumnFiniteCharacters
import ModifiedCartan.KPOperators

open scoped Classical

namespace ModifiedCartan
noncomputable section

/-- The actual single-column diagram with `k` boxes. -/
def columnPartition (k : ℕ) : YoungDiagram where
  cells := Finset.range k ×ˢ {0}
  isLowerSet := by
    intro a b hba ha
    rcases Finset.mem_product.mp ha with ⟨ha₁, ha₂⟩
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_range.mpr (hba.1.trans_lt (Finset.mem_range.mp ha₁)), ?_⟩
    simp only [Finset.mem_singleton] at ha₂ ⊢
    exact Nat.eq_zero_of_le_zero (ha₂ ▸ hba.2)

theorem partitionSize_columnPartition (k : ℕ) : partitionSize (columnPartition k) = k := by
  simp [partitionSize, columnPartition]

theorem columnPartition_column (k : ℕ) (b : YoungBoxes (columnPartition k)) : b.val.2 = 0 :=
  Finset.mem_singleton.mp (Finset.mem_product.mp b.property).2

theorem spechtCharacterOn_columnPartition {A : Type*} [Fintype A] [DecidableEq A]
    (k : ℕ) (h : Fintype.card A = partitionSize (columnPartition k)) (g : Equiv.Perm A) :
    spechtCharacterOn (columnPartition k) h g = ((Equiv.Perm.sign g : ℤ) : ℂ) :=
  spechtCharacterOn_single_column _ h (columnPartition_column k) g

end
end ModifiedCartan


