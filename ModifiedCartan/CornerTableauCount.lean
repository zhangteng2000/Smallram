import ModifiedCartan.CornerTableauEquiv
import ModifiedCartan.StandardPolytabloidBasis

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem standardTableauCount_remove_recurrence (μ : YoungDiagram) (hpos : 0 < partitionSize μ) :
    standardSkewTableauCount μ ⊥ =
      ∑ b : YoungCorner μ, standardSkewTableauCount (removePartitionBox μ b) ⊥ := by
  rw [← standardYoungTableau_card, Fintype.card_congr (youngTableauCornerEquiv μ hpos),
    Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro b _
  exact standardYoungTableau_card (removePartitionBox μ b)

/-- The dimension identity underlying branching, obtained from actual tableau
bijections. This statement does not assert representation-theoretic branching. -/
theorem finrank_specht_remove_recurrence (μ : YoungDiagram) (hpos : 0 < partitionSize μ) :
    Module.finrank ℂ (YoungSpechtModule μ) =
      ∑ b : YoungCorner μ, Module.finrank ℂ (YoungSpechtModule (removePartitionBox μ b)) := by
  simp_rw [finrank_specht_eq_standardTableauCount]
  exact standardTableauCount_remove_recurrence μ hpos

end
end ModifiedCartan


