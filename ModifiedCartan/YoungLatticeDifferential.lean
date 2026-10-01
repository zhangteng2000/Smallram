import ModifiedCartan.YoungSuccessorCount
import ModifiedCartan.YoungPredecessorCount
import ModifiedCartan.PartitionCommonCoverGeometry

open scoped Classical

namespace ModifiedCartan
noncomputable section

abbrev YoungCommonSuccessor (μ ν : YoungDiagram) :=
  {ξ : YoungSuccessor μ // PartitionCovers ξ.val ν}

abbrev YoungCommonPredecessor (μ ν : YoungDiagram) :=
  {δ : YoungPredecessor μ // PartitionCovers ν δ.val}

/-- For different diagrams of equal size, common lower and upper covers correspond
by intersection and union of the actual cell sets. -/
def youngCommonCoverEquiv (μ ν : YoungDiagram) (hs : partitionSize μ = partitionSize ν) (hne : μ ≠ ν) :
    YoungCommonPredecessor μ ν ≃ YoungCommonSuccessor μ ν where
  toFun δ :=
    let hh := common_sup_covers_of_lower μ ν δ.val.val hs hne δ.val.property δ.property
    ⟨⟨μ ⊔ ν, hh.1⟩, hh.2⟩
  invFun ξ :=
    let hh := common_inf_covers_of_upper μ ν ξ.val.val hs hne ξ.val.property ξ.property
    ⟨⟨μ ⊓ ν, hh.1⟩, hh.2⟩
  left_inv δ := by
    apply Subtype.ext
    apply Subtype.ext
    exact (common_lower_eq_inf μ ν δ.val.val hs hne δ.val.property δ.property).symm
  right_inv ξ := by
    apply Subtype.ext
    apply Subtype.ext
    exact (common_upper_eq_sup μ ν ξ.val.val hs hne ξ.val.property ξ.property).symm

def youngCommonSuccessorSelfEquiv (μ : YoungDiagram) : YoungCommonSuccessor μ μ ≃ YoungSuccessor μ where
  toFun := Subtype.val
  invFun ξ := ⟨ξ, ξ.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def youngCommonPredecessorSelfEquiv (μ : YoungDiagram) : YoungCommonPredecessor μ μ ≃ YoungPredecessor μ where
  toFun := Subtype.val
  invFun δ := ⟨δ, δ.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The differential relation of Young's lattice, stated as exact finite cover counts. -/
theorem young_lattice_differential_card (μ ν : YoungDiagram) (hs : partitionSize μ = partitionSize ν) :
    Fintype.card (YoungCommonSuccessor μ ν) =
      Fintype.card (YoungCommonPredecessor μ ν) + if μ = ν then 1 else 0 := by
  by_cases he : μ = ν
  · subst ν
    rw [Fintype.card_congr (youngCommonSuccessorSelfEquiv μ),
      Fintype.card_congr (youngCommonPredecessorSelfEquiv μ), youngSuccessor_card, youngPredecessor_card]
    simp
  · rw [ite_eq_right he, add_zero]
    exact (Fintype.card_congr (youngCommonCoverEquiv μ ν hs he)).symm

end
end ModifiedCartan


