import ModifiedCartan.PartitionCovers
import ModifiedCartan.SizedYoungDiagrams

open scoped Classical

namespace ModifiedCartan
noncomputable section

abbrev YoungPredecessor (μ : YoungDiagram) := {ν : YoungDiagram // PartitionCovers μ ν}

def youngPredecessorSized (μ : YoungDiagram) (ν : YoungPredecessor μ) :
    SizedYoungDiagram (partitionSize μ - 1) := ⟨ν.val, by have := ν.property.2; omega⟩

theorem youngPredecessorSized_injective (μ : YoungDiagram) :
    Function.Injective (youngPredecessorSized μ) := by
  intro ν ξ he
  have hh := congrArg (fun τ : SizedYoungDiagram (partitionSize μ - 1) => τ.val) he
  exact Subtype.ext hh

instance (μ : YoungDiagram) : Fintype (YoungPredecessor μ) :=
  Fintype.ofInjective (youngPredecessorSized μ) (youngPredecessorSized_injective μ)

def youngCornerPredecessor (μ : YoungDiagram) (b : YoungCorner μ) : YoungPredecessor μ :=
  ⟨removePartitionBox μ b, removePartitionBox_covers μ b⟩

theorem youngCornerPredecessor_bijective (μ : YoungDiagram) :
    Function.Bijective (youngCornerPredecessor μ) := by
  constructor
  · intro b c he
    exact removePartitionBox_injective μ (congrArg (fun τ : YoungPredecessor μ => τ.val) he)
  · intro ν
    obtain ⟨b, hb⟩ := ν.property.exists_corner_removal
    exact ⟨b, Subtype.ext hb⟩

def youngCornerEquivPredecessor (μ : YoungDiagram) : YoungCorner μ ≃ YoungPredecessor μ :=
  Equiv.ofBijective (youngCornerPredecessor μ) (youngCornerPredecessor_bijective μ)

theorem youngPredecessor_card (μ : YoungDiagram) :
    Fintype.card (YoungPredecessor μ) = Fintype.card (YoungCorner μ) :=
  (Fintype.card_congr (youngCornerEquivPredecessor μ)).symm

end
end ModifiedCartan


