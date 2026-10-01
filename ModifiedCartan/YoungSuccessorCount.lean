import ModifiedCartan.PartitionCoverAddition
import ModifiedCartan.AddableRowsCornerEquiv
import ModifiedCartan.SizedYoungDiagrams

open scoped Classical

namespace ModifiedCartan
noncomputable section

abbrev YoungSuccessor (μ : YoungDiagram) := {ν : YoungDiagram // PartitionCovers ν μ}

def youngSuccessorSized (μ : YoungDiagram) (ν : YoungSuccessor μ) :
    SizedYoungDiagram (partitionSize μ + 1) := ⟨ν.val, ν.property.2⟩

theorem youngSuccessorSized_injective (μ : YoungDiagram) : Function.Injective (youngSuccessorSized μ) := by
  intro ν ξ he
  have hh := congrArg (fun τ : SizedYoungDiagram (partitionSize μ + 1) => τ.val) he
  exact Subtype.ext hh

instance (μ : YoungDiagram) : Fintype (YoungSuccessor μ) :=
  Fintype.ofInjective (youngSuccessorSized μ) (youngSuccessorSized_injective μ)

def youngAddableRowSuccessor (μ : YoungDiagram) (r : YoungAddableRow μ) : YoungSuccessor μ :=
  ⟨addPartitionBox μ r.val r.property, addPartitionBox_covers μ r.val r.property⟩

theorem youngAddableRowSuccessor_bijective (μ : YoungDiagram) :
    Function.Bijective (youngAddableRowSuccessor μ) := by
  constructor
  · intro r s he
    have hh := congrArg (fun ν : YoungSuccessor μ => ν.val) he
    apply Subtype.ext
    apply Fin.ext
    exact addPartitionBox_row_injective μ r.val s.val r.property s.property hh
  · intro ν
    obtain ⟨r, hr, hbound, he⟩ := ν.property.exists_row_addition
    refine ⟨⟨⟨r, Nat.lt_succ_of_le hbound⟩, hr⟩, Subtype.ext he⟩

def youngAddableRowEquivSuccessor (μ : YoungDiagram) : YoungAddableRow μ ≃ YoungSuccessor μ :=
  Equiv.ofBijective (youngAddableRowSuccessor μ) (youngAddableRowSuccessor_bijective μ)

/-- Young's lattice has one more immediate successor than immediate predecessors. -/
theorem youngSuccessor_card (μ : YoungDiagram) :
    Fintype.card (YoungSuccessor μ) = Fintype.card (YoungCorner μ) + 1 := by
  rw [← Fintype.card_congr (youngAddableRowEquivSuccessor μ), youngAddableRow_card]

end
end ModifiedCartan


