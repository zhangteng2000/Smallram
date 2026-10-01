import ModifiedCartan.RemovedBoxes
import ModifiedCartan.TableauLastBox

open scoped Classical

namespace ModifiedCartan
noncomputable section

def youngDeletedLabel (μ : YoungDiagram) (b : YoungCorner μ) (T : YoungFilling μ)
    (htop : (T b.val).val = partitionSize (removePartitionBox μ b))
    (a : YoungBoxes (removePartitionBox μ b)) : Fin (partitionSize (removePartitionBox μ b)) :=
  ⟨(T (youngBoxBeforeRemoval μ b a)).val, by
    have hn : (T (youngBoxBeforeRemoval μ b a)).val ≠ (T b.val).val := by
      intro he
      exact youngBoxBeforeRemoval_ne μ b a (T.injective (Fin.ext he))
    have hh := (T (youngBoxBeforeRemoval μ b a)).isLt
    have hc := partitionSize_removePartitionBox_add_one μ b
    omega⟩

@[simp] theorem youngDeletedLabel_val (μ : YoungDiagram) (b : YoungCorner μ) (T : YoungFilling μ)
    (htop : (T b.val).val = partitionSize (removePartitionBox μ b))
    (a : YoungBoxes (removePartitionBox μ b)) :
    (youngDeletedLabel μ b T htop a).val = (T (youngBoxBeforeRemoval μ b a)).val := rfl

theorem youngDeletedLabel_injective (μ : YoungDiagram) (b : YoungCorner μ) (T : YoungFilling μ)
    (htop : (T b.val).val = partitionSize (removePartitionBox μ b)) :
    Function.Injective (youngDeletedLabel μ b T htop) := by
  intro a c he
  have hv := congrArg (fun x : Fin (partitionSize (removePartitionBox μ b)) => x.val) he
  apply youngBoxBeforeRemoval_injective μ b
  apply T.injective
  exact Fin.ext hv

def youngDeletedFilling (μ : YoungDiagram) (b : YoungCorner μ) (T : YoungFilling μ)
    (htop : (T b.val).val = partitionSize (removePartitionBox μ b)) :
    YoungFilling (removePartitionBox μ b) :=
  Equiv.ofBijective (youngDeletedLabel μ b T htop)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨youngDeletedLabel_injective μ b T htop,
        Fintype.card_congr (removePartitionBox μ b).cells.equivFin⟩)

theorem youngDeletedFilling_strict (μ : YoungDiagram) (b : YoungCorner μ) (T : YoungFilling μ)
    (htop : (T b.val).val = partitionSize (removePartitionBox μ b)) (hT : StrictMono T) :
    StrictMono (youngDeletedFilling μ b T htop) := by
  intro a c hac
  change (T (youngBoxBeforeRemoval μ b a)).val < (T (youngBoxBeforeRemoval μ b c)).val
  exact hT hac

/-- Delete a maximal label at a corner, retaining the other labels exactly. -/
def youngDeletedTableau (μ : YoungDiagram) (b : YoungCorner μ) (T : StandardYoungTableau μ)
    (htop : (T.val b.val).val = partitionSize (removePartitionBox μ b)) :
    StandardYoungTableau (removePartitionBox μ b) :=
  ⟨youngDeletedFilling μ b T.val htop, youngDeletedFilling_strict μ b T.val htop T.property⟩

@[simp] theorem youngDeletedTableau_label (μ : YoungDiagram) (b : YoungCorner μ)
    (T : StandardYoungTableau μ)
    (htop : (T.val b.val).val = partitionSize (removePartitionBox μ b))
    (a : YoungBoxes (removePartitionBox μ b)) :
    ((youngDeletedTableau μ b T htop).val a).val =
      (T.val (youngBoxBeforeRemoval μ b a)).val := rfl

end
end ModifiedCartan


