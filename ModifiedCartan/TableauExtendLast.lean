import ModifiedCartan.TableauDeleteLast

open scoped Classical

namespace ModifiedCartan
noncomputable section

def youngExtendedLabel (μ : YoungDiagram) (b : YoungCorner μ)
    (S : YoungFilling (removePartitionBox μ b)) (a : YoungBoxes μ) : Fin (partitionSize μ) :=
  if ha : a = b.val then
    ⟨partitionSize (removePartitionBox μ b), by
      have hc := partitionSize_removePartitionBox_add_one μ b
      omega⟩
  else
    ⟨(S (youngBoxAfterRemoval μ b a ha)).val, by
      have hs := (S (youngBoxAfterRemoval μ b a ha)).isLt
      have hc := partitionSize_removePartitionBox_add_one μ b
      omega⟩

theorem youngExtendedLabel_val_corner (μ : YoungDiagram) (b : YoungCorner μ)
    (S : YoungFilling (removePartitionBox μ b)) :
    (youngExtendedLabel μ b S b.val).val = partitionSize (removePartitionBox μ b) := by
  simp [youngExtendedLabel]

theorem youngExtendedLabel_val_of_ne (μ : YoungDiagram) (b : YoungCorner μ)
    (S : YoungFilling (removePartitionBox μ b)) (a : YoungBoxes μ) (ha : a ≠ b.val) :
    (youngExtendedLabel μ b S a).val = (S (youngBoxAfterRemoval μ b a ha)).val := by
  simp [youngExtendedLabel, ha]

theorem youngExtendedLabel_injective (μ : YoungDiagram) (b : YoungCorner μ)
    (S : YoungFilling (removePartitionBox μ b)) : Function.Injective (youngExtendedLabel μ b S) := by
  intro a c he
  have hv := congrArg Fin.val he
  by_cases ha : a = b.val
  · subst a
    by_cases hc : c = b.val
    · exact hc.symm
    · rw [youngExtendedLabel_val_corner, youngExtendedLabel_val_of_ne μ b S c hc] at hv
      have hbound := (S (youngBoxAfterRemoval μ b c hc)).isLt
      omega
  · by_cases hc : c = b.val
    · subst c
      rw [youngExtendedLabel_val_of_ne μ b S a ha, youngExtendedLabel_val_corner] at hv
      have hbound := (S (youngBoxAfterRemoval μ b a ha)).isLt
      omega
    · rw [youngExtendedLabel_val_of_ne μ b S a ha,
        youngExtendedLabel_val_of_ne μ b S c hc] at hv
      have hac := S.injective (Fin.ext hv)
      have hcoord := congrArg (fun x : YoungBoxes (removePartitionBox μ b) => x.val) hac
      exact Subtype.ext hcoord

def youngExtendedFilling (μ : YoungDiagram) (b : YoungCorner μ)
    (S : YoungFilling (removePartitionBox μ b)) : YoungFilling μ :=
  Equiv.ofBijective (youngExtendedLabel μ b S)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨youngExtendedLabel_injective μ b S, Fintype.card_congr μ.cells.equivFin⟩)

theorem youngExtendedFilling_strict (μ : YoungDiagram) (b : YoungCorner μ)
    (S : YoungFilling (removePartitionBox μ b)) (hS : StrictMono S) :
    StrictMono (youngExtendedFilling μ b S) := by
  intro a c hac
  change (youngExtendedLabel μ b S a).val < (youngExtendedLabel μ b S c).val
  by_cases ha : a = b.val
  · subst a
    have he := b.property c.val c.property hac.le
    exact False.elim (hac.ne (Subtype.ext he.symm))
  · by_cases hc : c = b.val
    · subst c
      rw [youngExtendedLabel_val_of_ne μ b S a ha, youngExtendedLabel_val_corner]
      exact (S (youngBoxAfterRemoval μ b a ha)).isLt
    · rw [youngExtendedLabel_val_of_ne μ b S a ha,
        youngExtendedLabel_val_of_ne μ b S c hc]
      exact hS hac

/-- Put the new maximal label in the specified outer corner. -/
def youngExtendedTableau (μ : YoungDiagram) (b : YoungCorner μ)
    (S : StandardYoungTableau (removePartitionBox μ b)) : StandardYoungTableau μ :=
  ⟨youngExtendedFilling μ b S.val, youngExtendedFilling_strict μ b S.val S.property⟩

theorem youngExtendedTableau_corner_label (μ : YoungDiagram) (b : YoungCorner μ)
    (S : StandardYoungTableau (removePartitionBox μ b)) :
    ((youngExtendedTableau μ b S).val b.val).val = partitionSize (removePartitionBox μ b) :=
  youngExtendedLabel_val_corner μ b S.val

theorem youngExtendedTableau_old_label (μ : YoungDiagram) (b : YoungCorner μ)
    (S : StandardYoungTableau (removePartitionBox μ b)) (a : YoungBoxes (removePartitionBox μ b)) :
    ((youngExtendedTableau μ b S).val (youngBoxBeforeRemoval μ b a)).val = (S.val a).val := by
  change (youngExtendedLabel μ b S.val (youngBoxBeforeRemoval μ b a)).val = _
  rw [youngExtendedLabel_val_of_ne μ b S.val _ (youngBoxBeforeRemoval_ne μ b a),
    youngBoxAfterBeforeRemoval]

end
end ModifiedCartan


