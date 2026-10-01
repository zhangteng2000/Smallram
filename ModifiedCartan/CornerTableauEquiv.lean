import ModifiedCartan.TableauExtendLast

open scoped Classical

namespace ModifiedCartan
noncomputable section

theorem youngDeletedTableau_extended (μ : YoungDiagram) (b : YoungCorner μ)
    (S : StandardYoungTableau (removePartitionBox μ b)) :
    youngDeletedTableau μ b (youngExtendedTableau μ b S)
      (youngExtendedTableau_corner_label μ b S) = S := by
  apply Subtype.ext
  apply Equiv.ext
  intro a
  apply Fin.ext
  rw [youngDeletedTableau_label, youngExtendedTableau_old_label]

theorem youngExtendedTableau_deleted (μ : YoungDiagram) (b : YoungCorner μ)
    (T : StandardYoungTableau μ)
    (htop : (T.val b.val).val = partitionSize (removePartitionBox μ b)) :
    youngExtendedTableau μ b (youngDeletedTableau μ b T htop) = T := by
  apply Subtype.ext
  apply Equiv.ext
  intro a
  apply Fin.ext
  by_cases ha : a = b.val
  · subst a
    rw [youngExtendedTableau_corner_label]
    exact htop.symm
  · change (youngExtendedLabel μ b (youngDeletedTableau μ b T htop).val a).val = (T.val a).val
    rw [youngExtendedLabel_val_of_ne μ b _ a ha,
      youngDeletedTableau_label, youngBoxBeforeAfterRemoval]

def youngCornerTableauEquiv (μ : YoungDiagram) (b : YoungCorner μ) :
    {T : StandardYoungTableau μ // (T.val b.val).val = partitionSize (removePartitionBox μ b)} ≃
      StandardYoungTableau (removePartitionBox μ b) where
  toFun T := youngDeletedTableau μ b T.val T.property
  invFun S := ⟨youngExtendedTableau μ b S, youngExtendedTableau_corner_label μ b S⟩
  left_inv T := Subtype.ext (youngExtendedTableau_deleted μ b T.val T.property)
  right_inv S := youngDeletedTableau_extended μ b S

theorem youngTableauLastBox_eq_iff (μ : YoungDiagram) (hpos : 0 < partitionSize μ)
    (T : StandardYoungTableau μ) (b : YoungCorner μ) :
    youngTableauLastBox μ hpos T = b ↔
      (T.val b.val).val = partitionSize (removePartitionBox μ b) := by
  constructor
  · intro he
    rw [← he]
    exact youngTableauLastBox_label_val μ hpos T
  · intro htop
    apply Subtype.ext
    apply T.val.injective
    apply Fin.ext
    rw [youngTableauLastBox_label]
    change partitionSize μ - 1 = (T.val b.val).val
    rw [htop, partitionSize_removePartitionBox]

def youngLastBoxFiberEquiv (μ : YoungDiagram) (hpos : 0 < partitionSize μ) (b : YoungCorner μ) :
    {T : StandardYoungTableau μ // youngTableauLastBox μ hpos T = b} ≃
      StandardYoungTableau (removePartitionBox μ b) :=
  (Equiv.subtypeEquivRight (fun T => youngTableauLastBox_eq_iff μ hpos T b)).trans
    (youngCornerTableauEquiv μ b)

/-- Standard tableaux split bijectively according to the removable corner
occupied by their largest label. -/
def youngTableauCornerEquiv (μ : YoungDiagram) (hpos : 0 < partitionSize μ) :
    StandardYoungTableau μ ≃ Σ b : YoungCorner μ, StandardYoungTableau (removePartitionBox μ b) :=
  (Equiv.sigmaFiberEquiv (youngTableauLastBox μ hpos)).symm.trans
    (Equiv.sigmaCongrRight (youngLastBoxFiberEquiv μ hpos))

end
end ModifiedCartan


