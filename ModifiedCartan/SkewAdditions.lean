import ModifiedCartan.TableauFirstBox
import ModifiedCartan.SkewBoxInsertion

open scoped BigOperators Classical

namespace ModifiedCartan

noncomputable section

/-- A legal first addition that stays inside the outer partition. -/
@[ext] structure SkewAddition (n : ℕ) (ν μ : YoungDiagram) where
  row : Fin (n + 1)
  legal : AddablePartitionRow μ row
  inside : addPartitionBox μ row legal ≤ ν

instance (n : ℕ) (ν μ : YoungDiagram) : Fintype (SkewAddition n ν μ) :=
  Fintype.ofInjective SkewAddition.row (fun a b h => SkewAddition.ext h)

def SkewAddition.enlarged {n : ℕ} {ν μ : YoungDiagram} (r : SkewAddition n ν μ) :
    YoungDiagram := addPartitionBox μ r.row r.legal

theorem SkewAddition.newBox_mem {n : ℕ} {ν μ : YoungDiagram} (r : SkewAddition n ν μ) :
    ((r.row : ℕ), μ.rowLen r.row) ∈ ν :=
  r.inside ((mem_addPartitionBox _ _ _ _).mpr (Or.inl rfl))

def SkewAddition.newBox {n : ℕ} {ν μ : YoungDiagram} (r : SkewAddition n ν μ) :
    SkewPartitionBoxes ν μ := ⟨((r.row : ℕ), μ.rowLen r.row), addedBox_mem_skew r.newBox_mem⟩

namespace StandardSkewTableau

def firstAddition {n : ℕ} {ν μ : YoungDiagram} (T : StandardSkewTableau ν μ)
    (hμν : μ ≤ ν) (hν : PartitionFits n ν) (hp : 0 < (ν.cells \ μ.cells).card) :
    SkewAddition n ν μ where
  row := ⟨(T.firstBox hp).val.1,
    hν.row_lt_of_mem (Finset.mem_sdiff.mp (T.firstBox hp).property).1⟩
  legal := T.firstBox_addable hp
  inside := T.addBox_le_of_label_zero hμν (T.firstBox hp) (T.firstBox_label hp)

theorem firstAddition_newBox {n : ℕ} {ν μ : YoungDiagram} (T : StandardSkewTableau ν μ)
    (hμν : μ ≤ ν) (hν : PartitionFits n ν) (hp : 0 < (ν.cells \ μ.cells).card) :
    (T.firstAddition hμν hν hp).newBox = T.firstBox hp := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact (T.column_eq_rowLen_of_label_zero _ (T.firstBox_label hp)).symm

theorem firstAddition_label {n : ℕ} {ν μ : YoungDiagram} (T : StandardSkewTableau ν μ)
    (hμν : μ ≤ ν) (hν : PartitionFits n ν) (hp : 0 < (ν.cells \ μ.cells).card) :
    (T.val (T.firstAddition hμν hν hp).newBox : ℕ) = 0 := by
  rw [T.firstAddition_newBox]
  exact T.firstBox_label hp

theorem firstAddition_eq_iff_label_zero {n : ℕ} {ν μ : YoungDiagram}
    (T : StandardSkewTableau ν μ) (hμν : μ ≤ ν) (hν : PartitionFits n ν)
    (hp : 0 < (ν.cells \ μ.cells).card) (r : SkewAddition n ν μ) :
    T.firstAddition hμν hν hp = r ↔ (T.val r.newBox : ℕ) = 0 := by
  constructor
  · rintro rfl
    exact T.firstAddition_label hμν hν hp
  · intro hz
    have hbox : T.firstBox hp = r.newBox := by
      apply T.val.injective
      apply Fin.ext
      rw [T.firstBox_label hp, hz]
    apply SkewAddition.ext
    apply Fin.ext
    exact congrArg (fun c : SkewPartitionBoxes ν μ => c.val.1) hbox

end StandardSkewTableau
end
end ModifiedCartan


