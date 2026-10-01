import ModifiedCartan.SkewAdditions
import ModifiedCartan.MinorGrowthPaths

open scoped BigOperators Classical

namespace ModifiedCartan

noncomputable section

@[simp] theorem fin_rev_val_for_minor {n : ℕ} (i : Fin (n + 1)) :
    (i.rev : ℕ) = n - (i : ℕ) := by
  dsimp [Fin.rev]
  omega

@[simp] theorem reverse_minor_row {n : ℕ} (i : Fin (n + 1)) :
    n - (i.rev : ℕ) = (i : ℕ) := by
  rw [fin_rev_val_for_minor]
  have := i.isLt
  omega

def SkewAddition.minorRow {n : ℕ} {ν μ : YoungDiagram} (r : SkewAddition n ν μ) :
    LegalMinorRow n μ := ⟨r.row.rev, by simpa only [reverse_minor_row] using r.legal⟩

@[simp] theorem SkewAddition.grow_minorRow {n : ℕ} {ν μ : YoungDiagram}
    (r : SkewAddition n ν μ) : growMinorPartition r.minorRow = r.enlarged := by
  simp only [growMinorPartition, SkewAddition.minorRow, reverse_minor_row, SkewAddition.enlarged]

def skewAdditionOfMinorRow {n : ℕ} {ν μ : YoungDiagram} (i : LegalMinorRow n μ)
    (hi : growMinorPartition i ≤ ν) : SkewAddition n ν μ where
  row := i.val.rev
  legal := by simpa only [fin_rev_val_for_minor] using i.property
  inside := by simpa only [fin_rev_val_for_minor, growMinorPartition] using hi

@[simp] theorem skewAdditionOfMinorRow_minorRow {n : ℕ} {ν μ : YoungDiagram}
    (i : LegalMinorRow n μ) (hi : growMinorPartition i ≤ ν) :
    (skewAdditionOfMinorRow i hi).minorRow = i := by
  apply Subtype.ext
  exact Fin.rev_rev i.val

@[simp] theorem SkewAddition.of_minorRow {n : ℕ} {ν μ : YoungDiagram}
    (r : SkewAddition n ν μ) :
    skewAdditionOfMinorRow r.minorRow (by rw [r.grow_minorRow]; exact r.inside) = r := by
  apply SkewAddition.ext
  exact Fin.rev_rev r.row

/-- Reversing row order identifies the determinant and Young-diagram conventions. -/
def legalMinorRowSkewAdditionEquiv (n : ℕ) (ν μ : YoungDiagram) :
    {i : LegalMinorRow n μ // growMinorPartition i ≤ ν} ≃ SkewAddition n ν μ where
  toFun i := skewAdditionOfMinorRow i.val i.property
  invFun r := ⟨r.minorRow, by rw [r.grow_minorRow]; exact r.inside⟩
  left_inv i := Subtype.ext (skewAdditionOfMinorRow_minorRow i.val i.property)
  right_inv r := r.of_minorRow

end
end ModifiedCartan


