import ModifiedCartan.SkewAdditions
import ModifiedCartan.TableauFirstBoxEquiv

open scoped BigOperators Classical

namespace ModifiedCartan

noncomputable section

namespace StandardSkewTableau

def firstAdditionFiberEquiv {n : ℕ} {ν μ : YoungDiagram}
    (hμν : μ ≤ ν) (hν : PartitionFits n ν) (hp : 0 < (ν.cells \ μ.cells).card)
    (r : SkewAddition n ν μ) :
    {T : StandardSkewTableau ν μ // T.firstAddition hμν hν hp = r} ≃
      StandardSkewTableau ν r.enlarged :=
  (Equiv.subtypeEquivRight (fun T => T.firstAddition_eq_iff_label_zero hμν hν hp r)).trans
    (firstBoxEquiv r.legal r.newBox_mem)

theorem card_eq_sum_first_additions {n : ℕ} {ν μ : YoungDiagram}
    (hμν : μ ≤ ν) (hν : PartitionFits n ν) (hp : 0 < (ν.cells \ μ.cells).card) :
    Fintype.card (StandardSkewTableau ν μ) =
      ∑ r : SkewAddition n ν μ, Fintype.card (StandardSkewTableau ν r.enlarged) := by
  let f : StandardSkewTableau ν μ → SkewAddition n ν μ :=
    fun T => T.firstAddition hμν hν hp
  have he := Fintype.card_congr (Equiv.sigmaFiberEquiv f)
  rw [Fintype.card_sigma] at he
  rw [← he]
  apply Finset.sum_congr rfl
  intro r _
  exact Fintype.card_congr (firstAdditionFiberEquiv hμν hν hp r)

end StandardSkewTableau

/-- First-box recurrence for the actual count in LaTeX `eq:Plucker-translation`. -/
theorem standardSkewTableauCount_rec {n : ℕ} {ν μ : YoungDiagram}
    (hμν : μ ≤ ν) (hν : PartitionFits n ν) (hp : 0 < (ν.cells \ μ.cells).card) :
    standardSkewTableauCount ν μ =
      ∑ r : SkewAddition n ν μ, standardSkewTableauCount ν r.enlarged := by
  rw [standardSkewTableauCount, if_pos hμν,
    StandardSkewTableau.card_eq_sum_first_additions hμν hν hp]
  apply Finset.sum_congr rfl
  intro r _
  have hr : r.enlarged ≤ ν := r.inside
  simp [standardSkewTableauCount, hr]

end
end ModifiedCartan


