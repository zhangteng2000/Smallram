import ModifiedCartan.YoungFillings
import ModifiedCartan.YoungColumns
import Mathlib.Data.Finset.Sort

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

def youngColumnLabels (μ : YoungDiagram) (T : YoungFilling μ) (j : Fin (μ.rowLen 0)) :
    Finset (Fin (partitionSize μ)) :=
  Finset.univ.image (fun b : YoungColumnBoxes μ j => T b.val)

theorem youngColumnLabel_injective (μ : YoungDiagram) (T : YoungFilling μ)
    (j : Fin (μ.rowLen 0)) : Function.Injective (fun b : YoungColumnBoxes μ j => T b.val) := by
  intro a b hab
  exact Subtype.ext (T.injective hab)

theorem youngColumnLabels_card (μ : YoungDiagram) (T : YoungFilling μ) (j : Fin (μ.rowLen 0)) :
    (youngColumnLabels μ T j).card = μ.colLen j.val := by
  rw [youngColumnLabels, Finset.card_image_of_injective _ (youngColumnLabel_injective μ T j),
    Finset.card_univ, youngColumnBoxes_card]

def youngColumnLabelEquiv (μ : YoungDiagram) (T : YoungFilling μ) (j : Fin (μ.rowLen 0)) :
    YoungColumnBoxes μ j ≃ (youngColumnLabels μ T j) :=
  Equiv.ofBijective (fun b => ⟨T b.val, Finset.mem_image.mpr ⟨b, Finset.mem_univ b, rfl⟩⟩) (by
    constructor
    · intro a b hab
      exact youngColumnLabel_injective μ T j (congrArg Subtype.val hab)
    · rintro ⟨k, hk⟩
      obtain ⟨b, hb, hbk⟩ := Finset.mem_image.mp hk
      exact ⟨b, Subtype.ext hbk⟩)

/-- Enumerate the boxes in a column in increasing order of their labels. -/
def youngSortedColumnEquiv (μ : YoungDiagram) (T : YoungFilling μ) (j : Fin (μ.rowLen 0)) :
    Fin (μ.colLen j.val) ≃ YoungColumnBoxes μ j :=
  ((youngColumnLabels μ T j).orderIsoOfFin (youngColumnLabels_card μ T j)).toEquiv.trans
    (youngColumnLabelEquiv μ T j).symm

theorem youngSortedColumnEquiv_label (μ : YoungDiagram) (T : YoungFilling μ)
    (j : Fin (μ.rowLen 0)) (r : Fin (μ.colLen j.val)) :
    T (youngSortedColumnEquiv μ T j r).val =
      (youngColumnLabels μ T j).orderEmbOfFin (youngColumnLabels_card μ T j) r := by
  exact congrArg Subtype.val ((youngColumnLabelEquiv μ T j).apply_symm_apply
    ((youngColumnLabels μ T j).orderIsoOfFin (youngColumnLabels_card μ T j) r))

theorem youngSortedColumnEquiv_strict (μ : YoungDiagram) (T : YoungFilling μ)
    (j : Fin (μ.rowLen 0)) :
    StrictMono (fun r => T (youngSortedColumnEquiv μ T j r).val) := by
  intro a b hab
  change T (youngSortedColumnEquiv μ T j a).val < T (youngSortedColumnEquiv μ T j b).val
  rw [youngSortedColumnEquiv_label μ T j a, youngSortedColumnEquiv_label μ T j b]
  exact ((youngColumnLabels μ T j).orderEmbOfFin (youngColumnLabels_card μ T j)).strictMono hab

end
end ModifiedCartan


