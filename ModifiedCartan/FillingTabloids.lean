import ModifiedCartan.FillingPolytabloids
import Mathlib.Order.Hom.Set

open scoped Classical

namespace ModifiedCartan
noncomputable section

def youngFillingTabloid (μ : YoungDiagram) (T : YoungFilling μ) : YoungTabloid μ :=
  youngTabloid μ (youngFillingPermutation μ T)

theorem youngFillingTabloid_row_label (μ : YoungDiagram) (T : YoungFilling μ)
    (x : Fin (partitionSize μ)) :
    youngTabloidRows μ (youngFillingTabloid μ T) ((youngBoxNumbering μ).symm x) =
      (T.symm x).val.1 := by
  change (T.symm (youngBoxNumbering μ ((youngBoxNumbering μ).symm x))).val.1 = _
  rw [Equiv.apply_symm_apply]

def youngRowFilling (μ : YoungDiagram) (T : YoungFilling μ) (r : ℕ) :
    Fin (μ.rowLen r) → Fin (partitionSize μ) :=
  fun i => T ⟨(r, i.val), YoungDiagram.mem_iff_lt_rowLen.mpr i.isLt⟩

theorem youngRowFilling_strict (μ : YoungDiagram) (T : YoungFilling μ)
    (hT : YoungRowStandard T) (r : ℕ) : StrictMono (youngRowFilling μ T r) := by
  intro a b hab
  exact hT _ _ rfl hab

theorem youngRowFilling_range (μ : YoungDiagram) (T : YoungFilling μ) (r : ℕ) :
    Set.range (youngRowFilling μ T r) = {x | (T.symm x).val.1 = r} := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    change (T.symm (T ⟨(r, i.val), _⟩)).val.1 = r
    rw [T.symm_apply_apply]
  · intro hx
    have hx' : (T.symm x).val.1 = r := hx
    have hc : (T.symm x).val.2 < μ.rowLen r := by
      have hb := YoungDiagram.mem_iff_lt_rowLen.mp (T.symm x).property
      rwa [hx'] at hb
    refine ⟨⟨(T.symm x).val.2, hc⟩, ?_⟩
    have hb : (⟨(r, (T.symm x).val.2), YoungDiagram.mem_iff_lt_rowLen.mpr hc⟩ :
        YoungBoxes μ) = T.symm x := Subtype.ext (Prod.ext hx'.symm rfl)
    change T ⟨(r, (T.symm x).val.2), _⟩ = x
    rw [hb, T.apply_symm_apply]

/-- A tabloid has at most one filling whose rows are increasing. -/
theorem youngFillingTabloid_injective_row_standard (μ : YoungDiagram)
    (T U : YoungFilling μ) (hT : YoungRowStandard T) (hU : YoungRowStandard U)
    (he : youngFillingTabloid μ T = youngFillingTabloid μ U) : T = U := by
  have hrows : ∀ x : Fin (partitionSize μ), (T.symm x).val.1 = (U.symm x).val.1 := by
    intro x
    rw [← youngFillingTabloid_row_label μ T x, ← youngFillingTabloid_row_label μ U x, he]
  have hr : ∀ r, youngRowFilling μ T r = youngRowFilling μ U r := by
    intro r
    apply ((youngRowFilling_strict μ T hT r).range_inj
      (youngRowFilling_strict μ U hU r)).mp
    rw [youngRowFilling_range, youngRowFilling_range]
    ext x
    change (T.symm x).val.1 = r ↔ (U.symm x).val.1 = r
    rw [hrows x]
  apply Equiv.ext
  intro b
  exact congrFun (hr b.val.1) ⟨b.val.2, YoungDiagram.mem_iff_lt_rowLen.mp b.property⟩

theorem youngStandardTableau_tabloid_injective (μ : YoungDiagram) :
    Function.Injective (fun T : StandardYoungTableau μ => youngFillingTabloid μ T.val) := by
  intro T U he
  apply Subtype.ext
  exact youngFillingTabloid_injective_row_standard μ T.val U.val
    ((young_filling_standard_iff T.val).mp T.property).1
    ((young_filling_standard_iff U.val).mp U.property).1 he

end
end ModifiedCartan


