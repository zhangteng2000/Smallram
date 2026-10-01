import ModifiedCartan.LastRowSupport
import ModifiedCartan.TabloidRowCutoff

open scoped Classical

namespace ModifiedCartan
noncomputable section

def youngRestrictedSpechtSubrepresentation (μ : YoungDiagram) (a : YoungBoxes μ) :
    Subrepresentation (youngLetterRepresentation μ a) where
  toSubmodule := (youngSpechtSubrepresentation μ).toSubmodule
  apply_mem_toSubmodule := by
    intro g v hv
    exact (youngSpechtSubrepresentation μ).apply_mem_toSubmodule g.val hv

/-- The invariant filtration of the restricted Specht space by the row of a
fixed letter. Its quotient identification is proved separately. -/
def youngSpechtRowFiltration (μ : YoungDiagram) (a : YoungBoxes μ) (r : ℕ) :
    Subrepresentation (youngLetterRepresentation μ a) :=
  youngRestrictedSpechtSubrepresentation μ a ⊓ youngTabloidRowCutoff μ a r

theorem youngSpechtRowFiltration_mono (μ : YoungDiagram) (a : YoungBoxes μ) :
    Monotone (youngSpechtRowFiltration μ a) := by
  intro r s hrs v hv
  exact ⟨hv.1, youngTabloidRowCutoffSubmodule_mono μ a hrs hv.2⟩

theorem youngSpechtRowFiltration_zero (μ : YoungDiagram) (a : YoungBoxes μ) :
    youngSpechtRowFiltration μ a 0 = ⊥ := by
  apply Subrepresentation.toSubmodule_injective
  change (youngSpechtSubrepresentation μ).toSubmodule ⊓
    youngTabloidRowCutoffSubmodule μ a 0 = ⊥
  rw [youngTabloidRowCutoffSubmodule_zero, inf_bot_eq]

theorem youngSpechtRowFiltration_height (μ : YoungDiagram) (a : YoungBoxes μ) :
    youngSpechtRowFiltration μ a (μ.colLen 0) = youngRestrictedSpechtSubrepresentation μ a := by
  apply Subrepresentation.toSubmodule_injective
  change (youngSpechtSubrepresentation μ).toSubmodule ⊓
    youngTabloidRowCutoffSubmodule μ a (μ.colLen 0) = _
  rw [youngTabloidRowCutoffSubmodule_height, inf_top_eq]
  rfl

theorem youngStandardPolytabloid_mem_rowFiltration (μ : YoungDiagram)
    (hpos : 0 < partitionSize μ) (T : StandardYoungTableau μ) (r : ℕ)
    (hrow : (youngTableauLastBox μ hpos T).val.val.1 < r) :
    youngFillingPolytabloid μ T.val ∈ youngSpechtRowFiltration μ
      ((youngBoxNumbering μ).symm (youngMaxLabel μ hpos)) r := by
  refine ⟨youngFillingPolytabloid_mem μ T.val, ?_⟩
  intro t ht
  by_contra hn
  have hbound := youngStandardPolytabloid_support_last_row μ hpos T t hn
  omega

def youngTableauRowSpan (μ : YoungDiagram) (hpos : 0 < partitionSize μ) (r : ℕ) :
    Submodule ℂ (YoungPermutationModule μ) :=
  Submodule.span ℂ (Set.range (fun T : {T : StandardYoungTableau μ //
    (youngTableauLastBox μ hpos T).val.val.1 < r} => youngFillingPolytabloid μ T.val.val))

theorem youngTableauRowSpan_le_filtration (μ : YoungDiagram) (hpos : 0 < partitionSize μ) (r : ℕ) :
    youngTableauRowSpan μ hpos r ≤ (youngSpechtRowFiltration μ
      ((youngBoxNumbering μ).symm (youngMaxLabel μ hpos)) r).toSubmodule := by
  apply Submodule.span_le.mpr
  rintro v ⟨T, rfl⟩
  exact youngStandardPolytabloid_mem_rowFiltration μ hpos T.val r T.property

end
end ModifiedCartan


