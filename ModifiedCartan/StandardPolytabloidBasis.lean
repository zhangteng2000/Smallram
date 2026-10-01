import ModifiedCartan.YoungTabloidWeight
import ModifiedCartan.LeadingCoefficientIndependence
import ModifiedCartan.StandardPolytabloidSpanning

open scoped Classical

namespace ModifiedCartan
noncomputable section

theorem youngStandardPolytabloids_linearIndependent (μ : YoungDiagram) :
    LinearIndependent ℂ (fun T : StandardYoungTableau μ => youngFillingPolytabloid μ T.val) := by
  apply linearIndependent_of_strict_leading_weight
    (fun T : StandardYoungTableau μ => youngFillingPolytabloid μ T.val)
    (fun T => youngFillingTabloid μ T.val) (youngTabloidWeight μ)
    (youngStandardTableau_tabloid_injective μ)
  · intro T
    exact youngFillingPolytabloid_leading_coefficient μ T.val
  · intro T t ht hc
    exact youngFillingPolytabloid_nonleading_weight_lt μ T.val
      ((young_filling_standard_iff T.val).mp T.property).2 t ht hc

/-- The actual standard-polytabloid basis of the constructed Specht module. -/
def youngStandardPolytabloidBasis (μ : YoungDiagram) :
    Module.Basis (StandardYoungTableau μ) ℂ (YoungSpechtModule μ) :=
  (Module.Basis.span (youngStandardPolytabloids_linearIndependent μ)).map
    (LinearEquiv.ofEq _ _ (youngStandardPolytabloids_span μ))

theorem youngStandardPolytabloidBasis_apply (μ : YoungDiagram) (T : StandardYoungTableau μ) :
    (youngStandardPolytabloidBasis μ T).val = youngFillingPolytabloid μ T.val := by
  simp [youngStandardPolytabloidBasis, Module.Basis.map_apply, Module.Basis.span_apply]

/-- The tableau dimension used in LaTeX `eq:KP-operators` and
`lem:character-projection`, proved from an actual basis. -/
theorem finrank_specht_eq_standardTableauCount (μ : YoungDiagram) :
    Module.finrank ℂ (YoungSpechtModule μ) = standardSkewTableauCount μ ⊥ := by
  rw [Module.finrank_eq_card_basis (youngStandardPolytabloidBasis μ), standardYoungTableau_card]

theorem spechtCharacter_one_eq_standardTableauCount (μ : YoungDiagram) :
    spechtCharacter μ 1 = (standardSkewTableauCount μ ⊥ : ℂ) := by
  rw [spechtCharacter_one, finrank_specht_eq_standardTableauCount]

end
end ModifiedCartan


