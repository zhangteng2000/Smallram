import ModifiedCartan.TableauLastBox
import ModifiedCartan.FillingCoefficients

open scoped Classical

namespace ModifiedCartan
noncomputable section

theorem youngFillingTabloid_column_row_label (μ : YoungDiagram) (T : YoungFilling μ)
    (c : youngColumnSubgroup μ) (x : Fin (partitionSize μ)) :
    youngTabloidRows μ (youngTabloid μ (youngFillingPermutation μ T * c.val))
      ((youngBoxNumbering μ).symm x) = (c.val⁻¹ (T.symm x)).val.1 := by
  rw [youngTabloidRows_mk, mul_inv_rev]
  change (c.val⁻¹ (T.symm (youngBoxNumbering μ ((youngBoxNumbering μ).symm x)))).val.1 = _
  rw [Equiv.apply_symm_apply]

/-- Every tabloid in a standard polytabloid places the maximal letter no lower
than its original corner row. This is the support bound used for branching. -/
theorem youngStandardPolytabloid_support_last_row (μ : YoungDiagram)
    (hpos : 0 < partitionSize μ) (T : StandardYoungTableau μ) (t : YoungTabloid μ)
    (ht : (youngFillingPolytabloid μ T.val).coeff t ≠ 0) :
    youngTabloidRows μ t ((youngBoxNumbering μ).symm (youngMaxLabel μ hpos)) ≤
      (youngTableauLastBox μ hpos T).val.val.1 := by
  obtain ⟨c, rfl⟩ := youngFillingPolytabloid_coefficient_support μ T.val t ht
  rw [youngFillingTabloid_column_row_label]
  exact youngCorner_column_row_le μ (youngTableauLastBox μ hpos T) c⁻¹

end
end ModifiedCartan


