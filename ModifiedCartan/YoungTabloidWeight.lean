import ModifiedCartan.FillingCoefficients
import ModifiedCartan.ColumnRearrangement

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

def youngTabloidWeight (μ : YoungDiagram) (t : YoungTabloid μ) : ℕ :=
  ∑ b : YoungBoxes μ, (youngBoxNumbering μ b).val * youngTabloidRows μ t b

theorem youngTabloidWeight_column (μ : YoungDiagram) (T : YoungFilling μ)
    (c : youngColumnSubgroup μ) :
    youngTabloidWeight μ (youngTabloid μ (youngFillingPermutation μ T * c.val)) =
      ∑ b : YoungBoxes μ, (c.val⁻¹ b).val.1 * (T b).val := by
  unfold youngTabloidWeight
  rw [← Equiv.sum_comp (youngFillingPermutation μ T)
    (fun b => (youngBoxNumbering μ b).val *
      youngTabloidRows μ (youngTabloid μ (youngFillingPermutation μ T * c.val)) b)]
  apply Finset.sum_congr rfl
  intro b _
  rw [youngTabloidRows_mk]
  have hn : youngBoxNumbering μ (youngFillingPermutation μ T b) = T b :=
    (youngBoxNumbering μ).apply_symm_apply (T b)
  rw [hn, mul_inv_rev]
  change (T b).val * (c.val⁻¹ ((youngFillingPermutation μ T)⁻¹
    (youngFillingPermutation μ T b))).val.1 = _
  have hi : (youngFillingPermutation μ T)⁻¹ (youngFillingPermutation μ T b) = b :=
    (youngFillingPermutation μ T).symm_apply_apply b
  rw [hi, mul_comm]

theorem youngTabloidWeight_filling (μ : YoungDiagram) (T : YoungFilling μ) :
    youngTabloidWeight μ (youngFillingTabloid μ T) =
      ∑ b : YoungBoxes μ, b.val.1 * (T b).val := by
  simpa only [youngFillingTabloid, Subgroup.coe_one, mul_one, inv_one, Equiv.Perm.one_apply] using
    youngTabloidWeight_column μ T (1 : youngColumnSubgroup μ)

/-- Every nonleading tabloid in a column-standard polytabloid has strictly
smaller row-label weight. -/
theorem youngFillingPolytabloid_nonleading_weight_lt (μ : YoungDiagram) (T : YoungFilling μ)
    (hT : YoungColumnStandard T) (t : YoungTabloid μ)
    (hne : t ≠ youngFillingTabloid μ T) (ht : (youngFillingPolytabloid μ T).coeff t ≠ 0) :
    youngTabloidWeight μ t < youngTabloidWeight μ (youngFillingTabloid μ T) := by
  obtain ⟨c, rfl⟩ := youngFillingPolytabloid_coefficient_support μ T t ht
  have hc : c ≠ 1 := by
    intro hc
    apply hne
    subst c
    simp [youngFillingTabloid]
  rw [youngTabloidWeight_column, youngTabloidWeight_filling]
  exact youngColumn_total_weighted_sum_lt μ T hT c⁻¹ (inv_ne_one.mpr hc)

end
end ModifiedCartan


