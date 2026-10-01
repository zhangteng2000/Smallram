import ModifiedCartan.ColumnSorting
import ModifiedCartan.FillingPolytabloids

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

/-- Sorting columns reduces the spanning family without changing its span. -/
theorem youngColumnStandardPolytabloids_span (μ : YoungDiagram) :
    Submodule.span ℂ (Set.range (fun T : {T : YoungFilling μ // YoungColumnStandard T} =>
      youngFillingPolytabloid μ T.val)) = (youngSpechtSubrepresentation μ).toSubmodule := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨T, rfl⟩
    exact youngFillingPolytabloid_mem μ T.val
  · rw [← youngFillingPolytabloids_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨T, rfl⟩
    let c : youngColumnSubgroup μ :=
      ⟨youngColumnSortPermutation μ T, youngColumnSortPermutation_mem μ T⟩
    let T' : YoungFilling μ := c.val.trans T
    have ht : YoungColumnStandard T' := youngColumnSort_standard μ T
    have he : youngFillingPolytabloid μ T =
        youngPermutationSign μ c.val • youngFillingPolytabloid μ T' := by
      change _ = youngPermutationSign μ c.val • youngFillingPolytabloid μ (c.val.trans T)
      rw [youngFillingPolytabloid_column, smul_smul, youngPermutationSign_mul_self, one_smul]
    rw [he]
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨⟨T', ht⟩, rfl⟩

end
end ModifiedCartan


