import ModifiedCartan.YoungFillingWeight
import ModifiedCartan.ColumnStandardSpanning

open scoped Classical

namespace ModifiedCartan
noncomputable section

theorem youngColumnStandard_mem_standard_span (μ : YoungDiagram) (T : YoungFilling μ)
    (hT : YoungColumnStandard T) :
    youngFillingPolytabloid μ T ∈ Submodule.span ℂ
      (Set.range (fun S : StandardYoungTableau μ => youngFillingPolytabloid μ S.val)) := by
  let U := Submodule.span ℂ
    (Set.range (fun S : StandardYoungTableau μ => youngFillingPolytabloid μ S.val))
  have main : ∀ k : ℕ, ∀ F : YoungFilling μ, youngFillingWeight μ F = k →
      YoungColumnStandard F → youngFillingPolytabloid μ F ∈ U := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro F hk hF
      by_cases hr : YoungRowStandard F
      · exact Submodule.subset_span ⟨⟨F, (young_filling_standard_iff F).mpr ⟨hr, hF⟩⟩, rfl⟩
      · obtain ⟨r, j, hl, hright, hinv⟩ := young_not_row_standard_adjacent_inversion μ F hr
        apply garnir_filling_mem_of_mixed μ r j hright F U
        intro g hg
        let G : YoungFilling μ := g.val.trans F
        let c : youngColumnSubgroup μ :=
          ⟨youngColumnSortPermutation μ G, youngColumnSortPermutation_mem μ G⟩
        let G' : YoungFilling μ := c.val.trans G
        have hs : YoungColumnStandard G' := youngColumnSort_standard μ G
        have hlow := youngFillingWeight_garnir_lt μ F hF r j hl hright hinv g hg
        rw [hk] at hlow
        have hlow' : youngFillingWeight μ G' < k := by
          change youngFillingWeight μ (c.val.trans G) < k
          rw [youngFillingWeight_column]
          exact hlow
        have hmem : youngFillingPolytabloid μ G' ∈ U :=
          ih (youngFillingWeight μ G') hlow' G' rfl hs
        have he : youngFillingPolytabloid μ G =
            youngPermutationSign μ c.val • youngFillingPolytabloid μ G' := by
          change _ = youngPermutationSign μ c.val •
            youngFillingPolytabloid μ (c.val.trans G)
          rw [youngFillingPolytabloid_column, smul_smul, youngPermutationSign_mul_self, one_smul]
        change youngFillingPolytabloid μ G ∈ U
        rw [he]
        exact U.smul_mem _ hmem
  exact main (youngFillingWeight μ T) T rfl hT

/-- Standard polytabloids span the actual Specht module. The proof is a terminating
Garnir straightening induction on an explicit natural-number weight. -/
theorem youngStandardPolytabloids_span (μ : YoungDiagram) :
    Submodule.span ℂ (Set.range (fun T : StandardYoungTableau μ =>
      youngFillingPolytabloid μ T.val)) = (youngSpechtSubrepresentation μ).toSubmodule := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨T, rfl⟩
    exact youngFillingPolytabloid_mem μ T.val
  · rw [← youngColumnStandardPolytabloids_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨T, rfl⟩
    exact youngColumnStandard_mem_standard_span μ T.val T.property

end
end ModifiedCartan


