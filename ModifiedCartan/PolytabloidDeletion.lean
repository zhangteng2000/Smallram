import ModifiedCartan.TabloidDeletionLinear
import ModifiedCartan.RemovalSigns

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

theorem youngPolytabloid_coefficient_support (μ : YoungDiagram) (t : YoungTabloid μ)
    (ht : (youngPolytabloid μ).coeff t ≠ 0) :
    ∃ c : youngColumnSubgroup μ, t = youngTabloid μ c.val := by
  by_contra h
  push Not at h
  apply ht
  simp only [youngPolytabloid, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    MonoidAlgebra.coeff_single]
  apply Finset.sum_eq_zero
  intro c _
  exact Finsupp.single_eq_of_ne' (h c).symm

theorem youngTabloidInsert_column_preimage (μ : YoungDiagram) (b : YoungCorner μ)
    (t : YoungTabloid (removePartitionBox μ b)) (c : youngColumnSubgroup μ)
    (hc : youngTabloidInsert μ b t = youngTabloid μ c.val) :
    ∃ p : youngColumnSubgroup (removePartitionBox μ b),
      t = youngTabloid (removePartitionBox μ b) p.val := by
  have hrow : youngTabloidRows μ (youngTabloid μ c.val) b.val = b.val.val.1 := by
    rw [← hc, youngTabloidInsert_row]
  have hfix := youngColumn_fixes_of_tabloid_row μ b.val c hrow
  let cH : youngLetterStabilizer μ b.val :=
    ⟨c.val, (mem_youngLetterStabilizer_iff μ b.val c.val).mpr hfix⟩
  let p := (youngRemovalPermutationEquiv μ b).symm cH
  have he : youngRemovalPermutationEquiv μ b p = cH :=
    (youngRemovalPermutationEquiv μ b).apply_symm_apply cH
  have hp : p ∈ youngColumnSubgroup (removePartitionBox μ b) := by
    apply (youngRemovalPermutation_column_iff μ b p).mp
    rw [he]
    exact c.property
  refine ⟨⟨p, hp⟩, ?_⟩
  apply youngTabloidInsert_injective μ b
  rw [youngTabloidInsert_mk, he]
  exact hc

/-- Corner deletion takes the actual identity polytabloid to the actual
identity polytabloid of the smaller diagram, with coefficient exactly one. -/
theorem youngTabloidDeleteLinear_polytabloid (μ : YoungDiagram) (b : YoungCorner μ) :
    youngTabloidDeleteLinear μ b (youngPolytabloid μ) =
      youngPolytabloid (removePartitionBox μ b) := by
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro t
  by_cases h : ∃ p : youngColumnSubgroup (removePartitionBox μ b),
      t = youngTabloid (removePartitionBox μ b) p.val
  · obtain ⟨p, rfl⟩ := h
    rw [youngTabloidDeleteLinear_coeff, youngTabloidInsert_mk,
      youngPolytabloid_column_coefficient]
    have hp : (youngRemovalPermutationEquiv μ b p.val).val ∈ youngColumnSubgroup μ :=
      (youngRemovalPermutation_column_iff μ b p.val).mpr p.property
    rw [youngPolytabloid_column_coefficient μ
      ⟨(youngRemovalPermutationEquiv μ b p.val).val, hp⟩, youngRemovalPermutation_sign]
  · have hsmall : (youngPolytabloid (removePartitionBox μ b)).coeff t = 0 := by
      by_contra hn
      exact h (youngPolytabloid_coefficient_support _ t hn)
    rw [hsmall, youngTabloidDeleteLinear_coeff]
    by_contra hn
    obtain ⟨c, hc⟩ := youngPolytabloid_coefficient_support μ (youngTabloidInsert μ b t) hn
    exact h (youngTabloidInsert_column_preimage μ b t c hc)

end
end ModifiedCartan


