import ModifiedCartan.GarnirBelt
import ModifiedCartan.SubsetAlternatingCancellation

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

theorem garnirBelt_column_row_bound (μ : YoungDiagram) (r j : ℕ)
    (c : youngColumnSubgroup μ) (a : YoungBoxes μ) (ha : a ∈ garnirBelt μ r j) :
    youngTabloidRows μ (youngTabloid μ c.val) a < μ.colLen j := by
  rw [youngTabloidRows_mk]
  have hc : (c.val⁻¹ a).val.2 = a.val.2 :=
    (youngColumnSubgroup μ).inv_mem c.property a
  have hb := YoungDiagram.mem_iff_lt_colLen.mp (c.val⁻¹ a).property
  rw [hc] at hb
  rcases Finset.mem_union.mp ha with hl | hr
  · have hj := ((mem_garnirLeft μ r j a).mp hl).1
    rwa [hj] at hb
  · have hj := ((mem_garnirRight μ r j a).mp hr).1
    rw [hj] at hb
    exact hb.trans_le (μ.colLen_anti j (j + 1) (Nat.le_succ j))

/-- The full Garnir alternating sum annihilates the identity polytabloid. -/
theorem garnirBelt_alternation_polytabloid_zero (μ : YoungDiagram) (r j : ℕ)
    (hcell : (r, j + 1) ∈ μ) :
    youngSubgroupAlternatingOperator μ (supportedPermutationSubgroup (garnirBelt μ r j))
      (youngPolytabloid μ) = 0 := by
  have hcard : μ.colLen j < (garnirBelt μ r j).card := by
    rw [garnirBelt_card μ r j hcell]
    omega
  rw [youngPolytabloid, map_sum]
  apply Finset.sum_eq_zero
  intro c _
  have hs : MonoidAlgebra.single (youngTabloid μ c.val) (youngPermutationSign μ c.val) =
      youngPermutationSign μ c.val • MonoidAlgebra.single (youngTabloid μ c.val) 1 := by simp
  rw [hs, map_smul, youngSubsetAlternatingOperator_zero_of_row_bound μ
    (garnirBelt μ r j) (youngTabloid μ c.val) (μ.colLen j)
      (fun a ha => garnirBelt_column_row_bound μ r j c a ha) hcard, smul_zero]

end
end ModifiedCartan


