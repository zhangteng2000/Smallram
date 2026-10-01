import ModifiedCartan.YoungTabloidCancellation

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

theorem young_swap_column_row_constraint (μ : YoungDiagram) (a b : YoungBoxes μ)
    (c : youngColumnSubgroup μ) (hr : Equiv.swap a b * c.val ∈ youngRowSubgroup μ) :
    a.val.1 = b.val.1 ∨ a.val.2 = b.val.2 := by
  have hc := c.property a
  have hh := hr a
  change (Equiv.swap a b (c.val a)).val.1 = a.val.1 at hh
  by_cases ha : c.val a = a
  · rw [ha, Equiv.swap_apply_left] at hh
    exact Or.inl hh.symm
  · by_cases hb : c.val a = b
    · change (c.val a).val.2 = a.val.2 at hc
      rw [hb] at hc
      exact Or.inr hc.symm
    · rw [Equiv.swap_apply_of_ne_of_ne ha hb] at hh
      exact False.elim (ha (Subtype.ext (Prod.ext hh hc)))

theorem youngPolytabloid_swap_coefficient_zero (μ : YoungDiagram) (a b : YoungBoxes μ)
    (hr : a.val.1 ≠ b.val.1) (hc : a.val.2 ≠ b.val.2) :
    (youngPolytabloid μ).coeff (youngTabloid μ (Equiv.swap a b)) = 0 := by
  simp only [youngPolytabloid, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    MonoidAlgebra.coeff_single]
  apply Finset.sum_eq_zero
  intro c _
  apply Finsupp.single_eq_of_ne'
  intro he
  have hm := (young_tabloid_eq_iff μ (Equiv.swap a b) c.val).mp he.symm
  rw [Equiv.swap_inv] at hm
  rcases young_swap_column_row_constraint μ a b c hm with h | h
  · exact hr h
  · exact hc h

theorem youngPolytabloid_swap_coefficient (μ : YoungDiagram) (a b : YoungBoxes μ)
    (hab : a ≠ b) :
    (youngPolytabloid μ).coeff (youngTabloid μ (Equiv.swap a b)) =
      (if a.val.1 = b.val.1 then (1 : ℂ) else 0) -
        (if a.val.2 = b.val.2 then (1 : ℂ) else 0) := by
  by_cases hr : a.val.1 = b.val.1
  · have hc : a.val.2 ≠ b.val.2 := fun he => hab (Subtype.ext (Prod.ext hr he))
    have ht : youngTabloid μ (Equiv.swap a b) = youngTabloid μ 1 := by
      apply (young_tabloid_eq_iff μ _ _).mpr
      rw [Equiv.swap_inv, mul_one]
      exact permutationFiberSubgroup_swap_mem (fun x : YoungBoxes μ => x.val.1) hr
    rw [ht, youngPolytabloid_identity_coefficient]
    simp [hr, hc]
  · by_cases hc : a.val.2 = b.val.2
    · let c : youngColumnSubgroup μ := ⟨Equiv.swap a b,
        permutationFiberSubgroup_swap_mem (fun x : YoungBoxes μ => x.val.2) hc⟩
      have he := youngPolytabloid_column_coefficient μ c
      change (youngPolytabloid μ).coeff (youngTabloid μ (Equiv.swap a b)) =
        youngPermutationSign μ (Equiv.swap a b) at he
      rw [he, youngPermutationSign_swap μ a b hab]
      simp [hr, hc]
    · rw [youngPolytabloid_swap_coefficient_zero μ a b hr hc]
      simp [hr, hc]

theorem young_swap_action_identity_coefficient (μ : YoungDiagram) (a b : YoungBoxes μ)
    (hab : a ≠ b) :
    (youngTabloidRepresentation μ (Equiv.swap a b) (youngPolytabloid μ)).coeff
        (youngTabloid μ 1) =
      (if a.val.1 = b.val.1 then (1 : ℂ) else 0) -
        (if a.val.2 = b.val.2 then (1 : ℂ) else 0) := by
  rw [youngTabloidRepresentation, Representation.coeff_ofMulAction, Equiv.swap_inv]
  change (youngPolytabloid μ).coeff (youngTabloid μ (Equiv.swap a b * 1)) = _
  rw [mul_one]
  exact youngPolytabloid_swap_coefficient μ a b hab

end
end ModifiedCartan


