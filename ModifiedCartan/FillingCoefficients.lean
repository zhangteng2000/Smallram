import ModifiedCartan.FillingTabloids

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

theorem youngFillingPolytabloid_eq_sum (μ : YoungDiagram) (T : YoungFilling μ) :
    youngFillingPolytabloid μ T = ∑ c : youngColumnSubgroup μ,
      MonoidAlgebra.single (youngTabloid μ (youngFillingPermutation μ T * c.val))
        (youngPermutationSign μ c.val) := by
  simp only [youngFillingPolytabloid, youngPolytabloid, map_sum, youngTabloidRepresentation_single]

theorem youngFilling_column_tabloid_injective (μ : YoungDiagram) (T : YoungFilling μ) :
    Function.Injective (fun c : youngColumnSubgroup μ =>
      youngTabloid μ (youngFillingPermutation μ T * c.val)) := by
  intro c d he
  apply young_column_tabloid_injective μ
  apply (young_tabloid_eq_iff μ c.val d.val).mpr
  have h := (young_tabloid_eq_iff μ (youngFillingPermutation μ T * c.val)
    (youngFillingPermutation μ T * d.val)).mp he
  simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel_left] using h

theorem youngFillingPolytabloid_column_coefficient (μ : YoungDiagram) (T : YoungFilling μ)
    (c : youngColumnSubgroup μ) :
    (youngFillingPolytabloid μ T).coeff
      (youngTabloid μ (youngFillingPermutation μ T * c.val)) = youngPermutationSign μ c.val := by
  simp only [youngFillingPolytabloid_eq_sum, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    MonoidAlgebra.coeff_single]
  rw [Finset.sum_eq_single c]
  · simp
  · intro b _ hbc
    exact Finsupp.single_eq_of_ne' (fun h => hbc (youngFilling_column_tabloid_injective μ T h))
  · simp

theorem youngFillingPolytabloid_leading_coefficient (μ : YoungDiagram) (T : YoungFilling μ) :
    (youngFillingPolytabloid μ T).coeff (youngFillingTabloid μ T) = 1 := by
  simpa only [youngFillingTabloid, Subgroup.coe_one, mul_one, youngPermutationSign_one] using
    youngFillingPolytabloid_column_coefficient μ T (1 : youngColumnSubgroup μ)

theorem youngFillingPolytabloid_coefficient_support (μ : YoungDiagram) (T : YoungFilling μ)
    (t : YoungTabloid μ) (ht : (youngFillingPolytabloid μ T).coeff t ≠ 0) :
    ∃ c : youngColumnSubgroup μ, t = youngTabloid μ (youngFillingPermutation μ T * c.val) := by
  by_contra h
  push Not at h
  apply ht
  simp only [youngFillingPolytabloid_eq_sum, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    MonoidAlgebra.coeff_single]
  apply Finset.sum_eq_zero
  intro c _
  exact Finsupp.single_eq_of_ne' (h c).symm

end
end ModifiedCartan


