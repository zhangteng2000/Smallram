import ModifiedCartan.YoungPolytabloid

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

theorem youngPermutationSign_inv (μ : YoungDiagram) (g : Equiv.Perm (YoungBoxes μ)) :
    youngPermutationSign μ g⁻¹ = youngPermutationSign μ g := by
  change ((Equiv.Perm.sign g⁻¹ : ℤ) : ℂ) = ((Equiv.Perm.sign g : ℤ) : ℂ)
  rw [Equiv.Perm.sign_inv]

theorem youngPermutationSign_mul_self (μ : YoungDiagram) (g : Equiv.Perm (YoungBoxes μ)) :
    youngPermutationSign μ g * youngPermutationSign μ g = 1 := by
  calc
    _ = youngPermutationSign μ g * youngPermutationSign μ g⁻¹ := by
      rw [youngPermutationSign_inv]
    _ = youngPermutationSign μ (g * g⁻¹) := (youngPermutationSign_mul μ g g⁻¹).symm
    _ = 1 := by simp

theorem youngTabloidRepresentation_single (μ : YoungDiagram)
    (g h : Equiv.Perm (YoungBoxes μ)) (a : ℂ) :
    youngTabloidRepresentation μ g (MonoidAlgebra.single (youngTabloid μ h) a) =
      MonoidAlgebra.single (youngTabloid μ (g * h)) a := by
  simpa only [youngTabloidRepresentation, youngTabloid, MulAction.Quotient.smul_mk,
    smul_eq_mul] using
    Representation.ofMulAction_single (k := ℂ) g (youngTabloid μ h) a

/-- Alternation under the column group, as required in the Specht construction. -/
theorem youngPolytabloid_column_action (μ : YoungDiagram) (c : youngColumnSubgroup μ) :
    youngTabloidRepresentation μ c.val (youngPolytabloid μ) =
      youngPermutationSign μ c.val • youngPolytabloid μ := by
  simp only [youngPolytabloid, map_sum, Finset.smul_sum, youngTabloidRepresentation_single,
    MonoidAlgebra.smul_single, smul_eq_mul]
  apply Fintype.sum_equiv (Equiv.mulLeft c)
  intro d
  change MonoidAlgebra.single (youngTabloid μ (c.val * d.val)) (youngPermutationSign μ d.val) =
    MonoidAlgebra.single (youngTabloid μ (c.val * d.val))
      (youngPermutationSign μ c.val * youngPermutationSign μ (c.val * d.val))
  rw [youngPermutationSign_mul, ← mul_assoc, youngPermutationSign_mul_self, one_mul]

end
end ModifiedCartan


