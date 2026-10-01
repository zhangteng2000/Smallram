import ModifiedCartan.YoungTabloidInnerProduct
import ModifiedCartan.YoungAlternatingOperator

open scoped BigOperators Classical MonoidAlgebra ComplexConjugate

namespace ModifiedCartan
noncomputable section

attribute [local instance] youngPermutationModuleNormed youngPermutationModuleInner

theorem unitary_inner_action_left {G W : Type*} [Group G]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (ρ : Representation ℂ G W) (hρ : IsUnitaryRepresentation ρ) (g : G) (v w : W) :
    inner ℂ (ρ g v) w = inner ℂ v (ρ g⁻¹ w) := by
  calc
    _ = inner ℂ (ρ g v) (ρ g (ρ g⁻¹ w)) := by rw [Representation.self_inv_apply]
    _ = _ := hρ g v (ρ g⁻¹ w)

theorem youngPermutationSign_conj (μ : YoungDiagram) (g : Equiv.Perm (YoungBoxes μ)) :
    conj (youngPermutationSign μ g) = youngPermutationSign μ g := by
  change conj ((Equiv.Perm.sign g : ℤ) : ℂ) = ((Equiv.Perm.sign g : ℤ) : ℂ)
  simp

/-- Column antisymmetrization is Hermitian for the tabloid inner product. -/
theorem youngColumnAlternatingOperator_inner (μ : YoungDiagram) (v w : YoungPermutationModule μ) :
    inner ℂ (youngColumnAlternatingOperator μ v) w =
      inner ℂ v (youngColumnAlternatingOperator μ w) := by
  simp only [youngColumnAlternatingOperator, LinearMap.sum_apply, sum_inner, inner_sum,
    LinearMap.smul_apply, inner_smul_left, inner_smul_right, youngPermutationSign_conj,
    unitary_inner_action_left (youngTabloidRepresentation μ) (youngTabloidRepresentation_unitary μ)]
  apply Fintype.sum_equiv (Equiv.inv (youngColumnSubgroup μ))
  intro c
  change youngPermutationSign μ c.val *
      inner ℂ v (youngTabloidRepresentation μ c.val⁻¹ w) =
    youngPermutationSign μ c.val⁻¹ * inner ℂ v (youngTabloidRepresentation μ c.val⁻¹ w)
  rw [youngPermutationSign_inv]

theorem youngColumnAlternatingOperator_mem_subrepresentation (μ : YoungDiagram)
    (U : Subrepresentation (youngTabloidRepresentation μ)) {v : YoungPermutationModule μ}
    (hv : v ∈ U) : youngColumnAlternatingOperator μ v ∈ U := by
  simp only [youngColumnAlternatingOperator, LinearMap.sum_apply, LinearMap.smul_apply]
  apply U.toSubmodule.sum_mem
  intro c _
  exact U.toSubmodule.smul_mem _ (U.apply_mem_toSubmodule c.val hv)

end
end ModifiedCartan


