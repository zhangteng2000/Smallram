import ModifiedCartan.YoungColumnAlternation

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

/-- Column antisymmetrization on the actual tabloid permutation module. -/
def youngColumnAlternatingOperator (μ : YoungDiagram) : Module.End ℂ (YoungPermutationModule μ) :=
  ∑ c : youngColumnSubgroup μ, youngPermutationSign μ c.val • youngTabloidRepresentation μ c.val

theorem youngColumnAlternatingOperator_mul_column (μ : YoungDiagram) (d : youngColumnSubgroup μ) :
    youngColumnAlternatingOperator μ * youngTabloidRepresentation μ d.val =
      youngPermutationSign μ d.val • youngColumnAlternatingOperator μ := by
  simp only [youngColumnAlternatingOperator, Finset.sum_mul, smul_mul_assoc,
    ← map_mul (youngTabloidRepresentation μ), Finset.smul_sum, smul_smul]
  apply Fintype.sum_equiv (Equiv.mulRight d)
  intro c
  change youngPermutationSign μ c.val • youngTabloidRepresentation μ (c.val * d.val) =
    (youngPermutationSign μ d.val * youngPermutationSign μ (c.val * d.val)) •
      youngTabloidRepresentation μ (c.val * d.val)
  rw [youngPermutationSign_mul]
  have hs : youngPermutationSign μ d.val *
      (youngPermutationSign μ c.val * youngPermutationSign μ d.val) =
        youngPermutationSign μ c.val := by
    calc
      _ = youngPermutationSign μ c.val *
          (youngPermutationSign μ d.val * youngPermutationSign μ d.val) := by ring
      _ = _ := by rw [youngPermutationSign_mul_self, mul_one]
  rw [hs]

theorem youngColumnAlternatingOperator_column_apply (μ : YoungDiagram)
    (d : youngColumnSubgroup μ) (v : YoungPermutationModule μ) :
    youngColumnAlternatingOperator μ (youngTabloidRepresentation μ d.val v) =
      youngPermutationSign μ d.val • youngColumnAlternatingOperator μ v := by
  exact congrArg (fun A : Module.End ℂ (YoungPermutationModule μ) => A v)
    (youngColumnAlternatingOperator_mul_column μ d)

theorem youngColumnAlternatingOperator_identity (μ : YoungDiagram) :
    youngColumnAlternatingOperator μ (MonoidAlgebra.single (youngTabloid μ 1) 1) =
      youngPolytabloid μ := by
  simp only [youngColumnAlternatingOperator, LinearMap.sum_apply, LinearMap.smul_apply,
    youngTabloidRepresentation_single, mul_one, MonoidAlgebra.smul_single, smul_eq_mul,
    youngPolytabloid]

end
end ModifiedCartan


