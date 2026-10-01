import ModifiedCartan.YoungSwapCoefficient
import ModifiedCartan.TotalTranspositionOperator
import ModifiedCartan.YoungSpechtIrreducible

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

def youngPairContent {μ : YoungDiagram} (a b : YoungBoxes μ) : ℂ :=
  (if a.val.1 = b.val.1 then 1 else 0) - (if a.val.2 = b.val.2 then 1 else 0)

theorem youngPairContent_self {μ : YoungDiagram} (a : YoungBoxes μ) : youngPairContent a a = 0 := by
  simp [youngPairContent]

theorem youngPairContent_symm {μ : YoungDiagram} (a b : YoungBoxes μ) :
    youngPairContent a b = youngPairContent b a := by simp only [youngPairContent, eq_comm]

def youngTranspositionScalar (μ : YoungDiagram) : ℂ :=
  (2 : ℂ)⁻¹ * ∑ a : YoungBoxes μ, ∑ b : YoungBoxes μ, youngPairContent a b

theorem young_totalTransposition_coefficient (μ : YoungDiagram) :
    (totalTranspositionOperator (youngTabloidRepresentation μ) (youngPolytabloid μ)).coeff
        (youngTabloid μ 1) = youngTranspositionScalar μ := by
  rw [totalTranspositionOperator_eq_sum]
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, MonoidAlgebra.coeff_smul_apply,
    MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, smul_eq_mul, youngTranspositionScalar]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases hab : a = b
  · subst b
    simp [youngPairContent_self]
  · rw [ite_eq_right hab]
    exact young_swap_action_identity_coefficient μ a b hab

/-- The scalar of the actual full transposition sum on the constructed Specht module. -/
theorem young_totalTransposition_scalar (μ : YoungDiagram) :
    totalTranspositionOperator (youngSpechtRepresentation μ) =
      youngTranspositionScalar μ • (1 : Module.End ℂ (YoungSpechtModule μ)) := by
  letI := youngSpechtRepresentation_irreducible μ
  obtain ⟨c, hc⟩ := exists_totalTransposition_scalar (youngSpechtRepresentation μ)
  let L : Representation.IntertwiningMap (youngSpechtRepresentation μ) (youngTabloidRepresentation μ) :=
    { toLinearMap := (youngSpechtSubrepresentation μ).toSubmodule.subtype
      isIntertwining' _ := rfl }
  let v : YoungSpechtModule μ := ⟨youngPolytabloid μ, youngPolytabloid_mem_specht μ⟩
  have hn := totalTranspositionOperator_natural (youngSpechtRepresentation μ)
    (youngTabloidRepresentation μ) L v
  rw [hc] at hn
  change totalTranspositionOperator (youngTabloidRepresentation μ) (youngPolytabloid μ) =
    c • youngPolytabloid μ at hn
  have hv := congrArg (fun x : YoungPermutationModule μ => x.coeff (youngTabloid μ 1)) hn
  rw [young_totalTransposition_coefficient, MonoidAlgebra.coeff_smul_apply,
    youngPolytabloid_identity_coefficient, smul_eq_mul, mul_one] at hv
  rw [hc, hv]

end
end ModifiedCartan


