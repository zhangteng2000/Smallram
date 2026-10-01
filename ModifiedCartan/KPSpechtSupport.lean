import ModifiedCartan.KPTranslatedVanishing
import ModifiedCartan.KPAlphaPositive

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

attribute [local instance] youngPermutationModuleNormed youngPermutationModuleInner

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem specht_kpAlpha_eq_zero_of_not_le (μ τ : YoungDiagram)
    (hτ : Fintype.card A = partitionSize τ) (hnot : ¬μ ≤ τ) (I : Finset A) :
    (spechtRepresentationOn τ hτ).asAlgebraHom (kpAlpha μ I) = 0 := by
  apply positive_operators_eq_zero_of_sum_eq_zero
    (fun J : Finset A => (spechtRepresentationOn τ hτ).asAlgebraHom (kpAlpha μ J))
    (fun J => kpAlpha_action_isPositive _ (spechtRepresentationOn_unitary τ hτ) μ J)
    (specht_sum_kpAlpha_eq_zero_of_not_le μ τ hτ hnot) I

/-- The operator support rule needed for LaTeX `lem:KP-correspondence`: shapes
outside the Specht shape act as zero, for every center and parameter tuple. -/
theorem specht_kpBeta_eq_zero_of_not_le (μ τ : YoungDiagram)
    (hτ : Fintype.card A = partitionSize τ) (hnot : ¬μ ≤ τ) (z : A → ℂ) (a : ℂ) :
    (spechtRepresentationOn τ hτ).asAlgebraHom (kpBeta μ z a) = 0 := by
  rw [kpBeta_eq_sum_all_subsets, map_sum]
  apply Finset.sum_eq_zero
  intro I _
  rw [map_smul, specht_kpAlpha_eq_zero_of_not_le μ τ hτ hnot I, smul_zero]

end
end ModifiedCartan


