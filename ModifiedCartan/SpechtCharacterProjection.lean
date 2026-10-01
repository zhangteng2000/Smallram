import ModifiedCartan.StandardPolytabloidBasis
import ModifiedCartan.SymmetricCharacterProjection

open scoped Classical

namespace ModifiedCartan
noncomputable section

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

/-- LaTeX `lem:character-projection` for the constructed Specht representation,
with its dimension identified with the actual standard-tableau count. -/
theorem specht_character_projection (μ : YoungDiagram)
    (π : Representation ℂ (Equiv.Perm (Fin (partitionSize μ))) W)
    (hπ : IsUnitaryRepresentation π) :
    ((standardSkewTableauCount μ ⊥ : ℂ) / ((partitionSize μ).factorial : ℂ)) •
      permutationCharacterOperator (spechtRepresentation μ) π =
      ((irreducibleCopiesSubmodule (spechtRepresentation μ) π).starProjection : W →ₗ[ℂ] W) := by
  letI := spechtRepresentation_irreducible μ
  have h := Paper.lem_character_projection (spechtRepresentation μ) π hπ
  change (spechtCharacter μ 1 / ((Fintype.card (Fin (partitionSize μ))).factorial : ℂ)) •
    permutationCharacterOperator (spechtRepresentation μ) π = _ at h
  simpa only [spechtCharacter_one_eq_standardTableauCount, Fintype.card_fin] using h

/-- The finite-group estimate in LaTeX `eq:projectionbound`, now specialized
to the actual Specht character without any representation assumptions. -/
theorem specht_character_expectation_bound (μ : YoungDiagram)
    (π : Representation ℂ (Equiv.Perm (Fin (partitionSize μ))) W)
    (hπ : IsUnitaryRepresentation π) (v : W) (hv : ‖v‖ = 1) :
    ‖inner ℂ v (permutationCharacterOperator (spechtRepresentation μ) π v)‖ ≤
      ((partitionSize μ).factorial : ℝ) := by
  letI := spechtRepresentation_irreducible μ
  simpa only [Fintype.card_fin] using
    permutation_character_expectation_bound (spechtRepresentation μ) π hπ v hv

end
end ModifiedCartan


