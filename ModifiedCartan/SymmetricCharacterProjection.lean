import ModifiedCartan.CharacterProjectionBound
import ModifiedCartan.IsotypicCopies
import Mathlib.GroupTheory.Perm.Cycle.Type

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

variable {ι V W : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

theorem permutation_character_inv (ρ : Representation ℂ (Equiv.Perm ι) V)
    (g : Equiv.Perm ι) : ρ.character g⁻¹ = ρ.character g := by
  have hc : IsConj g g⁻¹ := Equiv.Perm.isConj_iff_cycleType_eq.mpr
    (Equiv.Perm.cycleType_inv g).symm
  obtain ⟨h, hh⟩ := isConj_iff.mp hc
  rw [← hh, Representation.char_conj]

/-- The character sum `C^tau` in LaTeX `lem:character-projection`. -/
def permutationCharacterOperator (ρ : Representation ℂ (Equiv.Perm ι) V)
    (π : Representation ℂ (Equiv.Perm ι) W) : Module.End ℂ W :=
  ∑ g : Equiv.Perm ι, ρ.character g • π g

theorem permutationCharacterOperator_eq_weighted (ρ : Representation ℂ (Equiv.Perm ι) V)
    (π : Representation ℂ (Equiv.Perm ι) W) :
    permutationCharacterOperator ρ π = characterWeightedOperator ρ π := by
  simp only [permutationCharacterOperator, characterWeightedOperator, permutation_character_inv]

theorem natCard_permutation_eq_factorial : Nat.card (Equiv.Perm ι) = (Fintype.card ι).factorial := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm]

namespace Paper

/-- LaTeX `lem:character-projection`, in the stronger form for every actual irreducible
representation of the symmetric group. The factor `f^tau` is its character at the identity,
exactly as in the lemma. The target is the sum of all invariant isomorphic copies. -/
theorem lem_character_projection (ρ : Representation ℂ (Equiv.Perm ι) V)
    (π : Representation ℂ (Equiv.Perm ι) W) [Representation.IsIrreducible ρ]
    (hπ : IsUnitaryRepresentation π) :
    (ρ.character 1 / ((Fintype.card ι).factorial : ℂ)) • permutationCharacterOperator ρ π =
      ((irreducibleCopiesSubmodule ρ π).starProjection : W →ₗ[ℂ] W) := by
  rw [Representation.char_one, permutationCharacterOperator_eq_weighted]
  simpa only [characterProjector, natCard_permutation_eq_factorial,
    representationIsotypic_eq_sum_copies] using characterProjector_eq_starProjection ρ π hπ

end Paper

/-- Finite-group part of LaTeX `eq:projectionbound`, including the empty index set. -/
theorem permutation_character_expectation_bound (ρ : Representation ℂ (Equiv.Perm ι) V)
    (π : Representation ℂ (Equiv.Perm ι) W) [Representation.IsIrreducible ρ]
    (hπ : IsUnitaryRepresentation π) (v : W) (hv : ‖v‖ = 1) :
    ‖inner ℂ v (permutationCharacterOperator ρ π v)‖ ≤ ((Fintype.card ι).factorial : ℝ) := by
  rw [permutationCharacterOperator_eq_weighted]
  simpa only [natCard_permutation_eq_factorial] using
    norm_characterWeightedOperator_expectation_le_card ρ π hπ v hv

end
end ModifiedCartan


