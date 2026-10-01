import ModifiedCartan.CharacterProjectorOrthogonal
import ModifiedCartan.RegularCharacterTrace
import ModifiedCartan.FiniteOrthogonalProjectors
import ModifiedCartan.SpechtDimensionSquareSum
import ModifiedCartan.SpechtDistinctCharacters

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

abbrev sizedSpechtRepresentation (μ : SizedYoungDiagram (Fintype.card A)) :
    Representation ℂ (Equiv.Perm A) (YoungSpechtModule μ.val) :=
  spechtRepresentationOn μ.val μ.property.symm

theorem sizedSpechtProjector_mul {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (τ : Representation ℂ (Equiv.Perm A) W)
    (μ ν : SizedYoungDiagram (Fintype.card A)) :
    characterProjector (sizedSpechtRepresentation μ) τ *
      characterProjector (sizedSpechtRepresentation ν) τ =
      if μ = ν then characterProjector (sizedSpechtRepresentation μ) τ else 0 := by
  let _ := spechtRepresentationOn_irreducible μ.val μ.property.symm (A := A)
  let _ := spechtRepresentationOn_irreducible ν.val ν.property.symm (A := A)
  by_cases h : μ = ν
  · subst ν
    rw [if_pos rfl]
    exact characterProjector_idempotent _ τ
  · rw [if_neg h]
    apply characterProjector_mul_eq_zero
    rintro ⟨e⟩
    exact h (Subtype.ext (spechtRepresentationOn_equiv_shape μ.val ν.val _ _ e))

/-- The actual Specht projectors exhaust the regular representation.
No classification of the irreducible representations is assumed. -/
theorem sum_spechtProjector_regular :
    (∑ μ : SizedYoungDiagram (Fintype.card A),
      characterProjector (sizedSpechtRepresentation μ) (Representation.leftRegular ℂ (Equiv.Perm A))) = 1 := by
  let _ := (MonoidAlgebra.basis (Equiv.Perm A) ℂ).finiteDimensional_of_finite
  apply sum_orthogonal_projectors_eq_one
  · intro μ ν
    by_cases he : μ = ν <;>
      simpa only [he, ite_true, ite_false] using
        sizedSpechtProjector_mul (Representation.leftRegular ℂ (Equiv.Perm A)) μ ν
  · simp only [characterProjector_trace_regular]
    rw [Module.finrank_eq_card_basis (MonoidAlgebra.basis (Equiv.Perm A) ℂ), Fintype.card_perm]
    exact_mod_cast sum_specht_finrank_sq (Fintype.card A)

end
end ModifiedCartan


