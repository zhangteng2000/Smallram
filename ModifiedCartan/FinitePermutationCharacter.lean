import Mathlib.RepresentationTheory.Character
import Mathlib.Data.Complex.Basic

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

theorem finitePermutationRepresentation_character {G X : Type*} [Monoid G]
    [MulAction G X] [Fintype X] (g : G) :
    (Representation.ofMulAction ℂ G X).character g =
      ∑ x : X, if g • x = x then (1 : ℂ) else 0 := by
  rw [Representation.character,
    LinearMap.trace_eq_matrix_trace ℂ (MonoidAlgebra.basis X ℂ)]
  simp [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, MonoidAlgebra.basis,
    Representation.ofMulAction_single, MonoidAlgebra.coeff_single, Finsupp.single_apply]

end
end ModifiedCartan


