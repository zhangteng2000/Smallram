import ModifiedCartan.ClassFunctionIsotypicAction
import ModifiedCartan.SpechtProjectorCompleteness

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem classFunctionOperator_specht_expansion {A W : Type*} [Fintype A] [DecidableEq A]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (f : Equiv.Perm A → ℂ) (hf : IsConjugacyInvariant f)
    (τ : Representation ℂ (Equiv.Perm A) W) :
    classFunctionOperator f τ = ∑ μ : SizedYoungDiagram (Fintype.card A),
      classFunctionScalar f (sizedSpechtRepresentation μ) •
        characterProjector (sizedSpechtRepresentation μ) τ := by
  calc
    _ = classFunctionOperator f τ *
        (∑ μ : SizedYoungDiagram (Fintype.card A), characterProjector (sizedSpechtRepresentation μ) τ) := by
      rw [sum_spechtProjector, mul_one]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro μ hμ
      letI := spechtRepresentationOn_irreducible μ.val μ.property.symm (A := A)
      exact classFunctionOperator_mul_characterProjector f hf (sizedSpechtRepresentation μ) τ

end
end ModifiedCartan

