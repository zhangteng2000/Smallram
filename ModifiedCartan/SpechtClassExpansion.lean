import ModifiedCartan.SpechtProjectorCompleteness
import ModifiedCartan.ClassScalarIsotypic

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem classWeightedOperator_specht_expansion {W : Type*} [AddCommGroup W]
    [Module ℂ W] [FiniteDimensional ℂ W] (f : Equiv.Perm A → ℂ)
    (hf : IsConjugationInvariant f) (τ : Representation ℂ (Equiv.Perm A) W) :
    classWeightedOperator f τ = ∑ μ : SizedYoungDiagram (Fintype.card A),
      classScalar f (sizedSpechtRepresentation μ) • characterProjector (sizedSpechtRepresentation μ) τ := by
  calc
    _ = classWeightedOperator f τ * ∑ μ : SizedYoungDiagram (Fintype.card A),
        characterProjector (sizedSpechtRepresentation μ) τ := by rw [sum_spechtProjector, mul_one]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro μ _
      let _ := spechtRepresentationOn_irreducible μ.val μ.property.symm (A := A)
      exact classWeightedOperator_mul_projector f hf _ τ

/-- Fourier expansion of every actual conjugation-invariant function in the
constructed Specht characters, derived from regular-representation exhaustion. -/
theorem specht_class_function_expansion (f : Equiv.Perm A → ℂ)
    (hf : IsConjugationInvariant f) (g : Equiv.Perm A) :
    f g = ∑ μ : SizedYoungDiagram (Fintype.card A),
      ((Nat.card (Equiv.Perm A) : ℂ)⁻¹ * ∑ h : Equiv.Perm A,
        f h⁻¹ * (sizedSpechtRepresentation μ).character h) * (sizedSpechtRepresentation μ).character g := by
  let _ := (MonoidAlgebra.basis (Equiv.Perm A) ℂ).finiteDimensional_of_finite
  have he := congrArg (fun T : Module.End ℂ ℂ[Equiv.Perm A] =>
      (T (MonoidAlgebra.single 1 1)).coeff g⁻¹)
    (classWeightedOperator_specht_expansion f hf (Representation.leftRegular ℂ (Equiv.Perm A)))
  rw [classWeightedOperator_regular_coefficient, inv_inv] at he
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, MonoidAlgebra.coeff_sum,
    Finsupp.finsetSum_apply, MonoidAlgebra.coeff_smul_apply, smul_eq_mul,
    characterProjector_regular_coefficient, inv_inv] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro μ _
  let _ := spechtRepresentationOn_irreducible μ.val μ.property.symm (A := A)
  rw [← mul_assoc, classScalar_normalized]

end
end ModifiedCartan


