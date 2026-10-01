import ModifiedCartan.ClassFunctionSpechtExpansion
import ModifiedCartan.ClassFunctionRegularCoefficients

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

/-- Exact Fourier expansion in the already constructed and proved complete
family of Specht characters. Auxiliary to the Frobenius/Schur bridge for
LaTeX `lem:KP-correspondence`; it does not identify Schur polynomials. -/
theorem classFunction_specht_fourier {A : Type*} [Fintype A] [DecidableEq A]
    (f : Equiv.Perm A → ℂ) (hf : IsConjugacyInvariant f) (g : Equiv.Perm A) :
    f g = ∑ μ : SizedYoungDiagram (Fintype.card A),
      (sizedSpechtRepresentation μ).character g *
        classFunctionFourierCoefficient f (sizedSpechtRepresentation μ) := by
  letI := (MonoidAlgebra.basis (Equiv.Perm A) ℂ).finiteDimensional_of_finite
  have h := congrArg
    (fun L : Module.End ℂ ℂ[Equiv.Perm A] => (L (MonoidAlgebra.single 1 1)).coeff g⁻¹)
    (classFunctionOperator_specht_expansion f hf (Representation.leftRegular ℂ (Equiv.Perm A)))
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, MonoidAlgebra.coeff_sum,
    Finsupp.finsetSum_apply, MonoidAlgebra.coeff_smul_apply, smul_eq_mul,
    classFunctionOperator_regular_coeff, characterProjector_regular_coeff, inv_inv] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro μ hμ
  letI := spechtRepresentationOn_irreducible μ.val μ.property.symm (A := A)
  rw [← mul_assoc, classFunctionScalar_mul_dimension, mul_comm]

end
end ModifiedCartan

