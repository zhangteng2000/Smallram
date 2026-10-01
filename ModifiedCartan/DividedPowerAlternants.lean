import ModifiedCartan.MvDividedPowerNormalization
import ModifiedCartan.DividedPowerPolynomials
import ModifiedCartan.AlternantCauchyExpansion

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem multiDegreeInverseFactorial_permuted {m : ℕ} (e : Fin m → ℕ)
    (σ : Equiv.Perm (Fin m)) :
    multiDegreeInverseFactorial (finiteExponent (e ∘ σ)) =
      ∏ i : Fin m, ((e i).factorial : ℂ)⁻¹ := by
  exact Equiv.prod_comp σ (fun i => ((e i).factorial : ℂ)⁻¹)

def finiteDividedAlternant {m : ℕ} (e : Fin m → ℕ) : MvPolynomial (Fin m) ℂ :=
  mvDividedPowerNormalize (Fin m) (finiteAlternant e)

theorem finiteDividedAlternant_eq_scalar {m : ℕ} (e : Fin m → ℕ) :
    finiteDividedAlternant e = MvPolynomial.C (∏ i : Fin m, ((e i).factorial : ℂ)⁻¹) *
      finiteAlternant e := by
  simp only [finiteDividedAlternant, finiteAlternant, mvDividedPowerNormalize,
    map_sum, mvPolynomialCoefficientScale_monomial, multiDegreeInverseFactorial_permuted,
    Finset.mul_sum, MvPolynomial.C_mul_monomial]

/-- The coefficient normalization is exactly the determinant of the divided
    monomials, including the empty determinant. Auxiliary to `lem:KP-correspondence`. -/
theorem finiteDividedAlternant_eq_det {m : ℕ} (e : Fin m → ℕ) :
    finiteDividedAlternant e = Matrix.det (fun i j : Fin m =>
      Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X i) (complexDividedPowerPolynomial (e j))) := by
  rw [finiteDividedAlternant_eq_scalar, finiteAlternant_eq_det_columns]
  simp only [complexDividedPowerPolynomial, Polynomial.eval₂_monomial]
  rw [map_prod]
  symm
  convert Matrix.det_mul_row
    (fun j : Fin m => (MvPolynomial.C (((e j).factorial : ℂ)⁻¹) : MvPolynomial (Fin m) ℂ))
    (fun i j : Fin m => (MvPolynomial.X i : MvPolynomial (Fin m) ℂ) ^ e j) using 1
  rfl

end
end ModifiedCartan

#print axioms ModifiedCartan.finiteDividedAlternant_eq_det
