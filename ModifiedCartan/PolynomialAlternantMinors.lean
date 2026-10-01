import ModifiedCartan.PolynomialAlternantTranslation
import ModifiedCartan.KPDividedPolynomialTranslation

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

/-- Reversing both the derivative rows and polynomial columns identifies the
    ordered alternating coefficient with the paper's derivative minor.
    Auxiliary to manuscript `lem:KP-correspondence`. -/
theorem polynomialAlternant_translate_partition_coeff {n : ℕ}
    (p : Fin (n + 1) → Polynomial ℂ) (μ : YoungDiagram)
    (hμ : PartitionFits n μ) (a : ℂ) :
    MvPolynomial.coeff (finiteExponent (partitionAlternantExponent (n + 1) μ))
      (mvPolynomialTranslate (Fin (n + 1)) a (polynomialAlternant p)) =
        multiDegreeInverseFactorial (finiteExponent (partitionAlternantExponent (n + 1) μ)) *
          (partitionPolynomialMinor μ (fun j => p j.rev)).eval a := by
  rw [polynomialAlternant_translate, polynomialAlternant_taylor_coeff,
    partitionPolynomialMinor_of_fits hμ, polynomialDerivativeMinor_eval]
  congr 1
  have hd := Matrix.det_submatrix_equiv_self (Fin.revPerm : Equiv.Perm (Fin (n + 1)))
    (fun i j : Fin (n + 1) => (Polynomial.derivative^[partitionAlternantExponent (n + 1) μ i]
      (p j)).eval a)
  change Matrix.det (fun i j : Fin (n + 1) =>
    (Polynomial.derivative^[partitionAlternantExponent (n + 1) μ i.rev] (p j.rev)).eval a) = _ at hd
  simp only [partitionAlternantExponent_rev] at hd
  convert hd.symm using 1 <;> rfl

/-- Determinant representation recovers the exact scalar of every translated
    derivative minor; no coordinates are assumed. -/
theorem finitePartitionDividedPolynomial_representation_minor {n N : ℕ}
    (hN : N ≤ n + 1) (χ : YoungDiagram → ℂ)
    (p : Fin (n + 1) → Polynomial ℂ) (c : ℂ)
    (hP : finitePartitionDividedPolynomial (n + 1) N χ =
      MvPolynomial.C c * polynomialAlternant p)
    (μ : YoungDiagram) (hμ : PartitionFits n μ) (a : ℂ) :
    (kpJointValuePolynomial N χ μ).eval a =
      c * (partitionPolynomialMinor μ (fun j => p j.rev)).eval a := by
  have he := finitePartitionDividedPolynomial_translate_coeff hN χ μ hμ a
  rw [hP, map_mul, mvPolynomialTranslate_C, MvPolynomial.coeff_C_mul,
    polynomialAlternant_translate_partition_coeff p μ hμ a] at he
  apply mul_left_cancel₀ (multiDegreeInverseFactorial_ne_zero
    (finiteExponent (partitionAlternantExponent (n + 1) μ)))
  rw [← he]
  ring

end
end ModifiedCartan

#print axioms ModifiedCartan.finitePartitionDividedPolynomial_representation_minor