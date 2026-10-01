import ModifiedCartan.SeparatedFrobeniusCauchy
import ModifiedCartan.HomogeneousSeriesCoefficients
import ModifiedCartan.AlternantHomogeneity

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem finiteCauchyKernelSeries_coeff_frobenius {A B : Type*} [Fintype A] [Fintype B]
    (n : ℕ) (d : B →₀ ℕ) (hd : d.degree = n) :
    MvPowerSeries.coeff d (finiteCauchyKernelSeries (B := B)
      (fun a : A => (MvPolynomial.X a : MvPolynomial A ℂ))) =
      ∑ μ : SizedYoungDiagram n, finiteFrobeniusPolynomial A μ.val *
        MvPolynomial.C (MvPolynomial.coeff d (finiteFrobeniusPolynomial B μ.val)) := by
  have h := congrArg (MvPolynomial.coeff d)
    (finiteFrobeniusPolynomial_cauchy_separated (A := A) (B := B) n)
  rw [finiteCauchyCoefficientPolynomial_coeff, ite_eq_left hd] at h
  simpa only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_map] using h.symm

/-- The homogeneous part of the formal Cauchy kernel after multiplying by the
    actual alternant. Auxiliary to paper `lem:KP-correspondence`. -/
theorem finiteCauchyKernelSeries_alternant_coeff {A : Type*} [Fintype A] {m : ℕ}
    (n : ℕ) (d : Fin m →₀ ℕ) (hd : d.degree = (finiteStaircaseDegree m).degree + n) :
    MvPowerSeries.coeff d
      (((MvPolynomial.map MvPolynomial.C (finiteVandermondeAlternant m) :
          MvPolynomial (Fin m) (MvPolynomial A ℂ)) : MvPowerSeries (Fin m) (MvPolynomial A ℂ)) *
        finiteCauchyKernelSeries (B := Fin m) (fun a : A => (MvPolynomial.X a : MvPolynomial A ℂ))) =
      ∑ μ : SizedYoungDiagram n, finiteFrobeniusPolynomial A μ.val *
        MvPolynomial.C (MvPolynomial.coeff d
          (finiteVandermondeAlternant m * finiteFrobeniusPolynomial (Fin m) μ.val)) := by
  rw [homogeneous_polynomial_mul_series_coeff _
    (finiteCauchyCoefficientPolynomial (B := Fin m) (fun a : A => (MvPolynomial.X a : MvPolynomial A ℂ)) n)
    _ n (finiteStaircaseDegree m).degree
    ((finiteVandermondeAlternant_isHomogeneous m).map MvPolynomial.C)
    (fun e he => by rw [finiteCauchyCoefficientPolynomial_coeff, ite_eq_left he]) d hd]
  rw [← finiteFrobeniusPolynomial_cauchy_separated]
  simp only [Finset.mul_sum, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro μ _
  rw [← mul_assoc, mul_comm (MvPolynomial.map MvPolynomial.C (finiteVandermondeAlternant m)),
    mul_assoc, ← map_mul, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map]

end
end ModifiedCartan

#print axioms ModifiedCartan.finiteCauchyKernelSeries_alternant_coeff
