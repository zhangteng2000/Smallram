import ModifiedCartan.FormalFrobeniusKernel
import ModifiedCartan.VandermondeAlternantMaps
import ModifiedCartan.PolynomialScalarSeries
import ModifiedCartan.FiniteCauchySeries

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem finiteVandermondeSeries_product (m : ℕ) :
    MvPowerSeries.C (finiteVandermondeAlternant m) *
      polynomialScalarExtensionSeries (Fin m) (Fin m) ℂ (finiteVandermondeAlternant m) =
      finiteVandermondeProduct (fun i : Fin m => MvPowerSeries.C (MvPolynomial.X i : MvPolynomial (Fin m) ℂ)) *
        finiteVandermondeProduct (fun j : Fin m => (MvPowerSeries.X j :
          MvPowerSeries (Fin m) (MvPolynomial (Fin m) ℂ))) := by
  simpa only [polynomialScalarExtensionSeries_X] using
    finiteVandermondeAlternant_map_mul
      (MvPowerSeries.C : MvPolynomial (Fin m) ℂ →+* MvPowerSeries (Fin m) (MvPolynomial (Fin m) ℂ))
      (polynomialScalarExtensionSeries (Fin m) (Fin m) ℂ)

theorem finiteCauchySeries_alternant_identity (m : ℕ) :
    (finiteCauchySeriesMatrix (fun i : Fin m => (MvPolynomial.X i : MvPolynomial (Fin m) ℂ))).det =
      MvPowerSeries.C (finiteVandermondeAlternant m) *
        (polynomialScalarExtensionSeries (Fin m) (Fin m) ℂ (finiteVandermondeAlternant m) *
          finiteCauchyKernelSeries (B := Fin m)
            (fun i : Fin m => (MvPolynomial.X i : MvPolynomial (Fin m) ℂ))) := by
  rw [finiteCauchySeriesMatrix_det, ← finiteVandermondeSeries_product, mul_assoc]
  rfl

theorem finiteAlternant_eq_det_columns {m : ℕ} (e : Fin m → ℕ) :
    finiteAlternant e = Matrix.det (fun i j : Fin m =>
      (MvPolynomial.X i : MvPolynomial (Fin m) ℂ) ^ e j) := by
  rw [finiteAlternant_eq_det]
  exact Matrix.det_transpose (fun i j : Fin m =>
    (MvPolynomial.X i : MvPolynomial (Fin m) ℂ) ^ e j)

/-- Exact finite Frobenius expansion of an arbitrary homogeneous alternant,
    derived from the Cauchy determinant. Auxiliary to `lem:KP-correspondence`. -/
theorem finiteAlternant_frobenius_expansion {m : ℕ} (n : ℕ) (d : Fin m →₀ ℕ)
    (hd : d.degree = (finiteStaircaseDegree m).degree + n) :
    finiteAlternant (fun i => d i) = finiteVandermondeAlternant m *
      ∑ μ : SizedYoungDiagram n, finiteFrobeniusPolynomial (Fin m) μ.val *
        MvPolynomial.C (MvPolynomial.coeff d
          (finiteVandermondeAlternant m * finiteFrobeniusPolynomial (Fin m) μ.val)) := by
  have h := congrArg (MvPowerSeries.coeff d) (finiteCauchySeries_alternant_identity m)
  rw [finiteCauchySeriesMatrix_coeff_det, MvPowerSeries.coeff_C_mul,
    polynomialScalarExtensionSeries_apply, finiteCauchyKernelSeries_alternant_coeff n d hd] at h
  rw [finiteAlternant_eq_det_columns]
  exact h

end
end ModifiedCartan

#print axioms ModifiedCartan.finiteAlternant_frobenius_expansion
