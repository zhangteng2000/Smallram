import ModifiedCartan.HomogenizedGeometricSeries
import ModifiedCartan.GeometricProductCoefficients

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

def finiteCauchyKernelSeries {A B R : Type*} [Fintype A] [Fintype B] [CommSemiring R]
    (x : A → R) : MvPowerSeries B R := ∏ i : A, ∏ j : B, geometricMvSeries j (x i)

def finiteCauchyCoefficientPolynomial {A B R : Type*} [Fintype A] [Fintype B]
    [CommSemiring R] (x : A → R) (n : ℕ) : MvPolynomial B R :=
  ∑ s : Sym (A × B) n,
    (s.val.map (fun p => MvPolynomial.C (x p.1) * MvPolynomial.X p.2)).prod

theorem finiteCauchyKernelSeries_homogenization_coeff {A B R : Type*}
    [Fintype A] [Fintype B] [CommRing R] (x : A → R) (n : ℕ) :
    PowerSeries.coeff n (seriesHomogenization B R (finiteCauchyKernelSeries (B := B) x)) =
      finiteCauchyCoefficientPolynomial (B := B) x n := by
  simp only [finiteCauchyKernelSeries, map_prod, seriesHomogenization_geometricMvSeries]
  have hp : (∏ i : A, ∏ j : B, geometricPowerSeries (MvPolynomial.C (x i) * MvPolynomial.X j)) =
      ∏ p : A × B, geometricPowerSeries
        (MvPolynomial.C (x p.1) * (MvPolynomial.X p.2 : MvPolynomial B R)) := by
    rw [← Finset.prod_product', Finset.univ_product_univ]
  rw [hp]
  convert! geometricPowerSeries_prod_coeff
    (fun p : A × B => MvPolynomial.C (x p.1) * (MvPolynomial.X p.2 : MvPolynomial B R)) n using 1
  apply Finset.sum_congr (by ext; simp)
  intro s _
  rfl

/-- Coefficient-level link between the finite multiset Cauchy sum and the
    actual formal kernel, auxiliary to paper `lem:KP-correspondence`. -/
theorem finiteCauchyCoefficientPolynomial_coeff {A B R : Type*}
    [Fintype A] [Fintype B] [CommRing R] (x : A → R) (n : ℕ) (d : B →₀ ℕ) :
    MvPolynomial.coeff d (finiteCauchyCoefficientPolynomial (B := B) x n) =
      if d.degree = n then MvPowerSeries.coeff d (finiteCauchyKernelSeries (B := B) x) else 0 := by
  rw [← finiteCauchyKernelSeries_homogenization_coeff, seriesHomogenization_coeff_coeff]

end
end ModifiedCartan

#print axioms ModifiedCartan.finiteCauchyCoefficientPolynomial_coeff
