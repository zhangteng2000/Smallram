import ModifiedCartan.SingleVariableSeries

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

attribute [local instance 2000] MvPowerSeries.instAlgebra

/-- Retain each exponent as a polynomial monomial, and record total degree in
    a separate formal variable. Auxiliary to paper `lem:KP-correspondence`. -/
def seriesHomogenization (B R : Type*) [Fintype B] [CommSemiring R] :
    MvPowerSeries B R →+* PowerSeries (MvPolynomial B R) :=
  (MvPowerSeries.rename (R := MvPolynomial B R) (fun _ : B => ())).toRingHom.comp
    ((MvPowerSeries.rescale (fun b : B => (MvPolynomial.X b : MvPolynomial B R))).comp
      (MvPowerSeries.map MvPolynomial.C))

theorem polynomial_rescale_series_coeff {B R : Type*} [CommSemiring R]
    (F : MvPowerSeries B R) (d : B →₀ ℕ) :
    MvPowerSeries.coeff d
      (MvPowerSeries.rescale (fun b : B => (MvPolynomial.X b : MvPolynomial B R))
        (MvPowerSeries.map MvPolynomial.C F)) =
      MvPolynomial.monomial d (MvPowerSeries.coeff d F) := by
  rw [MvPowerSeries.coeff_rescale, MvPowerSeries.coeff_map, MvPolynomial.monomial_eq,
    mul_comm]

theorem finsupp_degree_unit (d : Unit →₀ ℕ) : d.degree = d () := by
  rw [Finsupp.degree_eq_sum]
  simp

theorem finsupp_mapDomain_unit {B : Type*} (d : B →₀ ℕ) :
    Finsupp.mapDomain (fun _ : B => ()) d = Finsupp.single () d.degree := by
  have h := Finsupp.degree_mapDomain (fun _ : B => ()) d
  rw [finsupp_degree_unit] at h
  calc
    _ = Finsupp.single () ((Finsupp.mapDomain (fun _ : B => ()) d) ()) :=
      Finsupp.unique_single _
    _ = _ := congrArg (Finsupp.single ()) h

theorem seriesHomogenization_coeff {B R : Type*} [Fintype B] [CommSemiring R]
    (F : MvPowerSeries B R) (n : ℕ) :
    PowerSeries.coeff n (seriesHomogenization B R F) =
      ∑ d ∈ (Finsupp.finite_of_degree_eq (σ := B) n).toFinset,
        MvPolynomial.monomial d (MvPowerSeries.coeff d F) := by
  change MvPowerSeries.coeff (Finsupp.single () n)
    (MvPowerSeries.rename (fun _ : B => ())
      (MvPowerSeries.rescale (fun b : B => (MvPolynomial.X b : MvPolynomial B R))
        (MvPowerSeries.map MvPolynomial.C F))) = _
  rw [MvPowerSeries.coeff_rename]
  simp only [polynomial_rescale_series_coeff]
  apply Finset.sum_congr
  · ext d
    simp [finsupp_mapDomain_unit]
  · intro d _
    rfl

theorem seriesHomogenization_coeff_coeff {B R : Type*} [Fintype B] [CommSemiring R]
    (F : MvPowerSeries B R) (n : ℕ) (d : B →₀ ℕ) :
    MvPolynomial.coeff d (PowerSeries.coeff n (seriesHomogenization B R F)) =
      if d.degree = n then MvPowerSeries.coeff d F else 0 := by
  rw [seriesHomogenization_coeff, MvPolynomial.coeff_sum]
  simp [MvPolynomial.coeff_monomial]

end
end ModifiedCartan

#print axioms ModifiedCartan.seriesHomogenization_coeff_coeff
