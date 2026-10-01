import ModifiedCartan.SchubertChartPolynomials
import ModifiedCartan.SchubertMonicWronskian

open scoped Classical BigOperators

namespace ModifiedCartan
noncomputable section

def schubertChartJetPolynomial {n : ℕ} (τ : YoungDiagram) (j : Fin (n + 1)) (k : ℕ) :
    MvPolynomial (SchubertChartSlot n τ) ℂ :=
  MvPolynomial.C (if k = partitionMinorOrders n τ j then 1 else 0) +
    ∑ l : {l : ℕ // l ∈ schubertFreeOrders n τ j},
      MvPolynomial.X ⟨j, l⟩ * MvPolynomial.C (if k = l.val then 1 else 0)

theorem schubertChartJetPolynomial_eval {n : ℕ} (τ : YoungDiagram)
    (x : SchubertChartSlot n τ → ℂ) (j : Fin (n + 1)) (k : ℕ) :
    MvPolynomial.eval x (schubertChartJetPolynomial τ j k) =
      (Polynomial.derivative^[k] (schubertChartPolynomial τ x j)).eval 0 := by
  rw [schubertChartPolynomial_jet]
  simp only [schubertChartJetPolynomial, map_add, map_sum, map_mul,
    MvPolynomial.eval_C]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  congr 1
  exact MvPolynomial.eval_X _

theorem schubertChartPolynomial_top_minor {n : ℕ} (τ : YoungDiagram)
    (hτ : PartitionFits n τ) (x : SchubertChartSlot n τ → ℂ) :
    (partitionPolynomialMinor τ (schubertChartPolynomial τ x)).eval 0 = 1 := by
  rw [partitionPolynomialMinor_of_fits hτ, polynomialDerivativeMinor_eval]
  have he : (fun i j : Fin (n + 1) => (Polynomial.derivative^[partitionMinorOrders n τ i]
      (schubertChartPolynomial τ x j)).eval 0) = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
    funext i j
    rw [schubertChartPolynomial_pivot_jets, Matrix.one_apply]
  erw [he, Matrix.det_one]

/-- The normalized Plucker coordinate as a polynomial in the actual affine
    Schubert chart; the normalizing top minor is identically one. -/
def schubertCoordinatePolynomial {n : ℕ} (τ μ : YoungDiagram) :
    MvPolynomial (SchubertChartSlot n τ) ℂ :=
  if PartitionFits n μ then
    MvPolynomial.C ((partitionSize τ).factorial / (standardSkewTableauCount τ ⊥ : ℂ)) *
      Matrix.det (fun i j : Fin (n + 1) =>
        schubertChartJetPolynomial τ j (partitionMinorOrders n μ i))
  else 0

theorem schubertCoordinatePolynomial_eval {n : ℕ} (τ μ : YoungDiagram)
    (hτ : PartitionFits n τ) (x : SchubertChartSlot n τ → ℂ) :
    MvPolynomial.eval x (schubertCoordinatePolynomial τ μ) =
      normalizedPartitionMinor τ (schubertChartPolynomial τ x) μ 0 := by
  rw [normalizedPartitionMinor, schubertChartPolynomial_top_minor τ hτ x, div_one]
  by_cases hμ : PartitionFits n μ
  · rw [schubertCoordinatePolynomial, ite_eq_left hμ, map_mul, MvPolynomial.eval_C]
    erw [RingHom.map_det]
    rw [partitionPolynomialMinor_of_fits hμ, polynomialDerivativeMinor_eval]
    congr 1
    congr 1
    funext i j
    exact schubertChartJetPolynomial_eval τ x j (partitionMinorOrders n μ i)
  · rw [schubertCoordinatePolynomial, ite_eq_right hμ, map_zero,
      partitionPolynomialMinor_of_not_fits hμ, Polynomial.eval_zero, mul_zero]

/-- Every chart coordinate is a genuine multivariate polynomial, with the
    exact manuscript normalization. Auxiliary to `lem:KP-correspondence`. -/
theorem normalizedSchubertCoordinate_chart {n D : ℕ} (τ μ : YoungDiagram)
    (hτ : PartitionFits n τ) (hD : n + 1 + τ.rowLen 0 ≤ D)
    (x : SchubertChartSlot n τ → ℂ) :
    normalizedSchubertCoordinate (schubertChartSpace_mem τ hτ hD x) μ 0 =
      MvPolynomial.eval x (schubertCoordinatePolynomial τ μ) := by
  rw [normalizedSchubertCoordinate_eq_basis _ (schubertChartFrame τ x).basis]
  change normalizedPartitionMinor τ (schubertChartFrame τ x).polynomials μ 0 = _
  rw [schubertChartFrame_polynomials]
  exact (schubertCoordinatePolynomial_eval τ μ hτ x).symm

/-- The monic Wronskian is the finite tableau-weighted coordinate polynomial.
    This is an exact identity obtained from the proved Plucker translation. -/
theorem schubertMonicWronskian_eq_coordinate_sum {n D : ℕ} {τ : YoungDiagram}
    {V : Submodule ℂ (Polynomial ℂ)} (hV : V ∈ polynomialSchubertCell n D τ) :
    schubertMonicWronskian hV = ∑ μ : Subpartition τ,
      Polynomial.monomial (partitionSize μ.val)
        ((standardSkewTableauCount μ.val ⊥ : ℂ) / ((partitionSize μ.val).factorial : ℂ) *
          normalizedSchubertCoordinate hV μ.val 0) := by
  apply Polynomial.funext
  intro a
  rw [← normalizedSchubertCoordinate_bot]
  have ht := Paper.lem_plucker_translation hV ⊥ 0 a
  simp only [zero_add, partitionSize_bot, Nat.sub_zero] at ht
  rw [ht, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro μ hμ
  rw [Polynomial.eval_monomial]
  ring

def schubertWronskiCoefficientPolynomial {n : ℕ} (τ : YoungDiagram) (k : ℕ) :
    MvPolynomial (SchubertChartSlot n τ) ℂ :=
  ∑ μ : Subpartition τ, if partitionSize μ.val = k then
    MvPolynomial.C ((standardSkewTableauCount μ.val ⊥ : ℂ) /
      ((partitionSize μ.val).factorial : ℂ)) * schubertCoordinatePolynomial τ μ.val else 0

/-- Wronski coefficients are polynomial functions of the affine chart.
    Auxiliary to the alternative proof of manuscript `lem:KP-correspondence`. -/
theorem schubertWronskiCoefficientPolynomial_eval {n D : ℕ} (τ : YoungDiagram)
    (hτ : PartitionFits n τ) (hD : n + 1 + τ.rowLen 0 ≤ D)
    (x : SchubertChartSlot n τ → ℂ) (k : ℕ) :
    MvPolynomial.eval x (schubertWronskiCoefficientPolynomial τ k) =
      (schubertMonicWronskian (schubertChartSpace_mem τ hτ hD x)).coeff k := by
  rw [schubertMonicWronskian_eq_coordinate_sum, Polynomial.finsetSum_coeff]
  simp only [schubertWronskiCoefficientPolynomial, map_sum]
  apply Finset.sum_congr rfl
  intro μ hμ
  rw [Polynomial.coeff_monomial, normalizedSchubertCoordinate_chart τ μ.val hτ hD x]
  split_ifs with h
  · rw [map_mul, MvPolynomial.eval_C]
  · exact map_zero _

end
end ModifiedCartan

#print axioms ModifiedCartan.normalizedSchubertCoordinate_chart
#print axioms ModifiedCartan.schubertWronskiCoefficientPolynomial_eval
