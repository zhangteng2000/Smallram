import ModifiedCartan.SchubertChartPolynomials
import ModifiedCartan.SchubertCoordinateInjectivity

open scoped Classical BigOperators

namespace ModifiedCartan
noncomputable section

/-- A polynomial tuple with unit pivot jets is recovered from its free jets.
    Auxiliary to manuscript `lem:KP-correspondence`. -/
theorem schubertChartPolynomial_eq_of_normalized {n : ℕ} (τ : YoungDiagram)
    (p : Fin (n + 1) → Polynomial ℂ)
    (hd : ∀ j, (p j).natDegree ≤ partitionMinorOrders n τ j)
    (hj : ∀ i j, (Polynomial.derivative^[partitionMinorOrders n τ i] (p j)).eval 0 =
      if i = j then 1 else 0) :
    schubertChartPolynomial τ
      (fun s : SchubertChartSlot n τ => (Polynomial.derivative^[s.2.val] (p s.1)).eval 0) = p := by
  let x : SchubertChartSlot n τ → ℂ :=
    fun s => (Polynomial.derivative^[s.2.val] (p s.1)).eval 0
  have he (j : Fin (n + 1)) (k : ℕ) :
      (Polynomial.derivative^[k] (schubertChartPolynomial τ x j)).eval 0 =
        (Polynomial.derivative^[k] (p j)).eval 0 := by
    by_cases hkp : ∃ i, k = partitionMinorOrders n τ i
    · obtain ⟨i, rfl⟩ := hkp
      rw [schubertChartPolynomial_pivot_jets, hj]
    · have hne : ∀ i, k ≠ partitionMinorOrders n τ i := by simpa using hkp
      by_cases hlt : k < partitionMinorOrders n τ j
      · have hk := (mem_schubertFreeOrders τ j k).mpr ⟨hlt, hne⟩
        exact schubertChartPolynomial_free_jets τ x j ⟨k, hk⟩
      · have hgt : partitionMinorOrders n τ j < k := by
          exact lt_of_le_of_ne (Nat.le_of_not_lt hlt) (Ne.symm (hne j))
        rw [Polynomial.iterate_derivative_eq_zero ((schubertChartPolynomial_natDegree_le τ x j).trans_lt hgt),
          Polynomial.iterate_derivative_eq_zero ((hd j).trans_lt hgt)]
  funext j
  apply Polynomial.ext
  intro k
  rw [FewInflection.polynomial_coeff_eq_jet, FewInflection.polynomial_coeff_eq_jet,
    FewInflection.iteratedDeriv_polynomial_eval, FewInflection.iteratedDeriv_polynomial_eval]
  exact congrArg (fun z : ℂ => z / (k.factorial : ℂ)) (he j k)

/-- Every actual polynomial Schubert space lies in the explicit affine chart.
    The coordinate count is proved in `schubertChartSlot_card`.
    Auxiliary to manuscript `lem:KP-correspondence`. -/
theorem polynomialSchubertSpace_exists_chart {n D : ℕ} {τ : YoungDiagram}
    {V : Submodule ℂ (Polynomial ℂ)} (hV : V ∈ polynomialSchubertCell n D τ) :
    ∃ x : SchubertChartSlot n τ → ℂ, schubertChartSpace τ x = V := by
  let F := schubertFrame hV
  have ht := partitionPolynomialMinor_top_eval_ne_zero hV.1 F.polynomials
    F.polynomials_ne_zero F.degree_eq 0
  have hdet : Matrix.det (fun i j : Fin (n + 1) =>
      (Polynomial.derivative^[partitionMinorOrders n τ i] (F.polynomials j)).eval 0) ≠ 0 := by
    rw [partitionPolynomialMinor_of_fits hV.1, polynomialDerivativeMinor_eval] at ht
    exact ht
  obtain ⟨B, hB, hj⟩ := polynomialMatrixGauge_exists_identity_jets
    (partitionMinorOrders n τ) F.polynomials 0 hdet
  let p := polynomialMatrixGauge F.polynomials B
  have hs (μ : YoungDiagram) (hμ : ¬ μ ≤ τ) : (partitionPolynomialMinor μ p).eval 0 = 0 := by
    rw [partitionPolynomialMinor_matrixGauge,
      partitionPolynomialMinor_eq_zero_of_not_le μ τ F.polynomials
        (fun j => (F.degree_eq j).le) hμ, zero_mul, Polynomial.eval_zero]
  have hd (j : Fin (n + 1)) : (p j).natDegree ≤ partitionMinorOrders n τ j :=
    (polynomial_natDegree_eq_of_identity_jets_support τ p hj hs j).le
  let x : SchubertChartSlot n τ → ℂ :=
    fun s => (Polynomial.derivative^[s.2.val] (p s.1)).eval 0
  have he : schubertChartPolynomial τ x = p :=
    schubertChartPolynomial_eq_of_normalized τ p hd hj
  refine ⟨x, polynomialSchubertSpace_eq_of_coordinates
    (schubertChartSpace_mem τ hV.1 hV.2.1 x) hV ?_⟩
  intro μ
  rw [normalizedSchubertCoordinate_eq_basis _ (schubertChartFrame τ x).basis]
  change normalizedPartitionMinor τ (schubertChartFrame τ x).polynomials μ 0 = _
  rw [schubertChartFrame_polynomials, he]
  exact normalizedPartitionMinor_matrixGauge τ μ F.polynomials B hB 0

end
end ModifiedCartan

#print axioms ModifiedCartan.polynomialSchubertSpace_exists_chart
