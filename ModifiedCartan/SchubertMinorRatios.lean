import ModifiedCartan.SchubertMonicWronskian

open scoped Classical BigOperators

namespace ModifiedCartan
noncomputable section

theorem partitionPolynomialMinor_top_ne_zero_of_basis {n D : ℕ} {τ : YoungDiagram}
    {V : Submodule ℂ (Polynomial ℂ)} (hV : V ∈ polynomialSchubertCell n D τ)
    (b : Module.Basis (Fin (n + 1)) ℂ V) (a : ℂ) :
    (partitionPolynomialMinor τ (fun j => (b j).val)).eval a ≠ 0 := by
  rw [partitionPolynomialMinor_basis_change (schubertFrame hV).basis b τ,
    Polynomial.eval_mul, Polynomial.eval_C]
  exact mul_ne_zero
    (partitionPolynomialMinor_top_eval_ne_zero hV.1 (schubertFrame hV).polynomials
      (schubertFrame hV).polynomials_ne_zero (schubertFrame hV).degree_eq a)
    (polynomialBasis_toMatrix_det_ne_zero (schubertFrame hV).basis b)

/-- Normalization cancels in the ratio of a derivative minor to the Wronskian,
    for every basis of the actual space. -/
theorem normalizedSchubertCoordinate_div_bot {n D : ℕ} {τ : YoungDiagram}
    {V : Submodule ℂ (Polynomial ℂ)} (hV : V ∈ polynomialSchubertCell n D τ)
    (b : Module.Basis (Fin (n + 1)) ℂ V) (μ : YoungDiagram) (a : ℂ) :
    normalizedSchubertCoordinate hV μ a / normalizedSchubertCoordinate hV ⊥ a =
      (partitionPolynomialMinor μ (fun j => (b j).val)).eval a /
        (FewInflection.polynomialWronskian (fun j => (b j).val)).eval a := by
  have hc : ((partitionSize τ).factorial : ℂ) / (standardSkewTableauCount τ ⊥ : ℂ) ≠ 0 := by
    apply div_ne_zero
    · exact_mod_cast Nat.factorial_ne_zero (partitionSize τ)
    · exact_mod_cast (standardSkewTableauCount_pos bot_le hV.1).ne'
  rw [normalizedSchubertCoordinate_eq_basis hV b μ,
    normalizedSchubertCoordinate_eq_basis hV b ⊥]
  unfold normalizedPartitionMinor
  rw [div_div_div_cancel_right₀ (partitionPolynomialMinor_top_ne_zero_of_basis hV b a),
    mul_div_mul_left _ _ hc, partitionPolynomialMinor_bot]

end
end ModifiedCartan

#print axioms ModifiedCartan.normalizedSchubertCoordinate_div_bot