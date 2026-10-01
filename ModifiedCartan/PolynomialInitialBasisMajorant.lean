import ModifiedCartan.InitialPolynomialTaylorCoefficients

open scoped Classical BigOperators

namespace ModifiedCartan
noncomputable section

/-- Summing an elementary-symmetric coefficient majorant gives the exact
    product majorant. The degree cutoff is derived from the coefficient bounds. -/
theorem polynomial_coeff_product_majorant {M : ℕ} (p : Polynomial ℂ)
    (j : ℕ) (x : Fin M → ℝ) (c : ℝ)
    (hlo : ∀ k, k < j → p.coeff k = 0)
    (hb : ∀ s, ‖p.coeff (j + s)‖ ≤ c * FewInflection.elementarySymmetric x s)
    (z : ℂ) :
    ‖p.eval z‖ ≤ c * ‖z‖ ^ j * ∏ i, (1 + ‖z‖ * x i) := by
  have hd : p.natDegree ≤ j + M := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    have hh := hb (k - j)
    rw [show j + (k - j) = k by omega,
      FewInflection.elementarySymmetric_of_gt_card x (by omega), mul_zero] at hh
    exact norm_eq_zero.mp (le_antisymm hh (norm_nonneg _))
  rw [Polynomial.eval_eq_sum_range' (n := j + M + 1) (by omega),
    show j + M + 1 = j + (M + 1) by omega, Finset.sum_range_add]
  have hz : (∑ k ∈ Finset.range j, p.coeff k * z ^ k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [hlo k (Finset.mem_range.mp hk), zero_mul]
  rw [hz, zero_add]
  calc
    _ ≤ ∑ s ∈ Finset.range (M + 1), ‖p.coeff (j + s)‖ * ‖z‖ ^ (j + s) := by
      simpa only [norm_mul, norm_pow] using
        norm_sum_le (Finset.range (M + 1)) (fun s => p.coeff (j + s) * z ^ (j + s))
    _ ≤ ∑ s ∈ Finset.range (M + 1),
        (c * FewInflection.elementarySymmetric x s) * ‖z‖ ^ (j + s) := by
      apply Finset.sum_le_sum
      intro s _
      exact mul_le_mul_of_nonneg_right (hb s) (by positivity)
    _ = c * ‖z‖ ^ j * ∑ s ∈ Finset.range (M + 1),
        FewInflection.elementarySymmetric x s * ‖z‖ ^ s := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      rw [pow_add]
      ring
    _ = _ := by rw [FewInflection.elementarySymmetric_generating_identity]

namespace Paper

/-- LaTeX `prop:initial-basis`, equation `eq:basismajorant`, for the actual
    normalized basis, with no assumed bound on its coefficients or degree. -/
theorem prop_initial_basis {M n : ℕ} {V : Submodule ℂ (Polynomial ℂ)}
    (b : Module.Basis (Fin (n + 1)) ℂ V) (roots : Fin M → ℂ)
    (hW : normalize (FewInflection.polynomialWronskian (fun j => (b j).val)) =
      ∏ i, (Polynomial.X - Polynomial.C (roots i))) (a : ℂ)
    (ha : (∏ i, (a - roots i)) ≠ 0)
    (hb : ∀ i j : Fin (n + 1),
      (Polynomial.derivative^[i.val] (b j).val).eval a = if i = j then 1 else 0)
    (j : Fin (n + 1)) (z : ℂ) :
    ‖(b j).val.eval (a + z)‖ ≤ (‖z‖ ^ j.val / (j.val.factorial : ℝ)) *
      ∏ i, (1 + ‖z‖ / ‖a - roots i‖) := by
  have h := polynomial_coeff_product_majorant ((b j).val.taylor a) j.val
    (fun i => ‖a - roots i‖⁻¹) (1 / (j.val.factorial : ℝ))
    (initialPolynomialBasis_taylorCoeff_zero_of_lt b a hb j)
    (initialPolynomialBasis_taylorCoeff_norm_le b roots hW a ha hb j) z
  simpa only [Polynomial.taylor_eval, add_comm z a, div_eq_mul_inv, one_mul,
    mul_comm ((j.val.factorial : ℝ)⁻¹) (‖z‖ ^ j.val)] using h

end Paper
end
end ModifiedCartan

#print axioms ModifiedCartan.Paper.prop_initial_basis