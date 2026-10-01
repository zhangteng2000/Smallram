import ModifiedCartan.PolynomialInitialBasisCoordinates
import ModifiedCartan.PolynomialInitialBasisMajorant
import Mathlib.Analysis.Complex.Exponential

open scoped Classical BigOperators

namespace ModifiedCartan
noncomputable section

/-- Initial derivatives control every member of the polynomial space by the
    root product. Auxiliary to manuscript `eq:initial-value-bound`. -/
theorem polynomialInitialValue_product_bound {M n : ℕ}
    {V : Submodule ℂ (Polynomial ℂ)} (b : Module.Basis (Fin (n + 1)) ℂ V)
    (roots : Fin M → ℂ)
    (hW : normalize (FewInflection.polynomialWronskian (fun j => (b j).val)) =
      ∏ i, (Polynomial.X - Polynomial.C (roots i))) (a : ℂ)
    (ha : (∏ i, (a - roots i)) ≠ 0)
    (hb : ∀ i j : Fin (n + 1),
      (Polynomial.derivative^[i.val] (b j).val).eval a = if i = j then 1 else 0)
    (h : V) (z : ℂ) :
    ‖h.val.eval (a + z)‖ ≤
      (∑ i : Fin (n + 1), ‖(Polynomial.derivative^[i.val] h.val).eval a‖ *
        ‖z‖ ^ i.val / (i.val.factorial : ℝ)) *
      ∏ i, (1 + ‖z‖ / ‖a - roots i‖) := by
  have he : h.val.eval (a + z) = ∑ i : Fin (n + 1),
      (Polynomial.derivative^[i.val] h.val).eval a * (b i).val.eval (a + z) := by
    have hh := congrArg (fun u : V => u.val.eval (a + z)) (b.sum_repr h)
    simpa only [Submodule.coe_sum, Submodule.coe_smul, Polynomial.eval_finsetSum,
      Polynomial.eval_smul, smul_eq_mul, polynomialBasis_repr_eq_jet b a hb] using hh.symm
  rw [he]
  calc
    _ ≤ ∑ i : Fin (n + 1), ‖(Polynomial.derivative^[i.val] h.val).eval a‖ *
        ‖(b i).val.eval (a + z)‖ := by
      simpa only [norm_mul] using norm_sum_le Finset.univ
        (fun i : Fin (n + 1) =>
          (Polynomial.derivative^[i.val] h.val).eval a * (b i).val.eval (a + z))
    _ ≤ ∑ i : Fin (n + 1), ‖(Polynomial.derivative^[i.val] h.val).eval a‖ *
        ((‖z‖ ^ i.val / (i.val.factorial : ℝ)) *
          ∏ k, (1 + ‖z‖ / ‖a - roots k‖)) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (Paper.prop_initial_basis b roots hW a ha hb i z) (norm_nonneg _)
    _ = _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring

namespace Paper

/-- LaTeX `eq:initial-value-bound` for every actual member of V. The
    normalized basis is constructed from the off-root condition. -/
theorem eq_initial_value_bound {M n : ℕ}
    {V : Submodule ℂ (Polynomial ℂ)} (b₀ : Module.Basis (Fin (n + 1)) ℂ V)
    (roots : Fin M → ℂ)
    (hW : normalize (FewInflection.polynomialWronskian (fun j => (b₀ j).val)) =
      ∏ i, (Polynomial.X - Polynomial.C (roots i))) (a : ℂ)
    (ha : (∏ i, (a - roots i)) ≠ 0) (h : V) (z : ℂ) :
    ‖h.val.eval (a + z)‖ ≤
      (∑ i : Fin (n + 1), ‖(Polynomial.derivative^[i.val] h.val).eval a‖ *
        ‖z‖ ^ i.val / (i.val.factorial : ℝ)) *
      Real.exp (‖z‖ * ∑ i, ‖a - roots i‖⁻¹) := by
  obtain ⟨b, hb⟩ := polynomialBasis_exists_identity_jets b₀ a
    (polynomialWronskian_eval_ne_zero_of_roots b₀ roots hW a ha)
  have hWb : normalize (FewInflection.polynomialWronskian (fun j => (b j).val)) =
      ∏ i, (Polynomial.X - Polynomial.C (roots i)) :=
    (polynomialWronskian_normalize_basis_change b₀ b).trans hW
  have hp : (∏ i, (1 + ‖z‖ / ‖a - roots i‖)) ≤
      Real.exp (‖z‖ * ∑ i, ‖a - roots i‖⁻¹) := by
    rw [Finset.mul_sum]
    simpa only [div_eq_mul_inv] using
      Real.prod_one_add_le_exp_sum Finset.univ
        (f := fun i : Fin M => ‖z‖ * ‖a - roots i‖⁻¹) (fun i => by positivity)
  exact (polynomialInitialValue_product_bound b roots hWb a ha hb h z).trans
    (mul_le_mul_of_nonneg_left hp (Finset.sum_nonneg (fun i _ => by positivity)))

end Paper
end
end ModifiedCartan

#print axioms ModifiedCartan.Paper.eq_initial_value_bound