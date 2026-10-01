import ModifiedCartan.ScaledPolynomialJets
import ModifiedCartan.JetLengthBounds
import ModifiedCartan.PolynomialFamilyExpansion
import ModifiedCartan.PolynomialInitialValueBound

open scoped Topology BigOperators
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- The original root list controls every actual constant basis change.
This is the quantitative inequality `eq:point-initial-upper`. -/
theorem polynomial_matrix_initial_value_bound {M n : ℕ} {s : ℝ} (hs : 0 < s)
    (p : Index n → Polynomial ℂ) (B : Matrix (Index n) (Index n) ℂ)
    (roots : Fin M → ℂ)
    (hW : normalize (FewInflection.polynomialWronskian p) =
      ∏ i, (Polynomial.X - Polynomial.C (roots i)))
    (a : ℂ) (ha : (FewInflection.polynomialWronskian p).eval a ≠ 0)
    (j : Index n) (z : ℂ) :
    ‖(polynomialMatrixGauge p B j).eval (a + z)‖ ≤
      scaledJetLength n s (fun w => (polynomialMatrixGauge p B j).eval w) a *
        (∑ i : Index n, (s * ‖z‖) ^ i.val / (i.val.factorial : ℝ)) *
          Real.exp (‖z‖ * ∑ i, ‖a - roots i‖⁻¹) := by
  classical
  have hp : FewInflection.polynomialWronskian p ≠ 0 := by
    intro he
    apply ha
    rw [he, Polynomial.eval_zero]
  have hroot : (∏ i, (a - roots i)) ≠ 0 := by
    have he := congrArg (fun q : Polynomial ℂ => q.eval a) hW
    rw [normalize_apply, Polynomial.coe_normUnit, Polynomial.eval_mul, Polynomial.eval_C] at he
    have hn := mul_ne_zero ha (normUnit (FewInflection.polynomialWronskian p).leadingCoeff).ne_zero
    rw [he] at hn
    simpa only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] using hn
  have hlin := polynomialFamily_linearIndependent_of_wronskian_ne_zero p hp
  let W : Submodule ℂ (Polynomial ℂ) := Submodule.span ℂ (range p)
  have hmem : polynomialMatrixGauge p B j ∈ W := by
    apply W.sum_mem
    intro k _
    rw [← Polynomial.smul_eq_C_mul]
    exact W.smul_mem _ (Submodule.subset_span (mem_range_self k))
  let q : W := ⟨polynomialMatrixGauge p B j, hmem⟩
  have hb := Paper.eq_initial_value_bound (Module.Basis.span hlin) roots
    (by simpa only [Module.Basis.coe_span_apply] using hW) a hroot q z
  have hd (i : Index n) := derivative_norm_le_scaledJetLength hs
    (fun w => (polynomialMatrixGauge p B j).eval w) a i
  simp only [FewInflection.iteratedDeriv_polynomial_eval] at hd
  have hsum : (∑ i : Index n,
      ‖(Polynomial.derivative^[i.val] (polynomialMatrixGauge p B j)).eval a‖ *
        ‖z‖ ^ i.val / (i.val.factorial : ℝ)) ≤
      scaledJetLength n s (fun w => (polynomialMatrixGauge p B j).eval w) a *
        (∑ i : Index n, (s * ‖z‖) ^ i.val / (i.val.factorial : ℝ)) := by
    calc
      _ ≤ ∑ i : Index n, (s ^ i.val *
          scaledJetLength n s (fun w => (polynomialMatrixGauge p B j).eval w) a) *
            ‖z‖ ^ i.val / (i.val.factorial : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        gcongr
        exact hd i
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [mul_pow]
        ring
  exact hb.trans (mul_le_mul_of_nonneg_right hsum (Real.exp_pos _).le)

end ModifiedCartan
#print axioms ModifiedCartan.polynomial_matrix_initial_value_bound
