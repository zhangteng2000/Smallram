import ModifiedCartan.PolynomialCoefficientExpansion
import ModifiedCartan.PolynomialODEKernelBound
import ModifiedCartan.LocalPolynomialApproximation

open scoped BigOperators Classical
set_option autoImplicit false
namespace ModifiedCartan

theorem polynomialFamily_linearIndependent_of_wronskian_ne_zero {n : ℕ}
    (p : Fin (n + 1) → Polynomial ℂ) (hp : FewInflection.polynomialWronskian p ≠ 0) :
    LinearIndependent ℂ p := by
  have he : ∃ z : ℂ, (FewInflection.polynomialWronskian p).eval z ≠ 0 := by
    by_contra h
    apply hp
    apply Polynomial.funext
    intro z
    have hz : (FewInflection.polynomialWronskian p).eval z = 0 := by
      by_contra hz
      exact h ⟨z, hz⟩
    simpa only [Polynomial.eval_zero] using hz
  obtain ⟨z, hz⟩ := he
  have hw : FewInflection.wronskian n (fun j w => (p j).eval w) z ≠ 0 := by
    simpa only [polynomialWronskian_eval_eq_wronskian] using hz
  have hlin := FewInflection.linearlyIndependent_of_wronskian_ne_zero
    (fun j w => (p j).eval w) z
    (fun i j => (AnalyticOnNhd.eval_polynomial (p j) z (Set.mem_univ z)).contDiffAt) hw
  exact LinearIndependent.of_comp polynomialFunctionLinear hlin

/-- The M7 coefficient expansion applied directly to a polynomial tuple,
with independence proved from its nonzero Wronskian. Used in Step 4 of
`prop:localcompact`; no independently chosen basis is required as input. -/
theorem polynomialFamily_product_expansion {M n : ℕ}
    (p : Fin (n + 1) → Polynomial ℂ) (hp : FewInflection.polynomialWronskian p ≠ 0)
    (a : Fin M → ℂ)
    (hW : normalize (FewInflection.polynomialWronskian p) =
      ∏ i, (Polynomial.X - Polynomial.C (a i))) :
    ∃ γ : ℕ → Finset (Fin M) → ℂ,
      (∀ q I, ‖γ q I‖ ≤ (q.factorial : ℝ)) ∧
      ∀ (q : ℕ) (hq0 : 1 ≤ q) (hqn : q ≤ n + 1) (z : ℂ),
        (∏ i, (z - a i)) ≠ 0 →
        FewInflection.fundamentalCoefficients n (fun j w => (p j).eval w) z
          ⟨n + 1 - q, by omega⟩ =
          (-1 : ℂ) ^ q * ∑ I ∈ (Finset.univ : Finset (Fin M)).powersetCard q,
            γ q I / (∏ i ∈ I, (z - a i)) := by
  have hlin := polynomialFamily_linearIndependent_of_wronskian_ne_zero p hp
  have he := polynomialFundamentalCoefficient_product_expansion (Module.Basis.span hlin) a
    (by simpa only [Module.Basis.coe_span_apply] using hW)
  simpa only [Module.Basis.coe_span_apply] using he

end ModifiedCartan
#print axioms ModifiedCartan.polynomialFamily_product_expansion
