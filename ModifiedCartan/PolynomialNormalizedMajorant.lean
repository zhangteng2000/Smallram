import ModifiedCartan.PolynomialInitialBasisMajorant
import ModifiedCartan.PolynomialJetMatrixGauge
import ModifiedCartan.PolynomialRootCount
import ModifiedCartan.EntireTaylorJets

open scoped Topology BigOperators
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

/-- Applying `prop:initial-basis` to a normalized polynomial tuple.
The basis is constructed from its jets, and its Wronskian roots are
obtained from the complex polynomial factorization theorem. -/
theorem normalized_polynomial_tuple_majorant {n : ℕ}
    (p : Fin (n + 1) → Polynomial ℂ)
    (hjets : ∀ i j : Fin (n + 1),
      iteratedDeriv i.val (fun z => (p j).eval z) 0 = if i = j then 1 else 0) :
    ∃ a : Fin (FewInflection.polynomialWronskian p).natDegree → ℂ,
      normalize (FewInflection.polynomialWronskian p) =
        ∏ i, (Polynomial.X - Polynomial.C (a i)) ∧
      (∀ i, a i ≠ 0) ∧ ∀ (j : Fin (n + 1)) (z : ℂ),
        ‖(p j).eval z‖ ≤ (‖z‖ ^ j.val / (j.val.factorial : ℝ)) *
          ∏ i, (1 + ‖z‖ / ‖a i‖) := by
  classical
  have hj : ∀ i j : Fin (n + 1),
      (Polynomial.derivative^[i.val] (p j)).eval 0 = if i = j then 1 else 0 := by
    intro i j
    simpa only [FewInflection.iteratedDeriv_polynomial_eval] using hjets i j
  have hw : (FewInflection.polynomialWronskian p).eval 0 = 1 := by
    simpa only [FewInflection.polynomialWronskian_eval, FewInflection.derivativeMinor,
      FewInflection.wronskian] using wronskian_zero_of_initial_jets hjets
  have hwne : FewInflection.polynomialWronskian p ≠ 0 := by
    intro h
    simp [h] at hw
  obtain ⟨a, ha⟩ := exists_normalized_polynomial_root_list _ hwne
  have hprod : (∏ i, ((0 : ℂ) - a i)) ≠ 0 := by
    have he := congrArg (fun q : Polynomial ℂ => q.eval 0) ha
    rw [normalize_apply, Polynomial.coe_normUnit, Polynomial.eval_mul, Polynomial.eval_C,
      hw, one_mul] at he
    have hne := (normUnit (FewInflection.polynomialWronskian p).leadingCoeff).ne_zero
    rw [he] at hne
    simpa only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C] using hne
  have hli := polynomialTuple_linearIndependent_of_identity_jets Fin.val p 0 hj
  let b := Module.Basis.span hli
  refine ⟨a, ha, ?_, ?_⟩
  · intro i hi
    apply hprod
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  · intro j z
    have h := Paper.prop_initial_basis b a
      (by simpa only [b, Module.Basis.coe_span_apply] using ha) 0 hprod
      (by simpa only [b, Module.Basis.coe_span_apply] using hj) j z
    simpa only [b, Module.Basis.coe_span_apply, zero_add, zero_sub, norm_neg] using h

end ModifiedCartan
#print axioms ModifiedCartan.normalized_polynomial_tuple_majorant
