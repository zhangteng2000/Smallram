import ModifiedCartan.PolynomialJetMatrixGauge
import ModifiedCartan.PolynomialSpaceSchubert
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

open scoped Classical BigOperators

namespace ModifiedCartan
noncomputable section

/-- The nonzero Wronskian at a point constructs an actual normalized basis.
    Existence assertion in manuscript `prop:initial-basis`. -/
theorem polynomialBasis_exists_identity_jets {n : ℕ}
    {V : Submodule ℂ (Polynomial ℂ)} (b₀ : Module.Basis (Fin (n + 1)) ℂ V)
    (a : ℂ) (ha : (FewInflection.polynomialWronskian (fun j => (b₀ j).val)).eval a ≠ 0) :
    ∃ b : Module.Basis (Fin (n + 1)) ℂ V, ∀ i j : Fin (n + 1),
      (Polynomial.derivative^[i.val] (b j).val).eval a = if i = j then 1 else 0 := by
  let p : Fin (n + 1) → Polynomial ℂ := fun j => (b₀ j).val
  have hd : Matrix.det (fun i j : Fin (n + 1) =>
      (Polynomial.derivative^[i.val] (p j)).eval a) ≠ 0 := by
    rw [← polynomialDerivativeMinor_wronskian, polynomialDerivativeMinor_eval] at ha
    exact ha
  obtain ⟨B, _, hj⟩ := polynomialMatrixGauge_exists_identity_jets Fin.val p a hd
  have hmem : ∀ j, polynomialMatrixGauge p B j ∈ V := by
    intro j
    apply V.sum_mem
    intro k _
    rw [← Polynomial.smul_eq_C_mul]
    exact V.smul_mem _ (b₀ k).property
  let ψ : Fin (n + 1) → V := fun j => ⟨polynomialMatrixGauge p B j, hmem j⟩
  have hli : LinearIndependent ℂ ψ :=
    (polynomialTuple_linearIndependent_of_identity_jets Fin.val _ a hj).of_comp V.subtype
  let : Module.Finite ℂ V := Module.Finite.of_basis b₀
  have hc : Fintype.card (Fin (n + 1)) = Module.finrank ℂ V :=
    (Module.finrank_eq_card_basis b₀).symm
  let b := basisOfLinearIndependentOfCardEqFinrank' ψ hli hc
  have hb : (b : Fin (n + 1) → V) = ψ :=
    coe_basisOfLinearIndependentOfCardEqFinrank' ψ hli hc
  refine ⟨b, ?_⟩
  intro i j
  rw [show b j = ψ j from congrFun hb j]
  exact hj i j

/-- Root factorization of the monic Wronskian gives the required nonzero jet
    determinant without a further hypothesis on the chosen basis. -/
theorem polynomialWronskian_eval_ne_zero_of_roots {M n : ℕ}
    {V : Submodule ℂ (Polynomial ℂ)} (b : Module.Basis (Fin (n + 1)) ℂ V)
    (roots : Fin M → ℂ)
    (hW : normalize (FewInflection.polynomialWronskian (fun j => (b j).val)) =
      ∏ i, (Polynomial.X - Polynomial.C (roots i))) (a : ℂ)
    (ha : (∏ i, (a - roots i)) ≠ 0) :
    (FewInflection.polynomialWronskian (fun j => (b j).val)).eval a ≠ 0 := by
  intro hz
  have he := congrArg (fun p : Polynomial ℂ => p.eval a) hW
  rw [normalize_apply, Polynomial.coe_normUnit, Polynomial.eval_mul,
    Polynomial.eval_C, hz, zero_mul] at he
  apply ha
  simpa only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C] using he.symm

end
end ModifiedCartan

#print axioms ModifiedCartan.polynomialBasis_exists_identity_jets