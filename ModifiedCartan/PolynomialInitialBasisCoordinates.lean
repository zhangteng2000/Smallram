import ModifiedCartan.PolynomialInitialBasisExistence

open scoped Classical BigOperators

namespace ModifiedCartan
noncomputable section

/-- Coordinates in the normalized basis are the actual initial derivatives.
    Auxiliary to manuscript `eq:initial-value-bound`. -/
theorem polynomialBasis_repr_eq_jet {n : ℕ}
    {V : Submodule ℂ (Polynomial ℂ)} (b : Module.Basis (Fin (n + 1)) ℂ V)
    (a : ℂ) (hb : ∀ i j : Fin (n + 1),
      (Polynomial.derivative^[i.val] (b j).val).eval a = if i = j then 1 else 0)
    (h : V) (i : Fin (n + 1)) :
    b.repr h i = (Polynomial.derivative^[i.val] h.val).eval a := by
  have he := congrArg (fun u : V => (Polynomial.derivative^[i.val] u.val).eval a)
    (b.sum_repr h)
  simpa only [Submodule.coe_sum, Submodule.coe_smul, Polynomial.iterate_derivative_sum,
    Polynomial.iterate_derivative_smul, Polynomial.eval_finsetSum, Polynomial.eval_smul,
    hb, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true] using he

/-- Uniqueness of the actual normalized basis in `prop:initial-basis`. -/
theorem polynomialBasis_identity_jets_unique {n : ℕ}
    {V : Submodule ℂ (Polynomial ℂ)} (b c : Module.Basis (Fin (n + 1)) ℂ V)
    (a : ℂ) (hb : ∀ i j : Fin (n + 1),
      (Polynomial.derivative^[i.val] (b j).val).eval a = if i = j then 1 else 0)
    (hc : ∀ i j : Fin (n + 1),
      (Polynomial.derivative^[i.val] (c j).val).eval a = if i = j then 1 else 0) :
    b = c := by
  apply DFunLike.ext
  intro j
  apply b.ext_elem_iff.mpr
  intro i
  rw [polynomialBasis_repr_eq_jet b a hb, polynomialBasis_repr_eq_jet b a hb, hb, hc]

/-- Existence and uniqueness in manuscript `prop:initial-basis`, with only
    the actual Wronskian roots and the off-root center as assumptions. -/
theorem polynomialBasis_existsUnique_identity_jets {M n : ℕ}
    {V : Submodule ℂ (Polynomial ℂ)} (b₀ : Module.Basis (Fin (n + 1)) ℂ V)
    (roots : Fin M → ℂ)
    (hW : normalize (FewInflection.polynomialWronskian (fun j => (b₀ j).val)) =
      ∏ i, (Polynomial.X - Polynomial.C (roots i))) (a : ℂ)
    (ha : (∏ i, (a - roots i)) ≠ 0) :
    ∃! b : Module.Basis (Fin (n + 1)) ℂ V, ∀ i j : Fin (n + 1),
      (Polynomial.derivative^[i.val] (b j).val).eval a = if i = j then 1 else 0 := by
  obtain ⟨b, hb⟩ := polynomialBasis_exists_identity_jets b₀ a
    (polynomialWronskian_eval_ne_zero_of_roots b₀ roots hW a ha)
  exact ⟨b, hb, fun c hc => polynomialBasis_identity_jets_unique c b a hc hb⟩

end
end ModifiedCartan

#print axioms ModifiedCartan.polynomialBasis_existsUnique_identity_jets