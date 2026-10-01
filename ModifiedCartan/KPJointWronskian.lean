import ModifiedCartan.KPJointEigenvalues

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

def kpJointValuePolynomial (N : ℕ) (χ : YoungDiagram → ℂ) (μ : YoungDiagram) : Polynomial ℂ :=
  ∑ ν : Subpartition (partitionSquare N),
    Polynomial.C ((standardSkewTableauCount ν.val μ : ℂ) /
      ((partitionSize ν.val - partitionSize μ).factorial : ℂ) * χ ν.val) *
        Polynomial.X ^ (partitionSize ν.val - partitionSize μ)

theorem kpJointValuePolynomial_eval (N : ℕ) (χ : YoungDiagram → ℂ) (μ : YoungDiagram) (a : ℂ) :
    (kpJointValuePolynomial N χ μ).eval a =
      ∑ ν : Subpartition (partitionSquare N),
        ((standardSkewTableauCount ν.val μ : ℂ) /
          ((partitionSize ν.val - partitionSize μ).factorial : ℂ) *
            a ^ (partitionSize ν.val - partitionSize μ)) * χ ν.val := by
  simp only [kpJointValuePolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  apply Finset.sum_congr rfl
  intro ν _
  ring

theorem kpJointValuePolynomial_action {A : Type*} [Fintype A] [DecidableEq A]
    (τ : YoungDiagram) (h : Fintype.card A = partitionSize τ) (z : A → ℂ)
    (χ : YoungDiagram → ℂ) (v : YoungSpechtModule τ) (hv : v ∈ kpJointEigenspace τ h z χ)
    (μ : YoungDiagram) (a : ℂ) :
    (spechtRepresentationOn τ h).asAlgebraHom (kpBeta μ z a) v =
      (kpJointValuePolynomial (Fintype.card A) χ μ).eval a • v := by
  rw [kpJointValuePolynomial_eval]
  exact kpJointEigenvector_translation τ h z χ v hv μ a

/-- The candidate Plucker eigenvalues satisfy the exact monic Wronskian
polynomial identity. Decomposability is a separate obligation. -/
theorem kpJointValuePolynomial_bot {A : Type*} [Fintype A] [DecidableEq A]
    (τ : YoungDiagram) (h : Fintype.card A = partitionSize τ) (z : A → ℂ)
    (χ : YoungDiagram → ℂ) (hne : kpJointEigenspace τ h z χ ≠ ⊥) :
    kpJointValuePolynomial (Fintype.card A) χ ⊥ =
      ∏ i : A, (Polynomial.X + Polynomial.C (z i)) := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  apply Polynomial.funext
  intro a
  apply smul_left_injective ℂ hv0
  have he := kpJointValuePolynomial_action τ h z χ v hv ⊥ a
  rw [kpBeta_empty, map_smul, map_one, LinearMap.smul_apply, Module.End.one_apply] at he
  simpa only [Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C] using he.symm

theorem kpJointEigenvalue_top_ne_zero {A : Type*} [Fintype A] [DecidableEq A]
    (τ : YoungDiagram) (h : Fintype.card A = partitionSize τ) (z : A → ℂ)
    (χ : YoungDiagram → ℂ) (hne : kpJointEigenspace τ h z χ ≠ ⊥) : χ τ ≠ 0 := by
  rw [kpJointEigenvalue_top τ h z χ hne]
  apply div_ne_zero
  · exact_mod_cast Nat.factorial_ne_zero (partitionSize τ)
  · rw [← finrank_specht_eq_standardTableauCount]
    letI := spechtRepresentationOn_irreducible τ h
    exact_mod_cast irreducible_finrank_ne_zero (spechtRepresentationOn τ h)

end
end ModifiedCartan


