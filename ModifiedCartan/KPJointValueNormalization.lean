import ModifiedCartan.KPJointWronskian

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem kpJointValuePolynomial_eval_zero {A : Type*} [Fintype A]
    (τ : YoungDiagram) (hτ : Fintype.card A = partitionSize τ) (z : A → ℂ)
    (χ : YoungDiagram → ℂ) (hne : kpJointEigenspace τ hτ z χ ≠ ⊥) (μ : YoungDiagram) :
    (kpJointValuePolynomial (Fintype.card A) χ μ).eval 0 = χ μ := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  apply smul_left_injective ℂ hv0
  exact (kpJointValuePolynomial_action τ hτ z χ v hv μ 0).symm.trans
    ((mem_kpJointEigenspace_iff τ hτ z χ v).mp hv μ)

/-- The top eigenvalue polynomial has exactly the paper's constant normalization.
    Auxiliary to `eq:normalized-Plucker-coordinates` and `lem:KP-correspondence`. -/
theorem kpJointValuePolynomial_top {A : Type*} [Fintype A]
    (τ : YoungDiagram) (hτ : Fintype.card A = partitionSize τ) (z : A → ℂ)
    (χ : YoungDiagram → ℂ) (hne : kpJointEigenspace τ hτ z χ ≠ ⊥) :
    kpJointValuePolynomial (Fintype.card A) χ τ =
      Polynomial.C ((partitionSize τ).factorial / (standardSkewTableauCount τ ⊥ : ℂ)) := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  apply Polynomial.funext
  intro a
  apply smul_left_injective ℂ hv0
  have he := kpJointValuePolynomial_action τ hτ z χ v hv τ a
  rw [specht_kpBeta_full_size τ hτ z a, LinearMap.smul_apply, Module.End.one_apply] at he
  simpa only [Polynomial.eval_C] using he.symm

theorem kpJointValuePolynomial_eq_zero_of_not_le {A : Type*} [Fintype A]
    (τ : YoungDiagram) (hτ : Fintype.card A = partitionSize τ) (z : A → ℂ)
    (χ : YoungDiagram → ℂ) (hne : kpJointEigenspace τ hτ z χ ≠ ⊥)
    (μ : YoungDiagram) (hμ : ¬ μ ≤ τ) :
    kpJointValuePolynomial (Fintype.card A) χ μ = 0 := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  apply Polynomial.funext
  intro a
  apply smul_left_injective ℂ hv0
  have he := kpJointValuePolynomial_action τ hτ z χ v hv μ a
  rw [specht_kpBeta_eq_zero_of_not_le μ τ hτ hμ z a, LinearMap.zero_apply] at he
  simpa only [Polynomial.eval_zero, zero_smul] using he.symm

end
end ModifiedCartan

#print axioms ModifiedCartan.kpJointValuePolynomial_top