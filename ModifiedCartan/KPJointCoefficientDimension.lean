import ModifiedCartan.PartitionAlternatingDualForm
import ModifiedCartan.AlternatingDualDescent
import ModifiedCartan.KPJointCoefficientSpace

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem alternatingMap_arity_le_finrank {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] {N : ℕ} (F : W [⋀^Fin N]→ₗ[ℂ] ℂ) (hne : F ≠ 0) :
    N ≤ Module.finrank ℂ W := by
  obtain ⟨v, hv⟩ : ∃ v, F v ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hne (AlternatingMap.ext hn)
  have hlin : LinearIndependent ℂ v := by
    by_contra hn
    exact hv (F.map_linearDependent v hn)
  simpa only [Fintype.card_fin] using hlin.fintype_card_le_finrank

theorem finitePartitionCoefficientSpace_finrank_ge {m N : ℕ} (χ : YoungDiagram → ℂ)
    (hP : finitePartitionDividedPolynomial (m + 1) N χ ≠ 0) :
    m + 1 ≤ Module.finrank ℂ (polynomialCoefficientSpace (MvPolynomial.finSuccEquiv ℂ m
      (finitePartitionDividedPolynomial (m + 1) N χ))) := by
  let V := polynomialCoefficientSpace (MvPolynomial.finSuccEquiv ℂ m
    (finitePartitionDividedPolynomial (m + 1) N χ))
  let F := finitePartitionAlternatingDualForm (m + 1) N χ
  have hf : ∀ v, (∀ p ∈ V, v 0 p = 0) → F v = 0 :=
    fun v hv => finitePartitionAlternatingDualForm_annihilator χ v hv
  have hF : F ≠ 0 := finitePartitionAlternatingDualForm_ne_zero _ _ χ hP
  have h := alternatingMap_arity_le_finrank (F.compLinearMap (Subspace.dualLift V))
    (alternatingDual_descent_ne_zero V F hf hF)
  simpa only [Subspace.dual_finrank_eq] using h

/-- The concrete coefficient solution space has exactly the differential
    order as its dimension. This proves the missing equality, using the
    nonzero alternating form and its descent to the space's dual.
    Auxiliary to manuscript `lem:KP-correspondence`. -/
theorem kpJointCoefficientSpace_finrank_eq {A : Type*} [Fintype A]
    {m : ℕ} (hm : Fintype.card A = m + 1)
    (τ : YoungDiagram) (hτ : Fintype.card A = partitionSize τ) (z : A → ℂ)
    (χ : YoungDiagram → ℂ) (hne : kpJointEigenspace τ hτ z χ ≠ ⊥) :
    Module.finrank ℂ (polynomialCoefficientSpace (MvPolynomial.finSuccEquiv ℂ m
      (finitePartitionDividedPolynomial (m + 1) (Fintype.card A) χ))) = Fintype.card A := by
  apply le_antisymm (kpJointCoefficientSpace_finrank_le hm τ hτ z χ hne)
  have hP : finitePartitionDividedPolynomial (m + 1) (Fintype.card A) χ ≠ 0 := by
    rw [← hm]
    exact kpJointDividedPolynomial_ne_zero τ hτ z χ hne
  exact hm.le.trans (finitePartitionCoefficientSpace_finrank_ge χ hP)

end
end ModifiedCartan

#print axioms ModifiedCartan.kpJointCoefficientSpace_finrank_eq
