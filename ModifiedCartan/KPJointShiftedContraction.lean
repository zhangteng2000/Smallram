import ModifiedCartan.KPDividedPolynomialTranslation

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem kpJointEigenspace_le_shifted {A : Type*} [Fintype A]
    (τ : YoungDiagram) (hτ : Fintype.card A = partitionSize τ) (z : A → ℂ)
    (χ : YoungDiagram → ℂ) (a : ℂ) :
    kpJointEigenspace τ hτ z χ ≤
      kpJointEigenspace τ hτ (fun i => z i + a)
        (fun μ => (kpJointValuePolynomial (Fintype.card A) χ μ).eval a) := by
  intro v hv
  apply (mem_kpJointEigenspace_iff τ hτ _ _ v).mpr
  intro μ
  rw [← kpBeta_parameter_shift μ z 0 a, zero_add]
  exact kpJointValuePolynomial_action τ hτ z χ v hv μ a

theorem kpJointEigenspace_shifted_ne_bot {A : Type*} [Fintype A]
    (τ : YoungDiagram) (hτ : Fintype.card A = partitionSize τ) (z : A → ℂ)
    (χ : YoungDiagram → ℂ) (hne : kpJointEigenspace τ hτ z χ ≠ ⊥) (a : ℂ) :
    kpJointEigenspace τ hτ (fun i => z i + a)
      (fun μ => (kpJointValuePolynomial (Fintype.card A) χ μ).eval a) ≠ ⊥ := by
  intro hz
  apply hne
  apply le_antisymm _ bot_le
  simpa only [hz] using kpJointEigenspace_le_shifted τ hτ z χ a

/-- Single-column contraction at every complex center, for the actual
    translated alternating polynomial. Auxiliary to `lem:KP-correspondence`.
    Repeated entries of the parameter tuple are allowed. -/
theorem kpJointDividedPolynomial_translated_contraction {A : Type*} [Fintype A]
    {m : ℕ} (hm : Fintype.card A = m + 1)
    (τ : YoungDiagram) (hτ : Fintype.card A = partitionSize τ) (z : A → ℂ)
    (χ : YoungDiagram → ℂ) (hne : kpJointEigenspace τ hτ z χ ≠ ⊥) (a : ℂ) :
    (∑ k ∈ Finset.range (Fintype.card A + 1),
      MvPolynomial.C (((-1 : ℂ) ^ k *
        (kpJointValuePolynomial (Fintype.card A) χ (columnPartition k)).eval a) *
          ((m + 1 - k).factorial : ℂ)) *
        (MvPolynomial.finSuccEquiv ℂ m
          (mvPolynomialTranslate (Fin (m + 1)) a
            (finitePartitionDividedPolynomial (m + 1) (Fintype.card A) χ))).coeff
              (m + 1 - k)) = 0 := by
  have h := kpJointDividedPolynomial_first_contraction hm τ hτ
    (fun i => z i + a)
    (fun μ => (kpJointValuePolynomial (Fintype.card A) χ μ).eval a)
    (kpJointEigenspace_shifted_ne_bot τ hτ z χ hne a)
  rw [finitePartitionDividedPolynomial_translation hm.le χ a]
  exact h

end
end ModifiedCartan

#print axioms ModifiedCartan.kpJointDividedPolynomial_translated_contraction
