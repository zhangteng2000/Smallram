import ModifiedCartan.KPJointDecomposability
import ModifiedCartan.PolynomialAlternantMinors
import ModifiedCartan.KPJointValueNormalization
import ModifiedCartan.NormalizedMinorTranslation

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

/-- Actual joint eigenvalues give an independent polynomial tuple with exactly
    the prescribed derivative minors at every center. The dimension here is
    the parameter cardinality; ambient-dimension transfer and Schubert shape
    are subsequent obligations in manuscript `lem:KP-correspondence`. -/
theorem kpJointPolynomialTuple_exists {A : Type*} [Fintype A]
    {m : ℕ} (hm : Fintype.card A = m + 1)
    (τ : YoungDiagram) (hτ : Fintype.card A = partitionSize τ) (z : A → ℂ)
    (χ : YoungDiagram → ℂ) (hne : kpJointEigenspace τ hτ z χ ≠ ⊥) :
    ∃ (p : Fin (m + 1) → Polynomial ℂ) (c : ℂ),
      LinearIndependent ℂ p ∧ c ≠ 0 ∧ ∀ μ a,
      (kpJointValuePolynomial (Fintype.card A) χ μ).eval a =
        c * (partitionPolynomialMinor μ p).eval a := by
  obtain ⟨p, c, hp, hc, he⟩ := kpJointDividedPolynomial_decomposable hm τ hτ z χ hne
  refine ⟨fun j => p j.rev, c, hp.comp (Fin.revPerm : Equiv.Perm (Fin (m + 1)))
    (Fin.revPerm.injective), hc, ?_⟩
  intro μ a
  by_cases hf : PartitionFits m μ
  · exact finitePartitionDividedPolynomial_representation_minor hm.le χ p c he μ hf a
  · have ht : PartitionFits m τ := (partitionFits_iff_height_le τ).mpr
      ((partition_colLen_le_size τ 0).trans_eq (hτ.symm.trans hm))
    have hn : ¬ μ ≤ τ := fun h => hf (ht.of_le h)
    rw [kpJointValuePolynomial_eq_zero_of_not_le τ hτ z χ hne μ hn,
      partitionPolynomialMinor_of_not_fits hf, Polynomial.eval_zero, mul_zero]

theorem kpJointPolynomialTuple_top_ne_zero {A : Type*} [Fintype A] {m : ℕ}
    (τ : YoungDiagram) (hτ : Fintype.card A = partitionSize τ) (z : A → ℂ)
    (χ : YoungDiagram → ℂ) (hne : kpJointEigenspace τ hτ z χ ≠ ⊥)
    (p : Fin (m + 1) → Polynomial ℂ) (c : ℂ)
    (hp : ∀ μ a, (kpJointValuePolynomial (Fintype.card A) χ μ).eval a =
      c * (partitionPolynomialMinor μ p).eval a) (a : ℂ) :
    (partitionPolynomialMinor τ p).eval a ≠ 0 := by
  intro hz
  have he := hp τ a
  rw [kpJointValuePolynomial_top τ hτ z χ hne, Polynomial.eval_C,
    hz, mul_zero, ← kpJointEigenvalue_top τ hτ z χ hne] at he
  exact kpJointEigenvalue_top_ne_zero τ hτ z χ hne he

/-- Exact normalization recovered from the constructed determinants. -/
theorem kpJointPolynomialTuple_normalized {A : Type*} [Fintype A] {m : ℕ}
    (τ : YoungDiagram) (hτ : Fintype.card A = partitionSize τ) (z : A → ℂ)
    (χ : YoungDiagram → ℂ) (hne : kpJointEigenspace τ hτ z χ ≠ ⊥)
    (p : Fin (m + 1) → Polynomial ℂ) (c : ℂ)
    (hp : ∀ μ a, (kpJointValuePolynomial (Fintype.card A) χ μ).eval a =
      c * (partitionPolynomialMinor μ p).eval a) (μ : YoungDiagram) (a : ℂ) :
    normalizedPartitionMinor τ p μ a =
      (kpJointValuePolynomial (Fintype.card A) χ μ).eval a := by
  have ht := hp τ a
  rw [kpJointValuePolynomial_top τ hτ z χ hne, Polynomial.eval_C] at ht
  have hn := kpJointPolynomialTuple_top_ne_zero τ hτ z χ hne p c hp a
  rw [normalizedPartitionMinor, ht, hp μ a]
  field_simp

end
end ModifiedCartan

#print axioms ModifiedCartan.kpJointPolynomialTuple_exists
#print axioms ModifiedCartan.kpJointPolynomialTuple_normalized