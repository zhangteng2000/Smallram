import ModifiedCartan.PolynomialCoefficientSpace

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem polynomialCoefficientSpace_ne_bot {B : Type*}
    (p : Polynomial (MvPolynomial B ℂ)) (hp : p ≠ 0) : polynomialCoefficientSpace p ≠ ⊥ := by
  intro hz
  apply hp
  ext k d
  let L : MvPolynomial B ℂ →ₗ[ℂ] ℂ := MvPolynomial.lcoeff ℂ d
  have hq : polynomialLinearCoefficientMap L p ∈ polynomialCoefficientSpace p := ⟨L, rfl⟩
  rw [hz] at hq
  have hh := congrArg (fun q : Polynomial ℂ => q.coeff k) hq
  rw [polynomialLinearCoefficientMap_coeff, Polynomial.coeff_zero] at hh
  change MvPolynomial.coeff d (p.coeff k) = 0 at hh
  simpa only [Polynomial.coeff_zero, MvPolynomial.coeff_zero] using hh

theorem columnPartition_zero_eq_bot : columnPartition 0 = ⊥ := by
  apply YoungDiagram.ext
  simp [columnPartition]

theorem kpJointDifferentialCoefficient_zero {A : Type*} [Fintype A]
    (τ : YoungDiagram) (hτ : Fintype.card A = partitionSize τ) (z : A → ℂ)
    (χ : YoungDiagram → ℂ) (hne : kpJointEigenspace τ hτ z χ ≠ ⊥) :
    kpJointDifferentialCoefficient (Fintype.card A) χ 0 =
      ∏ i : A, (Polynomial.X + Polynomial.C (z i)) := by
  simp only [kpJointDifferentialCoefficient, pow_zero, map_one, one_mul, columnPartition_zero_eq_bot]
  exact kpJointValuePolynomial_bot τ hτ z χ hne

theorem kpJointDifferentialCoefficient_zero_ne_zero {A : Type*} [Fintype A]
    (τ : YoungDiagram) (hτ : Fintype.card A = partitionSize τ) (z : A → ℂ)
    (χ : YoungDiagram → ℂ) (hne : kpJointEigenspace τ hτ z χ ≠ ⊥) :
    kpJointDifferentialCoefficient (Fintype.card A) χ 0 ≠ 0 := by
  rw [kpJointDifferentialCoefficient_zero τ hτ z χ hne]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _ hz
  have h := congrArg (fun p : Polynomial ℂ => p.coeff 1) hz
  simp at h

/-- A concrete finite-dimensional, nonzero coefficient space of actual
    polynomial solutions. Its upper dimension bound is the differential order;
    equality and decomposability are proved separately.
    Auxiliary to manuscript `lem:KP-correspondence`. -/
theorem kpJointCoefficientSpace_finrank_le {A : Type*} [Fintype A]
    {m : ℕ} (hm : Fintype.card A = m + 1)
    (τ : YoungDiagram) (hτ : Fintype.card A = partitionSize τ) (z : A → ℂ)
    (χ : YoungDiagram → ℂ) (hne : kpJointEigenspace τ hτ z χ ≠ ⊥) :
    Module.finrank ℂ (polynomialCoefficientSpace
      (MvPolynomial.finSuccEquiv ℂ m
        (finitePartitionDividedPolynomial (m + 1) (Fintype.card A) χ))) ≤ Fintype.card A := by
  exact polynomialCoefficientSpace_finrank_le _ _
    (kpJointDifferentialCoefficient_zero_ne_zero τ hτ z χ hne) _
    (kpJointDividedPolynomial_differential_eq_zero hm τ hτ z χ hne)

theorem kpJointCoefficientSpace_ne_bot {A : Type*} [Fintype A]
    {m : ℕ} (hm : Fintype.card A = m + 1)
    (τ : YoungDiagram) (hτ : Fintype.card A = partitionSize τ) (z : A → ℂ)
    (χ : YoungDiagram → ℂ) (hne : kpJointEigenspace τ hτ z χ ≠ ⊥) :
    polynomialCoefficientSpace (MvPolynomial.finSuccEquiv ℂ m
      (finitePartitionDividedPolynomial (m + 1) (Fintype.card A) χ)) ≠ ⊥ := by
  apply polynomialCoefficientSpace_ne_bot
  intro hz
  have hP : finitePartitionDividedPolynomial (m + 1) (Fintype.card A) χ = 0 := by
    apply (MvPolynomial.finSuccEquiv ℂ m).injective
    simpa only [map_zero] using hz
  have hn : finitePartitionDividedPolynomial (m + 1) (Fintype.card A) χ ≠ 0 := by
    rw [← hm]
    exact kpJointDividedPolynomial_ne_zero τ hτ z χ hne
  exact hn hP

end
end ModifiedCartan

#print axioms ModifiedCartan.kpJointCoefficientSpace_finrank_le
#print axioms ModifiedCartan.kpJointCoefficientSpace_ne_bot
