import ModifiedCartan.KPJointCoefficientDimension
import ModifiedCartan.AlternatingDualDeterminant

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem finitePartitionDividedPolynomial_basis_representation {m N : ℕ}
    (χ : YoungDiagram → ℂ) (hP : finitePartitionDividedPolynomial (m + 1) N χ ≠ 0)
    (hdim : Module.finrank ℂ (polynomialCoefficientSpace (MvPolynomial.finSuccEquiv ℂ m
      (finitePartitionDividedPolynomial (m + 1) N χ))) = m + 1) :
    ∃ (b : Module.Basis (Fin (m + 1)) ℂ (polynomialCoefficientSpace
      (MvPolynomial.finSuccEquiv ℂ m (finitePartitionDividedPolynomial (m + 1) N χ))))
      (c : ℂ), c ≠ 0 ∧ finitePartitionDividedPolynomial (m + 1) N χ =
        MvPolynomial.C c * polynomialAlternant (fun j => (b j).val) := by
  let V := polynomialCoefficientSpace (MvPolynomial.finSuccEquiv ℂ m
    (finitePartitionDividedPolynomial (m + 1) N χ))
  let b := Module.finBasisOfFinrankEq ℂ V hdim
  obtain ⟨c, hc, hF⟩ := alternatingDual_eq_scalar_det V b
    (finitePartitionAlternatingDualForm (m + 1) N χ)
    (fun v hv => finitePartitionAlternatingDualForm_annihilator χ v hv)
    (finitePartitionAlternatingDualForm_ne_zero _ _ χ hP)
  refine ⟨b, c, hc, ?_⟩
  apply MvPolynomial.ext
  intro d
  rw [MvPolynomial.coeff_C_mul, polynomialAlternant_coeff,
    ← finitePartitionAlternatingDualForm_coeff]
  simpa only [Polynomial.lcoeff_apply] using hF (fun i => Polynomial.lcoeff ℂ (d i))

set_option maxHeartbeats 800000 in
/-- Every actual nonzero KP joint eigenspace with a nonempty parameter index
    yields a tuple of independent polynomials whose determinant has exactly
    the prescribed divided alternating polynomial, up to a nonzero scalar.
    This proves decomposability; shape and normalized coordinates are separate
    subsequent obligations for manuscript `lem:KP-correspondence`. -/
theorem kpJointDividedPolynomial_decomposable {A : Type*} [Fintype A]
    {m : ℕ} (hm : Fintype.card A = m + 1)
    (τ : YoungDiagram) (hτ : Fintype.card A = partitionSize τ) (z : A → ℂ)
    (χ : YoungDiagram → ℂ) (hne : kpJointEigenspace τ hτ z χ ≠ ⊥) :
    ∃ (p : Fin (m + 1) → Polynomial ℂ) (c : ℂ),
      LinearIndependent ℂ p ∧ c ≠ 0 ∧
      finitePartitionDividedPolynomial (m + 1) (Fintype.card A) χ =
        MvPolynomial.C c * polynomialAlternant p := by
  have hP : finitePartitionDividedPolynomial (m + 1) (Fintype.card A) χ ≠ 0 := by
    rw [← hm]
    exact kpJointDividedPolynomial_ne_zero τ hτ z χ hne
  obtain ⟨b, c, hc, he⟩ := finitePartitionDividedPolynomial_basis_representation χ hP
    ((kpJointCoefficientSpace_finrank_eq hm τ hτ z χ hne).trans hm)
  refine ⟨fun j => (b j).val, c, ?_, hc, he⟩
  exact b.linearIndependent.map' (polynomialCoefficientSpace (MvPolynomial.finSuccEquiv ℂ m
    (finitePartitionDividedPolynomial (m + 1) (Fintype.card A) χ))).subtype
    (Submodule.ker_subtype _)

end
end ModifiedCartan

#print axioms ModifiedCartan.kpJointDividedPolynomial_decomposable
