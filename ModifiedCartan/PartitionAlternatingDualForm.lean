import ModifiedCartan.PolynomialTensorContraction
import ModifiedCartan.KPDividedPolynomialTranslation

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

def polynomialTupleDualMap {m : ℕ} (p : Fin m → Polynomial ℂ) :
    Module.Dual ℂ (Polynomial ℂ) →ₗ[ℂ] (Fin m → ℂ) where
  toFun v j := v (p j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def polynomialAlternatingDualForm {m : ℕ} (p : Fin m → Polynomial ℂ) :
    (Module.Dual ℂ (Polynomial ℂ)) [⋀^Fin m]→ₗ[ℂ] ℂ :=
  Matrix.detRowAlternating.compLinearMap (polynomialTupleDualMap p)

theorem polynomialAlternatingDualForm_apply {m : ℕ} (p : Fin m → Polynomial ℂ)
    (v : Fin m → Module.Dual ℂ (Polynomial ℂ)) :
    polynomialAlternatingDualForm p v = Matrix.det (fun i j : Fin m => v i (p j)) := rfl

def finitePartitionAlternatingDualForm (m N : ℕ) (χ : YoungDiagram → ℂ) :
    (Module.Dual ℂ (Polynomial ℂ)) [⋀^Fin m]→ₗ[ℂ] ℂ :=
  ∑ μ : Subpartition (partitionSquare N), χ μ.val • polynomialAlternatingDualForm
    (fun j => complexDividedPowerPolynomial (partitionAlternantExponent m μ.val j))

theorem finitePartitionAlternatingDualForm_apply (m N : ℕ) (χ : YoungDiagram → ℂ)
    (v : Fin m → Module.Dual ℂ (Polynomial ℂ)) :
    finitePartitionAlternatingDualForm m N χ v =
      polynomialTensorFunctional v (finitePartitionDividedPolynomial m N χ) := by
  rw [finitePartitionDividedPolynomial_eq_sum, map_sum]
  simp only [polynomialTensorFunctional_C_mul, finiteDividedAlternant_eq_det]
  have hμ (μ : Subpartition (partitionSquare N)) :
      polynomialTensorFunctional v
        (Matrix.det (fun i j : Fin m => Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X i)
          (complexDividedPowerPolynomial (partitionAlternantExponent m μ.val j)))) =
      polynomialAlternatingDualForm
        (fun j => complexDividedPowerPolynomial (partitionAlternantExponent m μ.val j)) v :=
    polynomialTensorFunctional_alternant v _
  simp_rw [hμ]
  have hs (s : Finset (Subpartition (partitionSquare N))) :
      (∑ μ ∈ s, χ μ.val • polynomialAlternatingDualForm
        (fun j => complexDividedPowerPolynomial (partitionAlternantExponent m μ.val j))) v =
      ∑ μ ∈ s, χ μ.val * polynomialAlternatingDualForm
        (fun j => complexDividedPowerPolynomial (partitionAlternantExponent m μ.val j)) v := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.sum_empty, AlternatingMap.zero_apply]
    | @insert μ s hμ ih =>
      rw [Finset.sum_insert hμ, Finset.sum_insert hμ, AlternatingMap.add_apply,
        AlternatingMap.smul_apply, ih]
      rfl
  exact hs Finset.univ

theorem finitePartitionAlternatingDualForm_coeff (m N : ℕ) (χ : YoungDiagram → ℂ)
    (d : Fin m →₀ ℕ) :
    finitePartitionAlternatingDualForm m N χ (fun i => Polynomial.lcoeff ℂ (d i)) =
      MvPolynomial.coeff d (finitePartitionDividedPolynomial m N χ) := by
  rw [finitePartitionAlternatingDualForm_apply, polynomialTensorFunctional_coeff]

theorem finitePartitionAlternatingDualForm_ne_zero (m N : ℕ) (χ : YoungDiagram → ℂ)
    (hP : finitePartitionDividedPolynomial m N χ ≠ 0) :
    finitePartitionAlternatingDualForm m N χ ≠ 0 := by
  intro hz
  apply hP
  ext d
  rw [MvPolynomial.coeff_zero, ← finitePartitionAlternatingDualForm_coeff, hz]
  rfl

/-- The actual alternating form vanishes when its first functional annihilates
    the concrete scalar coefficient space. This is the descent condition used
    for decomposition, auxiliary to manuscript `lem:KP-correspondence`. -/
theorem finitePartitionAlternatingDualForm_annihilator {m N : ℕ} (χ : YoungDiagram → ℂ)
    (v : Fin (m + 1) → Module.Dual ℂ (Polynomial ℂ))
    (hv : ∀ p ∈ polynomialCoefficientSpace (MvPolynomial.finSuccEquiv ℂ m
      (finitePartitionDividedPolynomial (m + 1) N χ)), v 0 p = 0) :
    finitePartitionAlternatingDualForm (m + 1) N χ v = 0 := by
  rw [finitePartitionAlternatingDualForm_apply]
  exact polynomialTensorFunctional_zero_of_annihilates_first v _ hv

end
end ModifiedCartan

#print axioms ModifiedCartan.finitePartitionAlternatingDualForm_annihilator
