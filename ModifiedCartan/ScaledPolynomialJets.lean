import ModifiedCartan.UnitaryNorm
import ModifiedCartan.PolynomialJetMatrixGauge
import FewInflection.PolynomialGauge

open scoped Topology BigOperators Matrix
open Matrix
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

/-- The actual initial matrix J_n(a) in `lem:basis-at-point`. -/
def scaledPolynomialJetMatrix {n : ℕ} (s : ℝ) (p : Index n → Polynomial ℂ) (a : ℂ) :
    Matrix (Index n) (Index n) ℂ :=
  fun i j => ((s : ℂ)⁻¹) ^ i.val * iteratedDeriv i.val (fun z => (p j).eval z) a

theorem scaledPolynomialJetMatrix_det {n : ℕ} (s : ℝ) (p : Index n → Polynomial ℂ) (a : ℂ) :
    (scaledPolynomialJetMatrix s p a).det =
      ((s : ℂ)⁻¹) ^ (∑ i : Index n, i.val) * (FewInflection.polynomialWronskian p).eval a := by
  have hh := Matrix.det_mul_column (fun i : Index n => ((s : ℂ)⁻¹) ^ i.val)
    (Matrix.of (fun i j : Index n => iteratedDeriv i.val (fun z => (p j).eval z) a))
  simpa only [scaledPolynomialJetMatrix, Matrix.of_apply, Finset.prod_pow_eq_pow_sum,
    FewInflection.polynomialWronskian_eval, FewInflection.derivativeMinor] using! hh

theorem norm_scaledPolynomialJetMatrix_det {n : ℕ} {s : ℝ} (hs : 0 < s)
    (p : Index n → Polynomial ℂ) (a : ℂ) :
    ‖(scaledPolynomialJetMatrix s p a).det‖ =
      s⁻¹ ^ (∑ i : Index n, i.val) * ‖(FewInflection.polynomialWronskian p).eval a‖ := by
  rw [scaledPolynomialJetMatrix_det, norm_mul, norm_pow, norm_inv,
    Complex.norm_real, Real.norm_of_nonneg hs.le]

theorem scaledPolynomialJetMatrix_gauge {n : ℕ} (s : ℝ)
    (p : Index n → Polynomial ℂ) (B : Matrix (Index n) (Index n) ℂ) (a : ℂ) :
    scaledPolynomialJetMatrix s (polynomialMatrixGauge p B) a =
      scaledPolynomialJetMatrix s p a * B := by
  ext i j
  simp only [scaledPolynomialJetMatrix, FewInflection.iteratedDeriv_polynomial_eval,
    polynomialMatrixGauge_jet, Matrix.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem polynomialMatrixGauge_eval_vecMul {n : ℕ} (p : Index n → Polynomial ℂ)
    (B : Matrix (Index n) (Index n) ℂ) (z : ℂ) :
    (fun j => (polynomialMatrixGauge p B j).eval z) = (fun j => (p j).eval z) ᵥ* B := by
  ext j
  simp only [polynomialMatrixGauge, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Matrix.vecMul, dotProduct, mul_comm]

theorem polynomialMatrixGauge_unitary_norm {n : ℕ} (p : Index n → Polynomial ℂ)
    (V : Matrix.unitaryGroup (Index n) ℂ) (z : ℂ) :
    euclideanNorm (fun j => (polynomialMatrixGauge p (V : Matrix (Index n) (Index n) ℂ) j).eval z) =
      euclideanNorm (fun j => (p j).eval z) := by
  rw [polynomialMatrixGauge_eval_vecMul, euclideanNorm_vecMul_unitary]

theorem polynomialMatrixGauge_unitary_wronskian_norm {n : ℕ} (p : Index n → Polynomial ℂ)
    (V : Matrix.unitaryGroup (Index n) ℂ) (z : ℂ) :
    ‖(FewInflection.polynomialWronskian
      (polynomialMatrixGauge p (V : Matrix (Index n) (Index n) ℂ))).eval z‖ =
      ‖(FewInflection.polynomialWronskian p).eval z‖ := by
  have he := FewInflection.polynomialWronskian_matrixGauge_eval
    (V : Matrix (Index n) (Index n) ℂ) p z
  change (FewInflection.polynomialWronskian
    (polynomialMatrixGauge p (V : Matrix (Index n) (Index n) ℂ))).eval z = _ at he
  rw [he, norm_mul, norm_det_unitary, one_mul]

/-- Positive singular lengths for the actual scaled polynomial jet matrix,
including the determinant product formula of `lem:basis-at-point`. -/
theorem exists_polynomial_unitary_jet_lengths {n : ℕ} {s : ℝ} (hs : 0 < s)
    (p : Index n → Polynomial ℂ) (a : ℂ)
    (hW : (FewInflection.polynomialWronskian p).eval a ≠ 0) :
    ∃ V : Matrix.unitaryGroup (Index n) ℂ, ∃ σ : Index n → ℝ,
      (∀ j, 0 < σ j) ∧
      (∀ j, σ j = euclideanNorm (fun i =>
        scaledPolynomialJetMatrix s (polynomialMatrixGauge p (V : Matrix (Index n) (Index n) ℂ)) a i j)) ∧
      (∏ j, σ j) = s⁻¹ ^ (∑ i : Index n, i.val) *
        ‖(FewInflection.polynomialWronskian p).eval a‖ := by
  have hJ : (scaledPolynomialJetMatrix s p a).det ≠ 0 := by
    rw [scaledPolynomialJetMatrix_det]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero (Complex.ofReal_ne_zero.mpr hs.ne'))) hW
  obtain ⟨V, σ, hσ, hnorm, _, hprod⟩ := exists_unitary_positive_column_norms
    (scaledPolynomialJetMatrix s p a) hJ
  refine ⟨V, σ, hσ, ?_, ?_⟩
  · simpa only [scaledPolynomialJetMatrix_gauge] using hnorm
  · simpa only [norm_scaledPolynomialJetMatrix_det hs] using hprod

end
end ModifiedCartan
#print axioms ModifiedCartan.exists_polynomial_unitary_jet_lengths
#print axioms ModifiedCartan.polynomialMatrixGauge_unitary_wronskian_norm
