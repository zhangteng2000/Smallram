import ModifiedCartan.PolynomialMinorBasisChange
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

def polynomialMatrixGauge {N : ℕ} (p : Fin N → Polynomial ℂ)
    (B : Matrix (Fin N) (Fin N) ℂ) (j : Fin N) : Polynomial ℂ :=
  ∑ k, Polynomial.C (B k j) * p k

theorem polynomialMatrixGauge_jet {N : ℕ} (p : Fin N → Polynomial ℂ)
    (B : Matrix (Fin N) (Fin N) ℂ) (j : Fin N) (k : ℕ) (a : ℂ) :
    (Polynomial.derivative^[k] (polynomialMatrixGauge p B j)).eval a =
      ∑ l, B l j * (Polynomial.derivative^[k] (p l)).eval a := by
  simp only [polynomialMatrixGauge, Polynomial.iterate_derivative_sum,
    Polynomial.iterate_derivative_C_mul, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C]

theorem partitionPolynomialMinor_matrixGauge {n : ℕ} (μ : YoungDiagram)
    (p : Fin (n + 1) → Polynomial ℂ) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    partitionPolynomialMinor μ (polynomialMatrixGauge p B) =
      partitionPolynomialMinor μ p * Polynomial.C B.det := by
  by_cases hf : PartitionFits n μ
  · rw [partitionPolynomialMinor_of_fits hf, partitionPolynomialMinor_of_fits hf]
    exact polynomialDerivativeMinor_matrixGauge _ p B
  · rw [partitionPolynomialMinor_of_not_fits hf, partitionPolynomialMinor_of_not_fits hf,
      zero_mul]

/-- Inverting the nonzero jet matrix provides an actual polynomial basis change.
    Auxiliary to manuscript `lem:KP-correspondence`. -/
theorem polynomialMatrixGauge_exists_identity_jets {N : ℕ}
    (d : Fin N → ℕ) (p : Fin N → Polynomial ℂ) (a : ℂ)
    (hd : Matrix.det (fun i j : Fin N => (Polynomial.derivative^[d i] (p j)).eval a) ≠ 0) :
    ∃ B : Matrix (Fin N) (Fin N) ℂ, B.det ≠ 0 ∧ ∀ i j,
      (Polynomial.derivative^[d i] (polynomialMatrixGauge p B j)).eval a =
        if i = j then 1 else 0 := by
  let M : Matrix (Fin N) (Fin N) ℂ := fun i j =>
    (Polynomial.derivative^[d i] (p j)).eval a
  have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr hd
  have hM := Matrix.mul_nonsing_inv M hu
  refine ⟨M⁻¹, ?_, ?_⟩
  · have ht := congrArg Matrix.det hM
    rw [Matrix.det_mul, Matrix.det_one] at ht
    intro hz
    rw [hz, mul_zero] at ht
    exact zero_ne_one ht
  · intro i j
    rw [polynomialMatrixGauge_jet]
    have h := congrFun (congrFun hM i) j
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro k _
    exact mul_comm _ _

theorem polynomialTuple_linearIndependent_of_identity_jets {N : ℕ}
    (d : Fin N → ℕ) (p : Fin N → Polynomial ℂ) (a : ℂ)
    (hp : ∀ i j, (Polynomial.derivative^[d i] (p j)).eval a = if i = j then 1 else 0) :
    LinearIndependent ℂ p := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have h := congrArg (fun q : Polynomial ℂ => (Polynomial.derivative^[d i] q).eval a) hc
  simpa only [Polynomial.iterate_derivative_sum, Polynomial.iterate_derivative_smul,
    Polynomial.eval_finsetSum, Polynomial.eval_smul, Polynomial.iterate_derivative_zero,
    Polynomial.eval_zero, hp, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true] using h

end
end ModifiedCartan

#print axioms ModifiedCartan.polynomialMatrixGauge_exists_identity_jets