import ModifiedCartan.PartitionMinorSupport
import Mathlib.LinearAlgebra.Matrix.Basis

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem polynomialDerivativeMinor_matrixGauge {n : ℕ}
    (orders : Fin (n + 1) → ℕ) (p : Fin (n + 1) → Polynomial ℂ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    polynomialDerivativeMinor orders (fun j => ∑ k, Polynomial.C (A k j) * p k) =
      polynomialDerivativeMinor orders p * Polynomial.C A.det := by
  let M : Matrix (Fin (n + 1)) (Fin (n + 1)) (Polynomial ℂ) :=
    Matrix.of fun i j => Polynomial.derivative^[orders i] (p j)
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) (Polynomial ℂ) :=
    Matrix.of fun i j => Polynomial.C (A i j)
  have hmat : (Matrix.of fun i j => Polynomial.derivative^[orders i]
      (∑ k, Polynomial.C (A k j) * p k)) = M * B := by
    funext i j
    simp only [Matrix.of_apply, Polynomial.iterate_derivative_sum,
      Polynomial.iterate_derivative_C_mul, Matrix.mul_apply, M, B]
    apply Finset.sum_congr rfl
    intro k _
    exact mul_comm _ _
  have hdet : B.det = Polynomial.C A.det := (RingHom.map_det Polynomial.C A).symm
  rw [polynomialDerivativeMinor, hmat, Matrix.det_mul, hdet]
  rfl

theorem polynomialBasis_toMatrix_det_ne_zero {n : ℕ}
    {V : Submodule ℂ (Polynomial ℂ)}
    (b c : Module.Basis (Fin (n + 1)) ℂ V) : (b.toMatrix c).det ≠ 0 := by
  have hm := b.toMatrix_mul_toMatrix_flip c
  have hd := congrArg Matrix.det hm
  rw [Matrix.det_mul, Matrix.det_one] at hd
  intro hz
  rw [hz, zero_mul] at hd
  exact zero_ne_one hd

theorem polynomialBasis_expansion {n : ℕ} {V : Submodule ℂ (Polynomial ℂ)}
    (b c : Module.Basis (Fin (n + 1)) ℂ V) (j : Fin (n + 1)) :
    (c j).val = ∑ k, Polynomial.C (b.toMatrix c k j) * (b k).val := by
  have he := congrArg (fun v : V => v.val) (b.sum_repr (c j))
  simpa only [Module.Basis.toMatrix_apply, Submodule.coe_sum, Submodule.coe_smul,
    Polynomial.smul_eq_C_mul] using he.symm

theorem partitionPolynomialMinor_basis_change {n : ℕ} {V : Submodule ℂ (Polynomial ℂ)}
    (b c : Module.Basis (Fin (n + 1)) ℂ V) (μ : YoungDiagram) :
    partitionPolynomialMinor μ (fun j => (c j).val) =
      partitionPolynomialMinor μ (fun j => (b j).val) * Polynomial.C (b.toMatrix c).det := by
  by_cases hμ : PartitionFits n μ
  · rw [partitionPolynomialMinor_of_fits hμ, partitionPolynomialMinor_of_fits hμ]
    have hp : (fun j => (c j).val) =
        fun j => ∑ k, Polynomial.C (b.toMatrix c k j) * (b k).val :=
      funext (polynomialBasis_expansion b c)
    rw [hp]
    exact polynomialDerivativeMinor_matrixGauge _ _ _
  · rw [partitionPolynomialMinor_of_not_fits hμ, partitionPolynomialMinor_of_not_fits hμ,
      zero_mul]

end
end ModifiedCartan


