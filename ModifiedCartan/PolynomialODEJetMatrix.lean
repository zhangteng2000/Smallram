import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.Block

open scoped Classical BigOperators

namespace ModifiedCartan
noncomputable section

variable {R : Type*} [CommRing R]

/-- The coefficient equations of a differential operator are triangular on
    monomials. Auxiliary to Bethe identification in `lem:KP-correspondence`. -/
theorem polynomialODE_monomial_coeff_zero {N r k : ℕ}
    (c : Fin (N + 1) → Polynomial R) (hk : N + r < k) :
    (∑ i : Fin (N + 1), c i * Polynomial.derivative^[i.val]
      (Polynomial.X ^ k)).coeff r = 0 := by
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro i _
  rw [Polynomial.iterate_derivative_X_pow_eq_C_mul,
    mul_left_comm (c i) (Polynomial.C _), Polynomial.coeff_C_mul,
    Polynomial.coeff_mul_X_pow', ite_eq_right (show ¬ k - i.val ≤ r by omega), mul_zero]

theorem polynomialODE_monomial_diagonal {N k : ℕ}
    (c : Fin (N + 1) → Polynomial R) (hk : N ≤ k) :
    (∑ i : Fin (N + 1), c i * Polynomial.derivative^[i.val]
      (Polynomial.X ^ k)).coeff (k - N) =
      (c (Fin.last N)).coeff 0 * (k.descFactorial N : R) := by
  rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single (Fin.last N)]
  · rw [Polynomial.iterate_derivative_X_pow_eq_C_mul,
      mul_left_comm (c (Fin.last N)) (Polynomial.C _), Polynomial.coeff_C_mul,
      Polynomial.coeff_mul_X_pow', ite_eq_left (show k - (Fin.last N).val ≤ k - N by rfl)]
    change (k.descFactorial N : R) * (c (Fin.last N)).coeff (k - N - (k - N)) = _
    rw [Nat.sub_self, mul_comm]
  · intro i _ hi
    have hiN : i.val < N := by
      have hn : i.val ≠ N := fun h => hi (Fin.ext h)
      omega
    rw [Polynomial.iterate_derivative_X_pow_eq_C_mul,
      mul_left_comm (c i) (Polynomial.C _), Polynomial.coeff_C_mul,
      Polynomial.coeff_mul_X_pow', ite_eq_right (show ¬ k - i.val ≤ k - N by omega), mul_zero]
  · simp

/-- Initial coefficients followed by differential equations on the truncated
    coefficient vector. It is lower triangular, without assumptions on roots. -/
def polynomialODEJetMatrix (N D : ℕ) (c : Fin (N + 1) → Polynomial R) :
    Matrix (Fin D) (Fin D) R := fun r k =>
  if r.val < N then if r = k then 1 else 0 else
    (∑ i : Fin (N + 1), c i * Polynomial.derivative^[i.val]
      (Polynomial.X ^ k.val)).coeff (r.val - N)

theorem polynomialODEJetMatrix_lowerTriangular (N D : ℕ)
    (c : Fin (N + 1) → Polynomial R) : (polynomialODEJetMatrix N D c).IsLowerTriangular := by
  intro r k hkr
  change r < k at hkr
  change (if r.val < N then if r = k then 1 else 0 else _) = 0
  by_cases hr : r.val < N
  · rw [ite_eq_left hr, ite_eq_right (ne_of_lt hkr)]
  · rw [ite_eq_right hr]
    apply polynomialODE_monomial_coeff_zero
    have h : r.val < k.val := hkr
    omega

theorem polynomialODEJetMatrix_diagonal (N D : ℕ)
    (c : Fin (N + 1) → Polynomial R) (r : Fin D) :
    polynomialODEJetMatrix N D c r r =
      if r.val < N then 1 else (c (Fin.last N)).coeff 0 * (r.val.descFactorial N : R) := by
  unfold polynomialODEJetMatrix
  by_cases hr : r.val < N
  · rw [ite_eq_left hr, ite_eq_left hr, ite_eq_left rfl]
  · rw [ite_eq_right hr, ite_eq_right hr]
    exact polynomialODE_monomial_diagonal c (by omega)

theorem polynomialODEJetMatrix_det (N D : ℕ)
    (c : Fin (N + 1) → Polynomial R) :
    (polynomialODEJetMatrix N D c).det =
      ∏ r : Fin D, if r.val < N then 1 else
        (c (Fin.last N)).coeff 0 * (r.val.descFactorial N : R) := by
  rw [Matrix.det_of_isLowerTriangular _ (polynomialODEJetMatrix_lowerTriangular N D c)]
  apply Finset.prod_congr rfl
  intro r _
  exact polynomialODEJetMatrix_diagonal N D c r

end
end ModifiedCartan

#print axioms ModifiedCartan.polynomialODEJetMatrix_det