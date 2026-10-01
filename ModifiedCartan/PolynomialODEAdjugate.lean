import ModifiedCartan.PolynomialODEJetMatrix
import Mathlib.Algebra.Polynomial.OfFn

open scoped Classical BigOperators

namespace ModifiedCartan
noncomputable section

variable {R : Type*} [CommRing R]

/-- The finite coefficient matrix acts exactly as the differential operator
    together with the initial-coefficient conditions. -/
theorem polynomialODEJetMatrix_mulVec {N D : ℕ}
    (c : Fin (N + 1) → Polynomial R) (p : Polynomial R) (hp : p.natDegree < D)
    (r : Fin D) :
    (polynomialODEJetMatrix N D c).mulVec (fun k => p.coeff k.val) r =
      if r.val < N then p.coeff r.val else
        (∑ i : Fin (N + 1), c i * Polynomial.derivative^[i.val] p).coeff (r.val - N) := by
  have he : p = ∑ k : Fin D, Polynomial.C (p.coeff k.val) * Polynomial.X ^ k.val := by
    exact (p.as_sum_range_C_mul_X_pow' hp).trans
      (Fin.sum_univ_eq_sum_range (fun k : ℕ => Polynomial.C (p.coeff k) * Polynomial.X ^ k) D).symm
  by_cases hr : r.val < N
  · simp [Matrix.mulVec, dotProduct, polynomialODEJetMatrix, hr]
  · rw [ite_eq_right hr]
    change (∑ k : Fin D, polynomialODEJetMatrix N D c r k * p.coeff k.val) = _
    simp only [polynomialODEJetMatrix, ite_eq_right hr]
    have hh : (∑ i : Fin (N + 1), c i * Polynomial.derivative^[i.val] p) =
        ∑ k : Fin D, Polynomial.C (p.coeff k.val) *
          ∑ i : Fin (N + 1), c i * Polynomial.derivative^[i.val] (Polynomial.X ^ k.val) := by
      calc
        _ = ∑ i : Fin (N + 1), ∑ k : Fin D,
            Polynomial.C (p.coeff k.val) *
              (c i * Polynomial.derivative^[i.val] (Polynomial.X ^ k.val)) := by
          apply Finset.sum_congr rfl
          intro i _
          calc
            _ = c i * Polynomial.derivative^[i.val]
                (∑ k : Fin D, Polynomial.C (p.coeff k.val) * Polynomial.X ^ k.val) :=
              congrArg (fun q => c i * Polynomial.derivative^[i.val] q) he
            _ = _ := by
              simp only [Polynomial.iterate_derivative_sum, Polynomial.iterate_derivative_C_mul,
                Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k _
              ring
        _ = _ := by rw [Finset.sum_comm]; simp only [Finset.mul_sum]
    rw [hh, Polynomial.finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro k _
    rw [Polynomial.coeff_C_mul, mul_comm]

/-- The adjugate reconstructs the coefficient vector of every actual
    polynomial solution, multiplied by the matrix determinant. -/
theorem polynomialODEJetMatrix_adjugate_solution {N D : ℕ}
    (c : Fin (N + 1) → Polynomial R) (p : Polynomial R) (hp : p.natDegree < D)
    (hsol : (∑ i : Fin (N + 1), c i * Polynomial.derivative^[i.val] p) = 0) :
    (polynomialODEJetMatrix N D c).adjugate.mulVec
        (fun r : Fin D => if r.val < N then p.coeff r.val else 0) =
      (polynomialODEJetMatrix N D c).det • (fun r : Fin D => p.coeff r.val) := by
  have he : (polynomialODEJetMatrix N D c).mulVec (fun r => p.coeff r.val) =
      fun r : Fin D => if r.val < N then p.coeff r.val else 0 := by
    funext r
    rw [polynomialODEJetMatrix_mulVec c p hp, hsol, Polynomial.coeff_zero]
  rw [← he, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]

/-- Polynomial form of the adjugate reconstruction, requiring only the
    actual differential equation and the finite degree bound. -/
theorem polynomialODEJetMatrix_ofFn_adjugate_solution {N D : ℕ}
    (c : Fin (N + 1) → Polynomial R) (p : Polynomial R) (hp : p.natDegree < D)
    (hsol : (∑ i : Fin (N + 1), c i * Polynomial.derivative^[i.val] p) = 0) :
    Polynomial.ofFn D ((polynomialODEJetMatrix N D c).adjugate.mulVec
        (fun r : Fin D => if r.val < N then p.coeff r.val else 0)) =
      (polynomialODEJetMatrix N D c).det • p := by
  rw [polynomialODEJetMatrix_adjugate_solution c p hp hsol, map_smul]
  congr 1
  exact Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt hp

end
end ModifiedCartan

#print axioms ModifiedCartan.polynomialODEJetMatrix_ofFn_adjugate_solution