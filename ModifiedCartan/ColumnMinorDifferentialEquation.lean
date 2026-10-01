import ModifiedCartan.ColumnMinorCramer

open scoped Classical BigOperators

namespace ModifiedCartan
noncomputable section

/-- Cramer's identity with no invertibility assumption. -/
theorem matrix_rowReplacement_sum {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] (M : Matrix ι ι R) (row : ι → R) (j : ι) :
    (∑ i, (M.updateRow i row).det * M i j) = M.det * row j := by
  have h := congrFun (Matrix.mulVec_cramer M.transpose row) j
  simpa only [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    Matrix.cramer_transpose_apply, Matrix.det_transpose, Pi.smul_apply,
    smul_eq_mul, mul_comm] using h

/-- The signed column minors annihilate each polynomial of the tuple.
    This cleared polynomial identity is valid even at Wronskian zeros.
    Auxiliary to manuscript `lem:KP-correspondence`. -/
theorem polynomial_columnMinor_differential_identity {n : ℕ}
    (p : Fin (n + 1) → Polynomial ℂ) (j : Fin (n + 1)) :
    FewInflection.polynomialWronskian p * Polynomial.derivative^[n + 1] (p j) +
      ∑ i : Fin (n + 1),
        Polynomial.C ((-1 : ℂ) ^ (n + 1 - i.val)) *
          partitionPolynomialMinor (columnPartition (n + 1 - i.val)) p *
            Polynomial.derivative^[i.val] (p j) = 0 := by
  apply Polynomial.funext
  intro a
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_finsetSum,
    Polynomial.eval_C, Polynomial.eval_zero]
  rw [← polynomialDerivativeMinor_wronskian, polynomialDerivativeMinor_eval]
  let M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
    fun i l => (Polynomial.derivative^[i.val] (p l)).eval a
  let row : Fin (n + 1) → ℂ := fun l =>
    -(Polynomial.derivative^[n + 1] (p l)).eval a
  have hn (i : Fin (n + 1)) :
      (-1 : ℂ) ^ (n + 1 - i.val) *
        (partitionPolynomialMinor (columnPartition (n + 1 - i.val)) p).eval a =
        (M.updateRow i row).det := by
    rw [← fundamentalNumerator_eq_columnMinor]
    simp only [FewInflection.fundamentalNumerator, FewInflection.iteratedDeriv_polynomial_eval]
    rfl
  change M.det * (Polynomial.derivative^[n + 1] (p j)).eval a +
      ∑ i : Fin (n + 1), ((-1 : ℂ) ^ (n + 1 - i.val) *
        (partitionPolynomialMinor (columnPartition (n + 1 - i.val)) p).eval a) *
          M i j = 0
  simp_rw [hn]
  rw [matrix_rowReplacement_sum]
  dsimp only [row]
  ring

end
end ModifiedCartan

#print axioms ModifiedCartan.polynomial_columnMinor_differential_identity
