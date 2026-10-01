import ModifiedCartan.ColumnPartitionMinorOrders

open scoped Classical BigOperators

namespace ModifiedCartan
noncomputable section

/-- Exact determinant sign obtained by moving the replaced row to the end. -/
theorem columnPartitionMinor_eval_eq_signed_update {n : ℕ}
    (p : Fin (n + 1) → Polynomial ℂ) (i : Fin (n + 1)) (a : ℂ) :
    (partitionPolynomialMinor (columnPartition (n + 1 - i.val)) p).eval a =
      (-1 : ℂ) ^ (n - i.val) *
        Matrix.det (Function.update
          (fun k j : Fin (n + 1) => (Polynomial.derivative^[k.val] (p j)).eval a) i
          (fun j => (Polynomial.derivative^[n + 1] (p j)).eval a)) := by
  let σ := Fin.cycleIcc i (Fin.last n)
  let U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := Function.update
    (fun k j : Fin (n + 1) => (Polynomial.derivative^[k.val] (p j)).eval a) i
    (fun j => (Polynomial.derivative^[n + 1] (p j)).eval a)
  have hm : U.submatrix σ id = Matrix.of (fun k j : Fin (n + 1) =>
      (Polynomial.derivative^[partitionMinorOrders n (columnPartition (n + 1 - i.val)) k]
        (p j)).eval a) := by
    funext k j
    change U (σ k) j =
      (Polynomial.derivative^[partitionMinorOrders n (columnPartition (n + 1 - i.val)) k]
        (p j)).eval a
    rw [← columnPartition_order_cycle i k]
    change U (σ k) j = (Polynomial.derivative^[Function.update
      (fun l : Fin (n + 1) => l.val) i (n + 1) (σ k)] (p j)).eval a
    by_cases hk : σ k = i
    · simp only [U, hk, Function.update_self]
    · simp only [U, Function.update_of_ne hk]
  have hs : ((Equiv.Perm.sign σ : ℤ) : ℂ) = (-1 : ℂ) ^ (n - i.val) := by
    rw [Fin.sign_cycleIcc_of_le (Fin.le_last i)]
    simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
      Int.cast_pow, Int.cast_neg, Int.cast_one, Fin.val_last]
  rw [partitionPolynomialMinor_of_fits (columnPartition_fits (Nat.sub_le _ _)),
    polynomialDerivativeMinor_eval, ← hm, Matrix.det_permute, hs]

/-- Cramer's numerator is the signed single-column derivative minor,
    with the paper's index q=n+1-i. -/
theorem fundamentalNumerator_eq_columnMinor {n : ℕ}
    (p : Fin (n + 1) → Polynomial ℂ) (i : Fin (n + 1)) (a : ℂ) :
    FewInflection.fundamentalNumerator n (fun j z => (p j).eval z) i a =
      (-1 : ℂ) ^ (n + 1 - i.val) *
        (partitionPolynomialMinor (columnPartition (n + 1 - i.val)) p).eval a := by
  rw [FewInflection.fundamentalNumerator]
  simp only [FewInflection.iteratedDeriv_polynomial_eval]
  let U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
    fun k j => (Polynomial.derivative^[k.val] (p j)).eval a
  let row := fun j => (Polynomial.derivative^[n + 1] (p j)).eval a
  have hrow : (fun j => -(Polynomial.derivative^[n + 1] (p j)).eval a) =
      (-1 : ℂ) • row := by
    funext j
    simp [row]
  rw [hrow]
  change (U.updateRow i ((-1 : ℂ) • row)).det = _
  rw [Matrix.det_updateRow_smul, columnPartitionMinor_eval_eq_signed_update]
  change (-1 : ℂ) * (U.updateRow i row).det =
    (-1 : ℂ) ^ (n + 1 - i.val) * ((-1 : ℂ) ^ (n - i.val) * (U.updateRow i row).det)
  have hi : n + 1 - i.val = (n - i.val) + 1 := by have := i.isLt; omega
  have hs : (-1 : ℂ) ^ (n - i.val) * (-1 : ℂ) ^ (n - i.val) = 1 := by
    rw [← mul_pow]
    simp
  rw [hi, pow_succ]
  symm
  calc
    _ = (-1 : ℂ) * ((-1 : ℂ) ^ (n - i.val) * (-1 : ℂ) ^ (n - i.val)) *
        (U.updateRow i row).det := by ring
    _ = _ := by rw [hs, mul_one]

/-- Fundamental coefficients are column-minor ratios at all points under
    Lean's total division convention, hence also as meromorphic functions. -/
theorem fundamentalCoefficients_eq_columnMinor {n : ℕ}
    (p : Fin (n + 1) → Polynomial ℂ) (i : Fin (n + 1)) (a : ℂ) :
    FewInflection.fundamentalCoefficients n (fun j z => (p j).eval z) a i =
      (-1 : ℂ) ^ (n + 1 - i.val) *
        ((partitionPolynomialMinor (columnPartition (n + 1 - i.val)) p).eval a /
          (FewInflection.polynomialWronskian p).eval a) := by
  rw [FewInflection.fundamentalCoefficients_eq_quotient,
    fundamentalNumerator_eq_columnMinor, mul_div_assoc,
    FewInflection.polynomialWronskian_eval,
    FewInflection.derivativeMinor_wronskian_special_case]

end
end ModifiedCartan

#print axioms ModifiedCartan.fundamentalCoefficients_eq_columnMinor