import ModifiedCartan.NormalizedMinorTranslation

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem partitionMinorOrders_succ_zero (n : ℕ) (μ : YoungDiagram) :
    partitionMinorOrders (n + 1) μ 0 = μ.rowLen (n + 1) := by
  simp only [partitionMinorOrders, Fin.val_zero, Nat.sub_zero, zero_add]

theorem partitionMinorOrders_succ_succ {n : ℕ} (μ : YoungDiagram) (i : Fin (n + 1)) :
    partitionMinorOrders (n + 1) μ i.succ = partitionMinorOrders n μ i + 1 := by
  have he : n + 1 - (i.val + 1) = n - i.val := by omega
  simp only [partitionMinorOrders, Fin.val_succ, he]
  omega

theorem polynomialDerivativeMinor_cons_constant {N : ℕ} (d : Fin N → ℕ)
    (p : Fin N → Polynomial ℂ) (c : ℂ) :
    polynomialDerivativeMinor (Fin.cons 0 (fun i => d i + 1)) (Fin.cons (Polynomial.C c) p) =
      Polynomial.C c * polynomialDerivativeMinor d (fun j => (p j).derivative) := by
  have hc (k : ℕ) : Polynomial.derivative^[k + 1] (Polynomial.C c) = 0 :=
    Polynomial.iterate_derivative_C (Nat.succ_pos k)
  rw [polynomialDerivativeMinor, Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp only [Matrix.of_apply, Fin.cons_zero, Fin.cons_succ, Fin.val_zero, pow_zero,
    one_mul, Function.iterate_zero_apply, hc, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  congr 1


/-- Removing a constant first column differentiates the remaining columns and
    preserves every partition minor up to that constant, including excess-row
    partitions. Auxiliary to dimension transfer in `lem:KP-correspondence`. -/
theorem partitionPolynomialMinor_cons_constant {n : ℕ} (μ : YoungDiagram)
    (p : Fin (n + 1) → Polynomial ℂ) (c : ℂ) :
    partitionPolynomialMinor μ (Fin.cons (Polynomial.C c) p) =
      Polynomial.C c * partitionPolynomialMinor μ (fun j => (p j).derivative) := by
  by_cases hs : PartitionFits n μ
  · have hb : PartitionFits (n + 1) μ := hs.rowLen_eq_zero (by omega)
    rw [partitionPolynomialMinor_of_fits hb, partitionPolynomialMinor_of_fits hs]
    have he : partitionMinorOrders (n + 1) μ = Fin.cons 0
        (fun i : Fin (n + 1) => partitionMinorOrders n μ i + 1) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [PartitionFits, Fin.cons_zero, partitionMinorOrders_succ_zero] using hs
      · simpa only [Fin.cons_succ] using partitionMinorOrders_succ_succ μ j
    rw [he]
    exact polynomialDerivativeMinor_cons_constant _ p c
  · rw [partitionPolynomialMinor_of_not_fits hs, mul_zero]
    by_cases hb : PartitionFits (n + 1) μ
    · rw [partitionPolynomialMinor_of_fits hb, polynomialDerivativeMinor]
      apply Matrix.det_eq_zero_of_column_eq_zero (0 : Fin (n + 2))
      intro i
      simp only [Matrix.of_apply, Fin.cons_zero]
      apply Polynomial.iterate_derivative_C
      have h0 : 0 < partitionMinorOrders (n + 1) μ 0 := by
        rw [partitionMinorOrders_succ_zero]
        exact Nat.pos_of_ne_zero hs
      exact h0.trans_le ((partitionMinorOrders_strictMono (n + 1) μ).monotone (Fin.zero_le i))
    · exact partitionPolynomialMinor_of_not_fits hb _

theorem normalizedPartitionMinor_cons_constant {n : ℕ} (τ μ : YoungDiagram)
    (p : Fin (n + 1) → Polynomial ℂ) (c : ℂ) (hc : c ≠ 0) (a : ℂ) :
    normalizedPartitionMinor τ (Fin.cons (Polynomial.C c) p) μ a =
      normalizedPartitionMinor τ (fun j => (p j).derivative) μ a := by
  rw [normalizedPartitionMinor, partitionPolynomialMinor_cons_constant,
    partitionPolynomialMinor_cons_constant]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  rw [mul_comm c ((partitionPolynomialMinor μ (fun j => (p j).derivative)).eval a),
    mul_comm c ((partitionPolynomialMinor τ (fun j => (p j).derivative)).eval a),
    ← mul_assoc, mul_div_mul_right _ _ hc]
  rfl

end
end ModifiedCartan

#print axioms ModifiedCartan.partitionPolynomialMinor_cons_constant