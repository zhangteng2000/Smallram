import ModifiedCartan.PartitionMinorSupport
import Mathlib.LinearAlgebra.Matrix.Block

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem iterate_derivative_eq_C_factorial_coeff_of_natDegree_le
    (p : Polynomial ℂ) (d : ℕ) (hp : p.natDegree ≤ d) :
    Polynomial.derivative^[d] p = Polynomial.C ((d.factorial : ℂ) * p.coeff d) := by
  have hd := Polynomial.natDegree_iterate_derivative p d
  have hz : (Polynomial.derivative^[d] p).natDegree ≤ 0 := by omega
  rw [Polynomial.eq_C_of_natDegree_le_zero hz, Polynomial.coeff_iterate_derivative]
  simp [Nat.descFactorial_self, nsmul_eq_mul]

/-- The top Schubert coordinate is independent of the evaluation point. -/
theorem partitionPolynomialMinor_top_eq_C {n : ℕ} {ω : YoungDiagram}
    (hω : PartitionFits n ω) (p : Fin (n + 1) → Polynomial ℂ)
    (hp : ∀ j, (p j).natDegree ≤ partitionMinorOrders n ω j) :
    partitionPolynomialMinor ω p = Polynomial.C
      (∏ j : Fin (n + 1), ((partitionMinorOrders n ω j).factorial : ℂ) *
        (p j).coeff (partitionMinorOrders n ω j)) := by
  let A : Matrix (Fin (n + 1)) (Fin (n + 1)) (Polynomial ℂ) :=
    Matrix.of fun i j => Polynomial.derivative^[partitionMinorOrders n ω i] (p j)
  have hA : A.IsUpperTriangular := by
    intro i j hij
    exact Polynomial.iterate_derivative_eq_zero
      ((hp j).trans_lt (partitionMinorOrders_strictMono n ω hij))
  rw [partitionPolynomialMinor_of_fits hω]
  change A.det = _
  rw [Matrix.det_of_isUpperTriangular hA, map_prod]
  apply Finset.prod_congr rfl
  intro j _
  exact iterate_derivative_eq_C_factorial_coeff_of_natDegree_le (p j) _ (hp j)

theorem partitionPolynomialMinor_top_eval_ne_zero {n : ℕ} {ω : YoungDiagram}
    (hω : PartitionFits n ω) (p : Fin (n + 1) → Polynomial ℂ)
    (hp0 : ∀ j, p j ≠ 0) (hp : ∀ j, (p j).natDegree = partitionMinorOrders n ω j)
    (a : ℂ) : (partitionPolynomialMinor ω p).eval a ≠ 0 := by
  rw [partitionPolynomialMinor_top_eq_C hω p (fun j => (hp j).le), Polynomial.eval_C]
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  apply mul_ne_zero
  · exact_mod_cast Nat.factorial_ne_zero (partitionMinorOrders n ω j)
  · rw [← hp j, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr (hp0 j)

end
end ModifiedCartan


