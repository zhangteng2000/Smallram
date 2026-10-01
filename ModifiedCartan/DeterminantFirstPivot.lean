import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

/-- Finite elimination used in the Schur identification, auxiliary to
    paper `lem:KP-correspondence`. -/
def firstPivotElimination {K : Type*} [Field K] {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  Matrix.of (Fin.cons (Pi.single 0 1)
    (fun i => Fin.cons (-(M i.succ 0 / M 0 0)) (fun j => if i = j then 1 else 0)))

theorem firstPivotElimination_det {K : Type*} [Field K] {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    (firstPivotElimination M).det = 1 := by
  rw [Matrix.det_succ_row_zero, Finset.sum_eq_single 0]
  · have h : (firstPivotElimination M).submatrix Fin.succ Fin.succ = 1 := by
      ext i j
      simp [firstPivotElimination, Matrix.one_apply]
    simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
    change 1 * ((firstPivotElimination M).submatrix Fin.succ Fin.succ).det = 1
    rw [h, Matrix.det_one, mul_one]
  · intro j _ hj
    simp [firstPivotElimination, Pi.single_eq_of_ne hj]
  · simp

theorem firstPivotElimination_mul_zero {K : Type*} [Field K] {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (j : Fin (n + 1)) :
    (firstPivotElimination M * M) 0 j = M 0 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_succ, firstPivotElimination]

theorem firstPivotElimination_mul_succ {K : Type*} [Field K] {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (i : Fin n) (j : Fin (n + 1)) :
    (firstPivotElimination M * M) i.succ j =
      M i.succ j - (M i.succ 0 / M 0 0) * M 0 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_succ, firstPivotElimination,
    ite_mul, sub_eq_add_neg, add_comm]

theorem det_first_pivot {K : Type*} [Field K] {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (h : M 0 0 ≠ 0) :
    M.det = M 0 0 * Matrix.det (fun i j : Fin n =>
      M i.succ j.succ - (M i.succ 0 / M 0 0) * M 0 j.succ) := by
  have hd : M.det = (firstPivotElimination M * M).det := by
    rw [Matrix.det_mul, firstPivotElimination_det, one_mul]
  rw [hd, Matrix.det_succ_column_zero, Finset.sum_eq_single 0]
  · simp only [Fin.val_zero, pow_zero, one_mul, firstPivotElimination_mul_zero,
      Fin.succAbove_zero]
    congr 1
    congr 1
    ext i j
    exact firstPivotElimination_mul_succ M i j.succ
  · intro i _ hi
    obtain ⟨i, rfl⟩ := i.eq_succ_of_ne_zero hi
    rw [firstPivotElimination_mul_succ, div_mul_cancel₀ _ h, sub_self]
    simp
  · simp

end
end ModifiedCartan

#print axioms ModifiedCartan.det_first_pivot
