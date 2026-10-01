import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace ModifiedCartan

def positiveGeometricSum {R : Type*} [Semiring R] (n : ℕ) (x : R) : R :=
  ∑ r : Fin n, x ^ (r.val + 1)

theorem positiveGeometricSum_eq {R : Type*} [Semiring R] (n : ℕ) (x : R) :
    positiveGeometricSum n x = (∑ r ∈ Finset.range n, x ^ r) * x := by
  simp only [positiveGeometricSum, pow_succ, ← Finset.sum_mul]
  rw [Fin.sum_univ_eq_sum_range]

theorem one_sub_mul_positiveGeometricSum {R : Type*} [Ring R] (n : ℕ) (x : R) :
    (1 - x) * positiveGeometricSum n x = x - x ^ (n + 1) := by
  rw [positiveGeometricSum_eq, ← mul_assoc, mul_neg_geom_sum, sub_mul, one_mul, ← pow_succ]

end ModifiedCartan

