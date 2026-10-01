import FewInflection.EntireTaylor

open scoped Topology BigOperators
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

theorem entire_taylorPolynomial_coeff (f : ℂ → ℂ) (N k : ℕ) :
    (FewInflection.taylorPolynomial f 0 N).coeff k =
      if k < N then (k.factorial : ℂ)⁻¹ * iteratedDeriv k f 0 else 0 := by
  classical
  simp only [FewInflection.taylorPolynomial, Polynomial.C_0, sub_zero,
    Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  simp [Finset.mem_range]

/-- Exact preservation of initial derivatives by Taylor truncation,
as used in Step 3 of LaTeX `lem:entire-majorant`. -/
theorem entire_taylorPolynomial_iteratedDeriv_zero (f : ℂ → ℂ) {N k : ℕ}
    (hk : k < N) :
    iteratedDeriv k (fun z => (FewInflection.taylorPolynomial f 0 N).eval z) 0 =
      iteratedDeriv k f 0 := by
  rw [FewInflection.iteratedDeriv_polynomial_eval_zero, entire_taylorPolynomial_coeff,
    if_pos hk, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero k), one_mul]

theorem wronskian_zero_of_initial_jets {n : ℕ} {y : FewInflection.Index n → ℂ → ℂ}
    (hy : ∀ i j : FewInflection.Index n, iteratedDeriv i.val (y j) 0 = if i = j then 1 else 0) :
    FewInflection.wronskian n y 0 = 1 := by
  have hmat : (fun i j : FewInflection.Index n => iteratedDeriv i.val (y j) 0) =
      (1 : Matrix (FewInflection.Index n) (FewInflection.Index n) ℂ) := by
    funext i j
    rw [hy i j, Matrix.one_apply]
  rw [FewInflection.wronskian, hmat, Matrix.det_one]

/-- The W_N(0)=1 part of LaTeX `eq:WN-growth`. -/
theorem entire_taylorPolynomial_wronskian_zero {n N : ℕ}
    {y : FewInflection.Index n → ℂ → ℂ} (hN : n < N)
    (hy : ∀ i j : FewInflection.Index n, iteratedDeriv i.val (y j) 0 = if i = j then 1 else 0) :
    FewInflection.wronskian n (fun j z => (FewInflection.taylorPolynomial (y j) 0 N).eval z) 0 = 1 := by
  apply wronskian_zero_of_initial_jets
  intro i j
  rw [entire_taylorPolynomial_iteratedDeriv_zero (y j) (by have := i.isLt; omega)]
  exact hy i j

end ModifiedCartan
#print axioms ModifiedCartan.entire_taylorPolynomial_wronskian_zero
