import ModifiedCartan.PointInitialValue

open scoped Topology BigOperators
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

theorem initial_polynomial_sum_le {n : ℕ} {s : ℝ} {z : ℂ}
    (hs : 1 ≤ s) (hz : ‖z‖ ≤ 1) :
    (∑ i : Index n, (s * ‖z‖) ^ i.val / (i.val.factorial : ℝ)) ≤ (n + 1) * s ^ n := by
  have hs0 : 0 ≤ s := zero_le_one.trans hs
  have hb (i : Index n) : (s * ‖z‖) ^ i.val / (i.val.factorial : ℝ) ≤ s ^ n := by
    have hfac : (1 : ℝ) ≤ (i.val.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos i.val
    calc
      _ ≤ (s * ‖z‖) ^ i.val := div_le_self (by positivity) hfac
      _ ≤ s ^ i.val := by gcongr; simpa only [mul_one] using mul_le_mul_of_nonneg_left hz hs0
      _ ≤ s ^ n := pow_le_pow_right₀ hs (by have hi := i.isLt; omega)
  calc
    _ ≤ ∑ _i : Index n, s ^ n := Finset.sum_le_sum (fun i _ => hb i)
    _ = _ := by simp [Index, FewInflection.Index]

theorem polynomial_matrix_initial_value_coarse_bound {M n : ℕ} {s : ℝ} (hs : 1 ≤ s)
    (p : Index n → Polynomial ℂ) (B : Matrix (Index n) (Index n) ℂ) (roots : Fin M → ℂ)
    (hW : normalize (FewInflection.polynomialWronskian p) =
      ∏ i, (Polynomial.X - Polynomial.C (roots i)))
    (a : ℂ) (ha : (FewInflection.polynomialWronskian p).eval a ≠ 0)
    (j : Index n) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖(polynomialMatrixGauge p B j).eval (a + z)‖ ≤
      scaledJetLength n s (fun w => (polynomialMatrixGauge p B j).eval w) a *
        ((n + 1) * s ^ n) * Real.exp (‖z‖ * ∑ i, ‖a - roots i‖⁻¹) := by
  apply (polynomial_matrix_initial_value_bound (zero_lt_one.trans_le hs) p B roots hW a ha j z).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (initial_polynomial_sum_le hs hz) (euclideanNorm_nonneg _)) (Real.exp_pos _).le

end ModifiedCartan
#print axioms ModifiedCartan.polynomial_matrix_initial_value_coarse_bound
