import ModifiedCartan.ZeroSharpProduct

open scoped Topology BigOperators
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

noncomputable def zeroSharpLogMajorant (r : ℝ) : ℝ :=
  ∑' j : ℕ, Real.log (1 + Real.exp (-((j + 1 : ℕ) : ℝ)) * r)

theorem zeroSharp_real_coeff_summable :
    Summable (fun j : ℕ => Real.exp (-((j + 1 : ℕ) : ℝ))) := by
  simpa only [Complex.norm_exp, Complex.neg_re, Complex.natCast_re]
    using zeroSharp_coeff_summable

theorem zeroSharp_log_majorant_summable (r : ℝ) :
    Summable (fun j : ℕ => Real.log (1 + Real.exp (-((j + 1 : ℕ) : ℝ)) * r)) :=
  Real.summable_log_one_add_of_summable (zeroSharp_real_coeff_summable.mul_right r)

theorem zeroSharp_norm_le_exp_majorant {r : ℝ} (hr : 0 ≤ r) {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖zeroSharpFunction z‖ ≤ Real.exp (zeroSharpLogMajorant r) := by
  rw [zeroSharpLogMajorant, Real.rexp_tsum_eq_tprod (fun _ => by positivity)
    (zeroSharp_log_majorant_summable r)]
  apply le_of_tendsto_of_tendsto (zeroSharp_factors_multipliable z).hasProd.norm
    (Real.multipliable_one_add_of_summable (zeroSharp_real_coeff_summable.mul_right r)).hasProd
  apply Eventually.of_forall
  intro S
  apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
  intro j _
  calc
    ‖1 + Complex.exp (-((j + 1 : ℕ) : ℂ)) * z‖ ≤
        1 + Real.exp (-((j + 1 : ℕ) : ℝ)) * ‖z‖ := by
      simpa only [norm_one, norm_mul, Complex.norm_exp, Complex.neg_re, Complex.natCast_re]
        using norm_add_le (1 : ℂ) (Complex.exp (-((j + 1 : ℕ) : ℂ)) * z)
    _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_left hz (Real.exp_nonneg _)) 1

theorem zeroSharpLogMajorant_nonneg {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ zeroSharpLogMajorant r := by
  apply tsum_nonneg
  intro j
  exact Real.log_nonneg (by linarith [mul_nonneg (Real.exp_nonneg (-((j + 1 : ℕ) : ℝ))) hr])

theorem zeroSharpLogMajorant_exp_succ (N : ℕ) :
    zeroSharpLogMajorant (Real.exp ((N + 1 : ℕ) : ℝ)) =
      Real.log (1 + Real.exp (N : ℝ)) + zeroSharpLogMajorant (Real.exp (N : ℝ)) := by
  have h := (zeroSharp_log_majorant_summable (Real.exp ((N + 1 : ℕ) : ℝ))).sum_add_tsum_nat_add 1
  have he (j : ℕ) :
      Real.exp (-((j + 1 + 1 : ℕ) : ℝ)) * Real.exp ((N + 1 : ℕ) : ℝ) =
        Real.exp (-((j + 1 : ℕ) : ℝ)) * Real.exp (N : ℝ) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    push_cast
    ring
  have he0 : Real.exp (-(1 : ℝ)) * Real.exp ((N + 1 : ℕ) : ℝ) = Real.exp (N : ℝ) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  simpa only [Finset.sum_range_one, Nat.zero_add, Nat.cast_one, he, he0,
    zeroSharpLogMajorant] using h.symm

theorem zeroSharpLogMajorant_exp_nat_le (N : ℕ) :
    zeroSharpLogMajorant (Real.exp (N : ℝ)) ≤
      (N : ℝ) * ((N : ℝ) - 1) / 2 + (N : ℝ) * Real.log 2 + zeroSharpLogMajorant 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [zeroSharpLogMajorant_exp_succ]
    have h1 : 1 ≤ Real.exp (N : ℝ) := Real.one_le_exp (Nat.cast_nonneg N)
    have hl : Real.log (1 + Real.exp (N : ℝ)) ≤ Real.log 2 + (N : ℝ) := by
      have hh := Real.log_le_log (by positivity : 0 < 1 + Real.exp (N : ℝ))
        (show 1 + Real.exp (N : ℝ) ≤ 2 * Real.exp (N : ℝ) by linarith)
      simpa only [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_ne_zero _), Real.log_exp]
        using hh
    push_cast
    nlinarith

/-- Uniform disk growth for LaTeX `eq:zero-sharp-growth`. -/
theorem zeroSharp_norm_quadratic_log_bound :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ r : ℝ, 1 ≤ r → ∀ z : ℂ, ‖z‖ ≤ r →
      ‖zeroSharpFunction z‖ ≤ Real.exp ((Real.log r) ^ 2 / 2 + A * Real.log r + B) := by
  have hS : 0 ≤ zeroSharpLogMajorant 1 := zeroSharpLogMajorant_nonneg (by norm_num)
  refine ⟨1 + Real.log 2, 1 + Real.log 2 + zeroSharpLogMajorant 1,
    by positivity, by positivity, ?_⟩
  intro r hr z hz
  let x := Real.log r
  let N := Nat.ceil x
  have hx : 0 ≤ x := Real.log_nonneg hr
  have hN : x ≤ (N : ℝ) := Nat.le_ceil x
  have hN' : (N : ℝ) < x + 1 := Nat.ceil_lt_add_one hx
  have hrN : r ≤ Real.exp (N : ℝ) := by
    calc
      r = Real.exp x := (Real.exp_log (zero_lt_one.trans_le hr)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hN
  have hbound := zeroSharp_norm_le_exp_majorant (Real.exp_nonneg _) (hz.trans hrN)
  apply hbound.trans (Real.exp_le_exp.mpr ((zeroSharpLogMajorant_exp_nat_le N).trans ?_))
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hNm : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hs : (N : ℝ) ^ 2 ≤ (x + 1) ^ 2 := by nlinarith
  have hp := mul_nonneg hl (sub_nonneg.mpr hN'.le)
  change (N : ℝ) * ((N : ℝ) - 1) / 2 + (N : ℝ) * Real.log 2 + zeroSharpLogMajorant 1 ≤
    x ^ 2 / 2 + (1 + Real.log 2) * x + (1 + Real.log 2 + zeroSharpLogMajorant 1)
  nlinarith

end ModifiedCartan
#print axioms ModifiedCartan.zeroSharp_norm_quadratic_log_bound
