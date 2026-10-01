import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Complex.Basic

open scoped Topology
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- The exact second-order integral formula needed for the subharmonic
Laplacian criterion. -/
theorem second_order_integral_taylor {f : ℂ → ℝ} (hf : ContDiff ℝ 2 f) (c z : ℂ) :
    f (c + z) = f c + fderiv ℝ f c z +
      ∫ t in (0 : ℝ)..1, (1 - t) *
        fderiv ℝ (fderiv ℝ f) (c + t • z) z z := by
  have ht := map_add_eq_sum_add_integral_iteratedFDeriv (x := c) (y := z) (n := 1)
    (fun t _ => hf.contDiffAt)
  simpa [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one, one_smul,
    iteratedFDeriv_zero_apply, iteratedFDeriv_one_apply, iteratedFDeriv_two_apply,
    pow_one, smul_eq_mul] using ht

end ModifiedCartan
#print axioms ModifiedCartan.second_order_integral_taylor
