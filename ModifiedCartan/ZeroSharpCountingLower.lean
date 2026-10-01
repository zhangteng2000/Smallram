import ModifiedCartan.ZeroSharpRolle
import ModifiedCartan.FiniteRootCountingLower

open scoped Topology BigOperators
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

/-- Lower bound needed for LaTeX `eq:zero-sharp-growth` and
`prop:sharpness-zero`, applied to every actual derivative. -/
theorem zeroSharp_derivative_logCounting_lower (m : ℕ) {R : ℝ} (hR : 1 ≤ R) :
    (Real.log R) ^ 2 / 2 - ((m : ℝ) + 1) * Real.log R - 1 ≤
      ValueDistribution.logCounting (iteratedDeriv m zeroSharpFunction) (0 : WithTop ℂ) R := by
  obtain ⟨x, hx, hroot⟩ := zeroSharp_derivative_root_sequence m
  apply logCounting_lower_of_exponentially_spaced_roots
    (zeroSharpFunction_iteratedDeriv_entire m) (zeroSharpFunction_iteratedDeriv_nonzero m)
    (Complex.ofReal_injective.comp hx.injective) (fun j => (hroot j).2.2) ?_
    (by positivity) ?_ hR
  · intro j
    change (x j : ℂ) ≠ 0
    have hneg : x j < 0 := (hroot j).2.1.trans_lt (neg_neg_of_pos (Real.exp_pos _))
    exact_mod_cast hneg.ne
  · intro j
    change ‖(x j : ℂ)‖ ≤ Real.exp ((j : ℝ) + ((m : ℝ) + 1))
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg
      ((hroot j).2.1.trans_lt (neg_neg_of_pos (Real.exp_pos _)))]
    have h := (hroot j).1
    push_cast at h
    simpa only [neg_neg, add_assoc] using neg_le_neg h

end ModifiedCartan
#print axioms ModifiedCartan.zeroSharp_derivative_logCounting_lower
