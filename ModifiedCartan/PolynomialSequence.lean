import ModifiedCartan.MaximumModulus
import ModifiedCartan.EntireTaylorJets
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.Liouville

open scoped Topology BigOperators
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

#check tsum_eq_sum
#check Real.rpow_natCast
#check exists_nat_gt

/-- Cauchy's estimate along the radii in LaTeX `eq:absorption` forces
every derivative above the real power exponent to vanish. -/
theorem iteratedDeriv_zero_of_power_sequence {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {r : ℕ → ℝ} (hr : ∀ ν, 0 < r ν)
    (ht : Tendsto r atTop atTop) {C γ : ℝ}
    (hb : ∀ᶠ ν in atTop, maximumModulus f (r ν) ≤ C * (r ν) ^ γ)
    {k : ℕ} (hk : γ < (k : ℝ)) : iteratedDeriv k f 0 = 0 := by
  have hlim : Tendsto (fun ν => (k.factorial : ℝ) * C * (r ν) ^ (γ - (k : ℝ)))
      atTop (𝓝 0) := by
    have hh := (tendsto_rpow_neg_atTop (sub_pos.mpr hk)).comp ht
    have he : -((k : ℝ) - γ) = γ - (k : ℝ) := by ring
    simpa only [Function.comp_def, he, mul_zero] using! hh.const_mul ((k.factorial : ℝ) * C)
  apply norm_le_zero_iff.mp
  apply ge_of_tendsto hlim
  filter_upwards [hb] with ν hν
  have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k (hr ν)
    hf.diffContOnCl (fun z hz =>
      (norm_le_maximumModulus hf.continuous (sphere_subset_closedBall hz)).trans hν)
  have he : (k.factorial : ℝ) * (C * (r ν) ^ γ) / (r ν) ^ k =
      (k.factorial : ℝ) * C * (r ν) ^ (γ - (k : ℝ)) := by
    rw [Real.rpow_sub (hr ν), Real.rpow_natCast]
    ring
  exact hc.trans_eq he

theorem entire_eq_taylorPolynomial_of_deriv_vanishing {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {N : ℕ}
    (hz : ∀ k : ℕ, N ≤ k → iteratedDeriv k f 0 = 0) (z : ℂ) :
    f z = (FewInflection.taylorPolynomial f 0 N).eval z := by
  classical
  rw [FewInflection.taylorPolynomial_eval_eq_sum]
  rw [← Complex.taylorSeries_eq_of_entire' 0 z hf]
  apply tsum_eq_sum
  intro k hk
  have hNk : N ≤ k := by
    by_contra hh
    exact hk (Finset.mem_range.mpr (by omega))
  rw [hz k hNk, mul_zero, zero_mul]

/-- Polynomiality conclusion used in both `prop:small-order` and
`prop:zero-order-ramification`; no global growth bound is required. -/
theorem entire_polynomial_of_power_sequence {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {r : ℕ → ℝ} (hr : ∀ ν, 0 < r ν)
    (ht : Tendsto r atTop atTop) {C γ : ℝ}
    (hb : ∀ᶠ ν in atTop, maximumModulus f (r ν) ≤ C * (r ν) ^ γ) :
    ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z := by
  obtain ⟨N, hN⟩ := exists_nat_gt γ
  refine ⟨FewInflection.taylorPolynomial f 0 N, ?_⟩
  apply entire_eq_taylorPolynomial_of_deriv_vanishing hf
  intro k hk
  exact iteratedDeriv_zero_of_power_sequence hf hr ht hb
    (hN.trans_le (by exact_mod_cast hk))

end ModifiedCartan
#print axioms ModifiedCartan.iteratedDeriv_zero_of_power_sequence
#print axioms ModifiedCartan.entire_polynomial_of_power_sequence
