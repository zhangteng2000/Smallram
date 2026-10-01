import ModifiedCartan.AllScaleCauchyBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

/-- A positive constant cannot be bounded at every positive radius by
two powers whose exponents lie strictly on the same side of zero. -/
theorem two_power_exponents_straddle_zero {d C a b : ℝ} (hd : 0 < d) (hab : a ≤ b)
    (hb : ∀ R : ℝ, 0 < R → d ≤ C * max (R ^ a) (R ^ b)) : a ≤ 0 ∧ 0 ≤ b := by
  constructor
  · by_contra hna
    have ha : 0 < a := lt_of_not_ge hna
    have ht : Tendsto (fun R : ℝ => C * R ^ a) (𝓝[>] 0) (𝓝 0) := by
      have hh := (Real.continuous_rpow_const ha.le).continuousAt.tendsto
        (x := (0 : ℝ))
      simpa only [Real.zero_rpow ha.ne', mul_zero] using
        (hh.mono_left nhdsWithin_le_nhds).const_mul C
    have he : ∀ᶠ R : ℝ in 𝓝[>] 0, d ≤ C * R ^ a := by
      filter_upwards [self_mem_nhdsWithin,
        (gt_mem_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds] with R hR hR1
      have hh := hb R hR
      rw [max_eq_left (Real.rpow_le_rpow_of_exponent_ge hR hR1.le hab)] at hh
      exact hh
    exact (not_le_of_gt hd) (ge_of_tendsto ht he)
  · by_contra hnb
    have hb0 : b < 0 := lt_of_not_ge hnb
    have ht : Tendsto (fun R : ℝ => C * R ^ b) atTop (𝓝 0) := by
      simpa only [neg_neg, mul_zero] using
        (tendsto_rpow_neg_atTop (neg_pos.mpr hb0)).const_mul C
    have he : ∀ᶠ R : ℝ in atTop, d ≤ C * R ^ b := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
      have hh := hb R (zero_lt_one.trans_le hR)
      rw [max_eq_right (Real.rpow_le_rpow_of_exponent_le hR hab)] at hh
      exact hh
    exact (not_le_of_gt hd) (ge_of_tendsto ht he)

/-- Letting epsilon decrease to zero in the two-sided Cauchy bounds
forces the derivative weight to be exactly zero; used for
LaTeX `eq:monomial-coefficients`. -/
theorem weight_zero_of_two_power_bounds {d p q ρ : ℝ} (hd : 0 < d)
    (hq : 0 ≤ q) (hρ : 0 < ρ)
    (hb : ∀ ε : ℝ, 0 < ε → ε < ρ → ∃ C : ℝ, ∀ R : ℝ, 0 < R →
      d ≤ C * max (R ^ (p - q * ε)) (R ^ (p + q * ε))) : p = 0 := by
  have he : ∀ᶠ ε : ℝ in 𝓝[>] 0, p - q * ε ≤ 0 ∧ 0 ≤ p + q * ε := by
    filter_upwards [self_mem_nhdsWithin,
      (gt_mem_nhds hρ).filter_mono nhdsWithin_le_nhds] with ε hε hερ
    obtain ⟨C, hC⟩ := hb ε hε hερ
    exact two_power_exponents_straddle_zero hd (by nlinarith [mul_nonneg hq hε.le]) hC
  have hi : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hl : Tendsto (fun ε : ℝ => p - q * ε) (𝓝[>] 0) (𝓝 p) := by
    simpa only [mul_zero, sub_zero] using tendsto_const_nhds.sub (hi.const_mul q)
  have hu : Tendsto (fun ε : ℝ => p + q * ε) (𝓝[>] 0) (𝓝 p) := by
    simpa only [mul_zero, add_zero] using tendsto_const_nhds.add (hi.const_mul q)
  exact le_antisymm (le_of_tendsto hl (he.mono (fun _ h => h.1)))
    (ge_of_tendsto hu (he.mono (fun _ h => h.2)))

end ModifiedCartan
#print axioms ModifiedCartan.two_power_exponents_straddle_zero
#print axioms ModifiedCartan.weight_zero_of_two_power_bounds
