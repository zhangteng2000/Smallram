import ModifiedCartan.SingularExponentLimits

open scoped Topology
open Filter
set_option autoImplicit false
namespace ModifiedCartan

/-- Taking logarithms of the pointwise polynomial initial-value bound,
including the negligible polynomial factor and the bounded root sum. -/
theorem normalized_log_limit_le_of_polynomial_majorant {s x σ b : ℕ → ℝ}
    {u ell D d C : ℝ} (n : ℕ) (hD : 0 < D) (hd : 0 ≤ d)
    (hspos : ∀ ν, 0 < s ν) (hs : Tendsto s atTop atTop)
    (hσpos : ∀ ν, 0 < σ ν) (hxpos : ∀ᶠ ν in atTop, 0 < x ν)
    (hσlim : Tendsto (fun ν => Real.log (σ ν) / s ν) atTop (𝓝 ell))
    (hxlim : Tendsto (fun ν => Real.log (x ν) / s ν) atTop (𝓝 u))
    (hb : ∀ᶠ ν in atTop, b ν / s ν ≤ C)
    (hx : ∀ᶠ ν in atTop, x ν ≤ σ ν * (D * s ν ^ n) * Real.exp (d * b ν)) :
    u ≤ ell + d * C := by
  have hlogs : Tendsto (fun ν => Real.log (s ν) / s ν) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hs
  have hlim : Tendsto (fun ν => Real.log (σ ν) / s ν + Real.log D / s ν +
      (n : ℝ) * (Real.log (s ν) / s ν) + d * C) atTop (𝓝 (ell + d * C)) := by
    simpa only [mul_zero, add_zero] using
      (((hσlim.add (hs.const_div_atTop (Real.log D))).add (hlogs.const_mul (n : ℝ))).add_const (d * C))
  apply le_of_tendsto_of_tendsto hxlim hlim
  filter_upwards [hxpos, hb, hx] with ν hxν hbν hν
  have hlog := Real.log_le_log hxν hν
  rw [Real.log_mul (mul_ne_zero (hσpos ν).ne' (mul_ne_zero hD.ne' (pow_ne_zero _ (hspos ν).ne')))
      (Real.exp_pos _).ne', Real.log_mul (hσpos ν).ne' (mul_ne_zero hD.ne' (pow_ne_zero _ (hspos ν).ne')),
    Real.log_mul hD.ne' (pow_ne_zero _ (hspos ν).ne'), Real.log_pow, Real.log_exp] at hlog
  have he : (Real.log (σ ν) + (Real.log D + (n : ℝ) * Real.log (s ν)) + d * b ν) / s ν =
      Real.log (σ ν) / s ν + Real.log D / s ν + (n : ℝ) * (Real.log (s ν) / s ν) + d * (b ν / s ν) := by ring
  have hh := div_le_div_of_nonneg_right hlog (hspos ν).le
  rw [he] at hh
  exact hh.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hbν hd))

end ModifiedCartan
#print axioms ModifiedCartan.normalized_log_limit_le_of_polynomial_majorant
