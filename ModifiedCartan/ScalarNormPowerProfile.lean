import ModifiedCartan.ScalarNormSquare

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Opposite choices of a complex square root have the same absolute real part. -/
theorem abs_re_eq_of_sq_eq_sq {a b : ℂ} (h : a ^ 2 = b ^ 2) : |a.re| = |b.re| := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with rfl | rfl
  · rfl
  · simp only [Complex.neg_re, abs_neg]

/-- Exact global norm profile of every actual scalar rescaling limit. The
absolute real part removes the sign change of the half-integer power across
the principal branch cut; no angular or sector ansatz is assumed. -/
theorem ArbitraryRadiusLimitData.scalar_norm_principal_power_profile
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hρ : 1 ≤ ρ) (hr : Tendsto r atTop atTop) :
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ z ∈ ball (0 : ℂ) 2,
      (d.U z).toReal = |(κ * z ^ (ρ : ℂ)).re| := by
  obtain ⟨k, c, hc, hρk, hcoeff⟩ := d.scalar_coefficient_monomial_nonzero hρ hr
  have hρpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hρ0 : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρpos.ne'
  have hi : ((ρ⁻¹ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (inv_ne_zero hρpos.ne')
  obtain ⟨κ, hκ⟩ := IsAlgClosed.exists_pow_nat_eq
    (-(c * ((ρ⁻¹ : ℝ) : ℂ) ^ 2)) (n := 2) (by norm_num)
  have hκne : κ ≠ 0 := by
    intro hz
    have hprod : -(c * ((ρ⁻¹ : ℝ) : ℂ) ^ 2) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero hc (pow_ne_zero 2 hi))
    apply hprod
    rw [← hκ, hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  have hdegree : (ρ : ℂ) * (2 : ℂ) = ((k + 2 : ℕ) : ℂ) := by
    have hh : ρ * 2 = ((k + 2 : ℕ) : ℝ) := by rw [hρk]; push_cast; ring
    exact_mod_cast hh
  have hsquare (z : ℂ) : (κ * z ^ (ρ : ℂ)) ^ 2 =
      -(d.coefficient 0 z * (z * ((ρ⁻¹ : ℝ) : ℂ)) ^ 2) := by
    rw [mul_pow, ← Complex.cpow_mul_nat, show ((2 : ℕ) : ℂ) = 2 by norm_num,
      hdegree, Complex.cpow_natCast, hκ, hcoeff]
    simp only [pow_add, mul_pow]
    ring
  refine ⟨κ, hκne, fun z hz => ?_⟩
  by_cases hz0 : z = 0
  · subst z
    simp only [d.origin_zero, EReal.toReal_zero, Complex.zero_cpow hρ0, mul_zero,
      Complex.zero_re, abs_zero]
  · have hz2 : ‖z‖ < 2 := by simpa only [mem_ball, dist_zero_right] using hz
    obtain ⟨b, hb, hU⟩ := d.scalar_norm_value_root hρ hz0 hz2
    exact hU.trans (abs_re_eq_of_sq_eq_sq (hb.trans (hsquare z).symm))

end ModifiedCartan
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalar_norm_principal_power_profile
