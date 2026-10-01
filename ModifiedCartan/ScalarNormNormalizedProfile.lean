import ModifiedCartan.ScalarPowerPolar
import ModifiedCartan.ScalarCosineIntegral

open scoped Topology
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- Exact normalized angular profile of every actual scalar rescaling limit.
The phase is free, but the amplitude pi/2 is forced by the unit-circle mean.
Auxiliary to LaTeX `thm:A` (b); actual asymptotic values are proved separately. -/
theorem ArbitraryRadiusLimitData.scalar_norm_polar_profile
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hρ : 1 ≤ ρ) (hr : Tendsto r atTop atTop) :
    ∃ φ : ℝ, ∀ R : ℝ, 0 < R → R < 2 → ∀ θ : ℝ,
      (d.U (circleMap 0 R θ)).toReal =
        (Real.pi / 2) * R ^ ρ * |Real.cos (ρ * θ + φ)| := by
  obtain ⟨κ, _, hκ⟩ := d.scalar_norm_principal_power_profile hρ hr
  obtain ⟨k, _, _, hρk, _⟩ := d.scalar_coefficient_monomial_nonzero hρ hr
  have hρm : ρ = ((k + 2 : ℕ) : ℝ) / 2 := by simpa only [Nat.cast_add, Nat.cast_ofNat] using hρk
  have hdegree : ρ * 2 = ((k + 2 : ℕ) : ℝ) := by rw [hρm]; ring
  have hp (R : ℝ) (hR : 0 < R) (hR2 : R < 2) (θ : ℝ) :
      (d.U (circleMap 0 R θ)).toReal = R ^ ρ * ‖κ‖ * |Real.cos (ρ * θ + κ.arg)| := by
    have hmem : circleMap 0 R θ ∈ ball (0 : ℂ) 2 := by
      simpa only [mem_ball, dist_zero_right, norm_circleMap_zero, abs_of_pos hR] using hR2
    rw [hκ _ hmem]
    exact abs_re_cpow_circleMap hdegree κ hR.le θ
  have he : Real.circleAverage (fun z => (d.U z).toReal) 0 1 =
      (2 * Real.pi)⁻¹ * (‖κ‖ * 4) := by
    simp only [Real.circleAverage_def, smul_eq_mul]
    simp_rw [hp 1 zero_lt_one (by norm_num), Real.one_rpow, one_mul]
    rw [intervalIntegral.integral_const_mul,
      integral_abs_cos_half_integer (m := k + 2) (by omega) hρm κ.arg]
  have hmean := d.circleAverage_one (lt_of_lt_of_le zero_lt_one hρ) hr
  rw [he] at hmean
  have hnorm : ‖κ‖ = Real.pi / 2 := by
    field_simp [Real.pi_ne_zero] at hmean
    nlinarith
  refine ⟨κ.arg, fun R hR hR2 θ => ?_⟩
  rw [hp R hR hR2 θ, hnorm]
  ring

end ModifiedCartan
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalar_norm_polar_profile
