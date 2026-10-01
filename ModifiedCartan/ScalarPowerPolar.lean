import ModifiedCartan.ScalarNormPowerProfile
import ModifiedCartan.RayPhases

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Polar expression of the real part with its actual complex phase. -/
theorem re_mul_rayPhase_eq_cos (κ : ℂ) (θ : ℝ) :
    (κ * rayPhase θ).re = ‖κ‖ * Real.cos (θ + κ.arg) := by
  have hκ : (‖κ‖ : ℂ) * rayPhase κ.arg = κ := Complex.norm_mul_exp_arg_mul_I κ
  calc
    (κ * rayPhase θ).re = (((‖κ‖ : ℂ) * rayPhase κ.arg) * rayPhase θ).re := by rw [hκ]
    _ = ((‖κ‖ : ℂ) * rayPhase (κ.arg + θ)).re := by rw [mul_assoc, rayPhase_mul]
    _ = ‖κ‖ * Real.cos (θ + κ.arg) := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        rayPhase, Complex.exp_ofReal_mul_I_re, add_comm κ.arg θ]

/-- The absolute real part of a half-integer power has a global polar formula.
Equality of squares makes it valid across the principal branch cut. -/
theorem abs_re_cpow_circleMap {m : ℕ} {ρ : ℝ} (hρ : ρ * 2 = (m : ℝ))
    (κ : ℂ) {R : ℝ} (hR : 0 ≤ R) (θ : ℝ) :
    |(κ * (circleMap 0 R θ) ^ (ρ : ℂ)).re| =
      R ^ ρ * ‖κ‖ * |Real.cos (ρ * θ + κ.arg)| := by
  have hc : (ρ : ℂ) * (2 : ℂ) = (m : ℂ) := by exact_mod_cast hρ
  have hpow (z : ℂ) : (z ^ (ρ : ℂ)) ^ 2 = z ^ m := by
    rw [← Complex.cpow_mul_nat, show ((2 : ℕ) : ℂ) = 2 by norm_num, hc, Complex.cpow_natCast]
  have hRpow : (R ^ ρ) ^ (2 : ℕ) = R ^ m := by
    rw [← Real.rpow_mul_natCast hR ρ 2, show ((2 : ℕ) : ℝ) = 2 by norm_num, hρ, Real.rpow_natCast]
  have hRpowC : ((R ^ ρ : ℝ) : ℂ) ^ 2 = (R : ℂ) ^ m := by
    exact_mod_cast hRpow
  have hphase : rayPhase (ρ * θ) ^ 2 = rayPhase θ ^ m := rayPhases_power_balance hρ θ
  have he : (κ * (circleMap 0 R θ) ^ (ρ : ℂ)) ^ 2 =
      (((R ^ ρ : ℝ) : ℂ) * (κ * rayPhase (ρ * θ))) ^ 2 := by
    rw [mul_pow, hpow, circleMap_zero]
    change κ ^ 2 * ((R : ℂ) * rayPhase θ) ^ m = _
    simp only [mul_pow, hRpowC, hphase]
    ring
  rw [abs_re_eq_of_sq_eq_sq he]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    abs_mul, abs_of_nonneg (Real.rpow_nonneg hR ρ)]
  change R ^ ρ * |(κ * rayPhase (ρ * θ)).re| = R ^ ρ * ‖κ‖ * |Real.cos (ρ * θ + κ.arg)|
  rw [re_mul_rayPhase_eq_cos, abs_mul, abs_of_nonneg (norm_nonneg κ)]
  ring

end ModifiedCartan
#print axioms ModifiedCartan.abs_re_cpow_circleMap

