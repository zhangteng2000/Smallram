import ModifiedCartan.RootIndicatorSectors
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open scoped Topology
open Filter Set MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- The actual root maximum integrates to 2*sin(pi/q) on one period. -/
theorem sharpnessRootIndicator_integral_period {q : ℕ} (hq : 1 ≤ q) (s : ℝ) :
    (∫ φ in s..s + 2 * Real.pi / q, sharpnessRootIndicator q hq φ) =
      2 * Real.sin (Real.pi / q) := by
  have hp : 0 < Real.pi / (q : ℝ) := div_pos Real.pi_pos (by exact_mod_cast (show 0 < q by omega))
  have he := (sharpnessRootIndicator_periodic hq).intervalIntegral_add_eq s (-(Real.pi / q))
  rw [show -(Real.pi / q) + 2 * Real.pi / q = Real.pi / q by ring] at he
  rw [he]
  calc
    _ = ∫ φ in -(Real.pi / q)..Real.pi / q, Real.cos φ := by
      apply intervalIntegral.integral_congr
      intro φ hφ
      rw [uIcc_of_le (by linarith)] at hφ
      exact sharpnessRootIndicator_eq_cos hq hφ
    _ = _ := by rw [integral_cos, Real.sin_neg]; ring

theorem sharpnessRootIndicator_integral_periods {q : ℕ} (hq : 1 ≤ q) (N : ℕ) :
    (∫ φ in 0..(N : ℝ) * (2 * Real.pi / q), sharpnessRootIndicator q hq φ) =
      (N : ℝ) * (2 * Real.sin (Real.pi / q)) := by
  have he := (sharpnessRootIndicator_periodic hq).intervalIntegral_add_zsmul_eq (N : ℤ) 0
    (fun a b => (sharpnessRootIndicator_continuous hq).intervalIntegrable a b)
  have hbase := sharpnessRootIndicator_integral_period hq 0
  simp only [zero_add] at hbase
  simpa only [zsmul_eq_mul, Int.cast_natCast, zero_add, hbase] using he

/-- The rescaled angle covers exactly q+k root periods. -/
theorem sharpnessRootIndicator_integral_scaled {q : ℕ} (hq : 1 ≤ q) (k : ℕ) :
    (∫ θ in 0..2 * Real.pi, sharpnessRootIndicator q hq ((1 + (k : ℝ) / q) * θ)) =
      (q : ℝ) * (2 * Real.sin (Real.pi / q)) := by
  let ρ : ℝ := 1 + (k : ℝ) / q
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have he : ρ * (2 * Real.pi) = ((q + k : ℕ) : ℝ) * (2 * Real.pi / q) := by
    dsimp [ρ]
    push_cast
    field_simp
    <;> ring
  change (∫ θ in 0..2 * Real.pi, sharpnessRootIndicator q hq (ρ * θ)) = _
  rw [intervalIntegral.integral_comp_mul_left _ hρ.ne', mul_zero, he,
    sharpnessRootIndicator_integral_periods hq (q + k), smul_eq_mul]
  have hbalance : ρ * (q : ℝ) = (q + k : ℕ) := by dsimp [ρ]; push_cast; field_simp
  rw [← hbalance]
  field_simp

/-- Exact average in LaTeX `eq:sharpness-asymptotic`. -/
theorem sharpness_indicator_average {q : ℕ} (hq : 1 ≤ q) (k : ℕ) :
    (2 * Real.pi)⁻¹ * (∫ θ in 0..2 * Real.pi,
      sharpnessRootIndicator q hq ((1 + (k : ℝ) / q) * θ) / (1 + (k : ℝ) / q)) =
    (q : ℝ) * Real.sin (Real.pi / q) / (Real.pi * (1 + (k : ℝ) / q)) := by
  rw [intervalIntegral.integral_div, sharpnessRootIndicator_integral_scaled hq k]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end ModifiedCartan
#print axioms ModifiedCartan.sharpnessRootIndicator_integral_period
#print axioms ModifiedCartan.sharpness_indicator_average

