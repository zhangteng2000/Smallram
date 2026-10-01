import ModifiedCartan.RootIndicatorIntegral

open scoped Topology
open Filter Set MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- The two-root indicator is exactly absolute cosine. -/
theorem sharpnessRootIndicator_two_eq_abs_cos (φ : ℝ) :
    sharpnessRootIndicator 2 (by norm_num) φ = |Real.cos φ| := by
  have h0 : (rayPhase φ * sharpnessRoot 2 (0 : Fin 2)).re = Real.cos φ := by
    simpa only [Fin.val_zero, Nat.cast_zero, mul_zero, add_zero] using
      sharpnessRoot_real_cos φ (0 : Fin 2)
  have h1 : (rayPhase φ * sharpnessRoot 2 (1 : Fin 2)).re = -Real.cos φ := by
    have hh := sharpnessRoot_real_cos φ (1 : Fin 2)
    norm_num only [Fin.val_one, Nat.cast_one, Nat.cast_ofNat, mul_one] at hh
    rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.cos_add_pi] at hh
    exact hh
  apply le_antisymm
  · unfold sharpnessRootIndicator
    apply Finset.sup'_le
    intro j _
    fin_cases j
    · change (rayPhase φ * sharpnessRoot 2 (0 : Fin 2)).re ≤ |Real.cos φ|
      rw [h0]; exact le_abs_self _
    · change (rayPhase φ * sharpnessRoot 2 (1 : Fin 2)).re ≤ |Real.cos φ|
      rw [h1]; exact neg_le_abs _
  · by_cases hp : 0 ≤ Real.cos φ
    · rw [abs_of_nonneg hp, ← h0]
      exact sharpnessRootIndicator_le (by norm_num) φ (0 : Fin 2)
    · rw [abs_of_neg (lt_of_not_ge hp), ← h1]
      exact sharpnessRootIndicator_le (by norm_num) φ (1 : Fin 2)

theorem abs_cos_periodic : Function.Periodic (fun θ : ℝ => |Real.cos θ|) Real.pi := by
  intro θ
  change |Real.cos (θ + Real.pi)| = |Real.cos θ|
  rw [Real.cos_add_pi, abs_neg]

/-- Exact mass of one cosine sector, independent of the angular origin. -/
theorem integral_abs_cos_period (φ : ℝ) :
    (∫ θ in φ..φ + Real.pi, |Real.cos θ|) = 2 := by
  have hh := sharpnessRootIndicator_integral_period (q := 2) (by norm_num) φ
  simpa only [sharpnessRootIndicator_two_eq_abs_cos, Nat.cast_ofNat,
    Real.sin_pi_div_two, mul_one, mul_div_cancel_left₀ Real.pi (by norm_num : (2 : ℝ) ≠ 0)] using hh

/-- The exact total mass over any integer number of sectors. -/
theorem integral_abs_cos_periods (m : ℕ) (φ : ℝ) :
    (∫ θ in φ..φ + (m : ℝ) * Real.pi, |Real.cos θ|) = (m : ℝ) * 2 := by
  have hh := abs_cos_periodic.intervalIntegral_add_zsmul_eq (m : ℤ) φ
    (fun a b => Real.continuous_cos.abs.intervalIntegrable a b)
  simpa only [zsmul_eq_mul, Int.cast_natCast, integral_abs_cos_period] using hh

/-- Exact angular integral for every positive half-integer order. Context:
normalization and sector weights in the scalar conclusion of `thm:A`. -/
theorem integral_abs_cos_half_integer {m : ℕ} (hm : 0 < m) {ρ : ℝ}
    (hρ : ρ = (m : ℝ) / 2) (φ : ℝ) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, |Real.cos (ρ * θ + φ)|) = 4 := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  have hr : 0 < ρ := by rw [hρ]; exact div_pos (Nat.cast_pos.mpr hm) (by norm_num)
  rw [intervalIntegral.integral_comp_mul_add (fun θ => |Real.cos θ|) hr.ne' φ,
    mul_zero, zero_add]
  have he : ρ * (2 * Real.pi) + φ = φ + (m : ℝ) * Real.pi := by rw [hρ]; ring
  rw [he, integral_abs_cos_periods, smul_eq_mul, hρ]
  field_simp
  <;> ring

end ModifiedCartan
#print axioms ModifiedCartan.integral_abs_cos_half_integer

