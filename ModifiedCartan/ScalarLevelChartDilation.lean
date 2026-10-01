import ModifiedCartan.ScalarLevelChart

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

theorem complex_positive_real_mul_cpow {t : ℝ} (ht : 0 < t) {w : ℂ} (hw : w ≠ 0) (z : ℂ) :
    ((t : ℂ) * w) ^ z = (t : ℂ) ^ z * w ^ z := by
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero ht0 hw), Complex.log_ofReal_mul ht hw,
    add_mul, Complex.exp_add, Complex.ofReal_log ht.le,
    ← Complex.cpow_def_of_ne_zero ht0, ← Complex.cpow_def_of_ne_zero hw]

theorem powerChart_positive_dilation (a : ℂ) {ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 < t)
    {w : ℂ} (hw : w ≠ 0) :
    powerChart a ρ (((t ^ ρ : ℝ) : ℂ) * w) = (t : ℂ) * powerChart a ρ w := by
  rw [powerChart, complex_positive_real_mul_cpow (Real.rpow_pos_of_pos ht ρ) hw,
    ← Complex.ofReal_cpow (Real.rpow_nonneg ht.le ρ), Real.rpow_rpow_inv ht.le hρ.ne', powerChart]
  ring

/-- A positive contraction rescales both the point and its strict level by
the exact homogeneous factor t^rho, with no loss in the coefficient. -/
theorem scalarLevelChart_dilation_mem {a b z : ℂ} {ρ t ℓ : ℝ}
    (hρ : 0 < ρ) (ht : 0 < t) (ht1 : t ≤ 1)
    (hz : z ∈ scalarLevelChart a ρ b ℓ) :
    (t : ℂ) * z ∈ scalarLevelChart a ρ b (t ^ ρ * ℓ) := by
  obtain ⟨w, hw, rfl⟩ := hz
  have hp : 0 < t ^ ρ := Real.rpow_pos_of_pos ht ρ
  have hp1 : t ^ ρ ≤ 1 := Real.rpow_le_one ht.le ht1 hρ.le
  have hw0 : w ≠ 0 := by intro he; have hh := hw.1.1; rw [he] at hh; simpa using hh
  refine ⟨(((t ^ ρ : ℝ) : ℂ) * w), ?_, powerChart_positive_dilation a hρ ht hw0⟩
  constructor
  · constructor
    · change 0 < ((((t ^ ρ : ℝ) : ℂ) * w).re)
      simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using
        mul_pos hp hw.1.1
    · have hwN : ‖w‖ < (2 / ‖a‖) ^ ρ := by simpa only [mem_ball, dist_zero_right] using hw.1.2
      rw [mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_of_nonneg hp.le]
      exact (mul_le_of_le_one_left (norm_nonneg w) hp1).trans_lt hwN
  · change t ^ ρ * ℓ < (b * (((t ^ ρ : ℝ) : ℂ) * w)).re
    have he : b * (((t ^ ρ : ℝ) : ℂ) * w) = ((t ^ ρ : ℝ) : ℂ) * (b * w) := by ring
    rw [he]
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using
      mul_lt_mul_of_pos_left hw.2 hp

end ModifiedCartan
#print axioms ModifiedCartan.powerChart_positive_dilation
#print axioms ModifiedCartan.scalarLevelChart_dilation_mem
