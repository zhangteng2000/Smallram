import ModifiedCartan.ScalarSectorGeometry
import ModifiedCartan.ScalarPowerChartProfile

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- The principal power chart agrees with the explicit small circular arc. -/
theorem powerChart_unit_arc {ρ θ : ℝ} (hρ : 0 < ρ)
    (hθ : ρ * θ ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2)) (a : ℂ) :
    powerChart a ρ (circleMap 0 1 (ρ * θ)) = a * circleMap 0 1 θ := by
  have h₁ : -Real.pi < (((ρ * θ : ℝ) : ℂ) * Complex.I).im := by
    simp only [Complex.mul_I_im, Complex.ofReal_re]
    linarith [hθ.1, Real.pi_pos]
  have h₂ : (((ρ * θ : ℝ) : ℂ) * Complex.I).im ≤ Real.pi := by
    simp only [Complex.mul_I_im, Complex.ofReal_re]
    linarith [hθ.2, Real.pi_pos]
  rw [powerChart]
  simp only [circleMap_zero, Complex.ofReal_one, one_mul]
  rw [Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _) _, Complex.log_exp h₁ h₂]
  congr 2
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hρ.ne']

/-- Every open angular sector arc lies in the actual positive power chart. -/
theorem unit_arc_mem_scalarPositiveChart {a : ℂ} (ha : ‖a‖ = 1) {ρ θ : ℝ}
    (hρ : 0 < ρ) (hθ : ρ * θ ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    a * circleMap 0 1 θ ∈ scalarPositiveChart a ρ ((Real.pi / 2 : ℝ) : ℂ) := by
  let w := circleMap (0 : ℂ) 1 (ρ * θ)
  have hwre : 0 < w.re := by
    simpa only [w, circleMap_zero_re, one_mul] using Real.cos_pos_of_mem_Ioo hθ
  have hw : w ∈ powerChartInnerDomain a ρ := by
    refine ⟨hwre, ?_⟩
    simpa only [w, mem_ball, dist_zero_right, norm_circleMap_zero, abs_one, ha, div_one] using
      Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) hρ
  refine ⟨w, ⟨hw, ?_⟩, powerChart_unit_arc hρ hθ a⟩
  change 0 < (((Real.pi / 2 : ℝ) : ℂ) * w).re
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using
    mul_pos (half_pos Real.pi_pos) hwre

/-- Exact cosine profile on a sector centered at a unit positive peak. -/
theorem ArbitraryRadiusLimitData.scalar_norm_unit_arc
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hρ : 1 ≤ ρ) {a : ℂ} (ha : ‖a‖ = 1)
    (hroot : (((Real.pi / 2 : ℝ) : ℂ)) ^ 2 = d.scalarQuadratic a)
    {θ : ℝ} (hθ : ρ * θ ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    (d.U (a * circleMap 0 1 θ)).toReal = (Real.pi / 2) * Real.cos (ρ * θ) := by
  have hrho : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have ha0 : a ≠ 0 := norm_ne_zero_iff.mp (by rw [ha]; norm_num)
  have he := powerChart_unit_arc hrho hθ a
  have hw : circleMap (0 : ℂ) 1 (ρ * θ) ∈ powerChartInnerDomain a ρ := by
    refine ⟨?_, ?_⟩
    · change 0 < (circleMap (0 : ℂ) 1 (ρ * θ)).re
      simpa only [circleMap_zero_re, one_mul] using Real.cos_pos_of_mem_Ioo hθ
    · simpa only [mem_ball, dist_zero_right, norm_circleMap_zero, abs_one, ha, div_one] using
      Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) hrho
  have hn : ‖powerChart a ρ (circleMap 0 1 (ρ * θ))‖ < 2 := by
    rw [he, norm_mul, ha, norm_circleMap_zero]
    norm_num
  have hh := d.scalar_norm_powerChart_profile hρ ha0 ((Real.pi / 2 : ℝ) : ℂ)
    hroot (powerChartInnerDomain_subset hrho.le hw) hn
  rw [he] at hh
  rw [hh]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    circleMap_zero_re, one_mul]
  exact abs_of_pos (mul_pos (half_pos Real.pi_pos) (Real.cos_pos_of_mem_Ioo hθ))

theorem scalar_sector_angle_mem {ρ θ : ℝ} (hρ : 0 < ρ)
    (hθ : θ ∈ Ioo (-(Real.pi / (2 * ρ))) (Real.pi / (2 * ρ))) :
    ρ * θ ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
  have he : ρ * (Real.pi / (2 * ρ)) = Real.pi / 2 := by field_simp
  have h₁ := mul_lt_mul_of_pos_left hθ.1 hρ
  have h₂ := mul_lt_mul_of_pos_left hθ.2 hρ
  rw [mul_neg, he] at h₁
  rw [he] at h₂
  exact ⟨h₁, h₂⟩

end ModifiedCartan
#print axioms ModifiedCartan.unit_arc_mem_scalarPositiveChart
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalar_norm_unit_arc
