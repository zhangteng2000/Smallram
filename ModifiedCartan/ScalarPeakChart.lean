import ModifiedCartan.ScalarSectorComponent
import ModifiedCartan.ScalarPositiveCenters

open scoped Topology
open Filter Set Metric ComplexConjugate
set_option autoImplicit false
namespace ModifiedCartan

theorem complex_eq_real_of_semicircle_phase_max {b : ℂ} (hb : 0 < b.re)
    (hmax : ∀ w : ℂ, ‖w‖ = 1 → 0 < w.re → |(b * w).re| ≤ b.re) :
    b = (b.re : ℂ) := by
  have hb0 : b ≠ 0 := by intro h; simpa only [h, Complex.zero_re, lt_self_iff_false] using hb
  have hn : 0 < ‖b‖ := norm_pos_iff.mpr hb0
  let w : ℂ := (‖b‖⁻¹ : ℝ) • conj b
  have hw : ‖w‖ = 1 := by
    dsimp only [w]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn),
      Complex.norm_conj, inv_mul_cancel₀ hn.ne']
  have hwpos : 0 < w.re := by
    simpa only [w, Complex.smul_re, Complex.conj_re, smul_eq_mul] using mul_pos (inv_pos.mpr hn) hb
  have hbw : (b * w).re = ‖b‖ := by
    dsimp only [w]
    rw [mul_smul_comm, Complex.mul_conj, Complex.smul_re, Complex.ofReal_re,
      smul_eq_mul, Complex.normSq_eq_norm_sq]
    field_simp
  have hbound : ‖b‖ ≤ b.re := by
    simpa only [hbw, abs_of_pos hn] using hmax w hw hwpos
  have he : ‖b‖ = b.re := le_antisymm hbound (Complex.re_le_norm b)
  have heq := Complex.normSq_eq_norm_sq b
  rw [Complex.normSq_apply, he] at heq
  have hbi : b.im = 0 := by
    have hh : b.im * b.im = 0 := by nlinarith
    rcases mul_eq_zero.mp hh with h | h <;> exact h
  apply Complex.ext
  · rfl
  · exact hbi

theorem ArbitraryRadiusLimitData.scalar_norm_unit_upper
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hρ : 1 ≤ ρ) (hr : Tendsto r atTop atTop) {z : ℂ} (hz : ‖z‖ = 1) :
    (d.U z).toReal ≤ Real.pi / 2 := by
  obtain ⟨φ, hφ⟩ := d.scalar_norm_polar_profile hρ hr
  have he : circleMap 0 1 z.arg = z := by
    rw [circleMap_zero, ← hz, Complex.norm_mul_exp_arg_mul_I]
  have hh := hφ 1 zero_lt_one (by norm_num) z.arg
  rw [he, Real.one_rpow, mul_one] at hh
  rw [hh]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (ρ * z.arg + φ)) (half_pos Real.pi_pos).le

/-- A geometrically chosen unit peak has the actual positive real quadratic
root pi/2. No good-center assumption is imposed on that direction. -/
theorem ArbitraryRadiusLimitData.scalar_exists_unit_peak_root
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hρ : 1 ≤ ρ) (hr : Tendsto r atTop atTop) :
    ∃ a : ℂ, ‖a‖ = 1 ∧ (d.U a).toReal = Real.pi / 2 ∧
      (((Real.pi / 2 : ℝ) : ℂ)) ^ 2 =
        -(d.coefficient 0 a * (a * ((ρ⁻¹ : ℝ) : ℂ)) ^ 2) := by
  obtain ⟨φ, hφ⟩ := d.scalar_norm_polar_profile hρ hr
  have hρpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  let a : ℂ := circleMap 0 1 (-φ / ρ)
  have ha1 : ‖a‖ = 1 := by simp only [a, norm_circleMap_zero, abs_one]
  have ha0 : a ≠ 0 := norm_ne_zero_iff.mp (by rw [ha1]; norm_num)
  have ha2 : ‖a‖ < 2 := by rw [ha1]; norm_num
  have he : ρ * (-φ / ρ) + φ = 0 := by field_simp; ring
  have hUa : (d.U a).toReal = Real.pi / 2 := by
    rw [hφ 1 zero_lt_one (by norm_num) (-φ / ρ), he, Real.cos_zero, abs_one,
      Real.one_rpow, mul_one, mul_one]
  obtain ⟨b, hb, hbRe, hbpos⟩ := d.scalar_exists_positive_root hρ ha0 ha2
    (by rw [hUa]; exact half_pos Real.pi_pos)
  have hbRe' : b.re = Real.pi / 2 := hbRe.trans hUa
  have hbReal : b = (b.re : ℂ) := by
    apply complex_eq_real_of_semicircle_phase_max hbpos
    intro w hw hwpos
    have hwInner : w ∈ powerChartInnerDomain a ρ := by
      refine ⟨hwpos, ?_⟩
      simpa only [mem_ball, dist_zero_right, norm_one, hw] using
        (powerChartInnerDomain_one_mem ha0 ha2 hρpos).2
    have hnorm : ‖powerChart a ρ w‖ = 1 := by
      rw [powerChart, norm_mul, Complex.norm_cpow_real, ha1, hw, Real.one_rpow, mul_one]
    have hprofile := d.scalar_norm_powerChart_profile hρ ha0 b hb
      (powerChartInnerDomain_subset hρpos.le hwInner) (by rw [hnorm]; norm_num)
    rw [← hprofile, hbRe']
    exact d.scalar_norm_unit_upper hρ hr hnorm
  have hbValue : b = ((Real.pi / 2 : ℝ) : ℂ) := hbReal.trans (congrArg (fun t : ℝ => (t : ℂ)) hbRe')
  exact ⟨a, ha1, hUa, by simpa only [hbValue] using hb⟩

theorem positivePowerChartDomain_real {a : ℂ} {ρ c : ℝ} (hc : 0 < c) :
    positivePowerChartDomain a ρ (c : ℂ) = powerChartInnerDomain a ρ := by
  ext w
  constructor
  · exact fun hw => hw.1
  · intro hw
    refine ⟨hw, ?_⟩
    change 0 < ((c : ℂ) * w).re
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using
      mul_pos hc hw.1

end ModifiedCartan
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalar_exists_unit_peak_root
#print axioms ModifiedCartan.positivePowerChartDomain_real
