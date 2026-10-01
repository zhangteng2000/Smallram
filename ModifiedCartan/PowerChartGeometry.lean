import ModifiedCartan.PowerChartAnalytic

open scoped Topology Real
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

theorem powerChartDomain_one_mem {a : ℂ} (ha : a ≠ 0) (ha4 : ‖a‖ < 4)
    {ρ : ℝ} (hρ : 0 < ρ) : (1 : ℂ) ∈ powerChartDomain a ρ := by
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hb : 1 < 4 / ‖a‖ := (lt_div_iff₀ hna).mpr (by simpa using ha4)
  exact ⟨by norm_num, by simpa only [mem_ball, dist_zero_right, norm_one] using Real.one_lt_rpow hb hρ⟩

theorem powerChart_mapsTo {a : ℂ} (ha : a ≠ 0) {ρ : ℝ} (hρ : 0 < ρ) :
    MapsTo (powerChart a ρ) (powerChartDomain a ρ) (ball (0 : ℂ) 4) := by
  intro w hw
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hb : ‖w‖ < (4 / ‖a‖) ^ ρ := by
    simpa only [mem_ball, dist_zero_right] using hw.2
  have hh := Real.rpow_lt_rpow (norm_nonneg w) hb (inv_pos.mpr hρ)
  rw [Real.rpow_rpow_inv (by positivity : 0 ≤ 4 / ‖a‖) hρ.ne'] at hh
  rw [mem_ball, dist_zero_right, powerChart, norm_mul, Complex.norm_cpow_real]
  calc
    ‖a‖ * ‖w‖ ^ ρ⁻¹ < ‖a‖ * (4 / ‖a‖) := mul_lt_mul_of_pos_left hh hna
    _ = 4 := by field_simp

theorem powerChartDomain_real_mem {a : ℂ} (ha : a ≠ 0) (ha4 : ‖a‖ < 4)
    {ρ : ℝ} (hρ : 0 < ρ) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (t : ℂ) ∈ powerChartDomain a ρ := by
  have h1 := powerChartDomain_one_mem ha ha4 hρ
  refine ⟨by simpa only [mem_ofPred_eq, Complex.ofReal_re] using ht, ?_⟩
  have hb : 1 < (4 / ‖a‖) ^ ρ := by simpa only [mem_ball, dist_zero_right, norm_one] using h1.2
  simpa only [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht] using ht1.trans_lt hb

theorem powerChart_zero (a : ℂ) {ρ : ℝ} (hρ : 0 < ρ) : powerChart a ρ 0 = 0 := by
  simpa only [Complex.ofReal_zero, Real.zero_rpow (inv_ne_zero hρ.ne'), zero_mul] using
    powerChart_real a ρ (t := 0) (by norm_num)

theorem powerChart_one (a : ℂ) (ρ : ℝ) : powerChart a ρ 1 = a := by
  simp only [powerChart, Complex.one_cpow, mul_one]

theorem powerChart_deriv {a : ℂ} {ρ : ℝ} {w : ℂ} (hw : w ∈ powerChartDomain a ρ) :
    deriv (powerChart a ρ) w = a * ((ρ⁻¹ : ℝ) : ℂ) * w ^ (((ρ⁻¹ : ℝ) : ℂ) - 1) :=
  (powerChart_hasDerivAt hw).deriv

end ModifiedCartan
#print axioms ModifiedCartan.powerChart_mapsTo

