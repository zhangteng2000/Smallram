import ModifiedCartan.PowerChartGeometry

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- The radius-two part of the already constructed power chart. -/
noncomputable def powerChartInnerDomain (a : ℂ) (ρ : ℝ) : Set ℂ :=
  {w | 0 < w.re} ∩ ball 0 ((2 / ‖a‖) ^ ρ)

theorem powerChartInnerDomain_isOpen (a : ℂ) (ρ : ℝ) : IsOpen (powerChartInnerDomain a ρ) :=
  (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ball

theorem powerChartInnerDomain_convex (a : ℂ) (ρ : ℝ) : Convex ℝ (powerChartInnerDomain a ρ) :=
  ((convex_Ioi (0 : ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter (convex_ball _ _)

theorem powerChartInnerDomain_subset {a : ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ) :
    powerChartInnerDomain a ρ ⊆ powerChartDomain a ρ := by
  intro w hw
  refine ⟨hw.1, (ball_subset_ball ?_) hw.2⟩
  exact Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_right (by norm_num) (norm_nonneg a)) hρ

theorem powerChartInnerDomain_mapsTo {a : ℂ} (ha : a ≠ 0) {ρ : ℝ} (hρ : 0 < ρ) :
    MapsTo (powerChart a ρ) (powerChartInnerDomain a ρ) (ball (0 : ℂ) 2) := by
  intro w hw
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hb : ‖w‖ < (2 / ‖a‖) ^ ρ := by simpa only [mem_ball, dist_zero_right] using hw.2
  have hh := Real.rpow_lt_rpow (norm_nonneg w) hb (inv_pos.mpr hρ)
  rw [Real.rpow_rpow_inv (by positivity : 0 ≤ 2 / ‖a‖) hρ.ne'] at hh
  rw [mem_ball, dist_zero_right, powerChart, norm_mul, Complex.norm_cpow_real]
  calc
    ‖a‖ * ‖w‖ ^ ρ⁻¹ < ‖a‖ * (2 / ‖a‖) := mul_lt_mul_of_pos_left hh hna
    _ = 2 := by field_simp

theorem powerChartInnerDomain_one_mem {a : ℂ} (ha : a ≠ 0) (ha2 : ‖a‖ < 2)
    {ρ : ℝ} (hρ : 0 < ρ) : (1 : ℂ) ∈ powerChartInnerDomain a ρ := by
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hb : 1 < 2 / ‖a‖ := (lt_div_iff₀ hna).mpr (by simpa using ha2)
  exact ⟨by norm_num, by simpa only [mem_ball, dist_zero_right, norm_one] using Real.one_lt_rpow hb hρ⟩

/-- The convex part of a power chart on which its prescribed phase is positive. -/
noncomputable def positivePowerChartDomain (a : ℂ) (ρ : ℝ) (b : ℂ) : Set ℂ :=
  powerChartInnerDomain a ρ ∩ {w | 0 < (b * w).re}

theorem positivePowerChartDomain_isOpen (a : ℂ) (ρ : ℝ) (b : ℂ) :
    IsOpen (positivePowerChartDomain a ρ b) :=
  (powerChartInnerDomain_isOpen a ρ).inter
    (isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_const.mul continuous_id)))

theorem positivePowerChartDomain_convex (a : ℂ) (ρ : ℝ) (b : ℂ) :
    Convex ℝ (positivePowerChartDomain a ρ b) := by
  refine (powerChartInnerDomain_convex a ρ).inter ?_
  intro x hx y hy p q hp hq hpq
  change 0 < (b * (p • x + q • y)).re
  simp only [mul_add, mul_smul_comm, Complex.add_re, Complex.smul_re, smul_eq_mul]
  change 0 < (b * x).re at hx
  change 0 < (b * y).re at hy
  have hpqpos : 0 < p ∨ 0 < q := by
    by_contra hn
    push Not at hn
    linarith
  rcases hpqpos with hp' | hq'
  · exact add_pos_of_pos_of_nonneg (mul_pos hp' hx) (mul_nonneg hq hy.le)
  · exact add_pos_of_nonneg_of_pos (mul_nonneg hp hx.le) (mul_pos hq' hy)

theorem positivePowerChartDomain_one_mem {a b : ℂ} (ha : a ≠ 0) (ha2 : ‖a‖ < 2)
    {ρ : ℝ} (hρ : 0 < ρ) (hb : 0 < b.re) : (1 : ℂ) ∈ positivePowerChartDomain a ρ b := by
  refine ⟨powerChartInnerDomain_one_mem ha ha2 hρ, ?_⟩
  change 0 < (b * 1).re
  simpa only [mul_one] using hb

end ModifiedCartan
#print axioms ModifiedCartan.positivePowerChartDomain_convex
