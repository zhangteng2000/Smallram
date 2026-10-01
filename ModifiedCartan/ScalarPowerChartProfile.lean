import ModifiedCartan.ScalarNormPowerProfile

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

theorem powerChart_deriv_mul {a w : ℂ} {ρ : ℝ} (hw : w ∈ powerChartDomain a ρ) :
    deriv (powerChart a ρ) w * w = powerChart a ρ w * ((ρ⁻¹ : ℝ) : ℂ) := by
  have hw0 : w ≠ 0 := by intro he; rw [he] at hw; simpa using hw.1
  have hp : w ^ (((ρ⁻¹ : ℝ) : ℂ) - 1) * w = w ^ ((ρ⁻¹ : ℝ) : ℂ) := by
    calc
      _ = w ^ (((ρ⁻¹ : ℝ) : ℂ) - 1) * w ^ (1 : ℂ) := by rw [Complex.cpow_one]
      _ = w ^ ((((ρ⁻¹ : ℝ) : ℂ) - 1) + 1) := (Complex.cpow_add _ _ hw0).symm
      _ = _ := by congr 1; ring
  rw [powerChart_deriv hw, powerChart]
  calc
    _ = (a * ((ρ⁻¹ : ℝ) : ℂ)) * (w ^ (((ρ⁻¹ : ℝ) : ℂ) - 1) * w) := by ring
    _ = _ := by rw [hp]; ring

/-- Exact transformation of the branch-independent scalar norm square. -/
theorem ArbitraryRadiusLimitData.scalar_square_powerChart
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hρ : ρ ≠ 0) (a : ℂ) {w : ℂ} (hw : w ∈ powerChartDomain a ρ) :
    -(d.coefficient 0 (powerChart a ρ w) *
      (powerChart a ρ w * ((ρ⁻¹ : ℝ) : ℂ)) ^ 2) =
      -(d.coefficient 0 a * (a * ((ρ⁻¹ : ℝ) : ℂ)) ^ 2) * w ^ 2 := by
  have h0 : d.fullCoefficient 0 = d.coefficient 0 := d.fullCoefficient_castSucc (0 : Fin 1)
  have he := d.fullCoefficient_powerChart hρ a hw (0 : Index 1)
  simp only [h0, Fin.val_zero, Nat.sub_zero, Nat.reduceAdd] at he
  rw [← powerChart_deriv_mul hw, mul_pow]
  calc
    _ = -(d.coefficient 0 (powerChart a ρ w) * (deriv (powerChart a ρ) w) ^ 2) * w ^ 2 := by ring
    _ = _ := by rw [he]

/-- Global chart profile of the actual scalar norm. The sign ambiguity of the
quadratic root disappears after taking the absolute real part. -/
theorem ArbitraryRadiusLimitData.scalar_norm_powerChart_profile
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hρ : 1 ≤ ρ) {a : ℂ} (ha : a ≠ 0) (b : ℂ)
    (hb : b ^ 2 = -(d.coefficient 0 a * (a * ((ρ⁻¹ : ℝ) : ℂ)) ^ 2))
    {w : ℂ} (hw : w ∈ powerChartDomain a ρ) (hw2 : ‖powerChart a ρ w‖ < 2) :
    (d.U (powerChart a ρ w)).toReal = |(b * w).re| := by
  have hr : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hw0 : w ≠ 0 := by intro he; rw [he] at hw; simpa using hw.1
  have hψ0 : powerChart a ρ w ≠ 0 := by
    unfold powerChart
    exact mul_ne_zero ha (Complex.cpow_ne_zero_iff.mpr (Or.inl hw0))
  obtain ⟨q, hq, hU⟩ := d.scalar_norm_value_root hρ hψ0 hw2
  have he : q ^ 2 = (b * w) ^ 2 := by
    rw [hq, d.scalar_square_powerChart hr.ne' a hw, ← hb, mul_pow]
  exact hU.trans (abs_re_eq_of_sq_eq_sq he)

end ModifiedCartan
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalar_norm_powerChart_profile
