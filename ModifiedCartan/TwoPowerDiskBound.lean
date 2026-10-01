import ModifiedCartan.MonomialExtension

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- The literal closed-disk estimate in LaTeX `eq:arbitrary-coefficients`. -/
theorem two_power_closed_disk_bound_of_model {A b : ℂ → ℂ} {ρ ε K R : ℝ}
    (hR : 0 < R) (q : ℕ) (hb : AnalyticOnNhd ℂ b (ball 0 4))
    (hbound : ∀ z ∈ ball (0 : ℂ) 1, ‖b z‖ ≤ K)
    (heq : EqOn (fun z : ℂ => A ((R : ℂ) * z))
      (fun z => ((arbitraryScaleWeight ρ ε R / R : ℝ) : ℂ) ^ q * b z) (ball 0 4)) :
    ∀ z ∈ closedBall (0 : ℂ) R, ‖A z‖ ≤ K *
      max (R ^ ((q : ℝ) * (ρ - 1 - ε))) (R ^ ((q : ℝ) * (ρ - 1 + ε))) := by
  intro z hz
  have hw : z / (R : ℂ) ∈ closedBall (0 : ℂ) 1 := by
    simp only [mem_closedBall, dist_zero_right] at hz ⊢
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le]
    exact (div_le_one hR).mpr hz
  have hh := heq ((closedBall_subset_ball (by norm_num : (1 : ℝ) < 4)) hw)
  dsimp only at hh
  have hRℂ : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  rw [mul_div_cancel₀ _ hRℂ] at hh
  rw [hh, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg (div_pos (arbitraryScaleWeight_pos ρ ε hR) hR).le]
  have hnorm := norm_le_closed_unit_ball_of_open_bound hb hbound _ hw
  calc
    _ ≤ (arbitraryScaleWeight ρ ε R / R) ^ q * K :=
      mul_le_mul_of_nonneg_left hnorm
        (pow_nonneg (div_pos (arbitraryScaleWeight_pos ρ ε hR) hR).le q)
    _ = _ := by rw [arbitraryScaleWeight_div_pow ρ ε hR q, mul_comm]

end ModifiedCartan
#print axioms ModifiedCartan.two_power_closed_disk_bound_of_model
