import ModifiedCartan.ArbitraryScaleWeight
import ModifiedCartan.AllScaleCauchyBounds

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

#check pow_le_pow_left₀

theorem nonneg_max_pow {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (q : ℕ) :
    (max a b) ^ q = max (a ^ q) (b ^ q) := by
  by_cases hab : a ≤ b
  · rw [max_eq_right hab, max_eq_right (pow_le_pow_left₀ ha hab q)]
  · have hba := le_of_not_ge hab
    rw [max_eq_left hba, max_eq_left (pow_le_pow_left₀ hb hba q)]

theorem arbitraryScaleWeight_div_pow (ρ ε : ℝ) {R : ℝ} (hR : 0 < R) (q : ℕ) :
    (arbitraryScaleWeight ρ ε R / R) ^ q =
      max (R ^ ((q : ℝ) * (ρ - 1 - ε))) (R ^ ((q : ℝ) * (ρ - 1 + ε))) := by
  unfold arbitraryScaleWeight
  rw [← max_div_div_right hR.le, nonneg_max_pow (by positivity) (by positivity)]
  have he (a : ℝ) : (R ^ a / R) ^ q = R ^ ((a - 1) * (q : ℝ)) := by
    rw [Real.rpow_mul_natCast hR.le, Real.rpow_sub_one hR.ne']
  rw [he, he]
  congr 2 <;> ring

/-- Cauchy's derivative estimate for the actual two-power scale factor.
Only the local analytic germ and the proved scale model are needed. -/
theorem norm_iteratedDeriv_le_of_two_power_germ {a b : ℂ → ℂ} {ρ ε K R : ℝ}
    (hR : 0 < R) (ha : AnalyticAt ℂ a 0)
    (hb : AnalyticOnNhd ℂ b (ball 0 4))
    (hbound : ∀ z ∈ ball (0 : ℂ) 1, ‖b z‖ ≤ K) (q m : ℕ)
    (hrel : (fun z : ℂ => a ((R : ℂ) * z)) =ᶠ[𝓝 0]
      (fun z => ((arbitraryScaleWeight ρ ε R / R : ℝ) : ℂ) ^ q * b z)) :
    ‖iteratedDeriv m a 0‖ ≤ ((m.factorial : ℝ) * K / (1 / 2 : ℝ) ^ m) *
      max (R ^ ((q : ℝ) * (ρ - 1 - ε) - m))
        (R ^ ((q : ℝ) * (ρ - 1 + ε) - m)) := by
  have hd := hrel.iteratedDeriv_eq m
  rw [iteratedDeriv_dilate_at (R : ℂ) m (by simpa only [mul_zero] using ha),
    mul_zero, iteratedDeriv_const_mul_field] at hd
  have hdn := congrArg norm hd
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hR.le,
    Real.norm_of_nonneg (div_pos (arbitraryScaleWeight_pos ρ ε hR) hR).le,
    arbitraryScaleWeight_div_pow ρ ε hR q] at hdn
  have hDb := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le m
    (by norm_num : (0 : ℝ) < 1 / 2)
    (hb.differentiableOn.diffContOnCl_ball (closedBall_subset_ball (by norm_num : (1 / 2 : ℝ) < 4)))
    (fun z hz => hbound z ((closedBall_subset_ball (by norm_num : (1 / 2 : ℝ) < 1))
      (sphere_subset_closedBall hz)))
  rw [Real.rpow_sub_natCast hR.ne', Real.rpow_sub_natCast hR.ne',
    max_div_div_right (pow_nonneg hR.le m), ← mul_div_assoc]
  apply (le_div_iff₀ (pow_pos hR m)).mpr
  have hn : 0 ≤ max (R ^ ((q : ℝ) * (ρ - 1 - ε)))
      (R ^ ((q : ℝ) * (ρ - 1 + ε))) := by positivity
  calc
    _ = _ := by rw [mul_comm]; exact hdn
    _ ≤ _ := mul_le_mul_of_nonneg_left hDb hn
    _ = _ := mul_comm _ _

end ModifiedCartan
#print axioms ModifiedCartan.norm_iteratedDeriv_le_of_two_power_germ
