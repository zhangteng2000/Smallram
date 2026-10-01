import ModifiedCartan.LogAreaJensen
import ModifiedCartan.SmallPolynomialLog
import ModifiedCartan.PolynomialApproximationCounting

open scoped Topology ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

theorem integral_norm_log_polynomial_approximation_le (P R : Polynomial ℂ)
    (hP : P.Monic) (hroots : ∀ a, P.eval a = 0 → ‖a‖ ≤ 64)
    (herr : ∀ z ∈ closedBall (0 : ℂ) 12, ‖R.eval z - P.eval z‖ ≤ 1 / 2)
    {K : Set ℂ} (_hK : IsCompact K) (hK4 : K ⊆ ball 0 4) :
    (∫ z in K, ‖Real.log ‖R.eval z‖‖) ≤
      25 * Real.pi * (3 * Real.log 2 + 2 * P.natDegree * Real.log 76) := by
  obtain ⟨a, ha, hPa, hRa, _⟩ := polynomial_approximation_growth_center P R hP herr
  have ha1 : ‖a‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using ha
  have hRa2 : (1 / 2 : ℝ) ≤ ‖R.eval a‖ := by linarith
  have hRa0 : R.eval a ≠ 0 := norm_pos_iff.mp (by linarith)
  let M : ℝ := Real.log 2 + (P.natDegree : ℝ) * Real.log 76
  have hM : 0 ≤ M := by
    dsimp [M]
    exact add_nonneg (Real.log_nonneg (by norm_num))
      (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num)))
  have hupper (z : ℂ) (hz : z ∈ closedBall a 5) : Real.log ‖R.eval z‖ ≤ M := by
    have hz12 : z ∈ closedBall (0 : ℂ) 12 := by
      have hz5 : ‖z - a‖ ≤ 5 := by simpa only [mem_closedBall, dist_eq_norm] using hz
      have hzsum : ‖z‖ ≤ ‖z - a‖ + ‖a‖ := by
        simpa only [sub_add_cancel] using norm_add_le (z - a) a
      rw [mem_closedBall, dist_zero_right]
      linarith
    have hpow : (1 : ℝ) ≤ 76 ^ P.natDegree := one_le_pow₀ (by norm_num)
    have hPn := norm_monic_polynomial_le_of_roots_bounded P hP hroots (by norm_num : (0 : ℝ) ≤ 12) hz12
    norm_num only [show (12 : ℝ) + 64 = 76 by norm_num] at hPn
    have hRn : ‖R.eval z‖ ≤ 2 * (76 : ℝ) ^ P.natDegree := by
      have ht := norm_sub_norm_le (R.eval z) (P.eval z)
      have he := herr z hz12
      linarith
    by_cases hz0 : R.eval z = 0
    · simpa only [hz0, norm_zero, Real.log_zero] using hM
    · have hl := Real.log_le_log (norm_pos_iff.mpr hz0) hRn
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hl
      exact hl
  have hlower : -Real.log 2 ≤ Real.log ‖R.eval a‖ := by
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hRa2
    simpa only [one_div, Real.log_inv] using hl
  have hK5 : K ⊆ ball a 5 := by
    intro z hz
    have hz4 : ‖z‖ < 4 := by simpa only [mem_ball, dist_zero_right] using hK4 hz
    rw [mem_ball, dist_eq_norm]
    linarith [norm_sub_le z a]
  have hiC : IntegrableOn (fun z => ‖Real.log ‖R.eval z‖‖) (closedBall a 5) :=
    (integrableOn_log_norm_on_compact
      (fun z _ => AnalyticOnNhd.eval_polynomial R z (mem_univ z)) (subset_univ _) (isCompact_closedBall a 5)).norm
  have hi := hiC.mono_set ball_subset_closedBall
  have harea := integral_norm_log_ball_le_of_log_upper R.differentiable hRa0
    (by norm_num : (0 : ℝ) < 5) hM hupper
  calc
    _ ≤ ∫ z in ball a 5, ‖Real.log ‖R.eval z‖‖ :=
      setIntegral_mono_set hi (Eventually.of_forall (fun _ => norm_nonneg _))
        (Eventually.of_forall hK5)
    _ ≤ Real.pi * 5 ^ 2 * (2 * M - Real.log ‖R.eval a‖) := harea
    _ ≤ _ := by dsimp [M]; nlinarith [Real.pi_pos]

/-- LaTeX `eq:replacement-data`, logarithmic local L1 convergence.
This derives the limit directly from the proved area Jensen estimate and
the actual small polynomial approximation; no convergence hypothesis on R. -/
theorem polynomial_approximation_log_localL1_zero (P R : ℕ → Polynomial ℂ)
    (hP : ∀ ν, (P ν).Monic)
    (hroots : ∀ ν a, (P ν).eval a = 0 → ‖a‖ ≤ 64)
    {s : ℕ → ℝ} (hs : Tendsto s atTop atTop)
    (hm : Tendsto (fun ν => ((P ν).natDegree : ℝ) / s ν) atTop (𝓝 0))
    (herr : ∀ᶠ ν in atTop, ∀ z ∈ closedBall (0 : ℂ) 12,
      ‖(R ν).eval z - (P ν).eval z‖ ≤ 1 / 2) :
    LocalLpConvergence 1 (ball (0 : ℂ) 4)
      (fun ν z => Real.log ‖(R ν).eval z‖ / s ν) (fun _ => 0) := by
  apply localL1_zero_of_integral_norm
  · intro K hK _ ν
    exact (integrableOn_log_norm_on_compact
      (fun z _ => AnalyticOnNhd.eval_polynomial (R ν) z (mem_univ z))
      (subset_univ K) hK).div_const _
  · intro K hK hK4
    have hl := ((tendsto_inv_atTop_zero.comp hs).const_mul (25 * Real.pi * (3 * Real.log 2))).add
      (hm.const_mul (50 * Real.pi * Real.log 76))
    simp only [mul_zero, add_zero] at hl
    apply squeeze_zero' (Eventually.of_forall (fun ν => integral_nonneg (fun _ => norm_nonneg _))) _ hl
    filter_upwards [herr, hs.eventually_gt_atTop 0] with ν heν hsν
    have he : (∫ z in K, ‖Real.log ‖(R ν).eval z‖ / s ν‖) =
        (∫ z in K, ‖Real.log ‖(R ν).eval z‖‖) / s ν := by
      simp_rw [norm_div, Real.norm_eq_abs, abs_of_pos hsν]
      rw [integral_div]
    rw [he]
    calc
      _ ≤ (25 * Real.pi * (3 * Real.log 2 + 2 * (P ν).natDegree * Real.log 76)) / s ν :=
        div_le_div_of_nonneg_right
          (integral_norm_log_polynomial_approximation_le (P ν) (R ν) (hP ν) (hroots ν) heν hK hK4) hsν.le
      _ = _ := by simp only [Function.comp_def]; ring

end
end ModifiedCartan
#print axioms ModifiedCartan.polynomial_approximation_log_localL1_zero
