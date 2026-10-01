import ModifiedCartan.LocalizedRepresentation
import ModifiedCartan.SingularPowerEstimate

open scoped Topology ENNReal ContDiff
open Filter MeasureTheory Set Metric MeromorphicOn

set_option autoImplicit false

namespace ModifiedCartan

/-! Fractional zero-weight bounds for `eq:higher-logderiv-measure`, derived from the mass of a larger cutoff equal to one on the inner support. -/

theorem localizedZeroMeasure_mass_sum {f : ℂ → ℂ} {c : ℂ} {R s : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hs : 0 ≤ s)
    {χ : ℂ → ℝ} (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hχ0 : ∀ a, 0 ≤ χ a) :
    (localizedZeroMeasure hf s χ hχ hχc : Measure ℂ).real univ =
      s⁻¹ * ∑ a ∈ hf.meromorphicOn.divisor_ball_support_finite.toFinset,
        χ a * (divisor f (ball c R) a : ℝ) := by
  rw [localizedZeroMeasure, localizedMeasure_real_univ _ _ _
    (fun a => mul_nonneg (inv_nonneg.mpr hs) (hχ0 a)),
    integral_finiteZeroCountingMeasure (hf.mono ball_subset_closedBall), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem zero_weight_fractional_sum_le_localized_mass
    {f : ℂ → ℂ} {c : ℂ} {R s α : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hs : 0 < s)
    {χ ξ : ℂ → ℝ} (hχ : ∀ a, 0 ≤ χ a ∧ χ a ≤ 1)
    (hξ : Continuous ξ) (hξc : HasCompactSupport ξ) (hξ0 : ∀ a, 0 ≤ ξ a)
    (hξone : ∀ a, χ a ≠ 0 → ξ a = 1) (hα : 0 < α) (hα1 : α ≤ 1) :
    (∑ a ∈ hf.meromorphicOn.divisor_ball_support_finite.toFinset,
      (χ a * (divisor f (ball c R) a : ℝ)) ^ α) ≤
      s * (localizedZeroMeasure hf s ξ hξ hξc : Measure ℂ).real univ := by
  rw [localizedZeroMeasure_mass_sum hf hs.le hξ hξc hξ0, ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
  apply Finset.sum_le_sum
  intro a _
  have hm := (hf.mono ball_subset_closedBall).divisor_nonneg a
  by_cases hχa : χ a = 0
  · simp only [hχa, zero_mul, Real.zero_rpow hα.ne']
    exact mul_nonneg (hξ0 a) (by exact_mod_cast hm)
  · rw [hξone a hχa, one_mul]
    exact weighted_integer_rpow_le hα hα1 (hχ a).1 (hχ a).2 hm

theorem LocalLpConvergence.zero_fractional_mass_bounded {U : Set ℂ}
    {f : ℕ → ℂ → ℂ} {s : ℕ → ℝ} {u : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hu : LocalLpConvergence 1 U (fun n z => (s n)⁻¹ * Real.log ‖f n z‖) u)
    (hball : ball c R ⊆ U) (hf : ∀ n, AnalyticOnNhd ℂ (f n) (closedBall c R))
    (hnonzero : ∀ n, ∃ b ∈ ball c R, f n b ≠ 0) (hs : ∀ n, 0 < s n)
    {χ ξ : ℂ → ℝ} (hχ : ∀ a, 0 ≤ χ a ∧ χ a ≤ 1)
    (hξ : ContDiff ℝ 2 ξ) (hξc : HasCompactSupport ξ) (hξU : tsupport ξ ⊆ ball c R)
    (hξ0 : ∀ a, 0 ≤ ξ a) (hξone : ∀ a, χ a ≠ 0 → ξ a = 1) :
    ∃ M : ℝ, 0 < M ∧ ∀ n (α : ℝ), 0 < α → α ≤ 1 →
      (∑ a ∈ (hf n).meromorphicOn.divisor_ball_support_finite.toFinset,
        (χ a * (divisor (f n) (ball c R) a : ℝ)) ^ α) ≤ s n * M := by
  obtain ⟨M, hM0, hM⟩ := hu.localizedZeroMeasure_mass_bounded hball hf hnonzero
    (fun n => (hs n).le) hξ hξc hξU hξ0
  refine ⟨M, hM0, ?_⟩
  intro n α hα hα1
  exact (zero_weight_fractional_sum_le_localized_mass (α := α) (hf n) (hs n) hχ
    hξ.continuous hξc hξ0 hξone hα hα1).trans
      (mul_le_mul_of_nonneg_left (hM n) (hs n).le)


end ModifiedCartan

