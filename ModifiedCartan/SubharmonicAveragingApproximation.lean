import ModifiedCartan.LocalAveragingError
import ModifiedCartan.SubharmonicAveragingOrder
import ModifiedCartan.LipschitzCutoff

open scoped Topology ENNReal NNReal
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan

theorem IsSubharmonicOn.integral_norm_diskAverage_twice_sub_le
    {U T K : Set ℂ} (hU : IsOpen U) {u : ℂ → EReal}
    (hu : IsSubharmonicOn U u)
    (hfinite : ∀ᵐ z ∂volume.restrict U, u z ≠ ⊥ ∧ u z ≠ ⊤)
    {f : ℂ → ℝ} (hf : Integrable f) (hTU : T ⊆ U)
    (hrep : EqOn (fun z => (u z).toReal) f T)
    {χ : ℂ → ℝ} (hχ : Integrable χ) {L : ℝ≥0} (hL : LipschitzWith L χ)
    (hχnonneg : ∀ z, 0 ≤ χ z) (hχbound : ∀ z, ‖χ z‖ ≤ 1)
    (hK : MeasurableSet K) (hχone : ∀ z ∈ K, χ z = 1)
    {r : ℝ} (hr : 0 < r)
    (hroom : ∀ z ∈ tsupport χ, closedBall z (2 * r) ⊆ T) :
    (∫ z in K, ‖diskAverage r (diskAverage r f) z - f z‖) ≤
      2 * (L : ℝ) * r * ∫ z, ‖f z‖ := by
  apply ModifiedCartan.integral_norm_diskAverage_twice_sub_le hr hf hχ hL hχnonneg hχbound hK hχone
  filter_upwards [(ae_restrict_iff' hU.measurableSet).mp hfinite] with z hz
  intro hne
  have hzs : z ∈ tsupport χ := subset_tsupport χ hne
  have hzT : z ∈ T := hroom z hzs (mem_closedBall_self (by linarith))
  have h := hu.toReal_le_diskAverage_twice hfinite hf hTU hrep hr (hroom z hzs) (hz (hTU hzT)).1
  have heq : (u z).toReal = f z := hrep hzT
  rwa [heq] at h

/-- The truncation keeps the original values on the larger compact disk. -/
theorem subharmonic_uniform_averaging_approximation_on_disk
    {U : Set ℂ} (hU : IsOpen U) {u : ℕ → ℂ → EReal}
    (hu : ∀ n, IsSubharmonicOn U (u n))
    (hfinite : ∀ n, ∀ᵐ z ∂volume.restrict U, u n z ≠ ⊥ ∧ u n z ≠ ⊤)
    {c : ℂ} {R : ℝ} (hR : 0 < R) (hball : closedBall c (4 * R) ⊆ U)
    {B : ℝ}
    (hint : ∀ n, IntegrableOn (fun z => (u n z).toReal) (closedBall c (4 * R)))
    (hbound : ∀ n, (∫ z in closedBall c (4 * R), ‖(u n z).toReal‖) ≤ B) :
    ∃ L : ℝ≥0, ∀ (n : ℕ) (r : ℝ), 0 < r → r ≤ R / 2 →
      (∫ z in closedBall c R,
        ‖diskAverage r (diskAverage r ((closedBall c (4 * R)).indicator
          (fun w => (u n w).toReal))) z - (u n z).toReal‖) ≤ 2 * (L : ℝ) * r * B := by
  classical
  obtain ⟨χ, L, hL, hχc, hχsupp, hχnonneg, hχbound, hχone⟩ :=
    exists_lipschitz_cutoff (isCompact_closedBall c R) isOpen_ball
      (closedBall_subset_ball (by linarith : R < 2 * R))
  refine ⟨L, ?_⟩
  intro n r hr hrR
  let f := (closedBall c (4 * R)).indicator (fun z => (u n z).toReal)
  have hf : Integrable f := (hint n).integrable_indicator isClosed_closedBall.measurableSet
  have hrep : EqOn (fun z => (u n z).toReal) f (closedBall c (4 * R)) := by
    intro z hz
    simp only [f, indicator_of_mem hz]
  have hroom : ∀ z ∈ tsupport χ, closedBall z (2 * r) ⊆ closedBall c (4 * R) := by
    intro z hz
    apply closedBall_subset_closedBall'
    have := mem_ball.mp (hχsupp hz)
    linarith
  have h := (hu n).integral_norm_diskAverage_twice_sub_le hU (hfinite n) hf hball hrep
    (hL.continuous.integrable_of_hasCompactSupport hχc) hL hχnonneg hχbound
    isClosed_closedBall.measurableSet hχone hr hroom
  have hnorm : (∫ z, ‖f z‖) = ∫ z in closedBall c (4 * R), ‖(u n z).toReal‖ := by
    simp only [f, norm_indicator_eq_indicator_norm, integral_indicator isClosed_closedBall.measurableSet]
  rw [hnorm] at h
  have heq : (∫ z in closedBall c R,
      ‖diskAverage r (diskAverage r f) z - f z‖) =
      ∫ z in closedBall c R, ‖diskAverage r (diskAverage r f) z - (u n z).toReal‖ := by
    apply setIntegral_congr_fun isClosed_closedBall.measurableSet
    intro z hz
    have hzbig : z ∈ closedBall c (4 * R) := closedBall_subset_closedBall (by linarith) hz
    change ‖diskAverage r (diskAverage r f) z - f z‖ = _
    rw [← hrep hzbig]
  rw [heq] at h
  exact h.trans (mul_le_mul_of_nonneg_left (hbound n) (by positivity))


end ModifiedCartan
