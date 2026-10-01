import ModifiedCartan.DiskAverageDuality

open scoped Topology ENNReal NNReal
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan

/-- Remove a common inner set and bound both remainders in the same annulus. -/
theorem norm_setIntegral_sub_le_of_between {A B S T : Set ℂ}
    (hA : MeasurableSet A) (hB : volume B < ⊤)
    (hAS : A ⊆ S) (hAT : A ⊆ T) (hSB : S ⊆ B) (hTB : T ⊆ B)
    {f : ℂ → ℝ} (hf : IntegrableOn f B) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ z, ‖f z‖ ≤ C) :
    ‖(∫ z in S, f z) - ∫ z in T, f z‖ ≤ 2 * C * volume.real (B \ A) := by
  have hrem : ∀ W : Set ℂ, W ⊆ B → ‖∫ z in W \ A, f z‖ ≤ C * volume.real (B \ A) := by
    intro W hWB
    have hsub : W \ A ⊆ B \ A := fun z hz => ⟨hWB hz.1, hz.2⟩
    have hfinite : volume (B \ A) < ⊤ := (measure_mono sdiff_subset).trans_lt hB
    have hn := norm_setIntegral_le_of_norm_le_const_ae
      ((measure_mono hsub).trans_lt hfinite) (Eventually.of_forall hbound)
    exact hn.trans (mul_le_mul_of_nonneg_left (measureReal_mono hsub hfinite.ne) hC)
  have hs := setIntegral_sdiff hA (hf.mono_set hSB) hAS
  have ht := setIntegral_sdiff hA (hf.mono_set hTB) hAT
  calc
    _ = ‖(∫ z in S \ A, f z) - ∫ z in T \ A, f z‖ := by rw [hs, ht]; congr 1; ring
    _ ≤ ‖∫ z in S \ A, f z‖ + ‖∫ z in T \ A, f z‖ := norm_sub_le _ _
    _ ≤ C * volume.real (B \ A) + C * volume.real (B \ A) :=
      add_le_add (hrem S hSB) (hrem T hTB)
    _ = 2 * C * volume.real (B \ A) := by ring

theorem integrableOn_ball_of_bounded {f : ℂ → ℝ}
    (hf : AEStronglyMeasurable f volume) {C : ℝ} (hbound : ∀ z, ‖f z‖ ≤ C)
    (c : ℂ) (r : ℝ) : IntegrableOn f (ball c r) := by
  have hvol : volume (ball c r) < ⊤ :=
    (measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall c r).measure_lt_top
  have : IsFiniteMeasure (volume.restrict (ball c r)) := ⟨by simpa using hvol⟩
  exact (integrable_const C).mono' hf.restrict (Eventually.of_forall hbound)

/-- A quantitative translation bound, using the annulus of width twice the displacement. -/
theorem norm_disk_integral_sub_le {f : ℂ → ℝ}
    (hf : AEStronglyMeasurable f volume) {C : ℝ} (hbound : ∀ z, ‖f z‖ ≤ C)
    {r : ℝ} {x y : ℂ} (hxy : dist x y < r) :
    ‖(∫ z in ball x r, f z) - ∫ z in ball y r, f z‖ ≤
      8 * C * Real.pi * r * dist x y := by
  have hd : 0 ≤ dist x y := dist_nonneg
  have hr : 0 < r := lt_of_le_of_lt hd hxy
  have hC : 0 ≤ C := (norm_nonneg (f 0)).trans (hbound 0)
  have hbig : volume (ball x (r + dist x y)) < ⊤ :=
    (measure_mono ball_subset_closedBall).trans_lt
      (isCompact_closedBall x (r + dist x y)).measure_lt_top
  have hinner : ball x (r - dist x y) ⊆ ball x (r + dist x y) :=
    ball_subset_ball (by linarith)
  have h := norm_setIntegral_sub_le_of_between isOpen_ball.measurableSet hbig
    (A := ball x (r - dist x y))
    (S := ball x r) (T := ball y r) (ball_subset_ball (by linarith))
    (ball_subset_ball' (by linarith)) (ball_subset_ball (by linarith))
    (ball_subset_ball' (by rw [dist_comm y x]))
    (integrableOn_ball_of_bounded hf hbound x (r + dist x y)) hC hbound
  rw [measureReal_sdiff hinner isOpen_ball.measurableSet hbig.ne] at h
  change ‖(∫ z in ball x r, f z) - ∫ z in ball y r, f z‖ ≤
    2 * C * ((volume (ball x (r + dist x y))).toReal -
      (volume (ball x (r - dist x y))).toReal) at h
  rw [complex_ball_real_volume x (by linarith : 0 ≤ r + dist x y),
    complex_ball_real_volume x (by linarith : 0 ≤ r - dist x y)] at h
  convert h using 1; ring

theorem diskAverage_lipschitzWith_of_bounded {f : ℂ → ℝ}
    (hf : AEStronglyMeasurable f volume) {C : ℝ} (hbound : ∀ z, ‖f z‖ ≤ C)
    {r : ℝ} (hr : 0 < r) :
    LipschitzWith (Real.toNNReal (8 * C / r)) (diskAverage r f) := by
  have hC : 0 ≤ C := (norm_nonneg (f 0)).trans (hbound 0)
  have hcoef : 0 ≤ 8 * C / r := div_nonneg (mul_nonneg (by norm_num) hC) hr.le
  apply LipschitzWith.of_dist_le'
  intro x y
  rw [dist_eq_norm]
  by_cases hxy : dist x y < r
  · rw [diskAverage_eq hr.le, diskAverage_eq hr.le, ← mul_sub, norm_mul,
      show ‖(Real.pi * r ^ 2)⁻¹‖ = (Real.pi * r ^ 2)⁻¹ from by
        rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (mul_pos Real.pi_pos (sq_pos_of_pos hr)))]]
    calc
      _ ≤ (Real.pi * r ^ 2)⁻¹ * (8 * C * Real.pi * r * dist x y) :=
        mul_le_mul_of_nonneg_left (norm_disk_integral_sub_le hf hbound hxy)
          (inv_nonneg.mpr (mul_nonneg Real.pi_pos.le (sq_nonneg r)))
      _ = 8 * C / r * dist x y := by field_simp
  · calc
      _ ≤ ‖diskAverage r f x‖ + ‖diskAverage r f y‖ := norm_sub_le _ _
      _ ≤ C + C := add_le_add (norm_diskAverage_le_of_bound hr hbound x)
        (norm_diskAverage_le_of_bound hr hbound y)
      _ ≤ 8 * C := by linarith
      _ = (8 * C / r) * r := by field_simp
      _ ≤ (8 * C / r) * dist x y := mul_le_mul_of_nonneg_left (le_of_not_gt hxy) hcoef

theorem norm_diskAverage_le_integral_norm {f : ℂ → ℝ} (hf : Integrable f)
    {r : ℝ} (hr : 0 < r) (c : ℂ) :
    ‖diskAverage r f c‖ ≤ (Real.pi * r ^ 2)⁻¹ * ∫ z, ‖f z‖ := by
  have h := norm_diskAverage_sub_le hr (c := c) (T := univ) (subset_univ _)
    hf.integrableOn (g := fun _ => 0) (integrable_zero ℂ ℝ _)
  simpa only [diskAverage_const hr 0 c, sub_zero, Measure.restrict_univ] using h

theorem diskAverage_twice_lipschitzWith {f : ℂ → ℝ} (hf : Integrable f)
    {r : ℝ} (hr : 0 < r) {B : ℝ} (hB : (∫ z, ‖f z‖) ≤ B) :
    LipschitzWith (Real.toNNReal (8 * ((Real.pi * r ^ 2)⁻¹ * B) / r))
      (diskAverage r (diskAverage r f)) := by
  apply diskAverage_lipschitzWith_of_bounded (diskAverage_integrable hr.le hf).aestronglyMeasurable
    (C := (Real.pi * r ^ 2)⁻¹ * B) _ hr
  intro z
  exact (norm_diskAverage_le_integral_norm hf hr z).trans
    (mul_le_mul_of_nonneg_left hB (inv_nonneg.mpr (mul_nonneg Real.pi_pos.le (sq_nonneg r))))


end ModifiedCartan
