import ModifiedCartan.DiskAverageDuality

open scoped Topology ENNReal NNReal
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan

theorem norm_diskAverage_le_of_bound_on_ball {r : ℝ} (hr : 0 < r)
    {f : ℂ → ℝ} {c : ℂ} {C : ℝ} (hbound : ∀ z ∈ ball c r, ‖f z‖ ≤ C) :
    ‖diskAverage r f c‖ ≤ C := by
  have harea : 0 < Real.pi * r ^ 2 := mul_pos Real.pi_pos (sq_pos_of_pos hr)
  have hvol : volume (ball c r) < ⊤ :=
    (measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall c r).measure_lt_top
  have hint := norm_setIntegral_le_of_norm_le_const_ae hvol
    ((ae_restrict_iff' isOpen_ball.measurableSet).mpr (Eventually.of_forall hbound))
  change ‖∫ z in ball c r, f z‖ ≤ C * (volume (ball c r)).toReal at hint
  rw [complex_ball_real_volume c hr.le] at hint
  rw [diskAverage_eq hr.le, norm_mul,
    show ‖(Real.pi * r ^ 2)⁻¹‖ = (Real.pi * r ^ 2)⁻¹ from by
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr harea)]]
  calc
    _ ≤ (Real.pi * r ^ 2)⁻¹ * (C * (Real.pi * r ^ 2)) :=
      mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr harea.le)
    _ = C := by field_simp

theorem diskAverage_mono {r : ℝ} (hr : 0 ≤ r) {f g : ℂ → ℝ} {c : ℂ}
    (hf : IntegrableOn f (ball c r)) (hg : IntegrableOn g (ball c r))
    (hfg : f ≤ᵐ[volume.restrict (ball c r)] g) :
    diskAverage r f c ≤ diskAverage r g c := by
  simp only [diskAverage_eq hr]
  exact mul_le_mul_of_nonneg_left (integral_mono_ae hf hg hfg)
    (inv_nonneg.mpr (mul_nonneg Real.pi_pos.le (sq_nonneg r)))

theorem lipschitz_norm_diskAverage_sub_le {L : ℝ≥0} {χ : ℂ → ℝ}
    (hχ : LipschitzWith L χ) {r : ℝ} (hr : 0 < r) (c : ℂ) :
    ‖diskAverage r χ c - χ c‖ ≤ (L : ℝ) * r := by
  have hint : IntegrableOn χ (ball c r) :=
    (hχ.continuous.continuousOn.integrableOn_compact (isCompact_closedBall c r)).mono_set
      ball_subset_closedBall
  have hvol : volume (ball c r) < ⊤ :=
    (measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall c r).measure_lt_top
  have : IsFiniteMeasure (volume.restrict (ball c r)) := ⟨by simpa using hvol⟩
  rw [← diskAverage_const hr (χ c) c, ← diskAverage_sub hint (integrable_const _)]
  apply norm_diskAverage_le_of_bound_on_ball hr
  intro z hz
  rw [← dist_eq_norm]
  exact (hχ.dist_le_mul z c).trans
    (mul_le_mul_of_nonneg_left (mem_ball.mp hz).le L.coe_nonneg)

theorem lipschitz_norm_diskAverage_twice_sub_le {L : ℝ≥0} {χ : ℂ → ℝ}
    (hχ : LipschitzWith L χ) (hint : Integrable χ) {r : ℝ} (hr : 0 < r) (c : ℂ) :
    ‖diskAverage r (diskAverage r χ) c - χ c‖ ≤ 2 * (L : ℝ) * r := by
  have hdiff := norm_diskAverage_le_of_bound hr
    (fun z => lipschitz_norm_diskAverage_sub_le hχ hr z) c
  rw [diskAverage_sub ((diskAverage_integrable hr.le hint).integrableOn)
    hint.integrableOn] at hdiff
  calc
    _ = ‖(diskAverage r (diskAverage r χ) c - diskAverage r χ c) +
        (diskAverage r χ c - χ c)‖ := by congr 1; ring
    _ ≤ ‖diskAverage r (diskAverage r χ) c - diskAverage r χ c‖ +
        ‖diskAverage r χ c - χ c‖ := norm_add_le _ _
    _ ≤ (L : ℝ) * r + (L : ℝ) * r := add_le_add hdiff (lipschitz_norm_diskAverage_sub_le hχ hr c)
    _ = 2 * (L : ℝ) * r := by ring

theorem integral_mul_diskAverage_twice {r : ℝ} (hr : 0 < r) {f χ : ℂ → ℝ}
    (hf : Integrable f) (hχ : Integrable χ) {C : ℝ} (hχbound : ∀ z, ‖χ z‖ ≤ C) :
    (∫ z, χ z * diskAverage r (diskAverage r f) z) =
      ∫ z, f z * diskAverage r (diskAverage r χ) z := by
  rw [integral_mul_diskAverage hr.le (diskAverage_integrable hr.le hf)
    hχ.aestronglyMeasurable hχbound]
  calc
    _ = ∫ z, diskAverage r χ z * diskAverage r f z := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => mul_comm _ _)
    _ = _ := integral_mul_diskAverage hr.le hf
      (diskAverage_integrable hr.le hχ).aestronglyMeasurable
      (fun z => norm_diskAverage_le_of_bound hr hχbound z)


end ModifiedCartan
