import ModifiedCartan.SubharmonicMean

open scoped Topology ENNReal NNReal
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan

/-- Recover the extended-valued submean definition from a locally integrable representative. -/
theorem isSubharmonicOn_of_real_disk_means {U : Set ℂ} {v : ℂ → EReal} {f : ℂ → ℝ}
    (husc : UpperSemicontinuousOn v U) (htop : ∀ z ∈ U, v z ≠ ⊤)
    (hf : LocallyIntegrableOn f U) (hrep : v =ᵐ[volume.restrict U] (fun z => (f z : EReal)))
    (hmean : ∀ c r, 0 < r → closedBall c r ⊆ U →
      v c ≤ (((Real.pi * r ^ 2)⁻¹ * ∫ z in ball c r, f z : ℝ) : EReal)) :
    IsSubharmonicOn U v := by
  refine ⟨husc, htop, ?_⟩
  intro c r hr hball M hM
  have hvol : volume (ball c r) < ⊤ :=
    (measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall c r).measure_lt_top
  have hpos : 0 < volume (ball c r) := isOpen_ball.measure_pos volume (nonempty_ball.mpr hr)
  by_cases hc : v c = ⊥
  · simp only [hc, EReal.coe_sub_bot, EReal.toENNReal_top,
      ENNReal.mul_top hpos.ne', le_top]
  have hcU := hball (mem_closedBall_self hr.le)
  have hcfin := htop c hcU
  have : IsFiniteMeasure (volume.restrict (ball c r)) := ⟨by simpa using hvol⟩
  have hfi := (hf.integrableOn_compact_subset hball (isCompact_closedBall c r)).mono_set
    ball_subset_closedBall
  have hrepball := hrep.filter_mono
    (ae_mono (Measure.restrict_mono_set _ (ball_subset_closedBall.trans hball)))
  have hnonneg : 0 ≤ᵐ[volume.restrict (ball c r)] (fun z => M - f z) := by
    filter_upwards [hrepball, ae_restrict_mem isOpen_ball.measurableSet] with z hz hzball
    have hle := hM z (ball_subset_closedBall hzball)
    rw [hz, EReal.coe_le_coe_iff] at hle
    exact sub_nonneg.mpr hle
  have heq : (fun z => ((M : EReal) - v z).toENNReal) =ᵐ[volume.restrict (ball c r)]
      (fun z => ENNReal.ofReal (M - f z)) := by
    filter_upwards [hrepball] with z hz
    rw [hz, ← EReal.coe_sub, EReal.real_coe_toENNReal]
  have hMi : Integrable (fun z => M - f z) (volume.restrict (ball c r)) :=
    (integrable_const M).sub hfi
  rw [lintegral_congr_ae heq, ← ofReal_integral_eq_lintegral_ofReal
    hMi hnonneg, integral_sub (integrable_const M) hfi,
    setIntegral_const, smul_eq_mul]
  have hcoe : ((M : EReal) - v c).toENNReal = ENNReal.ofReal (M - (v c).toReal) := by
    rw [← EReal.coe_toReal hcfin hc, ← EReal.coe_sub, EReal.real_coe_toENNReal]
    simp only [EReal.toReal_coe]
  rw [hcoe, ← ENNReal.ofReal_toReal hvol.ne, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  apply ENNReal.ofReal_le_ofReal
  have hle := hmean c r hr hball
  rw [← EReal.coe_toReal hcfin hc, EReal.coe_le_coe_iff] at hle
  change (volume (ball c r)).toReal * M - (∫ z in ball c r, f z) ≤
    (volume (ball c r)).toReal * (M - (v c).toReal)
  rw [complex_ball_real_volume c hr.le]
  have harea : 0 < Real.pi * r ^ 2 := mul_pos Real.pi_pos (sq_pos_of_pos hr)
  have hh := mul_le_mul_of_nonneg_left hle harea.le
  have he : (Real.pi * r ^ 2) * ((Real.pi * r ^ 2)⁻¹ * ∫ z in ball c r, f z) =
      ∫ z in ball c r, f z := by field_simp
  rw [he] at hh
  nlinarith


end ModifiedCartan
