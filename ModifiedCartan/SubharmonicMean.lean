import ModifiedCartan.SubharmonicBasic

open scoped Topology ENNReal
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan

theorem complex_ball_real_volume (c : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    (volume (ball c r)).toReal = Real.pi * r ^ 2 := by
  simp only [Complex.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hr, ENNReal.coe_toReal, NNReal.coe_real_pi, mul_comm]

theorem IsSubharmonicOn.mul_area_le_integral {U : Set ℂ} {u : ℂ → EReal}
    (hu : IsSubharmonicOn U u) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hball : closedBall c r ⊆ U) (hc : u c ≠ ⊥) :
    (Real.pi * r ^ 2) * (u c).toReal ≤ ∫ z in ball c r, (u z).toReal := by
  obtain ⟨M, hM⟩ := hu.exists_real_upper_bound (isCompact_closedBall c r) hball
  have hvol : volume (ball c r) < ⊤ :=
    (measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall c r).measure_lt_top
  have : IsFiniteMeasure (volume.restrict (ball c r)) := ⟨by simpa using hvol⟩
  have hcU := hball (mem_closedBall_self hr.le)
  have hc' := hu.ne_top c hcU
  have hdefc : ((M : EReal) - u c).toENNReal ≠ ⊤ := by
    apply EReal.toENNReal_ne_top_iff.mpr
    rw [← EReal.coe_toReal hc' hc, ← EReal.coe_sub]
    exact EReal.coe_ne_top _
  have hdef := (hu.mono (ball_subset_closedBall.trans hball)).deficit_aemeasurable isOpen_ball.measurableSet M
  have hdeffin := hu.deficit_lintegral_lt_top hr hball hc hM
  have hle := (ENNReal.toReal_le_toReal hdeffin.ne
    (ENNReal.mul_ne_top hvol.ne hdefc)).mpr (hu.disk_submean c r hr hball M hM)
  rw [← integral_toReal hdef (ae_lt_top' hdef hdeffin.ne), ENNReal.toReal_mul,
    complex_ball_real_volume c hr.le,
    ereal_deficit_toReal hc' hc (hM c (mem_closedBall_self hr.le))] at hle
  have heq : (fun z => ((M : EReal) - u z).toENNReal.toReal) =ᵐ[volume.restrict (ball c r)]
      (fun z => M - (u z).toReal) := by
    filter_upwards [hu.ae_finite_on_ball hr hball hc, ae_restrict_mem isOpen_ball.measurableSet]
      with z hz hzball
    exact ereal_deficit_toReal hz.2 hz.1 (hM z (ball_subset_closedBall hzball))
  rw [integral_congr_ae heq, integral_sub (integrable_const M)
    (hu.integrableOn_toReal_ball hr hball hc), setIntegral_const, smul_eq_mul] at hle
  change (volume (ball c r)).toReal * M - _ ≤ _ at hle
  rw [complex_ball_real_volume c hr.le] at hle
  nlinarith

theorem IsSubharmonicOn.le_diskAverage {U : Set ℂ} {u : ℂ → EReal}
    (hu : IsSubharmonicOn U u) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hball : closedBall c r ⊆ U) :
    u c ≤ (((Real.pi * r ^ 2)⁻¹ * ∫ z in ball c r, (u z).toReal : ℝ) : EReal) := by
  by_cases hc : u c = ⊥
  · rw [hc]
    exact bot_le
  have hc' := hu.ne_top c (hball (mem_closedBall_self hr.le))
  rw [← EReal.coe_toReal hc' hc, EReal.coe_le_coe_iff]
  have harea : 0 < Real.pi * r ^ 2 := mul_pos Real.pi_pos (sq_pos_of_pos hr)
  have hle := hu.mul_area_le_integral hr hball hc
  have hquot := (le_div_iff₀ harea).mpr (by simpa only [mul_comm] using hle)
  simpa only [div_eq_mul_inv, mul_comm, EReal.toReal_coe] using hquot

theorem IsSubharmonicOn.le_diskAverage_of_ae_eq {U : Set ℂ} {u : ℂ → EReal} {v : ℂ → ℝ}
    (hu : IsSubharmonicOn U u) (hrep : u =ᵐ[volume.restrict U] (fun z => (v z : EReal)))
    {c : ℂ} {r : ℝ} (hr : 0 < r) (hball : closedBall c r ⊆ U) :
    u c ≤ (((Real.pi * r ^ 2)⁻¹ * ∫ z in ball c r, v z : ℝ) : EReal) := by
  have heq : (fun z => (u z).toReal) =ᵐ[volume.restrict (ball c r)] v := by
    filter_upwards [hrep.filter_mono (ae_mono (Measure.restrict_mono_set _
      (ball_subset_closedBall.trans hball)))] with z hz
    rw [hz, EReal.toReal_coe]
  simpa only [integral_congr_ae heq] using hu.le_diskAverage hr hball


end ModifiedCartan

