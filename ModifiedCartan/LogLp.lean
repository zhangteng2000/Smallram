import ModifiedCartan.LogKernel

open scoped Topology ENNReal
open Filter MeasureTheory Set Metric

namespace ModifiedCartan

/-! Finite positive Lp membership of the logarithmic kernel, a supporting result
for `lem:logderivlimit`. -/

theorem log_rpow_le_of_nonneg {x p : ℝ} (hx : 0 ≤ x) (hp : 0 < p)
    (hl : 0 ≤ Real.log x) : (Real.log x) ^ p ≤ p ^ p * x := by
  have hlog : Real.log x ≤ p * x ^ p⁻¹ := by
    simpa only [div_eq_mul_inv, inv_inv, mul_comm] using
      Real.log_le_rpow_div hx (inv_pos.mpr hp)
  have h := Real.rpow_le_rpow hl hlog hp.le
  rw [Real.mul_rpow hp.le (Real.rpow_nonneg hx _),
    ← Real.rpow_mul hx, inv_mul_cancel₀ hp.ne', Real.rpow_one] at h
  exact h

theorem abs_log_rpow_le {x p : ℝ} (hx : 0 ≤ x) (hp : 0 < p) :
    |Real.log x| ^ p ≤ p ^ p * (x + x⁻¹) := by
  by_cases hl : 0 ≤ Real.log x
  · rw [abs_of_nonneg hl]
    exact (log_rpow_le_of_nonneg hx hp hl).trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (inv_nonneg.mpr hx))
        (Real.rpow_nonneg hp.le p))
  · have hli : 0 ≤ Real.log x⁻¹ := by rw [Real.log_inv]; linarith
    rw [abs_of_neg (lt_of_not_ge hl), ← Real.log_inv]
    exact (log_rpow_le_of_nonneg (inv_nonneg.mpr hx) hp hli).trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hx)
        (Real.rpow_nonneg hp.le p))

theorem memLp_logKernel_on_compact {p : ℝ} (hp : 0 < p) (a : ℂ)
    {K : Set ℂ} (hK : IsCompact K) :
    MemLp (fun z : ℂ => Real.log ‖z - a‖) (ENNReal.ofReal p) (volume.restrict K) := by
  have hmeas : Measurable (fun z : ℂ => Real.log ‖z - a‖) :=
    Real.measurable_log.comp (measurable_id.sub measurable_const).norm
  apply (integrable_norm_rpow_iff hmeas.aestronglyMeasurable
    (by simpa using hp) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal hp.le]
  have hn : IntegrableOn (fun z : ℂ => ‖z - a‖) K :=
    (continuous_id.sub continuous_const).norm.continuousOn.integrableOn_compact hK
  have hi : IntegrableOn (fun z : ℂ => ‖(z - a)⁻¹‖) K := by
    have := memLp_cauchyKernel_on_compact (p := 1) zero_lt_one (by norm_num) a hK
    rw [ENNReal.ofReal_one, memLp_one_iff_integrable] at this
    exact this.norm
  apply ((hn.add hi).const_mul (p ^ p)).mono'
    (hmeas.norm.pow_const p).aestronglyMeasurable
  filter_upwards [] with z
  simp only [Pi.add_apply]
  rw [norm_inv, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
    Real.norm_eq_abs]
  exact abs_log_rpow_le (norm_nonneg _) hp

end ModifiedCartan


