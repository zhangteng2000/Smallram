import ModifiedCartan.CauchyWeak
import ModifiedCartan.LogKernel

open scoped Topology ENNReal
open Filter MeasureTheory Set Metric

namespace ModifiedCartan

/-! Logarithmic-kernel regularization in the proof of `lem:logderivlimit`.
An upper cap permits bounded weak-convergence test functions. It is removed on
compact sets once the source measures have common compact support. The lower
cutoff error is estimated almost everywhere, excluding the singular diagonal. -/

noncomputable def cappedLogKernel (L : ℝ) (w : ℂ) : ℝ := Real.log (min L ‖w‖)

noncomputable def logRegularization (R L : ℝ) (w : ℂ) : ℝ :=
  Real.log (max R (min L ‖w‖))

theorem continuous_logRegularization {R : ℝ} (hR : 0 < R) (L : ℝ) :
    Continuous (logRegularization R L) := by
  apply (continuous_const.max (continuous_const.min continuous_norm)).log
  intro w
  exact ne_of_gt (lt_of_lt_of_le hR (le_max_left _ _))

theorem measurable_cappedLogKernel (L : ℝ) : Measurable (cappedLogKernel L) :=
  Real.measurable_log.comp (measurable_const.min measurable_norm)

theorem logRegularization_eq_cappedLog {R L : ℝ} (hRL : R ≤ L) {w : ℂ}
    (hw : R ≤ ‖w‖) : logRegularization R L w = cappedLogKernel L w := by
  simp only [logRegularization, cappedLogKernel, max_eq_right (le_min hRL hw)]

theorem norm_logRegularization_le {R L : ℝ} (hR : 0 < R) (hRL : R ≤ L) (w : ℂ) :
    ‖logRegularization R L w‖ ≤ |Real.log R| + |Real.log L| := by
  have hlo : Real.log R ≤ logRegularization R L w :=
    Real.log_le_log hR (le_max_left _ _)
  have hhi : logRegularization R L w ≤ Real.log L :=
    Real.log_le_log (lt_of_lt_of_le hR (le_max_left _ _)) (max_le hRL (min_le_left _ _))
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor <;> linarith [le_abs_self (Real.log R), neg_abs_le (Real.log R),
    le_abs_self (Real.log L), abs_nonneg (Real.log R), abs_nonneg (Real.log L)]

theorem norm_cappedLog_error_le_nearCauchy {R L : ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1) (hL : 1 ≤ L) {w : ℂ} (hw0 : w ≠ 0) :
    ‖cappedLogKernel L w - logRegularization R L w‖ ≤ ‖nearCauchyKernel R 0 w‖ := by
  by_cases hw : R ≤ ‖w‖
  · rw [logRegularization_eq_cappedLog (hR1.trans hL) hw, sub_self, norm_zero]
    exact norm_nonneg _
  have hwr : ‖w‖ < R := lt_of_not_ge hw
  have hmem : w ∈ ball (0 : ℂ) R := by simpa using hwr
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hlr : Real.log ‖w‖ ≤ Real.log R := Real.log_le_log hn hwr.le
  have hl0 : Real.log R ≤ 0 := Real.log_nonpos hR.le hR1
  have hlow := Real.neg_inv_le_log (norm_nonneg w)
  simp only [cappedLogKernel, logRegularization, min_eq_right (hwr.le.trans (hR1.trans hL)),
    max_eq_left hwr.le, nearCauchyKernel, indicator_of_mem hmem, sub_zero, norm_inv,
    Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hlr)]
  linarith

theorem eLpNorm_cappedLog_error_le {R L : ℝ} (hR : 0 < R) (hR1 : R ≤ 1) (hL : 1 ≤ L)
    (a : ℂ) :
    eLpNorm (fun z => cappedLogKernel L (z - a) - logRegularization R L (z - a))
      1 volume ≤ ENNReal.ofReal (2 * Real.pi * R) := by
  have hmono : eLpNorm (fun z => cappedLogKernel L (z - a) - logRegularization R L (z - a))
      1 volume ≤ eLpNorm (nearCauchyKernel R a) 1 volume := by
    apply eLpNorm_mono_ae
    filter_upwards [volume.ae_ne a] with z hz
    have h := norm_cappedLog_error_le_nearCauchy hR hR1 hL (sub_ne_zero.mpr hz)
    simpa only [nearCauchyKernel, indicator, mem_ball, dist_eq_norm, sub_zero] using h
  apply hmono.trans_eq
  have heq := eLpNorm_nearCauchyKernel (p := 1) zero_lt_one (by norm_num) hR.le a
  norm_num at heq
  exact heq

theorem measurable_cappedLog_error {R : ℝ} (hR : 0 < R) (L : ℝ) :
    Measurable (fun x : ℂ × ℂ => cappedLogKernel L (x.2 - x.1) -
      logRegularization R L (x.2 - x.1)) :=
  ((measurable_cappedLogKernel L).comp (measurable_snd.sub measurable_fst)).sub
    ((continuous_logRegularization hR L).measurable.comp (measurable_snd.sub measurable_fst))

theorem integrable_prod_cappedLog_error (ν : Measure ℂ) [IsFiniteMeasure ν]
    {R L : ℝ} (hR : 0 < R) (hR1 : R ≤ 1) (hL : 1 ≤ L) :
    Integrable (fun x : ℂ × ℂ => cappedLogKernel L (x.2 - x.1) -
      logRegularization R L (x.2 - x.1)) (ν.prod volume) :=
  integrable_prod_of_eLpNorm_one_le ν volume (measurable_cappedLog_error hR L)
    ENNReal.ofReal_lt_top (eLpNorm_cappedLog_error_le hR hR1 hL)

theorem integrable_logRegularization (ν : Measure ℂ) [IsFiniteMeasure ν]
    {R L : ℝ} (hR : 0 < R) (hRL : R ≤ L) (z : ℂ) :
    Integrable (fun a => logRegularization R L (z - a)) ν := by
  apply (integrable_const (|Real.log R| + |Real.log L|)).mono'
    (((continuous_logRegularization hR L).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable)
  exact Eventually.of_forall fun a => norm_logRegularization_le hR hRL (z - a)

theorem ae_integrable_cappedLogKernel (ν : Measure ℂ) [IsFiniteMeasure ν]
    {L : ℝ} (hL : 1 ≤ L) :
    ∀ᵐ z ∂volume, Integrable (fun a => cappedLogKernel L (z - a)) ν := by
  filter_upwards [(integrable_prod_cappedLog_error ν zero_lt_one le_rfl hL).prod_left_ae]
    with z hz
  simpa only [sub_add_cancel] using
    hz.fun_add (integrable_logRegularization ν zero_lt_one hL z)

noncomputable def cappedLogPotential (L : ℝ) (ν : Measure ℂ) (z : ℂ) : ℝ :=
  ∫ a, cappedLogKernel L (z - a) ∂ν

noncomputable def regularizedLogPotential (R L : ℝ) (ν : Measure ℂ) (z : ℂ) : ℝ :=
  ∫ a, logRegularization R L (z - a) ∂ν

theorem eLpNorm_cappedLogPotential_sub_regularized_le (ν : Measure ℂ) [IsFiniteMeasure ν]
    {R L : ℝ} (hR : 0 < R) (hR1 : R ≤ 1) (hL : 1 ≤ L) (K : Set ℂ) :
    eLpNorm (cappedLogPotential L ν - regularizedLogPotential R L ν) 1 (volume.restrict K) ≤
      ν univ * ENNReal.ofReal (2 * Real.pi * R) := by
  have heq : cappedLogPotential L ν - regularizedLogPotential R L ν =ᵐ[volume.restrict K]
      (fun z => ∫ a, cappedLogKernel L (z - a) - logRegularization R L (z - a) ∂ν) := by
    filter_upwards [ae_restrict_of_ae (ae_integrable_cappedLogKernel ν hL)] with z hz
    exact (integral_sub hz (integrable_logRegularization ν hR (hR1.trans hL) z)).symm
  rw [eLpNorm_congr_ae heq]
  have h := eLpNorm_integral_finite_le ν (volume.restrict K)
    (measurable_cappedLog_error hR L) (p := 1) le_rfl
    (C := ENNReal.ofReal (2 * Real.pi * R))
  simp only [ENNReal.ofReal_one] at h
  apply h
  intro a
  exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans
    (eLpNorm_cappedLog_error_le hR hR1 hL a)

theorem measurable_cappedLogPotential (L : ℝ) (ν : Measure ℂ) [IsFiniteMeasure ν] :
    Measurable (cappedLogPotential L ν) :=
  ((measurable_cappedLogKernel L).comp
    (measurable_snd.sub measurable_fst)).stronglyMeasurable.integral_prod_left'.measurable

theorem measurable_regularizedLogPotential {R : ℝ} (hR : 0 < R) (L : ℝ)
    (ν : Measure ℂ) [IsFiniteMeasure ν] : Measurable (regularizedLogPotential R L ν) :=
  ((continuous_logRegularization hR L).measurable.comp
    (measurable_snd.sub measurable_fst)).stronglyMeasurable.integral_prod_left'.measurable

theorem norm_regularizedLogPotential_le (ν : Measure ℂ) [IsFiniteMeasure ν]
    {R L : ℝ} (hR : 0 < R) (hRL : R ≤ L) (z : ℂ) :
    ‖regularizedLogPotential R L ν z‖ ≤ (|Real.log R| + |Real.log L|) * ν.real univ :=
  norm_integral_le_of_norm_le_const (Eventually.of_forall fun a =>
    norm_logRegularization_le hR hRL (z - a))

theorem memLp_regularizedLogPotential (ν : Measure ℂ) [IsFiniteMeasure ν]
    {R L : ℝ} (hR : 0 < R) (hRL : R ≤ L) {K : Set ℂ} (hK : IsCompact K) (p : ℝ≥0∞) :
    MemLp (regularizedLogPotential R L ν) p (volume.restrict K) := by
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  exact MemLp.of_bound (measurable_regularizedLogPotential hR L ν).aestronglyMeasurable
    ((|Real.log R| + |Real.log L|) * ν.real univ)
    (Eventually.of_forall (norm_regularizedLogPotential_le ν hR hRL))

theorem memLp_cappedLogPotential_on_compact (ν : Measure ℂ) [IsFiniteMeasure ν]
    {L : ℝ} (hL : 1 ≤ L) {K : Set ℂ} (hK : IsCompact K) :
    MemLp (cappedLogPotential L ν) 1 (volume.restrict K) := by
  have herr : MemLp (cappedLogPotential L ν - regularizedLogPotential 1 L ν)
      1 (volume.restrict K) := by
    refine ⟨((measurable_cappedLogPotential L ν).sub
      (measurable_regularizedLogPotential zero_lt_one L ν)).aestronglyMeasurable, ?_⟩
    apply (eLpNorm_cappedLogPotential_sub_regularized_le ν zero_lt_one le_rfl hL K).trans_lt
    finiteness
  simpa only [sub_add_cancel] using
    herr.add (memLp_regularizedLogPotential ν zero_lt_one hL hK 1)


end ModifiedCartan
