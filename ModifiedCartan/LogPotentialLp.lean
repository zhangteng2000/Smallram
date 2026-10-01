import ModifiedCartan.LogWeak
import ModifiedCartan.LogLp

open scoped Topology ENNReal
open Filter MeasureTheory Set Metric

namespace ModifiedCartan

/-! Local finite-exponent Lp membership of logarithmic potentials, used in
Step 1 of `lem:logderivlimit`. The logarithmic cutoff error at radius one is a
translate of a single compactly supported Lp function, so its column norms are
uniform in the source point. The finite-measure integral estimate completes the
proof, with no restriction excluding atoms. -/

noncomputable def nearLogKernel (w : ℂ) : ℝ :=
  (ball (0 : ℂ) 1).indicator (fun z : ℂ => Real.log ‖z‖) w

theorem memLp_nearLogKernel {p : ℝ} (hp : 0 < p) :
    MemLp nearLogKernel (ENNReal.ofReal p) volume := by
  apply (memLp_indicator_iff_restrict measurableSet_ball).mpr
  have h := memLp_logKernel_on_compact hp (0 : ℂ) (isCompact_closedBall (0 : ℂ) 1)
  have h' := h.mono_measure (Measure.restrict_mono_set volume ball_subset_closedBall)
  simpa only [sub_zero] using h'

theorem cappedLog_error_one_eq_nearLog {L : ℝ} (hL : 1 ≤ L) (w : ℂ) :
    cappedLogKernel L w - logRegularization 1 L w = nearLogKernel w := by
  by_cases hw : ‖w‖ < 1
  · have hm : w ∈ ball (0 : ℂ) 1 := by simpa using hw
    simp only [cappedLogKernel, logRegularization, min_eq_right (hw.le.trans hL),
      max_eq_left hw.le, Real.log_one, sub_zero, nearLogKernel, indicator_of_mem hm]
  · have hm : w ∉ ball (0 : ℂ) 1 := by simpa using hw
    rw [logRegularization_eq_cappedLog hL (le_of_not_gt hw), sub_self]
    simp only [nearLogKernel, indicator_of_notMem hm]

theorem eLpNorm_cappedLog_error_one_le {p L : ℝ} (hp : 0 < p) (hL : 1 ≤ L)
    (a : ℂ) (K : Set ℂ) :
    eLpNorm (fun z => cappedLogKernel L (z - a) - logRegularization 1 L (z - a))
      (ENNReal.ofReal p) (volume.restrict K) ≤ eLpNorm nearLogKernel (ENNReal.ofReal p) volume := by
  simp_rw [cappedLog_error_one_eq_nearLog hL]
  apply (eLpNorm_mono_measure (fun z => nearLogKernel (z - a))
    (ν := volume.restrict K) Measure.restrict_le_self).trans_eq
  exact eLpNorm_comp_measurePreserving (memLp_nearLogKernel hp).aestronglyMeasurable
    (measurePreserving_sub_right volume a)

theorem memLp_cappedLogPotential_of_one_le (ν : Measure ℂ) [IsFiniteMeasure ν]
    {p L : ℝ} (hp : 1 ≤ p) (hL : 1 ≤ L) {K : Set ℂ} (hK : IsCompact K) :
    MemLp (cappedLogPotential L ν) (ENNReal.ofReal p) (volume.restrict K) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have heq : cappedLogPotential L ν - regularizedLogPotential 1 L ν =ᵐ[volume.restrict K]
      (fun z => ∫ a, cappedLogKernel L (z - a) - logRegularization 1 L (z - a) ∂ν) := by
    filter_upwards [ae_restrict_of_ae (ae_integrable_cappedLogKernel ν hL)] with z hz
    exact (integral_sub hz (integrable_logRegularization ν zero_lt_one hL z)).symm
  have herr : MemLp (cappedLogPotential L ν - regularizedLogPotential 1 L ν)
      (ENNReal.ofReal p) (volume.restrict K) := by
    refine ⟨((measurable_cappedLogPotential L ν).sub
      (measurable_regularizedLogPotential zero_lt_one L ν)).aestronglyMeasurable, ?_⟩
    rw [eLpNorm_congr_ae heq]
    apply (eLpNorm_integral_finite_le ν (volume.restrict K)
      (measurable_cappedLog_error zero_lt_one L) hp
      (fun a => eLpNorm_cappedLog_error_one_le hp0 hL a K)).trans_lt
    exact ENNReal.mul_lt_top (measure_lt_top ν univ) (memLp_nearLogKernel hp0).eLpNorm_lt_top
  simpa only [sub_add_cancel] using
    herr.add (memLp_regularizedLogPotential ν zero_lt_one hL hK (ENNReal.ofReal p))

theorem memLp_logPotential_of_one_le (ν : Measure ℂ) [IsFiniteMeasure ν]
    {p : ℝ} (hp : 1 ≤ p) {S K : Set ℂ} (hS : IsCompact S)
    (hsupp : ∀ᵐ a ∂ν, a ∈ S) (hK : IsCompact K) :
    MemLp (logPotential ν) (ENNReal.ofReal p) (volume.restrict K) := by
  obtain ⟨L, hL, hbound⟩ := exists_log_cap_of_compact hK hS
  have heq : logPotential ν =ᵐ[volume.restrict K] cappedLogPotential L ν := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    exact logPotential_eq_capped_of_ae_bound ν z (hsupp.mono fun a ha => hbound z hz a ha)
  exact (memLp_congr_ae heq).mpr (memLp_cappedLogPotential_of_one_le ν hp hL hK)

theorem memLp_logPotential_of_pos (ν : Measure ℂ) [IsFiniteMeasure ν]
    {p : ℝ} (_hp : 0 < p) {S K : Set ℂ} (hS : IsCompact S)
    (hsupp : ∀ᵐ a ∂ν, a ∈ S) (hK : IsCompact K) :
    MemLp (logPotential ν) (ENNReal.ofReal p) (volume.restrict K) := by
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  by_cases hp1 : 1 ≤ p
  · exact memLp_logPotential_of_one_le ν hp1 hS hsupp hK
  · exact (memLp_logPotential_of_one_le ν (p := 1) le_rfl hS hsupp hK).mono_exponent
      (ENNReal.ofReal_le_ofReal (le_of_not_ge hp1))


end ModifiedCartan

