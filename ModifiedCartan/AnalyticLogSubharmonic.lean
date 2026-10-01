import ModifiedCartan.AnalyticLogDiskMean
import ModifiedCartan.SubharmonicMeanCriterion

open scoped Topology ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

theorem normalizedExtendedLog_continuousOn {U : Set ℂ} {f : ℂ → ℂ}
    (hf : ContinuousOn f U) (s : ℝ) : ContinuousOn (normalizedExtendedLog s f) U := by
  have hl : ContinuousOn (fun z => extendedLogNorm (f z)) U :=
    ENNReal.continuous_log.comp_continuousOn (ENNReal.continuous_ofReal.comp_continuousOn hf.norm)
  intro z hz
  exact EReal.Tendsto.const_mul (hl z hz) (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))

/-- The application bridge from analytic logarithms to the literal submean
definition used in M6. Zeros retain value negative infinity. -/
theorem normalizedExtendedLog_isSubharmonicOn {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsPreconnected U) {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hnonzero : ∃ z ∈ U, f z ≠ 0) {s : ℝ} (hs : 0 < s) :
    IsSubharmonicOn U (normalizedExtendedLog s f) := by
  apply isSubharmonicOn_of_real_disk_means
    (normalizedExtendedLog_continuousOn hf.continuousOn s).upperSemicontinuousOn
    (f := fun z => s⁻¹ * Real.log ‖f z‖)
  · intro z _
    by_cases hz : f z = 0
    · rw [normalizedExtendedLog_eq_bot hs hz]
      exact bot_ne_top
    · rw [normalizedExtendedLog_of_ne_zero s hz]
      exact EReal.coe_ne_top _
  · apply (locallyIntegrableOn_iff hU.isLocallyClosed).mpr
    intro K hKU hK
    exact (integrableOn_log_norm_on_compact hf hKU hK).const_mul s⁻¹
  · filter_upwards [analytic_ae_ne_zero hU hUc hf hnonzero] with z hz
    exact normalizedExtendedLog_of_ne_zero s hz
  · intro c r hr hball
    by_cases hc : f c = 0
    · rw [normalizedExtendedLog_eq_bot hs hc]
      exact bot_le
    · rw [normalizedExtendedLog_of_ne_zero s hc, EReal.coe_le_coe_iff, integral_const_mul]
      calc
        s⁻¹ * Real.log ‖f c‖ ≤ s⁻¹ * ((Real.pi * r ^ 2)⁻¹ * ∫ z in ball c r, Real.log ‖f z‖) :=
          mul_le_mul_of_nonneg_left (analytic_log_le_disk_mean hr (hf.mono hball) hc) (inv_nonneg.mpr hs.le)
        _ = _ := by ring

end ModifiedCartan
#print axioms ModifiedCartan.normalizedExtendedLog_isSubharmonicOn
